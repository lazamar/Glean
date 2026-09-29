{-
  Copyright (c) Meta Platforms, Inc. and affiliates.
  All rights reserved.

  This source code is licensed under the BSD-style license found in the
  LICENSE file in the root directory of this source tree.
-}

module Glean.Query.Recursion
  ( expandRecursion
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable (toList)
import qualified Data.HashMap.Strict as HashMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word64)

import Glean.Angle.Types (PredicateId(..), DerivingInfo(..), queryPredicateId)
import qualified Glean.Angle.Types as Angle
import Glean.Database.Schema.Types
import Glean.Display
import Glean.Query.Codegen.Types
import Glean.Query.Flatten (flattenDerivation)
import Glean.Query.Flatten.Types (FlattenedQuery)
import Glean.Query.Vars (varsBound, varsUsed)
import Glean.RTS.Term (Term(..))
import Glean.RTS.Types (Pid(..), PidRef(..), Type, FieldDef, derefType)
import Glean.Schema.Util (showRef)

{- Note [Evaluating recursive predicates]

Calls to derived predicates are normally inlined, but we can't do that
for recursive predicates because the expansion would never end. Instead
we flatten a call to a recursive predicate into a search for its facts,
as if it were a stored predicate. Then, after the query is reordered, we
replace that search with an evaluation that derives the facts it needs.
For a call

  P { "a", X }

we generate

  rec ( _ = Event_P_bf <- (0|{ "a" }) )    -- 1. record what the call needs
    ( ... )                                 -- 2. derive it
    yield ( ... )                           -- 3. produce the facts found

1. The binding pattern of the call says which fields of the key are
   bound when the call runs: here the first field is bound (b) and the
   second is free (f). We only know it after reordering, which is why
   this happens after reordering. The call creates a demand: the values
   of the bound fields that we need facts of P for. Demands are facts of
   an Event predicate, which only exists while the query runs. There is
   one for each recursive predicate and binding pattern, and its facts
   also record the progress of the evaluation (Note [Events]).

2. For each recursive predicate and binding pattern there is a
   derivation of the facts of P that match its demands:

     { Key, Value, D } where
       D = Event_P_bf (0|{ A });
       <derivation of P, with its first field set to A>

   Calls to recursive predicates inside it are treated in the same way:
   the call creates a demand. If the predicate is in the same component
   of mutually recursive predicates (see 'RecursiveComponent'), the
   derivation is suspended at the call, and resumed when facts are
   derived for the demand (see Note [Suspension]). We also need the
   derivation for the call's binding pattern, and so on until we have
   them all. The derivations of a component are evaluated together by
   CgRec: it runs them in rounds, until a round creates no new facts,
   including no new demands (see Note [Semi-naive evaluation]).

   A call to a predicate in another component (which must be a lower
   one) gets its own rec statement, so that component is complete for
   the demand before we use the call's results. In particular, a negated
   recursive predicate is always complete before it is negated, because
   stratification puts it in a lower component (see Note [Stratification]
   in Glean.Database.Schema).

   The facts are created by statements that we add at the end of the
   derivations once they have been reordered, rather than by statements of
   the derivation, because the reorderer could put such a statement
   before a filter and create facts that aren't true (see
   Note [Writing derived facts] in Glean.Query.UserQuery). Those facts
   would then be used to derive more.

3. After each round, we match the facts derived for the call in that
   round against the call's pattern, and run the rest of the query for
   each of them before starting the next round (see Note [Streaming]).

This is the Magic Sets transformation. Evaluation is bottom-up, but we
only derive facts that are relevant to the call. Binding patterns come
from the final order of the statements, so the result is correct
whatever the order. The order only affects how much gets derived.
-}

{- Note [Streaming]

A call to a recursive predicate is a generator (section 2 of the
design). Its results come out as they are derived, rather than once the
evaluation has finished. We schedule by rounds. After each round of the
evaluation we run the rest of the query for each fact that round derived
for the call, and then start the next round.

The facts derived for the call are those with a new Supply event for the
call's demand (Note [Events]). A Supply event is only created once, however
many ways its fact is derived, so each fact is produced once (unique
production, section 11 of the design). The same statements that find the facts for a
suspended derivation (Note [Suspension]) look them up and match them
against the call's pattern, which can be more specific than the binding
pattern.

We find them by going through the round's new events and keeping the
Supply events for the call's demand, rather than by searching for the
Supply events of the demand in the round. A search with a key prefix in
a range of ids goes through every fact with that prefix and skips those
outside the range (FactSet::seekWithinSection), so each round would go
through every fact derived for the call so far, which is quadratic in
the number of rounds. Going through the round's new events uses the
index of facts by id, and over the whole evaluation goes through each
event once.

Streaming lets a query stop an evaluation early. For example, a negation
stops at its first result, and a query that reaches a limit returns the
results it has so far (it can't be continued, see noContinuation in
Glean.Query.UserQuery). It also means that the rest of the query can
make a call with a demand that the evaluation in progress has already
created, which is why evaluations are isolated (see Note [Isolation]).
-}

{- Note [Suspension]

When a derivation calls a predicate of its own component, the facts it
needs may not have been derived yet. So instead of searching for them we
stop the derivation there, and resume it once for each fact derived for
the call (sections 6 to 8 of the design). For

  P { A, B } where Edge { A, K }; (Q { K, X } | ...); Label { X, B }

the branch deriving the facts for a new demand D0 of P becomes

  D0 = Event_P (0|{ A });
  Edge { A, K };
  ( ( D1 = Event_Q <- (0|{ K });               -- a demand for Q
      _ = Event_Q <- (2|{ D1, K, A, D0 });      -- the suspension
      fail ) | ... );
  Label { X, B }

and the branch resuming it after the call, for a new event of Q whose
key is E, is

  ( ( (1|{ D1, F }) = E;                        -- a Supply event
      Event_Q<all> (2|{ D1, K, A, D0 }) )        -- and its suspensions
  | ( (2|{ D1, K, A, D0 }) = E;                  -- a suspension
      Event_Q<old> (1|{ D1, F }) ) );            -- and earlier Supply events
  F = Q { K, X };       -- the fact derived for the call
  Label { X, B }        -- the rest of the derivation

Both branches end by creating the fact of P they derived and its Supply
event, Event_P <- (1|{ D0, Fact }) (see Note [Events]).

* Every fact derived for a demand D of P comes with a Supply event
  (1|{ D, Fact }). Resuming a suspension compares demand fact ids rather
  than the keys of the facts (demand factoring, section 8).

* A suspension holds the call's demand and the variables that the rest
  of the derivation needs: those bound before the call that are used by
  the call's pattern, by the statements after it, or by the result
  (sideways information passing, section 7). The demand D0 being derived
  is always among them, since it's part of the result.

* The rest of the derivation is everything that runs after the call.
  That's the rest of the statements around it, then the rest of the
  statements around those, and so on outwards. Alternatives of a
  disjunction or an if that weren't taken never run again, so wherever
  the call is, the rest is a flat list of statements. Calls in it are
  suspended in the same way.

* Each pair of a Supply event and a suspension for the same demand
  resumes the derivation exactly once: in the round after the later of
  the two was created. That relies on a round only seeing the facts
  derived before it started, see Note [Semi-naive evaluation].

D0 must be bound before any call is suspended, and the derivation is
reordered before we know which demands it is for. So we tell the
reorderer that D0 is bound, which makes D0 = Event_P (0|{ A }) a lookup,
and bind D0 to each new event before the rest of the branch. The branch
then matches the key of the event instead of looking it up.
-}

{- Note [Semi-naive evaluation]

A round only does work that can derive something new (section 5 of the
design). It looks at each event created in the previous round once
(Note [Events]):

* a new demand starts its derivation;
* a new Supply event or suspension resumes the derivations it pairs with
  (Note [Suspension]), so each pair of a Supply event and a suspension
  where one of them is new is considered once.

Facts are never removed and new facts get increasing ids, so the facts
derived in a round are a range of ids. At the start of a round,
CgRec sets the range of the previous round, and the searches of its
queries find the facts derived in it (SeekOnRoundNew), before it
(SeekOnRoundOld), or in both (SeekOnRoundAll). So these searches don't
see the facts derived during the current round (the snapshot of section
1); they are new in the next round.

The first round starts before the statements that create the call's
demand (the first argument of the design's two-argument rec), so it
only looks at that demand. The demand is always new, since each
evaluation starts with an empty store (see Note [Isolation]).
-}

{- Note [Events]

The auxiliary facts of an evaluation are events (section 9 of the
design). For each recursive predicate P and binding pattern there is an
Event predicate, Event_P_bf, whose key has an alternative for each kind
of event:

  (0|Demand)             a demand for facts of P: the values of the bound
                         fields of the key
  (1|{ D, Fact })        a Supply event: Fact was derived for the demand D
  (2|{ D, Live.., D0 })  a suspension of a derivation at a call to P with
  (3|...)                the demand D (Note [Suspension]); there is one
  ...                    alternative for each call site

A suspension is an event of the predicate it waits for, since that's
where the Supply events that resume it appear. The demand it's deriving,
D0, can be of another Event predicate: a derivation of Q suspended at a
call to P is an event of Event_P that refers to a demand of Event_Q.

In each round, an evaluation runs one query for each Event predicate of
its component. The query goes through the events created in the previous
round, and runs for each of them the branches of the derivations that are
for events of that predicate. The search binds the key of each event,
and each branch starts by matching it against an alternative:

  D = Event_P_bf<new> E;
  ( ( (0|{ A }) = E; ... )                  -- a new demand D
  | ( (1|{ D1, F }) = E; ... )              -- a Supply event: resume Q
  | ... )

So a round searches once for the new events of each Event predicate,
rather than once for each kind of event and each call site. A branch can
derive facts of a predicate other than the one whose events it's for:
resuming Q's derivation derives facts of Q. So each branch creates the
facts it derives, and their Supply events, at its end.

The alternatives for suspensions are only all known once every
derivation of the component has been generated, since each call site
adds one. They are only ever added at the end of the key type, and
generating code to create or match an alternative only needs its index,
so the code generated before an alternative is added stays valid. Nothing
uses the key type of an auxiliary predicate when the query runs: it has
no typechecker or traversal.
-}

{- Note [Isolation]

Each evaluation of a call to a recursive predicate (each CgRec, the
design's rec) keeps its auxiliary facts -- the facts of its Event
predicates: demands, Supply events and suspensions (Note [Events]) -- in
a store of its own (section 10 of the design). The store is freed when
the evaluation finishes (section 12).

This matters because results stream out of an evaluation before it
finishes (see Note [Streaming]). Another evaluation with the same demand
could find the demand already there, assume it was fully evaluated, and
miss results. It also stops the auxiliary facts of different evaluations
from filling up the query's fact set.

The facts of the recursive predicates themselves are shared. They go in
the query's fact set like any other derived facts, since they are the
results. Only the auxiliary facts record whether a demand has been fully
evaluated, so sharing derived facts can't make an evaluation stop early.

The downside is that evaluations no longer share work. A call with a
demand that an earlier call has evaluated will derive its facts again.
Caching completed demands (section 14) can bring the sharing back.

A store lives on the query's iterator stack, so when an evaluation is
left early (e.g. when a negation finds a result) its store is freed
along with its iterators. A component's CgRec lists its auxiliary
predicates, and code generation routes their facts, searches and
lookups to the store of the evaluation being compiled.
-}

{- Note [Caching]

Isolated evaluations (Note [Isolation]) don't share work, so a query
that calls a recursive predicate many times with the same demand would
derive the same facts every time. To avoid that we cache completed
demands (section 14 of the design):

* When an evaluation reaches its fixpoint, every demand in its store has
  been fully evaluated -- the demand of the call and every demand created
  while evaluating it. So before freeing the store, it creates a
  Completed fact for each of them, with the same key as the demand. There
  is a Completed predicate for each predicate and binding pattern, like
  the Event predicates, but its facts go in the query's fact set, where
  they outlive the evaluation.

* A call first looks for a Completed fact for its demand. If there is
  one then all the facts it needs are already there, so it just
  searches for them:

    if (Completed_P_bf { "a" }) then P { "a", X } else <evaluate>

  A call to the predicate's own component inside a derivation does the
  same instead of suspending. This lets an evaluation reuse the subgoals
  that earlier evaluations completed.

An evaluation that is left early (e.g. by a negation that found a
result) doesn't mark anything as completed, so a later call with the
same demand will evaluate it again.
-}

-- | Derive the facts of the recursive predicates that a query searches
-- for. See Note [Evaluating recursive predicates].
expandRecursion
  :: DbSchema
  -> (DbSchema -> [Var] -> FlattenedQuery -> Except Text CodegenQuery)
     -- ^ optimise and reorder a query, given variables that are bound
     -- before it runs
  -> CodegenQuery
  -> Except Text CodegenQuery
expandRecursion dbSchema compile query
  | HashMap.null (recursiveComponents dbSchema) = return query
  | otherwise = evalStateT (expandQuery Nothing query) state
  where
  state = ExpandState
    { exSchema = dbSchema
    , exCompile = compile
    , exNextPid = succ (tempPid dbSchema)
    , exEvents = Map.empty
    , exDerivations = Map.empty
    , exRequired = Set.empty
    , exOwnCalls = IntMap.empty
    , exAuxiliary = IntMap.empty
    , exCompleted = Map.empty
    }

-- | Which fields of the key of a predicate are bound at a call. For a
-- key that isn't a record there is only one field: the whole key.
type BindingPattern = [Bool]

type Call = (PredicateId, BindingPattern)

data ExpandState = ExpandState
  { exSchema :: DbSchema
    -- ^ including the auxiliary predicates created so far
  , exCompile
      :: DbSchema -> [Var] -> FlattenedQuery -> Except Text CodegenQuery
  , exNextPid :: Pid
  , exEvents :: Map Call Event
    -- ^ the Event predicate for each call, see Note [Events]
  , exDerivations :: Map Call (Derivation, Set Call)
    -- ^ the derivation of the facts demanded by each call, and the calls
    -- it makes to predicates of its own component
  , exRequired :: Set Call
    -- ^ calls made to predicates of the component we are generating
    -- queries for
  , exOwnCalls :: IntMap Call
    -- ^ those calls, by the variable of the demand fact they create
  , exAuxiliary :: IntMap [PidRef]
    -- ^ the auxiliary predicates of each component, by its index. Their
    -- facts live in the store of an evaluation, see Note [Isolation].
  , exCompleted :: Map Call PidRef
    -- ^ the Completed predicate for each call, see Note [Caching]
  }

type E a = StateT ExpandState (Except Text) a

-- | Fresh variables for the query we are expanding.
type V a = StateT Int (StateT ExpandState (Except Text)) a

-- | Expand the calls to recursive predicates in a query. If the query is
-- one of the saturation queries, it derives facts of the given component.
expandQuery :: Maybe Int -> CodegenQuery -> E CodegenQuery
expandQuery inside query@QueryWithInfo{..} = do
  let CgQuery hd stmts = qiQuery
  -- The generator of the result (qiGenerator), if any, looks up a fact
  -- that the statements have already found (see Note [query result] in
  -- Glean.Query.Flatten), so it needs no evaluation.
  (stmts', numVars) <- flip runStateT qiNumVars $ expandStmts inside stmts
  return query
    { qiQuery = CgQuery hd stmts'
    , qiNumVars = numVars
    }

expandStmts :: Maybe Int -> [CgStatement] -> V [CgStatement]
expandStmts inside = fmap concat . mapM expandStmt
  where
  expandStmt stmt = case stmt of
    CgStatement _ FactGenerator{} -> call inside stmt
    CgStatement{} -> return [stmt]
    CgAllStatement var expr stmts ->
      one $ CgAllStatement var expr <$> expandStmts inside stmts
    CgNegation stmts ->
      one $ CgNegation <$> expandStmts inside stmts
    CgDisjunction stmtss ->
      one $ CgDisjunction <$> mapM (expandStmts inside) stmtss
    CgConditional cond then_ else_ ->
      one $ CgConditional
        <$> expandStmts inside cond
        <*> expandStmts inside then_
        <*> expandStmts inside else_
    CgRec{} -> return [stmt]

  one = fmap (:[])

-- | The statements that replace a search for facts. If it's a call to a
-- recursive predicate whose demand hasn't been completed (Note [Caching]),
-- we create its demand and evaluate it. If the query we are in evaluates
-- the same component, we leave the search to be suspended instead
-- (Note [Suspension]).
call :: Maybe Int -> CgStatement -> V [CgStatement]
call inside search = do
  dbSchema <- lift $ gets exSchema
  (ref, key) <- case search of
    CgStatement _ (FactGenerator (PidRef _ ref) key _ _) -> return (ref, key)
    _ -> throwError "internal error: call"
  case HashMap.lookup ref (recursiveComponents dbSchema) of
    Nothing -> return [search]
    Just component -> do
      details <- lift $ getDetails ref
      let
        (binding, demandKey) = bindingPattern (predicateKeyType details) key
        this = (ref, binding)
      event <- lift $ eventPredicate this
      fid <- freshVar (Angle.PredicateTy () event)
      completed <- lift $ completedPredicate this
      let
        create = CgStatement (Ref (MatchBind fid))
          (DerivedFactGenerator event (Alt demandAlt demandKey) (Tuple []))
        -- if the demand has been completed, just search (Note [Caching])
        ifCompleted evaluate = CgConditional
          { cond =
              [ CgStatement (Ref (MatchWild (Angle.PredicateTy () completed)))
                  (FactGenerator completed demandKey (Tuple []) SeekOnAllFacts)
              ]
          , then_ = [search]
          , else_ = evaluate
          }
      if inside == Just (componentIndex component)
        then do
          lift $ modify $ \s -> s
            { exRequired = Set.insert this (exRequired s)
            , exOwnCalls = IntMap.insert (varId fid) this (exOwnCalls s)
            }
          return [ifCompleted [create, search]]
        else do
          (derivations, calls) <- lift $ componentDerivations this
          rounds <- lift $ mapM (roundQuery derivations) (Set.toList calls)
          complete <- mapM completeDemands (Set.toList calls)
          auxiliary <- lift $ gets $
            IntMap.findWithDefault [] (componentIndex component) . exAuxiliary
          new <- freshVar (Angle.PredicateTy () event)
          newKey <- freshVar =<< lift (eventKeyType' event)
          fact <- freshVar (Angle.PredicateTy () (pidRef details))
          suppliedFor <- freshVar (Angle.PredicateTy () event)
          let
            -- the facts derived for the call in the round: the round's new
            -- Supply events for the call's demand. Not a search for the
            -- demand's Supply events, see Note [Streaming].
            supplied =
              [ newEvent new newKey event
              , matchEvent newKey supplyAlt
                  (Tuple [Ref (MatchBind suppliedFor), Ref (MatchBind fact)])
              , CgStatement (Ref (MatchVar suppliedFor))
                  (TermGenerator (Ref (MatchVar fid)))
              ]
          return
            [ ifCompleted
                [ CgRec [create] rounds auxiliary
                    (supplied <> found search fact) complete ]
            ]

-- | The statements marking every demand of a call in an evaluation's
-- store as completed. See Note [Caching].
completeDemands :: Call -> V [CgStatement]
completeDemands this = do
  event <- lift $ eventOf this
  completed <- lift $ completedPredicate this
  key <- freshVar (evDemand event)
  done <- freshVar (Angle.PredicateTy () completed)
  return
    [ searchEvents (evPredicate event) demandAlt (Ref (MatchBind key))
        SeekOnAllFacts
    -- a DerivedFactGenerator whose result isn't bound creates nothing
    , CgStatement (Ref (MatchBind done))
        (DerivedFactGenerator completed (Ref (MatchVar key)) (Tuple []))
    ]

freshVar :: Monad m => Type -> StateT Int m Var
freshVar ty = do
  n <- get
  put (n + 1)
  return (Var ty n Nothing)

-- | The binding pattern of a call with the given key pattern, and the
-- key of its demand, which holds the values of the bound fields.
--
-- A field is bound when its pattern can't bind any variables, which
-- means it's an expression whose value is known when the search runs.
-- Anything else is treated as free. That's always correct but may
-- derive more facts than necessary.
bindingPattern :: Type -> Pat -> (BindingPattern, Expr)
bindingPattern keyTy pat = case fields keyTy of
  Just fs -> case stripBinds pat of
    Tuple pats | length pats == length fs ->
      let binding = map isBound pats in
      (binding, Tuple [ p | (p, True) <- zip pats binding ])
    p | isBound p -> (map (const True) fs, p)
      | otherwise -> (map (const False) fs, Tuple [])
  Nothing
    | isBound p -> ([True], p)
    | otherwise -> ([False], Tuple [])
    where p = stripBinds pat
  where
  isBound = all $ \case
    MatchVar{} -> True
    MatchFid{} -> True
    _ -> False

  -- a pattern "X@P" (MatchAnd with a binder) binds X to the value
  -- matched by P, so the value is bound if P is.
  stripBinds = \case
    Ref (MatchAnd (Ref MatchBind{}) p) -> stripBinds p
    Ref (MatchAnd p (Ref MatchBind{})) -> stripBinds p
    p -> p

-- | The fields of a record key type
fields :: Type -> Maybe [FieldDef]
fields ty = case derefType ty of
  Angle.RecordTy fs -> Just fs
  _ -> Nothing


-- | The Event predicate of a call: its facts are the demands for the
-- call's predicate and binding pattern, the Supply events for them, and the
-- suspensions waiting for them. See Note [Events].
data Event = Event
  { evPredicate :: PidRef
  , evFact :: PidRef
    -- ^ the predicate called
  , evDemand :: Type
    -- ^ the key of a demand: the values of the bound fields of the key
  , evSuspended :: [Type]
    -- ^ the suspensions waiting for the demands: an alternative for each
    -- call site, in order
  }

-- | The alternatives of the key of an Event predicate
demandAlt, supplyAlt :: Word64
demandAlt = 0
supplyAlt = 1

-- | The alternative for the suspensions of the n-th call site that waits
-- for the demands of an Event predicate
suspendedAlt :: Int -> Word64
suspendedAlt n = 2 + fromIntegral n

eventKeyType :: Event -> Type
eventKeyType Event{..} = Angle.SumTy $
  [ Angle.FieldDef "demand" evDemand
  , Angle.FieldDef "supply" $ Angle.RecordTy
      [ Angle.FieldDef "demand" (Angle.PredicateTy () evPredicate)
      , Angle.FieldDef "fact" (Angle.PredicateTy () evFact)
      ]
  ] <>
  [ Angle.FieldDef ("suspended_" <> Text.pack (show n)) ty
  | (n, ty) <- zip [0 :: Int ..] evSuspended ]

-- | The Event predicate for a call. See Note [Events].
eventOf :: Call -> E Event
eventOf this@(ref, binding) = do
  existing <- gets (Map.lookup this . exEvents)
  case existing of
    Just event -> return event
    Nothing -> do
      details <- getDetails ref
      let
        keyTy = predicateKeyType details
        demandTy = case fields keyTy of
          Just fs -> Angle.RecordTy [ f | (f, True) <- zip fs binding ]
          Nothing
            | and binding -> keyTy
            | otherwise -> Angle.RecordTy []
        event self = Event
          { evPredicate = self
          , evFact = pidRef details
          , evDemand = demandTy
          , evSuspended = []
          }
      predicate <- auxiliaryPredicate this (callName "event" this)
        (eventKeyType . event)
      modify $ \s ->
        s { exEvents = Map.insert this (event predicate) (exEvents s) }
      return (event predicate)

eventPredicate :: Call -> E PidRef
eventPredicate = fmap evPredicate . eventOf

-- | Add an alternative to the key of the Event predicate of a call, for
-- the suspensions of a call site that waits for its demands. Alternatives
-- are only ever added at the end, so the code already generated for the
-- others stays valid (see Note [Events]).
suspendedAlternative :: Call -> Type -> E Word64
suspendedAlternative callee ty = do
  event <- eventOf callee
  let
    event' = event { evSuspended = evSuspended event <> [ty] }
    PidRef _ ref = evPredicate event
  details <- getDetails ref
  modify $ \s -> s
    { exEvents = Map.insert callee event' (exEvents s)
    , exSchema = addPredicate
        details { predicateKeyType = eventKeyType event' }
        (exSchema s)
    }
  return (suspendedAlt (length (evSuspended event)))

-- | Bind variables to each new event of an Event predicate and to its
-- key: the events of the previous round in the queries of an evaluation,
-- and the events of the round that just finished after it.
newEvent :: Var -> Var -> PidRef -> CgStatement
newEvent var key event = CgStatement (Ref (MatchBind var))
  (FactGenerator event (Ref (MatchBind key)) (Tuple []) SeekOnRoundNew)

-- | Match the key of an event against an alternative
matchEvent :: Var -> Word64 -> Pat -> CgStatement
matchEvent key alt pat =
  CgStatement (Alt alt pat) (TermGenerator (Ref (MatchVar key)))

-- | The key type of an Event predicate, with the alternatives added so far
eventKeyType' :: PidRef -> E Type
eventKeyType' (PidRef _ ref) = predicateKeyType <$> getDetails ref

-- | Search for events of an alternative of the key of an Event predicate
searchEvents :: PidRef -> Word64 -> Pat -> SeekSection -> CgStatement
searchEvents event alt pat section =
  CgStatement (Ref (MatchWild (Angle.PredicateTy () event)))
    (FactGenerator event (Alt alt pat) (Tuple []) section)

-- | e.g. @event:x.Path.1:bf@
callName :: Text -> Call -> Text
callName kind (ref, binding) =
  kind <> ":" <> showRef (predicateIdRef ref) <> ":" <>
  Text.pack [ if bound then 'b' else 'f' | bound <- binding ]

-- | The Completed predicate for a call, which records which of its
-- demands have been fully evaluated. See Note [Caching].
completedPredicate :: Call -> E PidRef
completedPredicate this = do
  existing <- gets (Map.lookup this . exCompleted)
  case existing of
    Just completed -> return completed
    Nothing -> do
      event <- eventOf this
      completed <- newPredicate (callName "completed" this)
        (const (evDemand event))
      modify $ \s ->
        s { exCompleted = Map.insert this completed (exCompleted s) }
      return completed

-- | A predicate for evaluating the component of a call. Its facts live
-- in the evaluation's store. See Note [Isolation].
auxiliaryPredicate :: Call -> Text -> (PidRef -> Type) -> E PidRef
auxiliaryPredicate (owner, _) name keyTy = do
  component <- gets (HashMap.lookup owner . recursiveComponents . exSchema)
  index <- case component of
    Just c -> return (componentIndex c)
    Nothing -> throwError "internal error: auxiliaryPredicate"
  predicate <- newPredicate name keyTy
  modify $ \s -> s
    { exAuxiliary =
        IntMap.insertWith (<>) index [predicate] (exAuxiliary s)
    }
  return predicate

-- | A predicate that only exists while the query runs. Its key type is
-- given the predicate, so that it can refer to it.
newPredicate :: Text -> (PidRef -> Type) -> E PidRef
newPredicate name keyTy = do
  pid <- gets exNextPid
  let
    ref = queryPredicateId name
    details = PredicateDetails
      { predicatePid = pid
      , predicateId = ref
      , predicateSchema = error "auxiliary predicate: predicateSchema"
      , predicateKeyType = keyTy (PidRef pid ref)
      , predicateValueType = Angle.RecordTy []
      , predicateTypecheck = error "auxiliary predicate: predicateTypecheck"
      , predicateTraversal = error "auxiliary predicate: predicateTraversal"
      , predicateDeriving = NoDeriving
      , predicateInStoredSchema = False
      }
  modify $ \s -> s
    { exNextPid = succ pid
    , exSchema = addPredicate details (exSchema s)
    }
  return (PidRef pid ref)

addPredicate :: PredicateDetails -> DbSchema -> DbSchema
addPredicate details dbSchema = dbSchema
  { predicatesById =
      HashMap.insert (predicateId details) details (predicatesById dbSchema)
  , predicatesByPid =
      IntMap.insert (fromIntegral (fromPid (predicatePid details))) details
        (predicatesByPid dbSchema)
  }

getDetails :: PredicateId -> E PredicateDetails
getDetails ref = do
  dbSchema <- gets exSchema
  case lookupPredicateId ref dbSchema of
    Just details -> return details
    Nothing -> throwError $ "internal error: expandRecursion: " <>
      Text.pack (show (displayDefault ref))


-- | The derivations of the facts demanded by a call, and by the calls
-- they make to predicates of the same component, transitively, and all
-- those calls.
componentDerivations :: Call -> E ([Derivation], Set Call)
componentDerivations start = go [start] Set.empty []
  where
  go [] done acc = return (reverse acc, done)
  go (this : rest) done acc
    | this `Set.member` done = go rest done acc
    | otherwise = do
      (derivation, required) <- derivationsFor this
      go (rest <> Set.toList required) (Set.insert this done)
        (derivation : acc)

-- | The derivation of the facts demanded by a call.
derivationsFor :: Call -> E (Derivation, Set Call)
derivationsFor this@(ref, binding) = do
  existing <- gets (Map.lookup this . exDerivations)
  case existing of
    Just result -> return result
    Nothing -> do
      details <- getDetails ref
      component <- gets (HashMap.lookup ref . recursiveComponents . exSchema)
      event <- eventPredicate this
      dbSchema <- gets exSchema
      compile <- gets exCompile
      query <- liftEither $ runExcept $ do
        (flat, d0) <- flattenDerivation dbSchema ref event binding
        compile dbSchema [d0] flat
      -- expand the calls inside it, collecting those to its own component
      outer <- gets $ \s -> (exRequired s, exOwnCalls s)
      modify $ \s -> s { exRequired = Set.empty, exOwnCalls = IntMap.empty }
      expanded <- expandQuery (componentIndex <$> component) query
      required <- gets exRequired
      ownCalls <- gets exOwnCalls
      modify $ \s -> s { exRequired = fst outer, exOwnCalls = snd outer }
      derivation <- suspend this (pidRef details) event expanded ownCalls
      let result = (derivation, required)
      modify $ \s ->
        s { exDerivations = Map.insert this result (exDerivations s) }
      return result

-- | The branches deriving the facts demanded by a call. They share their
-- variables, which are separate from those of other derivations.
data Derivation = Derivation
  { derivationBranches :: [Branch]
  , derivationVars :: Int
  }

-- | What to do with a new event of an Event predicate, if it's of the
-- right kind: start the derivation for a new demand, or resume it. See
-- Note [Events].
data Branch = Branch
  { branchEvent :: Call
    -- ^ the call whose Event predicate the event is of
  , branchVar :: Var
    -- ^ bound to the event
  , branchKey :: Var
    -- ^ bound to the key of the event
  , branchStmts :: [CgStatement]
  }

-- | The query that runs in each round for the new events of the Event
-- predicate of a call: one search for them, and for each event the
-- branches of all the derivations that are for its predicate. See
-- Note [Events].
roundQuery :: [Derivation] -> Call -> E CgDerivation
roundQuery derivations this = do
  event <- eventPredicate this
  keyTy <- eventKeyType' event
  let
    var = Var (Angle.PredicateTy () event) 0 Nothing
    key = Var keyTy 1 Nothing
    -- the derivations with branches for these events
    relevant =
      [ (derivationVars, ours)
      | Derivation{..} <- derivations
      , let ours = filter ((== this) . branchEvent) derivationBranches
      , not (null ours)
      ]
    -- the variables of each derivation come after those of the ones
    -- before it, and each branch's event and key are the ones found
    offsets = scanl (+) 2 (map fst relevant)
    rename offset Branch{..} v@(Var ty n name)
      | v == branchVar = var
      | v == branchKey = key
      | otherwise = Var ty (n + offset) name
    branches =
      [ map (fmap (rename offset branch)) (branchStmts branch)
      | (offset, (_, ours)) <- zip offsets relevant
      , branch <- ours
      ]
  return CgDerivation
    { derivationStmts = [newEvent var key event, CgDisjunction branches]
    , derivationNumVars = last offsets
    }

-- | A call to the component being derived. It holds the variable of the
-- demand fact it creates, the search for its facts, and what runs after
-- the search.
data Site = Site
  { siteDemand :: Var
  , siteCall :: Call
  , siteSearch :: CgStatement
  , siteRest :: [CgStatement]
  }

-- | A call where the derivation is suspended
data Suspension = Suspension
  { suspSite :: Site
  , suspEvent :: PidRef
    -- ^ the Event predicate of the call, which has the suspensions as an
    -- alternative
  , suspAlt :: Word64
  , suspLive :: [Var]
    -- ^ the variables that the rest of the derivation needs
  , suspVar :: Var
    -- ^ for the suspension
  }

-- | The branches deriving the facts demanded by a call: one running the
-- derivation for a new demand, and one resuming it after each call it
-- makes to its own component. Each branch ends by creating the fact it
-- derived and its Supply event. See Note [Suspension].
suspend
  :: Call            -- ^ the call it derives facts for
  -> PidRef          -- ^ the predicate of the call
  -> PidRef          -- ^ its Event predicate
  -> CodegenQuery    -- ^ the derivation
  -> IntMap Call     -- ^ calls to its own component, see exOwnCalls
  -> E Derivation
suspend this predicate event query ownCalls = do
  let QueryWithInfo (CgQuery result stmts) numVars _ _ = query
  (key, val, d0) <- case result of
    Tuple [key, val, Ref (MatchVar d0)] -> return (key, val, d0)
    _ -> throwError "internal error: suspend: unexpected result"
  sites <- liftEither $ callSites ownCalls stmts []
  flip evalStateT numVars $ do
    suspensions <- forM sites $ \site -> do
      let live = liveVars (siteSearch site : siteRest site) result
      callee <- lift $ eventPredicate (siteCall site)
      alt <- lift $ suspendedAlternative (siteCall site) $ Angle.RecordTy
        [ Angle.FieldDef (Text.pack ("f" <> show i)) ty
        | (i, ty) <- zip [0 :: Int ..]
            (varType (siteDemand site) : map varType live) ]
      var <- freshVar (Angle.PredicateTy () callee)
      return (Suspension site callee alt live var)
    fact <- freshVar (Angle.PredicateTy () predicate)
    supplied <- freshVar (Angle.PredicateTy () event)
    eventKey <- freshVar =<< lift (eventKeyType' event)
    let
      byDemand = IntMap.fromList
        [ (varId (siteDemand (suspSite s)), s) | s <- suspensions ]
      -- Create the fact and its Supply event at the end, after the
      -- statements have been reordered: see Note [Evaluating recursive
      -- predicates]. (A DerivedFactGenerator whose result isn't bound
      -- creates nothing.)
      create =
        [ CgStatement (Ref (MatchBind fact))
            (DerivedFactGenerator predicate key val)
        , CgStatement (Ref (MatchBind supplied))
            (DerivedFactGenerator event
              (Alt supplyAlt (Tuple [Ref (MatchVar d0), Ref (MatchVar fact)]))
              (Tuple []))
        ]
      -- The derivation looks up D0, which is bound to the new event:
      -- match the event's key instead.
      matchDemand stmt = case stmt of
        CgStatement (Ref (MatchVar v)) (FactGenerator e (Alt alt pat) _ _)
          | v == d0, e == event -> matchEvent eventKey alt pat
        _ -> stmt
      start = Branch this d0 eventKey
        (map matchDemand (suspendCalls byDemand stmts) <> create)
    resumes <- forM suspensions $ \s -> do
      branch <- resume byDemand s
      return branch { branchStmts = branchStmts branch <> create }
    Derivation (start : resumes) <$> get

-- | The branch resuming a derivation after a call. It is for the new
-- events of the Event predicate of the call: a Supply event for the call's
-- demand resumes each suspension waiting for it, and a suspension resumes
-- with each earlier Supply event. See Note [Suspension].
resume :: IntMap Suspension -> Suspension -> V Branch
resume suspensions Suspension{..} = do
  let Site{..} = suspSite
  called <- case siteSearch of
    CgStatement _ (FactGenerator called _ _ _) -> return called
    _ -> throwError "internal error: resume: unexpected call"
  fact <- freshVar (Angle.PredicateTy () called)
  new <- freshVar (Angle.PredicateTy () suspEvent)
  key <- freshVar =<< lift (eventKeyType' suspEvent)
  let
    bind = Ref . MatchBind
    use = Ref . MatchVar
    suspended demand = Tuple (demand : map bind suspLive)
    supplied demand = Tuple [demand, bind fact]
    -- each pair of a Supply event and a suspension where one is new
    resumed = CgDisjunction
      [ [ matchEvent key supplyAlt (supplied (bind siteDemand))
        , searchEvents suspEvent suspAlt (suspended (use siteDemand))
            SeekOnRoundAll ]
      , [ matchEvent key suspAlt (suspended (bind siteDemand))
        , searchEvents suspEvent supplyAlt (supplied (use siteDemand))
            SeekOnRoundOld ]
      ]
  return $ Branch siteCall new key
    (resumed : found siteSearch fact <> suspendCalls suspensions siteRest)

-- | Given a search for facts and a variable holding a fact found for it by
-- other means, the statements that match the fact against the search as
-- the search would have.
found :: CgStatement -> Var -> [CgStatement]
found search fact = case search of
  CgStatement lhs (FactGenerator called key value _) ->
    [ CgStatement lhs (TermGenerator (use fact)) | not (isWild lhs) ] <>
    [ CgStatement (use fact) (FactGenerator called key value SeekOnAllFacts) ]
  _ -> error "internal error: found"
  where
  use = Ref . MatchVar
  isWild (Ref MatchWild{}) = True
  isWild _ = False


-- | Replace the calls to the component being derived with a suspension.
-- That is, create the demand, record what the rest of the derivation
-- needs, and stop.
suspendCalls :: IntMap Suspension -> [CgStatement] -> [CgStatement]
suspendCalls suspensions = go
  where
  go [] = []
  go (stmt : rest) = case stmt of
    CgStatement (Ref (MatchBind var)) DerivedFactGenerator{}
      | Just Suspension{..} <- IntMap.lookup (varId var) suspensions ->
        [ stmt
        , CgStatement (Ref (MatchBind suspVar))
            (DerivedFactGenerator suspEvent
              (Alt suspAlt (Tuple (map (Ref . MatchVar) (var : suspLive))))
              (Tuple []))
        , CgDisjunction []  -- fail
        ]
    CgDisjunction stmtss -> CgDisjunction (map go stmtss) : go rest
    CgConditional cond then_ else_ ->
      CgConditional cond (go then_) (go else_) : go rest
    _ -> stmt : go rest

-- | The calls to the component being derived, each with what runs after
-- it. That's the rest of the statements around it, then the rest of the
-- statements around those, and so on outwards.
callSites
  :: IntMap Call      -- ^ see exOwnCalls
  -> [CgStatement]
  -> [CgStatement]    -- ^ what runs after these statements
  -> Either Text [Site]
callSites calls = go
  where
  go [] _ = return []
  go (stmt : rest) after = case stmt of
    CgStatement (Ref (MatchBind var)) DerivedFactGenerator{}
      | Just this <- IntMap.lookup (varId var) calls ->
        case rest of
          search : rest' ->
            (Site var this search (rest' <> after) :) <$> go rest' after
          [] -> Left "internal error: callSites: call without a search"
    CgDisjunction stmtss -> do
      inside <- mapM (\stmts -> go stmts (rest <> after)) stmtss
      (concat inside <>) <$> go rest after
    CgConditional cond then_ else_ -> do
      -- calls to the same component in the condition would be recursion
      -- through negation, which stratification rules out
      noCalls cond
      inThen <- go then_ (rest <> after)
      inElse <- go else_ (rest <> after)
      ((inThen <> inElse) <>) <$> go rest after
    CgNegation stmts -> noCalls stmts >> go rest after
    CgAllStatement _ _ stmts -> noCalls stmts >> go rest after
    _ -> go rest after

  noCalls stmts = do
    sites <- go stmts []
    unless (null sites) $
      Left "internal error: callSites: recursion through negation"

-- | The variables that statements use before binding them, and those that
-- the result uses, in order of their number.
liveVars :: [CgStatement] -> Expr -> [Var]
liveVars stmts result =
  [ var | var <- IntMap.elems allVars, varId var `IntSet.member` free ]
  where
  (bound, used) = freeVars IntSet.empty stmts
  free = IntSet.union used (varsUsed result `IntSet.difference` bound)
  allVars = IntMap.fromList
    [ (varId var, var) | var <- foldMap toList stmts <> foldMap toList result ]

-- | Given the variables bound before some statements, the variables bound
-- after them, and those they use before binding them.
freeVars :: IntSet -> [CgStatement] -> (IntSet, IntSet)
freeVars bound0 = foldl' step (bound0, IntSet.empty)
  where
  step (bound, free) stmt =
    let (bound', free') = statementFree bound stmt in
    (bound', IntSet.union free free')

  statementFree bound stmt = case stmt of
    CgStatement{} ->
      let bound' = IntSet.union bound (varsBound stmt) in
      (bound', varsUsed stmt `IntSet.difference` bound')
    CgAllStatement var expr stmts ->
      let (inner, free) = freeVars bound stmts in
      ( IntSet.insert (varId var) bound
      , IntSet.union free (varsUsed expr `IntSet.difference` inner) )
    CgNegation stmts -> (bound, snd (freeVars bound stmts))
    CgDisjunction stmtss ->
      -- A variable bound in some alternatives but not others is local to
      -- them, so it can't be used after the disjunction.
      let results = map (freeVars bound) stmtss in
      (IntSet.unions (bound : map fst results), IntSet.unions (map snd results))
    CgConditional cond then_ else_ ->
      let
        (boundCond, freeCond) = freeVars bound cond
        (boundThen, freeThen) = freeVars boundCond then_
        (boundElse, freeElse) = freeVars bound else_
      in
      ( IntSet.union boundThen boundElse
      , IntSet.unions [freeCond, freeThen, freeElse] )
    CgRec first _ _ yield _ -> freeVars bound (first <> yield)
