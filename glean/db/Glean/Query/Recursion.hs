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

A call to a derived predicate is normally expanded into the statements
of its derivation. That doesn't work for a recursive predicate, because
the expansion would never end. Instead, a call to a recursive predicate
is flattened into a search for its facts, like a call to a stored
predicate, and after the query is reordered we replace the search with an
evaluation that derives the facts it needs. For a call

  P { "a", X }

we generate

  rec ( _ = Demand_P_bf <- { "a" } )       -- 1. record what the call needs
    ( ... )                                 -- 2. derive it
    yield ( ... )                           -- 3. produce the facts found

1. The binding pattern of the call says which fields of the key are
   bound when the call runs: here the first field is bound (b) and the
   second is free (f). We only know it after reordering, which is why
   this happens after reordering. For each recursive predicate and
   binding pattern there is a Demand predicate, whose facts are the
   values of the bound fields that we need facts of P for. It only
   exists while the query runs.

2. For each recursive predicate and binding pattern there are queries
   deriving the facts of P that match its demands. The first one runs the
   derivation of P for a demand:

     { Key, Value, D } where
       D = Demand_P_bf { A };
       <derivation of P, with its first field set to A>

   Calls to recursive predicates inside it are treated in the same way:
   the call creates a demand. If the predicate is in the same component
   of mutually recursive predicates (see 'RecursiveComponent'), the
   derivation is suspended at the call, and other queries resume it when
   facts are derived for the demand (see Note [Suspension]). We also need
   the queries for the call's binding pattern, and so on until we have
   them all. The queries of a component are evaluated together by
   CgRec: it runs them in rounds, creating a fact for each result,
   until a round derives no new facts, including no new demands (see
   Note [Semi-naive evaluation]).

   A call to a predicate of another component, which must be a lower
   one, gets its own rec statement, so that component is complete
   for the demand before the call's results are used. In particular a
   negated recursive predicate is complete before it is negated, since
   stratification (see Note [Stratification] in Glean.Database.Schema)
   guarantees that it is in a lower component.

   The facts are created from the results of the queries rather than by
   a statement in them, because the statement could be reordered before
   a filter and create facts that aren't true (see
   Note [Writing derived facts] in Glean.Query.UserQuery). Those facts
   would then be used to derive more.

3. After each round, the facts derived for the call in that round are
   matched against the call's pattern, and the rest of the query runs for
   each of them before the next round (Note [Streaming]).

This is the Magic Sets transformation: evaluation is bottom-up, but only
derives facts that are relevant to the call. The binding patterns come
from the final order of the statements, so the result is correct
whatever the order; the order only decides how much gets derived.
-}

{- Note [Streaming]

A call to a recursive predicate is a generator (section 2 of the design):
its results come out as they are derived, not after its evaluation has
finished. We schedule by rounds: after each round of the evaluation, the
rest of the query runs for each fact that the round derived for the
call, and then the next round starts.

The facts derived for the call are those with a new Supply fact for the
call's demand. A Supply fact is only created once, however many ways its
fact is derived, so each fact is produced once (unique production,
section 11 of the design). The same statements that find the facts for a
suspended derivation (Note [Suspension]) look them up and match them
against the call's pattern, which can be more specific than the binding
pattern.

We find them by going through the round's new Supply facts and keeping
those for the call's demand, rather than by searching for the Supply
facts of the demand in the round. A search with a key prefix in a range
of ids goes through every fact with that prefix and skips those outside
the range (FactSet::seekWithinSection), so each round would go through
every fact derived for the call so far, which is quadratic in the number
of rounds. Going through the round's new Supply facts uses the index of
facts by id, and over the whole evaluation goes through each Supply fact
once.

Streaming lets a query stop an evaluation early, e.g. a negation stops at
its first result, and a query that reaches a limit returns the results it
has (it can't be continued, see noContinuation in Glean.Query.UserQuery).
It also means that the rest of the query can run a call with a
demand that the evaluation still in progress has created, which is why
evaluations are isolated (Note [Isolation]).
-}

{- Note [Suspension]

When a derivation calls a predicate of its own component, the facts it
needs may not have been derived yet. Instead of searching for them, the
derivation stops there, and is resumed once for each fact derived for the
call (sections 6 to 8 of the design). For

  P { A, B } where Edge { A, K }; (Q { K, X } | ...); Label { X, B }

the query deriving the facts for new demands becomes

  D0 = Demand_P[new] _;
  D0 = Demand_P { A };
  Edge { A, K };
  ( ( D1 = Demand_Q <- { K };
      _ = Suspended_1 <- { D1, K, A, D0 };
      fail ) | ... );
  Label { X, B }

and the query resuming it after the call is

  ( ( Supply_Q[new] { D1, F }; Suspended_1 { D1, K, A, D0 } )
  | ( Suspended_1[new] { D1, K, A, D0 }; Supply_Q[old] { D1, F } ) );
  F = Q { K, X };       -- the fact derived for the call
  Label { X, B }        -- the rest of the derivation

* Every fact derived for a demand D of P comes with a Supply_P { D, Fact }
  fact. Resuming a suspension compares demand fact ids rather than the
  keys of the facts (demand factoring, section 8).

* A Suspended fact holds the call's demand and the variables that the
  rest of the derivation needs: those bound before the call that are used
  by the call's pattern, by the statements after it, or by the result
  (sideways information passing, section 7). The demand D0 being derived
  is always among them, since it's part of the result.

* The rest of the derivation is everything that runs after the call: the
  rest of the statements around it, then the rest of the statements
  around those, and so on outwards. Alternatives of a disjunction or of
  an if that weren't taken never run again, so it is a flat list of
  statements wherever the call is. Calls in it are suspended in the same
  way.

* Each pair of a Supply fact and a Suspended fact for the same demand
  resumes the derivation exactly once: in the round after the later of
  the two was created. That relies on a round only seeing the facts
  derived before it started, see Note [Semi-naive evaluation].

D0 must be bound before any call is suspended, and the derivation is
reordered before we know which demands it is for. So we tell the
reorderer that D0 is bound, which makes D0 = Demand_P { A } a lookup,
and then bind D0 with a search for new demands before the rest of the
query.
-}

{- Note [Semi-naive evaluation]

A round of a saturation only does work that can derive something new
(section 5 of the design):

* the queries deriving facts for demands only run for the new demands;
* the queries resuming suspended derivations (Note [Suspension]) only
  consider pairs of a Supply fact and a Suspended fact where one of them
  is new.

Facts are never removed and new facts get increasing ids, so the facts
derived in a round are a range of ids. At the start of a round,
CgRec sets the range of the previous round, and the searches of the
queries find the facts derived in it (SeekOnRoundNew), before it
(SeekOnRoundOld), or in both (SeekOnRoundAll). So these searches don't
see the facts derived during the current round (the snapshot of section
1); they are new in the next round.

The first round starts before the statements that create the demand of
the call (the first argument of the design's two-argument rec), so it
only looks at that demand. The demand is always new, since each
evaluation starts with an empty store (Note [Isolation]).
-}

{- Note [Isolation]

Each evaluation of a call to a recursive predicate (each CgRec, the
design's rec) keeps its auxiliary facts -- demands, Supply facts and
Suspended facts -- in a store of its own (section 10 of the design). The
store is freed when the evaluation finishes (section 12).

This matters because results stream out of an evaluation before it
finishes (Note [Streaming]): another evaluation with the same demand could
find the demand already there, take it as fully evaluated, and miss
results. It also keeps
the auxiliary facts of different evaluations from filling up the query's
fact set.

The facts of the recursive predicates themselves are shared: they go in the
query's fact set like any other derived facts, since they are the results.
Whether a demand has been fully evaluated is only recorded by the auxiliary
facts, so sharing derived facts can't make an evaluation stop early.

The cost is that evaluations no longer share work: a call with a demand
that an earlier call evaluated derives its facts again. Caching completed
demands (section 14) can bring the sharing back.

A store lives on the query's iterator stack, so an evaluation that is left
early (e.g. when a negation finds a result) frees its store together with
its iterators. The auxiliary predicates of a component are listed in its
CgRec, and code generation routes their facts, searches and lookups
to the store of the evaluation being compiled.
-}

{- Note [Caching]

Isolated evaluations (Note [Isolation]) don't share work, so a query that
calls a recursive predicate many times with the same demand would derive
the same facts each time. Section 14 of the design caches completed
demands instead:

* When an evaluation reaches its fixpoint, every demand in its store has
  been fully evaluated -- the demand of the call and every demand created
  while evaluating it. So before freeing the store, it creates a
  Completed fact for each of them, with the same key as the demand. There
  is a Completed predicate for each predicate and binding pattern, like
  Demand, but its facts go in the query's fact set, where they outlive the
  evaluation.

* A call first looks for a Completed fact for its demand. If there is one,
  the facts it needs are all there, so it just searches for them:

    if (Completed_P_bf { "a" }) then P { "a", X } else <evaluate>

  A call to the predicate's own component, inside a derivation, does the
  same instead of suspending. That lets an evaluation use the subgoals
  that earlier evaluations completed.

An evaluation that is left early (e.g. by a negation that found a result)
completes nothing, so a later call with the same demand evaluates it.
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
    , exDemands = Map.empty
    , exSupplies = Map.empty
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
  , exDemands :: Map Call PidRef
    -- ^ the Demand predicate for each call
  , exSupplies :: Map Call PidRef
    -- ^ the Supply predicate for each call
  , exDerivations :: Map Call ([CgDerivation], Set Call)
    -- ^ the queries deriving the facts demanded by each call, and the
    -- calls they make to predicates of their own component
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

-- | Expand the calls to recursive predicates in a query, which derives
-- facts of the given component if it is one of the saturation queries.
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

-- | The statements that replace a search for facts: if it's a call to a
-- recursive predicate whose demand hasn't been completed (Note [Caching]),
-- create its demand, and either evaluate it or, if the query we are in is
-- evaluating the same component, leave the search for suspension
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
      demand <- lift $ demandPredicate this
      fid <- freshVar (Angle.PredicateTy () demand)
      completed <- lift $ completedPredicate this
      let
        create = CgStatement (Ref (MatchBind fid))
          (DerivedFactGenerator demand demandKey (Tuple []))
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
          complete <- mapM completeDemands (Set.toList calls)
          auxiliary <- lift $ gets $
            IntMap.findWithDefault [] (componentIndex component) . exAuxiliary
          supply <- lift $ supplyPredicate this
          fact <- freshVar (Angle.PredicateTy () (pidRef details))
          suppliedFor <- freshVar (Angle.PredicateTy () demand)
          let
            -- the facts derived for the call in the round: the round's new
            -- Supply facts, then those for the call's demand. Not a search
            -- for the demand's Supply facts, see Note [Streaming].
            supplied =
              [ CgStatement
                  (Ref (MatchWild (Angle.PredicateTy () supply)))
                  (FactGenerator supply
                    (Tuple [Ref (MatchBind suppliedFor), Ref (MatchBind fact)])
                    (Tuple [])
                    SeekOnRoundNew)
              , CgStatement (Ref (MatchVar suppliedFor))
                  (TermGenerator (Ref (MatchVar fid)))
              ]
          return
            [ ifCompleted
                [ CgRec [create] derivations auxiliary
                    (supplied <> found search fact) complete ]
            ]

-- | The statements marking every demand of a call in an evaluation's
-- store as completed. See Note [Caching].
completeDemands :: Call -> V [CgStatement]
completeDemands this = do
  demand <- lift $ demandPredicate this
  completed <- lift $ completedPredicate this
  demandDetails <- lift $ getDetails (pidRefId demand)
  key <- freshVar (predicateKeyType demandDetails)
  done <- freshVar (Angle.PredicateTy () completed)
  return
    [ CgStatement (Ref (MatchWild (Angle.PredicateTy () demand)))
        (FactGenerator demand (Ref (MatchBind key)) (Tuple []) SeekOnAllFacts)
    -- a DerivedFactGenerator whose result isn't bound creates nothing
    , CgStatement (Ref (MatchBind done))
        (DerivedFactGenerator completed (Ref (MatchVar key)) (Tuple []))
    ]
  where
  pidRefId (PidRef _ ref) = ref

freshVar :: Monad m => Type -> StateT Int m Var
freshVar ty = do
  n <- get
  put (n + 1)
  return (Var ty n Nothing)

-- | The binding pattern of a call with the given key pattern, and the
-- key of its demand: the values of the bound fields.
--
-- A field is bound when its pattern can't bind any variables, so it is
-- an expression whose value is known when the search runs. Anything else
-- is treated as free, which is always correct but can derive more
-- facts than necessary.
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

-- | The Demand predicate for a call: its key holds the values of the
-- bound fields of the key of the predicate.
demandPredicate :: Call -> E PidRef
demandPredicate this@(ref, binding) = do
  existing <- gets (Map.lookup this . exDemands)
  case existing of
    Just demand -> return demand
    Nothing -> do
      details <- getDetails ref
      let
        keyTy = predicateKeyType details
        demandTy = case fields keyTy of
          Just fs -> Angle.RecordTy [ f | (f, True) <- zip fs binding ]
          Nothing
            | and binding -> keyTy
            | otherwise -> Angle.RecordTy []
      demand <- auxiliaryPredicate this (callName "demand" this) demandTy
      modify $ \s -> s { exDemands = Map.insert this demand (exDemands s) }
      return demand

-- | The Supply predicate for a call: which demand each fact derived for
-- it was for. See Note [Suspension].
supplyPredicate :: Call -> E PidRef
supplyPredicate this@(ref, _) = do
  existing <- gets (Map.lookup this . exSupplies)
  case existing of
    Just supply -> return supply
    Nothing -> do
      details <- getDetails ref
      demand <- demandPredicate this
      supply <- auxiliaryPredicate this (callName "supply" this) $
        Angle.RecordTy
        [ Angle.FieldDef "demand" (Angle.PredicateTy () demand)
        , Angle.FieldDef "fact" (Angle.PredicateTy () (pidRef details))
        ]
      modify $ \s -> s { exSupplies = Map.insert this supply (exSupplies s) }
      return supply

-- | e.g. @demand:x.Path.1:bf@
callName :: Text -> Call -> Text
callName kind (ref, binding) =
  kind <> ":" <> showRef (predicateIdRef ref) <> ":" <>
  Text.pack [ if bound then 'b' else 'f' | bound <- binding ]

-- | The Completed predicate for a call: which of its demands have been
-- fully evaluated. See Note [Caching].
completedPredicate :: Call -> E PidRef
completedPredicate this = do
  existing <- gets (Map.lookup this . exCompleted)
  case existing of
    Just completed -> return completed
    Nothing -> do
      PidRef _ demandRef <- demandPredicate this
      demandDetails <- getDetails demandRef
      completed <- newPredicate (callName "completed" this)
        (predicateKeyType demandDetails)
      modify $ \s ->
        s { exCompleted = Map.insert this completed (exCompleted s) }
      return completed

-- | A predicate for the evaluation of the component of a call, whose facts
-- live in the evaluation's store. See Note [Isolation].
auxiliaryPredicate :: Call -> Text -> Type -> E PidRef
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

-- | A predicate that only exists while the query runs
newPredicate :: Text -> Type -> E PidRef
newPredicate name keyTy = do
  pid <- gets exNextPid
  let
    ref = queryPredicateId name
    details = PredicateDetails
      { predicatePid = pid
      , predicateId = ref
      , predicateSchema = error "auxiliary predicate: predicateSchema"
      , predicateKeyType = keyTy
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

-- | The queries deriving the facts demanded by a call, and by the calls
-- they make to predicates of the same component, transitively, and all
-- those calls.
componentDerivations :: Call -> E ([CgDerivation], Set Call)
componentDerivations start = go [start] Set.empty []
  where
  go [] done acc = return (concat (reverse acc), done)
  go (this : rest) done acc
    | this `Set.member` done = go rest done acc
    | otherwise = do
      (derivations, required) <- derivationsFor this
      go (rest <> Set.toList required) (Set.insert this done)
        (derivations : acc)

-- | The queries deriving the facts demanded by a call.
derivationsFor :: Call -> E ([CgDerivation], Set Call)
derivationsFor this@(ref, binding) = do
  existing <- gets (Map.lookup this . exDerivations)
  case existing of
    Just result -> return result
    Nothing -> do
      details <- getDetails ref
      component <- gets (HashMap.lookup ref . recursiveComponents . exSchema)
      demand <- demandPredicate this
      supply <- supplyPredicate this
      dbSchema <- gets exSchema
      compile <- gets exCompile
      query <- liftEither $ runExcept $ do
        (flat, d0) <- flattenDerivation dbSchema ref demand binding
        compile dbSchema [d0] flat
      -- expand the calls inside it, collecting those to its own component
      outer <- gets $ \s -> (exRequired s, exOwnCalls s)
      modify $ \s -> s { exRequired = Set.empty, exOwnCalls = IntMap.empty }
      expanded <- expandQuery (componentIndex <$> component) query
      required <- gets exRequired
      ownCalls <- gets exOwnCalls
      modify $ \s -> s { exRequired = fst outer, exOwnCalls = snd outer }
      queries <- suspend this demand expanded ownCalls
      let
        result =
          ( [ CgDerivation (pidRef details) supply q | q <- queries ]
          , required )
      modify $ \s ->
        s { exDerivations = Map.insert this result (exDerivations s) }
      return result

-- | A call to the component being derived: the variable of the demand fact
-- it creates, the search for its facts, and what runs after the search.
data Site = Site
  { siteDemand :: Var
  , siteCall :: Call
  , siteSearch :: CgStatement
  , siteRest :: [CgStatement]
  }

-- | A call where the derivation is suspended
data Suspension = Suspension
  { suspSite :: Site
  , suspPredicate :: PidRef
  , suspLive :: [Var]
    -- ^ the variables that the rest of the derivation needs
  , suspVar :: Var
    -- ^ for the Suspended fact
  }

-- | The queries deriving the facts demanded by a call: one running the
-- derivation for new demands, and one resuming it after each call it makes
-- to its own component. See Note [Suspension].
suspend
  :: Call            -- ^ the call it derives facts for
  -> PidRef          -- ^ its Demand predicate
  -> CodegenQuery    -- ^ the derivation
  -> IntMap Call     -- ^ calls to its own component, see exOwnCalls
  -> E [CodegenQuery]
suspend this demand query ownCalls = do
  let QueryWithInfo (CgQuery result stmts) numVars _ _ = query
  d0 <- case result of
    Tuple [_, _, Ref (MatchVar d0)] -> return d0
    _ -> throwError "internal error: suspend: unexpected result"
  sites <- liftEither $ callSites ownCalls stmts []
  demandDetails <- getDetails (pidRefId demand)
  flip evalStateT numVars $ do
    suspensions <- forM (zip [0 :: Int ..] sites) $ \(n, site) -> do
      let
        live = liveVars (siteSearch site : siteRest site) result
        demandTy = varType (siteDemand site)
      predicate <- lift $ auxiliaryPredicate this
        (callName "suspended" this <> ":" <> Text.pack (show n))
        (Angle.RecordTy
          [ Angle.FieldDef (Text.pack ("f" <> show i)) ty
          | (i, ty) <- zip [0 :: Int ..] (demandTy : map varType live) ])
      var <- freshVar (Angle.PredicateTy () predicate)
      return (Suspension site predicate live var)
    let
      byDemand = IntMap.fromList
        [ (varId (siteDemand (suspSite s)), s) | s <- suspensions ]
      demandSearch = CgStatement (Ref (MatchBind d0))
        (FactGenerator demand (Ref (MatchWild (predicateKeyType demandDetails)))
          (Tuple []) SeekOnRoundNew)
      first = demandSearch : suspendCalls byDemand stmts
    resumes <- forM suspensions $ resume byDemand
    numVars' <- get
    return
      [ query
          { qiQuery = CgQuery result body
          , qiNumVars = numVars'
          }
      | body <- first : resumes
      ]
  where
  pidRefId (PidRef _ ref) = ref

-- | The query resuming a derivation after a call. See Note [Suspension].
resume :: IntMap Suspension -> Suspension -> V [CgStatement]
resume suspensions Suspension{..} = do
  let Site{..} = suspSite
  called <- case siteSearch of
    CgStatement _ (FactGenerator called _ _ _) -> return called
    _ -> throwError "internal error: resume: unexpected call"
  supply <- lift $ supplyPredicate siteCall
  fact <- freshVar (Angle.PredicateTy () called)
  let
    bind = Ref . MatchBind
    use = Ref . MatchVar
    wild pid = Ref (MatchWild (Angle.PredicateTy () pid))
    suspended demand section =
      CgStatement (wild suspPredicate)
        (FactGenerator suspPredicate (Tuple (demand : map bind suspLive))
          (Tuple []) section)
    supplied demand section =
      CgStatement (wild supply)
        (FactGenerator supply (Tuple [demand, bind fact]) (Tuple []) section)
    -- each pair of a Supply and a Suspended fact where one is new
    resumed = CgDisjunction
      [ [ supplied (bind siteDemand) SeekOnRoundNew
        , suspended (use siteDemand) SeekOnRoundAll ]
      , [ suspended (bind siteDemand) SeekOnRoundNew
        , supplied (use siteDemand) SeekOnRoundOld ]
      ]
  return (resumed : found siteSearch fact <> suspendCalls suspensions siteRest)

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

-- | Replace the calls to the component being derived with a suspension:
-- create the demand, record what the rest of the derivation needs, and
-- stop.
suspendCalls :: IntMap Suspension -> [CgStatement] -> [CgStatement]
suspendCalls suspensions = go
  where
  go [] = []
  go (stmt : rest) = case stmt of
    CgStatement (Ref (MatchBind var)) DerivedFactGenerator{}
      | Just Suspension{..} <- IntMap.lookup (varId var) suspensions ->
        [ stmt
        , CgStatement (Ref (MatchBind suspVar))
            (DerivedFactGenerator suspPredicate
              (Tuple (map (Ref . MatchVar) (var : suspLive)))
              (Tuple []))
        , CgDisjunction []  -- fail
        ]
    CgDisjunction stmtss -> CgDisjunction (map go stmtss) : go rest
    CgConditional cond then_ else_ ->
      CgConditional cond (go then_) (go else_) : go rest
    _ -> stmt : go rest

-- | The calls to the component being derived, with what runs after each:
-- the rest of the statements around it, then the rest of the statements
-- around those, and so on outwards.
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
