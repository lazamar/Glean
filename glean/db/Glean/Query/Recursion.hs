{-
  Copyright (c) Meta Platforms, Inc. and affiliates.
  All rights reserved.

  This source code is licensed under the BSD-style license found in the
  LICENSE file in the root directory of this source tree.
-}

module Glean.Query.Recursion
  ( expandRecursion
  ) where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.HashMap.Strict as HashMap
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Glean.Angle.Hash (hash0)
import Glean.Angle.Types (PredicateId(..), DerivingInfo(..))
import qualified Glean.Angle.Types as Angle
import Glean.Database.Schema.Types
import Glean.Display
import Glean.Query.Codegen.Types
import Glean.Query.Flatten (flattenDerivation)
import Glean.Query.Flatten.Types (FlattenedQuery)
import Glean.RTS.Term (Term(..))
import Glean.Schema.Util (showRef)
import Glean.RTS.Types (Pid(..), PidRef(..), Type, FieldDef, derefType)
import Glean.Types (PredicateRef(..))

{- Note [Evaluating recursive predicates]

A call to a derived predicate is normally expanded into the statements
of its derivation. That doesn't work for a recursive predicate, because
the expansion would never end. Instead, a call to a recursive predicate
is flattened into a search for its facts, like a call to a stored
predicate, and after the query is reordered we derive the facts that
the search needs just before it. For a call

  P { "a", X }

we generate

  _ = Demand_P_bf <- { "a" };  -- 1. record what the call needs
  rec ( ... );                 -- 2. derive it
  P { "a", X }                 -- 3. search for it

1. The binding pattern of the call says which fields of the key are
   bound when the call runs: here the first field is bound (b) and the
   second is free (f). We only know it after reordering, which is why
   this happens after reordering. For each recursive predicate and
   binding pattern there is a Demand predicate, whose facts are the
   values of the bound fields that we need facts of P for. It only
   exists while the query runs.

2. For each recursive predicate and binding pattern there is a query
   returning the key and value of the facts of P that match a demand:

     { Key, Value } where
       Demand_P_bf { A };
       <derivation of P, with its first field set to A>

   References to recursive predicates inside it are treated in the same
   way: the call creates a demand and searches for the facts derived so
   far. If the predicate is in the same component of mutually recursive
   predicates (see 'RecursiveComponent'), we also need the query for its
   binding pattern, and so on until we have them all. The queries of a
   component are evaluated together by CgRec: it runs them
   repeatedly, creating a fact for each result, until a round derives no
   new facts, including no new demands.

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

3. The search then finds the facts that match the call.

This is the Magic Sets transformation: evaluation is bottom-up, but only
derives facts that are relevant to the call. The binding patterns come
from the final order of the statements, so the result is correct
whatever the order; the order only decides how much gets derived.

Every round of a saturation looks at all the facts derived so far, and
results only arrive once the saturation is complete. Demands and facts
derived for a call are kept for the rest of the query, so later calls
that need the same facts find them already derived.
-}

{- Note [Semi-naive evaluation]

Re-running the queries of a saturation for every demand in every round
repeats work: a round can only derive something new for a demand if the
demand is new, or if the previous round derived new facts of the
predicates being derived. So a round only looks at (section 5 of the
design):

  Demand[new] | (P[new] _; Demand[old])

that is, the new demands, and also the old ones if there are new facts
of the predicates being derived. Facts are never removed and new facts
get increasing ids, so "new" means "with an id from the first free id at
the start of the previous round", and the demands to look at are a range
of ids: from the start of the previous round, or from the beginning if
there were new facts of the predicates being derived. CgRec
computes the range at the start of each round, and the derivation
queries search for demands with SeekOnRound, which searches within it.

The first round starts before the statements that create the demand of
the call (the first argument of the design's two-argument rec), so it
only looks at that demand. If the demand already existed, nothing is new
and the saturation stops straight away: the facts it needs were derived
by an earlier call.

A search can miss facts that are derived while it is in progress (see
FactSet::seek). That's fine: a missed fact is new in the next round.
-}

-- | Derive the facts of the recursive predicates that a query searches
-- for. See Note [Evaluating recursive predicates].
expandRecursion
  :: DbSchema
  -> (DbSchema -> FlattenedQuery -> Except Text CodegenQuery)
     -- ^ optimise and reorder a query
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
    , exDerivations = Map.empty
    , exRequired = Set.empty
    }

-- | Which fields of the key of a predicate are bound at a call. For a
-- key that isn't a record there is only one field: the whole key.
type BindingPattern = [Bool]

type Call = (PredicateId, BindingPattern)

-- | A query deriving facts of a predicate, see CgRec.
type Derivation = (PidRef, CodegenQuery)

data ExpandState = ExpandState
  { exSchema :: DbSchema
    -- ^ including the Demand predicates created so far
  , exCompile :: DbSchema -> FlattenedQuery -> Except Text CodegenQuery
  , exNextPid :: Pid
  , exDemands :: Map Call PidRef
    -- ^ the Demand predicate for each call
  , exDerivations :: Map Call (Derivation, Set Call)
    -- ^ the query deriving the facts demanded by each call, and the
    -- calls it makes to predicates of its own component
  , exRequired :: Set Call
    -- ^ calls made to predicates of the component we are generating a
    -- query for
  }

type E a = StateT ExpandState (Except Text) a

-- | Fresh variables for the query we are expanding.
type V a = StateT Int (StateT ExpandState (Except Text)) a

-- | Expand the calls to recursive predicates in a query, which derives
-- facts of the given component if it is one of the saturation queries.
expandQuery :: Maybe Int -> CodegenQuery -> E CodegenQuery
expandQuery inside query@QueryWithInfo{..} = do
  let CgQuery hd stmts = qiQuery
  ((stmts', lookup), numVars) <- flip runStateT qiNumVars $ do
    stmts' <- expandStmts inside stmts
    -- The generator of the result is searched after the statements, see
    -- compileQuery.
    lookup <- case qiGenerator of
      Just (FactGenerator (PidRef _ ref) key _ _) -> call inside ref key
      _ -> return []
    return (stmts', lookup)
  return query
    { qiQuery = CgQuery hd (stmts' <> lookup)
    , qiNumVars = numVars
    }

expandStmts :: Maybe Int -> [CgStatement] -> V [CgStatement]
expandStmts inside = fmap concat . mapM expandStmt
  where
  expandStmt stmt = case stmt of
    CgStatement _ (FactGenerator (PidRef _ ref) key _ _) -> do
      before <- call inside ref key
      return (before <> [stmt])
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

-- | The statements to run before searching for facts of a predicate
-- with a key pattern: create the demand, and derive the facts unless
-- that is being done by the query we are in.
call :: Maybe Int -> PredicateId -> Pat -> V [CgStatement]
call inside ref key = do
  dbSchema <- lift $ gets exSchema
  case HashMap.lookup ref (recursiveComponents dbSchema) of
    Nothing -> return []
    Just component -> do
      details <- lift $ getDetails ref
      let
        (binding, demandKey) = bindingPattern (predicateKeyType details) key
        this = (ref, binding)
      demand <- lift $ demandPredicate this
      fid <- freshVar (Angle.PredicateTy () demand)
      let
        create = CgStatement (Ref (MatchBind fid))
          (DerivedFactGenerator demand demandKey (Tuple []))
      if inside == Just (componentIndex component)
        then do
          lift $ modify $ \s ->
            s { exRequired = Set.insert this (exRequired s) }
          return [create]
        else do
          derivations <- lift $ componentDerivations this
          return [CgRec [create] derivations]

freshVar :: Type -> V Var
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
      pid <- gets exNextPid
      let
        keyTy = predicateKeyType details
        demandTy = case fields keyTy of
          Just fs -> Angle.RecordTy [ f | (f, True) <- zip fs binding ]
          Nothing
            | and binding -> keyTy
            | otherwise -> Angle.RecordTy []
        demandId = PredicateId
          (PredicateRef (demandName ref binding) 0)
          hash0
        demand = PidRef pid demandId
        demandDetails = PredicateDetails
          { predicatePid = pid
          , predicateId = demandId
          , predicateSchema = error "demand predicate: predicateSchema"
          , predicateKeyType = demandTy
          , predicateValueType = Angle.RecordTy []
          , predicateTypecheck = error "demand predicate: predicateTypecheck"
          , predicateTraversal = error "demand predicate: predicateTraversal"
          , predicateDeriving = NoDeriving
          , predicateInStoredSchema = False
          }
      modify $ \s -> s
        { exNextPid = succ pid
        , exDemands = Map.insert this demand (exDemands s)
        , exSchema = addPredicate demandDetails (exSchema s)
        }
      return demand

-- | e.g. @demand:x.Path.1:bf@
demandName :: PredicateId -> BindingPattern -> Text
demandName ref binding =
  "demand:" <> showRef (predicateIdRef ref) <>
  ":" <> Text.pack [ if bound then 'b' else 'f' | bound <- binding ]

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
-- they make to predicates of the same component, transitively.
componentDerivations :: Call -> E [Derivation]
componentDerivations start = go [start] Set.empty []
  where
  go [] _ acc = return (reverse acc)
  go (this : rest) done acc
    | this `Set.member` done = go rest done acc
    | otherwise = do
      (derivation, required) <- derivationFor this
      go (rest <> Set.toList required) (Set.insert this done)
        (derivation : acc)

-- | The query deriving the facts demanded by a call.
derivationFor :: Call -> E (Derivation, Set Call)
derivationFor this@(ref, binding) = do
  existing <- gets (Map.lookup this . exDerivations)
  case existing of
    Just result -> return result
    Nothing -> do
      details <- getDetails ref
      component <- gets (HashMap.lookup ref . recursiveComponents . exSchema)
      demand <- demandPredicate this
      dbSchema <- gets exSchema
      compile <- gets exCompile
      query <- liftEither $ runExcept $ do
        flat <- flattenDerivation dbSchema ref demand binding
        compile dbSchema flat
      -- collect the calls to its own component
      outer <- gets exRequired
      modify $ \s -> s { exRequired = Set.empty }
      query' <- expandQuery (componentIndex <$> component) query
      required <- gets exRequired
      modify $ \s -> s { exRequired = outer }
      let
        result =
          ((PidRef (predicatePid details) (predicateId details), query'),
            required)
      modify $ \s ->
        s { exDerivations = Map.insert this result (exDerivations s) }
      return result
