{-
  Copyright (c) Meta Platforms, Inc. and affiliates.
  All rights reserved.

  This source code is licensed under the BSD-style license found in the
  LICENSE file in the root directory of this source tree.
-}

module Glean.Query.UserQuery
  ( userQueryFacts
  , userQuery
  , userQueryWrites
  , schemaVersionForQuery
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.Except
import Data.Bifoldable (bifoldMap)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Coerce
import Data.Default
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (hash)
import Data.Int
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Compat.Prettyprinter hiding ((<>))
import Compat.Prettyprinter.Render.Text
import qualified Data.Vector as Vector
import Data.Vector (Vector)
import qualified Data.Vector.Storable as VS
import Data.Word (Word64)
import System.IO
import TextShow

import ServiceData.GlobalStats as Stats
import qualified ServiceData.Types as Stats
import Util.AllocLimit
import Util.Timing
import Util.Log
import Util.STM

import Glean.Display
import qualified Glean.Angle.Parser as Angle
import Glean.Angle.Types hiding (Type, FieldDef, SourcePat_(..))
import qualified Glean.Angle.Types as Angle
import qualified Glean.Internal.Types as Thrift
import qualified Glean.Backend.Types as Backend
import Glean.Schema.Types
  (RefTarget(..), LookupResult(..), NameEnv, resolveRef)
import qualified Glean.Database.Catalog as Catalog
import Glean.Database.Schema (addLocalPredicates)
import Glean.Database.Schema.Types
import Glean.Database.Open
import qualified Glean.Database.PredicateStats as PredicateStats
import Glean.Database.Types as Database
import Glean.Database.Writes
import Glean.FFI
import Glean.Query.Codegen
import Glean.Query.Codegen.Types hiding (Match(..))
import Glean.Query.Transform
import Glean.Query.Flatten
import Glean.Query.Opt
import Glean.Query.Reorder
import Glean.Query.Incremental (makeIncremental)
import Glean.Query.Recursion (expandRecursion)
import Glean.RTS as RTS
import Glean.RTS.Bytecode.Disassemble
import qualified Glean.RTS.Bytecode.Gen.Version as Bytecode
import qualified Glean.RTS.Foreign.Bytecode as Bytecode
import Glean.RTS.Foreign.FactSet (FactSet)
import qualified Glean.RTS.Foreign.FactSet as FactSet
import Glean.RTS.Foreign.Lookup
import Glean.RTS.Foreign.Ownership
import Glean.RTS.Foreign.Query
import Glean.RTS.Foreign.Stacked (stacked)
import Glean.RTS.Types (Type, PidRef(..))
import qualified Glean.Types as Thrift
import qualified Glean.ServerConfig.Types as ServerConfig
import Glean.Query.JSON
import Glean.Schema.Resolve
import Glean.Schema.Util
import Glean.Util.Observed as Observed
import Glean.Query.Typecheck
import Glean.Bytecode.SysCalls (userQuerySysCalls)
import Glean.Types (UserQueryCont)
import qualified Glean.Backend.Types as StackedDbOpts
import Glean.Util.Some
import Glean.Query.Typecheck.Types (TcPred)
-- NOTE: We keep the public interface monomorphic, at least for now.

--
-- | Perform a query using the JSON query syntax, and return the results
-- as JSON-encoded Thrift data.
--
userQuery
  :: Database.Env
  -> Thrift.Repo
  -> Thrift.UserQuery
  -> IO Thrift.UserQueryResults
userQuery env repo query = chooseEncoding
  (Thrift.userQuery_options query)
  (Thrift.userQuery_encodings query)
  $ genericUserQuery env repo query

--
-- | Query a list of facts and return the result as JSON-encoded Thrift data.
--
userQueryFacts
  :: Database.Env
  -> Thrift.Repo
  -> Thrift.UserQueryFacts
  -> IO Thrift.UserQueryResults
userQueryFacts env repo query = chooseEncoding
  (Thrift.userQueryFacts_options query)
  (Thrift.userQueryFacts_encodings query)
  $ genericUserQueryFacts env repo query

-- | A generic implementation of scan queries.
genericUserQuery
  :: Encoding e
  => Database.Env
  -> Thrift.Repo
  -> Thrift.UserQuery
  -> e
  -> IO Thrift.UserQueryResults
{-# INLINE genericUserQuery #-}
genericUserQuery env repo query enc = do
  config@ServerConfig.Config{..} <- Observed.get (envServerConfig env)
  checkAclsEnabled <- envAclCheckEnabled env
  readDatabaseWithBoundaries env repo checkAclsEnabled $ \odb bounds lookup ->
    maybe id limitAllocsThrow config_query_alloc_limit
      $ performUserQuery enc (odbSchema odb) $
          userQueryImpl env odb config
            NoExtraSteps bounds lookup repo query

-- | A generic implementation of lookup queries.
genericUserQueryFacts
  :: Encoding e
  => Database.Env
  -> Thrift.Repo
  -> Thrift.UserQueryFacts
  -> e
  -> IO Thrift.UserQueryResults
{-# INLINE genericUserQueryFacts #-}
genericUserQueryFacts env repo query enc = do
  config <- Observed.get (envServerConfig env)
  checkAclsEnabled <- envAclCheckEnabled env
  readDatabaseWithBoundaries env repo checkAclsEnabled $ \odb _bounds lookup ->
    performUserQuery enc (odbSchema odb) $
      userQueryFactsImpl (odbSchema odb) config lookup query

-- | Results returned from a query, parametrised of the types of facts and
-- statistics
data Results stats fact = Results
  { -- | Facts matching the query
    resFacts :: [(Fid, fact)]

    -- | Type of the results, if known
  , resPredicate :: Maybe PredicateDetails

    -- | Additional facts satisfying nested parts of the query
  , resNestedFacts :: IntMap fact

    -- | The predicates declared by the query, by Pid, which nested facts
    -- can belong to. See Note [Query-local predicates].
  , resLocalPredicates :: IntMap PredicateDetails

    -- | Continuation for paging
  , resCont :: Maybe Thrift.UserQueryCont

    -- | Statistics
  , resStats :: stats

    -- | Diagnostics
  , resDiags :: [Text]

    -- | Write handle for derived facts
  , resWriteHandle :: Maybe Thrift.Handle

    -- | Count of the facts searched per Pid
  , resFactsSearched :: Maybe (Map Int64 Int64)

    -- | Inferred type of the query, for logging
  , resType :: Maybe Text

    -- | Size of compiled bytecode, for logging
  , resBytecodeSize :: Maybe Int

    -- | Query compile time, for logging, in seconds
  , resCompileTime :: Maybe Double

  , resCodegenTime :: Maybe Double

    -- | Query execution time after compilation, for logging, in nanoseconds
  , resExecutionTime :: Maybe Word64

  -- | Size of query results, for logging
  , resResultBytes :: Maybe Int64
  }

class Encoding e where
  type EncodedFact e

  shouldExpand :: e -> Bool

  -- | Whether the encoding can have facts of the predicates declared by
  -- the query. Clients decode the other encodings with their own schema,
  -- which doesn't have them. See Note [Query-local predicates].
  encodesLocalFacts :: e -> Bool

  serializeFact
    :: e
    -> IntMap (EncodedFact e)
    -> Fid
    -> PredicateDetails
    -> Thrift.Fact
    -> IO (EncodedFact e)
  setResults
    :: e
    -> Results stats (EncodedFact e)
    -> Thrift.UserQueryResults
    -> Thrift.UserQueryResults

withEncoding
  :: Thrift.UserQueryEncoding
  -> (forall e. Encoding e => e -> a)
  -> Maybe a
{-# INLINE withEncoding #-}
withEncoding (Thrift.UserQueryEncoding_bin x) f = Just $ f x
withEncoding (Thrift.UserQueryEncoding_json x) f = Just $ f x
withEncoding (Thrift.UserQueryEncoding_compact x) f = Just $ f x
withEncoding (Thrift.UserQueryEncoding_listbin x) f = Just $ f x
withEncoding _ _ = Nothing

chooseEncoding
  :: Maybe Thrift.UserQueryOptions
  -> [Thrift.UserQueryEncoding]
  -> (forall e. Encoding e => e -> IO a)
  -> IO a
{-# INLINE chooseEncoding #-}
chooseEncoding mopts encs f = do
  forM_ (Thrift.userQueryOptions_continuation =<< mopts) checkUserQueryCont
  case encs of
    [] -> f $ LegacyJSONEncoding $ fromMaybe def mopts
    _ | act : _ <- mapMaybe (`withEncoding` f) encs -> act
      | otherwise -> throwIO $ Thrift.BadQuery
          "none of the requested encodings are supported"

newtype LegacyJSONEncoding = LegacyJSONEncoding Thrift.UserQueryOptions

instance Encoding LegacyJSONEncoding where
  type EncodedFact LegacyJSONEncoding = ByteString

  shouldExpand (LegacyJSONEncoding opts) =
    Thrift.userQueryOptions_expand_results opts

  encodesLocalFacts _ = True

  serializeFact
    (LegacyJSONEncoding opts)
    serialized
    fid
    predicateDetails
    Thrift.Fact{..} = factToJSON
      (Thrift.userQueryOptions_no_base64_binary opts)
      serialized
      predicateDetails
      fid
      fact_key
      fact_value

  setResults _ res qres = qres
      { Thrift.userQueryResults_facts = snd <$> resFacts res
      , Thrift.userQueryResults_nestedFacts = Map.fromList
          [ (fromIntegral i, fact)
            | (i,fact) <- IntMap.toList $ resNestedFacts res ]
      }

instance Encoding Thrift.UserQueryEncodingJSON where
  type EncodedFact Thrift.UserQueryEncodingJSON = ByteString

  shouldExpand = Thrift.userQueryEncodingJSON_expand_results

  encodesLocalFacts _ = True

  serializeFact enc serialized fid predicateDetails Thrift.Fact{..} =
    factToJSON
      (Thrift.userQueryEncodingJSON_no_base64_binary enc)
      serialized
      predicateDetails
      fid
      fact_key
      fact_value

  setResults enc res qres = qres
    { Thrift.userQueryResults_results = Thrift.UserQueryEncodedResults_json
        Thrift.UserQueryResultsJSON
          { userQueryResultsJSON_encoding = enc
          , userQueryResultsJSON_facts = snd <$> resFacts res
          , userQueryResultsJSON_nestedFacts = Map.fromList
              [ (fromIntegral i, fact)
                | (i,fact) <- IntMap.toList $ resNestedFacts res ]
          }
    }

instance Encoding Thrift.UserQueryEncodingCompact where
  type EncodedFact Thrift.UserQueryEncodingCompact = ByteString

  shouldExpand = Thrift.userQueryEncodingCompact_expand_results

  encodesLocalFacts _ = False

  serializeFact _ serialized fid predicateDetails Thrift.Fact{..} =
    factToCompact
      serialized
      predicateDetails
      fid
      fact_key
      fact_value

  setResults enc res qres = qres
    { Thrift.userQueryResults_results = Thrift.UserQueryEncodedResults_compact
        Thrift.UserQueryResultsCompact
          { userQueryResultsCompact_encoding = enc
          , userQueryResultsCompact_facts = snd <$> resFacts res
          , userQueryResultsCompact_nestedFacts = Map.fromList
              [ (fromIntegral i, fact)
                | (i,fact) <- IntMap.toList $ resNestedFacts res ]
          }
    }

instance Encoding Thrift.UserQueryEncodingBin where
  type EncodedFact Thrift.UserQueryEncodingBin = Thrift.Fact

  shouldExpand _ = False

  encodesLocalFacts _ = False

  serializeFact _ _ _ _ = return

  setResults enc res qres = qres
    { Thrift.userQueryResults_results = Thrift.UserQueryEncodedResults_bin
        Thrift.UserQueryResultsBin
          { userQueryResultsBin_encoding = enc
          , userQueryResultsBin_facts =
              Map.fromList
              $ coerce
              $ resFacts res
          , userQueryResultsBin_nestedFacts =
              Map.fromList
              $ map (first fromIntegral)
              $ IntMap.toList
              $ resNestedFacts res
          }
    }

instance Encoding Thrift.UserQueryEncodingListBin where
  type EncodedFact Thrift.UserQueryEncodingListBin = Thrift.Fact

  shouldExpand _ = False

  encodesLocalFacts _ = False

  serializeFact _ _ _ _ = return

  setResults enc res qres = qres
    { Thrift.userQueryResults_results = Thrift.UserQueryEncodedResults_listbin
        Thrift.UserQueryResultsListBin
          { userQueryResultsListBin_encoding = enc
          , userQueryResultsListBin_ids =
              coerce $ Vector.fromList (map fst (resFacts res))
          , userQueryResultsListBin_facts =
              Vector.fromList (map snd (resFacts res))
          , userQueryResultsListBin_nestedFacts =
              Map.fromList
              $ map (first fromIntegral)
              $ IntMap.toList
              $ resNestedFacts res
          }
    }

-- | Perform a query and convert the 'Results' to a Thrift result
performUserQuery
  :: Encoding e
  => e
  -> DbSchema
  -> IO (Results Stats Thrift.Fact)
  -> IO Thrift.UserQueryResults
{-# INLINE performUserQuery #-}
performUserQuery encoding schema query = do
  !results <- withStats $ do
    res <- query

    let
      factDetails ty =
        case IntMap.lookup (fromIntegral ty) (resLocalPredicates res) of
          Nothing -> pidDetails schema ty
          Just details
            | encodesLocalFacts encoding -> return details
            | otherwise -> throwIO $ Thrift.BadQuery $
              "the results have facts of predicates declared by the " <>
              "query, which only the JSON encoding can return"

    -- Convert nested facts - we do it in the order of their fact ids
    -- which means we can only depend on facts converted earlier.
    nested <- foldM
      (\expanded (fid, fact@Thrift.Fact{..}) -> do
          details <- factDetails fact_type
          encoded <- serializeFact
            encoding
            (if shouldExpand encoding then expanded else IntMap.empty)
            (Fid $ fromIntegral fid)
            details
            fact
          return $ IntMap.insert fid encoded expanded)
      IntMap.empty
      (IntMap.toList $ resNestedFacts res)

    let
      -- avoid lookupPid if we know the result type
      getDetails = case resPredicate res of
        Just d -> const (return d)
        Nothing -> pidDetails schema

    facts <- forM (resFacts res) $ \(i, fact) -> do
      details <- getDetails (Thrift.fact_type fact)
      enc <- serializeFact
        encoding
        (if shouldExpand encoding then nested else IntMap.empty)
        i
        details
        fact
      return (i,enc)

    return res
      { resFacts = facts
      , resNestedFacts = if shouldExpand encoding then IntMap.empty else nested
      }
  return $ setResults encoding results def
    { Thrift.userQueryResults_stats = Just $ resStats results
    , Thrift.userQueryResults_continuation = resCont results
    , Thrift.userQueryResults_diagnostics = resDiags results
    , Thrift.userQueryResults_handle = resWriteHandle results
    , Thrift.userQueryResults_type = resType results
    }

pidDetails :: DbSchema -> Int64 -> IO PredicateDetails
pidDetails schema ty = do
  case lookupPid (Pid (fromIntegral ty)) schema of
    Nothing ->  throwIO $ Thrift.Exception $
      "failed looking up fact type: " <> Text.pack (show ty)
    Just d -> return d

userQueryFactsImpl
  :: DbSchema
  -> ServerConfig.Config
  -> Lookup
  -> Thrift.UserQueryFacts
  -> IO (Results Stats Thrift.Fact)
     -- The length of the result list is guaranteed to be the same
     -- as the userQueryFacts_facts list in the input.
userQueryFactsImpl
    schema@DbSchema{..}
    config
    lookup
    query@Thrift.UserQueryFacts{..} = do
  let opts = fromMaybe def userQueryFacts_options

  schemaSelector <- schemaVersionForQuery schema config userQueryFacts_schema_id

  expandPids <- optsExpandPids opts schemaSelector schema
  let limits = mkQueryRuntimeOptions opts config expandPids

  trans <- transformationsForQuery schema schemaSelector

  vlog 2 $ "userQueryFactsImpl: " <> show (length userQueryFacts_facts)
  (qResults@QueryResults{..}, fullScans) <- do
    nextId <- firstFreeId lookup
    -- executeCompiled needs a Define, even though we won't use it
    bracket (FactSet.new nextId) release $ \derived -> do
    let stack = stacked lookup derived
    bracket
      (compileQueryFacts userQueryFacts_facts)
      (release . compiledQuerySub) $ \sub -> do
        results <- executeCompiled schemaInventory
          Nothing stack sub limits
        appliedTrans <- either (throwIO . Thrift.BadQuery) return $
          userQueryFactsTransformations trans schemaSelector schema query results
        -- use Pids in result facts to apply a suitable transformation if neded.
        return
          ( transformResultsBack appliedTrans results
          , compiledQueryFullScans sub
          )

  stats <- getStats schema fullScans qResults

  let results = Results
        { resFacts = Vector.toList queryResultsFacts
        , resPredicate = Nothing
        , resNestedFacts = mkNestedFacts queryResultsNestedFacts
        , resLocalPredicates = IntMap.empty
        , resCont = Nothing
        , resStats = stats
        , resDiags = []
        , resWriteHandle = Nothing
        , resFactsSearched = Nothing
        , resType = Nothing  -- could be facts of different predicates
        , resBytecodeSize = Nothing
        , resCompileTime = Nothing
        , resCodegenTime = Nothing
        , resExecutionTime = Nothing
        , resResultBytes = Nothing
        }

  return $ if Thrift.userQueryOptions_omit_results opts
     then withoutFacts results
     else results

userQueryFactsTransformations
  :: QueryTransformations
  -> SchemaSelector
  -> DbSchema
  -> Thrift.UserQueryFacts
  -> QueryResults
  -> Either Text ResultTransformations
userQueryFactsTransformations qtrans selector schema query results = do
  nameEnv <-  maybe (Left "invalid schema_id") return $ do
    schemaNameEnv schema selector

  let predRefs :: [PidRef]
      predRefs = mapMaybe (toPidRef nameEnv) sourceRefs

      -- a type containing all types in the response
      allTypes :: Type
      allTypes = Angle.RecordTy
        [ Angle.FieldDef "" (PredicateTy () predId) | predId <- predRefs ]

  -- errors if multiple versions of the same predicate are requested.
  transformationsFor schema qtrans allTypes
  where
    sourceRefs :: [SourceRef]
    sourceRefs = mapMaybe toRef $ Set.toList vset
      where
        vset :: Set (Pid, Maybe Version)
        vset = Vector.foldr insert mempty zipped
        zipped = Vector.zip (queryResultsFacts results) versions
        insert ((_, fact), version) acc =
          Set.insert (Pid $ Thrift.fact_type fact, version) acc

        versions :: Vector (Maybe Version)
        versions = Vector.fromList $
          Thrift.factQuery_predicate_version <$>
            Thrift.userQueryFacts_facts query

        toRef :: (Pid, Maybe Version) -> Maybe SourceRef
        toRef (pid, mversion) = do
          details <- lookupPid pid schema
          let PredicateRef name _ = predicateRef details
          return $ SourceRef name mversion

    toPidRef :: NameEnv RefTargetId -> SourceRef -> Maybe PidRef
    toPidRef nameEnv ref = do
      ResolvesTo (RefPred predId) <- return $ resolveRef nameEnv ref
      details <- lookupPredicateId predId schema
      return (pidRef details)

-- | A version of userQuery where we only care about the resulting writes
-- caused by the query. Used for stored predicate derivation.
userQueryWrites
  :: Database.Env
  -> OpenDB
  -> ServerConfig.Config
  -> Boundaries
  -> Lookup
  -> Thrift.Repo
  -> PredicateId
  -> Thrift.UserQuery
  -> IO (
       Thrift.UserQueryStats,
       Maybe Thrift.UserQueryCont,
       Maybe Thrift.Handle
     )
userQueryWrites env odb config bounds lookup repo pred q = do
  meta <- atomically $ Catalog.readMeta (envCatalog env) repo
  inc <- shouldDeriveIncrementally meta
  mode <-
    if inc
    then IncrementalDerivation <$> sectionsStats
    else return NoExtraSteps
  Results{..} <- withStats $
    userQueryImpl env odb config mode bounds lookup repo q
  return (resStats, resCont, resWriteHandle)
  where
    -- We derive incrementally if
    --   1. the DB is stacked, and
    --   2. the predicate was derived in the base DB
    --
    -- (2) might be false if we're deriving a predicate in a
    -- stacked DB that we didn't derive on the base DB.
    shouldDeriveIncrementally meta =
      case Thrift.metaDependencies meta of
        Just (Thrift.Dependencies_stacked Thrift.Stacked{..}) ->
          check $ Thrift.Repo stacked_name stacked_hash
        Just (Thrift.Dependencies_pruned pruned) ->
          check (Thrift.pruned_base pruned)
        Nothing -> return False
      where
      check base = do
        meta <- atomically $ Catalog.readMeta (envCatalog env) base
        return $ predicateIdRef pred `elem` Thrift.metaCompletePredicates meta

    -- Here the best we can do is say whether a Pid could have facts in a DB.
    -- Because of ownership slicing it may be that even though
    -- `Backend.predicateStats` gives a positive number all facts could be
    -- filtered out.
    sectionsStats :: IO (SeekSection -> Pid -> Bool)
    sectionsStats = do
      stackStats <- stats Backend.IncludeBase
      topStats <- stats Backend.ExcludeBase
      let baseStats = stackStats `minus` topStats
          pidHasFacts seekWhere (Pid pid) = case seekWhere  of
            SeekOnAllFacts -> hasFacts pid stackStats
            SeekOnBase -> hasFacts pid baseStats
            SeekOnStacked -> hasFacts pid topStats
            -- only the facts derived by a recursive query
            SeekOnRoundNew -> True
            SeekOnRoundOld -> True
            SeekOnRoundAll -> True
      return pidHasFacts

    stats opts =
      fmap Thrift.predicateStats_count
      <$> PredicateStats.predicateStats env repo opts
    minus = Map.unionWith (-)
    hasFacts pid m = maybe False (> 0) $ Map.lookup pid m

userQueryImpl
  :: Database.Env
  -> OpenDB
  -> ServerConfig.Config
  -> CompilationMode
  -> Boundaries
  -> Lookup
  -> Thrift.Repo
  -> Thrift.UserQuery
  -> IO (Results Stats Thrift.Fact)

userQueryImpl
  env
  odb
  config
  mode
  bounds
  lookup
  repo
  query@Thrift.UserQuery{..} = do
    let opts = fromMaybe def userQuery_options

    case Thrift.userQueryOptions_syntax opts of
      Thrift.QuerySyntax_ANGLE -> return ()
      other -> throwIO $ Thrift.Exception $
        "query syntax not supported: " <> Text.pack (show other)

    let
      schema = odbSchema odb
      stored = Thrift.userQueryOptions_store_derived_facts opts
      debug = Thrift.userQueryOptions_debug opts

    schemaVersion <-
      schemaVersionForQuery schema config userQuery_schema_id

    (returnType,compileTime,diag,cont,querySchema) <-
      case Thrift.userQueryOptions_continuation opts of
        Just ucont
          -- An empty continuation can't be resumed (see runQuery). We check
          -- this before compiling its type, which can refer to predicates
          -- declared by the query.
          | B.null (Thrift.userQueryCont_continuation ucont) ->
            throwIO $ Thrift.BadQuery noContinuation
          | Just retTy <- Thrift.userQueryCont_returnType ucont -> do
          (compileTime, _, returnType) <-
            timeIt $ compileType schema schemaVersion retTy
          return (returnType,compileTime,[],Right ucont,schema)

        -- This is either a new query or the continuation of a query
        -- that returns a temporary predicate.
        _ -> do
          (compileTime, _, compiled) <-
            timeIt $ compileAngleQuery
              schemaVersion
              schema
              mode
              userQuery_query
              stored
              (envDebug env)
          let (query@QueryWithInfo{..}, ty, preds, querySchema) = compiled

          predDiag <- if Thrift.queryDebugOptions_pred_has_facts debug then
              getPredDiags env repo querySchema preds
              else return []
          let
            irDiag =
              [ "ir:\n" <> Text.pack (show (displayDefault qiQuery))
              | Thrift.queryDebugOptions_ir debug ]

            cont = case Thrift.userQueryOptions_continuation opts of
              Just c -> Right c
              Nothing -> Left query
          return (ty,compileTime,irDiag <> predDiag,cont,querySchema)

    details <- getReturnPredicateDetails querySchema returnType

    if Thrift.userQueryOptions_just_check opts then do
      return $ emptyResult {resDiags = diag}
    else do
      let compileInfo = CompileInfo {
        returnType = returnType,
        compileTime = compileTime,
        compileDiag = diag,
        cont = cont,
        querySchema = querySchema
        }
      runQuery env odb config bounds lookup repo details compileInfo query

data CompileInfo = CompileInfo {
  returnType :: Type,
  compileTime :: Double,
  compileDiag :: [Text],
  cont :: Either CodegenQuery UserQueryCont,
  querySchema :: DbSchema
    -- ^ the DB's schema and the predicates the query declares
}

getPredDiags
  :: Database.Env
  -> Thrift.Repo
  -> DbSchema
  -> [TcPred]
  -> IO [Text]
getPredDiags env repo schema preds = do
  predStats <- PredicateStats.predicateStats env repo StackedDbOpts.IncludeBase
  let predsMissing = filter (\p -> not (tcPredExist p predStats)) preds
  return $ map warnDiag predsMissing
    where
      tcPredExist (PidRef pid _, _) predStats =
        derived schema pid || hasFacts predStats pid
      -- we assume derived predicates "exist" since we won't find any facts
      derived schema pid = case lookupPid pid schema of
        Just details -> case predicateDeriving details of
          Derive DeriveOnDemand _ -> True
          Derive DeriveIfEmpty _ -> True
          _ -> False
        Nothing -> error "Unknown Pid in getPredDiags"
      hasFacts predStats pid = case Map.lookup (fromPid pid) predStats of
        Just stat -> Thrift.predicateStats_count stat > 0
        Nothing -> False
      warnDiag :: TcPred -> Text
      warnDiag (PidRef _ (PredicateId predRef _), Some span) = Text.pack $
        "Warning: "
        <> show (pretty span) ++ " "
        <> Text.unpack (predicateRef_name predRef)
        <> Text.unpack " doesn't exist in " ++ show (Thrift.repo_name repo)

getReturnPredicateDetails :: DbSchema -> Type -> IO PredicateDetails
getReturnPredicateDetails schema@DbSchema{..} returnType = do
  case returnType of
    Angle.PredicateTy _ (PidRef pid _) ->
      case IntMap.lookup (fromIntegral (fromPid pid)) predicatesByPid of
        Nothing -> throwIO $ Thrift.Exception "internal: no predicate"
        Just d
          -- We return facts of a predicate declared by the query as facts
          -- of the temporary predicate. See Flatten.captureKey and
          -- Note [Query-local predicates]
          | pid `Set.member` schemaLocalPids -> return d
            { predicatePid = tempPid schema
            , predicateId = tempPredicateId
            }
          | otherwise -> return d

    _not_a_predicate -> do
      return
          -- This is a temporary Pid generated by Flatten.captureKey,
          -- because the query doesn't return facts. In this case we
          -- are pretending the query returns facts for a new predicate,
          -- so we need a PredicateDetails to pass to unfoldFacts below.
          -- (this is temporary, unfoldFacts wil go away in due course
          -- when we compile it to bytecode).
          PredicateDetails
            { predicatePid = tempPid schema
            , predicateKeyType = returnType
            , predicateValueType = unit
            , predicateId = tempPredicateId
            , predicateSchema = error "predicateSchema"
            , predicateTraversal = error "predicateTraversal"
            , predicateTypecheck = error "predicateTypecheck"
            , predicateDeriving = NoDeriving
            , predicateInStoredSchema = False
            }

runQuery
  :: Database.Env
  -> OpenDB
  -> ServerConfig.Config
  -> Boundaries
  -> Lookup
  -> Thrift.Repo
  -> PredicateDetails
  -> CompileInfo
  -> Thrift.UserQuery
  -> IO (Results Stats Thrift.Fact)
runQuery
  env
  odb
  config
  bounds
  lookup
  repo
  details
  CompileInfo{..}
  Thrift.UserQuery{..} = do
    vlog 2 $ "return type: " <> show (displayDefault returnType)

    let
      schema = odbSchema odb
      opts = fromMaybe def userQuery_options
      stored = Thrift.userQueryOptions_store_derived_facts opts

    schemaVersion <-
        schemaVersionForQuery schema config userQuery_schema_id
    trans <- transformationsForQuery schema schemaVersion

    unless (Text.null userQuery_predicate) $ do
      -- With Angle queries, setting userQuery_predicate is
      -- optional. If the client sets it, we will check it: this
      -- can be a useful way to catch errors in the client.
      -- If the query is not returning whole facts, then the
      -- client should set this field to "".
      let ref = SourceRef userQuery_predicate userQuery_predicate_version
      checkPredicatesMatch schema details ref schemaVersion

    expandPids <- optsExpandPids opts schemaVersion schema
    let
      localPredicates = IntMap.fromList
        [ (fromIntegral (fromPid pid), d)
        | pid <- Set.toList (schemaLocalPids querySchema)
        , Just d <- [lookupPid pid querySchema] ]

      -- Facts of predicates declared by the query are always included in
      -- the nested facts, because their ids mean nothing outside the
      -- query. See Note [Query-local predicates]
      nestedLocal = not $ Set.null $
        localPidsIn querySchema (predicateKeyType details) <>
        localPidsIn querySchema (predicateValueType details)

      limits = mkQueryRuntimeOptions opts config $
        if nestedLocal
          then expandPids <> schemaLocalPids querySchema
          else expandPids

    nextId <- case Thrift.userQueryOptions_continuation opts of
      Just Thrift.UserQueryCont{..}
        | userQueryCont_nextId > 0 -> return (Fid userQueryCont_nextId)
      _otherwise -> firstFreeId lookup
    derived <- FactSet.new nextId
    let stack = stacked lookup derived

    defineOwners <- if stored
      then do
        maybeOwnership <- readTVarIO (odbOwnership odb)
        forM maybeOwnership $ \ownership ->
          newDefineOwnership ownership nextId
        else return Nothing

    appliedTrans <- either (throwIO . Thrift.BadQuery) return $
      transformationsFor schema trans $
        -- including the types that facts of declared predicates refer to
        Angle.RecordTy $ map (Angle.FieldDef "") $ returnType : concat
          [ [predicateKeyType d, predicateValueType d]
          | d <- IntMap.elems localPredicates ]

    ( qResults@QueryResults{..}
      , queryDiag
      , bytecodeSize
      , codegenTime
      , fullScans ) <-
      case cont of
        Right ucont -> do
          let binaryCont = Thrift.userQueryCont_continuation ucont
          results <- transformResultsBack appliedTrans <$>
            restartCompiled
              (schemaInventory schema)
              defineOwners
              stack
              (Just $ predicatePid details)
              limits
              binaryCont
          return (results, [], B.length binaryCont, 0, [])

        Left query -> do
          let
            debug = Thrift.userQueryOptions_debug opts
            bytecodeDiag sub =
              [ "bytecode:\n" <> Text.unlines
                (disassemble "Query" userQuerySysCalls $ compiledQuerySub sub)
              | Thrift.queryDebugOptions_bytecode debug ]

          bracket
            (timeIt $ compileQuery trans bounds query)
            (\(_, _, sub) -> release $ compiledQuerySub sub)
            $ \(codegenTime, _, sub) -> do
              results <- transformResultsBack appliedTrans <$>
                executeCompiled (schemaInventory querySchema) defineOwners
                  stack sub limits

              diags <-
                evaluate $ force (bytecodeDiag sub) -- don't keep sub alive
              sz <- evaluate $ Bytecode.size (compiledQuerySub sub)
              let fullScans = compiledQueryFullScans sub
              return (results, diags, sz, codegenTime, fullScans)

    -- If we're storing derived facts, queue them for writing and
    -- return the handle. We allow querying for stored derived
    -- predicates with stored=True on a read-only DB; this is used
    -- by the regression testing framework to test derived predicates.
    maybeWriteHandle <-
      if stored && (
          isJust (odbWriting odb) ||
          Thrift.userQueryOptions_omit_results opts)
        then writeDerivedFacts env repo nextId derived defineOwners
          queryResultsFacts
        else return Nothing

    -- A query that evaluates recursive predicates can't be continued,
    -- because the continuation would resume without the facts derived so
    -- far. So when it reaches a limit we return the results we have
    -- along with an empty continuation, which tells clients that the
    -- results are incomplete. Resuming it is an error. The same goes for
    -- queries that declare predicates (see Note [Query-local predicates]).
    let incomplete = isJust queryResultsCont && case cont of
          Left query -> usesRecursion query || declaresPredicates
          Right _ -> False
        declaresPredicates = not (Set.null (schemaLocalPids querySchema))
    userCont <- case queryResultsCont of
      Nothing -> return Nothing
      Just bs -> do
        nextId <- firstFreeId derived
        let bs' = if incomplete then B.empty else bs
        return $ Just $ mkUserQueryCont (Right returnType) bs' nextId

    stats <- getStats schema fullScans qResults

    when (isJust userCont) $
      addStatValueType "glean.query.truncated" 1 Stats.Sum

    let ppType = renderStrict $ layoutPretty defaultLayoutOptions $
          displayDefault returnType

        -- leave out predicates that only exist while the query runs, like
        -- the Event predicates of recursive queries
        knownPid pid _ = isJust (lookupPid (Pid pid) schema)

        results = Results
          { resFacts = Vector.toList queryResultsFacts
          , resPredicate = Just details
          , resNestedFacts = mkNestedFacts queryResultsNestedFacts
          , resLocalPredicates = localPredicates
          , resCont = userCont
          , resStats = stats
          , resDiags = compileDiag ++ queryDiag ++
              [ noContinuation | incomplete ]
          , resWriteHandle = maybeWriteHandle
          , resFactsSearched = Map.filterWithKey knownPid <$> queryResultsStats
          , resType = Just ppType
          , resBytecodeSize = Just bytecodeSize
          , resCompileTime = Just compileTime
          , resCodegenTime = Just codegenTime
          , resExecutionTime = Just queryResultsElapsedNs
          , resResultBytes = Just queryResultsResultBytes
          }

    return $ if Thrift.userQueryOptions_omit_results opts
      then withoutFacts results
      else results

transformationsForQuery
  :: DbSchema
  -> SchemaSelector
  -> IO QueryTransformations
transformationsForQuery schema selector = do
  case allSchemaVersion schema selector of
    Nothing -> throwIO $ Thrift.BadQuery "invalid schema_id"
    Just schemaId ->
      let transMap = predicatesTransformations schema in
      case HashMap.lookup schemaId transMap of
        Just trans -> return trans
        Nothing -> throwIO $ Thrift.BadQuery "no transformations for schema_id"

schemaVersionForQuery
  :: DbSchema
  -> ServerConfig.Config
  -> Maybe Thrift.SchemaId  -- ^ SchemaId specified by client
  -> IO SchemaSelector
schemaVersionForQuery schema ServerConfig.Config{..} qid = do
  use <-
    case qid of
      Nothing -> return LatestSchema
      Just id
        | id `Map.member` schemaEnvs schema -> return (SpecificSchemaId id)
        | config_strict_query_schema_id ->
            throwIO (Thrift.UnknownSchemaId id)
        | otherwise -> do
            logWarning $ "schema unavailable: " <> show id
            return LatestSchema

  vlog 1 $ "using schema ID: " <> show (pretty use)
  return use

optsExpandPids
  :: Thrift.UserQueryOptions
  -> SchemaSelector
  -> DbSchema
  -> IO (Set Pid)
optsExpandPids opts schemaVersion dbSchema =
  fmap Set.fromList $ forM (Thrift.userQueryOptions_expand_predicates opts) $
    \(Thrift.SourcePredicate name version) -> do
      let ref = SourceRef name version
      case lookupPredicateSourceRef ref schemaVersion dbSchema of
        Left err -> throwIO $ Thrift.BadQuery err
        Right details -> return (predicatePid details)

data CompilationMode
  = NoExtraSteps
  | IncrementalDerivation (SeekSection -> Pid -> Bool)

compileAngleQuery
  :: SchemaSelector
    -- ^ Schema version to resolve unversioned predicates
  -> DbSchema
  -> CompilationMode
    -- ^ only used in predicate derivations on incremental dbs
  -> ByteString
  -> Bool
  -> DebugFlags
  -> IO (CodegenQuery, Type, [TcPred], DbSchema)
     -- ^ the query, its type, the predicates it uses, and the schema it
     -- was compiled with (the DB's schema plus the declared predicates)
compileAngleQuery ver schema mode source stored debug = do
  (parsed, decls) <- checkBadQuery Text.pack $
    Angle.parseQueryWithPredicates source
  ifDebug $ "parsed query: " <> show (displayDefault parsed)

  -- the facts of declared predicates only exist while the query runs
  when (stored && not (null decls)) $ throwIO $ Thrift.BadQuery
    "a query that declares predicates can't store derived facts"

  let scope = addTmpPredicate $ fromMaybe HashMap.empty $
        schemaNameEnv schema ver

  (resolved, defs) <- checkBadQuery id $ runExcept $
    runResolve latestAngleVersion scope $
      resolveQueryWithPredicates parsed decls
  ifDebug $ "resolved query: " <> show (displayDefault resolved)

  -- See Note [Query-local predicates]
  let tcOpts = defaultTcOpts debug latestAngleVersion
  dbSchema <- (checkBadQuery id =<<) $ runExceptT $
    addLocalPredicates tcOpts defs schema

  (typechecked, preds) <- (checkBadQuery id =<<) $ runExceptT $
    typecheck dbSchema tcOpts (dbSchemaRtsType dbSchema) resolved
  ifDebug $ "typechecked query: " <> show (displayDefault (qiQuery typechecked))

  flattened <- checkBadQuery id $ runExcept $
    flatten dbSchema latestAngleVersion stored typechecked
  ifDebug $ "flattened query: " <> show (displayDefault (qiQuery flattened))

  optimised <- checkBadQuery id $ runExcept $ optimise flattened
  ifDebug $ "optimised query: " <> show (displayDefault (qiQuery optimised))

  reordered <- checkBadQuery id $ runExcept $ reorder dbSchema optimised
  ifDebug $ "reordered query: " <> show (displayDefault (qiQuery reordered))

  final <- case mode of
    NoExtraSteps -> return reordered
    IncrementalDerivation getStats -> do
      vlog 2 "made incremental"
      return $ makeIncremental getStats reordered

  -- See Note [Evaluating recursive predicates] in Glean.Query.Recursion
  withRecursion <- checkBadQuery id $ runExcept $
    expandRecursion dbSchema
      (\schema bound query -> reorderWithBound schema bound =<< optimise query)
      final
  when (usesRecursion withRecursion) $
    ifDebug $ "with recursive predicates: " <>
      show (displayDefault (qiQuery withRecursion))

  return (withRecursion, qiReturnType typechecked, preds, dbSchema)
  where
  ifDebug = when (queryDebug debug) . hPutStrLn stderr

  checkBadQuery :: (err -> Text) -> Either err a -> IO a
  checkBadQuery txt act = case act of
    Left str -> throwIO $ Thrift.BadQuery $ txt str
    Right a -> return a

{- Note [Query-local predicates]

A query can declare predicates after its body, written the same way as
a schema's derived predicates:

  X where Reach { 1, X }
  predicate Reach : { from: nat, to: nat }
    { A, B } where x.Edge { A, B } | (Reach { A, K }; x.Edge { K, B })

They're derived when they're used, like a schema's derived predicates,
and can be recursive (see Note [Evaluating recursive predicates] in
Glean.Query.Recursion). That's the whole point. They let a query compute
a relation that the schema has no predicate for, like the transitive
closure of a relation, in a single query.

* Names. A declared predicate has a plain name, with no schema or
  version. It's in scope in the query and in the derivations of all the
  declared predicates, so they can call themselves and each other. It
  can't shadow anything, because everything else a query can refer to
  has a qualified name (x.Edge).

* Declarations. Only predicates derived on demand can be declared, with
  a key type and optionally a value type. Stored predicates and default
  derivations make no sense for predicates that only exist while the
  query runs.

* Schema. We compile the query with the DB's schema plus the declared
  predicates (addLocalPredicates), which get the Pids after the schema's.
  They're checked in the same way as a schema's predicates. Their
  derivations are typechecked, and they can't depend on their own
  negation (see Note [Stratification] in Glean.Database.Schema). After
  that they're like any other derived predicate, so flattening,
  recursion and code generation need nothing new. Queries that don't
  declare predicates use the DB's schema as before.

* Results. Clients have no schema for the declared predicates, and the
  ids of their facts mean nothing outside the query, but their facts can
  still be returned:
  - A query whose result is a declared predicate returns its facts as
    facts of the temporary predicate, with their keys and values. That's
    how a query returns any value that isn't a fact of the schema
    (Flatten.captureKey, getReturnPredicateDetails).
  - Facts of declared predicates nested in the results are returned like
    the schema's. The query's schema has the code to traverse them
    (schemaInventory), and the JSON encoding uses their types. They're
    always included in the nested facts, even if the query doesn't ask
    for nested facts, since the client couldn't look them up later.
  - Other encodings can't have them, because clients decode those with
    their own schema. A query whose results have them fails.

* Continuations. A query that declares predicates can't be continued,
  just like a query that evaluates recursive predicates. When it reaches
  a limit it returns the results it has. Resuming it would need the
  declarations, which aren't part of the continuation, and the facts
  derived so far, which don't outlive the query.
-}

-- | The predicates declared by a query that a type refers to directly.
-- See Note [Query-local predicates].
localPidsIn :: DbSchema -> Type -> Set Pid
localPidsIn dbSchema ty = Set.intersection (schemaLocalPids dbSchema) pids
  where
  pids = bifoldMap (\(PidRef pid _) -> Set.singleton pid) (const mempty) ty

-- | Why the results of a query that can't be continued are incomplete,
-- when it reaches a limit
noContinuation :: Text
noContinuation =
  "the query reached one of its limits (results, bytes or time), and " <>
  "queries that use recursive predicates or declare predicates can't be " <>
  "continued. These are the results found so far; to get more, increase " <>
  "the limit."

-- | Whether a query evaluates recursive predicates
-- (see Note [Evaluating recursive predicates] in Glean.Query.Recursion).
usesRecursion :: CodegenQuery -> Bool
usesRecursion QueryWithInfo{..} = any hasRec stmts
  where
  CgQuery _ stmts = qiQuery
  hasRec = \case
    CgStatement{} -> False
    CgAllStatement _ _ stmts -> any hasRec stmts
    CgNegation stmts -> any hasRec stmts
    CgDisjunction stmtss -> any (any hasRec) stmtss
    CgConditional cond then_ else_ -> any (any hasRec) [cond, then_, else_]
    CgRec{} -> True

-- | Put the nested facts in the right form for the conversion to
-- (JSON, Compact, Bin).
mkNestedFacts :: Vector (Fid, Thrift.Fact) -> IntMap Thrift.Fact
mkNestedFacts facts =
  IntMap.fromList
    [ (fromIntegral (fromFid id), f)
    | (id,f) <- Vector.toList facts ]

withoutFacts :: Results stats fact -> Results stats fact
withoutFacts results = results
    { resFacts = mempty
    , resNestedFacts = mempty
    }

mkQueryRuntimeOptions
  :: Thrift.UserQueryOptions
  -> ServerConfig.Config
  -> Set Pid
  -> QueryRuntimeOptions
mkQueryRuntimeOptions
    Thrift.UserQueryOptions{..} ServerConfig.Config{..} expandPids =
  QueryRuntimeOptions
    { queryMaxResults = userQueryOptions_max_results
        <|> config_default_max_results -- from ServerConfig
    , queryMaxBytes = userQueryOptions_max_bytes
        <|> config_default_max_bytes -- from ServerConfig
    , queryMaxTimeMs = userQueryOptions_max_time_ms
        <|> config_default_max_time_ms -- from ServerConfig
    , queryMaxSetSize = config_max_set_size_bytes
    , queryWantStats = userQueryOptions_collect_facts_searched
    , queryDepth = if
        | userQueryOptions_recursive && not userQueryOptions_omit_results ->
          ExpandRecursive
        | not (null expandPids) -> ExpandPartial expandPids
        | otherwise -> ResultsOnly
    }

emptyResult :: Results Stats fact
emptyResult = Results {
    resFacts = mempty
  , resPredicate = Nothing
  , resNestedFacts = mempty
  , resLocalPredicates = IntMap.empty
  , resCont = Nothing
  , resStats = Stats {
      statFactCount = 0
    , statResultCount = 0
    , statFullScans = []
    }
  , resDiags = []
  , resWriteHandle = Nothing
  , resFactsSearched = Nothing
  , resType = Nothing
  , resBytecodeSize = Nothing
  , resCompileTime = Nothing
  , resCodegenTime = Nothing
  , resExecutionTime = Nothing
  , resResultBytes = Nothing
  }


{- Note [Writing derived facts]

When deriving, we
  (1) Run a query that produces all the derived facts
  (2) Serialize the FactSet
  (3) Write this to the DB

As the query runs, it writes derived facts into a FactSet and also
produces a set of results. The results are correct, however the
FactSet may contain some additional invalid facts. For example, this
can happen if the derived predicate is something like

predicate P : string
  X where
    Q X;
    X != "foo"

when we compile the query, it can look something like

F where
  Q X;
  F = P<- X;    -- (*)
  X != "foo"

The statement labelled (*) produces the derived fact. Note that this
is just a regular statement; it can get arbitrarily reordered relative
to the other statements. In this case the compiler chose to put it
before the final filter X != "foo", which means that we'll create some
derived facts that aren't actually true. There's nothing wrong with
this: the result of the query is still correct, but we have to be
careful to use the query results and not just write the whole contents
of the FactSet to the DB.

It would be difficult to ensure the compiler always ordered F = P<- X
after the filter, there's nothing requiring it to do this. We can't
use statement ordering for this, because statement ordering is for
optimisation and shouldn't change sementics. The compiler can override
ordering hints if it wants.

The right thing to do is to use the query results to filter the
FactSet, and fortunately there's a good place to do this: we already
reorder the results when we serialize the FactSet (for ownership
reasons), so we can do the filtering there.
-}

writeDerivedFacts
  :: Env
  -> Thrift.Repo
  -> Fid
  -> FactSet
  -> Maybe DefineOwnership
  -> Vector (Fid, Thrift.Fact)
  -> IO (Maybe Thrift.Handle)
writeDerivedFacts env repo firstId derived owned results = do
  -- See Note [Writing Derived Facts] for why we filter here
  let order = VS.fromList
         [ fromFid fid
         | (fid,_) <- Vector.toList results
         , fid >= firstId  -- ignore existing facts
         ]
  batch <- case owned of
    Nothing -> FactSet.serializeReorder derived order
    Just define -> do
      nextId <- firstFreeId derived
      let count = fromIntegral (fromFid nextId - fromFid firstId)
      sorted <- defineOwnershipSortByOwner define count order
      FactSet.serializeReorder derived sorted
  -- If the batch is empty, we may still have new ownership data about
  -- existing facts, so we have to write that
  if Thrift.batch_count batch == 0 && isNothing owned
    then return Nothing
    else do
      resp <- enqueueBatch env Thrift.ComputedBatch
        { computedBatch_repo = repo
        , computedBatch_remember = True
        , computedBatch_batch = batch }
        owned
      case resp of
        Thrift.SendResponse_handle handle -> return (Just handle)
        Thrift.SendResponse_retry (Thrift.BatchRetry s) ->
          throwIO $ Thrift.Retry s


-- | Check that the predicate declared in the UserQuery request
-- matches the actual type of the query as determined by the
-- typechecker. This adds some rudimentary type safety: the predicate
-- declared in the UserQuery is typically the one expected at the call
-- site.
checkPredicatesMatch
  :: DbSchema
  -> PredicateDetails
  -> SourceRef
  -> SchemaSelector
  -> IO ()
checkPredicatesMatch dbSchema details predicate schemaVer = do
  case lookupPredicateSourceRef predicate schemaVer dbSchema of
    Left err -> throwIO $ Thrift.BadQuery err
    Right details' ->
      if predicatePid details == predicatePid details'
        then return ()
        else throwIO $ Thrift.BadQuery $ mconcat
          [ "predicate " <> showRef predicate <>
            " does not match type of query: "
          <> predicateRef_name (predicateRef details) <> "."
          <> showt (predicateRef_version (predicateRef details)) ]


data Stats = Stats
  { statFactCount :: {-# UNPACK #-} !Int
  , statResultCount :: {-# UNPACK #-} !Int
  , statFullScans :: [PredicateRef]
  }

getStats :: DbSchema -> [Pid] -> QueryResults -> IO Stats
getStats schema fullScans QueryResults{..} = do
  let
    results =
      Vector.length queryResultsFacts

    facts =
      Vector.length queryResultsFacts +
      Vector.length queryResultsNestedFacts

    -- leave out predicates that only exist while the query runs, like the
    -- Event predicates of recursive queries
    pref pid = predicateIdRef . predicateId <$> lookupPid pid schema

  addStatValueType "glean.query.facts" facts Stats.Sum
  addStatValueType "glean.query.results" results Stats.Sum
  return $ Stats
    { statFactCount = facts
    , statResultCount  = results
    , statFullScans = mapMaybe pref fullScans
    }

withStats :: IO (Results Stats fact) -> IO (Results Thrift.UserQueryStats fact)
withStats io = do
  (secs, bytes, res) <- timeIt io
  let stats = Thrift.UserQueryStats
        { Thrift.userQueryStats_num_facts =
            fromIntegral $ statFactCount $ resStats res
        , Thrift.userQueryStats_result_count =
            fromIntegral $ statResultCount $ resStats res
        , Thrift.userQueryStats_elapsed_ns = truncate (secs * 1000000000)
        , Thrift.userQueryStats_allocated_bytes = fromIntegral bytes
        , Thrift.userQueryStats_facts_searched = resFactsSearched res
        , Thrift.userQueryStats_bytecode_size =
            fromIntegral <$> resBytecodeSize res
        , Thrift.userQueryStats_compile_time_ns =
            fmap (round . (* 1000000000)) (resCompileTime res )
        , Thrift.userQueryStats_codegen_time_ns =
            fmap (round . (* 1000000000)) (resCodegenTime res )
        , Thrift.userQueryStats_execute_time_ns =
            fromIntegral <$> resExecutionTime res
        , Thrift.userQueryStats_full_scans = statFullScans $ resStats res
        , Thrift.userQueryStats_result_bytes =
            fromIntegral <$> resResultBytes res
        }
  return res{ resStats = stats }

mkUserQueryCont
  :: Either (Set Pid) Type
  -> ByteString
  -> Fid
  -> Thrift.UserQueryCont
mkUserQueryCont contInfo cont nextId =
  hashUserQueryCont $ Thrift.UserQueryCont
  { userQueryCont_continuation = cont
  , userQueryCont_nextId = fromFid nextId
  , userQueryCont_version = fromIntegral Bytecode.version
  , userQueryCont_hash = 0
  , userQueryCont_returnType = returnType
  , userQueryCont_pids = pids
  }
  where
    returnType = case contInfo of
      Right ty -> Just $ serializeType ty
      Left _ -> Nothing
    pids = case contInfo of
      Right _ -> []
      Left ps -> map fromPid $ Set.elems ps

checkUserQueryCont :: Thrift.UserQueryCont -> IO ()
checkUserQueryCont cont@Thrift.UserQueryCont{..} = do
  when
    (userQueryCont_version < fromIntegral Bytecode.lowestSupportedVersion
      || userQueryCont_version > fromIntegral Bytecode.version)
    $ throwIO $ Thrift.BadQuery $
        "unsupported query continuation version "
          <> Text.pack (show userQueryCont_version)
  when
    (userQueryCont_hash /= Thrift.userQueryCont_hash (hashUserQueryCont cont))
    $ throwIO $ Thrift.BadQuery "invalid query continuation hash"

hashUserQueryCont :: Thrift.UserQueryCont -> Thrift.UserQueryCont
hashUserQueryCont Thrift.UserQueryCont{..} = Thrift.UserQueryCont
  -- NOTE: The hash is really just a checksum to detect accidental corruption
  -- so a 64 bit non-crypto hash should work fine. Hashable currently uses a
  -- slightly broken (https://github.com/tibbe/hashable/issues/190) version of
  -- FNV-1 but should still be good enough.
  { userQueryCont_hash = fromIntegral $ hash
      ( userQueryCont_continuation
      , userQueryCont_nextId
      , userQueryCont_version
      , userQueryCont_returnType
      )
  , ..
  }

serializeType :: Type -> ByteString
serializeType = Text.encodeUtf8 . renderStrict . layoutCompact .
  displayDefault
    -- Note that we have to print PredicateIds as PredicateRefs, because
    -- the parser will parse it as a source type. The default display options
    -- do exactly that.

compileType :: DbSchema -> SchemaSelector -> ByteString -> IO Type
compileType schema version src = do
  parsed <- checkParsed $ Angle.parseType src
  let scope = addTmpPredicate $ fromMaybe HashMap.empty $
        schemaNameEnv schema version
  resolved <- checkResolved $ runResolve latestAngleVersion scope $
    resolveType parsed
  checkConverted $ dbSchemaRtsType schema resolved
  where
    checkParsed = either (badQuery . Text.pack) return
    checkResolved = either badQuery return . runExcept
    checkConverted = maybe (badQuery "type not present in schema") return

    badQuery :: Text -> IO a
    badQuery err = throwIO $ Thrift.BadQuery $ Text.unlines
      ["unable to compile type: ", err, "type was: ", Text.decodeUtf8 src]
