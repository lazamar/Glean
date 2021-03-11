module Glean.Database.Schema.Types
  ( DbSchema(..)
  , PredicateDetails(..)
  , lookupPredicate
  , lookupPredicateRef
  , lookupPid
  , TypeDetails(..)
  , lookupType
  , lookupTypeRef
  , dbSchemaRtsType
  , mkRtsType
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Glean.Angle.Types as Schema hiding (Type, FieldDef)
import qualified Glean.Angle.Types as Schema
import Glean.Query.Typecheck.Types
import Glean.RTS.Foreign.Bytecode (Subroutine)
import Glean.RTS.Foreign.Inventory (Inventory)
import Glean.RTS.Typecheck
import Glean.RTS.Traverse
import Glean.RTS.Types (Pid(..), Type, PidRef(..), FieldDef, ExpandedType(..))
import Glean.Schema.Resolve

-- | The Schema used by a DB
data DbSchema = DbSchema
  { predicatesByRef :: HashMap PredicateRef PredicateDetails
  , predicatesByName :: HashMap Name PredicateDetails
     -- ^ points to the latest predicate for each name
  , predicatesById :: IntMap PredicateDetails
  , schemaTypesByRef :: HashMap TypeRef TypeDetails
  , schemaTypesByName :: HashMap Name TypeDetails
  , schemaInventory :: Inventory
  , schemaSpec :: Schemas
  , schemaSource :: SourceSchemas
  , schemaMaxPid :: Pid
  }

data TypeDetails = TypeDetails
  { typeRef :: TypeRef
  , typeType :: Type
  }

data PredicateDetails = PredicateDetails
  { predicatePid :: Pid
  , predicateRef :: PredicateRef
  , predicateSchema :: PredicateDef
  , predicateKeyType :: Type
  , predicateValueType :: Type
  , predicateTypecheck :: Subroutine CompiledTypecheck
  , predicateTraversal :: Subroutine CompiledTraversal
  , predicateDeriving :: DerivingInfo TypecheckedQuery
  , predicateInStoredSchema :: Bool
    -- ^ True if this prediate is part of the schema stored in the DB.
    -- Only predicates in the stored schema can be written.
  }

lookupPredicate
  :: Name
  -> Maybe Version
  -> DbSchema
  -> Maybe PredicateDetails
lookupPredicate name (Just ver) = lookupPredicateRef $ PredicateRef name ver
lookupPredicate name Nothing = HashMap.lookup name . predicatesByName

lookupPredicateRef :: PredicateRef -> DbSchema -> Maybe PredicateDetails
lookupPredicateRef ref = HashMap.lookup ref . predicatesByRef

lookupPid :: Pid -> DbSchema -> Maybe PredicateDetails
lookupPid (Pid pid) = IntMap.lookup (fromIntegral pid) . predicatesById

lookupType :: SourceRef -> DbSchema -> Maybe TypeDetails
lookupType (SourceRef name Nothing) = HashMap.lookup name . schemaTypesByName
lookupType (SourceRef name (Just v)) = lookupTypeRef (TypeRef name v)

lookupTypeRef :: TypeRef -> DbSchema -> Maybe TypeDetails
lookupTypeRef ref  = HashMap.lookup ref . schemaTypesByRef


-- | Convert Schema types to RTS types using a DbSchema
dbSchemaRtsType :: DbSchema -> Schema.Type -> Maybe Type
dbSchemaRtsType dbSchema = mkRtsType lookupType lookupPid
  where
  lookupType ref = typeType <$> lookupTypeRef ref dbSchema
  lookupPid ref = predicatePid <$> lookupPredicateRef ref dbSchema


-- | Convert from Schema Types to RTS Types. This involves
-- 1. PredicateRef -> PidRef
-- 2. Expand NamedTypes
mkRtsType
  :: (TypeRef -> Maybe Type)
  -> (PredicateRef -> Maybe Pid)
  -> Schema.Type -> Maybe Type
mkRtsType lookupType lookupPid = rtsType
  where
    rtsType :: Schema.Type -> Maybe Type
    rtsType Schema.Byte = return Schema.Byte
    rtsType Schema.Nat = return Schema.Nat
    rtsType (Schema.Array elty) = Schema.Array <$> rtsType elty
    rtsType (Schema.Record fields) = Schema.Record <$> mapM fieldType fields
    rtsType (Schema.Sum fields) = Schema.Sum <$> mapM fieldType fields
    rtsType Schema.String = return Schema.String
    rtsType (Schema.Predicate ref) = do
      pid <- lookupPid ref
      return (Schema.Predicate (PidRef pid ref))
    -- TODO: This will loop if we have recursive typedefs but we don't allow
    -- those at the moment.
    rtsType (Schema.NamedType ref) =
      Schema.NamedType . ExpandedType ref <$> lookupType ref
    rtsType (Schema.Maybe eltTy) = Schema.Maybe <$> rtsType eltTy
    rtsType (Schema.Enumerated names) = return (Schema.Enumerated names)
    rtsType Schema.Boolean = return Schema.Boolean

    fieldType :: Schema.FieldDef -> Maybe FieldDef
    fieldType (Schema.FieldDef name ty) = Schema.FieldDef name <$> rtsType ty
