module Glean.RTS.Foreign.FactSet
  ( FactSet
  , new
  , factMemory
  , serialize
  , append
  , renameFacts
  ) where

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr

import Glean.FFI
import Glean.RTS.Foreign.Define
import Glean.RTS.Foreign.Inventory (Inventory)
import Glean.RTS.Foreign.Lookup (Lookup(..), CanLookup(..))
import Glean.RTS.Foreign.Stacked (stacked)
import Glean.RTS.Foreign.Subst (Subst)
import Glean.RTS.Types (Fid(..))
import qualified Glean.Types as Thrift

-- An environment for defining facts
newtype FactSet = FactSet (ForeignPtr FactSet)

instance Object FactSet where
  wrap = FactSet
  unwrap (FactSet p) = p
  destroy = glean_factset_free

instance CanLookup FactSet where
  withLookup x f = with x $ f . glean_factset_lookup

instance CanDefine FactSet where
  withDefine x f = with x $ f . glean_factset_define

new :: Fid -> IO FactSet
new next_id = construct $ invoke $ glean_factset_new next_id

factMemory :: FactSet -> IO Int
factMemory facts = fromIntegral <$> with facts glean_factset_fact_memory

serialize :: FactSet -> IO Thrift.Batch
serialize facts =
  with facts $ \facts_ptr -> do
  (Fid first_id, count, facts_data, facts_size) <-
    invoke $ glean_factset_serialize facts_ptr
  Thrift.Batch first_id (fromIntegral count)
    <$> unsafeMallocedByteString facts_data facts_size
    <*> pure Nothing

append :: FactSet -> FactSet -> IO ()
append target source =
  with target $ \target_ptr ->
  with source $ \source_ptr ->
  invoke $ glean_factset_append target_ptr source_ptr

-- Prepare a Thrift batch for writing into the database by renaming and
-- deduplicating facts.
renameFacts
  :: CanLookup l
  => Inventory          -- ^ where to lookup predicates
  -> l                  -- ^ where to lookup facts
  -> Fid                -- ^ first free fact id in the database
  -> Thrift.Batch       -- ^ batch to rename
  -> IO (FactSet, Subst)
                        -- ^ resulting facts and substitution
renameFacts inventory base next batch = do
  added <- new next
  subst <- defineUntrustedBatch (stacked base added) inventory batch
  return (added, subst)

foreign import ccall unsafe glean_factset_new
  :: Fid -> Ptr (Ptr FactSet) -> IO CString
foreign import ccall unsafe "&glean_factset_free" glean_factset_free
  :: FunPtr (Ptr FactSet -> IO ())

foreign import ccall unsafe glean_factset_fact_memory
  :: Ptr FactSet -> IO CSize

foreign import ccall unsafe glean_factset_lookup
  :: Ptr FactSet -> Lookup

foreign import ccall unsafe glean_factset_define
  :: Ptr FactSet -> Define

foreign import ccall unsafe glean_factset_serialize
  :: Ptr FactSet
  -> Ptr Fid
  -> Ptr CSize
  -> Ptr (Ptr ())
  -> Ptr CSize
  -> IO CString

foreign import ccall unsafe glean_factset_append
  :: Ptr FactSet -> Ptr FactSet -> IO CString
