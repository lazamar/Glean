module Glean.Write.Async (
  Sender, SendQueueSettings(..), SendQueueEvent(..), withSender, addSenderWait,
  senderQueue,
  Writer, WriterSettings(..), WriterEvent(..), withWriter, writeFacts,
  withBatchWriter,
  basicWriter
) where

import Control.Applicative
import Control.Concurrent.MVar
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Default

import Glean.Backend.Remote (Backend)
import qualified Glean.Backend.Remote as Backend
import Glean.RTS as RTS
import Glean.Typed.BuildFact
import Glean.Typed.Predicate
import qualified Glean.Types as Thrift
import Glean.Write.SendQueue
import Glean.Util.Some
import Glean.Util.Time


-- | An asynchronous batch sender. Can be interacted with via a 'Writer'.
data Sender = Sender
  { senderQueue :: SendQueue
  , senderPredicates :: Predicates
  , senderBackend :: Some Backend
  , senderRepo :: Thrift.Repo
  }

instance HasPredicates Sender where
  getPid = getPid . senderPredicates

-- | Create an asynchronous 'Sender', run an action and wait until the sender
-- finished sending all batches. The 'Sender' is only usable within the action
-- but is thread safe. Any communication errors will be raised as exceptions.
--
-- A 'Sender' wraps a 'SendQueue', so 'withSender' takes
-- 'SendQueueSettings' to manage its behaviour.
withSender
  :: (Backend be)
  => be
  -> Thrift.Repo
  -> [SchemaPredicates]
  -> SendQueueSettings
  -> (Sender -> IO a)
  -> IO a
withSender backend repo proxy settings action = do
  predicates <- Backend.loadPredicates backend repo proxy
  withSendQueue backend repo settings $ \q ->
    action Sender
      { senderQueue = q
      , senderPredicates = predicates
      , senderBackend = Some backend
      , senderRepo = repo
      }

-- | Add a handle to the queue of writes that the sender is waiting
-- for.  This can be used when we have sent a batch to the server via
-- a different route (e.g. a query with store_derived_predicates=True)
-- and we want the sender to wait for the writes to complete.
addSenderWait
  :: Sender
  -> Thrift.Handle
  -> Int
  -> IO ()
addSenderWait Sender{..} = addSendQueueWait senderQueue


-- | An event that happens in a 'Writer' and can be logged
data WriterEvent
  =
    -- | Writer is pushing a patch to the sender
    WriterPushing Thrift.Batch

    -- | Writer is stalling due to the send queue being full
  | WriterStalling

    -- | Writer is resuming after having stalled previously
  | WriterResuming
      DiffTimePoints -- time spent stalled

-- | 'Writer' settings
data WriterSettings = WriterSettings
  { -- | Maximum size of a batch the write can accumulate before pushing it
    -- to the 'Sender' (soft limit)
    writerMaxSize :: !Int

    -- | Function called whenever a 'WriterEvent' occurs
  , writerLog :: WriterEvent -> IO ()
  }

instance Show WriterSettings where
  show _ = "WriterSettings{}"

instance Default WriterSettings where
  def = WriterSettings
    { writerMaxSize = 30000000
    , writerLog = const $ return ()
    }

-- | An asynchronous writer. It accumulates facts (via 'writeFacts') into
-- batches and pushes those batches to the underlying 'Sender' when they reach
-- a certain size.  Alternatively, the 'WriterContext' holds the 'Predicates'
-- and 'withBatchWriter' produces a single 'Batch' for regression testing.
--
-- NOTE: Writers serialise all writes - if you want to produce facts in
-- parallel, use multiple writers.
data Writer = Writer
  { writerPredicates :: !Predicates
  , writerSender :: Maybe Sender
  , writerFirstId :: !Fid
  , writerFacts :: !(MVar Facts)
  , writerSettings :: WriterSettings
  }

instance HasPredicates Writer where
  getPid = getPid . writerPredicates

newWriter :: Sender -> WriterSettings -> IO Writer
newWriter s settings = do
  first_id <- RTS.Fid <$> Backend.firstFreeId (senderBackend s) (senderRepo s)
  v <- newMVar =<< newFacts (senderPredicates s) (Just first_id)
  return Writer
    { writerPredicates = senderPredicates s
    , writerSender = Just s
    , writerFirstId = first_id
    , writerFacts = v
    , writerSettings = settings
    }

newWriterFromPredicates :: Predicates -> WriterSettings -> IO Writer
newWriterFromPredicates ps settings = do
  let first_id = lowestFid
  v <- newMVar =<< newFacts ps (Just first_id)
  return Writer
    { writerPredicates = ps
    , writerSender = Nothing
    , writerFirstId = first_id
    , writerFacts = v
    , writerSettings = settings
    }

-- Helper type for the @action@ passed to 'maybeFlush'
data MaybeFlush = DoNotFlushFacts | FlushFacts
  deriving (Eq)

flushWriter :: Writer -> Callback -> IO ()
flushWriter w callback = maybeFlush w callback $ const $ return FlushFacts

-- | Create a new 'Writer' based on the given 'Sender'. The facts created
-- by the 'Writer' will have fact ids which are guaranteed not to clash with
-- any facts already in the database at the point the 'Writer' is created. At
-- the end, the function will wait until all batches have been delivered to
-- and acknowledged by the server. This means that any subsequent queries will
-- return the facts produced by the 'Writer'.
withWriter :: Sender -> WriterSettings -> (Writer -> IO a) -> IO a
withWriter s settings action = do
  w <- newWriter s settings
  result <- action w
  done <- newEmptyTMVarIO
  flushWriter w (void . tryPutTMVar done)
  r <- atomically $ readTMVar done
  case r of
    Right () -> return result
    Left exc -> throwIO exc

-- | Create a new 'Writer' for regression testing.  This accumulates into
-- a single 'Facts' and produces a single 'Batch' without sending to a backend.
withBatchWriter
  :: Predicates -> WriterSettings -> (Writer -> IO a) -> IO (a, Thrift.Batch)
withBatchWriter ps settings action = do
  w <- newWriterFromPredicates ps settings
  result <- action w
  facts <- takeMVar (writerFacts w)
  batch <- serializeFacts facts
  return (result, batch)

-- | Write a bunch of facts to a 'Writer'. If the accumulated batch goes over
-- the threshold (cf. 'writerMaxSize') the batch will be pushed to the 'Sender'.
--
-- Because 'FactBuilder' uses a forall so as not to expose 'IO' (or similar),
-- fact ids created while running 'FactBuilder' are local to one call of
-- 'writeFacts' and cannot be saved or reused later.
writeFacts :: Writer -> FactBuilder -> IO ()
writeFacts w builder = maybeFlush w (const $ return ()) $ \facts -> do
  extendFacts facts builder
  mem <- factsMemory facts
  return $ if mem > writerMaxSize (writerSettings w)
    then FlushFacts
    else DoNotFlushFacts

-- @'maybeFlush' w calback action@ without a 'Sender' is used merely
-- runs the @action@ and @callback is ignored.
--
-- With a 'Sender' this checks 'MaybeFlush' and if the result is 'FlushFacts'
-- will write to the 'Sender' queue and execute the @callback@ , and if the
-- result is 'DoNotFlushFacts' the @callback@ is ignored.
maybeFlush :: Writer -> Callback -> (Facts -> IO MaybeFlush) -> IO ()
maybeFlush w callback action = modifyMVar_ (writerFacts w) $ \facts -> do
  flush <- action facts
  case writerSender w of
    Just sender | flush == FlushFacts -> do
      new_facts <- newFacts (writerPredicates w) (Just $ writerFirstId w)
      batch <- serializeFacts facts
      writerLog (writerSettings w) $ WriterPushing batch
      let write = writeSendQueue (senderQueue sender) batch callback
      -- NOTE: Yes, we're intentionally blocking inside modifyMVar_
      ok <- atomically $ (write >> return True) <|> return False
      when (not ok) $ do
        writerLog (writerSettings w) WriterStalling
        start <- getTimePoint
        atomically write
        elapsed <- getElapsedTime start
        writerLog (writerSettings w) $ WriterResuming elapsed
      return new_facts

    _ -> return facts


-- | Write facts to a Repo using an asynchronous sender, with all the
-- default settings.
basicWriter
  :: (Backend be)
  => be
  -> Thrift.Repo
  -> [SchemaPredicates]
  -> FactBuilder
  -> IO ()
basicWriter backend repo proxy builder =
  withSender backend repo proxy def $ \sender ->
  withWriter sender def $ \writer ->
  writeFacts writer builder
