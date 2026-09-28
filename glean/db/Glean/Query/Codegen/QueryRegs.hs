{-
  Copyright (c) Meta Platforms, Inc. and affiliates.
  All rights reserved.

  This source code is licensed under the BSD-style license found in the
  LICENSE file in the root directory of this source tree.
-}

module Glean.Query.Codegen.QueryRegs
  ( QueryRegs(..)
  ) where

import Glean.Bytecode.Types
import Glean.RTS.Bytecode.Code

data QueryRegs = QueryRegs
  {
    -- | Start a new traversal of facts beginning with a given prefix
    seek
     :: Register 'Word -- predicate id
     -> Register 'DataPtr -- prefix
     -> Register 'DataPtr -- prefix end
     -> Register 'Word -- (output) token
     -> Code ()

  , seekWithinSection
     :: Register 'Word -- predicate id
     -> Register 'DataPtr -- prefix
     -> Register 'DataPtr -- prefix end
     -> Register 'Word -- section start
     -> Register 'Word -- section end
     -> Register 'Word -- (output) token
     -> Code ()

    -- | Fetch the current seek token
  , currentSeek
     :: Register 'Word
     -> Code ()

    -- | Release the state associated with an iterator token
  , endSeek
     :: Register 'Word
     -> Code ()

    -- | Grab the next fact in a traversal
  , next
     :: Register 'Word     -- token
     -> Bool               -- do we need the value?
     -> Register 'Word     -- result
     -> Register 'DataPtr  -- clause begin
     -> Register 'DataPtr  -- key end
     -> Register 'DataPtr  -- clause end
     -> Register 'Word     -- id
     -> Code ()

    -- | Fact lookup
  , lookupKeyValue
     :: Register 'Word
     -> Register 'BinaryOutputPtr
     -> Register 'BinaryOutputPtr
     -> Register 'Word
     -> Code ()

    -- | Record a result
  , result
     :: Register 'Word
     -> Register 'BinaryOutputPtr
     -> Register 'BinaryOutputPtr
     -> Register 'Word
     -> Code ()

    -- | Record a result, with a given pid and optional recursive expansion
  , resultWithPid
     :: Register 'Word
     -> Register 'BinaryOutputPtr
     -> Register 'BinaryOutputPtr
     -> Register 'Word
     -> Register 'Word
     -> Code ()

    -- | Record a new derived fact
  , newDerivedFact
     :: Register 'Word
     -> Register 'BinaryOutputPtr
     -> Register 'Word
     -> Register 'Word
     -> Code ()

  , firstFreeId
    :: Register 'Word -- first free id
    -> Code ()

  , newSet
    :: Register 'Word -- (output) set token
    -> Code ()

  , insertOutputSet
    :: Register 'Word -- set token
    -> Register 'BinaryOutputPtr
    -> Code ()

  , setToArray
    :: Register 'Word -- set token
    -> Register 'BinaryOutputPtr -- (output) array
    -> Code ()

  , freeSet
    :: Register 'Word -- set token (invalid after this call)
    -> Code ()

  , newWordSet
    :: Register 'Word -- (output) set token
    -> Code ()

  , insertWordSet
    :: Register 'Word -- set token
    -> Register 'Word
    -> Code ()

  , wordSetToArray
    :: Register 'Word -- set token
    -> Register 'BinaryOutputPtr -- (output) array
    -> Code ()

  , byteSetToByteArray
    :: Register 'Word -- set token
    -> Register 'BinaryOutputPtr -- (output) array
    -> Code ()

  , freeWordSet
    :: Register 'Word -- set token (invalid after this call)
    -> Code ()

    -- | Create a store for the auxiliary facts of an evaluation of
    -- recursive predicates. Its token is also a seek token: endSeek with it
    -- (or an earlier token) frees it. See Note [Isolation] in
    -- Glean.Query.Recursion.
  , newStore
    :: Register 'Word -- (output) store token
    -> Code ()

  , storeFirstFreeId
    :: Register 'Word -- store
    -> Register 'Word -- (output) first free id
    -> Code ()

    -- | Define a fact in a store
  , storeNewFact
    :: Register 'Word -- store
    -> Register 'Word -- predicate id
    -> Register 'BinaryOutputPtr -- clause
    -> Register 'Word -- key size
    -> Register 'Word -- (output) fact id
    -> Code ()

    -- | Start a traversal of the facts of a store in a range of ids
  , storeSeekWithinSection
    :: Register 'Word -- store
    -> Register 'Word -- predicate id
    -> Register 'DataPtr -- prefix
    -> Register 'DataPtr -- prefix end
    -> Register 'Word -- section start
    -> Register 'Word -- section end
    -> Register 'Word -- (output) token
    -> Code ()

    -- | Fact lookup in a store
  , storeLookupKeyValue
    :: Register 'Word -- store
    -> Register 'Word -- fact id
    -> Register 'BinaryOutputPtr
    -> Register 'BinaryOutputPtr
    -> Register 'Word -- (output) pid
    -> Code ()

    -- | Unused, temporarily kept for backwards compatibility
  , saveState :: Register 'Word

    -- | When compiling the queries of a saturation, the range of ids of
    -- the facts derived by the previous round, which 'SeekOnRoundNew'
    -- searches. 'SeekOnRoundOld' searches the ids before it, and
    -- 'SeekOnRoundAll' both.
    -- See Note [Semi-naive evaluation] in Glean.Query.Recursion.
  , roundRange :: Maybe (Register 'Word, Register 'Word)

    -- | Maximum number of results to return
  , maxResults :: Register 'Word

    -- | Maximum number of bytes to return
  , maxBytes :: Register 'Word
  }
