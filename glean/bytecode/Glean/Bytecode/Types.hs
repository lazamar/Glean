module Glean.Bytecode.Types
  ( Ty(..)
  , Control(..)
  ) where

-- | Instruction argument types
data Ty
  = Void -- ^ function return type only
  | Word -- ^ 64 bit word
  | WordPtr -- ^ pointer to 64 bit word
  | Literal -- ^ index into the (string) literal table
  | Offset -- ^ jump offset (relative to start of next instruction)
  | Offsets -- ^ array of jump offsets (length + array in the insn stream)
  | DataPtr -- ^ a void pointer
  | BinaryOutputPtr -- ^ pointer to binary::Output (temporary, will be removed)
  | Fun [Ty] Ty -- ^ pointer to std::function (temporary, will be removed)
  deriving(Eq, Show)

data Control
  = FallThrough
  | CondJump
  | UncondJump
  deriving(Eq, Ord, Enum, Bounded, Read, Show)
