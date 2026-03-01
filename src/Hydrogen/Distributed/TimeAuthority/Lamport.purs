-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // distributed // time-authority // lamport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lamport and Logical timestamps for causal ordering.
-- |
-- | ## Lamport Timestamps
-- |
-- | Scalar logical clocks that establish causal ordering:
-- |
-- | - Each agent maintains a counter
-- | - On local event: counter++
-- | - On send: attach counter to message
-- | - On receive: counter = max(local, received) + 1
-- |
-- | Property: If A causally precedes B, then L(A) < L(B).
-- | Note: L(A) < L(B) does NOT imply A causally precedes B.
-- |
-- | ## Logical Time
-- |
-- | Extension that pairs Lamport counter with agent identity.
-- | Useful for total ordering when counters are equal.

module Hydrogen.Distributed.TimeAuthority.Lamport
  ( -- * Core Type Aliases
    AgentId
  , WallClock
  
  -- * Lamport Timestamps
  , LamportTime
  , mkLamportTime
  , lamportTick
  , lamportSend
  , lamportReceive
  , lamportCompare
  , happenedBefore
  
  -- * Logical Time (with Agent ID)
  , LogicalTime
  , mkLogicalTime
  , logicalTick
  , logicalSend
  , logicalReceive
  , logicalCompare
  , logicalHappenedBefore
  
  -- * Internal Helpers
  , maxInt
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(EQ)
  , show
  , compare
  , (<)
  , (<>)
  , (>=)
  , (+)
  )

import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique agent identifier (UUID5 string)
type AgentId = String

-- | Wall clock time in milliseconds since epoch
type WallClock = Number

-- ════════��════════════════════════════════════════════════════════════════════
--                                                         // lamport timestamps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lamport timestamp — scalar logical clock
-- |
-- | Provides causal ordering: if event A causally precedes B, then L(A) < L(B).
-- | However, L(A) < L(B) does NOT imply A causally precedes B.
newtype LamportTime = LamportTime Int

derive instance eqLamportTime :: Eq LamportTime
derive instance ordLamportTime :: Ord LamportTime

instance showLamportTime :: Show LamportTime where
  show (LamportTime t) = "L(" <> show t <> ")"

-- | Create initial Lamport timestamp
mkLamportTime :: LamportTime
mkLamportTime = LamportTime 0

-- | Increment for local event
lamportTick :: LamportTime -> LamportTime
lamportTick (LamportTime t) = LamportTime (t + 1)

-- | Prepare timestamp for sending (tick then return)
lamportSend :: LamportTime -> Tuple LamportTime LamportTime
lamportSend lt = 
  let newTime = lamportTick lt
  in Tuple newTime newTime

-- | Update on receiving a message with remote timestamp
lamportReceive :: LamportTime -> LamportTime -> LamportTime
lamportReceive (LamportTime local) (LamportTime remote) =
  LamportTime (maxInt local remote + 1)

-- | Compare two Lamport timestamps
lamportCompare :: LamportTime -> LamportTime -> Ordering
lamportCompare (LamportTime a) (LamportTime b) = compare a b

-- | Check if first timestamp happened-before second
-- |
-- | Note: This is a necessary but not sufficient condition for causality.
happenedBefore :: LamportTime -> LamportTime -> Boolean
happenedBefore (LamportTime a) (LamportTime b) = a < b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // logical time
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logical time combining Lamport timestamp with agent identity
-- |
-- | Includes wall clock for debugging/logging, but ordering uses Lamport only.
type LogicalTime =
  { wallClock :: WallClock
  , logicalCounter :: Int
  , agentId :: AgentId
  }

-- | Create initial logical time
mkLogicalTime :: AgentId -> WallClock -> LogicalTime
mkLogicalTime agentId wallClock =
  { wallClock
  , logicalCounter: 0
  , agentId
  }

-- | Tick logical time for local event
logicalTick :: WallClock -> LogicalTime -> LogicalTime
logicalTick newWallClock lt = lt
  { wallClock = newWallClock
  , logicalCounter = lt.logicalCounter + 1
  }

-- | Prepare logical time for sending
logicalSend :: WallClock -> LogicalTime -> Tuple LogicalTime LogicalTime
logicalSend wallClock lt =
  let newTime = logicalTick wallClock lt
  in Tuple newTime newTime

-- | Update logical time on receiving message
logicalReceive :: WallClock -> LogicalTime -> LogicalTime -> LogicalTime
logicalReceive wallClock local remote = local
  { wallClock = wallClock
  , logicalCounter = maxInt local.logicalCounter remote.logicalCounter + 1
  }

-- | Compare logical times (by counter, then agent ID for tiebreak)
logicalCompare :: LogicalTime -> LogicalTime -> Ordering
logicalCompare a b =
  case compare a.logicalCounter b.logicalCounter of
    EQ -> compare a.agentId b.agentId
    other -> other

-- | Check if first logical time happened-before second
logicalHappenedBefore :: LogicalTime -> LogicalTime -> Boolean
logicalHappenedBefore a b = a.logicalCounter < b.logicalCounter

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two integers
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b
