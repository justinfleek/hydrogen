-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // distributed // time-authority // vector-clock
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vector clocks for detecting concurrent events.
-- |
-- | ## What are Vector Clocks?
-- |
-- | Extension of Lamport timestamps that can detect concurrent events:
-- |
-- | - Each agent maintains a vector of counters (one per known agent)
-- | - On local event: increment own counter
-- | - On send: attach entire vector to message
-- | - On receive: merge vectors (point-wise max), then increment own
-- |
-- | ## Ordering Detection
-- |
-- | Vector clocks can determine:
-- | - A happened-before B (all components of A ≤ B, at least one <)
-- | - A happened-after B (inverse of above)
-- | - A and B are concurrent (neither happened-before)
-- | - A equals B (all components equal)

module Hydrogen.Distributed.TimeAuthority.VectorClock
  ( -- * Vector Clock Type
    VectorClock
  , mkVectorClock
  , vectorTick
  , vectorSend
  , vectorReceive
  , vectorMerge
  , vectorCompare
  
  -- * Vector Ordering
  , VectorOrdering
      ( VectorLT
      , VectorGT
      , VectorEQ
      , VectorConcurrent
      )
  , isConcurrent
  , isHappenedBefore
  
  -- * Predicates
  , allHappenedBefore
  ) where

import Prelude
  ( class Eq
  , class Show
  , Ordering(LT, GT, EQ)
  , show
  , compare
  , map
  , (==)
  , (<>)
  , (+)
  , (#)
  )

import Data.Array as Array
import Data.Foldable (foldl, all)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Distributed.TimeAuthority.Lamport (AgentId, maxInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // vector clocks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vector clock — detects concurrent events
-- |
-- | Maps each known agent to their logical counter.
-- | Can determine happened-before, happened-after, or concurrent relationships.
newtype VectorClock = VectorClock (Map AgentId Int)

derive instance eqVectorClock :: Eq VectorClock

instance showVectorClock :: Show VectorClock where
  show (VectorClock m) = "VC(" <> show (Map.toUnfoldable m :: Array (Tuple AgentId Int)) <> ")"

-- | Create empty vector clock for an agent
mkVectorClock :: AgentId -> VectorClock
mkVectorClock agentId = VectorClock (Map.singleton agentId 0)

-- | Tick vector clock for local event
vectorTick :: AgentId -> VectorClock -> VectorClock
vectorTick agentId (VectorClock m) =
  let current = fromMaybe 0 (Map.lookup agentId m)
  in VectorClock (Map.insert agentId (current + 1) m)

-- | Prepare vector clock for sending (tick then return)
vectorSend :: AgentId -> VectorClock -> Tuple VectorClock VectorClock
vectorSend agentId vc =
  let newVc = vectorTick agentId vc
  in Tuple newVc newVc

-- | Update vector clock on receiving message
vectorReceive :: AgentId -> VectorClock -> VectorClock -> VectorClock
vectorReceive agentId local remote =
  vectorTick agentId (vectorMerge local remote)

-- | Merge two vector clocks (point-wise maximum)
vectorMerge :: VectorClock -> VectorClock -> VectorClock
vectorMerge (VectorClock a) (VectorClock b) =
  VectorClock (Map.unionWith maxInt a b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // vector ordering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ordering relationship between vector clocks
data VectorOrdering
  = VectorLT       -- First happened strictly before second
  | VectorGT       -- First happened strictly after second
  | VectorEQ       -- Identical clocks
  | VectorConcurrent  -- Neither happened before the other

derive instance eqVectorOrdering :: Eq VectorOrdering

instance showVectorOrdering :: Show VectorOrdering where
  show VectorLT = "HappenedBefore"
  show VectorGT = "HappenedAfter"
  show VectorEQ = "Equal"
  show VectorConcurrent = "Concurrent"

-- | Compare two vector clocks
vectorCompare :: VectorClock -> VectorClock -> VectorOrdering
vectorCompare (VectorClock a) (VectorClock b) =
  let
    -- Get all keys from both maps (deduplicated)
    allKeysRaw = Array.concat 
      [ Map.keys a # Array.fromFoldable
      , Map.keys b # Array.fromFoldable
      ]
    allKeys = arrayNub allKeysRaw
    
    -- Compare each component
    comparisons = map (\k -> 
      let va = fromMaybe 0 (Map.lookup k a)
          vb = fromMaybe 0 (Map.lookup k b)
      in compare va vb
    ) allKeys
    
    hasLT = Array.any (_ == LT) comparisons
    hasGT = Array.any (_ == GT) comparisons
  in
    case Tuple hasLT hasGT of
      Tuple false false -> VectorEQ
      Tuple true false -> VectorLT
      Tuple false true -> VectorGT
      Tuple true true -> VectorConcurrent

-- | Check if events are concurrent (neither happened-before the other)
isConcurrent :: VectorClock -> VectorClock -> Boolean
isConcurrent a b = vectorCompare a b == VectorConcurrent

-- | Check if first clock strictly happened-before second
isHappenedBefore :: VectorClock -> VectorClock -> Boolean
isHappenedBefore a b = vectorCompare a b == VectorLT

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all vector clocks in array have happened-before reference
allHappenedBefore :: VectorClock -> Array VectorClock -> Boolean
allHappenedBefore reference clocks = all (\c -> isHappenedBefore c reference) clocks

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placeholder for Array.nub (deduplicate)
arrayNub :: forall a. Eq a => Array a -> Array a
arrayNub = foldl (\acc x -> if elemArray x acc then acc else Array.snoc acc x) []

-- | Check if element is in array
elemArray :: forall a. Eq a => a -> Array a -> Boolean
elemArray x arr = Array.any (_ == x) arr
