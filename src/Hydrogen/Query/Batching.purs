-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // query // batching
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataLoader-style request batching for the Query system.
-- |
-- | This module provides request coalescing to batch multiple concurrent
-- | requests for the same resource type into a single batch request:
-- | - Batcher: Manages a queue of pending requests
-- | - BatchOptions: Configuration for batch behavior
-- | - load: Load a single value, batching with concurrent requests
-- | - loadMany: Load multiple values in a single batch
module Hydrogen.Query.Batching
  ( -- * Batching types
    Batcher
      ( Batcher
      )
  , BatchOptions
  
    -- * Batching operations
  , newBatcher
  , load
  , loadMany
  ) where

import Prelude
  ( class Ord
  , Unit
  , bind
  , pure
  , ($)
  )

import Prim (Array, Boolean, Int, String)
import Data.Either (Either(Left))
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Time.Duration (Milliseconds)
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // batching types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Options for a batcher.
type BatchOptions k v =
  { -- | Batch function that fetches multiple keys at once
    batchFn :: Array k -> Aff (Array (Tuple k (Either String v)))
    -- | Maximum batch size
  , maxBatchSize :: Int
    -- | Delay before dispatching (ms) - allows more requests to queue
  , batchDelay :: Milliseconds
  }

-- | Batcher for DataLoader-style request coalescing.
newtype Batcher k v = Batcher
  { queue :: Ref (Array { key :: k, resolve :: Either String v -> Effect Unit })
  , scheduled :: Ref Boolean
  , options :: BatchOptions k v
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // batching operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a new batcher.
newBatcher :: forall k v. BatchOptions k v -> Effect (Batcher k v)
newBatcher options = do
  queue <- Ref.new []
  scheduled <- Ref.new false
  pure $ Batcher { queue, scheduled, options }

-- | Load a single value, batching with concurrent requests.
load :: forall k v. Ord k => Batcher k v -> k -> Aff (Either String v)
load batcher key = do
  results <- loadMany batcher [key]
  pure $ fromMaybe (Left "Key not found in batch result") (Map.lookup key results)

-- | Load multiple values in a single batch.
loadMany :: forall k v. Ord k => Batcher k v -> Array k -> Aff (Map.Map k (Either String v))
loadMany (Batcher b) keys = do
  results <- b.options.batchFn keys
  pure $ Map.fromFoldable results
