-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // distributed // viewport-sync // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shared effect state for cross-viewport coordination.
-- |
-- | When multiple viewports display the same animation or transition,
-- | they need to share effect state to stay in sync. This module provides:
-- |
-- | - SharedEffectState: A single effect's state across viewports
-- | - EffectRegistry: Collection of all shared effects

module Hydrogen.Distributed.ViewportSync.Effects
  ( -- * Shared Effect State
    SharedEffectState
  , mkSharedEffect
  , subscribeViewport
  , unsubscribeViewport
  , updateEffectPhase
  , isEffectOwner
  , getSubscribers
  
  -- * Effect Registry
  , EffectRegistry
  , mkEffectRegistry
  , registerEffect
  , unregisterEffect
  , getEffect
  , getEffectsForViewport
  , tickEffects
  ) where

import Prelude
  ( map
  , show
  , (||)
  , (>=)
  , (==)
  , (+)
  , (<>)
  , (#)
  )

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Distributed.TimeAuthority 
  ( FrameNumber
  )

import Hydrogen.Distributed.ViewportSync.Types
  ( ViewportId
  , EffectId
  , EffectPhase
      ( EffectIdle
      , EffectRunning
      , EffectComplete
      , EffectPaused
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // shared effect state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shared effect state for cross-viewport coordination
type SharedEffectState =
  { effectId :: EffectId
  , owningViewport :: ViewportId
  , subscribedViewports :: Set ViewportId
  , currentPhase :: EffectPhase
  , lastSyncFrame :: FrameNumber
  , priority :: Int                   -- Higher priority effects sync first
  }

-- | Create shared effect
mkSharedEffect :: EffectId -> ViewportId -> Int -> SharedEffectState
mkSharedEffect effectId owningViewport priority =
  { effectId
  , owningViewport
  , subscribedViewports: Set.singleton owningViewport
  , currentPhase: EffectIdle
  , lastSyncFrame: 0
  , priority
  }

-- | Subscribe viewport to effect
subscribeViewport :: ViewportId -> SharedEffectState -> SharedEffectState
subscribeViewport viewportId effect = effect
  { subscribedViewports = Set.insert viewportId effect.subscribedViewports }

-- | Unsubscribe viewport from effect
unsubscribeViewport :: ViewportId -> SharedEffectState -> SharedEffectState
unsubscribeViewport viewportId effect = effect
  { subscribedViewports = Set.delete viewportId effect.subscribedViewports }

-- | Update effect phase
updateEffectPhase :: EffectPhase -> FrameNumber -> SharedEffectState -> SharedEffectState
updateEffectPhase phase frame effect = effect
  { currentPhase = phase
  , lastSyncFrame = frame
  }

-- | Check if viewport owns this effect
isEffectOwner :: ViewportId -> SharedEffectState -> Boolean
isEffectOwner viewportId effect = effect.owningViewport == viewportId

-- | Get all subscribed viewports
getSubscribers :: SharedEffectState -> Array ViewportId
getSubscribers effect = Set.toUnfoldable effect.subscribedViewports

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registry of shared effects
type EffectRegistry =
  { effects :: Map EffectId SharedEffectState
  , nextId :: Int
  }

-- | Create empty effect registry
mkEffectRegistry :: EffectRegistry
mkEffectRegistry =
  { effects: Map.empty
  , nextId: 1
  }

-- | Register new effect
registerEffect :: ViewportId -> Int -> EffectRegistry -> Tuple EffectId EffectRegistry
registerEffect owningViewport priority registry =
  let
    effectId = "effect-" <> show registry.nextId
    effect = mkSharedEffect effectId owningViewport priority
    newRegistry =
      { effects: Map.insert effectId effect registry.effects
      , nextId: registry.nextId + 1
      }
  in Tuple effectId newRegistry

-- | Unregister effect
unregisterEffect :: EffectId -> EffectRegistry -> EffectRegistry
unregisterEffect effectId registry = registry
  { effects = Map.delete effectId registry.effects }

-- | Get effect by ID
getEffect :: EffectId -> EffectRegistry -> Maybe SharedEffectState
getEffect effectId registry = Map.lookup effectId registry.effects

-- | Get all effects owned by or subscribed to by a viewport
getEffectsForViewport :: ViewportId -> EffectRegistry -> Array SharedEffectState
getEffectsForViewport viewportId registry =
  Array.filter (viewportInEffect viewportId) 
    (Map.values registry.effects # Array.fromFoldable)

-- | Check if viewport is involved in effect
viewportInEffect :: ViewportId -> SharedEffectState -> Boolean
viewportInEffect viewportId effect =
  effect.owningViewport == viewportId || 
  Set.member viewportId effect.subscribedViewports

-- | Tick all effects (advance running effects)
tickEffects :: FrameNumber -> Number -> EffectRegistry -> EffectRegistry
tickEffects frame deltaProgress registry = registry
  { effects = map (tickEffect frame deltaProgress) registry.effects }

-- | Tick single effect
tickEffect :: FrameNumber -> Number -> SharedEffectState -> SharedEffectState
tickEffect frame deltaProgress effect = case effect.currentPhase of
  EffectRunning progress ->
    let newProgress = progress + deltaProgress
    in if newProgress >= 1.0
         then effect { currentPhase = EffectComplete, lastSyncFrame = frame }
         else effect { currentPhase = EffectRunning newProgress, lastSyncFrame = frame }
  EffectIdle -> effect
  EffectComplete -> effect
  EffectPaused _ -> effect
