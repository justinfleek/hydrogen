-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // reactive // hover-effect/state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverState — State machine for hover interaction.
-- |
-- | ## State Machine
-- |
-- | ```
-- | idle → entering → hovering → leaving → idle
-- | ```
-- |
-- | The hover state tracks where an element is in its hover lifecycle,
-- | enabling smooth transitions between states.

module Hydrogen.Schema.Reactive.HoverEffect.State
  ( HoverState
      ( HoverIdle
      , HoverEntering
      , HoverActive
      , HoverLeaving
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current hover state of an element
data HoverState
  = HoverIdle       -- ^ Not being hovered
  | HoverEntering   -- ^ Mouse just entered, transition starting
  | HoverActive     -- ^ Actively being hovered
  | HoverLeaving    -- ^ Mouse just left, transition ending

derive instance eqHoverState :: Eq HoverState
derive instance ordHoverState :: Ord HoverState

instance showHoverState :: Show HoverState where
  show HoverIdle = "idle"
  show HoverEntering = "entering"
  show HoverActive = "active"
  show HoverLeaving = "leaving"
