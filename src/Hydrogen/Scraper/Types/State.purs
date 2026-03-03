-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // scraper // types // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interactive state types for 1:1 visual parity.
-- |
-- | Captures element appearance in different interaction states:
-- | - Default (rest state)
-- | - Hover
-- | - Focus
-- | - Active (pressed)
-- | - Visited (for links)
-- | - Disabled
-- |
-- | Each state captures the visual differences from default.

module Hydrogen.Scraper.Types.State
  ( -- * Types
    InteractionState(..)
  , StateDiff
  , InteractiveStyles
  
  -- * Constructors
  , emptyStateDiff
  , emptyInteractiveStyles
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow, noShadow)
import Hydrogen.Scraper.Types.Transform (ExtractedTransform, identityTransform)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // interaction state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS pseudo-class states
data InteractionState
  = Default
  | Hover
  | Focus
  | FocusVisible
  | FocusWithin
  | Active
  | Visited
  | Disabled
  | Checked
  | Indeterminate

derive instance eqInteractionState :: Eq InteractionState
derive instance ordInteractionState :: Ord InteractionState

instance showInteractionState :: Show InteractionState where
  show Default = "default"
  show Hover = "hover"
  show Focus = "focus"
  show FocusVisible = "focus-visible"
  show FocusWithin = "focus-within"
  show Active = "active"
  show Visited = "visited"
  show Disabled = "disabled"
  show Checked = "checked"
  show Indeterminate = "indeterminate"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // state diff
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visual differences from default state
-- |
-- | Only stores properties that change. Nothing means "same as default".
type StateDiff =
  { -- Colors
    backgroundColor :: Maybe OKLCH
  , color :: Maybe OKLCH
  , borderColor :: Maybe OKLCH
  
  -- Outline (focus rings)
  , outlineColor :: Maybe OKLCH
  , outlineWidth :: Maybe Pixel
  , outlineOffset :: Maybe Pixel
  
  -- Transforms (hover effects)
  , transform :: Maybe ExtractedTransform
  
  -- Shadows
  , shadow :: Maybe LayeredShadow
  
  -- Opacity
  , opacity :: Maybe Number
  
  -- Cursor
  , cursor :: Maybe String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // interactive styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All interactive states for an element
-- |
-- | Each state contains only the differences from default.
-- | Nothing means the element doesn't respond to that state.
type InteractiveStyles =
  { hover :: Maybe StateDiff
  , focus :: Maybe StateDiff
  , focusVisible :: Maybe StateDiff
  , active :: Maybe StateDiff
  , visited :: Maybe StateDiff
  , disabled :: Maybe StateDiff
  , checked :: Maybe StateDiff
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty state diff (no changes)
emptyStateDiff :: StateDiff
emptyStateDiff =
  { backgroundColor: Nothing
  , color: Nothing
  , borderColor: Nothing
  , outlineColor: Nothing
  , outlineWidth: Nothing
  , outlineOffset: Nothing
  , transform: Nothing
  , shadow: Nothing
  , opacity: Nothing
  , cursor: Nothing
  }

-- | Empty interactive styles (no state responses)
emptyInteractiveStyles :: InteractiveStyles
emptyInteractiveStyles =
  { hover: Nothing
  , focus: Nothing
  , focusVisible: Nothing
  , active: Nothing
  , visited: Nothing
  , disabled: Nothing
  , checked: Nothing
  }
