-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // tour // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Element Render Functions for Product Tours
-- |
-- | This module provides pure render functions that output Hydrogen Elements.
-- | These are framework-agnostic and can be interpreted to any rendering target:
-- |
-- | - DOM (browser)
-- | - Static HTML (SSG)
-- | - Test harness
-- |
-- | ## Design Philosophy
-- |
-- | All render functions are pure functions producing Element values.
-- | No effects, no framework dependencies. Just data describing UI.
-- |
-- | Data attributes encode runtime behavior that the interpreter handles:
-- | - `data-tour-overlay` — Overlay identification
-- | - `data-tour-spotlight` — Spotlight positioning
-- | - `data-tour-tooltip` — Tooltip behavior
-- | - `data-reduced-motion` — Motion preference awareness
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Hydrogen.Tour.Render.Types` — Configuration types
-- | - `Hydrogen.Tour.Render.Overlay` — Overlay backdrop
-- | - `Hydrogen.Tour.Render.Spotlight` — Target highlight
-- | - `Hydrogen.Tour.Render.Tooltip` — Step content tooltip
-- | - `Hydrogen.Tour.Render.Progress` — Progress indicators
-- | - `Hydrogen.Tour.Render.Navigation` — Button row
-- | - `Hydrogen.Tour.Render.Arrow` — Pointing arrow
-- | - `Hydrogen.Tour.Render.Helpers` — Utility functions
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Render as Render
-- |
-- | myOverlay :: Element TourMsg
-- | myOverlay = Render.tourOverlay
-- |   { clickBehavior: CloseOnClick (DismissTour ClickedOverlay)
-- |   , blurBackground: true
-- |   , reducedMotion: false
-- |   , overlayOpacity: 0.75
-- |   }
-- | ```

module Hydrogen.Tour.Render
  ( -- * Configuration Types (re-exported from Types)
    module Types
    -- * Render Functions (re-exported from submodules)
  , module Arrow
  , module Helpers
  , module Navigation
  , module Overlay
  , module Progress
  , module Spotlight
  , module Tooltip
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Re-export all configuration types
import Hydrogen.Tour.Render.Types
  ( ClickBehavior(AdvanceOnClick, BlockClick, CloseOnClick)
  , NavigationConfig
  , OverlayConfig
  , ProgressStyle(ProgressBar, ProgressDots, ProgressFraction, ProgressHidden)
  , SpotlightConfig
  , TooltipConfig
  ) as Types

-- | Re-export render functions
import Hydrogen.Tour.Render.Arrow (sideToRotation, tourArrow) as Arrow
import Hydrogen.Tour.Render.Helpers (placementToClass, sideToString) as Helpers
import Hydrogen.Tour.Render.Navigation (tourNavigation) as Navigation
import Hydrogen.Tour.Render.Overlay (tourOverlay) as Overlay
import Hydrogen.Tour.Render.Progress (tourProgress) as Progress
import Hydrogen.Tour.Render.Spotlight (tourSpotlight) as Spotlight
import Hydrogen.Tour.Render.Tooltip (tourTooltip) as Tooltip
