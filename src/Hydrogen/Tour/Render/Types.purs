-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // tour // render // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Configuration Types for Tour Rendering
-- |
-- | This module defines the configuration records and ADTs used by the
-- | tour render functions. Types are separated to enable clean imports
-- | and reduce coupling between render components.

module Hydrogen.Tour.Render.Types
  ( -- * Click Behavior
    ClickBehavior(AdvanceOnClick, CloseOnClick, BlockClick)
    -- * Configuration Records
  , OverlayConfig
  , SpotlightConfig
  , TooltipConfig
  , NavigationConfig
    -- * Progress Style
  , ProgressStyle(ProgressDots, ProgressBar, ProgressFraction, ProgressHidden)
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe)
import Hydrogen.Tour.Step (Button)
import Hydrogen.Tour.Types (Pixel, Placement, Progress, StepId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // click behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay click behavior
data ClickBehavior msg
  = AdvanceOnClick msg
    -- ^ Clicking advances to next step
  | CloseOnClick msg
    -- ^ Clicking closes the tour
  | BlockClick
    -- ^ Clicking does nothing (modal behavior)

derive instance eqClickBehavior :: Eq msg => Eq (ClickBehavior msg)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // configuration records
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for the overlay backdrop
type OverlayConfig msg =
  { clickBehavior :: ClickBehavior msg
    -- ^ What happens when overlay is clicked
  , blurBackground :: Boolean
    -- ^ Whether to apply blur effect
  , reducedMotion :: Boolean
    -- ^ Respect prefers-reduced-motion
  , overlayOpacity :: Number
    -- ^ Opacity of the overlay (0.0 to 1.0)
  }

-- | Configuration for the spotlight cutout
type SpotlightConfig =
  { targetRect :: { x :: Int, y :: Int, width :: Int, height :: Int }
    -- ^ Bounding box of the target element
  , padding :: Pixel
    -- ^ Extra space around the target
  , borderRadius :: Pixel
    -- ^ Corner radius of the cutout
  , pulseAnimation :: Boolean
    -- ^ Whether to show pulse effect
  , transitionDuration :: Int
    -- ^ Milliseconds for morph transition
  }

-- | Configuration for the tooltip
type TooltipConfig msg =
  { title :: Maybe String
    -- ^ Tooltip heading
  , body :: Maybe String
    -- ^ Tooltip body text
  , placement :: Placement
    -- ^ Positioning relative to target
  , showArrow :: Boolean
    -- ^ Whether to show pointing arrow
  , progress :: Maybe Progress
    -- ^ Progress through tour
  , progressStyle :: ProgressStyle
    -- ^ How to display progress
  , buttons :: Array (Button msg)
    -- ^ Navigation buttons
  , onClose :: msg
    -- ^ Message when close button clicked
  , onNext :: msg
    -- ^ Message for next step
  , onPrev :: msg
    -- ^ Message for previous step
  , onSkip :: msg
    -- ^ Message for skip tour
  , onComplete :: msg
    -- ^ Message for complete tour
  , onGoTo :: StepId -> msg
    -- ^ Message for go-to step
  , isFirstStep :: Boolean
    -- ^ Whether this is the first step
  , isLastStep :: Boolean
    -- ^ Whether this is the last step
  }

-- | Configuration for navigation buttons
type NavigationConfig msg =
  { buttons :: Array (Button msg)
    -- ^ Buttons to render
  , showKeyboardHints :: Boolean
    -- ^ Show keyboard shortcut hints
  , isFirstStep :: Boolean
    -- ^ Disable prev on first step
  , isLastStep :: Boolean
    -- ^ Change next to complete on last step
  , onNext :: msg
    -- ^ Message for next action
  , onPrev :: msg
    -- ^ Message for prev action
  , onSkip :: msg
    -- ^ Message for skip action
  , onComplete :: msg
    -- ^ Message for complete action
  , onGoTo :: StepId -> msg
    -- ^ Message for go-to action
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // progress style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style for progress indicator
data ProgressStyle
  = ProgressDots
    -- ^ Dot indicators
  | ProgressBar
    -- ^ Horizontal bar
  | ProgressFraction
    -- ^ Text "2 of 5"
  | ProgressHidden
    -- ^ No progress shown

derive instance eqProgressStyle :: Eq ProgressStyle

instance showProgressStyle :: Show ProgressStyle where
  show ProgressDots = "ProgressDots"
  show ProgressBar = "ProgressBar"
  show ProgressFraction = "ProgressFraction"
  show ProgressHidden = "ProgressHidden"
