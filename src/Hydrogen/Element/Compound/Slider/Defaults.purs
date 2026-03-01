-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // slider // defaults
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider Defaults — Sensible fallback values for all Schema atoms.
-- |
-- | These defaults provide a neutral, accessible appearance when no
-- | brand-specific atoms are supplied. Components should resolve
-- | `Nothing` to these fallbacks, ensuring sliders work out-of-box.
-- |
-- | ## Design Rationale
-- |
-- | - **Track**: Neutral gray — doesn't compete with range fill
-- | - **Range**: Blue — high contrast, universally recognizable
-- | - **Thumb**: White with blue border — clear grab target
-- | - **Focus ring**: Blue — accessibility-compliant focus state
-- | - **Dimensions**: 8px track, 20px thumb — touch-friendly

module Hydrogen.Element.Compound.Slider.Defaults
  ( -- * Default Props
    defaultProps
    
  -- * Default Colors
  , defaultTrackColor
  , defaultRangeColor
  , defaultThumbColor
  , defaultThumbBorderColor
  , defaultFocusRingColor
  , defaultTickColor
  , defaultTooltipBgColor
  , defaultTooltipTextColor
  
  -- * Default Dimensions
  , defaultTrackHeight
  , defaultThumbSize
  , defaultThumbBorderWidth
  
  -- * Default Geometry
  , defaultBorderRadius
  
  -- * Default Motion
  , defaultTransitionDuration
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Element.Compound.Slider.Types
  ( Orientation(Horizontal)
  , SliderProps
  )
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // default props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default properties
-- |
-- | Visual properties default to `Nothing` (use sensible fallbacks).
-- | This ensures sliders work with any brand without hardcoded values.
defaultProps :: forall msg. SliderProps msg
defaultProps =
  { value: 0.0
  , rangeVal: { low: 0.0, high: 100.0 }
  , minVal: 0.0
  , maxVal: 100.0
  , step: 1.0
  , disabled: false
  , orientation: Horizontal
  , showTicks: false
  , showTooltip: false
  , trackColor: Nothing
  , rangeColor: Nothing
  , thumbColor: Nothing
  , thumbBorderColor: Nothing
  , focusRingColor: Nothing
  , tickColor: Nothing
  , tooltipBackgroundColor: Nothing
  , tooltipTextColor: Nothing
  , trackHeight: Nothing
  , thumbSize: Nothing
  , thumbBorderWidth: Nothing
  , borderRadius: Nothing
  , transitionDuration: Nothing
  , onChange: Nothing
  , onRangeChange: Nothing
  , ariaLabel: "Slider"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // default colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default track color (neutral gray)
-- |
-- | Gray-200 equivalent — subtle background for unfilled portion
defaultTrackColor :: Color.RGB
defaultTrackColor = Color.rgb 229 231 235

-- | Default range color (blue)
-- |
-- | Blue-500 equivalent — clear visual indication of selected range
defaultRangeColor :: Color.RGB
defaultRangeColor = Color.rgb 59 130 246

-- | Default thumb color (white)
-- |
-- | Pure white — high contrast grab target
defaultThumbColor :: Color.RGB
defaultThumbColor = Color.rgb 255 255 255

-- | Default thumb border color (same as range)
-- |
-- | Blue-500 — matches range for visual continuity
defaultThumbBorderColor :: Color.RGB
defaultThumbBorderColor = Color.rgb 59 130 246

-- | Default focus ring color (blue with transparency handled via box-shadow)
-- |
-- | Blue-500 — accessibility-compliant focus indication
defaultFocusRingColor :: Color.RGB
defaultFocusRingColor = Color.rgb 59 130 246

-- | Default tick color (muted)
-- |
-- | Gray-400 — subtle tick marks that don't compete with slider
defaultTickColor :: Color.RGB
defaultTickColor = Color.rgb 156 163 175

-- | Default tooltip background (dark)
-- |
-- | Gray-800 — high contrast background for tooltip text
defaultTooltipBgColor :: Color.RGB
defaultTooltipBgColor = Color.rgb 31 41 55

-- | Default tooltip text (white)
-- |
-- | Pure white — maximum readability on dark background
defaultTooltipTextColor :: Color.RGB
defaultTooltipTextColor = Color.rgb 255 255 255

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // default dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default track height
-- |
-- | 8px — visible but not dominant
defaultTrackHeight :: Device.Pixel
defaultTrackHeight = Device.px 8.0

-- | Default thumb size
-- |
-- | 20px — touch-friendly target (meets 44px when including padding)
defaultThumbSize :: Device.Pixel
defaultThumbSize = Device.px 20.0

-- | Default thumb border width
-- |
-- | 2px — visible border without being heavy
defaultThumbBorderWidth :: Device.Pixel
defaultThumbBorderWidth = Device.px 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // default geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default border radius (full/pill)
-- |
-- | Full radius — creates pill-shaped track
defaultBorderRadius :: Geometry.Radius
defaultBorderRadius = Geometry.full

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // default motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default transition duration
-- |
-- | 150ms — snappy but smooth transitions
defaultTransitionDuration :: Temporal.Milliseconds
defaultTransitionDuration = Temporal.ms 150.0
