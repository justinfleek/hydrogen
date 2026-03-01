-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // slider // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider Types — Core type definitions for the Slider compound.
-- |
-- | This module defines:
-- | - `Orientation` — Horizontal or Vertical slider axis
-- | - `RangeValue` — Low/high bounds for range sliders
-- | - `SliderProps` — Complete property record for slider configuration
-- | - `SliderProp` — Property modifier function type

module Hydrogen.Element.Compound.Slider.Types
  ( -- * Types
    Orientation(Horizontal, Vertical)
  , RangeValue
  , SliderProps
  , SliderProp
  ) where

import Prelude
  ( class Eq
  )

import Data.Maybe (Maybe)

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider orientation
-- |
-- | Determines the axis along which the slider operates:
-- | - `Horizontal` — Left-to-right value progression (default)
-- | - `Vertical` — Bottom-to-top value progression
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // range value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range slider value
-- |
-- | Represents the low and high bounds for a dual-thumb range slider.
-- | Invariant: `low <= high` should be maintained by the application.
type RangeValue =
  { low :: Number
  , high :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // slider props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider properties
-- |
-- | All visual properties accept Schema atoms directly.
-- | Use `Maybe` for optional properties that should use defaults.
-- |
-- | ## Property Categories
-- |
-- | **State Properties**
-- | - `value` — Current slider position (single slider)
-- | - `rangeVal` — Low/high bounds (range slider)
-- | - `minVal`, `maxVal` — Value bounds
-- | - `step` — Increment step size
-- | - `disabled` — Interaction state
-- | - `orientation` — Horizontal or Vertical
-- | - `showTicks`, `showTooltip` — Visual aids
-- |
-- | **Color Atoms**
-- | Track, range fill, thumb, borders, focus ring, ticks, tooltip
-- |
-- | **Dimension Atoms**
-- | Track height/width, thumb size, border widths
-- |
-- | **Geometry Atoms**
-- | Border radius for rounded corners
-- |
-- | **Motion Atoms**
-- | Transition duration for smooth animations
-- |
-- | **Behavior**
-- | Change handlers and accessibility labels
type SliderProps msg =
  { -- State
    value :: Number
  , rangeVal :: RangeValue
  , minVal :: Number
  , maxVal :: Number
  , step :: Number
  , disabled :: Boolean
  , orientation :: Orientation
  , showTicks :: Boolean
  , showTooltip :: Boolean
  
  -- Color atoms
  , trackColor :: Maybe Color.RGB
  , rangeColor :: Maybe Color.RGB
  , thumbColor :: Maybe Color.RGB
  , thumbBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , tickColor :: Maybe Color.RGB
  , tooltipBackgroundColor :: Maybe Color.RGB
  , tooltipTextColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , trackHeight :: Maybe Device.Pixel
  , thumbSize :: Maybe Device.Pixel
  , thumbBorderWidth :: Maybe Device.Pixel
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Radius
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onChange :: Maybe (Number -> msg)
  , onRangeChange :: Maybe (RangeValue -> msg)
  , ariaLabel :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // slider prop
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property modifier function
-- |
-- | Slider configuration follows the builder pattern:
-- | ```purescript
-- | slider [ value 50.0, trackColor brand.primary, onChange HandleChange ]
-- | ```
-- |
-- | Each `SliderProp` modifies a single field of `SliderProps`.
type SliderProp msg = SliderProps msg -> SliderProps msg
