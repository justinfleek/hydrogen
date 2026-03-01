-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // slider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider — Schema-native range slider component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | All visual properties map directly to Schema pillar atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      | CSS Output              |
-- | |----------------------|------------|---------------------------|-------------------------|
-- | | trackColor           | Color      | Color.RGB                 | background-color (track)|
-- | | rangeColor           | Color      | Color.RGB                 | background-color (range)|
-- | | thumbColor           | Color      | Color.RGB                 | background-color (thumb)|
-- | | thumbBorderColor     | Color      | Color.RGB                 | border-color (thumb)    |
-- | | focusRingColor       | Color      | Color.RGB                 | box-shadow (focus)      |
-- | | trackHeight          | Dimension  | Device.Pixel              | height/width (track)    |
-- | | thumbSize            | Dimension  | Device.Pixel              | width, height (thumb)   |
-- | | thumbBorderWidth     | Dimension  | Device.Pixel              | border-width (thumb)    |
-- | | borderRadius         | Geometry   | Geometry.Radius           | border-radius           |
-- | | transitionDuration   | Temporal   | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Slider as Slider
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- |
-- | -- Basic slider with brand atoms
-- | Slider.slider
-- |   [ Slider.value 50.0
-- |   , Slider.onChange HandleSliderChange
-- |   , Slider.trackColor brand.surfaceColor
-- |   , Slider.rangeColor brand.primaryColor
-- |   , Slider.thumbColor brand.backgroundColor
-- |   , Slider.thumbBorderColor brand.primaryColor
-- |   ]
-- |
-- | -- Range slider with custom sizing
-- | Slider.rangeSlider
-- |   [ Slider.rangeValue { low: 20.0, high: 80.0 }
-- |   , Slider.onRangeChange HandleRangeChange
-- |   , Slider.trackHeight (Device.px 4.0)
-- |   , Slider.thumbSize (Device.px 20.0)
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Slider.Types` — Core type definitions
-- | - `Slider.Defaults` — Default Schema atom values
-- | - `Slider.Props` — Property builder functions
-- | - `Slider.Internal` — Helper utilities (not re-exported)
-- | - `Slider.Render` — Component rendering

module Hydrogen.Element.Compound.Slider
  ( -- * Types (from Types)
    module Hydrogen.Element.Compound.Slider.Types
  
  -- * Defaults (from Defaults)
  , module Hydrogen.Element.Compound.Slider.Defaults
  
  -- * Props (from Props)
  , module Hydrogen.Element.Compound.Slider.Props
  
  -- * Render (from Render)
  , module Hydrogen.Element.Compound.Slider.Render
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Types
import Hydrogen.Element.Compound.Slider.Types
  ( Orientation(Horizontal, Vertical)
  , RangeValue
  , SliderProps
  , SliderProp
  )

-- Defaults
import Hydrogen.Element.Compound.Slider.Defaults
  ( defaultProps
  )

-- Props
import Hydrogen.Element.Compound.Slider.Props
  ( value
  , rangeValue
  , minValue
  , maxValue
  , step
  , sliderDisabled
  , orientation
  , showTicks
  , showTooltip
  , trackColor
  , rangeColor
  , thumbColor
  , thumbBorderColor
  , focusRingColor
  , tickColor
  , tooltipBackgroundColor
  , tooltipTextColor
  , trackHeight
  , thumbSize
  , thumbBorderWidth
  , borderRadius
  , transitionDuration
  , onChange
  , onRangeChange
  , sliderAriaLabel
  )

-- Render
import Hydrogen.Element.Compound.Slider.Render
  ( slider
  , rangeSlider
  )
