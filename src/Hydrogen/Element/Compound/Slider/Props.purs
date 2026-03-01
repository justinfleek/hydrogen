-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // slider // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider Props — Builder functions for slider configuration.
-- |
-- | This module provides prop builder functions that modify `SliderProps`.
-- | Each function targets a specific property, enabling clean composition:
-- |
-- | ```purescript
-- | slider
-- |   [ value 50.0
-- |   , minValue 0.0
-- |   , maxValue 100.0
-- |   , trackColor brand.surfaceColor
-- |   , rangeColor brand.primaryColor
-- |   , onChange HandleSliderChange
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Slider.Props
  ( -- * State Props
    value
  , rangeValue
  , minValue
  , maxValue
  , step
  , sliderDisabled
  , orientation
  , showTicks
  , showTooltip
  
  -- * Color Atoms
  , trackColor
  , rangeColor
  , thumbColor
  , thumbBorderColor
  , focusRingColor
  , tickColor
  , tooltipBackgroundColor
  , tooltipTextColor
  
  -- * Dimension Atoms
  , trackHeight
  , thumbSize
  , thumbBorderWidth
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onChange
  , onRangeChange
  , sliderAriaLabel
  ) where

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.Slider.Types
  ( Orientation
  , RangeValue
  , SliderProp
  )
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set slider value
-- |
-- | The current position of a single-thumb slider.
-- | Should be between `minValue` and `maxValue`.
value :: forall msg. Number -> SliderProp msg
value v props = props { value = v }

-- | Set range slider value
-- |
-- | The low and high bounds for a dual-thumb range slider.
-- | Invariant: `low <= high`.
rangeValue :: forall msg. RangeValue -> SliderProp msg
rangeValue v props = props { rangeVal = v }

-- | Set minimum value
-- |
-- | Lower bound of the slider range. Default: 0.0
minValue :: forall msg. Number -> SliderProp msg
minValue v props = props { minVal = v }

-- | Set maximum value
-- |
-- | Upper bound of the slider range. Default: 100.0
maxValue :: forall msg. Number -> SliderProp msg
maxValue v props = props { maxVal = v }

-- | Set step increment
-- |
-- | The granularity of value changes. Default: 1.0
-- | Smaller steps = finer control, larger steps = coarser control.
step :: forall msg. Number -> SliderProp msg
step v props = props { step = v }

-- | Set disabled state
-- |
-- | When `true`, the slider is non-interactive and visually muted.
sliderDisabled :: forall msg. Boolean -> SliderProp msg
sliderDisabled d props = props { disabled = d }

-- | Set orientation
-- |
-- | `Horizontal` (default) or `Vertical`.
-- | Vertical sliders progress from bottom to top.
orientation :: forall msg. Orientation -> SliderProp msg
orientation o props = props { orientation = o }

-- | Show tick marks
-- |
-- | When `true`, renders tick marks at step intervals.
showTicks :: forall msg. Boolean -> SliderProp msg
showTicks s props = props { showTicks = s }

-- | Show tooltip on hover/focus
-- |
-- | When `true`, displays current value in a tooltip above the thumb.
showTooltip :: forall msg. Boolean -> SliderProp msg
showTooltip s props = props { showTooltip = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track background color (Color.RGB atom)
-- |
-- | The unfilled portion of the track.
trackColor :: forall msg. Color.RGB -> SliderProp msg
trackColor c props = props { trackColor = Just c }

-- | Set filled range color (Color.RGB atom)
-- |
-- | The filled portion indicating selected range.
rangeColor :: forall msg. Color.RGB -> SliderProp msg
rangeColor c props = props { rangeColor = Just c }

-- | Set thumb background color (Color.RGB atom)
-- |
-- | The draggable handle background.
thumbColor :: forall msg. Color.RGB -> SliderProp msg
thumbColor c props = props { thumbColor = Just c }

-- | Set thumb border color (Color.RGB atom)
-- |
-- | The draggable handle border.
thumbBorderColor :: forall msg. Color.RGB -> SliderProp msg
thumbBorderColor c props = props { thumbBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
-- |
-- | Visible when slider is focused via keyboard navigation.
focusRingColor :: forall msg. Color.RGB -> SliderProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set tick mark color (Color.RGB atom)
-- |
-- | Color of step indicators (when `showTicks` is enabled).
tickColor :: forall msg. Color.RGB -> SliderProp msg
tickColor c props = props { tickColor = Just c }

-- | Set tooltip background color (Color.RGB atom)
-- |
-- | Background of the value tooltip (when `showTooltip` is enabled).
tooltipBackgroundColor :: forall msg. Color.RGB -> SliderProp msg
tooltipBackgroundColor c props = props { tooltipBackgroundColor = Just c }

-- | Set tooltip text color (Color.RGB atom)
-- |
-- | Text color in the value tooltip.
tooltipTextColor :: forall msg. Color.RGB -> SliderProp msg
tooltipTextColor c props = props { tooltipTextColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track height/width (Device.Pixel atom)
-- |
-- | Thickness of the track. Height for horizontal, width for vertical.
trackHeight :: forall msg. Device.Pixel -> SliderProp msg
trackHeight h props = props { trackHeight = Just h }

-- | Set thumb size (Device.Pixel atom)
-- |
-- | Diameter of the circular thumb handle.
thumbSize :: forall msg. Device.Pixel -> SliderProp msg
thumbSize s props = props { thumbSize = Just s }

-- | Set thumb border width (Device.Pixel atom)
-- |
-- | Thickness of the thumb border.
thumbBorderWidth :: forall msg. Device.Pixel -> SliderProp msg
thumbBorderWidth w props = props { thumbBorderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Radius atom)
-- |
-- | Corner rounding for the track and range fill.
-- | Use `Geometry.full` for pill shape, `Geometry.px n` for specific radius.
borderRadius :: forall msg. Geometry.Radius -> SliderProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
-- |
-- | Animation duration for thumb position changes.
transitionDuration :: forall msg. Temporal.Milliseconds -> SliderProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set value change handler
-- |
-- | Called when the slider value changes (single-thumb slider).
-- | Receives the new value.
onChange :: forall msg. (Number -> msg) -> SliderProp msg
onChange handler props = props { onChange = Just handler }

-- | Set range change handler
-- |
-- | Called when the range changes (dual-thumb slider).
-- | Receives the new `RangeValue`.
onRangeChange :: forall msg. (RangeValue -> msg) -> SliderProp msg
onRangeChange handler props = props { onRangeChange = Just handler }

-- | Set ARIA label
-- |
-- | Accessibility label for screen readers.
sliderAriaLabel :: forall msg. String -> SliderProp msg
sliderAriaLabel l props = props { ariaLabel = l }
