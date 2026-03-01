-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // slider // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider Internal — Helper functions for slider rendering.
-- |
-- | This module provides internal utilities used by the Render module:
-- | - Percentage calculations
-- | - Default value resolution
-- | - String formatting

module Hydrogen.Element.Compound.Slider.Internal
  ( -- * Calculations
    toPercent
  , showPercent
  
  -- * Default Resolution
  , getColor
  , getPixel
  , getRadius
  , getDuration
  ) where

import Prelude
  ( show
  , (<>)
  , (-)
  , (/)
  , (*)
  )

import Data.Maybe (Maybe, maybe)

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate percentage position
-- |
-- | Converts a value within a range to a percentage (0-100).
-- | Used for positioning thumbs and range fills.
-- |
-- | ```purescript
-- | toPercent 0.0 100.0 50.0  -- Returns 50.0
-- | toPercent 0.0 100.0 25.0  -- Returns 25.0
-- | toPercent 10.0 20.0 15.0  -- Returns 50.0
-- | ```
toPercent :: Number -> Number -> Number -> Number
toPercent minV maxV val =
  ((val - minV) / (maxV - minV)) * 100.0

-- | Show a number as percentage string
-- |
-- | Appends "%" suffix for CSS positioning.
-- |
-- | ```purescript
-- | showPercent 50.0  -- Returns "50%"
-- | ```
showPercent :: Number -> String
showPercent n = show n <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // default resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get effective color with fallback
-- |
-- | Resolves `Maybe Color.RGB` to a concrete color, using the provided
-- | fallback when `Nothing`.
getColor :: Maybe Color.RGB -> Color.RGB -> Color.RGB
getColor maybeColor fallback = maybe fallback (\c -> c) maybeColor

-- | Get effective pixel with fallback
-- |
-- | Resolves `Maybe Device.Pixel` to a concrete dimension, using the
-- | provided fallback when `Nothing`.
getPixel :: Maybe Device.Pixel -> Device.Pixel -> Device.Pixel
getPixel maybePixel fallback = maybe fallback (\p -> p) maybePixel

-- | Get effective radius with fallback
-- |
-- | Resolves `Maybe Geometry.Radius` to a concrete radius, using the
-- | provided fallback when `Nothing`.
getRadius :: Maybe Geometry.Radius -> Geometry.Radius -> Geometry.Radius
getRadius maybeRadius fallback = maybe fallback (\r -> r) maybeRadius

-- | Get effective duration with fallback
-- |
-- | Resolves `Maybe Temporal.Milliseconds` to a concrete duration, using
-- | the provided fallback when `Nothing`.
getDuration :: Maybe Temporal.Milliseconds -> Temporal.Milliseconds -> Temporal.Milliseconds
getDuration maybeDuration fallback = maybe fallback (\d -> d) maybeDuration
