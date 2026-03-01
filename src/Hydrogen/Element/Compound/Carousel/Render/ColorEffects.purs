-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // element // carousel // render // color-effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Color Effects — Color tinting based on slide position.
-- |
-- | ## Design Philosophy
-- |
-- | Color effects calculate tint values based on slide position. These can be
-- | applied as overlays or used for color grading effects. The computation is
-- | pure and deterministic.
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (SlidePosition)
-- | - Carousel.Effects (SlideEffects)
-- | - Schema.Color.RGB

module Hydrogen.Element.Compound.Carousel.Render.ColorEffects
  ( -- * Color Tinting
    slidePositionTint
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (>)
  , (<)
  )

import Data.Int (toNumber)

import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Compound.Carousel.Types 
  ( SlidePosition
      ( PositionActive
      , PositionPrev
      , PositionNext
      , PositionNearby
      , PositionOffscreen
      )
  )
import Hydrogen.Element.Compound.Carousel.Effects 
  ( SlideEffects
  , isEffectEnabled
  )
import Hydrogen.Element.Compound.Carousel.Render.Layout (absInt, toInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color tinting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate a color tint based on slide position
-- | Returns an RGB color representing the intensity at this position
-- | Can be used for overlay effects or color grading based on distance from active
-- |
-- | The tint intensity decreases with distance from the active slide:
-- | - Active: 100% intensity (white)
-- | - Prev/Next: 80% intensity
-- | - Nearby: Fades by 10% per position
-- | - Offscreen: 50% intensity
-- |
-- | When grayscale effect is enabled, the tint also accounts for
-- | desaturation, shifting toward gray.
slidePositionTint :: SlideEffects -> SlidePosition -> Color.RGB
slidePositionTint effects position =
  let
    -- Base intensity based on distance from active
    intensity = case position of
      PositionActive -> 1.0
      PositionPrev -> 0.8
      PositionNext -> 0.8
      PositionNearby n -> 
        let dist = toNumber (absInt n)
        in 1.0 - (dist * 0.1)
      PositionOffscreen -> 0.5
    
    -- Apply grayscale effect if enabled (reduces saturation based on distance)
    grayscaleAmount = if isEffectEnabled effects.grayscale.enabled
      then effects.grayscale.inactive
      else 0.0
    
    -- Compute channel values (intensity-based white)
    -- When grayscale is applied, slides fade toward gray
    baseChannel = toInt (intensity * 255.0)
    grayOffset = toInt (grayscaleAmount * (1.0 - intensity) * 50.0)
    channelValue = baseChannel - grayOffset
    clampedChannel = if channelValue < 0 then 0 
                     else if channelValue > 255 then 255 
                     else channelValue
  in
    Color.rgb clampedChannel clampedChannel clampedChannel
