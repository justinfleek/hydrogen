-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // color // conversion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color space conversions for picker/wheel synchronization.
-- |
-- | **BIDIRECTIONAL SYNC REQUIREMENT:**
-- | When a user adjusts any color property (hue slider, RGB input, hex code),
-- | ALL representations must update synchronously. This module provides the
-- | mathematical conversions to maintain consistency across color spaces.
-- |
-- | **Use case: Playground color picker**
-- | 1. User adjusts Hue slider (0-359)
-- | 2. HSL updates → rgbToHsl converts → RGB updates
-- | 3. RGB updates → rgbToHex converts → Hex display updates
-- | 4. All views show the same color, zero drift
-- |
-- | **Color space conversions:**
-- | - HSL ↔ RGB (color wheel ↔ display values)
-- | - RGB ↔ CMYK (screen ↔ print)
-- | - RGB ↔ Hex (code ↔ human-readable)
-- | - RGB ↔ XYZ ↔ LAB ↔ LCH (perceptual spaces)
-- | - RGB ↔ OKLAB ↔ OKLCH (modern perceptual)
-- | - RGB ↔ HWB (CSS4 intuitive)
-- | - RGB ↔ YUV (video)
-- | - Kelvin → RGB (temperature ↔ display)
-- |
-- | **Billion-agent scale requirement:**
-- | All conversions use industry-standard algorithms. Two agents converting
-- | the same color will get identical results (within floating point precision).
-- |
-- | **Module structure:**
-- | - Core: HSL, CMYK, Hex, Kelvin (fundamental conversions)
-- | - XYZ: CIE XYZ, LAB, LCH (perceptual spaces)
-- | - Modern: OKLAB, OKLCH, HWB, YUV (CSS4 and video)
-- | - Serialization: Record conversions for JSON persistence

module Hydrogen.Schema.Color.Conversion
  ( -- * HSL ↔ RGB (re-exported from Core)
    module Core
  
  -- * XYZ/LAB/LCH conversions (re-exported from XYZ)
  , module XYZ
  
  -- * OKLAB/OKLCH/HWB/YUV conversions (re-exported from Modern)
  , module Modern
  
  -- * Record serialization (re-exported from Serialization)
  , module Serialization
  ) where

import Hydrogen.Schema.Color.Conversion.Core
  ( hslToRgb
  , rgbToHsl
  , rgbToCmyk
  , cmykToRgb
  , rgbToHex
  , hexToRgb
  , kelvinToRgb
  ) as Core

import Hydrogen.Schema.Color.Conversion.XYZ
  ( rgbToXyz
  , xyzToRgb
  , xyzToLab
  , labToXyz
  , rgbToLab
  , labToRgb
  , rgbToLch
  , lchToRgb
  ) as XYZ

import Hydrogen.Schema.Color.Conversion.Modern
  ( rgbToOklab
  , oklabToRgb
  , oklabToOklch
  , oklchToOklab
  , rgbToOklch
  , oklchToRgb
  , rgbToHwb
  , hwbToRgb
  , rgbToYuv
  , yuvToRgb
  ) as Modern

import Hydrogen.Schema.Color.Conversion.Serialization
  ( rgbToRecord
  , rgbFromRecord
  , hslToRecord
  , hslFromRecord
  , cmykToRecord
  , cmykFromRecord
  , labToRecord
  , labFromRecord
  , lchToRecord
  , lchFromRecord
  , xyzToRecord
  , xyzFromRecord
  ) as Serialization
