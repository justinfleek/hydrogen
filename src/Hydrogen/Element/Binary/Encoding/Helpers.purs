-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // binary // encoding // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Helper Functions for Binary Encoding
-- |
-- | Utility functions for converting schema atoms to serializable values.

module Hydrogen.Element.Binary.Encoding.Helpers
  ( unwrapPixel
  , radiusToNumber
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (*)
  )

import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unwrap Pixel to Number
unwrapPixel :: Device.Pixel -> Number
unwrapPixel (Device.Pixel n) = n

-- | Convert Radius to Number (pixels)
radiusToNumber :: Radius.Radius -> Number
radiusToNumber = case _ of
  Radius.RadiusPx n -> n
  Radius.RadiusPercent n -> n  -- Runtime resolves to pixels
  Radius.RadiusRem n -> n * 16.0  -- Assume 16px base
  Radius.RadiusFull -> 9999.0
  Radius.RadiusNone -> 0.0
