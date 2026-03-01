-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // composition // effect // stylize-effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stylize Effects — RGB Split, Scanlines, VHS, Glitch, Pixelate, Halftone.
-- |
-- | These effects create retro/digital aesthetic treatments.
-- | All parameters are bounded.

module Hydrogen.Composition.Effect.StylizeEffects
  ( RGBSplitSpec
  , ScanlinesSpec
  , VHSSpec
  , GlitchSpec
  , PixelateSpec
  , HalftoneSpec
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // rgb split
-- ═══════════════════════════════════════════════════════════════════════════════

type RGBSplitSpec =
  { redOffsetX :: Number
  , redOffsetY :: Number
  , blueOffsetX :: Number
  , blueOffsetY :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // scanlines
-- ═══════════════════════════════════════════════════════════════════════════════

type ScanlinesSpec =
  { spacing :: Number     -- 1-100
  , thickness :: Number   -- 0.1-10
  , opacity :: Number     -- 0-100%
  , angle :: Number       -- 0-360
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // vhs
-- ═══════════════════════════════════════════════════════════════════════════════

type VHSSpec =
  { distortion :: Number  -- 0-100
  , noise :: Number       -- 0-100
  , colorBleed :: Number  -- 0-100
  , scanlines :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // glitch
-- ═══════════════════════════════════════════════════════════════════════════════

type GlitchSpec =
  { intensity :: Number   -- 0-100
  , blockSize :: Number   -- 1-100
  , frequency :: Number   -- 0-100
  , rgbShift :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // pixelate
-- ═══════════════════════════════════════════════════════════════════════════════

type PixelateSpec =
  { blockWidth :: Number  -- 1-500
  , blockHeight :: Number -- 1-500
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // halftone
-- ═══════════════════════════════════════════════════════════════════════════════

type HalftoneSpec =
  { dotSize :: Number     -- 1-100
  , angle :: Number       -- 0-360
  , shape :: String       -- "circle", "square", "line"
  }
