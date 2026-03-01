-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // composition // effect // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Correction Effects — Brightness, Contrast, Hue/Sat, Curves, etc.
-- |
-- | Color effects modify pixel values without spatial displacement.
-- | All parameters are bounded to prevent invalid color transformations.

module Hydrogen.Composition.Effect.Color
  ( BrightnessContrastSpec
  , HueSaturationSpec
  , LevelsSpec
  , CurvesSpec
  , CurvePoint
  , ColorBalanceSpec
  , TintSpec
  , VignetteSpec
  , ExposureSpec
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Color.RGB (RGB)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // brightness / contrast
-- ═══════════════════════════════════════════════════════════════════════════════

type BrightnessContrastSpec =
  { brightness :: Number  -- -100 to 100
  , contrast :: Number    -- -100 to 100
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // hue / saturation
-- ═══════════════════════════════════════════════════════════════════════════════

type HueSaturationSpec =
  { hue :: Number         -- -180 to 180
  , saturation :: Number  -- -100 to 100
  , lightness :: Number   -- -100 to 100
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // levels
-- ═══════════════════════════════════════════════════════════════════════════════

type LevelsSpec =
  { inputBlack :: Number  -- 0-255
  , inputWhite :: Number  -- 0-255
  , gamma :: Number       -- 0.1-10
  , outputBlack :: Number -- 0-255
  , outputWhite :: Number -- 0-255
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // curves
-- ═══════════════════════════════════════════════════════════════════════════════

type CurvePoint = { x :: Number, y :: Number }

type CurvesSpec =
  { master :: Array CurvePoint
  , red :: Array CurvePoint
  , green :: Array CurvePoint
  , blue :: Array CurvePoint
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // color balance
-- ═══════════════════════════════════════════════════════════════════════════════

type ColorBalanceSpec =
  { shadowsCyanRed :: Number      -- -100 to 100
  , shadowsMagentaGreen :: Number
  , shadowsYellowBlue :: Number
  , midtonesCyanRed :: Number
  , midtonesMagentaGreen :: Number
  , midtonesYellowBlue :: Number
  , highlightsCyanRed :: Number
  , highlightsMagentaGreen :: Number
  , highlightsYellowBlue :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // tint
-- ═══════════════════════════════════════════════════════════════════════════════

type TintSpec =
  { color :: RGB
  , amount :: Number      -- 0-100%
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // vignette
-- ═══════════════════════════════════════════════════════════════════════════════

type VignetteSpec =
  { amount :: Number      -- 0-100
  , midpoint :: Number    -- 0-100
  , roundness :: Number   -- -100 to 100
  , feather :: Number     -- 0-100
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // exposure
-- ═══════════════════════════════════════════════════════════════════════════════

type ExposureSpec =
  { exposure :: Number    -- -5 to 5 stops
  , offset :: Number      -- -1 to 1
  , gamma :: Number       -- 0.1 to 10
  }
