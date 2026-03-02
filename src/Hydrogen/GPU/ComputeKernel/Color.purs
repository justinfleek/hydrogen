-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // compute-kernel/color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Color — GPU Color Processing Kernel Types
-- |
-- | Color operations for image processing:
-- | - Grading: Exposure, contrast, saturation, color balance
-- | - Tone Mapping: HDR to LDR conversion
-- | - Color Space: Conversion between color spaces

module Hydrogen.GPU.ComputeKernel.Color
  ( -- * Color Types
    ColorKernel(ColorGrading, ColorToneMapping, ColorSpace)
  , ColorAdjust
  , ToneMappingAlgorithm(TonemapReinhard, TonemapACES, TonemapHable, TonemapFilmic)
  , ColorSpaceType(ColorSpaceSRGB, ColorSpaceLinear, ColorSpaceP3, ColorSpaceRec2020, ColorSpaceOKLab, ColorSpaceOKLCH)
  
  -- * Specific Kernels
  , ColorGradingKernel(ColorGradingKernel)
  , ToneMappingKernel(ToneMappingKernel)
  , ColorSpaceKernel(ColorSpaceKernel)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color processing kernel variants
-- |
-- | Each variant maps to a WebGPU compute shader with workgroup 16x16x1.
data ColorKernel
  = ColorGrading ColorGradingKernel
  | ColorToneMapping ToneMappingKernel
  | ColorSpace ColorSpaceKernel

derive instance eqColorKernel :: Eq ColorKernel

instance showColorKernel :: Show ColorKernel where
  show (ColorGrading k) = "(ColorGrading " <> show k <> ")"
  show (ColorToneMapping k) = "(ColorToneMapping " <> show k <> ")"
  show (ColorSpace k) = "(ColorSpace " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // grading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color grading kernel
-- |
-- | Comprehensive color adjustment with lift/gamma/gain per tonal range.
newtype ColorGradingKernel = ColorGradingKernel
  { exposure :: Number         -- Exposure adjustment (-2.0 to 2.0)
  , contrast :: Number         -- Contrast (-1.0 to 1.0)
  , saturation :: Number       -- Saturation (0.0 to 2.0)
  , temperature :: Number      -- Color temperature (-1.0 to 1.0)
  , tint :: Number             -- Green/magenta tint (-1.0 to 1.0)
  , shadows :: ColorAdjust     -- Shadow color adjustment
  , midtones :: ColorAdjust    -- Midtone color adjustment
  , highlights :: ColorAdjust  -- Highlight color adjustment
  , config :: KernelConfig
  }

derive instance eqColorGradingKernel :: Eq ColorGradingKernel

instance showColorGradingKernel :: Show ColorGradingKernel where
  show (ColorGradingKernel k) = "(ColorGradingKernel exposure:" <> show k.exposure <> ")"

-- | Color adjustment per tonal range
-- |
-- | Applied as additive RGB shifts to shadows, midtones, or highlights.
type ColorAdjust =
  { r :: Number                -- Red adjustment (-1.0 to 1.0)
  , g :: Number                -- Green adjustment
  , b :: Number                -- Blue adjustment
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tone mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tone mapping kernel (HDR to LDR)
-- |
-- | Compresses high dynamic range to displayable range.
newtype ToneMappingKernel = ToneMappingKernel
  { algorithm :: ToneMappingAlgorithm
  , whitePoint :: Number       -- Reference white level
  , config :: KernelConfig
  }

derive instance eqToneMappingKernel :: Eq ToneMappingKernel

instance showToneMappingKernel :: Show ToneMappingKernel where
  show (ToneMappingKernel k) = "(ToneMappingKernel " <> show k.algorithm <> ")"

-- | Tone mapping algorithms
-- |
-- | Industry-standard approaches for HDR rendering:
-- | - Reinhard: Simple, preserves colors well
-- | - ACES: Film-like, industry standard
-- | - Hable: Uncharted 2, good contrast
-- | - Filmic: Mimics film response
data ToneMappingAlgorithm
  = TonemapReinhard
  | TonemapACES
  | TonemapHable              -- Uncharted 2
  | TonemapFilmic

derive instance eqToneMappingAlgorithm :: Eq ToneMappingAlgorithm

instance showToneMappingAlgorithm :: Show ToneMappingAlgorithm where
  show TonemapReinhard = "TonemapReinhard"
  show TonemapACES = "TonemapACES"
  show TonemapHable = "TonemapHable"
  show TonemapFilmic = "TonemapFilmic"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color spaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color space conversion kernel
-- |
-- | Converts between color spaces for correct color handling.
newtype ColorSpaceKernel = ColorSpaceKernel
  { from :: ColorSpaceType
  , to :: ColorSpaceType
  , config :: KernelConfig
  }

derive instance eqColorSpaceKernel :: Eq ColorSpaceKernel

instance showColorSpaceKernel :: Show ColorSpaceKernel where
  show (ColorSpaceKernel k) = "(ColorSpaceKernel " <> show k.from <> " -> " <> show k.to <> ")"

-- | Color space types
-- |
-- | Supported color spaces:
-- | - sRGB: Standard web/display (gamma-encoded)
-- | - Linear: Linear light for compositing
-- | - P3: Wide gamut for modern displays
-- | - Rec2020: HDR broadcast standard
-- | - OKLab: Perceptually uniform
-- | - OKLCH: Perceptually uniform with polar coordinates
data ColorSpaceType
  = ColorSpaceSRGB
  | ColorSpaceLinear
  | ColorSpaceP3
  | ColorSpaceRec2020
  | ColorSpaceOKLab
  | ColorSpaceOKLCH

derive instance eqColorSpaceType :: Eq ColorSpaceType

instance showColorSpaceType :: Show ColorSpaceType where
  show ColorSpaceSRGB = "sRGB"
  show ColorSpaceLinear = "Linear"
  show ColorSpaceP3 = "P3"
  show ColorSpaceRec2020 = "Rec2020"
  show ColorSpaceOKLab = "OKLab"
  show ColorSpaceOKLCH = "OKLCH"
