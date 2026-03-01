-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // device // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Constructors, operations, accessors, and common densities for device units.
-- |
-- | This module provides:
-- | - Smart constructors for all device unit types
-- | - Arithmetic operations on pixel values
-- | - Unwrap/accessor functions
-- | - PPI/PPCM conversion
-- | - Common display density constants

module Hydrogen.Schema.Dimension.Device.Operations
  ( -- * Constructors
    px
  , devicePx
  , cssPx
  , dp
  , sp
  , ppi
  , ppcm
  , dpr
  
  -- * Operations
  , addPx
  , subtractPx
  , scalePx
  , negatePx
  , absPx
  
  -- * Common Display Densities
  , ppiStandard
  , ppiRetina
  , ppiRetinaHD
  , ppi4K
  , ppiPrint300
  , ppiPrint600
  
  -- * Accessors
  , unwrapPixel
  , unwrapDevicePixel
  , unwrapCSSPixel
  , unwrapDp
  , unwrapSp
  , unwrapPpi
  , unwrapPpcm
  , unwrapDpr
  
  -- * PPI/PPCM Conversion
  , ppiToPpcm
  , ppcmToPpi
  ) where

import Prelude
  ( negate
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  , DevicePixel(DevicePixel)
  , CSSPixel(CSSPixel)
  , DensityIndependentPixel(DensityIndependentPixel)
  , ScaledPixel(ScaledPixel)
  , PixelsPerInch(PixelsPerInch)
  , PixelsPerCentimeter(PixelsPerCentimeter)
  , DevicePixelRatio(DevicePixelRatio)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Pixel value
px :: Number -> Pixel
px = Pixel

-- | Create a DevicePixel value
devicePx :: Number -> DevicePixel
devicePx = DevicePixel

-- | Create a CSSPixel value
cssPx :: Number -> CSSPixel
cssPx = CSSPixel

-- | Create a DensityIndependentPixel value
dp :: Number -> DensityIndependentPixel
dp = DensityIndependentPixel

-- | Create a ScaledPixel value
sp :: Number -> ScaledPixel
sp = ScaledPixel

-- | Create a PixelsPerInch value
ppi :: Number -> PixelsPerInch
ppi = PixelsPerInch

-- | Create a PixelsPerCentimeter value
ppcm :: Number -> PixelsPerCentimeter
ppcm = PixelsPerCentimeter

-- | Create a DevicePixelRatio value
dpr :: Number -> DevicePixelRatio
dpr = DevicePixelRatio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two Pixel values
addPx :: Pixel -> Pixel -> Pixel
addPx (Pixel a) (Pixel b) = Pixel (a + b)

-- | Subtract two Pixel values
subtractPx :: Pixel -> Pixel -> Pixel
subtractPx (Pixel a) (Pixel b) = Pixel (a - b)

-- | Scale a Pixel value by a dimensionless factor
scalePx :: Number -> Pixel -> Pixel
scalePx factor (Pixel n) = Pixel (n * factor)

-- | Negate a Pixel value
negatePx :: Pixel -> Pixel
negatePx (Pixel n) = Pixel (negate n)

-- | Absolute value of a Pixel
absPx :: Pixel -> Pixel
absPx (Pixel n) = Pixel (Math.abs n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // common display densities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard desktop monitor (96 PPI)
-- | This is the CSS reference density
ppiStandard :: PixelsPerInch
ppiStandard = PixelsPerInch 96.0

-- | Apple Retina display (~220-230 PPI)
-- | iPhone 4 was 326 PPI, MacBook Pro is ~220 PPI
ppiRetina :: PixelsPerInch
ppiRetina = PixelsPerInch 220.0

-- | Apple Retina HD display (~326-458 PPI)
-- | iPhone Plus/Max models
ppiRetinaHD :: PixelsPerInch
ppiRetinaHD = PixelsPerInch 326.0

-- | 4K UHD at typical monitor sizes (~163-185 PPI)
ppi4K :: PixelsPerInch
ppi4K = PixelsPerInch 163.0

-- | Print quality at 300 DPI
ppiPrint300 :: PixelsPerInch
ppiPrint300 = PixelsPerInch 300.0

-- | High quality print at 600 DPI
ppiPrint600 :: PixelsPerInch
ppiPrint600 = PixelsPerInch 600.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number from a Pixel
unwrapPixel :: Pixel -> Number
unwrapPixel (Pixel n) = n

-- | Extract the raw Number from a DevicePixel
unwrapDevicePixel :: DevicePixel -> Number
unwrapDevicePixel (DevicePixel n) = n

-- | Extract the raw Number from a CSSPixel
unwrapCSSPixel :: CSSPixel -> Number
unwrapCSSPixel (CSSPixel n) = n

-- | Extract the raw Number from a DensityIndependentPixel
unwrapDp :: DensityIndependentPixel -> Number
unwrapDp (DensityIndependentPixel n) = n

-- | Extract the raw Number from a ScaledPixel
unwrapSp :: ScaledPixel -> Number
unwrapSp (ScaledPixel n) = n

-- | Extract the raw Number from a PixelsPerInch
unwrapPpi :: PixelsPerInch -> Number
unwrapPpi (PixelsPerInch n) = n

-- | Extract the raw Number from a PixelsPerCentimeter
unwrapPpcm :: PixelsPerCentimeter -> Number
unwrapPpcm (PixelsPerCentimeter n) = n

-- | Extract the raw Number from a DevicePixelRatio
unwrapDpr :: DevicePixelRatio -> Number
unwrapDpr (DevicePixelRatio n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // ppi/ppcm conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Conversion factor: 1 inch = 2.54 centimeters
inchesPerCm :: Number
inchesPerCm = 2.54

-- | Convert PPI to PPCM.
-- |
-- | PPCM = PPI / 2.54
-- |
-- | ```purescript
-- | ppiToPpcm (ppi 96.0)  -- ~37.8 PPCM
-- | ```
ppiToPpcm :: PixelsPerInch -> PixelsPerCentimeter
ppiToPpcm (PixelsPerInch n) = PixelsPerCentimeter (n / inchesPerCm)

-- | Convert PPCM to PPI.
-- |
-- | PPI = PPCM × 2.54
-- |
-- | ```purescript
-- | ppcmToPpi (ppcm 37.8)  -- ~96 PPI
-- | ```
ppcmToPpi :: PixelsPerCentimeter -> PixelsPerInch
ppcmToPpi (PixelsPerCentimeter n) = PixelsPerInch (n * inchesPerCm)
