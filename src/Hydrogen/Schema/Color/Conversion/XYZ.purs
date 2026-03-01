-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // color // xyz
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CIE XYZ and perceptual color space conversions
-- |
-- | **Device-independent color:**
-- | XYZ is the master reference space. All perceptual calculations go through it.
-- |
-- | **Conversion chain:**
-- | RGB → XYZ → LAB → LCH
-- |   ↓     ↓     ↓     ↓
-- | device  CIE   uniform  cylindrical
-- |
-- | **Billion-agent requirement:**
-- | All conversions use CIE standards with D65 white point.
-- | Deterministic across all systems.

module Hydrogen.Schema.Color.Conversion.XYZ
  ( -- * RGB ↔ XYZ
    rgbToXyz
  , xyzToRgb
  
  -- * XYZ ↔ LAB
  , xyzToLab
  , labToXyz
  
  -- * RGB ↔ LAB (convenience)
  , rgbToLab
  , labToRgb
  
  -- * RGB ↔ LCH (convenience)
  , rgbToLch
  , lchToRgb
  ) where

import Prelude
  ( negate
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>>>)
  )

import Data.Int as Int
import Data.Number (pow)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.XYZ as XYZ
import Hydrogen.Schema.Color.LAB as LAB
import Hydrogen.Schema.Color.LCH as LCH

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ xyz
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to XYZ (device-dependent to device-independent)
-- |
-- | Assumes sRGB color space with D65 white point.
-- | Steps:
-- | 1. Convert RGB 0-255 to 0-1
-- | 2. Apply inverse sRGB companding (gamma correction)
-- | 3. Apply sRGB → XYZ matrix transformation
-- |
-- | ```purescript
-- | rgbToXyz (RGB.rgb 255 255 255)  -- D65 white point
-- | rgbToXyz (RGB.rgb 0 0 0)        -- Black
-- | ```
rgbToXyz :: RGB.RGB -> XYZ.XYZ
rgbToXyz rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    -- Apply inverse sRGB companding (gamma correction)
    r' = if r <= 0.04045 then r / 12.92 else pow ((r + 0.055) / 1.055) 2.4
    g' = if g <= 0.04045 then g / 12.92 else pow ((g + 0.055) / 1.055) 2.4
    b' = if b <= 0.04045 then b / 12.92 else pow ((b + 0.055) / 1.055) 2.4
    
    -- Apply sRGB → XYZ matrix (D65)
    x = r' * 0.4124564 + g' * 0.3575761 + b' * 0.1804375
    y = r' * 0.2126729 + g' * 0.7151522 + b' * 0.0721750
    z = r' * 0.0193339 + g' * 0.1191920 + b' * 0.9503041
  in
    XYZ.xyz x y z

-- | Convert XYZ to RGB (device-independent to device-dependent)
-- |
-- | Assumes sRGB color space with D65 white point.
-- | Steps:
-- | 1. Apply XYZ → sRGB matrix transformation
-- | 2. Apply sRGB companding (gamma correction)
-- | 3. Convert 0-1 to RGB 0-255
-- |
-- | ```purescript
-- | xyzToRgb XYZ.d65White  -- RGB(255, 255, 255)
-- | ```
xyzToRgb :: XYZ.XYZ -> RGB.RGB
xyzToRgb xyzColor =
  let
    rec = XYZ.toRecord xyzColor
    x = rec.x
    y = rec.y
    z = rec.z
    
    -- Apply XYZ → sRGB matrix (D65)
    r' = x * 3.2404542 + y * (-1.5371385) + z * (-0.4985314)
    g' = x * (-0.9692660) + y * 1.8760108 + z * 0.0415560
    b' = x * 0.0556434 + y * (-0.2040259) + z * 1.0572252
    
    -- Apply sRGB companding (gamma correction)
    r = if r' <= 0.0031308 then r' * 12.92 else 1.055 * pow r' (1.0 / 2.4) - 0.055
    g = if g' <= 0.0031308 then g' * 12.92 else 1.055 * pow g' (1.0 / 2.4) - 0.055
    b = if b' <= 0.0031308 then b' * 12.92 else 1.055 * pow b' (1.0 / 2.4) - 0.055
    
    -- Clamp and convert to 0-255
    rInt = Int.round (clamp01 r * 255.0)
    gInt = Int.round (clamp01 g * 255.0)
    bInt = Int.round (clamp01 b * 255.0)
  in
    RGB.rgb rInt gInt bInt
  where
    clamp01 n
      | n < 0.0 = 0.0
      | n > 1.0 = 1.0
      | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // xyz ↔ lab
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert XYZ to LAB (device-independent to perceptual)
-- |
-- | Uses D65 white point and CIE standard formulas.
-- | This is where the perceptual uniformity is created.
-- |
-- | ```purescript
-- | xyzToLab XYZ.d65White  -- LAB(100, 0, 0) - white
-- | ```
xyzToLab :: XYZ.XYZ -> LAB.LAB
xyzToLab xyzColor =
  let
    rec = XYZ.toRecord xyzColor
    
    -- Normalize by D65 white point
    xr = rec.x / 0.95047
    yr = rec.y / 1.00000
    zr = rec.z / 1.08883
    
    -- Apply CIE LAB function
    fx = labF xr
    fy = labF yr
    fz = labF zr
    
    -- Calculate L*, a*, b*
    l = 116.0 * fy - 16.0
    a = 500.0 * (fx - fy)
    b = 200.0 * (fy - fz)
  in
    LAB.lab l a b
  where
    -- CIE LAB function (piecewise)
    labF t = if t > 0.008856
               then pow t (1.0 / 3.0)
               else (7.787 * t) + (16.0 / 116.0)

-- | Convert LAB to XYZ (perceptual to device-independent)
-- |
-- | Inverse of xyzToLab.
-- |
-- | ```purescript
-- | labToXyz (LAB.lab 100.0 0.0 0.0)  -- D65 white point
-- | ```
labToXyz :: LAB.LAB -> XYZ.XYZ
labToXyz labColor =
  let
    rec = LAB.toRecord labColor
    l = rec.l
    a = rec.a
    b = rec.b
    
    -- Calculate intermediate values
    fy = (l + 16.0) / 116.0
    fx = a / 500.0 + fy
    fz = fy - b / 200.0
    
    -- Apply inverse CIE LAB function
    xr = labFInv fx
    yr = labFInv fy
    zr = labFInv fz
    
    -- Denormalize by D65 white point
    x = xr * 0.95047
    y = yr * 1.00000
    z = zr * 1.08883
  in
    XYZ.xyz x y z
  where
    -- Inverse CIE LAB function (piecewise)
    labFInv t = 
      let t3 = t * t * t
      in if t3 > 0.008856
           then t3
           else (t - 16.0 / 116.0) / 7.787

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // rgb ↔ lab (convenience)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to LAB (convenience function)
-- |
-- | Goes through XYZ: RGB → XYZ → LAB
-- |
-- | ```purescript
-- | rgbToLab (RGB.rgb 255 0 0)  -- Red in perceptual space
-- | ```
rgbToLab :: RGB.RGB -> LAB.LAB
rgbToLab = rgbToXyz >>> xyzToLab

-- | Convert LAB to RGB (convenience function)
-- |
-- | Goes through XYZ: LAB → XYZ → RGB
-- |
-- | ```purescript
-- | labToRgb (LAB.lab 50.0 80.0 67.0)  -- Perceptual red to display RGB
-- | ```
labToRgb :: LAB.LAB -> RGB.RGB
labToRgb = labToXyz >>> xyzToRgb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // rgb ↔ lch (convenience)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to LCH (convenience function)
-- |
-- | Goes through XYZ and LAB: RGB → XYZ → LAB → LCH
-- |
-- | ```purescript
-- | rgbToLch (RGB.rgb 255 0 0)  -- Red in cylindrical perceptual space
-- | ```
rgbToLch :: RGB.RGB -> LCH.LCH
rgbToLch = rgbToLab >>> LCH.labToLch

-- | Convert LCH to RGB (convenience function)
-- |
-- | Goes through LAB and XYZ: LCH → LAB → XYZ → RGB
-- |
-- | ```purescript
-- | lchToRgb (LCH.lch 50.0 100.0 0.0)  -- Perceptual cylindrical to display RGB
-- | ```
lchToRgb :: LCH.LCH -> RGB.RGB
lchToRgb = LCH.lchToLab >>> labToRgb
