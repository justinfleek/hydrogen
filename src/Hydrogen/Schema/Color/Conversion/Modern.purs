-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // modern
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Modern color space conversions: OKLAB, OKLCH, HWB, YUV
-- |
-- | **OKLAB:** Björn Ottosson's perceptually uniform color space (2020).
-- | Superior to CIE LAB for hue preservation during lightness changes.
-- |
-- | **OKLCH:** Cylindrical form of OKLAB. CSS Color Level 4 standard.
-- | The recommended space for programmatic color manipulation.
-- |
-- | **HWB:** Hue-Whiteness-Blackness. CSS Color Level 4.
-- | Intuitive for humans: "add white to tint, add black to shade."
-- |
-- | **YUV:** Luma-chroma for video applications.
-- | ITU-R BT.601 standard definition coefficients.

module Hydrogen.Schema.Color.Conversion.Modern
  ( -- * RGB ↔ OKLAB
    rgbToOklab
  , oklabToRgb
  
  -- * OKLAB ↔ OKLCH
  , oklabToOklch
  , oklchToOklab
  
  -- * RGB ↔ OKLCH (convenience)
  , rgbToOklch
  , oklchToRgb
  
  -- * RGB ↔ HWB
  , rgbToHwb
  , hwbToRgb
  
  -- * RGB ↔ YUV
  , rgbToYuv
  , yuvToRgb
  ) where

import Prelude
  ( min
  , negate
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (<<<)
  )

import Data.Int as Int
import Data.Number (pow)
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.OKLAB as OKLAB
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.HWB as HWB
import Hydrogen.Schema.Color.YUV as YUV
import Hydrogen.Schema.Color.Conversion.Core (hslToRgb, rgbToHsl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // rgb ↔ oklab
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → OKLAB (modern perceptual uniform space)
-- | Uses linear RGB → LMS → OKLAB transformation
rgbToOklab :: RGB.RGB -> OKLAB.OKLAB
rgbToOklab rgb =
  let
    -- Convert to linear RGB (remove sRGB gamma)
    r = toLinear (Ch.toNumber (RGB.red rgb) / 255.0)
    g = toLinear (Ch.toNumber (RGB.green rgb) / 255.0)
    b = toLinear (Ch.toNumber (RGB.blue rgb) / 255.0)
    
    -- Linear RGB → LMS (cone response)
    l = 0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b
    m = 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b
    s = 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b
    
    -- LMS → OKLAB (cube root for perceptual uniformity)
    l' = cbrt l
    m' = cbrt m
    s' = cbrt s
    
    okL = 0.2104542553 * l' + 0.7936177850 * m' - 0.0040720468 * s'
    okA = 1.9779984951 * l' - 2.4285922050 * m' + 0.4505937099 * s'
    okB = 0.0259040371 * l' + 0.7827717662 * m' - 0.8086757660 * s'
  in
    OKLAB.oklab okL okA okB
  where
  -- sRGB to linear RGB
  toLinear c
    | c <= 0.04045 = c / 12.92
    | otherwise = pow ((c + 0.055) / 1.055) 2.4
  
  -- Cube root (∛x)
  cbrt x = pow x (1.0 / 3.0)

-- | OKLAB → RGB
oklabToRgb :: OKLAB.OKLAB -> RGB.RGB
oklabToRgb oklab =
  let
    okL = OKLAB.unwrapOkL (OKLAB.okL oklab)
    okA = OKLAB.unwrapOkA (OKLAB.okA oklab)
    okB = OKLAB.unwrapOkB (OKLAB.okB oklab)
    
    -- OKLAB → LMS (inverse)
    l' = okL + 0.3963377774 * okA + 0.2158037573 * okB
    m' = okL - 0.1055613458 * okA - 0.0638541728 * okB
    s' = okL - 0.0894841775 * okA - 1.2914855480 * okB
    
    -- LMS → Linear RGB (cube and inverse matrix)
    l = l' * l' * l'
    m = m' * m' * m'
    s = s' * s' * s'
    
    r = 4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s
    g = (-1.2684380046) * l + 2.6097574011 * m - 0.3413193965 * s
    b = (-0.0041960863) * l - 0.7034186147 * m + 1.7076147010 * s
    
    -- Linear RGB → sRGB (apply gamma)
    rGamma = toGamma r
    gGamma = toGamma g
    bGamma = toGamma b
  in
    RGB.rgb (Int.round (rGamma * 255.0)) (Int.round (gGamma * 255.0)) (Int.round (bGamma * 255.0))
  where
  -- Linear to sRGB gamma
  toGamma c
    | c <= 0.0031308 = 12.92 * c
    | otherwise = 1.055 * pow c (1.0 / 2.4) - 0.055

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // oklab ↔ oklch
-- ═════════════════════════════════════════════════════════════════════════════

-- | OKLAB → OKLCH (rectangular → cylindrical)
oklabToOklch :: OKLAB.OKLAB -> OKLCH.OKLCH
oklabToOklch oklab =
  let
    okL = OKLAB.unwrapOkL (OKLAB.okL oklab)
    okA = OKLAB.unwrapOkA (OKLAB.okA oklab)
    okB = OKLAB.unwrapOkB (OKLAB.okB oklab)
    
    -- Chroma (distance from neutral)
    c = sqrt (okA * okA + okB * okB)
    
    -- Hue (angle in degrees)
    h = atan2 okB okA * 180.0 / pi
    hNormalized = if h < 0.0 then h + 360.0 else h
  in
    OKLCH.oklch okL c (Int.round hNormalized)
  where
  atan2 y x = Math.atan2 y x
  sqrt x = Math.sqrt x
  pi = Math.pi

-- | OKLCH → OKLAB (cylindrical → rectangular)
oklchToOklab :: OKLCH.OKLCH -> OKLAB.OKLAB
oklchToOklab oklch =
  let
    okL = OKLAB.unwrapOkL (OKLCH.oklchL oklch)
    c = OKLCH.unwrapChroma (OKLCH.chroma oklch)
    h = Int.toNumber (Hue.unwrap (OKLCH.hue oklch))
    
    -- Convert hue to radians
    hRad = h * pi / 180.0
    
    -- Chroma and hue → a,b
    okA = c * cos hRad
    okB = c * sin hRad
  in
    OKLAB.oklab okL okA okB
  where
  cos x = Math.cos x
  sin x = Math.sin x
  pi = Math.pi

-- | RGB → OKLCH (convenience)
rgbToOklch :: RGB.RGB -> OKLCH.OKLCH
rgbToOklch = oklabToOklch <<< rgbToOklab

-- | OKLCH → RGB (convenience)
oklchToRgb :: OKLCH.OKLCH -> RGB.RGB
oklchToRgb = oklabToRgb <<< oklchToOklab

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ hwb
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → HWB (direct conversion)
-- |
-- | **Algorithm:**
-- | - Hue: same as HSL hue (derived from RGB)
-- | - Whiteness: min(R, G, B) / 255 as percentage
-- | - Blackness: 1 - max(R, G, B) / 255 as percentage
-- |
-- | This is a direct calculation, not via HSL intermediate.
rgbToHwb :: RGB.RGB -> HWB.HWB
rgbToHwb rgb =
  let
    r = Ch.unwrap (RGB.red rgb)
    g = Ch.unwrap (RGB.green rgb)
    b = Ch.unwrap (RGB.blue rgb)
    
    -- Get hue from HSL (hue calculation is independent)
    hsl = rgbToHsl rgb
    h = Hue.unwrap (HSL.hue hsl)
    
    -- Direct whiteness/blackness calculation
    minVal = min3 r g b
    maxVal = max3 r g b
    
    -- Whiteness = min / 255 * 100
    wNum = Int.toNumber minVal / 255.0 * 100.0
    -- Blackness = (1 - max / 255) * 100
    bNum = (1.0 - Int.toNumber maxVal / 255.0) * 100.0
  in
    HWB.hwb h (Int.round wNum) (Int.round bNum)
  where
  min3 a b c = if a <= b then (if a <= c then a else c) else (if b <= c then b else c)
  max3 a b c = if a >= b then (if a >= c then a else c) else (if b >= c then b else c)

-- | HWB → RGB (direct conversion)
-- |
-- | **Algorithm:**
-- | 1. If W + B >= 100: achromatic gray = W / (W + B)
-- | 2. Otherwise: calculate pure hue RGB, then:
-- |    RGB' = RGB * (1 - W/100 - B/100) + W/100
-- |
-- | This avoids HSL intermediate for better precision.
hwbToRgb :: HWB.HWB -> RGB.RGB
hwbToRgb hwb =
  let
    h = Hue.unwrap (HWB.hue hwb)
    wInt = HWB.unwrapWhiteness (HWB.getWhiteness hwb)
    bInt = HWB.unwrapBlackness (HWB.getBlackness hwb)
    w = Int.toNumber wInt / 100.0
    b = Int.toNumber bInt / 100.0
    
    -- Normalize if w + b > 1
    total = w + b
    w' = if total > 1.0 then w / total else w
    b' = if total > 1.0 then b / total else b
  in
    if w' + b' >= 1.0
      then
        -- Achromatic case: gray
        let gray = Int.round (w' / (w' + b') * 255.0)
        in RGB.rgb gray gray gray
      else
        -- Chromatic case: get pure hue, then apply whiteness/blackness
        let
          -- Get pure hue RGB (saturation=100, lightness=50)
          pureHueRgb = hslToRgb (HSL.hsl h 100 50)
          pr = Int.toNumber (Ch.unwrap (RGB.red pureHueRgb)) / 255.0
          pg = Int.toNumber (Ch.unwrap (RGB.green pureHueRgb)) / 255.0
          pb = Int.toNumber (Ch.unwrap (RGB.blue pureHueRgb)) / 255.0
          
          -- Apply formula: RGB' = RGB * (1 - W - B) + W
          factor = 1.0 - w' - b'
          r = Int.round ((pr * factor + w') * 255.0)
          g = Int.round ((pg * factor + w') * 255.0)
          bb = Int.round ((pb * factor + w') * 255.0)
        in
          RGB.rgb r g bb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ yuv
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → YUV (video color space)
rgbToYuv :: RGB.RGB -> YUV.YUV
rgbToYuv rgb =
  let
    r = Ch.toNumber (RGB.red rgb) / 255.0
    g = Ch.toNumber (RGB.green rgb) / 255.0
    b = Ch.toNumber (RGB.blue rgb) / 255.0
    
    -- ITU-R BT.601 coefficients (standard definition)
    y = 0.299 * r + 0.587 * g + 0.114 * b
    u = 0.492 * (b - y)
    v = 0.877 * (r - y)
  in
    YUV.yuv y u v

-- | YUV → RGB
yuvToRgb :: YUV.YUV -> RGB.RGB
yuvToRgb yuv =
  let
    y = YUV.unwrapLuma (YUV.getLuma yuv)
    u = YUV.unwrapU (YUV.getU yuv)
    v = YUV.unwrapV (YUV.getV yuv)
    
    -- ITU-R BT.601 inverse
    r = y + 1.140 * v
    g = y - 0.395 * u - 0.581 * v
    b = y + 2.032 * u
  in
    RGB.rgb (Int.round (r * 255.0)) (Int.round (g * 255.0)) (Int.round (b * 255.0))
