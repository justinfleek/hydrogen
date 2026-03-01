-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core color space conversions: HSL, CMYK, Hex
-- |
-- | **Bidirectional sync requirement:**
-- | These conversions enable color picker synchronization. When a user adjusts
-- | any color property, all representations update atomically.
-- |
-- | **Conversions provided:**
-- | - HSL ↔ RGB (color wheel ↔ display values)
-- | - RGB ↔ CMYK (screen ↔ print)
-- | - RGB ↔ Hex (code ↔ human-readable)
-- | - Kelvin → RGB (temperature ↔ display)

module Hydrogen.Schema.Color.Conversion.Core
  ( -- * HSL ↔ RGB
    hslToRgb
  , rgbToHsl
  
  -- * RGB ↔ CMYK
  , rgbToCmyk
  , cmykToRgb
  
  -- * RGB ↔ Hex
  , rgbToHex
  , hexToRgb
  
  -- * Kelvin → RGB
  , kelvinToRgb
  
  -- * Internal Helpers (exported for sibling modules)
  , mod'
  , toHex
  , hexDigit
  , fromHex
  , hexValue
  ) where

import Prelude
  ( max
  , min
  , mod
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Int as Int
import Data.Number (abs)
import Data.String (take, drop)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.CMYK as CMYK
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Cyan as Cyan
import Hydrogen.Schema.Color.Magenta as Magenta
import Hydrogen.Schema.Color.Yellow as Yellow
import Hydrogen.Schema.Color.Key as Key
import Hydrogen.Schema.Color.Kelvin as K

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // hsl ↔ rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert HSL to RGB
-- |
-- | Uses standard HSL → RGB algorithm:
-- | 1. Convert HSL percentages to 0-1 range
-- | 2. Calculate chroma and intermediate values
-- | 3. Map to RGB cube
-- |
-- | ```purescript
-- | hslToRgb (HSL.hsl 0 100 50)     -- Pure red: RGB(255, 0, 0)
-- | hslToRgb (HSL.hsl 120 100 50)   -- Pure green: RGB(0, 255, 0)
-- | hslToRgb (HSL.hsl 240 100 50)   -- Pure blue: RGB(0, 0, 255)
-- | ```
hslToRgb :: HSL.HSL -> RGB.RGB
hslToRgb hsl =
  let
    h = Int.toNumber (Hue.unwrap (HSL.hue hsl)) / 360.0
    s = Int.toNumber (Sat.unwrap (HSL.saturation hsl)) / 100.0
    l = Int.toNumber (Light.unwrap (HSL.lightness hsl)) / 100.0
    
    -- Calculate chroma
    c = (1.0 - abs (2.0 * l - 1.0)) * s
    x = c * (1.0 - abs (mod' (h * 6.0) 2.0 - 1.0))
    m = l - c / 2.0
    
    -- Map to RGB based on hue sector
    { r: r', g: g', b: b' } = 
      if h < (1.0 / 6.0) then { r: c, g: x, b: 0.0 }
      else if h < (2.0 / 6.0) then { r: x, g: c, b: 0.0 }
      else if h < (3.0 / 6.0) then { r: 0.0, g: c, b: x }
      else if h < (4.0 / 6.0) then { r: 0.0, g: x, b: c }
      else if h < (5.0 / 6.0) then { r: x, g: 0.0, b: c }
      else { r: c, g: 0.0, b: x }
    
    -- Convert to 0-255 range
    r = Int.round ((r' + m) * 255.0)
    g = Int.round ((g' + m) * 255.0)
    b = Int.round ((b' + m) * 255.0)
  in
    RGB.rgb r g b

-- | Convert RGB to HSL
-- |
-- | Uses standard RGB → HSL algorithm:
-- | 1. Normalize RGB to 0-1 range
-- | 2. Find min, max, delta
-- | 3. Calculate hue, saturation, lightness
-- |
-- | ```purescript
-- | rgbToHsl (RGB.rgb 255 0 0)   -- HSL(0°, 100%, 50%) - red
-- | rgbToHsl (RGB.rgb 128 128 128) -- HSL(0°, 0%, 50%) - gray
-- | ```
rgbToHsl :: RGB.RGB -> HSL.HSL
rgbToHsl rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    cmax = max r (max g b)
    cmin = min r (min g b)
    delta = cmax - cmin
    
    -- Calculate lightness
    l = (cmax + cmin) / 2.0
    
    -- Calculate saturation
    s = if delta == 0.0
          then 0.0
          else delta / (1.0 - abs (2.0 * l - 1.0))
    
    -- Calculate hue
    h' = if delta == 0.0
          then 0.0
          else if cmax == r
            then mod' ((g - b) / delta) 6.0
            else if cmax == g
              then ((b - r) / delta) + 2.0
              else ((r - g) / delta) + 4.0
    
    h = h' * 60.0
    
    -- Convert to integer percentages
    hInt = Int.round (if h < 0.0 then h + 360.0 else h)
    sInt = Int.round (s * 100.0)
    lInt = Int.round (l * 100.0)
  in
    HSL.hsl hInt sInt lInt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // rgb ↔ cmyk
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to CMYK (screen to print)
-- |
-- | Uses standard RGB → CMYK algorithm:
-- | 1. Normalize RGB to 0-1 range
-- | 2. Calculate K (black key) = 1 - max(R, G, B)
-- | 3. If K = 1 (pure black), C=M=Y=0
-- | 4. Otherwise: C = (1-R-K)/(1-K), same for M and Y
-- |
-- | ```purescript
-- | rgbToCmyk (RGB.rgb 255 0 0)    -- CMYK(0, 100, 100, 0) - red
-- | rgbToCmyk (RGB.rgb 0 0 0)      -- CMYK(0, 0, 0, 100) - black
-- | ```
rgbToCmyk :: RGB.RGB -> CMYK.CMYK
rgbToCmyk rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    k = 1.0 - max r (max g b)
    
    -- If pure black, CMY are 0
    { c, m, y } = 
      if k >= 1.0 
        then { c: 0.0, m: 0.0, y: 0.0 }
        else 
          { c: (1.0 - r - k) / (1.0 - k)
          , m: (1.0 - g - k) / (1.0 - k)
          , y: (1.0 - b - k) / (1.0 - k)
          }
    
    -- Convert to percentages
    cInt = Int.round (c * 100.0)
    mInt = Int.round (m * 100.0)
    yInt = Int.round (y * 100.0)
    kInt = Int.round (k * 100.0)
  in
    CMYK.cmyk cInt mInt yInt kInt

-- | Convert CMYK to RGB (print to screen)
-- |
-- | Uses standard CMYK → RGB algorithm:
-- | 1. R = 255 * (1 - C) * (1 - K)
-- | 2. G = 255 * (1 - M) * (1 - K)
-- | 3. B = 255 * (1 - Y) * (1 - K)
-- |
-- | ```purescript
-- | cmykToRgb (CMYK.cmyk 0 100 100 0)  -- RGB(255, 0, 0) - red
-- | cmykToRgb (CMYK.cmyk 0 0 0 100)    -- RGB(0, 0, 0) - black
-- | ```
cmykToRgb :: CMYK.CMYK -> RGB.RGB
cmykToRgb cmyk =
  let
    c = Int.toNumber (Cyan.unwrap (CMYK.cyan cmyk)) / 100.0
    m = Int.toNumber (Magenta.unwrap (CMYK.magenta cmyk)) / 100.0
    y = Int.toNumber (Yellow.unwrap (CMYK.yellow cmyk)) / 100.0
    k = Int.toNumber (Key.unwrap (CMYK.key cmyk)) / 100.0
    
    r = Int.round (255.0 * (1.0 - c) * (1.0 - k))
    g = Int.round (255.0 * (1.0 - m) * (1.0 - k))
    b = Int.round (255.0 * (1.0 - y) * (1.0 - k))
  in
    RGB.rgb r g b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ hex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to hex string
-- |
-- | Returns 6-character hex string (no # prefix).
-- | Agents can prepend # if needed for CSS/HTML contexts.
-- |
-- | ```purescript
-- | rgbToHex (RGB.rgb 255 0 0)     -- "FF0000"
-- | rgbToHex (RGB.rgb 128 128 128) -- "808080"
-- | ```
rgbToHex :: RGB.RGB -> String
rgbToHex rgb =
  let
    r = Ch.unwrap (RGB.red rgb)
    g = Ch.unwrap (RGB.green rgb)
    b = Ch.unwrap (RGB.blue rgb)
  in
    toHex r <> toHex g <> toHex b

-- | Convert hex string to RGB
-- |
-- | Accepts formats:
-- | - "FF0000" (6 chars)
-- | - "#FF0000" (7 chars with #)
-- | - "F00" (3 chars, expands to FF0000)
-- | - "#F00" (4 chars with #)
-- |
-- | Invalid hex returns black RGB(0, 0, 0).
-- |
-- | ```purescript
-- | hexToRgb "FF0000"   -- RGB(255, 0, 0)
-- | hexToRgb "#FF0000"  -- RGB(255, 0, 0)
-- | hexToRgb "F00"      -- RGB(255, 0, 0)
-- | hexToRgb "invalid"  -- RGB(0, 0, 0) - fallback
-- | ```
hexToRgb :: String -> RGB.RGB
hexToRgb hex =
  let
    -- Strip # if present
    cleaned = if take 1 hex == "#" then drop 1 hex else hex
    
    -- Expand 3-char format to 6-char
    expanded = case toCharArray cleaned of
      [ch1, ch2, ch3] -> fromCharArray [ch1, ch1, ch2, ch2, ch3, ch3]
      _ -> cleaned
    
    -- Parse hex components
    r = fromHex (take 2 expanded)
    g = fromHex (take 2 (drop 2 expanded))
    b = fromHex (take 2 (drop 4 expanded))
  in
    RGB.rgb r g b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // kelvin → rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Kelvin color temperature to RGB
-- |
-- | Re-export from Kelvin module for convenience.
-- | Uses Tanner Helland's algorithm for accurate temperature conversion.
-- |
-- | ```purescript
-- | kelvinToRgb (K.kelvin 2700)  -- Warm tungsten light
-- | kelvinToRgb (K.kelvin 6500)  -- Cool daylight
-- | ```
kelvinToRgb :: K.Kelvin -> RGB.RGB
kelvinToRgb = K.kelvinToRgb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Floating point modulo
mod' :: Number -> Number -> Number
mod' a b = a - b * Int.toNumber (Int.floor (a / b))

-- | Convert int to 2-character hex string
toHex :: Int -> String
toHex n =
  let
    hi = n / 16
    lo = n `mod` 16
  in
    hexDigit hi <> hexDigit lo

-- | Convert digit to hex character
hexDigit :: Int -> String
hexDigit n = case n of
  0 -> "0"
  1 -> "1"
  2 -> "2"
  3 -> "3"
  4 -> "4"
  5 -> "5"
  6 -> "6"
  7 -> "7"
  8 -> "8"
  9 -> "9"
  10 -> "A"
  11 -> "B"
  12 -> "C"
  13 -> "D"
  14 -> "E"
  15 -> "F"
  _ -> "0"

-- | Parse 2-character hex string to int
fromHex :: String -> Int
fromHex str = case toCharArray str of
  [hi, lo] -> hexValue hi * 16 + hexValue lo
  [c] -> hexValue c
  _ -> 0

-- | Get numeric value of hex character
hexValue :: Char -> Int
hexValue c = case c of
  '0' -> 0
  '1' -> 1
  '2' -> 2
  '3' -> 3
  '4' -> 4
  '5' -> 5
  '6' -> 6
  '7' -> 7
  '8' -> 8
  '9' -> 9
  'A' -> 10
  'B' -> 11
  'C' -> 12
  'D' -> 13
  'E' -> 14
  'F' -> 15
  'a' -> 10
  'b' -> 11
  'c' -> 12
  'd' -> 13
  'e' -> 14
  'f' -> 15
  _ -> 0
