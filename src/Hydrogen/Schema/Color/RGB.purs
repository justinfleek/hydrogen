-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // rgb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RGB color molecule — composition of three Channel atoms.
-- |
-- | RGB (Red, Green, Blue) is the additive color model used by displays.
-- | Each channel represents light intensity from 0 (none) to 255 (full).
-- |
-- | - **Red**: Long wavelength light (~700nm)
-- | - **Green**: Medium wavelength light (~546nm)
-- | - **Blue**: Short wavelength light (~436nm)
-- |
-- | ## Additive Color Mixing
-- |
-- | ```
-- | Red + Green       = Yellow
-- | Green + Blue      = Cyan
-- | Blue + Red        = Magenta
-- | Red + Green + Blue = White
-- | ```
-- |
-- | ## Device Dependency
-- |
-- | RGB values are device-dependent — the same values can appear differently
-- | on different displays. For color-accurate work, use a color-managed
-- | workflow with a defined color space (sRGB, Display P3, etc.).

module Hydrogen.Schema.Color.RGB
  ( -- * Types
    RGB
  , RGBA
  
  -- * RGB Constructors
  , rgb
  , fromRecord
  , fromChannels
  
  -- * RGB Accessors
  , red
  , green
  , blue
  , toRecord
  
  -- * RGB Operations
  , invert
  , blend
  , add
  , multiply
  , screen
  
  -- * RGB Output
  , toCss
  , toHex
  
  -- * RGBA
  , rgba
  , alpha
  , toRecordA
  , toCssA
  , toRGBA
  , fromRGBA
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.Channel as Ch

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // rgb
-- ═══════════════════════════════════════════════════════════════════════════════

-- | RGB color value — a molecule composed of three Channel atoms.
-- |
-- | This is a lawful composition: if each Channel is correct (0-255, clamped),
-- | then RGB is correct by construction. No invalid RGB values can exist.
newtype RGB = RGB
  { red :: Ch.Channel
  , green :: Ch.Channel
  , blue :: Ch.Channel
  }

derive instance eqRGB :: Eq RGB
derive instance ordRGB :: Ord RGB

instance showRGB :: Show RGB where
  show = toCss

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an RGB color from raw values.
-- |
-- | Values are clamped to 0-255 by the underlying Channel atoms.
-- |
-- | ```purescript
-- | rgb 255 128 0    -- Orange
-- | rgb 0 0 0        -- Black
-- | rgb 255 255 255  -- White
-- | ```
rgb :: Int -> Int -> Int -> RGB
rgb r g b = RGB
  { red: Ch.channel r
  , green: Ch.channel g
  , blue: Ch.channel b
  }

-- | Create from a record of raw values.
fromRecord :: { r :: Int, g :: Int, b :: Int } -> RGB
fromRecord { r, g, b } = rgb r g b

-- | Create from already-validated Channel atoms.
-- |
-- | Use when you already have valid Channel values.
fromChannels :: Ch.Channel -> Ch.Channel -> Ch.Channel -> RGB
fromChannels r g b = RGB { red: r, green: g, blue: b }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the red channel.
red :: RGB -> Ch.Channel
red (RGB c) = c.red

-- | Extract the green channel.
green :: RGB -> Ch.Channel
green (RGB c) = c.green

-- | Extract the blue channel.
blue :: RGB -> Ch.Channel
blue (RGB c) = c.blue

-- | Convert to a record of raw Int values.
-- |
-- | Useful for interop with other systems or JSON serialization.
toRecord :: RGB -> { r :: Int, g :: Int, b :: Int }
toRecord (RGB c) =
  { r: Ch.unwrap c.red
  , g: Ch.unwrap c.green
  , b: Ch.unwrap c.blue
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Invert the color (255 - each channel).
-- |
-- | ```purescript
-- | invert (rgb 255 0 0)  -- rgb 0 255 255 (cyan)
-- | invert (rgb 0 0 0)    -- rgb 255 255 255 (white)
-- | ```
invert :: RGB -> RGB
invert (RGB c) = RGB
  { red: Ch.invert c.red
  , green: Ch.invert c.green
  , blue: Ch.invert c.blue
  }

-- | Blend two colors with a weight (0.0 = all first, 1.0 = all second).
-- |
-- | ```purescript
-- | blend 0.5 (rgb 255 0 0) (rgb 0 0 255)  -- Purple-ish
-- | ```
blend :: Number -> RGB -> RGB -> RGB
blend weight (RGB c1) (RGB c2) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in RGB
    { red: Ch.blend w c1.red c2.red
    , green: Ch.blend w c1.green c2.green
    , blue: Ch.blend w c1.blue c2.blue
    }

-- | Add two colors (clamped at 255).
-- |
-- | Additive blending — used for light mixing effects.
add :: RGB -> RGB -> RGB
add (RGB c1) (RGB c2) = RGB
  { red: Ch.add c1.red c2.red
  , green: Ch.add c1.green c2.green
  , blue: Ch.add c1.blue c2.blue
  }

-- | Multiply blend mode.
-- |
-- | Result = (A × B) / 255. Always darkens.
multiply :: RGB -> RGB -> RGB
multiply (RGB c1) (RGB c2) = RGB
  { red: multiplyChannels c1.red c2.red
  , green: multiplyChannels c1.green c2.green
  , blue: multiplyChannels c1.blue c2.blue
  }
  where
  multiplyChannels a b =
    let 
      product = Int.toNumber (Ch.unwrap a) * Int.toNumber (Ch.unwrap b) / 255.0
    in Ch.channel (Int.round product)

-- | Screen blend mode.
-- |
-- | Result = 255 - ((255 - A) × (255 - B)) / 255. Always lightens.
screen :: RGB -> RGB -> RGB
screen (RGB c1) (RGB c2) = RGB
  { red: screenChannels c1.red c2.red
  , green: screenChannels c1.green c2.green
  , blue: screenChannels c1.blue c2.blue
  }
  where
  screenChannels a b =
    let
      a' = 255.0 - Int.toNumber (Ch.unwrap a)
      b' = 255.0 - Int.toNumber (Ch.unwrap b)
      result = 255.0 - (a' * b' / 255.0)
    in Ch.channel (Int.round result)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // css output
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS rgb() function string.
-- |
-- | ```purescript
-- | toCss (rgb 255 128 0)  -- "rgb(255, 128, 0)"
-- | ```
toCss :: RGB -> String
toCss (RGB c) =
  "rgb(" <> show (Ch.unwrap c.red)
  <> ", " <> show (Ch.unwrap c.green)
  <> ", " <> show (Ch.unwrap c.blue) <> ")"

-- | Convert to 6-character hex string (without #).
-- |
-- | ```purescript
-- | toHex (rgb 255 128 0)  -- "ff8000"
-- | ```
toHex :: RGB -> String
toHex (RGB c) =
  intToHex (Ch.unwrap c.red) 
  <> intToHex (Ch.unwrap c.green) 
  <> intToHex (Ch.unwrap c.blue)

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                  // internal
-- ─────────────────────────────────────────────────────────────────────────────

-- | Convert int (0-255) to 2-char hex string.
intToHex :: Int -> String
intToHex n =
  let
    hi = n / 16
    lo = n `mod` 16
  in intToHexChar hi <> intToHexChar lo

-- | Convert int (0-15) to hex char.
intToHexChar :: Int -> String
intToHexChar n = case n of
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
  10 -> "a"
  11 -> "b"
  12 -> "c"
  13 -> "d"
  14 -> "e"
  15 -> "f"
  _ -> "0"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // rgba
-- ═══════════════════════════════════════════════════════════════════════════════

-- | RGBA color value — RGB with an alpha channel.
-- |
-- | Alpha is also a Channel (0-255): 0 = fully transparent, 255 = fully opaque.
newtype RGBA = RGBA
  { red :: Ch.Channel
  , green :: Ch.Channel
  , blue :: Ch.Channel
  , alpha :: Ch.Channel
  }

derive instance eqRGBA :: Eq RGBA
derive instance ordRGBA :: Ord RGBA

instance showRGBA :: Show RGBA where
  show = toCssA

-- | Create an RGBA color from raw values.
rgba :: Int -> Int -> Int -> Int -> RGBA
rgba r g b a = RGBA
  { red: Ch.channel r
  , green: Ch.channel g
  , blue: Ch.channel b
  , alpha: Ch.channel a
  }

-- | Extract the alpha channel.
alpha :: RGBA -> Ch.Channel
alpha (RGBA c) = c.alpha

-- | Convert RGBA to a record of raw Int values.
toRecordA :: RGBA -> { r :: Int, g :: Int, b :: Int, a :: Int }
toRecordA (RGBA c) =
  { r: Ch.unwrap c.red
  , g: Ch.unwrap c.green
  , b: Ch.unwrap c.blue
  , a: Ch.unwrap c.alpha
  }

-- | Convert to CSS rgba() function string.
toCssA :: RGBA -> String
toCssA (RGBA c) =
  let a' = Int.toNumber (Ch.unwrap c.alpha) / 255.0
  in "rgba(" <> show (Ch.unwrap c.red)
  <> ", " <> show (Ch.unwrap c.green)
  <> ", " <> show (Ch.unwrap c.blue)
  <> ", " <> show a' <> ")"

-- | Convert RGB to RGBA with full opacity.
toRGBA :: RGB -> RGBA
toRGBA (RGB c) = RGBA
  { red: c.red
  , green: c.green
  , blue: c.blue
  , alpha: Ch.channel 255
  }

-- | Convert RGBA to RGB (drops alpha).
fromRGBA :: RGBA -> RGB
fromRGBA (RGBA c) = RGB
  { red: c.red
  , green: c.green
  , blue: c.blue
  }
