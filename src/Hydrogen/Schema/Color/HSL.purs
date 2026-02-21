-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // hsl
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HSL color molecule - composition of Hue, Saturation, Lightness atoms.
-- |
-- | HSL (Hue, Saturation, Lightness) is a cylindrical color space that
-- | separates color identity (hue) from color properties (saturation, lightness).
-- | This makes it intuitive for color manipulation:
-- |
-- | - **Hue**: Position on the color wheel (0-359°)
-- | - **Saturation**: Color intensity/purity (0-100%)
-- | - **Lightness**: Light/dark level (0-100%)
-- |
-- | ## Color Wheel Reference
-- |
-- | ```
-- |   0°/360° = Red
-- |      60°  = Yellow
-- |     120°  = Green
-- |     180°  = Cyan
-- |     240°  = Blue
-- |     300°  = Magenta
-- | ```
-- |
-- | ## Lightness Behavior
-- |
-- | - At L=0%, any hue is black
-- | - At L=50%, colors are most vivid
-- | - At L=100%, any hue is white

module Hydrogen.Schema.Color.HSL
  ( -- * Types
    HSL
  
  -- * Constructors
  , hsl
  , fromRecord
  , fromComponents
  
  -- * Accessors
  , hue
  , saturation
  , lightness
  , toRecord
  
  -- * Operations
  , rotate
  , complement
  , lighten
  , darken
  , saturate
  , desaturate
  , grayscale
  
  -- * CSS Output
  , toCss
  
  -- * Interop
  , fromLegacy
  , toLegacy
  ) where

import Prelude

import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // hsl
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HSL color value - a molecule composed of three atoms.
-- |
-- | This is a lawful composition: if Hue, Saturation, and Lightness are each
-- | correct (valid bounds, proper semantics), then HSL is correct by construction.
newtype HSL = HSL
  { hue :: Hue.Hue
  , saturation :: Sat.Saturation
  , lightness :: Light.Lightness
  }

derive instance eqHSL :: Eq HSL
derive instance ordHSL :: Ord HSL

instance showHSL :: Show HSL where
  show = toCss

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an HSL color from raw values.
-- |
-- | Values are normalized by the underlying atoms:
-- | - Hue clamps to 0-359 (use `rotate` for wrapping behavior)
-- | - Saturation clamps to 0-100
-- | - Lightness clamps to 0-100
-- |
-- | ```purescript
-- | hsl 210 80 50  -- Ocean blue
-- | hsl 0 100 50   -- Pure red
-- | hsl 120 100 25 -- Dark green
-- | ```
hsl :: Int -> Int -> Int -> HSL
hsl h s l = HSL
  { hue: Hue.hue h
  , saturation: Sat.saturation s
  , lightness: Light.lightness l
  }

-- | Create from a record of raw values.
fromRecord :: { h :: Int, s :: Int, l :: Int } -> HSL
fromRecord { h, s, l } = hsl h s l

-- | Create from already-validated atoms.
-- |
-- | Use when you already have valid Hue, Saturation, Lightness values.
fromComponents :: Hue.Hue -> Sat.Saturation -> Light.Lightness -> HSL
fromComponents h s l = HSL { hue: h, saturation: s, lightness: l }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the hue component.
hue :: HSL -> Hue.Hue
hue (HSL c) = c.hue

-- | Extract the saturation component.
saturation :: HSL -> Sat.Saturation
saturation (HSL c) = c.saturation

-- | Extract the lightness component.
lightness :: HSL -> Light.Lightness
lightness (HSL c) = c.lightness

-- | Convert to a record of raw Int values.
-- |
-- | Useful for interop with other systems or JSON serialization.
toRecord :: HSL -> { h :: Int, s :: Int, l :: Int }
toRecord (HSL c) =
  { h: Hue.unwrap c.hue
  , s: Sat.unwrap c.saturation
  , l: Light.unwrap c.lightness
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees (wraps around the color wheel).
-- |
-- | ```purescript
-- | rotate 120 (hsl 0 100 50)   -- Red → Green
-- | rotate (-60) (hsl 60 100 50) -- Yellow → Red
-- | ```
rotate :: Int -> HSL -> HSL
rotate degrees (HSL c) = HSL
  { hue: Hue.rotate degrees c.hue
  , saturation: c.saturation
  , lightness: c.lightness
  }

-- | Get the complementary color (opposite on color wheel).
-- |
-- | ```purescript
-- | complement (hsl 0 100 50)   -- Red → Cyan (180°)
-- | complement (hsl 60 100 50)  -- Yellow → Blue (240°)
-- | ```
complement :: HSL -> HSL
complement = rotate 180

-- | Increase lightness by percentage points.
-- |
-- | ```purescript
-- | lighten 20 (hsl 0 100 50)  -- L: 50 → 70
-- | ```
lighten :: Int -> HSL -> HSL
lighten amount (HSL c) = HSL
  { hue: c.hue
  , saturation: c.saturation
  , lightness: Light.lighten amount c.lightness
  }

-- | Decrease lightness by percentage points.
-- |
-- | ```purescript
-- | darken 20 (hsl 0 100 50)  -- L: 50 → 30
-- | ```
darken :: Int -> HSL -> HSL
darken amount (HSL c) = HSL
  { hue: c.hue
  , saturation: c.saturation
  , lightness: Light.darken amount c.lightness
  }

-- | Increase saturation by percentage points.
-- |
-- | ```purescript
-- | saturate 20 (hsl 0 50 50)  -- S: 50 → 70
-- | ```
saturate :: Int -> HSL -> HSL
saturate amount (HSL c) = HSL
  { hue: c.hue
  , saturation: Sat.increase amount c.saturation
  , lightness: c.lightness
  }

-- | Decrease saturation by percentage points.
-- |
-- | ```purescript
-- | desaturate 20 (hsl 0 100 50)  -- S: 100 → 80
-- | ```
desaturate :: Int -> HSL -> HSL
desaturate amount (HSL c) = HSL
  { hue: c.hue
  , saturation: Sat.decrease amount c.saturation
  , lightness: c.lightness
  }

-- | Convert to grayscale (saturation = 0).
-- |
-- | Preserves hue information (can be re-saturated later).
grayscale :: HSL -> HSL
grayscale (HSL c) = HSL
  { hue: c.hue
  , saturation: Sat.saturation 0
  , lightness: c.lightness
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // css output
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS hsl() function string.
-- |
-- | ```purescript
-- | toCss (hsl 210 80 50)  -- "hsl(210, 80%, 50%)"
-- | ```
toCss :: HSL -> String
toCss (HSL c) =
  "hsl(" <> show (Hue.unwrap c.hue) 
  <> ", " <> show (Sat.unwrap c.saturation) <> "%"
  <> ", " <> show (Light.unwrap c.lightness) <> "%)"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // interop
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert from legacy Value.purs HSL record.
-- |
-- | For migration from `Hydrogen.Schema.Color.Value.HSL` to this module.
fromLegacy :: { h :: Int, s :: Int, l :: Int } -> HSL
fromLegacy = fromRecord

-- | Convert to legacy Value.purs HSL record.
-- |
-- | For interop with code still using `Hydrogen.Schema.Color.Value`.
toLegacy :: HSL -> { h :: Int, s :: Int, l :: Int }
toLegacy = toRecord
