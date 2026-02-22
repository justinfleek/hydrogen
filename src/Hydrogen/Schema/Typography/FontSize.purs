-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // typography // fontsize
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontSize - typographic scale in pixels.
-- |
-- | A positive number representing font size in CSS pixels. Font sizes are
-- | resolution-independent - a 16px font renders at appropriate physical
-- | size on any device via DPR scaling.
-- |
-- | Common base sizes:
-- | - **16px**: Browser default, most readable for body text
-- | - **18px**: Enhanced readability, common for premium sites
-- | - **14px**: Compact interfaces, data-heavy applications
-- |
-- | Font sizes must be positive. Zero and negative values are invalid.

module Hydrogen.Schema.Typography.FontSize
  ( FontSize
  , fontSize
  , unsafeFontSize
  , unwrap
  , scale
  , toCss
  , bounds
  -- Common sizes
  , browserDefault
  , compact
  , readable
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // font size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Font size in CSS pixels (positive Number)
-- |
-- | Represents the em-square height of a font. Actual glyph heights vary
-- | within this bounding box based on the font's design.
newtype FontSize = FontSize Number

derive instance eqFontSize :: Eq FontSize
derive instance ordFontSize :: Ord FontSize

instance showFontSize :: Show FontSize where
  show (FontSize s) = show s <> "px"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a font size, clamping to positive values
-- |
-- | Minimum size is 1px to prevent invisible text.
-- | Maximum size is 1000px (practical limit for display).
fontSize :: Number -> FontSize
fontSize n = FontSize (Bounded.clampNumber 1.0 1000.0 n)

-- | Create a font size without clamping
-- |
-- | Use only when you know the value is valid.
unsafeFontSize :: Number -> FontSize
unsafeFontSize = FontSize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // common sizes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Browser default size (16px)
-- |
-- | The standard base size for web content. Used as the reference for
-- | rem calculations.
browserDefault :: FontSize
browserDefault = FontSize 16.0

-- | Compact size (14px)
-- |
-- | For data-dense interfaces where space efficiency matters more than
-- | optimal readability.
compact :: FontSize
compact = FontSize 14.0

-- | Enhanced readable size (18px)
-- |
-- | For premium reading experiences and accessibility-focused designs.
readable :: FontSize
readable = FontSize 18.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scale font size by a factor
-- |
-- | Used for type scale calculations. The factor must be positive.
scale :: Number -> FontSize -> FontSize
scale factor (FontSize s) = fontSize (s * factor)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FontSize -> Number
unwrap (FontSize s) = s

-- | Convert to CSS font-size value
toCss :: FontSize -> String
toCss (FontSize s) = show s <> "px"

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 1000.0 "fontSize" "Font size in CSS pixels"
