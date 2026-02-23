-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // typography // lineheight
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LineHeight - vertical rhythm and text leading.
-- |
-- | A unitless ratio relative to font size:
-- | - **1.0**: Lines touch (no leading) - display text only
-- | - **1.2-1.3**: Tight - headings, short bursts
-- | - **1.4-1.5**: Normal - balanced readability
-- | - **1.6-1.8**: Relaxed - body text, long-form reading
-- | - **2.0+**: Loose - special effects, dramatic spacing
-- |
-- | Line height = font-size × ratio. For 16px text at 1.5 ratio = 24px lines.
-- |
-- | Professional typographers call the space between lines "leading" (rhymes
-- | with "bedding"), from the lead strips inserted between lines of metal type.

module Hydrogen.Schema.Typography.LineHeight
  ( LineHeight
  , lineHeight
  , unsafeLineHeight
  , unwrap
  , toPixels
  , toLegacyCss
  , bounds
  -- Common ratios
  , solid
  , tight
  , normal
  , relaxed
  , loose
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Typography.FontSize (FontSize)
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // line height
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Line height as unitless ratio (positive Number)
-- |
-- | This is a multiplier of the font size. Using unitless values ensures
-- | line height scales proportionally when font size changes.
newtype LineHeight = LineHeight Number

derive instance eqLineHeight :: Eq LineHeight
derive instance ordLineHeight :: Ord LineHeight

instance showLineHeight :: Show LineHeight where
  show (LineHeight h) = show h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a line height, clamping to valid range
-- |
-- | Minimum is 0.5 (prevents text overlap in most cases).
-- | Maximum is 5.0 (practical limit for display).
lineHeight :: Number -> LineHeight
lineHeight n = LineHeight (Bounded.clampNumber 0.5 5.0 n)

-- | Create a line height without clamping
-- |
-- | Use only when you know the value is valid.
unsafeLineHeight :: Number -> LineHeight
unsafeLineHeight = LineHeight

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // common ratios
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Solid line height (1.0)
-- |
-- | No leading - lines touch. Use only for single-line display text where
-- | vertical space is at a premium.
solid :: LineHeight
solid = LineHeight 1.0

-- | Tight line height (1.25)
-- |
-- | Minimal leading for headings and short text bursts. Creates visual
-- | density and urgency.
tight :: LineHeight
tight = LineHeight 1.25

-- | Normal line height (1.5)
-- |
-- | Balanced readability for most content. Good default for body text
-- | in interfaces.
normal :: LineHeight
normal = LineHeight 1.5

-- | Relaxed line height (1.75)
-- |
-- | Enhanced readability for long-form content. Reduces eye strain during
-- | extended reading sessions.
relaxed :: LineHeight
relaxed = LineHeight 1.75

-- | Loose line height (2.0)
-- |
-- | Dramatic vertical spacing for special effects or when content needs
-- | room to breathe.
loose :: LineHeight
loose = LineHeight 2.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: LineHeight -> Number
unwrap (LineHeight h) = h

-- | Calculate actual pixel height for a given font size
toPixels :: FontSize -> LineHeight -> Number
toPixels fs (LineHeight ratio) = FontSize.unwrap fs * ratio

-- | Convert to CSS line-height value (unitless) for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
toLegacyCss :: LineHeight -> String
toLegacyCss (LineHeight h) = show h

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.5 5.0 "lineHeight" "Line height as unitless ratio"
