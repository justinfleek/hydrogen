-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // typography // letterspacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LetterSpacing - horizontal space between characters (tracking).
-- |
-- | Expressed as thousandths of an em (per mille). This is the professional
-- | typographic convention used in design tools:
-- | - **0**: Normal spacing (font's default metrics)
-- | - **25-50**: Light tracking - uppercase headings
-- | - **100+**: Loose tracking - display text, all-caps
-- | - **-25 to -50**: Tight tracking - large display text
-- |
-- | Note: In brand guides, "tracking 25" means 0.025em = 25/1000em.
-- | This module uses the same convention.
-- |
-- | Letter spacing affects text density and readability:
-- | - Uppercase text NEEDS positive tracking to breathe
-- | - Body text usually looks best at 0 (font's designed spacing)
-- | - Large display sizes can use negative tracking

module Hydrogen.Schema.Typography.LetterSpacing
  ( LetterSpacing
  , letterSpacing
  , unsafeLetterSpacing
  , fromEm
  , unwrap
  , toEm
  , toLegacyCss
  , bounds
  -- Common values
  , none
  , tight
  , normal
  , loose
  , uppercase
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // letter spacing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Letter spacing in thousandths of an em (per mille)
-- |
-- | Professional typographic convention. A value of 25 means 0.025em
-- | of additional space between each character.
newtype LetterSpacing = LetterSpacing Int

derive instance eqLetterSpacing :: Eq LetterSpacing
derive instance ordLetterSpacing :: Ord LetterSpacing

instance showLetterSpacing :: Show LetterSpacing where
  show (LetterSpacing s) = show s <> "‰"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create letter spacing in per mille (thousandths of em)
-- |
-- | Range: -500 to 1000 (practical limits)
-- | - Negative values tighten spacing
-- | - Positive values loosen spacing
letterSpacing :: Int -> LetterSpacing
letterSpacing n = LetterSpacing (Bounded.clampInt (-500) 1000 n)

-- | Create letter spacing without clamping
-- |
-- | Use only when you know the value is valid.
unsafeLetterSpacing :: Int -> LetterSpacing
unsafeLetterSpacing = LetterSpacing

-- | Create letter spacing from em value
-- |
-- | Converts em to per mille: 0.025em → 25
fromEm :: Number -> LetterSpacing
fromEm em = letterSpacing (Int.round (em * 1000.0))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // common values
-- ═══════════════════════════════════════════════════════════════════════════════

-- | No additional spacing (0)
-- |
-- | Font's designed character spacing. Best for body text.
none :: LetterSpacing
none = LetterSpacing 0

-- | Tight spacing (-25)
-- |
-- | Subtle tightening for large display text where the optical spacing
-- | appears too loose.
tight :: LetterSpacing
tight = LetterSpacing (-25)

-- | Normal positive spacing (20)
-- |
-- | Slight expansion for improved readability in some contexts.
normal :: LetterSpacing
normal = LetterSpacing 20

-- | Loose spacing (50)
-- |
-- | Noticeable expansion for stylistic effect.
loose :: LetterSpacing
loose = LetterSpacing 50

-- | Uppercase tracking (25)
-- |
-- | Standard tracking for uppercase text. ALL-CAPS needs more space
-- | because uppercase letters have uniform height and no descenders.
uppercase :: LetterSpacing
uppercase = LetterSpacing 25

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value (per mille)
unwrap :: LetterSpacing -> Int
unwrap (LetterSpacing s) = s

-- | Convert to em value for calculations
-- |
-- | 25 per mille → 0.025em
toEm :: LetterSpacing -> Number
toEm (LetterSpacing s) = Int.toNumber s / 1000.0

-- | Convert to CSS letter-spacing value for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
-- |
-- | Outputs in em units for proper scaling with font size.
toLegacyCss :: LetterSpacing -> String
toLegacyCss ls = show (toEm ls) <> "em"

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds (-500) 1000 "letterSpacing" "Letter spacing in per mille"
