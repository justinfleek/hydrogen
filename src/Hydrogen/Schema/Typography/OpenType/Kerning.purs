-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // typography // opentype // kerning
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kerning - OpenType kerning and spacing features.
-- |
-- | Kerning adjusts the space between specific character pairs for
-- | improved visual consistency. Without kerning, combinations like
-- | "AV", "To", or "Yo" can appear to have too much space.
-- |
-- | ## Kerning (kern)
-- |
-- | Built-in pair kerning from the font's kern table.
-- | - On: Apply kerning (default for most fonts)
-- | - Off: Disable kerning (useful for monospace or artistic effect)
-- |
-- | ## Optical Sizing (opsz)
-- |
-- | Adjusts letterforms based on size. Small text gets more robust
-- | features (thicker strokes, more open counters). Display text gets
-- | refined details.
-- |
-- | ## Case-Sensitive Forms (case)
-- |
-- | Adjusts punctuation and symbols for all-caps text. Raises hyphens,
-- | parentheses, and other marks to align with capital letters.
-- |
-- | ## Capital Spacing (cpsp)
-- |
-- | Adds extra letter-spacing between capitals. Improves readability
-- | of all-caps text.
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `font-kerning`, `font-optical-sizing`, and `font-feature-settings`.

module Hydrogen.Schema.Typography.OpenType.Kerning
  ( -- * Types
    KerningMode(KerningAuto, KerningOn, KerningOff)
  , OpticalSizing(OpticalAuto, OpticalNone)
  , Kerning(Kerning)
  
  -- * Constructors
  , auto
  , normal
  , none
  , withOpticalSizing
  , withCaseSensitive
  , withCapitalSpacing
  , custom
  
  -- * Modifiers
  , enableKerning
  , disableKerning
  , enableOpticalSizing
  , disableOpticalSizing
  , enableCaseSensitive
  , enableCapitalSpacing
  
  -- * Predicates
  , isKerningEnabled
  , isKerningDisabled
  , isKerningAuto
  , hasOpticalSizing
  , hasCaseSensitive
  , hasCapitalSpacing
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // kerning mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kerning mode
-- |
-- | Controls whether built-in kerning pairs are applied.
data KerningMode
  = KerningAuto   -- ^ Browser decides (usually on)
  | KerningOn     -- ^ Explicitly enable kerning
  | KerningOff    -- ^ Explicitly disable kerning

derive instance eqKerningMode :: Eq KerningMode
derive instance ordKerningMode :: Ord KerningMode

instance showKerningMode :: Show KerningMode where
  show KerningAuto = "KerningAuto"
  show KerningOn = "KerningOn"
  show KerningOff = "KerningOff"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // optical sizing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Optical sizing mode
-- |
-- | Controls automatic adjustment of letterforms based on font size.
data OpticalSizing
  = OpticalAuto  -- ^ Enable optical sizing (default)
  | OpticalNone  -- ^ Disable optical sizing

derive instance eqOpticalSizing :: Eq OpticalSizing
derive instance ordOpticalSizing :: Ord OpticalSizing

instance showOpticalSizing :: Show OpticalSizing where
  show OpticalAuto = "OpticalAuto"
  show OpticalNone = "OpticalNone"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // kerning
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete kerning and spacing configuration
-- |
-- | Combines kerning, optical sizing, and case-sensitive features.
newtype Kerning = Kerning
  { kerning :: KerningMode
  , opticalSizing :: OpticalSizing
  , caseSensitive :: Boolean  -- ^ Case-sensitive forms (case)
  , capitalSpacing :: Boolean -- ^ Capital spacing (cpsp)
  }

derive instance eqKerning :: Eq Kerning

instance showKerning :: Show Kerning where
  show (Kerning k) =
    "Kerning { kerning: " <> show k.kerning <>
    ", opticalSizing: " <> show k.opticalSizing <>
    ", caseSensitive: " <> show k.caseSensitive <>
    ", capitalSpacing: " <> show k.capitalSpacing <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto kerning (browser defaults)
auto :: Kerning
auto = Kerning
  { kerning: KerningAuto
  , opticalSizing: OpticalAuto
  , caseSensitive: false
  , capitalSpacing: false
  }

-- | Normal kerning (explicitly enabled)
normal :: Kerning
normal = Kerning
  { kerning: KerningOn
  , opticalSizing: OpticalAuto
  , caseSensitive: false
  , capitalSpacing: false
  }

-- | No kerning (explicitly disabled)
-- |
-- | Use for: Monospace fonts, artistic effect, performance optimization.
none :: Kerning
none = Kerning
  { kerning: KerningOff
  , opticalSizing: OpticalNone
  , caseSensitive: false
  , capitalSpacing: false
  }

-- | Kerning with optical sizing enabled
withOpticalSizing :: Kerning
withOpticalSizing = Kerning
  { kerning: KerningOn
  , opticalSizing: OpticalAuto
  , caseSensitive: false
  , capitalSpacing: false
  }

-- | Kerning with case-sensitive forms
-- |
-- | Use for: All-caps text where punctuation should align with capitals.
withCaseSensitive :: Kerning
withCaseSensitive = Kerning
  { kerning: KerningOn
  , opticalSizing: OpticalAuto
  , caseSensitive: true
  , capitalSpacing: false
  }

-- | Kerning with capital spacing
-- |
-- | Use for: All-caps text that needs additional letter spacing.
withCapitalSpacing :: Kerning
withCapitalSpacing = Kerning
  { kerning: KerningOn
  , opticalSizing: OpticalAuto
  , caseSensitive: false
  , capitalSpacing: true
  }

-- | Custom kerning configuration
custom
  :: { kerning :: KerningMode
     , opticalSizing :: OpticalSizing
     , caseSensitive :: Boolean
     , capitalSpacing :: Boolean
     }
  -> Kerning
custom = Kerning

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable kerning
enableKerning :: Kerning -> Kerning
enableKerning (Kerning k) = Kerning k { kerning = KerningOn }

-- | Disable kerning
disableKerning :: Kerning -> Kerning
disableKerning (Kerning k) = Kerning k { kerning = KerningOff }

-- | Enable optical sizing
enableOpticalSizing :: Kerning -> Kerning
enableOpticalSizing (Kerning k) = Kerning k { opticalSizing = OpticalAuto }

-- | Disable optical sizing
disableOpticalSizing :: Kerning -> Kerning
disableOpticalSizing (Kerning k) = Kerning k { opticalSizing = OpticalNone }

-- | Enable case-sensitive forms
enableCaseSensitive :: Kerning -> Kerning
enableCaseSensitive (Kerning k) = Kerning k { caseSensitive = true }

-- | Enable capital spacing
enableCapitalSpacing :: Kerning -> Kerning
enableCapitalSpacing (Kerning k) = Kerning k { capitalSpacing = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is kerning explicitly enabled?
isKerningEnabled :: Kerning -> Boolean
isKerningEnabled (Kerning { kerning: KerningOn }) = true
isKerningEnabled _ = false

-- | Is kerning explicitly disabled?
isKerningDisabled :: Kerning -> Boolean
isKerningDisabled (Kerning { kerning: KerningOff }) = true
isKerningDisabled _ = false

-- | Is kerning in auto mode?
isKerningAuto :: Kerning -> Boolean
isKerningAuto (Kerning { kerning: KerningAuto }) = true
isKerningAuto _ = false

-- | Is optical sizing enabled?
hasOpticalSizing :: Kerning -> Boolean
hasOpticalSizing (Kerning { opticalSizing: OpticalAuto }) = true
hasOpticalSizing _ = false

-- | Are case-sensitive forms enabled?
hasCaseSensitive :: Kerning -> Boolean
hasCaseSensitive (Kerning { caseSensitive: true }) = true
hasCaseSensitive _ = false

-- | Is capital spacing enabled?
hasCapitalSpacing :: Kerning -> Boolean
hasCapitalSpacing (Kerning { capitalSpacing: true }) = true
hasCapitalSpacing _ = false
