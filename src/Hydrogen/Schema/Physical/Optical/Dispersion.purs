-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // physical // optical // dispersion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Optical dispersion — wavelength-dependent refraction.
-- |
-- | ## What is Dispersion?
-- |
-- | Dispersion occurs because a material's refractive index varies with light
-- | wavelength. Blue light bends more than red light. This creates:
-- | - Rainbows (sunlight through water droplets)
-- | - "Fire" in gemstones (spectral colors flashing)
-- | - Chromatic aberration in lenses
-- |
-- | ## Abbe Number (Vd)
-- |
-- | The Abbe number quantifies dispersion. Higher Abbe = lower dispersion:
-- |
-- | Vd = (nd - 1) / (nF - nC)
-- |
-- | Where:
-- | - nd = refractive index at 587.6 nm (helium d-line, yellow)
-- | - nF = refractive index at 486.1 nm (hydrogen F-line, blue)
-- | - nC = refractive index at 656.3 nm (hydrogen C-line, red)
-- |
-- | ## Value Ranges
-- |
-- | - **High dispersion** (20-30): Dense flint glass, gemstones with "fire"
-- | - **Medium dispersion** (30-50): Crown glass, common materials
-- | - **Low dispersion** (50-95): Fluorite, special optical glasses
-- |
-- | ## Gemstone "Fire"
-- |
-- | Dispersion creates the "fire" (spectral flashes) in gemstones:
-- | - Diamond: 0.044 (exceptional fire)
-- | - Moissanite: 0.104 (more fire than diamond!)
-- | - Cubic zirconia: 0.060 (good fire)
-- | - Ruby/sapphire: 0.018 (subtle fire)
-- |
-- | Fire value = (nB - nR) where nB is blue IOR and nR is red IOR.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, dispersion determines:
-- | - Gemstone appearance (fire, brilliance, scintillation)
-- | - Lens design (achromatic doublets need high/low Abbe pairs)
-- | - Rainbow rendering (atmospheric effects)
-- | - Prism effects (spectral separation)
-- |
-- | ## Data Sources
-- |
-- | Schott optical glass catalog, GIA gemological data, CRC Handbook.

module Hydrogen.Schema.Physical.Optical.Dispersion
  ( -- * Abbe Number Type
    AbbeNumber
  , abbeNumber
  , abbeNumberUnsafe
  , unwrapAbbe
  , abbeBounds
  
  -- * Fire Value Type
  , FireValue
  , fireValue
  , fireValueUnsafe
  , unwrapFire
  , fireBounds
  
  -- * Optical Glass — Low Dispersion
  , fluorite
  , fusedSilica
  , bk7
  , nbk7
  , pk52a
  , fk51a
  
  -- * Optical Glass — Medium Dispersion
  , crownGlass
  , borosilicate
  , nsk2
  
  -- * Optical Glass — High Dispersion
  , flintGlass
  , denseFlint
  , sf11
  , sf57
  , lasf9
  
  -- * Gemstones — By Fire Value
  , diamondFire
  , moissaniteFire
  , cubicZirconiaFire
  , sphaleriteFire
  , demantoidFire
  , sphene_Fire
  , zirconFire
  , sapphireFire
  , rubyFire
  , emeraldFire
  , topazFire
  , peridotFire
  , quartzFire
  , opalFire
  
  -- * Gemstones — Abbe Number
  , diamondAbbe
  , rubyAbbe
  , sapphireAbbe
  , emeraldAbbe
  , quartzAbbe
  
  -- * Liquids
  , waterAbbe
  , ethanolAbbe
  , benzeneAbbe
  , carbonDisulfideAbbe
  
  -- * Operations
  , dispersionCategory
  , isLowDispersion
  , fireCategory
  , hasExceptionalFire
  , lerpAbbe
  , lerpFire
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, abs, pow) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // abbe number type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Abbe number (Vd) — reciprocal dispersion [15.0, 100.0].
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 15.0: Below most dense flint glasses (~17)
-- | - Upper bound 100.0: Above calcium fluoride (~95)
-- |
-- | Higher Abbe number = lower dispersion (less rainbow effect).
newtype AbbeNumber = AbbeNumber Number

derive instance eqAbbeNumber :: Eq AbbeNumber
derive instance ordAbbeNumber :: Ord AbbeNumber

instance showAbbeNumber :: Show AbbeNumber where
  show (AbbeNumber n) = "Abbe(" <> show n <> ")"

-- | Create AbbeNumber with validation.
abbeNumber :: Number -> Maybe AbbeNumber
abbeNumber n
  | n >= 15.0 && n <= 100.0 = Just (AbbeNumber n)
  | otherwise = Nothing

-- | Create AbbeNumber with clamping.
abbeNumberUnsafe :: Number -> AbbeNumber
abbeNumberUnsafe n = AbbeNumber (Bounded.clampNumber 15.0 100.0 n)

-- | Extract the underlying Number.
unwrapAbbe :: AbbeNumber -> Number
unwrapAbbe (AbbeNumber n) = n

-- | Bounds documentation for Abbe number.
abbeBounds :: Bounded.NumberBounds
abbeBounds = Bounded.numberBounds 15.0 100.0 Bounded.Clamps
  "abbe"
  "Abbe number Vd (15=high dispersion, 100=low dispersion)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // fire value type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fire value — spectral dispersion for gemstones [0.0, 0.2].
-- |
-- | Fire = nB - nR (blue IOR minus red IOR)
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 0.0: No dispersion (impossible, but allows for future)
-- | - Upper bound 0.2: Above synthetic rutile (~0.190)
-- |
-- | Higher fire = more rainbow flashes in gemstones.
newtype FireValue = FireValue Number

derive instance eqFireValue :: Eq FireValue
derive instance ordFireValue :: Ord FireValue

instance showFireValue :: Show FireValue where
  show (FireValue n) = "Fire(" <> show n <> ")"

-- | Create FireValue with validation.
fireValue :: Number -> Maybe FireValue
fireValue n
  | n >= 0.0 && n <= 0.2 = Just (FireValue n)
  | otherwise = Nothing

-- | Create FireValue with clamping.
fireValueUnsafe :: Number -> FireValue
fireValueUnsafe n = FireValue (Bounded.clampNumber 0.0 0.2 n)

-- | Extract the underlying Number.
unwrapFire :: FireValue -> Number
unwrapFire (FireValue n) = n

-- | Bounds documentation for fire value.
fireBounds :: Bounded.NumberBounds
fireBounds = Bounded.numberBounds 0.0 0.2 Bounded.Clamps
  "fire"
  "Gemstone fire value (0.044=diamond, 0.104=moissanite)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // optical glass — low dispersion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calcium fluorite (CaF₂) — lowest dispersion common optical material
fluorite :: AbbeNumber
fluorite = AbbeNumber 95.0

-- | Fused silica (SiO₂) — very low dispersion
fusedSilica :: AbbeNumber
fusedSilica = AbbeNumber 67.8

-- | BK7 — standard optical crown glass (Schott)
bk7 :: AbbeNumber
bk7 = AbbeNumber 64.2

-- | N-BK7 — newer formulation of BK7
nbk7 :: AbbeNumber
nbk7 = AbbeNumber 64.2

-- | PK52A — extra-low dispersion phosphate crown
pk52a :: AbbeNumber
pk52a = AbbeNumber 81.6

-- | FK51A — fluorophosphate crown, excellent for apochromats
fk51a :: AbbeNumber
fk51a = AbbeNumber 84.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                           // optical glass — medium dispersion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Crown glass — generic optical crown
crownGlass :: AbbeNumber
crownGlass = AbbeNumber 59.0

-- | Borosilicate glass (Pyrex family)
borosilicate :: AbbeNumber
borosilicate = AbbeNumber 51.0

-- | N-SK2 — dense crown (Schott)
nsk2 :: AbbeNumber
nsk2 = AbbeNumber 60.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // optical glass — high dispersion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flint glass — lead-containing high dispersion
flintGlass :: AbbeNumber
flintGlass = AbbeNumber 36.0

-- | Dense flint — very high dispersion
denseFlint :: AbbeNumber
denseFlint = AbbeNumber 25.0

-- | SF11 — dense flint (Schott)
sf11 :: AbbeNumber
sf11 = AbbeNumber 25.8

-- | SF57 — extra-dense flint (Schott)
sf57 :: AbbeNumber
sf57 = AbbeNumber 18.0

-- | LaSF9 — lanthanum dense flint
lasf9 :: AbbeNumber
lasf9 = AbbeNumber 32.2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // gemstones — by fire value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diamond — exceptional fire, the benchmark
diamondFire :: FireValue
diamondFire = FireValue 0.044

-- | Moissanite — more fire than diamond!
moissaniteFire :: FireValue
moissaniteFire = FireValue 0.104

-- | Cubic zirconia — good fire, diamond simulant
cubicZirconiaFire :: FireValue
cubicZirconiaFire = FireValue 0.060

-- | Sphalerite — extremely high fire but soft
sphaleriteFire :: FireValue
sphaleriteFire = FireValue 0.156

-- | Demantoid garnet — exceptional fire for a colored stone
demantoidFire :: FireValue
demantoidFire = FireValue 0.057

-- | Sphene (titanite) — very high fire
sphene_Fire :: FireValue
sphene_Fire = FireValue 0.051

-- | Zircon — high fire, not to be confused with CZ
zirconFire :: FireValue
zirconFire = FireValue 0.039

-- | Sapphire — moderate fire
sapphireFire :: FireValue
sapphireFire = FireValue 0.018

-- | Ruby — moderate fire (same as sapphire, both corundum)
rubyFire :: FireValue
rubyFire = FireValue 0.018

-- | Emerald — low fire
emeraldFire :: FireValue
emeraldFire = FireValue 0.014

-- | Topaz — moderate fire
topazFire :: FireValue
topazFire = FireValue 0.014

-- | Peridot — moderate fire
peridotFire :: FireValue
peridotFire = FireValue 0.020

-- | Quartz — low fire
quartzFire :: FireValue
quartzFire = FireValue 0.013

-- | Opal — fire comes from diffraction, not dispersion (placeholder)
opalFire :: FireValue
opalFire = FireValue 0.012

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // gemstones — abbe number
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diamond — relatively high dispersion for a gemstone
diamondAbbe :: AbbeNumber
diamondAbbe = AbbeNumber 33.3

-- | Ruby/Sapphire (corundum)
rubyAbbe :: AbbeNumber
rubyAbbe = AbbeNumber 72.2

sapphireAbbe :: AbbeNumber
sapphireAbbe = AbbeNumber 72.2

-- | Emerald (beryl)
emeraldAbbe :: AbbeNumber
emeraldAbbe = AbbeNumber 53.0

-- | Quartz
quartzAbbe :: AbbeNumber
quartzAbbe = AbbeNumber 58.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // liquids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Water
waterAbbe :: AbbeNumber
waterAbbe = AbbeNumber 55.8

-- | Ethanol
ethanolAbbe :: AbbeNumber
ethanolAbbe = AbbeNumber 60.6

-- | Benzene — relatively high dispersion
benzeneAbbe :: AbbeNumber
benzeneAbbe = AbbeNumber 30.1

-- | Carbon disulfide — very high dispersion liquid
carbonDisulfideAbbe :: AbbeNumber
carbonDisulfideAbbe = AbbeNumber 18.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Categorize dispersion level based on Abbe number.
-- |
-- | - High dispersion: Abbe < 30 (flint glass, diamonds)
-- | - Medium dispersion: Abbe 30-55 (crown glass, water)
-- | - Low dispersion: Abbe > 55 (fluorite, fused silica)
dispersionCategory :: AbbeNumber -> String
dispersionCategory (AbbeNumber n)
  | n <= 30.0 = "high"
  | n <= 55.0 = "medium"
  | otherwise = "low"

-- | Check if material has low dispersion (good for lenses).
isLowDispersion :: AbbeNumber -> Boolean
isLowDispersion (AbbeNumber n) = n > 55.0

-- | Categorize gemstone fire.
-- |
-- | - Exceptional: fire > 0.05 (diamond, moissanite, CZ)
-- | - High: fire 0.03-0.05 (zircon, demantoid)
-- | - Moderate: fire 0.015-0.03 (sapphire, peridot)
-- | - Low: fire < 0.015 (quartz, emerald)
fireCategory :: FireValue -> String
fireCategory (FireValue n)
  | n > 0.05 = "exceptional"
  | n > 0.03 = "high"
  | n > 0.015 = "moderate"
  | otherwise = "low"

-- | Check if gemstone has exceptional fire.
hasExceptionalFire :: FireValue -> Boolean
hasExceptionalFire (FireValue n) = n > 0.05

-- | Linear interpolation between two Abbe numbers.
lerpAbbe :: Number -> AbbeNumber -> AbbeNumber -> AbbeNumber
lerpAbbe t (AbbeNumber a) (AbbeNumber b) =
  abbeNumberUnsafe (a + t * (b - a))

-- | Linear interpolation between two fire values.
lerpFire :: Number -> FireValue -> FireValue -> FireValue
lerpFire t (FireValue a) (FireValue b) =
  fireValueUnsafe (a + t * (b - a))
