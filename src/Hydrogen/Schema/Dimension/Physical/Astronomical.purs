-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // dimension // physical // astronomical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Astronomical length units.
-- |
-- | For measuring at cosmic scales - planetary, stellar, and galactic.
-- | All units convert through Meter as the canonical representation.
-- |
-- | ## Scale Reference
-- | - AU: Solar system scale (sun-earth distance)
-- | - Light year: Stellar/interstellar distances
-- | - Parsec: Astronomical parallax measurement
-- | - Kiloparsec/Megaparsec: Galactic/intergalactic distances

module Hydrogen.Schema.Dimension.Physical.Astronomical
  ( -- * Types
    LightYear(..)
  , Parsec(..)
  , AstronomicalUnit(..)
  , Kiloparsec(..)
  , Megaparsec(..)
  , LightSecond(..)
  , LightMinute(..)
  
  -- * Constructors
  , lightYear
  , lightYears
  , parsec
  , parsecs
  , au
  , astronomicalUnit
  , kiloparsec
  , kiloparsecs
  , megaparsec
  , megaparsecs
  , lightSecond
  , lightSeconds
  , lightMinute
  , lightMinutes
  
  -- * Accessors
  , unwrapLightYear
  , unwrapParsec
  , unwrapAU
  , unwrapKiloparsec
  , unwrapMegaparsec
  , unwrapLightSecond
  , unwrapLightMinute
  
  -- * Conversions to Meter
  , lightYearsToMeters
  , parsecsToMeters
  , auToMeters
  , kiloparsecsToMeters
  , megaparsecsToMeters
  , lightSecondsToMeters
  , lightMinutesToMeters
  
  -- * Physical Constants
  , speedOfLight
  , metersPerLightYear
  , metersPerParsec
  , metersPerAU
  ) where

import Prelude

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Speed of light in m/s (exact by definition)
speedOfLight :: Number
speedOfLight = 299792458.0

-- | Meters per light year
metersPerLightYear :: Number
metersPerLightYear = 9.4607304725808e15

-- | Meters per parsec
metersPerParsec :: Number
metersPerParsec = 3.0856775814913673e16

-- | Meters per AU (exact by definition)
metersPerAU :: Number
metersPerAU = 1.495978707e11

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // light year
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Light year - distance light travels in one Julian year
newtype LightYear = LightYear Number

derive instance eqLightYear :: Eq LightYear
derive instance ordLightYear :: Ord LightYear

instance showLightYear :: Show LightYear where
  show (LightYear n) = show n <> " ly"

lightYear :: Number -> LightYear
lightYear = LightYear

lightYears :: Number -> LightYear
lightYears = LightYear

unwrapLightYear :: LightYear -> Number
unwrapLightYear (LightYear n) = n

lightYearsToMeters :: LightYear -> Number
lightYearsToMeters (LightYear n) = n * metersPerLightYear

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // parsec
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parsec - parallax of one arcsecond (~3.26 light years)
newtype Parsec = Parsec Number

derive instance eqParsec :: Eq Parsec
derive instance ordParsec :: Ord Parsec

instance showParsec :: Show Parsec where
  show (Parsec n) = show n <> " pc"

parsec :: Number -> Parsec
parsec = Parsec

parsecs :: Number -> Parsec
parsecs = Parsec

unwrapParsec :: Parsec -> Number
unwrapParsec (Parsec n) = n

parsecsToMeters :: Parsec -> Number
parsecsToMeters (Parsec n) = n * metersPerParsec

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // astronomical unit
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Astronomical Unit - mean sun-earth distance (exact by definition)
newtype AstronomicalUnit = AstronomicalUnit Number

derive instance eqAstronomicalUnit :: Eq AstronomicalUnit
derive instance ordAstronomicalUnit :: Ord AstronomicalUnit

instance showAstronomicalUnit :: Show AstronomicalUnit where
  show (AstronomicalUnit n) = show n <> " AU"

au :: Number -> AstronomicalUnit
au = AstronomicalUnit

astronomicalUnit :: Number -> AstronomicalUnit
astronomicalUnit = AstronomicalUnit

unwrapAU :: AstronomicalUnit -> Number
unwrapAU (AstronomicalUnit n) = n

auToMeters :: AstronomicalUnit -> Number
auToMeters (AstronomicalUnit n) = n * metersPerAU

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // kiloparsec
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Kiloparsec - 1000 parsecs (galactic scale)
newtype Kiloparsec = Kiloparsec Number

derive instance eqKiloparsec :: Eq Kiloparsec
derive instance ordKiloparsec :: Ord Kiloparsec

instance showKiloparsec :: Show Kiloparsec where
  show (Kiloparsec n) = show n <> " kpc"

kiloparsec :: Number -> Kiloparsec
kiloparsec = Kiloparsec

kiloparsecs :: Number -> Kiloparsec
kiloparsecs = Kiloparsec

unwrapKiloparsec :: Kiloparsec -> Number
unwrapKiloparsec (Kiloparsec n) = n

kiloparsecsToMeters :: Kiloparsec -> Number
kiloparsecsToMeters (Kiloparsec n) = n * metersPerParsec * 1000.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // megaparsec
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Megaparsec - 1 million parsecs (intergalactic scale)
newtype Megaparsec = Megaparsec Number

derive instance eqMegaparsec :: Eq Megaparsec
derive instance ordMegaparsec :: Ord Megaparsec

instance showMegaparsec :: Show Megaparsec where
  show (Megaparsec n) = show n <> " Mpc"

megaparsec :: Number -> Megaparsec
megaparsec = Megaparsec

megaparsecs :: Number -> Megaparsec
megaparsecs = Megaparsec

unwrapMegaparsec :: Megaparsec -> Number
unwrapMegaparsec (Megaparsec n) = n

megaparsecsToMeters :: Megaparsec -> Number
megaparsecsToMeters (Megaparsec n) = n * metersPerParsec * 1.0e6

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // light second
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Light second - distance light travels in one second
newtype LightSecond = LightSecond Number

derive instance eqLightSecond :: Eq LightSecond
derive instance ordLightSecond :: Ord LightSecond

instance showLightSecond :: Show LightSecond where
  show (LightSecond n) = show n <> " ls"

lightSecond :: Number -> LightSecond
lightSecond = LightSecond

lightSeconds :: Number -> LightSecond
lightSeconds = LightSecond

unwrapLightSecond :: LightSecond -> Number
unwrapLightSecond (LightSecond n) = n

lightSecondsToMeters :: LightSecond -> Number
lightSecondsToMeters (LightSecond n) = n * speedOfLight

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // light minute
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Light minute - distance light travels in one minute
newtype LightMinute = LightMinute Number

derive instance eqLightMinute :: Eq LightMinute
derive instance ordLightMinute :: Ord LightMinute

instance showLightMinute :: Show LightMinute where
  show (LightMinute n) = show n <> " lm"

lightMinute :: Number -> LightMinute
lightMinute = LightMinute

lightMinutes :: Number -> LightMinute
lightMinutes = LightMinute

unwrapLightMinute :: LightMinute -> Number
unwrapLightMinute (LightMinute n) = n

lightMinutesToMeters :: LightMinute -> Number
lightMinutesToMeters (LightMinute n) = n * speedOfLight * 60.0
