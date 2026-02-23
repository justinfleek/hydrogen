-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // physical // atomic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Atomic and quantum scale length units.
-- |
-- | For measuring at the scale of atoms, nuclei, and quantum phenomena.
-- | All units convert through Meter as the canonical representation.
-- |
-- | ## Scale Reference
-- | - Angstrom: atomic radii, light wavelengths
-- | - Bohr radius: hydrogen atom orbital
-- | - Picometer: atomic bonds, X-rays
-- | - Femtometer/Fermi: atomic nuclei
-- | - Planck length: quantum minimum (theoretical)

module Hydrogen.Schema.Dimension.Physical.Atomic
  ( -- * Types
    Picometer(Picometer)
  , Femtometer(Femtometer)
  , Angstrom(Angstrom)
  , BohrRadius(BohrRadius)
  , Fermi(Fermi)
  , PlanckLength(PlanckLength)
  
  -- * Constructors
  , picometer
  , picometers
  , femtometer
  , femtometers
  , angstrom
  , angstroms
  , bohrRadius
  , fermi
  , fermis
  , planckLength
  
  -- * Accessors
  , unwrapPicometer
  , unwrapFemtometer
  , unwrapAngstrom
  , unwrapBohrRadius
  , unwrapFermi
  , unwrapPlanckLength
  
  -- * Conversions to Meter
  , picometersToMeters
  , femtometersToMeters
  , angstromsToMeters
  , bohrRadiusToMeters
  , fermiToMeters
  , planckLengthToMeters
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (<>)
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // picometer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Picometer - 10^-12 meter (atomic scale)
newtype Picometer = Picometer Number

derive instance eqPicometer :: Eq Picometer
derive instance ordPicometer :: Ord Picometer

instance showPicometer :: Show Picometer where
  show (Picometer n) = show n <> " pm"

picometer :: Number -> Picometer
picometer = Picometer

picometers :: Number -> Picometer
picometers = Picometer

unwrapPicometer :: Picometer -> Number
unwrapPicometer (Picometer n) = n

picometersToMeters :: Picometer -> Number
picometersToMeters (Picometer n) = n * 1.0e-12

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // femtometer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Femtometer - 10^-15 meter (nuclear scale)
newtype Femtometer = Femtometer Number

derive instance eqFemtometer :: Eq Femtometer
derive instance ordFemtometer :: Ord Femtometer

instance showFemtometer :: Show Femtometer where
  show (Femtometer n) = show n <> " fm"

femtometer :: Number -> Femtometer
femtometer = Femtometer

femtometers :: Number -> Femtometer
femtometers = Femtometer

unwrapFemtometer :: Femtometer -> Number
unwrapFemtometer (Femtometer n) = n

femtometersToMeters :: Femtometer -> Number
femtometersToMeters (Femtometer n) = n * 1.0e-15

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // angstrom
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Angstrom - 10^-10 meter (atomic radii, wavelengths)
newtype Angstrom = Angstrom Number

derive instance eqAngstrom :: Eq Angstrom
derive instance ordAngstrom :: Ord Angstrom

instance showAngstrom :: Show Angstrom where
  show (Angstrom n) = show n <> " Å"

angstrom :: Number -> Angstrom
angstrom = Angstrom

angstroms :: Number -> Angstrom
angstroms = Angstrom

unwrapAngstrom :: Angstrom -> Number
unwrapAngstrom (Angstrom n) = n

angstromsToMeters :: Angstrom -> Number
angstromsToMeters (Angstrom n) = n * 1.0e-10

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // bohr radius
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bohr radius - 5.29177210903×10^-11 m (hydrogen atom ground state)
newtype BohrRadius = BohrRadius Number

derive instance eqBohrRadius :: Eq BohrRadius
derive instance ordBohrRadius :: Ord BohrRadius

instance showBohrRadius :: Show BohrRadius where
  show (BohrRadius n) = show n <> " a₀"

bohrRadius :: Number -> BohrRadius
bohrRadius = BohrRadius

unwrapBohrRadius :: BohrRadius -> Number
unwrapBohrRadius (BohrRadius n) = n

bohrRadiusToMeters :: BohrRadius -> Number
bohrRadiusToMeters (BohrRadius n) = n * 5.29177210903e-11

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // fermi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fermi - 10^-15 meter (nuclear physics, same as femtometer)
newtype Fermi = Fermi Number

derive instance eqFermi :: Eq Fermi
derive instance ordFermi :: Ord Fermi

instance showFermi :: Show Fermi where
  show (Fermi n) = show n <> " fm"

fermi :: Number -> Fermi
fermi = Fermi

fermis :: Number -> Fermi
fermis = Fermi

unwrapFermi :: Fermi -> Number
unwrapFermi (Fermi n) = n

fermiToMeters :: Fermi -> Number
fermiToMeters (Fermi n) = n * 1.0e-15

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // planck length
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Planck length - 1.616255×10^-35 m (quantum minimum, theoretical)
newtype PlanckLength = PlanckLength Number

derive instance eqPlanckLength :: Eq PlanckLength
derive instance ordPlanckLength :: Ord PlanckLength

instance showPlanckLength :: Show PlanckLength where
  show (PlanckLength n) = show n <> " ℓP"

planckLength :: Number -> PlanckLength
planckLength = PlanckLength

unwrapPlanckLength :: PlanckLength -> Number
unwrapPlanckLength (PlanckLength n) = n

planckLengthToMeters :: PlanckLength -> Number
planckLengthToMeters (PlanckLength n) = n * 1.616255e-35
