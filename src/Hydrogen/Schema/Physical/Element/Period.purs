-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // physical // element // period
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Period — Row of the periodic table (1-7).
-- |
-- | ## PURPOSE
-- | Period determines the principal quantum number of valence electrons.
-- | Essential for:
-- | - Periodic table layout (rows)
-- | - Atomic radius trends (increases down period)
-- | - Ionization energy trends (decreases down period)
-- |
-- | ## SCHEMA CLASSIFICATION
-- | - Type: ATOM (bounded Int 1-7)
-- | - Pillar: Physical
-- | - Parent: Element.purs
-- |
-- | ## BOUNDS
-- | - Min: 1 (Hydrogen, Helium)
-- | - Max: 7 (Francium through Oganesson)
-- | - Behavior: Clamps
-- |
-- | ## AUTHORITY
-- | IUPAC periodic table row numbering

module Hydrogen.Schema.Physical.Element.Period
  ( Period
  , mkPeriod
  , unwrapPeriod
  , period
  , periodBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps)) as Bounded
import Hydrogen.Schema.Physical.Element (Element(Hydrogen, Helium, Lithium, Beryllium, Boron, Carbon, Nitrogen, Oxygen, Fluorine, Neon, Sodium, Magnesium, Aluminium, Silicon, Phosphorus, Sulfur, Chlorine, Argon, Potassium, Calcium, Scandium, Titanium, Vanadium, Chromium, Manganese, Iron, Cobalt, Nickel, Copper, Zinc, Gallium, Germanium, Arsenic, Selenium, Bromine, Krypton, Rubidium, Strontium, Yttrium, Zirconium, Niobium, Molybdenum, Technetium, Ruthenium, Rhodium, Palladium, Silver, Cadmium, Indium, Tin, Antimony, Tellurium, Iodine, Xenon, Cesium, Barium, Lanthanum, Cerium, Praseodymium, Neodymium, Promethium, Samarium, Europium, Gadolinium, Terbium, Dysprosium, Holmium, Erbium, Thulium, Ytterbium, Lutetium, Hafnium, Tantalum, Tungsten, Rhenium, Osmium, Iridium, Platinum, Gold, Mercury, Thallium, Lead, Bismuth, Polonium, Astatine, Radon, Francium, Radium, Actinium, Thorium, Protactinium, Uranium, Neptunium, Plutonium, Americium, Curium, Berkelium, Californium, Einsteinium, Fermium, Mendelevium, Nobelium, Lawrencium, Rutherfordium, Dubnium, Seaborgium, Bohrium, Hassium, Meitnerium, Darmstadtium, Roentgenium, Copernicium, Nihonium, Flerovium, Moscovium, Livermorium, Tennessine, Oganesson))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // period
-- ═════════════════════════════════════════════════════════════════════════════

-- | Period (row) of periodic table, bounded 1-7.
-- |
-- | Corresponds to the principal quantum number of the outermost electrons.
newtype Period = Period Int

derive instance eqPeriod :: Eq Period
derive instance ordPeriod :: Ord Period

instance showPeriod :: Show Period where
  show (Period p) = "Period " <> show p

-- | Create bounded period (clamps to 1-7).
mkPeriod :: Int -> Period
mkPeriod n = Period (Bounded.clampInt 1 7 n)

-- | Extract raw value.
unwrapPeriod :: Period -> Int
unwrapPeriod (Period p) = p

-- | Bounds documentation for UI/serialization.
periodBounds :: Bounded.IntBounds
periodBounds = Bounded.intBounds 1 7 Bounded.Clamps
  "period" "Periodic table row (1-7)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // period // function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get period of an element.
-- |
-- | Total function: every element maps to exactly one period.
period :: Element -> Period
-- Period 1 (Z=1-2)
period Hydrogen = Period 1
period Helium = Period 1
-- Period 2 (Z=3-10)
period Lithium = Period 2
period Beryllium = Period 2
period Boron = Period 2
period Carbon = Period 2
period Nitrogen = Period 2
period Oxygen = Period 2
period Fluorine = Period 2
period Neon = Period 2
-- Period 3 (Z=11-18)
period Sodium = Period 3
period Magnesium = Period 3
period Aluminium = Period 3
period Silicon = Period 3
period Phosphorus = Period 3
period Sulfur = Period 3
period Chlorine = Period 3
period Argon = Period 3
-- Period 4 (Z=19-36)
period Potassium = Period 4
period Calcium = Period 4
period Scandium = Period 4
period Titanium = Period 4
period Vanadium = Period 4
period Chromium = Period 4
period Manganese = Period 4
period Iron = Period 4
period Cobalt = Period 4
period Nickel = Period 4
period Copper = Period 4
period Zinc = Period 4
period Gallium = Period 4
period Germanium = Period 4
period Arsenic = Period 4
period Selenium = Period 4
period Bromine = Period 4
period Krypton = Period 4
-- Period 5 (Z=37-54)
period Rubidium = Period 5
period Strontium = Period 5
period Yttrium = Period 5
period Zirconium = Period 5
period Niobium = Period 5
period Molybdenum = Period 5
period Technetium = Period 5
period Ruthenium = Period 5
period Rhodium = Period 5
period Palladium = Period 5
period Silver = Period 5
period Cadmium = Period 5
period Indium = Period 5
period Tin = Period 5
period Antimony = Period 5
period Tellurium = Period 5
period Iodine = Period 5
period Xenon = Period 5
-- Period 6 (Z=55-86)
period Cesium = Period 6
period Barium = Period 6
period Lanthanum = Period 6
period Cerium = Period 6
period Praseodymium = Period 6
period Neodymium = Period 6
period Promethium = Period 6
period Samarium = Period 6
period Europium = Period 6
period Gadolinium = Period 6
period Terbium = Period 6
period Dysprosium = Period 6
period Holmium = Period 6
period Erbium = Period 6
period Thulium = Period 6
period Ytterbium = Period 6
period Lutetium = Period 6
period Hafnium = Period 6
period Tantalum = Period 6
period Tungsten = Period 6
period Rhenium = Period 6
period Osmium = Period 6
period Iridium = Period 6
period Platinum = Period 6
period Gold = Period 6
period Mercury = Period 6
period Thallium = Period 6
period Lead = Period 6
period Bismuth = Period 6
period Polonium = Period 6
period Astatine = Period 6
period Radon = Period 6
-- Period 7 (Z=87-118)
period Francium = Period 7
period Radium = Period 7
period Actinium = Period 7
period Thorium = Period 7
period Protactinium = Period 7
period Uranium = Period 7
period Neptunium = Period 7
period Plutonium = Period 7
period Americium = Period 7
period Curium = Period 7
period Berkelium = Period 7
period Californium = Period 7
period Einsteinium = Period 7
period Fermium = Period 7
period Mendelevium = Period 7
period Nobelium = Period 7
period Lawrencium = Period 7
period Rutherfordium = Period 7
period Dubnium = Period 7
period Seaborgium = Period 7
period Bohrium = Period 7
period Hassium = Period 7
period Meitnerium = Period 7
period Darmstadtium = Period 7
period Roentgenium = Period 7
period Copernicium = Period 7
period Nihonium = Period 7
period Flerovium = Period 7
period Moscovium = Period 7
period Livermorium = Period 7
period Tennessine = Period 7
period Oganesson = Period 7
