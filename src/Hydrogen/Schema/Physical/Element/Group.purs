-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // physical // element // group
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Group — Column of the periodic table (1-18).
-- |
-- | ## PURPOSE
-- | Group determines valence electron count and chemical behavior.
-- | Essential for:
-- | - Periodic table layout (columns)
-- | - Predicting valence and bonding
-- | - Chemical family classification
-- |
-- | ## SCHEMA CLASSIFICATION
-- | - Type: ATOM (bounded Int 1-18)
-- | - Pillar: Physical
-- | - Parent: Element.purs
-- |
-- | ## BOUNDS
-- | - Min: 1 (Alkali metals + Hydrogen)
-- | - Max: 18 (Noble gases)
-- | - Behavior: Clamps
-- |
-- | ## NOTE ON LANTHANIDES/ACTINIDES
-- | f-block elements (La-Lu, Ac-Lr) are conventionally placed in Group 3,
-- | though they could be considered their own f-block groups.
-- |
-- | ## AUTHORITY
-- | IUPAC 1-18 group numbering (supersedes old IA-VIIIA system)

module Hydrogen.Schema.Physical.Element.Group
  ( Group
  , mkGroup
  , unwrapGroup
  , group
  , groupBounds
  , groupName
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps)) as Bounded
import Hydrogen.Schema.Physical.Element (Element(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group (column) of periodic table, bounded 1-18.
-- |
-- | Determines valence electron count (for main group elements).
newtype Group = Group Int

derive instance eqGroup :: Eq Group
derive instance ordGroup :: Ord Group

instance showGroup :: Show Group where
  show (Group g) = "Group " <> show g

-- | Create bounded group (clamps to 1-18).
mkGroup :: Int -> Group
mkGroup n = Group (Bounded.clampInt 1 18 n)

-- | Extract raw value.
unwrapGroup :: Group -> Int
unwrapGroup (Group g) = g

-- | Bounds documentation for UI/serialization.
groupBounds :: Bounded.IntBounds
groupBounds = Bounded.intBounds 1 18 Bounded.Clamps
  "group" "Periodic table column (1-18)"

-- | IUPAC group names for named groups.
-- |
-- | Only certain groups have official IUPAC names.
groupName :: Group -> Maybe String
groupName (Group 1) = Just "Alkali metals"
groupName (Group 2) = Just "Alkaline earth metals"
groupName (Group 17) = Just "Halogens"
groupName (Group 18) = Just "Noble gases"
groupName _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // group // function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get group of an element.
-- |
-- | Total function: every element maps to exactly one group.
-- | Lanthanides and Actinides are placed in Group 3 by convention.
group :: Element -> Group
-- Group 1 (Alkali metals + H)
group Hydrogen = Group 1
group Lithium = Group 1
group Sodium = Group 1
group Potassium = Group 1
group Rubidium = Group 1
group Cesium = Group 1
group Francium = Group 1
-- Group 2 (Alkaline earth metals)
group Beryllium = Group 2
group Magnesium = Group 2
group Calcium = Group 2
group Strontium = Group 2
group Barium = Group 2
group Radium = Group 2
-- Group 3 (Sc, Y, La, Ac + Lanthanides/Actinides by convention)
group Scandium = Group 3
group Yttrium = Group 3
group Lanthanum = Group 3
group Actinium = Group 3
group Cerium = Group 3
group Praseodymium = Group 3
group Neodymium = Group 3
group Promethium = Group 3
group Samarium = Group 3
group Europium = Group 3
group Gadolinium = Group 3
group Terbium = Group 3
group Dysprosium = Group 3
group Holmium = Group 3
group Erbium = Group 3
group Thulium = Group 3
group Ytterbium = Group 3
group Lutetium = Group 3
group Thorium = Group 3
group Protactinium = Group 3
group Uranium = Group 3
group Neptunium = Group 3
group Plutonium = Group 3
group Americium = Group 3
group Curium = Group 3
group Berkelium = Group 3
group Californium = Group 3
group Einsteinium = Group 3
group Fermium = Group 3
group Mendelevium = Group 3
group Nobelium = Group 3
group Lawrencium = Group 3
-- Group 4
group Titanium = Group 4
group Zirconium = Group 4
group Hafnium = Group 4
group Rutherfordium = Group 4
-- Group 5
group Vanadium = Group 5
group Niobium = Group 5
group Tantalum = Group 5
group Dubnium = Group 5
-- Group 6
group Chromium = Group 6
group Molybdenum = Group 6
group Tungsten = Group 6
group Seaborgium = Group 6
-- Group 7
group Manganese = Group 7
group Technetium = Group 7
group Rhenium = Group 7
group Bohrium = Group 7
-- Group 8
group Iron = Group 8
group Ruthenium = Group 8
group Osmium = Group 8
group Hassium = Group 8
-- Group 9
group Cobalt = Group 9
group Rhodium = Group 9
group Iridium = Group 9
group Meitnerium = Group 9
-- Group 10
group Nickel = Group 10
group Palladium = Group 10
group Platinum = Group 10
group Darmstadtium = Group 10
-- Group 11 (Coinage metals)
group Copper = Group 11
group Silver = Group 11
group Gold = Group 11
group Roentgenium = Group 11
-- Group 12
group Zinc = Group 12
group Cadmium = Group 12
group Mercury = Group 12
group Copernicium = Group 12
-- Group 13 (Boron group)
group Boron = Group 13
group Aluminium = Group 13
group Gallium = Group 13
group Indium = Group 13
group Thallium = Group 13
group Nihonium = Group 13
-- Group 14 (Carbon group)
group Carbon = Group 14
group Silicon = Group 14
group Germanium = Group 14
group Tin = Group 14
group Lead = Group 14
group Flerovium = Group 14
-- Group 15 (Pnictogens)
group Nitrogen = Group 15
group Phosphorus = Group 15
group Arsenic = Group 15
group Antimony = Group 15
group Bismuth = Group 15
group Moscovium = Group 15
-- Group 16 (Chalcogens)
group Oxygen = Group 16
group Sulfur = Group 16
group Selenium = Group 16
group Tellurium = Group 16
group Polonium = Group 16
group Livermorium = Group 16
-- Group 17 (Halogens)
group Fluorine = Group 17
group Chlorine = Group 17
group Bromine = Group 17
group Iodine = Group 17
group Astatine = Group 17
group Tennessine = Group 17
-- Group 18 (Noble gases)
group Helium = Group 18
group Neon = Group 18
group Argon = Group 18
group Krypton = Group 18
group Xenon = Group 18
group Radon = Group 18
group Oganesson = Group 18
