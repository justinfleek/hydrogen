-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // physical // element // block
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Block — Electron orbital block classification (s, p, d, f).
-- |
-- | ## PURPOSE
-- | Classification by valence electron orbital type. Essential for:
-- | - Periodic table layout (f-block elements shown separately)
-- | - Predicting chemical properties
-- | - Understanding electron configurations
-- |
-- | ## SCHEMA CLASSIFICATION
-- | - Type: ATOM (4 discrete values)
-- | - Pillar: Physical
-- | - Parent: Element.purs
-- |
-- | ## AUTHORITY
-- | IUPAC electron configuration notation
-- |
-- | ## CHECKLIST COMPLIANCE
-- | - [x] BOUNDS: Exactly 4 blocks (s, p, d, f)
-- | - [x] PURE MATH: Total function over all 118 elements
-- | - [x] INDUSTRY STANDARD: IUPAC block definitions

module Hydrogen.Schema.Physical.Element.Block
  ( ElementBlock(..)
  , allElementBlocks
  , block
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , top
  , bottom
  )

import Hydrogen.Schema.Physical.Element (Element(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // element block
-- ═════════════════════════════════════════════════════════════════════════════

-- | Electron orbital block (s, p, d, f).
-- |
-- | Determines valence electron behavior and chemical properties.
data ElementBlock
  = SBlock  -- ^ Groups 1-2 + He (s orbital filling)
  | PBlock  -- ^ Groups 13-18 (p orbital filling)
  | DBlock  -- ^ Groups 3-12 (d orbital filling, transition metals)
  | FBlock  -- ^ Lanthanides and Actinides (f orbital filling)

derive instance eqElementBlock :: Eq ElementBlock
derive instance ordElementBlock :: Ord ElementBlock

instance showElementBlock :: Show ElementBlock where
  show SBlock = "s-block"
  show PBlock = "p-block"
  show DBlock = "d-block"
  show FBlock = "f-block"

instance boundedElementBlock :: Bounded ElementBlock where
  top = FBlock
  bottom = SBlock

-- | All element blocks for UI enumeration.
allElementBlocks :: Array ElementBlock
allElementBlocks = [SBlock, PBlock, DBlock, FBlock]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // block // function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get block of an element based on electron configuration.
-- |
-- | Total function: every element maps to exactly one block.
block :: Element -> ElementBlock
-- s-block (Groups 1-2 + He)
block Hydrogen = SBlock
block Helium = SBlock
block Lithium = SBlock
block Beryllium = SBlock
block Sodium = SBlock
block Magnesium = SBlock
block Potassium = SBlock
block Calcium = SBlock
block Rubidium = SBlock
block Strontium = SBlock
block Cesium = SBlock
block Barium = SBlock
block Francium = SBlock
block Radium = SBlock
-- f-block (Lanthanides Z=57-71)
block Lanthanum = FBlock
block Cerium = FBlock
block Praseodymium = FBlock
block Neodymium = FBlock
block Promethium = FBlock
block Samarium = FBlock
block Europium = FBlock
block Gadolinium = FBlock
block Terbium = FBlock
block Dysprosium = FBlock
block Holmium = FBlock
block Erbium = FBlock
block Thulium = FBlock
block Ytterbium = FBlock
block Lutetium = FBlock
-- f-block (Actinides Z=89-103)
block Actinium = FBlock
block Thorium = FBlock
block Protactinium = FBlock
block Uranium = FBlock
block Neptunium = FBlock
block Plutonium = FBlock
block Americium = FBlock
block Curium = FBlock
block Berkelium = FBlock
block Californium = FBlock
block Einsteinium = FBlock
block Fermium = FBlock
block Mendelevium = FBlock
block Nobelium = FBlock
block Lawrencium = FBlock
-- d-block (Transition metals, Groups 3-12)
block Scandium = DBlock
block Titanium = DBlock
block Vanadium = DBlock
block Chromium = DBlock
block Manganese = DBlock
block Iron = DBlock
block Cobalt = DBlock
block Nickel = DBlock
block Copper = DBlock
block Zinc = DBlock
block Yttrium = DBlock
block Zirconium = DBlock
block Niobium = DBlock
block Molybdenum = DBlock
block Technetium = DBlock
block Ruthenium = DBlock
block Rhodium = DBlock
block Palladium = DBlock
block Silver = DBlock
block Cadmium = DBlock
block Hafnium = DBlock
block Tantalum = DBlock
block Tungsten = DBlock
block Rhenium = DBlock
block Osmium = DBlock
block Iridium = DBlock
block Platinum = DBlock
block Gold = DBlock
block Mercury = DBlock
block Rutherfordium = DBlock
block Dubnium = DBlock
block Seaborgium = DBlock
block Bohrium = DBlock
block Hassium = DBlock
block Meitnerium = DBlock
block Darmstadtium = DBlock
block Roentgenium = DBlock
block Copernicium = DBlock
-- p-block (Groups 13-18, except He)
block Boron = PBlock
block Carbon = PBlock
block Nitrogen = PBlock
block Oxygen = PBlock
block Fluorine = PBlock
block Neon = PBlock
block Aluminium = PBlock
block Silicon = PBlock
block Phosphorus = PBlock
block Sulfur = PBlock
block Chlorine = PBlock
block Argon = PBlock
block Gallium = PBlock
block Germanium = PBlock
block Arsenic = PBlock
block Selenium = PBlock
block Bromine = PBlock
block Krypton = PBlock
block Indium = PBlock
block Tin = PBlock
block Antimony = PBlock
block Tellurium = PBlock
block Iodine = PBlock
block Xenon = PBlock
block Thallium = PBlock
block Lead = PBlock
block Bismuth = PBlock
block Polonium = PBlock
block Astatine = PBlock
block Radon = PBlock
block Nihonium = PBlock
block Flerovium = PBlock
block Moscovium = PBlock
block Livermorium = PBlock
block Tennessine = PBlock
block Oganesson = PBlock
