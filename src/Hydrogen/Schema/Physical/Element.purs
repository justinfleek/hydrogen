-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // physical // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chemical Element — The 118 elements of the periodic table.
-- |
-- | ## PURPOSE
-- | Foundation for physically accurate material simulation. When a BMI user
-- | touches simulated gold, the haptics must deliver correct thermal
-- | conductivity, density, and yield strength. This ADT is the atomic
-- | vocabulary from which all materials compose.
-- |
-- | ## AUTHORITY
-- | IUPAC (International Union of Pure and Applied Chemistry)
-- | https://iupac.org/what-we-do/periodic-table-of-elements/
-- |
-- | ## SCHEMA CLASSIFICATION
-- | - Type: ATOM (fundamental, not composed from other Schema types)
-- | - Pillar: Physical
-- | - Bounds: 118 discrete values (ADT, not numeric)
-- |
-- | ## CHECKLIST COMPLIANCE
-- | - [x] DEPENDENCIES: Prelude (Eq, Ord, Show, Bounded, Enum)
-- | - [x] BOUNDS: Exactly 118 constructors, 1:1 with IUPAC elements
-- | - [x] SCALING: N/A (discrete ADT)
-- | - [x] UUID5: namespace "hydrogen.schema.physical.element"
-- | - [x] INDUSTRY STANDARD: Matches IUPAC 2024 periodic table
-- | - [x] PURE MATH: Total functions, no partiality
-- | - [x] WASM: Clean enum translation
-- | - [x] HASKELL: Direct Haskell ADT equivalent
-- |
-- | ## LEAN4 MAPPING
-- | See: proofs/Hydrogen/Schema/Physical/Element.lean
-- | - `Element` inductive type with 118 constructors
-- | - `atomicNumber : Element → Fin 119` (1-indexed, 0 unused)
-- | - `fromAtomicNumber : Fin 119 → Option Element`
-- | - Theorem: `∀ e, fromAtomicNumber (atomicNumber e) = some e`
-- |
-- | ## DEPENDENTS
-- | - Physical/AtomicProperties.purs (mass, radius, electronegativity)
-- | - Physical/Metal.purs (metal element subset with properties)
-- | - Physical/Gas.purs (noble gases and gaseous elements)
-- | - Spatial/Material/Types.purs (PBR material definitions)

module Hydrogen.Schema.Physical.Element
  ( -- * Element Type
    Element(Hydrogen, Helium, Lithium, Beryllium, Boron, Carbon, Nitrogen, Oxygen, Fluorine, Neon, Sodium, Magnesium, Aluminium, Silicon, Phosphorus, Sulfur, Chlorine, Argon, Potassium, Calcium, Scandium, Titanium, Vanadium, Chromium, Manganese, Iron, Cobalt, Nickel, Copper, Zinc, Gallium, Germanium, Arsenic, Selenium, Bromine, Krypton, Rubidium, Strontium, Yttrium, Zirconium, Niobium, Molybdenum, Technetium, Ruthenium, Rhodium, Palladium, Silver, Cadmium, Indium, Tin, Antimony, Tellurium, Iodine, Xenon, Cesium, Barium, Lanthanum, Cerium, Praseodymium, Neodymium, Promethium, Samarium, Europium, Gadolinium, Terbium, Dysprosium, Holmium, Erbium, Thulium, Ytterbium, Lutetium, Hafnium, Tantalum, Tungsten, Rhenium, Osmium, Iridium, Platinum, Gold, Mercury, Thallium, Lead, Bismuth, Polonium, Astatine, Radon, Francium, Radium, Actinium, Thorium, Protactinium, Uranium, Neptunium, Plutonium, Americium, Curium, Berkelium, Californium, Einsteinium, Fermium, Mendelevium, Nobelium, Lawrencium, Rutherfordium, Dubnium, Seaborgium, Bohrium, Hassium, Meitnerium, Darmstadtium, Roentgenium, Copernicium, Nihonium, Flerovium, Moscovium, Livermorium, Tennessine, Oganesson)
  , allElements
  
  -- * Atomic Number
  , AtomicNumber
  , atomicNumber
  , mkAtomicNumber
  , unwrapAtomicNumber
  , atomicNumberBounds
  , fromAtomicNumber
  ) where

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (==)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (<>)
  , ($)
  , top
  , bottom
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps)) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // element adt
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chemical element - one of 118 known elements.
-- | Named constructors match IUPAC element names.
data Element
  -- Period 1
  = Hydrogen      -- Z=1
  | Helium        -- Z=2
  -- Period 2
  | Lithium       -- Z=3
  | Beryllium     -- Z=4
  | Boron         -- Z=5
  | Carbon        -- Z=6
  | Nitrogen      -- Z=7
  | Oxygen        -- Z=8
  | Fluorine      -- Z=9
  | Neon          -- Z=10
  -- Period 3
  | Sodium        -- Z=11
  | Magnesium     -- Z=12
  | Aluminium     -- Z=13
  | Silicon       -- Z=14
  | Phosphorus    -- Z=15
  | Sulfur        -- Z=16
  | Chlorine      -- Z=17
  | Argon         -- Z=18
  -- Period 4
  | Potassium     -- Z=19
  | Calcium       -- Z=20
  | Scandium      -- Z=21
  | Titanium      -- Z=22
  | Vanadium      -- Z=23
  | Chromium      -- Z=24
  | Manganese     -- Z=25
  | Iron          -- Z=26
  | Cobalt        -- Z=27
  | Nickel        -- Z=28
  | Copper        -- Z=29
  | Zinc          -- Z=30
  | Gallium       -- Z=31
  | Germanium     -- Z=32
  | Arsenic       -- Z=33
  | Selenium      -- Z=34
  | Bromine       -- Z=35
  | Krypton       -- Z=36
  -- Period 5
  | Rubidium      -- Z=37
  | Strontium     -- Z=38
  | Yttrium       -- Z=39
  | Zirconium     -- Z=40
  | Niobium       -- Z=41
  | Molybdenum    -- Z=42
  | Technetium    -- Z=43
  | Ruthenium     -- Z=44
  | Rhodium       -- Z=45
  | Palladium     -- Z=46
  | Silver        -- Z=47
  | Cadmium       -- Z=48
  | Indium        -- Z=49
  | Tin           -- Z=50
  | Antimony      -- Z=51
  | Tellurium     -- Z=52
  | Iodine        -- Z=53
  | Xenon         -- Z=54
  -- Period 6
  | Cesium        -- Z=55
  | Barium        -- Z=56
  | Lanthanum     -- Z=57
  | Cerium        -- Z=58
  | Praseodymium  -- Z=59
  | Neodymium     -- Z=60
  | Promethium    -- Z=61
  | Samarium      -- Z=62
  | Europium      -- Z=63
  | Gadolinium    -- Z=64
  | Terbium       -- Z=65
  | Dysprosium    -- Z=66
  | Holmium       -- Z=67
  | Erbium        -- Z=68
  | Thulium       -- Z=69
  | Ytterbium     -- Z=70
  | Lutetium      -- Z=71
  | Hafnium       -- Z=72
  | Tantalum      -- Z=73
  | Tungsten      -- Z=74
  | Rhenium       -- Z=75
  | Osmium        -- Z=76
  | Iridium       -- Z=77
  | Platinum      -- Z=78
  | Gold          -- Z=79
  | Mercury       -- Z=80
  | Thallium      -- Z=81
  | Lead          -- Z=82
  | Bismuth       -- Z=83
  | Polonium      -- Z=84
  | Astatine      -- Z=85
  | Radon         -- Z=86
  -- Period 7
  | Francium      -- Z=87
  | Radium        -- Z=88
  | Actinium      -- Z=89
  | Thorium       -- Z=90
  | Protactinium  -- Z=91
  | Uranium       -- Z=92
  | Neptunium     -- Z=93
  | Plutonium     -- Z=94
  | Americium     -- Z=95
  | Curium        -- Z=96
  | Berkelium     -- Z=97
  | Californium   -- Z=98
  | Einsteinium   -- Z=99
  | Fermium       -- Z=100
  | Mendelevium   -- Z=101
  | Nobelium      -- Z=102
  | Lawrencium    -- Z=103
  | Rutherfordium -- Z=104
  | Dubnium       -- Z=105
  | Seaborgium    -- Z=106
  | Bohrium       -- Z=107
  | Hassium       -- Z=108
  | Meitnerium    -- Z=109
  | Darmstadtium  -- Z=110
  | Roentgenium   -- Z=111
  | Copernicium   -- Z=112
  | Nihonium      -- Z=113
  | Flerovium     -- Z=114
  | Moscovium     -- Z=115
  | Livermorium   -- Z=116
  | Tennessine    -- Z=117
  | Oganesson     -- Z=118

derive instance eqElement :: Eq Element
derive instance ordElement :: Ord Element

instance showElement :: Show Element where
  show Hydrogen = "Hydrogen"
  show Helium = "Helium"
  show Lithium = "Lithium"
  show Beryllium = "Beryllium"
  show Boron = "Boron"
  show Carbon = "Carbon"
  show Nitrogen = "Nitrogen"
  show Oxygen = "Oxygen"
  show Fluorine = "Fluorine"
  show Neon = "Neon"
  show Sodium = "Sodium"
  show Magnesium = "Magnesium"
  show Aluminium = "Aluminium"
  show Silicon = "Silicon"
  show Phosphorus = "Phosphorus"
  show Sulfur = "Sulfur"
  show Chlorine = "Chlorine"
  show Argon = "Argon"
  show Potassium = "Potassium"
  show Calcium = "Calcium"
  show Scandium = "Scandium"
  show Titanium = "Titanium"
  show Vanadium = "Vanadium"
  show Chromium = "Chromium"
  show Manganese = "Manganese"
  show Iron = "Iron"
  show Cobalt = "Cobalt"
  show Nickel = "Nickel"
  show Copper = "Copper"
  show Zinc = "Zinc"
  show Gallium = "Gallium"
  show Germanium = "Germanium"
  show Arsenic = "Arsenic"
  show Selenium = "Selenium"
  show Bromine = "Bromine"
  show Krypton = "Krypton"
  show Rubidium = "Rubidium"
  show Strontium = "Strontium"
  show Yttrium = "Yttrium"
  show Zirconium = "Zirconium"
  show Niobium = "Niobium"
  show Molybdenum = "Molybdenum"
  show Technetium = "Technetium"
  show Ruthenium = "Ruthenium"
  show Rhodium = "Rhodium"
  show Palladium = "Palladium"
  show Silver = "Silver"
  show Cadmium = "Cadmium"
  show Indium = "Indium"
  show Tin = "Tin"
  show Antimony = "Antimony"
  show Tellurium = "Tellurium"
  show Iodine = "Iodine"
  show Xenon = "Xenon"
  show Cesium = "Cesium"
  show Barium = "Barium"
  show Lanthanum = "Lanthanum"
  show Cerium = "Cerium"
  show Praseodymium = "Praseodymium"
  show Neodymium = "Neodymium"
  show Promethium = "Promethium"
  show Samarium = "Samarium"
  show Europium = "Europium"
  show Gadolinium = "Gadolinium"
  show Terbium = "Terbium"
  show Dysprosium = "Dysprosium"
  show Holmium = "Holmium"
  show Erbium = "Erbium"
  show Thulium = "Thulium"
  show Ytterbium = "Ytterbium"
  show Lutetium = "Lutetium"
  show Hafnium = "Hafnium"
  show Tantalum = "Tantalum"
  show Tungsten = "Tungsten"
  show Rhenium = "Rhenium"
  show Osmium = "Osmium"
  show Iridium = "Iridium"
  show Platinum = "Platinum"
  show Gold = "Gold"
  show Mercury = "Mercury"
  show Thallium = "Thallium"
  show Lead = "Lead"
  show Bismuth = "Bismuth"
  show Polonium = "Polonium"
  show Astatine = "Astatine"
  show Radon = "Radon"
  show Francium = "Francium"
  show Radium = "Radium"
  show Actinium = "Actinium"
  show Thorium = "Thorium"
  show Protactinium = "Protactinium"
  show Uranium = "Uranium"
  show Neptunium = "Neptunium"
  show Plutonium = "Plutonium"
  show Americium = "Americium"
  show Curium = "Curium"
  show Berkelium = "Berkelium"
  show Californium = "Californium"
  show Einsteinium = "Einsteinium"
  show Fermium = "Fermium"
  show Mendelevium = "Mendelevium"
  show Nobelium = "Nobelium"
  show Lawrencium = "Lawrencium"
  show Rutherfordium = "Rutherfordium"
  show Dubnium = "Dubnium"
  show Seaborgium = "Seaborgium"
  show Bohrium = "Bohrium"
  show Hassium = "Hassium"
  show Meitnerium = "Meitnerium"
  show Darmstadtium = "Darmstadtium"
  show Roentgenium = "Roentgenium"
  show Copernicium = "Copernicium"
  show Nihonium = "Nihonium"
  show Flerovium = "Flerovium"
  show Moscovium = "Moscovium"
  show Livermorium = "Livermorium"
  show Tennessine = "Tennessine"
  show Oganesson = "Oganesson"

instance boundedElement :: Bounded Element where
  top = Oganesson
  bottom = Hydrogen

-- | All 118 elements in atomic number order.
allElements :: Array Element
allElements =
  [ Hydrogen, Helium, Lithium, Beryllium, Boron, Carbon, Nitrogen, Oxygen
  , Fluorine, Neon, Sodium, Magnesium, Aluminium, Silicon, Phosphorus, Sulfur
  , Chlorine, Argon, Potassium, Calcium, Scandium, Titanium, Vanadium, Chromium
  , Manganese, Iron, Cobalt, Nickel, Copper, Zinc, Gallium, Germanium
  , Arsenic, Selenium, Bromine, Krypton, Rubidium, Strontium, Yttrium, Zirconium
  , Niobium, Molybdenum, Technetium, Ruthenium, Rhodium, Palladium, Silver, Cadmium
  , Indium, Tin, Antimony, Tellurium, Iodine, Xenon, Cesium, Barium
  , Lanthanum, Cerium, Praseodymium, Neodymium, Promethium, Samarium, Europium
  , Gadolinium, Terbium, Dysprosium, Holmium, Erbium, Thulium, Ytterbium, Lutetium
  , Hafnium, Tantalum, Tungsten, Rhenium, Osmium, Iridium, Platinum, Gold
  , Mercury, Thallium, Lead, Bismuth, Polonium, Astatine, Radon, Francium
  , Radium, Actinium, Thorium, Protactinium, Uranium, Neptunium, Plutonium
  , Americium, Curium, Berkelium, Californium, Einsteinium, Fermium, Mendelevium
  , Nobelium, Lawrencium, Rutherfordium, Dubnium, Seaborgium, Bohrium, Hassium
  , Meitnerium, Darmstadtium, Roentgenium, Copernicium, Nihonium, Flerovium
  , Moscovium, Livermorium, Tennessine, Oganesson
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // atomic number
-- ═════════════════════════════════════════════════════════════════════════════

-- | Atomic number (Z) - bounded 1-118.
-- | The number of protons in an atom's nucleus.
newtype AtomicNumber = AtomicNumber Int

derive instance eqAtomicNumber :: Eq AtomicNumber
derive instance ordAtomicNumber :: Ord AtomicNumber

instance showAtomicNumber :: Show AtomicNumber where
  show (AtomicNumber z) = "Z=" <> show z

-- | Create bounded atomic number (clamps to 1-118).
mkAtomicNumber :: Int -> AtomicNumber
mkAtomicNumber n = AtomicNumber (Bounded.clampInt 1 118 n)

-- | Extract raw value.
unwrapAtomicNumber :: AtomicNumber -> Int
unwrapAtomicNumber (AtomicNumber z) = z

-- | Bounds documentation.
atomicNumberBounds :: Bounded.IntBounds
atomicNumberBounds = Bounded.intBounds 1 118 Bounded.Clamps
  "atomicNumber" "Atomic number (proton count), 1-118"

-- | Get atomic number of an element.
atomicNumber :: Element -> AtomicNumber
atomicNumber Hydrogen = AtomicNumber 1
atomicNumber Helium = AtomicNumber 2
atomicNumber Lithium = AtomicNumber 3
atomicNumber Beryllium = AtomicNumber 4
atomicNumber Boron = AtomicNumber 5
atomicNumber Carbon = AtomicNumber 6
atomicNumber Nitrogen = AtomicNumber 7
atomicNumber Oxygen = AtomicNumber 8
atomicNumber Fluorine = AtomicNumber 9
atomicNumber Neon = AtomicNumber 10
atomicNumber Sodium = AtomicNumber 11
atomicNumber Magnesium = AtomicNumber 12
atomicNumber Aluminium = AtomicNumber 13
atomicNumber Silicon = AtomicNumber 14
atomicNumber Phosphorus = AtomicNumber 15
atomicNumber Sulfur = AtomicNumber 16
atomicNumber Chlorine = AtomicNumber 17
atomicNumber Argon = AtomicNumber 18
atomicNumber Potassium = AtomicNumber 19
atomicNumber Calcium = AtomicNumber 20
atomicNumber Scandium = AtomicNumber 21
atomicNumber Titanium = AtomicNumber 22
atomicNumber Vanadium = AtomicNumber 23
atomicNumber Chromium = AtomicNumber 24
atomicNumber Manganese = AtomicNumber 25
atomicNumber Iron = AtomicNumber 26
atomicNumber Cobalt = AtomicNumber 27
atomicNumber Nickel = AtomicNumber 28
atomicNumber Copper = AtomicNumber 29
atomicNumber Zinc = AtomicNumber 30
atomicNumber Gallium = AtomicNumber 31
atomicNumber Germanium = AtomicNumber 32
atomicNumber Arsenic = AtomicNumber 33
atomicNumber Selenium = AtomicNumber 34
atomicNumber Bromine = AtomicNumber 35
atomicNumber Krypton = AtomicNumber 36
atomicNumber Rubidium = AtomicNumber 37
atomicNumber Strontium = AtomicNumber 38
atomicNumber Yttrium = AtomicNumber 39
atomicNumber Zirconium = AtomicNumber 40
atomicNumber Niobium = AtomicNumber 41
atomicNumber Molybdenum = AtomicNumber 42
atomicNumber Technetium = AtomicNumber 43
atomicNumber Ruthenium = AtomicNumber 44
atomicNumber Rhodium = AtomicNumber 45
atomicNumber Palladium = AtomicNumber 46
atomicNumber Silver = AtomicNumber 47
atomicNumber Cadmium = AtomicNumber 48
atomicNumber Indium = AtomicNumber 49
atomicNumber Tin = AtomicNumber 50
atomicNumber Antimony = AtomicNumber 51
atomicNumber Tellurium = AtomicNumber 52
atomicNumber Iodine = AtomicNumber 53
atomicNumber Xenon = AtomicNumber 54
atomicNumber Cesium = AtomicNumber 55
atomicNumber Barium = AtomicNumber 56
atomicNumber Lanthanum = AtomicNumber 57
atomicNumber Cerium = AtomicNumber 58
atomicNumber Praseodymium = AtomicNumber 59
atomicNumber Neodymium = AtomicNumber 60
atomicNumber Promethium = AtomicNumber 61
atomicNumber Samarium = AtomicNumber 62
atomicNumber Europium = AtomicNumber 63
atomicNumber Gadolinium = AtomicNumber 64
atomicNumber Terbium = AtomicNumber 65
atomicNumber Dysprosium = AtomicNumber 66
atomicNumber Holmium = AtomicNumber 67
atomicNumber Erbium = AtomicNumber 68
atomicNumber Thulium = AtomicNumber 69
atomicNumber Ytterbium = AtomicNumber 70
atomicNumber Lutetium = AtomicNumber 71
atomicNumber Hafnium = AtomicNumber 72
atomicNumber Tantalum = AtomicNumber 73
atomicNumber Tungsten = AtomicNumber 74
atomicNumber Rhenium = AtomicNumber 75
atomicNumber Osmium = AtomicNumber 76
atomicNumber Iridium = AtomicNumber 77
atomicNumber Platinum = AtomicNumber 78
atomicNumber Gold = AtomicNumber 79
atomicNumber Mercury = AtomicNumber 80
atomicNumber Thallium = AtomicNumber 81
atomicNumber Lead = AtomicNumber 82
atomicNumber Bismuth = AtomicNumber 83
atomicNumber Polonium = AtomicNumber 84
atomicNumber Astatine = AtomicNumber 85
atomicNumber Radon = AtomicNumber 86
atomicNumber Francium = AtomicNumber 87
atomicNumber Radium = AtomicNumber 88
atomicNumber Actinium = AtomicNumber 89
atomicNumber Thorium = AtomicNumber 90
atomicNumber Protactinium = AtomicNumber 91
atomicNumber Uranium = AtomicNumber 92
atomicNumber Neptunium = AtomicNumber 93
atomicNumber Plutonium = AtomicNumber 94
atomicNumber Americium = AtomicNumber 95
atomicNumber Curium = AtomicNumber 96
atomicNumber Berkelium = AtomicNumber 97
atomicNumber Californium = AtomicNumber 98
atomicNumber Einsteinium = AtomicNumber 99
atomicNumber Fermium = AtomicNumber 100
atomicNumber Mendelevium = AtomicNumber 101
atomicNumber Nobelium = AtomicNumber 102
atomicNumber Lawrencium = AtomicNumber 103
atomicNumber Rutherfordium = AtomicNumber 104
atomicNumber Dubnium = AtomicNumber 105
atomicNumber Seaborgium = AtomicNumber 106
atomicNumber Bohrium = AtomicNumber 107
atomicNumber Hassium = AtomicNumber 108
atomicNumber Meitnerium = AtomicNumber 109
atomicNumber Darmstadtium = AtomicNumber 110
atomicNumber Roentgenium = AtomicNumber 111
atomicNumber Copernicium = AtomicNumber 112
atomicNumber Nihonium = AtomicNumber 113
atomicNumber Flerovium = AtomicNumber 114
atomicNumber Moscovium = AtomicNumber 115
atomicNumber Livermorium = AtomicNumber 116
atomicNumber Tennessine = AtomicNumber 117
atomicNumber Oganesson = AtomicNumber 118

-- | Lookup element by atomic number.
fromAtomicNumber :: AtomicNumber -> Maybe Element
fromAtomicNumber (AtomicNumber z)
  | z == 1 = Just Hydrogen
  | z == 2 = Just Helium
  | z == 3 = Just Lithium
  | z == 4 = Just Beryllium
  | z == 5 = Just Boron
  | z == 6 = Just Carbon
  | z == 7 = Just Nitrogen
  | z == 8 = Just Oxygen
  | z == 9 = Just Fluorine
  | z == 10 = Just Neon
  | z == 11 = Just Sodium
  | z == 12 = Just Magnesium
  | z == 13 = Just Aluminium
  | z == 14 = Just Silicon
  | z == 15 = Just Phosphorus
  | z == 16 = Just Sulfur
  | z == 17 = Just Chlorine
  | z == 18 = Just Argon
  | z == 19 = Just Potassium
  | z == 20 = Just Calcium
  | z == 21 = Just Scandium
  | z == 22 = Just Titanium
  | z == 23 = Just Vanadium
  | z == 24 = Just Chromium
  | z == 25 = Just Manganese
  | z == 26 = Just Iron
  | z == 27 = Just Cobalt
  | z == 28 = Just Nickel
  | z == 29 = Just Copper
  | z == 30 = Just Zinc
  | z == 31 = Just Gallium
  | z == 32 = Just Germanium
  | z == 33 = Just Arsenic
  | z == 34 = Just Selenium
  | z == 35 = Just Bromine
  | z == 36 = Just Krypton
  | z == 37 = Just Rubidium
  | z == 38 = Just Strontium
  | z == 39 = Just Yttrium
  | z == 40 = Just Zirconium
  | z == 41 = Just Niobium
  | z == 42 = Just Molybdenum
  | z == 43 = Just Technetium
  | z == 44 = Just Ruthenium
  | z == 45 = Just Rhodium
  | z == 46 = Just Palladium
  | z == 47 = Just Silver
  | z == 48 = Just Cadmium
  | z == 49 = Just Indium
  | z == 50 = Just Tin
  | z == 51 = Just Antimony
  | z == 52 = Just Tellurium
  | z == 53 = Just Iodine
  | z == 54 = Just Xenon
  | z == 55 = Just Cesium
  | z == 56 = Just Barium
  | z == 57 = Just Lanthanum
  | z == 58 = Just Cerium
  | z == 59 = Just Praseodymium
  | z == 60 = Just Neodymium
  | z == 61 = Just Promethium
  | z == 62 = Just Samarium
  | z == 63 = Just Europium
  | z == 64 = Just Gadolinium
  | z == 65 = Just Terbium
  | z == 66 = Just Dysprosium
  | z == 67 = Just Holmium
  | z == 68 = Just Erbium
  | z == 69 = Just Thulium
  | z == 70 = Just Ytterbium
  | z == 71 = Just Lutetium
  | z == 72 = Just Hafnium
  | z == 73 = Just Tantalum
  | z == 74 = Just Tungsten
  | z == 75 = Just Rhenium
  | z == 76 = Just Osmium
  | z == 77 = Just Iridium
  | z == 78 = Just Platinum
  | z == 79 = Just Gold
  | z == 80 = Just Mercury
  | z == 81 = Just Thallium
  | z == 82 = Just Lead
  | z == 83 = Just Bismuth
  | z == 84 = Just Polonium
  | z == 85 = Just Astatine
  | z == 86 = Just Radon
  | z == 87 = Just Francium
  | z == 88 = Just Radium
  | z == 89 = Just Actinium
  | z == 90 = Just Thorium
  | z == 91 = Just Protactinium
  | z == 92 = Just Uranium
  | z == 93 = Just Neptunium
  | z == 94 = Just Plutonium
  | z == 95 = Just Americium
  | z == 96 = Just Curium
  | z == 97 = Just Berkelium
  | z == 98 = Just Californium
  | z == 99 = Just Einsteinium
  | z == 100 = Just Fermium
  | z == 101 = Just Mendelevium
  | z == 102 = Just Nobelium
  | z == 103 = Just Lawrencium
  | z == 104 = Just Rutherfordium
  | z == 105 = Just Dubnium
  | z == 106 = Just Seaborgium
  | z == 107 = Just Bohrium
  | z == 108 = Just Hassium
  | z == 109 = Just Meitnerium
  | z == 110 = Just Darmstadtium
  | z == 111 = Just Roentgenium
  | z == 112 = Just Copernicium
  | z == 113 = Just Nihonium
  | z == 114 = Just Flerovium
  | z == 115 = Just Moscovium
  | z == 116 = Just Livermorium
  | z == 117 = Just Tennessine
  | z == 118 = Just Oganesson
  | otherwise = Nothing
