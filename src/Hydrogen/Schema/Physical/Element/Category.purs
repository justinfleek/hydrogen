-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // physical // element // category
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Category — Chemical classification (metals, nonmetals, etc.)
-- |
-- | ## PURPOSE
-- | IUPAC element category classification for:
-- | - Periodic table coloring
-- | - Material property prediction
-- | - Chemical behavior grouping
-- |
-- | ## SCHEMA CLASSIFICATION
-- | - Type: ATOM (10 discrete categories)
-- | - Pillar: Physical
-- | - Parent: Element.purs
-- |
-- | ## AUTHORITY
-- | IUPAC element classification
-- |
-- | ## CHECKLIST COMPLIANCE
-- | - [x] BOUNDS: 10 categories covering all 118 elements
-- | - [x] UI ELEMENTS: categoryColor for periodic table rendering
-- | - [x] PURE MATH: Total function, every element has exactly one category

module Hydrogen.Schema.Physical.Element.Category
  ( -- * Element Category
    ElementCategory(..)
  , allElementCategories
  , category
  , categoryColor
  
  -- * Category Predicates
  , isMetal
  , isNonmetal
  , isMetalloid
  , isNobleGas
  , isAlkaliMetal
  , isAlkalineEarthMetal
  , isTransitionMetal
  , isLanthanide
  , isActinide
  , isHalogen
  , isPostTransitionMetal
  , isReactiveNonmetal
  
  -- * Occurrence Predicates
  , isNaturallyOccurring
  , isSynthetic
  , isRadioactive
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , top
  , bottom
  , (==)
  , (||)
  , (>=)
  , (<=)
  , (>)
  )

import Hydrogen.Schema.Physical.Element (Element(..), atomicNumber, unwrapAtomicNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // element category
-- ═════════════════════════════════════════════════════════════════════════════

-- | IUPAC element category classification.
-- |
-- | These 10 categories cover all 118 known elements.
data ElementCategory
  = AlkaliMetal          -- ^ Group 1 (except H): Li, Na, K, Rb, Cs, Fr
  | AlkalineEarthMetal   -- ^ Group 2: Be, Mg, Ca, Sr, Ba, Ra
  | TransitionMetal      -- ^ Groups 3-12 (d-block, excluding f-block)
  | PostTransitionMetal  -- ^ Al, Ga, In, Sn, Tl, Pb, Bi, Po, Fl, Mc, Lv
  | Metalloid            -- ^ B, Si, Ge, As, Sb, Te, At
  | ReactiveNonmetal     -- ^ H, C, N, O, P, S, Se, F, Cl, Br, I
  | NobleGas             -- ^ Group 18: He, Ne, Ar, Kr, Xe, Rn, Og
  | Lanthanide           -- ^ Z=57-71: La through Lu
  | Actinide             -- ^ Z=89-103: Ac through Lr
  | Unknown              -- ^ Properties unconfirmed: Nh, Ts

derive instance eqElementCategory :: Eq ElementCategory
derive instance ordElementCategory :: Ord ElementCategory

instance showElementCategory :: Show ElementCategory where
  show AlkaliMetal = "Alkali Metal"
  show AlkalineEarthMetal = "Alkaline Earth Metal"
  show TransitionMetal = "Transition Metal"
  show PostTransitionMetal = "Post-Transition Metal"
  show Metalloid = "Metalloid"
  show ReactiveNonmetal = "Reactive Nonmetal"
  show NobleGas = "Noble Gas"
  show Lanthanide = "Lanthanide"
  show Actinide = "Actinide"
  show Unknown = "Unknown"

instance boundedElementCategory :: Bounded ElementCategory where
  top = Unknown
  bottom = AlkaliMetal

-- | All element categories for UI enumeration.
allElementCategories :: Array ElementCategory
allElementCategories =
  [ AlkaliMetal, AlkalineEarthMetal, TransitionMetal, PostTransitionMetal
  , Metalloid, ReactiveNonmetal, NobleGas, Lanthanide, Actinide, Unknown
  ]

-- | Hex color for category (for periodic table UI).
-- |
-- | Colors chosen for accessibility and visual distinction.
categoryColor :: ElementCategory -> String
categoryColor AlkaliMetal = "#FF6B6B"
categoryColor AlkalineEarthMetal = "#FFE66D"
categoryColor TransitionMetal = "#4ECDC4"
categoryColor PostTransitionMetal = "#95E1D3"
categoryColor Metalloid = "#A8D8EA"
categoryColor ReactiveNonmetal = "#98D8C8"
categoryColor NobleGas = "#C9B1FF"
categoryColor Lanthanide = "#FFB7B2"
categoryColor Actinide = "#FFDAC1"
categoryColor Unknown = "#E2E2E2"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // category // function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get category of an element.
-- |
-- | Total function: every element maps to exactly one category.
category :: Element -> ElementCategory
-- Alkali metals (Group 1, except H)
category Lithium = AlkaliMetal
category Sodium = AlkaliMetal
category Potassium = AlkaliMetal
category Rubidium = AlkaliMetal
category Cesium = AlkaliMetal
category Francium = AlkaliMetal
-- Alkaline earth metals (Group 2)
category Beryllium = AlkalineEarthMetal
category Magnesium = AlkalineEarthMetal
category Calcium = AlkalineEarthMetal
category Strontium = AlkalineEarthMetal
category Barium = AlkalineEarthMetal
category Radium = AlkalineEarthMetal
-- Noble gases (Group 18)
category Helium = NobleGas
category Neon = NobleGas
category Argon = NobleGas
category Krypton = NobleGas
category Xenon = NobleGas
category Radon = NobleGas
category Oganesson = NobleGas
-- Metalloids
category Boron = Metalloid
category Silicon = Metalloid
category Germanium = Metalloid
category Arsenic = Metalloid
category Antimony = Metalloid
category Tellurium = Metalloid
category Astatine = Metalloid
-- Reactive nonmetals
category Hydrogen = ReactiveNonmetal
category Carbon = ReactiveNonmetal
category Nitrogen = ReactiveNonmetal
category Oxygen = ReactiveNonmetal
category Phosphorus = ReactiveNonmetal
category Sulfur = ReactiveNonmetal
category Selenium = ReactiveNonmetal
category Fluorine = ReactiveNonmetal
category Chlorine = ReactiveNonmetal
category Bromine = ReactiveNonmetal
category Iodine = ReactiveNonmetal
-- Post-transition metals
category Aluminium = PostTransitionMetal
category Gallium = PostTransitionMetal
category Indium = PostTransitionMetal
category Tin = PostTransitionMetal
category Thallium = PostTransitionMetal
category Lead = PostTransitionMetal
category Bismuth = PostTransitionMetal
category Polonium = PostTransitionMetal
category Flerovium = PostTransitionMetal
category Moscovium = PostTransitionMetal
category Livermorium = PostTransitionMetal
-- Lanthanides (Z=57-71)
category Lanthanum = Lanthanide
category Cerium = Lanthanide
category Praseodymium = Lanthanide
category Neodymium = Lanthanide
category Promethium = Lanthanide
category Samarium = Lanthanide
category Europium = Lanthanide
category Gadolinium = Lanthanide
category Terbium = Lanthanide
category Dysprosium = Lanthanide
category Holmium = Lanthanide
category Erbium = Lanthanide
category Thulium = Lanthanide
category Ytterbium = Lanthanide
category Lutetium = Lanthanide
-- Actinides (Z=89-103)
category Actinium = Actinide
category Thorium = Actinide
category Protactinium = Actinide
category Uranium = Actinide
category Neptunium = Actinide
category Plutonium = Actinide
category Americium = Actinide
category Curium = Actinide
category Berkelium = Actinide
category Californium = Actinide
category Einsteinium = Actinide
category Fermium = Actinide
category Mendelevium = Actinide
category Nobelium = Actinide
category Lawrencium = Actinide
-- Transition metals (Groups 3-12, d-block)
category Scandium = TransitionMetal
category Titanium = TransitionMetal
category Vanadium = TransitionMetal
category Chromium = TransitionMetal
category Manganese = TransitionMetal
category Iron = TransitionMetal
category Cobalt = TransitionMetal
category Nickel = TransitionMetal
category Copper = TransitionMetal
category Zinc = TransitionMetal
category Yttrium = TransitionMetal
category Zirconium = TransitionMetal
category Niobium = TransitionMetal
category Molybdenum = TransitionMetal
category Technetium = TransitionMetal
category Ruthenium = TransitionMetal
category Rhodium = TransitionMetal
category Palladium = TransitionMetal
category Silver = TransitionMetal
category Cadmium = TransitionMetal
category Hafnium = TransitionMetal
category Tantalum = TransitionMetal
category Tungsten = TransitionMetal
category Rhenium = TransitionMetal
category Osmium = TransitionMetal
category Iridium = TransitionMetal
category Platinum = TransitionMetal
category Gold = TransitionMetal
category Mercury = TransitionMetal
category Rutherfordium = TransitionMetal
category Dubnium = TransitionMetal
category Seaborgium = TransitionMetal
category Bohrium = TransitionMetal
category Hassium = TransitionMetal
category Meitnerium = TransitionMetal
category Darmstadtium = TransitionMetal
category Roentgenium = TransitionMetal
category Copernicium = TransitionMetal
-- Unknown (properties predicted but unconfirmed)
category Nihonium = Unknown
category Tennessine = Unknown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // category // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this element a metal?
-- |
-- | Metals include: alkali, alkaline earth, transition, post-transition,
-- | lanthanides, and actinides.
isMetal :: Element -> Boolean
isMetal e = case category e of
  AlkaliMetal -> true
  AlkalineEarthMetal -> true
  TransitionMetal -> true
  PostTransitionMetal -> true
  Lanthanide -> true
  Actinide -> true
  _ -> false

-- | Is this element a nonmetal?
-- |
-- | Nonmetals include: reactive nonmetals and noble gases.
isNonmetal :: Element -> Boolean
isNonmetal e = case category e of
  ReactiveNonmetal -> true
  NobleGas -> true
  _ -> false

-- | Is this element a metalloid (semimetal)?
isMetalloid :: Element -> Boolean
isMetalloid e = category e == Metalloid

-- | Is this element a noble gas?
isNobleGas :: Element -> Boolean
isNobleGas e = category e == NobleGas

-- | Is this element an alkali metal?
isAlkaliMetal :: Element -> Boolean
isAlkaliMetal e = category e == AlkaliMetal

-- | Is this element an alkaline earth metal?
isAlkalineEarthMetal :: Element -> Boolean
isAlkalineEarthMetal e = category e == AlkalineEarthMetal

-- | Is this element a transition metal?
isTransitionMetal :: Element -> Boolean
isTransitionMetal e = category e == TransitionMetal

-- | Is this element a lanthanide?
isLanthanide :: Element -> Boolean
isLanthanide e = category e == Lanthanide

-- | Is this element an actinide?
isActinide :: Element -> Boolean
isActinide e = category e == Actinide

-- | Is this element a halogen?
-- |
-- | Halogens: F, Cl, Br, I, At, Ts (Group 17)
isHalogen :: Element -> Boolean
isHalogen Fluorine = true
isHalogen Chlorine = true
isHalogen Bromine = true
isHalogen Iodine = true
isHalogen Astatine = true
isHalogen Tennessine = true
isHalogen _ = false

-- | Is this element a post-transition metal?
isPostTransitionMetal :: Element -> Boolean
isPostTransitionMetal e = category e == PostTransitionMetal

-- | Is this element a reactive nonmetal?
isReactiveNonmetal :: Element -> Boolean
isReactiveNonmetal e = category e == ReactiveNonmetal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // occurrence // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this element naturally occurring?
-- |
-- | Elements with Z <= 94 occur naturally (though some only in trace amounts).
-- | Technetium (Z=43) and Promethium (Z=61) are naturally occurring only in
-- | trace amounts from spontaneous fission.
isNaturallyOccurring :: Element -> Boolean
isNaturallyOccurring e = unwrapAtomicNumber (atomicNumber e) <= 94

-- | Is this element synthetic (man-made)?
-- |
-- | Elements with Z > 94 are produced only artificially.
isSynthetic :: Element -> Boolean
isSynthetic e = unwrapAtomicNumber (atomicNumber e) > 94

-- | Is this element radioactive?
-- |
-- | All elements with Z >= 84 are radioactive (no stable isotopes).
-- | Additionally, Technetium (Z=43) and Promethium (Z=61) have no stable isotopes.
isRadioactive :: Element -> Boolean
isRadioactive e =
  let z = unwrapAtomicNumber (atomicNumber e)
  in z >= 84 || z == 43 || z == 61
