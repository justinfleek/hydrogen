-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // engineering // tolerance // datum
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Datum references and material condition modifiers for GD&T.
-- |
-- | ## Datum Labels
-- |
-- | Datum labels (A-Z) per ASME Y14.5. Letters I, O, Q are excluded
-- | to avoid confusion with numbers.
-- |
-- | ## Material Conditions
-- |
-- | - **MMC**: Maximum Material Condition (largest shaft, smallest hole)
-- | - **LMC**: Least Material Condition (smallest shaft, largest hole)
-- | - **RFS**: Regardless of Feature Size (default, no symbol)

module Hydrogen.Schema.Engineering.Tolerance.Datum
  ( -- * Datum Labels
    DatumLabel(DatumA, DatumB, DatumC, DatumD, DatumE, DatumF, DatumG, DatumH, DatumJ, DatumK, DatumL, DatumM, DatumN, DatumP, DatumR, DatumS, DatumT, DatumU, DatumV, DatumW, DatumX, DatumY, DatumZ)
  , allDatumLabels
  , datumLabelChar
  
  -- * Datum Features
  , DatumFeature(DatumFeature)
  , datumFeature
  , primaryDatum
  , secondaryDatum
  , tertiaryDatum
  
  -- * Material Conditions
  , MaterialCondition(MMC, LMC, RFS)
  , allMaterialConditions
  , conditionSymbol
  , conditionDescription
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // datum // reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Datum labels (A-Z per ASME Y14.5).
data DatumLabel
  = DatumA | DatumB | DatumC | DatumD | DatumE | DatumF
  | DatumG | DatumH | DatumJ | DatumK | DatumL | DatumM
  | DatumN | DatumP | DatumR | DatumS | DatumT | DatumU
  | DatumV | DatumW | DatumX | DatumY | DatumZ

derive instance eqDatumLabel :: Eq DatumLabel
derive instance ordDatumLabel :: Ord DatumLabel

instance showDatumLabel :: Show DatumLabel where
  show d = "Datum " <> datumLabelChar d

-- | All datum labels for enumeration.
-- | Note: I, O, Q excluded per standard (confusing with numbers).
allDatumLabels :: Array DatumLabel
allDatumLabels =
  [ DatumA, DatumB, DatumC, DatumD, DatumE, DatumF
  , DatumG, DatumH, DatumJ, DatumK, DatumL, DatumM
  , DatumN, DatumP, DatumR, DatumS, DatumT, DatumU
  , DatumV, DatumW, DatumX, DatumY, DatumZ
  ]

-- | Get single character for datum.
datumLabelChar :: DatumLabel -> String
datumLabelChar DatumA = "A"
datumLabelChar DatumB = "B"
datumLabelChar DatumC = "C"
datumLabelChar DatumD = "D"
datumLabelChar DatumE = "E"
datumLabelChar DatumF = "F"
datumLabelChar DatumG = "G"
datumLabelChar DatumH = "H"
datumLabelChar DatumJ = "J"
datumLabelChar DatumK = "K"
datumLabelChar DatumL = "L"
datumLabelChar DatumM = "M"
datumLabelChar DatumN = "N"
datumLabelChar DatumP = "P"
datumLabelChar DatumR = "R"
datumLabelChar DatumS = "S"
datumLabelChar DatumT = "T"
datumLabelChar DatumU = "U"
datumLabelChar DatumV = "V"
datumLabelChar DatumW = "W"
datumLabelChar DatumX = "X"
datumLabelChar DatumY = "Y"
datumLabelChar DatumZ = "Z"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // datum // feature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Datum feature with optional material condition modifier.
data DatumFeature = DatumFeature
  { label :: DatumLabel
  , modifier :: Maybe MaterialCondition
  }

derive instance eqDatumFeature :: Eq DatumFeature

instance showDatumFeature :: Show DatumFeature where
  show (DatumFeature d) = 
    datumLabelChar d.label <> case d.modifier of
      Nothing -> ""
      Just m -> conditionSymbol m

-- | Create datum feature.
datumFeature :: DatumLabel -> Maybe MaterialCondition -> DatumFeature
datumFeature label modifier = DatumFeature { label, modifier }

-- | Primary datum (no modifier).
primaryDatum :: DatumLabel -> DatumFeature
primaryDatum label = DatumFeature { label, modifier: Nothing }

-- | Secondary datum (no modifier).
secondaryDatum :: DatumLabel -> DatumFeature
secondaryDatum = primaryDatum

-- | Tertiary datum (no modifier).
tertiaryDatum :: DatumLabel -> DatumFeature
tertiaryDatum = primaryDatum

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // material // condition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material condition modifiers (ASME Y14.5).
data MaterialCondition
  = MMC  -- ^ Maximum Material Condition
  | LMC  -- ^ Least Material Condition
  | RFS  -- ^ Regardless of Feature Size (default, no symbol)

derive instance eqMaterialCondition :: Eq MaterialCondition
derive instance ordMaterialCondition :: Ord MaterialCondition

instance showMaterialCondition :: Show MaterialCondition where
  show MMC = "MMC"
  show LMC = "LMC"
  show RFS = "RFS"

-- | All material conditions for enumeration.
allMaterialConditions :: Array MaterialCondition
allMaterialConditions = [MMC, LMC, RFS]

-- | Symbol for material condition.
conditionSymbol :: MaterialCondition -> String
conditionSymbol MMC = "(M)"
conditionSymbol LMC = "(L)"
conditionSymbol RFS = ""  -- No symbol per standard

-- | Description of material condition.
conditionDescription :: MaterialCondition -> String
conditionDescription MMC = "Maximum Material Condition - largest shaft, smallest hole"
conditionDescription LMC = "Least Material Condition - smallest shaft, largest hole"
conditionDescription RFS = "Regardless of Feature Size - tolerance applies at any size"
