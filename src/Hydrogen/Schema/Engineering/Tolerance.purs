-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // engineering // tolerance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GD&T (Geometric Dimensioning and Tolerancing) primitives.
-- |
-- | ## What is GD&T?
-- |
-- | GD&T is the engineering language for defining and communicating
-- | tolerances on mechanical drawings. It specifies:
-- |
-- | - **Size tolerances**: How much a dimension can vary
-- | - **Geometric tolerances**: Form, orientation, location, runout
-- | - **Datum references**: Reference features for measurements
-- | - **Material conditions**: MMC, LMC, RFS modifiers
-- |
-- | ## Standards
-- |
-- | - **ASME Y14.5-2018**: US standard (primary)
-- | - **ISO 1101:2017**: International standard
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from submodules:
-- | - `Tolerance.Characteristic` — Geometric characteristics and categories
-- | - `Tolerance.Datum` — Datum labels, features, material conditions
-- | - `Tolerance.Fit` — ISO fit classes and surface finish

module Hydrogen.Schema.Engineering.Tolerance
  ( -- * Re-exports from Characteristic
    module Hydrogen.Schema.Engineering.Tolerance.Characteristic
  
  -- * Re-exports from Datum
  , module Hydrogen.Schema.Engineering.Tolerance.Datum
  
  -- * Re-exports from Fit
  , module Hydrogen.Schema.Engineering.Tolerance.Fit
  
  -- * Tolerance Value
  , ToleranceValue
  , toleranceValue
  , toleranceValueUnsafe
  , unwrapTolerance
  , toleranceBounds
  , toleranceMm
  
  -- * Tolerance Constants
  , toleranceTight
  , tolerancePrecision
  , toleranceStandard
  , toleranceLoose
  
  -- * Feature Control Frame
  , FeatureControlFrame(..)
  , featureControlFrame
  , simpleFrame
  , frameWithDatums
  , frameWithModifier
  
  -- * Bilateral Tolerance
  , BilateralTolerance(..)
  , symmetricTolerance
  , asymmetricTolerance
  , plusTolerance
  , minusTolerance
  
  -- * Unilateral Tolerance
  , UnilateralTolerance(..)
  , unilateralPlus
  , unilateralMinus
  
  -- * Limit Dimensions
  , LimitDimension(..)
  , limitDimension
  , limitFromBilateral
  
  -- * Operations
  , toleranceStackUp
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>=)
  , (<>)
  )

import Data.Array (foldl) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- Re-export all submodules
import Hydrogen.Schema.Engineering.Tolerance.Characteristic
  ( GeometricCharacteristic(..)
  , allGeometricCharacteristics
  , characteristicSymbol
  , characteristicCategory
  , characteristicDescription
  , ToleranceCategory(..)
  , allToleranceCategories
  , isFormTolerance
  , isOrientationTolerance
  , isLocationTolerance
  , isRunoutTolerance
  , requiresDatum
  )

import Hydrogen.Schema.Engineering.Tolerance.Datum
  ( DatumLabel(..)
  , allDatumLabels
  , datumLabelChar
  , DatumFeature(..)
  , datumFeature
  , primaryDatum
  , secondaryDatum
  , tertiaryDatum
  , MaterialCondition(..)
  , allMaterialConditions
  , conditionSymbol
  , conditionDescription
  )

import Hydrogen.Schema.Engineering.Tolerance.Fit
  ( FitClass(..)
  , allFitClasses
  , fitDescription
  , fitTolerance
  , SurfaceFinish
  , surfaceFinish
  , surfaceFinishUnsafe
  , unwrapFinish
  , finishBounds
  , roughnessRa
  , finishMirror
  , finishGround
  , finishMachined
  , finishRough
  , finishCast
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // tolerance // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tolerance value in mm [0.001, 100.0].
-- |
-- | Most engineering tolerances fall in 0.01-1.0 mm range.
newtype ToleranceValue = ToleranceValue Number

derive instance eqToleranceValue :: Eq ToleranceValue

instance showToleranceValue :: Show ToleranceValue where
  show (ToleranceValue n) = "+-" <> show n <> " mm"

-- | Safe constructor with clamping.
toleranceValue :: Number -> ToleranceValue
toleranceValue n = ToleranceValue (Bounded.clampNumber 0.001 100.0 n)

-- | Unsafe constructor for known-valid values.
toleranceValueUnsafe :: Number -> ToleranceValue
toleranceValueUnsafe = ToleranceValue

-- | Extract raw value.
unwrapTolerance :: ToleranceValue -> Number
unwrapTolerance (ToleranceValue n) = n

-- | Valid bounds documentation.
toleranceBounds :: Bounded.NumberBounds
toleranceBounds = Bounded.numberBounds 0.001 100.0 Bounded.Clamps "tolerance" "Tolerance value in mm"

-- | Get tolerance in mm (identity).
toleranceMm :: ToleranceValue -> Number
toleranceMm = unwrapTolerance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // tolerance // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tight tolerance (+-0.01 mm).
toleranceTight :: ToleranceValue
toleranceTight = ToleranceValue 0.01

-- | Precision tolerance (+-0.05 mm).
tolerancePrecision :: ToleranceValue
tolerancePrecision = ToleranceValue 0.05

-- | Standard tolerance (+-0.1 mm).
toleranceStandard :: ToleranceValue
toleranceStandard = ToleranceValue 0.1

-- | Loose tolerance (+-0.5 mm).
toleranceLoose :: ToleranceValue
toleranceLoose = ToleranceValue 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // feature // control frame
-- ═════════════════════════════════════════════════════════════════════════════

-- | Feature control frame — the complete GD&T callout.
data FeatureControlFrame = FeatureControlFrame
  { characteristic :: GeometricCharacteristic
  , tolerance :: ToleranceValue
  , toleranceModifier :: Maybe MaterialCondition
  , primaryDatum_ :: Maybe DatumFeature
  , secondaryDatum_ :: Maybe DatumFeature
  , tertiaryDatum_ :: Maybe DatumFeature
  }

derive instance eqFeatureControlFrame :: Eq FeatureControlFrame

instance showFeatureControlFrame :: Show FeatureControlFrame where
  show (FeatureControlFrame f) =
    "|" <> characteristicSymbol f.characteristic 
    <> "|" <> show f.tolerance
    <> showDatum f.primaryDatum_
    <> showDatum f.secondaryDatum_
    <> showDatum f.tertiaryDatum_
    <> "|"
    where
      showDatum :: Maybe DatumFeature -> String
      showDatum Nothing = ""
      showDatum (Just d) = "|" <> show d

-- | Create feature control frame.
featureControlFrame 
  :: GeometricCharacteristic 
  -> ToleranceValue 
  -> Maybe MaterialCondition
  -> Maybe DatumFeature 
  -> Maybe DatumFeature 
  -> Maybe DatumFeature 
  -> FeatureControlFrame
featureControlFrame characteristic tolerance toleranceModifier primaryDatum_ secondaryDatum_ tertiaryDatum_ =
  FeatureControlFrame 
    { characteristic, tolerance, toleranceModifier
    , primaryDatum_, secondaryDatum_, tertiaryDatum_
    }

-- | Simple frame (form tolerance, no datums).
simpleFrame :: GeometricCharacteristic -> ToleranceValue -> FeatureControlFrame
simpleFrame char tol = 
  featureControlFrame char tol Nothing Nothing Nothing Nothing

-- | Frame with datums.
frameWithDatums 
  :: GeometricCharacteristic 
  -> ToleranceValue 
  -> DatumFeature 
  -> Maybe DatumFeature 
  -> Maybe DatumFeature 
  -> FeatureControlFrame
frameWithDatums char tol primary secondary tertiary =
  featureControlFrame char tol Nothing (Just primary) secondary tertiary

-- | Frame with tolerance modifier.
frameWithModifier
  :: GeometricCharacteristic 
  -> ToleranceValue 
  -> MaterialCondition
  -> DatumFeature
  -> FeatureControlFrame
frameWithModifier char tol modifier primary =
  featureControlFrame char tol (Just modifier) (Just primary) Nothing Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // bilateral // tolerance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bilateral tolerance (+-) for size dimensions.
data BilateralTolerance = BilateralTolerance
  { plus :: Number   -- Upper deviation
  , minus :: Number  -- Lower deviation (stored as positive)
  }

derive instance eqBilateralTolerance :: Eq BilateralTolerance

instance showBilateralTolerance :: Show BilateralTolerance where
  show (BilateralTolerance t) =
    "+" <> show t.plus <> "/-" <> show t.minus

-- | Symmetric bilateral tolerance (+-x).
symmetricTolerance :: Number -> BilateralTolerance
symmetricTolerance x = BilateralTolerance { plus: absNum x, minus: absNum x }

-- | Asymmetric bilateral tolerance (+x/-y).
asymmetricTolerance :: Number -> Number -> BilateralTolerance
asymmetricTolerance p m = 
  BilateralTolerance { plus: absNum p, minus: absNum m }

-- | Positive-only bilateral (+x/0).
plusTolerance :: Number -> BilateralTolerance
plusTolerance x = BilateralTolerance { plus: absNum x, minus: 0.0 }

-- | Negative-only bilateral (0/-x).
minusTolerance :: Number -> BilateralTolerance
minusTolerance x = BilateralTolerance { plus: 0.0, minus: absNum x }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // unilateral // tolerance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unilateral tolerance (one direction only).
data UnilateralTolerance
  = UnilateralPlus Number   -- +x only
  | UnilateralMinus Number  -- -x only

derive instance eqUnilateralTolerance :: Eq UnilateralTolerance

instance showUnilateralTolerance :: Show UnilateralTolerance where
  show (UnilateralPlus x) = "+" <> show x
  show (UnilateralMinus x) = "-" <> show x

-- | Unilateral plus tolerance.
unilateralPlus :: Number -> UnilateralTolerance
unilateralPlus = UnilateralPlus

-- | Unilateral minus tolerance.
unilateralMinus :: Number -> UnilateralTolerance
unilateralMinus = UnilateralMinus

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // limit // dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Limit dimension (upper and lower limits).
data LimitDimension = LimitDimension
  { upper :: Number
  , lower :: Number
  }

derive instance eqLimitDimension :: Eq LimitDimension

instance showLimitDimension :: Show LimitDimension where
  show (LimitDimension l) = show l.upper <> "/" <> show l.lower

-- | Create limit dimension.
limitDimension :: Number -> Number -> LimitDimension
limitDimension upper lower = 
  if upper >= lower
  then LimitDimension { upper, lower }
  else LimitDimension { upper: lower, lower: upper }

-- | Convert bilateral to limit.
limitFromBilateral :: Number -> BilateralTolerance -> LimitDimension
limitFromBilateral nominal (BilateralTolerance t) =
  LimitDimension 
    { upper: nominal + t.plus
    , lower: nominal - t.minus
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate worst-case tolerance stack-up.
-- |
-- | Simple RSS (Root Sum Square) for statistical tolerance.
toleranceStackUp :: Array ToleranceValue -> ToleranceValue
toleranceStackUp tolerances =
  let squares = map (\(ToleranceValue t) -> t * t) tolerances
      sumSquares = Array.foldl (+) 0.0 squares
      rss = sqrtApprox sumSquares
  in toleranceValue rss

-- Helper: absolute value
absNum :: Number -> Number
absNum n = if n < 0.0 then n * (-1.0) else n

-- Helper: approximate square root (Newton's method)
sqrtApprox :: Number -> Number
sqrtApprox n =
  if n < 0.0 then 0.0
  else iterate 10 (n / 2.0)
  where
    iterate :: Int -> Number -> Number
    iterate 0 x = x
    iterate i x = iterate (i - 1) ((x + n / x) / 2.0)
