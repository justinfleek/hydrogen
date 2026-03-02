-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // engineering // dimension // value
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dimension values and text formatting.
-- |
-- | Dimension values capture the numeric measurement with type-specific
-- | prefixes (R for radius, diameter symbol for diameter, etc.).
-- |
-- | Dimension text combines values with optional tolerances or limits.

module Hydrogen.Schema.Engineering.Dimension.Value
  ( -- * Dimension Value
    DimensionValue(LinearValue, AngularValue, RadialValue, DiameterValue, ArcLengthValue)
  , linearDimension
  , angularDimension
  , radialDimension
  , diameterDimension
  , arcLengthDimension
  
  -- * Dimension Text
  , DimensionText(BasicDimensionText, LimitDimensionText, ReferenceDimensionText, BasicBoxedText)
  , dimensionText
  , textWithTolerance
  , textWithLimits
  , referenceText
  , basicText
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Engineering.Tolerance (BilateralTolerance, LimitDimension)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dimension // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dimension value with type-specific data.
data DimensionValue
  = LinearValue Number        -- ^ Linear distance in mm
  | AngularValue Number       -- ^ Angle in degrees
  | RadialValue Number        -- ^ Radius in mm
  | DiameterValue Number      -- ^ Diameter in mm
  | ArcLengthValue Number     -- ^ Arc length in mm

derive instance eqDimensionValue :: Eq DimensionValue

instance showDimensionValue :: Show DimensionValue where
  show (LinearValue v) = show v <> " mm"
  show (AngularValue v) = show v <> " deg"
  show (RadialValue v) = "R" <> show v
  show (DiameterValue v) = "D" <> show v
  show (ArcLengthValue v) = "Arc " <> show v

-- | Create linear dimension value.
linearDimension :: Number -> DimensionValue
linearDimension = LinearValue

-- | Create angular dimension value.
angularDimension :: Number -> DimensionValue
angularDimension = AngularValue

-- | Create radial dimension value.
radialDimension :: Number -> DimensionValue
radialDimension = RadialValue

-- | Create diameter dimension value.
diameterDimension :: Number -> DimensionValue
diameterDimension = DiameterValue

-- | Create arc length dimension value.
arcLengthDimension :: Number -> DimensionValue
arcLengthDimension = ArcLengthValue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // dimension // text
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dimension text with optional tolerance/modifiers.
data DimensionText
  = BasicDimensionText
      { value :: DimensionValue
      , tolerance :: Maybe BilateralTolerance
      }
  | LimitDimensionText
      { limits :: LimitDimension
      }
  | ReferenceDimensionText
      { value :: DimensionValue  -- Enclosed in parentheses
      }
  | BasicBoxedText
      { value :: DimensionValue  -- Enclosed in box (basic dimension)
      }

derive instance eqDimensionText :: Eq DimensionText

instance showDimensionText :: Show DimensionText where
  show (BasicDimensionText d) = 
    show d.value <> case d.tolerance of
      Nothing -> ""
      Just t -> " " <> show t
  show (LimitDimensionText d) = show d.limits
  show (ReferenceDimensionText d) = "(" <> show d.value <> ")"
  show (BasicBoxedText d) = "[" <> show d.value <> "]"

-- | Create basic dimension text.
dimensionText :: DimensionValue -> DimensionText
dimensionText value = BasicDimensionText { value, tolerance: Nothing }

-- | Create dimension text with tolerance.
textWithTolerance :: DimensionValue -> BilateralTolerance -> DimensionText
textWithTolerance value tol = 
  BasicDimensionText { value, tolerance: Just tol }

-- | Create limit dimension text.
textWithLimits :: LimitDimension -> DimensionText
textWithLimits limits = LimitDimensionText { limits }

-- | Create reference dimension (parenthesized).
referenceText :: DimensionValue -> DimensionText
referenceText value = ReferenceDimensionText { value }

-- | Create basic (boxed) dimension.
basicText :: DimensionValue -> DimensionText
basicText value = BasicBoxedText { value }
