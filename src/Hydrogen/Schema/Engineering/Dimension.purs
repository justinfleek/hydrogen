-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // engineering // dimension
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Engineering dimension primitives — dimension lines for technical drawings.
-- |
-- | ## What are Engineering Dimensions?
-- |
-- | Dimensions convey size and location information on technical drawings:
-- |
-- | - **Linear dimensions**: Length, width, height
-- | - **Angular dimensions**: Angles between features
-- | - **Radial dimensions**: Radii and diameters
-- | - **Ordinate dimensions**: Distances from datum
-- | - **Arc length dimensions**: Length along curves
-- |
-- | ## Standards
-- |
-- | - **ASME Y14.5**: US dimensioning standard
-- | - **ISO 129-1**: International dimensioning standard
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from submodules:
-- | - `Dimension.Types` — DimensionType, ArrowheadStyle, TextPosition
-- | - `Dimension.Value` — DimensionValue, DimensionText

module Hydrogen.Schema.Engineering.Dimension
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Engineering.Dimension.Types
  
  -- * Re-exports from Value
  , module Hydrogen.Schema.Engineering.Dimension.Value
  
  -- * Linear Dimension
  , LinearDimension(LinearDimension)
  , horizontalDimension
  , verticalDimension
  , alignedDimension
  , rotatedDimension
  
  -- * Angular Dimension
  , AngularDimension(AngularDimension)
  , angularDim
  , arcAngleDimension
  
  -- * Radial Dimension
  , RadialDimension(RadiusDim, DiameterDim, CenterMarkDim, CenterLineDim)
  , radiusDimension
  , diameter
  , centerMark
  , centerLine
  
  -- * Ordinate Dimension
  , OrdinateDimension(OrdinateDimension)
  , xOrdinate
  , yOrdinate
  
  -- * Chain Dimension
  , ChainDimension(ChainDim, BaselineDim)
  , chainDimension
  , baselineDimension
  
  -- * Dimension Style
  , DimensionStyle(DimensionStyle)
  , defaultStyle
  , isoStyle
  , asmeStyle
  
  -- * Operations
  , formatValue
  , totalChainLength
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<>)
  )

import Data.Array (foldl) as Array

-- Re-export all submodules
import Hydrogen.Schema.Engineering.Dimension.Types
  ( DimensionType(Linear, Angular, Radial, Diameter, ArcLength, Ordinate, Chain, Baseline)
  , allDimensionTypes
  , dimensionTypeDescription
  , ArrowheadStyle(FilledArrow, OpenArrow, ClosedArrow, Tick, Dot, OpenDot, ArchitecturalTick, Integral, NoArrow)
  , allArrowheadStyles
  , arrowheadDescription
  , TextPosition(TextAbove, TextCentered, TextBelow, TextInline, TextOutside)
  , allTextPositions
  )

import Hydrogen.Schema.Engineering.Dimension.Value
  ( DimensionValue(LinearValue, AngularValue, RadialValue, DiameterValue, ArcLengthValue)
  , linearDimension
  , angularDimension
  , radialDimension
  , diameterDimension
  , arcLengthDimension
  , DimensionText(BasicDimensionText, LimitDimensionText, ReferenceDimensionText, BasicBoxedText)
  , dimensionText
  , textWithTolerance
  , textWithLimits
  , referenceText
  , basicText
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // linear // dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear dimension with position and value.
data LinearDimension = LinearDimension
  { startX :: Number
  , startY :: Number
  , endX :: Number
  , endY :: Number
  , text :: DimensionText
  , textPosition :: TextPosition
  , offset :: Number  -- Distance from feature to dimension line
  }

derive instance eqLinearDimension :: Eq LinearDimension

instance showLinearDimension :: Show LinearDimension where
  show (LinearDimension d) = "LinearDimension " <> show d.text

-- | Create horizontal dimension.
horizontalDimension :: Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
horizontalDimension x1 y1 x2 y2 offset text =
  LinearDimension 
    { startX: x1, startY: y1, endX: x2, endY: y2
    , text, textPosition: TextAbove, offset
    }

-- | Create vertical dimension.
verticalDimension :: Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
verticalDimension x1 y1 x2 y2 offset text =
  LinearDimension 
    { startX: x1, startY: y1, endX: x2, endY: y2
    , text, textPosition: TextAbove, offset
    }

-- | Create aligned dimension (parallel to feature).
alignedDimension :: Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
alignedDimension x1 y1 x2 y2 offset text =
  LinearDimension 
    { startX: x1, startY: y1, endX: x2, endY: y2
    , text, textPosition: TextAbove, offset
    }

-- | Create rotated dimension (at specified angle).
rotatedDimension :: Number -> Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
rotatedDimension x1 y1 x2 y2 _angle offset text =
  LinearDimension 
    { startX: x1, startY: y1, endX: x2, endY: y2
    , text, textPosition: TextAbove, offset
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // angular // dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Angular dimension between two lines.
data AngularDimension = AngularDimension
  { vertexX :: Number
  , vertexY :: Number
  , startAngle :: Number  -- Degrees
  , endAngle :: Number    -- Degrees
  , radius :: Number      -- Arc radius for dimension line
  , text :: DimensionText
  }

derive instance eqAngularDimension :: Eq AngularDimension

instance showAngularDimension :: Show AngularDimension where
  show (AngularDimension d) = "AngularDimension " <> show d.text

-- | Create angular dimension.
angularDim :: Number -> Number -> Number -> Number -> Number -> DimensionText -> AngularDimension
angularDim vertexX vertexY startAngle endAngle radius text =
  AngularDimension { vertexX, vertexY, startAngle, endAngle, radius, text }

-- | Create arc angle dimension.
arcAngleDimension :: Number -> Number -> Number -> Number -> Number -> AngularDimension
arcAngleDimension cx cy startDeg endDeg r =
  let angle = if endDeg < startDeg then endDeg - startDeg + 360.0 else endDeg - startDeg
  in AngularDimension 
       { vertexX: cx, vertexY: cy
       , startAngle: startDeg, endAngle: endDeg
       , radius: r
       , text: dimensionText (angularDimension angle)
       }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // radial // dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radial dimension for circles and arcs.
data RadialDimension
  = RadiusDim
      { centerX :: Number
      , centerY :: Number
      , radius_ :: Number
      , leaderAngle :: Number
      , text :: DimensionText
      }
  | DiameterDim
      { centerX :: Number
      , centerY :: Number
      , diameter_ :: Number
      , angle :: Number
      , text :: DimensionText
      }
  | CenterMarkDim
      { centerX :: Number
      , centerY :: Number
      , markSize :: Number
      }
  | CenterLineDim
      { centerX :: Number
      , centerY :: Number
      , radius_ :: Number
      , startAngle :: Number
      , endAngle :: Number
      }

derive instance eqRadialDimension :: Eq RadialDimension

instance showRadialDimension :: Show RadialDimension where
  show (RadiusDim d) = "Radius " <> show d.text
  show (DiameterDim d) = "Diameter " <> show d.text
  show (CenterMarkDim _) = "CenterMark"
  show (CenterLineDim _) = "CenterLine"

-- | Create radius dimension.
radiusDimension :: Number -> Number -> Number -> Number -> RadialDimension
radiusDimension cx cy r angle =
  RadiusDim 
    { centerX: cx, centerY: cy, radius_: r
    , leaderAngle: angle
    , text: dimensionText (radialDimension r)
    }

-- | Create diameter dimension.
diameter :: Number -> Number -> Number -> Number -> RadialDimension
diameter cx cy d angle =
  DiameterDim 
    { centerX: cx, centerY: cy, diameter_: d, angle
    , text: dimensionText (diameterDimension d)
    }

-- | Create center mark.
centerMark :: Number -> Number -> Number -> RadialDimension
centerMark cx cy size = CenterMarkDim { centerX: cx, centerY: cy, markSize: size }

-- | Create center line.
centerLine :: Number -> Number -> Number -> Number -> Number -> RadialDimension
centerLine cx cy r startAngle endAngle =
  CenterLineDim { centerX: cx, centerY: cy, radius_: r, startAngle, endAngle }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // ordinate // dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ordinate dimension (distance from datum).
data OrdinateDimension = OrdinateDimension
  { originX :: Number
  , originY :: Number
  , pointX :: Number
  , pointY :: Number
  , isXDimension :: Boolean
  , text :: DimensionText
  }

derive instance eqOrdinateDimension :: Eq OrdinateDimension

instance showOrdinateDimension :: Show OrdinateDimension where
  show (OrdinateDimension d) = 
    (if d.isXDimension then "X" else "Y") <> " Ordinate " <> show d.text

-- | Create X ordinate dimension.
xOrdinate :: Number -> Number -> Number -> Number -> OrdinateDimension
xOrdinate originX originY pointX pointY =
  let dist = absNum (pointX - originX)
  in OrdinateDimension 
       { originX, originY, pointX, pointY
       , isXDimension: true
       , text: dimensionText (linearDimension dist)
       }

-- | Create Y ordinate dimension.
yOrdinate :: Number -> Number -> Number -> Number -> OrdinateDimension
yOrdinate originX originY pointX pointY =
  let dist = absNum (pointY - originY)
  in OrdinateDimension 
       { originX, originY, pointX, pointY
       , isXDimension: false
       , text: dimensionText (linearDimension dist)
       }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // chain // dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chain or baseline dimension group.
data ChainDimension
  = ChainDim { dimensions :: Array LinearDimension }
  | BaselineDim
      { baselineX :: Number
      , baselineY :: Number
      , dimensions :: Array LinearDimension
      }

derive instance eqChainDimension :: Eq ChainDimension

instance showChainDimension :: Show ChainDimension where
  show (ChainDim d) = "ChainDimension [" <> show (arrayLength d.dimensions) <> " dims]"
  show (BaselineDim d) = "BaselineDimension [" <> show (arrayLength d.dimensions) <> " dims]"

-- | Create chain dimension.
chainDimension :: Array LinearDimension -> ChainDimension
chainDimension dimensions = ChainDim { dimensions }

-- | Create baseline dimension.
baselineDimension :: Number -> Number -> Array LinearDimension -> ChainDimension
baselineDimension baselineX baselineY dimensions =
  BaselineDim { baselineX, baselineY, dimensions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dimension // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dimension style settings.
data DimensionStyle = DimensionStyle
  { arrowhead :: ArrowheadStyle
  , arrowSize :: Number
  , textHeight :: Number
  , extensionOffset :: Number
  , extensionExtend :: Number
  , textGap :: Number
  , decimalPlaces :: Int
  , suppressLeadingZero :: Boolean
  , suppressTrailingZero :: Boolean
  }

derive instance eqDimensionStyle :: Eq DimensionStyle

instance showDimensionStyle :: Show DimensionStyle where
  show _ = "DimensionStyle"

-- | Default dimension style.
defaultStyle :: DimensionStyle
defaultStyle = DimensionStyle
  { arrowhead: FilledArrow
  , arrowSize: 2.5
  , textHeight: 3.5
  , extensionOffset: 1.5
  , extensionExtend: 2.0
  , textGap: 1.0
  , decimalPlaces: 2
  , suppressLeadingZero: false
  , suppressTrailingZero: true
  }

-- | ISO standard style.
isoStyle :: DimensionStyle
isoStyle = DimensionStyle
  { arrowhead: FilledArrow
  , arrowSize: 2.5
  , textHeight: 3.5
  , extensionOffset: 2.0
  , extensionExtend: 2.0
  , textGap: 0.0
  , decimalPlaces: 2
  , suppressLeadingZero: false
  , suppressTrailingZero: false
  }

-- | ASME standard style.
asmeStyle :: DimensionStyle
asmeStyle = DimensionStyle
  { arrowhead: FilledArrow
  , arrowSize: 3.0
  , textHeight: 3.0
  , extensionOffset: 1.5
  , extensionExtend: 3.0
  , textGap: 1.5
  , decimalPlaces: 3
  , suppressLeadingZero: true
  , suppressTrailingZero: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format dimension value with style settings.
formatValue :: DimensionStyle -> DimensionValue -> String
formatValue _style value =
  case value of
    LinearValue v -> show v <> " mm"
    AngularValue v -> show v <> " deg"
    RadialValue v -> "R" <> show v
    DiameterValue v -> "D" <> show v
    ArcLengthValue v -> "Arc " <> show v

-- | Calculate total length of chain dimension.
totalChainLength :: ChainDimension -> Number
totalChainLength (ChainDim d) =
  Array.foldl addDimLength 0.0 d.dimensions
totalChainLength (BaselineDim d) =
  Array.foldl maxDimLength 0.0 d.dimensions

-- Helper: add dimension length
addDimLength :: Number -> LinearDimension -> Number
addDimLength acc (LinearDimension d) =
  let dx = d.endX - d.startX
      dy = d.endY - d.startY
      len = sqrtApprox (dx * dx + dy * dy)
  in acc + len

-- Helper: max dimension length
maxDimLength :: Number -> LinearDimension -> Number
maxDimLength acc (LinearDimension d) =
  let dx = d.endX - d.startX
      dy = d.endY - d.startY
      len = sqrtApprox (dx * dx + dy * dy)
  in if len < acc then acc else len

-- Helper: array length
arrayLength :: forall a. Array a -> Int
arrayLength arr = Array.foldl (\acc _ -> acc + 1) 0 arr

-- Helper: absolute value
absNum :: Number -> Number
absNum n = if n < 0.0 then n * (0.0 - 1.0) else n

-- Helper: approximate square root
sqrtApprox :: Number -> Number
sqrtApprox n =
  if n < 0.0 then 0.0
  else iterate 10 (n / 2.0)
  where
    iterate :: Int -> Number -> Number
    iterate 0 x = x
    iterate i x = iterate (i - 1) ((x + n / x) / 2.0)
