-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // engineering // dimension // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Engineering dimension type enumerations.
-- |
-- | Types of dimensions, arrowhead styles, and text positions for
-- | technical drawings per ASME Y14.5 and ISO 129-1.

module Hydrogen.Schema.Engineering.Dimension.Types
  ( -- * Dimension Type
    DimensionType(Linear, Angular, Radial, Diameter, ArcLength, Ordinate, Chain, Baseline)
  , allDimensionTypes
  , dimensionTypeDescription
  
  -- * Arrowhead Style
  , ArrowheadStyle(FilledArrow, OpenArrow, ClosedArrow, Tick, Dot, OpenDot, ArchitecturalTick, Integral, NoArrow)
  , allArrowheadStyles
  , arrowheadDescription
  
  -- * Text Position
  , TextPosition(TextAbove, TextCentered, TextBelow, TextInline, TextOutside)
  , allTextPositions
  ) where

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // dimension // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of engineering dimensions.
data DimensionType
  = Linear      -- ^ Straight-line distance
  | Angular     -- ^ Angle measurement
  | Radial      -- ^ Radius dimension (R)
  | Diameter    -- ^ Diameter dimension
  | ArcLength   -- ^ Length along arc
  | Ordinate    -- ^ Distance from datum (X or Y)
  | Chain       -- ^ Connected series of dimensions
  | Baseline    -- ^ Multiple dimensions from common baseline

derive instance eqDimensionType :: Eq DimensionType

instance showDimensionType :: Show DimensionType where
  show Linear = "Linear"
  show Angular = "Angular"
  show Radial = "Radial"
  show Diameter = "Diameter"
  show ArcLength = "ArcLength"
  show Ordinate = "Ordinate"
  show Chain = "Chain"
  show Baseline = "Baseline"

-- | All dimension types for enumeration.
allDimensionTypes :: Array DimensionType
allDimensionTypes = 
  [Linear, Angular, Radial, Diameter, ArcLength, Ordinate, Chain, Baseline]

-- | Description of dimension type.
dimensionTypeDescription :: DimensionType -> String
dimensionTypeDescription Linear = "Straight-line distance between two points"
dimensionTypeDescription Angular = "Angle between two lines or surfaces"
dimensionTypeDescription Radial = "Radius of arc or circle (R prefix)"
dimensionTypeDescription Diameter = "Diameter of circle or cylinder"
dimensionTypeDescription ArcLength = "Length measured along an arc"
dimensionTypeDescription Ordinate = "Distance from a datum in X or Y direction"
dimensionTypeDescription Chain = "Series of connected dimensions end-to-end"
dimensionTypeDescription Baseline = "Multiple dimensions sharing a common origin"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // arrowhead // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arrowhead (terminator) styles for dimension lines.
data ArrowheadStyle
  = FilledArrow     -- ^ Solid filled triangle (most common)
  | OpenArrow       -- ^ Open triangle outline
  | ClosedArrow     -- ^ Closed but not filled
  | Tick            -- ^ 45 degree tick mark
  | Dot             -- ^ Filled circle
  | OpenDot         -- ^ Open circle
  | ArchitecturalTick -- ^ Diagonal line (architectural drawings)
  | Integral        -- ^ Loop/integral symbol
  | NoArrow         -- ^ No terminator

derive instance eqArrowheadStyle :: Eq ArrowheadStyle

instance showArrowheadStyle :: Show ArrowheadStyle where
  show FilledArrow = "FilledArrow"
  show OpenArrow = "OpenArrow"
  show ClosedArrow = "ClosedArrow"
  show Tick = "Tick"
  show Dot = "Dot"
  show OpenDot = "OpenDot"
  show ArchitecturalTick = "ArchitecturalTick"
  show Integral = "Integral"
  show NoArrow = "None"

-- | All arrowhead styles for enumeration.
allArrowheadStyles :: Array ArrowheadStyle
allArrowheadStyles = 
  [FilledArrow, OpenArrow, ClosedArrow, Tick, Dot, OpenDot, ArchitecturalTick, Integral, NoArrow]

-- | Description of arrowhead style.
arrowheadDescription :: ArrowheadStyle -> String
arrowheadDescription FilledArrow = "Solid filled triangular arrow"
arrowheadDescription OpenArrow = "Open triangular arrow outline"
arrowheadDescription ClosedArrow = "Closed triangle, not filled"
arrowheadDescription Tick = "45-degree tick mark"
arrowheadDescription Dot = "Filled circular dot"
arrowheadDescription OpenDot = "Open circular dot"
arrowheadDescription ArchitecturalTick = "Diagonal tick (architectural standard)"
arrowheadDescription Integral = "Loop or integral symbol"
arrowheadDescription NoArrow = "No terminator"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // text // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of dimension text relative to dimension line.
data TextPosition
  = TextAbove      -- ^ Text above dimension line
  | TextCentered   -- ^ Text breaks dimension line (ISO standard)
  | TextBelow      -- ^ Text below dimension line
  | TextInline     -- ^ Text inline with extension lines
  | TextOutside    -- ^ Text outside dimension (small spaces)

derive instance eqTextPosition :: Eq TextPosition

instance showTextPosition :: Show TextPosition where
  show TextAbove = "Above"
  show TextCentered = "Centered"
  show TextBelow = "Below"
  show TextInline = "Inline"
  show TextOutside = "Outside"

-- | All text positions for enumeration.
allTextPositions :: Array TextPosition
allTextPositions = [TextAbove, TextCentered, TextBelow, TextInline, TextOutside]
