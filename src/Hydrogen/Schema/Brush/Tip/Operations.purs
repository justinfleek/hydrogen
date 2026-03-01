-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brush // tip // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Tip Operations — Accessors, modifiers, and queries for brush tips.
-- |
-- | ## Design Philosophy
-- |
-- | Pure functions for inspecting and transforming BrushTip values. These
-- | operations enable compositional brush tip manipulation without mutation.
-- |
-- | ## Categories
-- |
-- | - **Accessors**: Extract individual parameters from a BrushTip
-- | - **Modifiers**: Return new BrushTip with updated parameters
-- | - **Queries**: Predicate functions for classification
-- |
-- | ## Dependencies
-- |
-- | - Prelude (comparison operators)
-- | - Tip.Types (TipShape)
-- | - Tip.Parameters (parameter types and unwrap functions)
-- | - Tip.Compound (BrushTip type)

module Hydrogen.Schema.Brush.Tip.Operations
  ( -- * Accessors
    tipShape
  , tipDiameter
  , tipHardness
  , tipRoundness
  , tipAngleValue
  , tipSpacing
  , tipFlipX
  , tipFlipY
  
  -- * Modifiers
  , withDiameter
  , withHardness
  , withRoundness
  , withAngle
  , withSpacing
  , withFlipX
  , withFlipY
  
  -- * Queries
  , isHardEdge
  , isSoftEdge
  , isMediumEdge
  , isCircular
  , isElliptical
  , isDense
  , isSparse
  , dabsPerDiameter
  , isFineDetail
  , isBroadCoverage
  , hasSignificantAngle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (>=)
  , (<=)
  , (>)
  , (<)
  , (&&)
  , (||)
  , (/)
  )

import Hydrogen.Schema.Brush.Tip.Types
  ( TipShape
  )

import Hydrogen.Schema.Brush.Tip.Parameters
  ( Diameter
  , Hardness
  , Roundness
  , TipAngle
  , Spacing
  , FlipX
  , FlipY
  , unwrapDiameter
  , unwrapHardness
  , unwrapRoundness
  , unwrapTipAngle
  , unwrapSpacing
  )

import Hydrogen.Schema.Brush.Tip.Compound
  ( BrushTip
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the tip shape.
tipShape :: BrushTip -> TipShape
tipShape t = t.shape

-- | Get the diameter.
tipDiameter :: BrushTip -> Diameter
tipDiameter t = t.diameter

-- | Get the hardness.
tipHardness :: BrushTip -> Hardness
tipHardness t = t.hardness

-- | Get the roundness.
tipRoundness :: BrushTip -> Roundness
tipRoundness t = t.roundness

-- | Get the angle.
tipAngleValue :: BrushTip -> TipAngle
tipAngleValue t = t.angle

-- | Get the spacing.
tipSpacing :: BrushTip -> Spacing
tipSpacing t = t.spacing

-- | Get the horizontal flip.
tipFlipX :: BrushTip -> FlipX
tipFlipX t = t.flipX

-- | Get the vertical flip.
tipFlipY :: BrushTip -> FlipY
tipFlipY t = t.flipY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the diameter.
withDiameter :: Diameter -> BrushTip -> BrushTip
withDiameter d t = t { diameter = d }

-- | Set the hardness.
withHardness :: Hardness -> BrushTip -> BrushTip
withHardness h t = t { hardness = h }

-- | Set the roundness.
withRoundness :: Roundness -> BrushTip -> BrushTip
withRoundness r t = t { roundness = r }

-- | Set the angle.
withAngle :: TipAngle -> BrushTip -> BrushTip
withAngle a t = t { angle = a }

-- | Set the spacing.
withSpacing :: Spacing -> BrushTip -> BrushTip
withSpacing s t = t { spacing = s }

-- | Set horizontal flip.
withFlipX :: FlipX -> BrushTip -> BrushTip
withFlipX fx t = t { flipX = fx }

-- | Set vertical flip.
withFlipY :: FlipY -> BrushTip -> BrushTip
withFlipY fy t = t { flipY = fy }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this a hard-edged brush (hardness >= 80%)?
isHardEdge :: BrushTip -> Boolean
isHardEdge t = unwrapHardness t.hardness >= 80.0

-- | Is this a soft-edged brush (hardness <= 30%)?
isSoftEdge :: BrushTip -> Boolean
isSoftEdge t = unwrapHardness t.hardness <= 30.0

-- | Is this a medium-hardness brush (between 30% and 80%)?
isMediumEdge :: BrushTip -> Boolean
isMediumEdge t = 
  let h = unwrapHardness t.hardness
  in h > 30.0 && h < 80.0

-- | Is the brush circular (roundness >= 95%)?
isCircular :: BrushTip -> Boolean
isCircular t = unwrapRoundness t.roundness >= 95.0

-- | Is the brush elliptical (roundness < 95%)?
isElliptical :: BrushTip -> Boolean
isElliptical t = unwrapRoundness t.roundness < 95.0

-- | Is the spacing dense (spacing <= 25%)?
isDense :: BrushTip -> Boolean
isDense t = unwrapSpacing t.spacing <= 25.0

-- | Is the spacing sparse (spacing >= 100%)?
isSparse :: BrushTip -> Boolean
isSparse t = unwrapSpacing t.spacing >= 100.0

-- | Calculate how many dabs fit per brush diameter at current spacing.
dabsPerDiameter :: BrushTip -> Number
dabsPerDiameter t = 100.0 / unwrapSpacing t.spacing

-- | Is this brush suitable for fine detail work?
-- | Fine detail = small diameter AND hard edge AND dense spacing.
isFineDetail :: BrushTip -> Boolean
isFineDetail t =
  unwrapDiameter t.diameter <= 10.0 &&
  isHardEdge t &&
  isDense t

-- | Is this brush suitable for broad coverage?
-- | Broad coverage = large diameter OR soft edge OR sparse spacing.
isBroadCoverage :: BrushTip -> Boolean
isBroadCoverage t =
  unwrapDiameter t.diameter > 100.0 ||
  isSoftEdge t ||
  isSparse t

-- | Is the tip angle significant (not near horizontal)?
hasSignificantAngle :: BrushTip -> Boolean
hasSignificantAngle t =
  let a = unwrapTipAngle t.angle
  in a > 15.0 && a < 345.0
