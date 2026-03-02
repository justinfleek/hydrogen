-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brush // tip // parameters
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Tip Parameters — Bounded numeric parameters for brush tips.
-- |
-- | ## Design Philosophy
-- |
-- | All brush tip parameters are bounded values that clamp or wrap at their
-- | limits. This ensures deterministic behavior at all scales.
-- |
-- | ## Key Properties
-- |
-- | - **Diameter**: Size in pixels (1-5000)
-- | - **Hardness**: Edge falloff (0% = soft gaussian, 100% = hard circle)
-- | - **Roundness**: Ellipse ratio (100% = circle, 1% = line)
-- | - **Angle**: Rotation of ellipse (0-360°, wraps)
-- | - **Spacing**: Distance between dabs as % of diameter (1-1000%)
-- | - **FlipX/FlipY**: Axis mirroring for asymmetric tips
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Tip.Parameters
  ( -- * Diameter (1-5000 pixels)
    Diameter(Diameter)
  , diameter
  , diameterBounds
  , unwrapDiameter
  , minDiameter
  , maxDiameter
  , defaultDiameter
  
  -- * Hardness (0-100%)
  , Hardness(Hardness)
  , hardness
  , hardnessBounds
  , unwrapHardness
  , softHardness
  , mediumHardness
  , hardHardness
  , maxHardness
  
  -- * Roundness (1-100%)
  , Roundness(Roundness)
  , roundness
  , roundnessBounds
  , unwrapRoundness
  , circularRoundness
  , ellipticalRoundness
  , flatRoundness
  
  -- * Tip Angle (0-360°)
  , TipAngle(TipAngle)
  , tipAngle
  , tipAngleBounds
  , unwrapTipAngle
  , horizontalAngle
  , verticalAngle
  , diagonalAngle
  
  -- * Spacing (1-1000%)
  , Spacing(Spacing)
  , spacing
  , spacingBounds
  , unwrapSpacing
  , minSpacing
  , defaultSpacing
  , wideSpacing
  , airbrushSpacing
  
  -- * Flip Axes
  , FlipX(FlipX)
  , FlipY(FlipY)
  , flipX
  , flipY
  , noFlipX
  , noFlipY
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // diameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brush diameter in pixels (1-5000).
-- | This is the maximum extent of a single dab.
newtype Diameter = Diameter Number

derive instance eqDiameter :: Eq Diameter
derive instance ordDiameter :: Ord Diameter

instance showDiameter :: Show Diameter where
  show (Diameter d) = "Diameter " <> show d <> "px"

-- | Bounded specification for diameter.
diameterBounds :: Bounded.NumberBounds
diameterBounds = Bounded.numberBounds 1.0 5000.0 Bounded.Clamps 
  "diameter" "Brush diameter in pixels (1-5000)"

-- | Create a diameter value (clamped to 1-5000).
diameter :: Number -> Diameter
diameter n = Diameter (Bounded.clampNumber 1.0 5000.0 n)

-- | Extract the raw diameter value.
unwrapDiameter :: Diameter -> Number
unwrapDiameter (Diameter d) = d

-- | Minimum brush diameter (1px).
minDiameter :: Diameter
minDiameter = Diameter 1.0

-- | Maximum brush diameter (5000px).
maxDiameter :: Diameter
maxDiameter = Diameter 5000.0

-- | Default brush diameter (24px).
defaultDiameter :: Diameter
defaultDiameter = Diameter 24.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // hardness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brush hardness (0-100%).
-- | 0% = soft gaussian falloff, 100% = hard circle edge.
newtype Hardness = Hardness Number

derive instance eqHardness :: Eq Hardness
derive instance ordHardness :: Ord Hardness

instance showHardness :: Show Hardness where
  show (Hardness h) = "Hardness " <> show h <> "%"

-- | Bounded specification for hardness.
hardnessBounds :: Bounded.NumberBounds
hardnessBounds = Bounded.numberBounds 0.0 100.0 Bounded.Clamps
  "hardness" "Brush edge hardness percentage (0-100)"

-- | Create a hardness value (clamped to 0-100).
hardness :: Number -> Hardness
hardness n = Hardness (Bounded.clampNumber 0.0 100.0 n)

-- | Extract the raw hardness value.
unwrapHardness :: Hardness -> Number
unwrapHardness (Hardness h) = h

-- | Soft airbrush edge (0%).
softHardness :: Hardness
softHardness = Hardness 0.0

-- | Medium hardness (50%).
mediumHardness :: Hardness
mediumHardness = Hardness 50.0

-- | Hard but not crisp (85%).
hardHardness :: Hardness
hardHardness = Hardness 85.0

-- | Maximum hardness, crisp edge (100%).
maxHardness :: Hardness
maxHardness = Hardness 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // roundness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brush roundness (1-100%).
-- | 100% = perfect circle, lower values create ellipses.
newtype Roundness = Roundness Number

derive instance eqRoundness :: Eq Roundness
derive instance ordRoundness :: Ord Roundness

instance showRoundness :: Show Roundness where
  show (Roundness r) = "Roundness " <> show r <> "%"

-- | Bounded specification for roundness.
roundnessBounds :: Bounded.NumberBounds
roundnessBounds = Bounded.numberBounds 1.0 100.0 Bounded.Clamps
  "roundness" "Brush ellipse ratio percentage (1-100)"

-- | Create a roundness value (clamped to 1-100).
roundness :: Number -> Roundness
roundness n = Roundness (Bounded.clampNumber 1.0 100.0 n)

-- | Extract the raw roundness value.
unwrapRoundness :: Roundness -> Number
unwrapRoundness (Roundness r) = r

-- | Perfect circle (100%).
circularRoundness :: Roundness
circularRoundness = Roundness 100.0

-- | Moderate ellipse (50%).
ellipticalRoundness :: Roundness
ellipticalRoundness = Roundness 50.0

-- | Nearly flat line (10%).
flatRoundness :: Roundness
flatRoundness = Roundness 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tip angle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brush tip rotation angle (0-360°).
-- | Rotates the ellipse or flat brush shape.
newtype TipAngle = TipAngle Number

derive instance eqTipAngle :: Eq TipAngle
derive instance ordTipAngle :: Ord TipAngle

instance showTipAngle :: Show TipAngle where
  show (TipAngle a) = "TipAngle " <> show a <> "°"

-- | Bounded specification for tip angle.
tipAngleBounds :: Bounded.NumberBounds
tipAngleBounds = Bounded.numberBounds 0.0 360.0 Bounded.Wraps
  "tipAngle" "Brush tip rotation angle in degrees (0-360)"

-- | Create a tip angle value (wraps at 360).
tipAngle :: Number -> TipAngle
tipAngle n = TipAngle (Bounded.wrapNumber 0.0 360.0 n)

-- | Extract the raw angle value.
unwrapTipAngle :: TipAngle -> Number
unwrapTipAngle (TipAngle a) = a

-- | Horizontal orientation (0°).
horizontalAngle :: TipAngle
horizontalAngle = TipAngle 0.0

-- | Vertical orientation (90°).
verticalAngle :: TipAngle
verticalAngle = TipAngle 90.0

-- | Diagonal orientation (45°).
diagonalAngle :: TipAngle
diagonalAngle = TipAngle 45.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dab spacing as percentage of diameter (1-1000%).
-- | Lower = denser stroke, higher = more separated dabs.
newtype Spacing = Spacing Number

derive instance eqSpacing :: Eq Spacing
derive instance ordSpacing :: Ord Spacing

instance showSpacing :: Show Spacing where
  show (Spacing s) = "Spacing " <> show s <> "%"

-- | Bounded specification for spacing.
spacingBounds :: Bounded.NumberBounds
spacingBounds = Bounded.numberBounds 1.0 1000.0 Bounded.Clamps
  "spacing" "Dab spacing as percentage of diameter (1-1000)"

-- | Create a spacing value (clamped to 1-1000).
spacing :: Number -> Spacing
spacing n = Spacing (Bounded.clampNumber 1.0 1000.0 n)

-- | Extract the raw spacing value.
unwrapSpacing :: Spacing -> Number
unwrapSpacing (Spacing s) = s

-- | Minimum spacing (1% = very dense, nearly continuous).
minSpacing :: Spacing
minSpacing = Spacing 1.0

-- | Default brush spacing (25%).
defaultSpacing :: Spacing
defaultSpacing = Spacing 25.0

-- | Wide spacing for texture effects (100%).
wideSpacing :: Spacing
wideSpacing = Spacing 100.0

-- | Airbrush-style dense spacing (5%).
airbrushSpacing :: Spacing
airbrushSpacing = Spacing 5.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // flip axes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal flip of the brush tip.
newtype FlipX = FlipX Boolean

derive instance eqFlipX :: Eq FlipX
derive instance ordFlipX :: Ord FlipX

instance showFlipX :: Show FlipX where
  show (FlipX true) = "FlipX"
  show (FlipX false) = "NoFlipX"

-- | Vertical flip of the brush tip.
newtype FlipY = FlipY Boolean

derive instance eqFlipY :: Eq FlipY
derive instance ordFlipY :: Ord FlipY

instance showFlipY :: Show FlipY where
  show (FlipY true) = "FlipY"
  show (FlipY false) = "NoFlipY"

-- | Enable horizontal flip.
flipX :: FlipX
flipX = FlipX true

-- | Enable vertical flip.
flipY :: FlipY
flipY = FlipY true

-- | No horizontal flip (default).
noFlipX :: FlipX
noFlipX = FlipX false

-- | No vertical flip (default).
noFlipY :: FlipY
noFlipY = FlipY false
