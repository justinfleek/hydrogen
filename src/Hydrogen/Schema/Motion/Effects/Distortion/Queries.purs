-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--           // hydrogen // schema // motion // effects // distortion // queries
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion Queries — Query and utility functions for distortion effects.
-- |
-- | ## Functions Included
-- |
-- | - Effect name functions
-- | - Effect description functions
-- | - Query predicates
-- | - Advanced utility functions

module Hydrogen.Schema.Motion.Effects.Distortion.Queries
  ( -- * Effect Names
    warpEffectName
  , displacementMapEffectName
  , bezierWarpEffectName
  , bulgeEffectName
  , cornerPinEffectName
  , liquifyEffectName
  , mirrorEffectName
  , offsetEffectName
  , opticsCompensationEffectName
  , polarCoordinatesEffectName
  , rippleEffectName
  , spherizeEffectName
  , transformEffectName
  , turbulentDisplaceEffectName
  , twirlEffectName
  , waveWarpEffectName
  , ccBendItEffectName
  , ccBlobbylizeEffectName
  , ccFloMotionEffectName
  , ccGriddlerEffectName
  , ccLensEffectName
  , ccPageTurnEffectName
  , ccPowerPinEffectName
  , ccRipplePulseEffectName
  , ccSlantEffectName
  , ccSmearEffectName
  , ccSplitEffectName
  , ccTilerEffectName
  
  -- * Effect Descriptions
  , describeWarp
  , describeDisplacementMap
  , describeBulge
  , describeTwirl
  , describeWaveWarp
  , describeTurbulentDisplace
  
  -- * Queries
  , isWarpBent
  , isDisplacementActive
  , hasBulgeHeight
  , isTwirlSignificant
  , isWaveWarpAnimated
  , isTurbulentDisplaceComplex
  
  -- * Advanced Utilities
  , scaleWarpBend
  , combineBulgeHeights
  , totalDisplacementMagnitude
  , waveWarpIntensity
  , isBulgeExpanding
  , twirlRevolutions
  , offsetTwirlAngle
  , scaleTurbulentAmount
  , displacementDifference
  , classifyWarpIntensity
  , hasTransformChange
  , hasWarpBothDistortions
  ) where

import Prelude
  ( ($)
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Distortion.Warp
  ( WarpEffect
  , BezierWarpEffect
  , BulgeEffect
  , TwirlEffect
  , WaveWarpEffect
  , RippleEffect
  , SpherizeEffect
  , LiquifyEffect
  )
import Hydrogen.Schema.Motion.Effects.Distortion.Displacement
  ( DisplacementMapEffect
  , TurbulentDisplaceEffect
  )
import Hydrogen.Schema.Motion.Effects.Distortion.Transform
  ( CornerPinEffect
  , MirrorEffect
  , OffsetEffect
  , OpticsCompensationEffect
  , PolarCoordinatesEffect
  , TransformEffect
  )
import Hydrogen.Schema.Motion.Effects.Distortion.CC
  ( CCBendItEffect
  , CCBlobbylizeEffect
  , CCFloMotionEffect
  , CCGriddlerEffect
  , CCLensEffect
  , CCPageTurnEffect
  , CCPowerPinEffect
  , CCRipplePulseEffect
  , CCSlantEffect
  , CCSmearEffect
  , CCSplitEffect
  , CCTilerEffect
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

warpEffectName :: WarpEffect -> String
warpEffectName _ = "Warp"

displacementMapEffectName :: DisplacementMapEffect -> String
displacementMapEffectName _ = "Displacement Map"

bezierWarpEffectName :: BezierWarpEffect -> String
bezierWarpEffectName _ = "Bezier Warp"

bulgeEffectName :: BulgeEffect -> String
bulgeEffectName _ = "Bulge"

cornerPinEffectName :: CornerPinEffect -> String
cornerPinEffectName _ = "Corner Pin"

liquifyEffectName :: LiquifyEffect -> String
liquifyEffectName _ = "Liquify"

mirrorEffectName :: MirrorEffect -> String
mirrorEffectName _ = "Mirror"

offsetEffectName :: OffsetEffect -> String
offsetEffectName _ = "Offset"

opticsCompensationEffectName :: OpticsCompensationEffect -> String
opticsCompensationEffectName _ = "Optics Compensation"

polarCoordinatesEffectName :: PolarCoordinatesEffect -> String
polarCoordinatesEffectName _ = "Polar Coordinates"

rippleEffectName :: RippleEffect -> String
rippleEffectName _ = "Ripple"

spherizeEffectName :: SpherizeEffect -> String
spherizeEffectName _ = "Spherize"

transformEffectName :: TransformEffect -> String
transformEffectName _ = "Transform"

turbulentDisplaceEffectName :: TurbulentDisplaceEffect -> String
turbulentDisplaceEffectName _ = "Turbulent Displace"

twirlEffectName :: TwirlEffect -> String
twirlEffectName _ = "Twirl"

waveWarpEffectName :: WaveWarpEffect -> String
waveWarpEffectName _ = "Wave Warp"

ccBendItEffectName :: CCBendItEffect -> String
ccBendItEffectName _ = "CC Bend It"

ccBlobbylizeEffectName :: CCBlobbylizeEffect -> String
ccBlobbylizeEffectName _ = "CC Blobbylize"

ccFloMotionEffectName :: CCFloMotionEffect -> String
ccFloMotionEffectName _ = "CC Flo Motion"

ccGriddlerEffectName :: CCGriddlerEffect -> String
ccGriddlerEffectName _ = "CC Griddler"

ccLensEffectName :: CCLensEffect -> String
ccLensEffectName _ = "CC Lens"

ccPageTurnEffectName :: CCPageTurnEffect -> String
ccPageTurnEffectName _ = "CC Page Turn"

ccPowerPinEffectName :: CCPowerPinEffect -> String
ccPowerPinEffectName _ = "CC Power Pin"

ccRipplePulseEffectName :: CCRipplePulseEffect -> String
ccRipplePulseEffectName _ = "CC Ripple Pulse"

ccSlantEffectName :: CCSlantEffect -> String
ccSlantEffectName _ = "CC Slant"

ccSmearEffectName :: CCSmearEffect -> String
ccSmearEffectName _ = "CC Smear"

ccSplitEffectName :: CCSplitEffect -> String
ccSplitEffectName _ = "CC Split"

ccTilerEffectName :: CCTilerEffect -> String
ccTilerEffectName _ = "CC Tiler"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

describeWarp :: WarpEffect -> String
describeWarp e =
  "Warp(" <> show e.warpStyle <> ", bend: " <> show e.bend <> ")"

describeDisplacementMap :: DisplacementMapEffect -> String
describeDisplacementMap e =
  "DisplacementMap(layer: " <> show e.mapLayer 
    <> ", h: " <> show e.maxHorizontalDisplacement
    <> ", v: " <> show e.maxVerticalDisplacement <> ")"

describeBulge :: BulgeEffect -> String
describeBulge e =
  "Bulge(radius: " <> show e.horizontalRadius <> "x" <> show e.verticalRadius
    <> ", height: " <> show e.bulgeHeight <> ")"

describeTwirl :: TwirlEffect -> String
describeTwirl e =
  "Twirl(angle: " <> show e.angle <> "°, radius: " <> show e.twirlRadius <> ")"

describeWaveWarp :: WaveWarpEffect -> String
describeWaveWarp e =
  "WaveWarp(" <> show e.waveType 
    <> ", height: " <> show e.waveHeight
    <> ", width: " <> show e.waveWidth <> ")"

describeTurbulentDisplace :: TurbulentDisplaceEffect -> String
describeTurbulentDisplace e =
  "TurbulentDisplace(" <> show e.displacement
    <> ", amount: " <> show e.amount
    <> ", complexity: " <> show e.complexity <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if warp has any bend applied.
isWarpBent :: WarpEffect -> Boolean
isWarpBent e = e.bend > 0.0 || e.bend < 0.0

-- | Check if displacement is active (non-zero displacement).
isDisplacementActive :: DisplacementMapEffect -> Boolean
isDisplacementActive e = 
  e.maxHorizontalDisplacement > 0.0 || e.maxVerticalDisplacement > 0.0

-- | Check if bulge has significant height.
hasBulgeHeight :: BulgeEffect -> Boolean
hasBulgeHeight e = e.bulgeHeight > 0.1 || e.bulgeHeight < (-0.1)

-- | Check if twirl angle is significant (> 10 degrees).
isTwirlSignificant :: TwirlEffect -> Boolean
isTwirlSignificant e = e.angle >= 10.0 || e.angle <= (-10.0)

-- | Check if wave warp has animation speed.
isWaveWarpAnimated :: WaveWarpEffect -> Boolean
isWaveWarpAnimated e = e.waveSpeed > 0.0

-- | Check if turbulent displace is complex (complexity >= 5).
isTurbulentDisplaceComplex :: TurbulentDisplaceEffect -> Boolean
isTurbulentDisplaceComplex e = e.complexity >= 5.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // advanced // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale warp bend by a factor.
scaleWarpBend :: Number -> WarpEffect -> WarpEffect
scaleWarpBend factor e =
  { warpStyle: e.warpStyle
  , bend: clampNumber (-100.0) 100.0 $ e.bend * factor
  , horizontalDistortion: e.horizontalDistortion
  , verticalDistortion: e.verticalDistortion
  }

-- | Combine two bulge effects (average heights).
combineBulgeHeights :: BulgeEffect -> BulgeEffect -> Number
combineBulgeHeights a b = (a.bulgeHeight + b.bulgeHeight) / 2.0

-- | Compute total displacement magnitude.
totalDisplacementMagnitude :: DisplacementMapEffect -> Number
totalDisplacementMagnitude e = 
  e.maxHorizontalDisplacement + e.maxVerticalDisplacement

-- | Compute wave warp intensity (height * width ratio).
waveWarpIntensity :: WaveWarpEffect -> Number
waveWarpIntensity e = e.waveHeight * (100.0 / e.waveWidth)

-- | Check if bulge is expanding or contracting.
isBulgeExpanding :: BulgeEffect -> Boolean
isBulgeExpanding e = e.bulgeHeight > 0.0

-- | Compute effective twirl revolutions.
twirlRevolutions :: TwirlEffect -> Number
twirlRevolutions e = e.angle / 360.0

-- | Adjust twirl angle by offset.
offsetTwirlAngle :: Number -> TwirlEffect -> TwirlEffect
offsetTwirlAngle offset e =
  { angle: clampNumber (-3600.0) 3600.0 $ e.angle + offset
  , twirlRadius: e.twirlRadius
  , twirlCenter: e.twirlCenter
  }

-- | Scale turbulent displace amount.
scaleTurbulentAmount :: Number -> TurbulentDisplaceEffect -> TurbulentDisplaceEffect
scaleTurbulentAmount factor e =
  { displacement: e.displacement
  , amount: clampNumber 0.0 1000.0 $ e.amount * factor
  , size: e.size
  , offset: e.offset
  , complexity: e.complexity
  , evolution: e.evolution
  , cycleEvolution: e.cycleEvolution
  , cycleRevolutions: e.cycleRevolutions
  , randomSeed: e.randomSeed
  , pinAllEdges: e.pinAllEdges
  , antialiasing: e.antialiasing
  }

-- | Compute displacement difference.
displacementDifference :: DisplacementMapEffect -> DisplacementMapEffect -> Number
displacementDifference a b =
  let
    hDiff = a.maxHorizontalDisplacement - b.maxHorizontalDisplacement
    vDiff = a.maxVerticalDisplacement - b.maxVerticalDisplacement
  in
    hDiff + vDiff

-- | Classify warp intensity by bend amount.
classifyWarpIntensity :: WarpEffect -> String
classifyWarpIntensity e
  | e.bend >= 75.0 || e.bend <= (-75.0) = "extreme"
  | e.bend >= 50.0 || e.bend <= (-50.0) = "strong"
  | e.bend >= 25.0 || e.bend <= (-25.0) = "moderate"
  | e.bend > 0.0 || e.bend < 0.0 = "subtle"
  | otherwise = "none"

-- | Check if transform has any spatial change.
hasTransformChange :: TransformEffect -> Boolean
hasTransformChange e =
  e.scaleHeight > 100.0 || e.scaleHeight < 100.0 ||
  e.scaleWidth > 100.0 || e.scaleWidth < 100.0 ||
  e.rotation > 0.0 || e.rotation < 0.0 ||
  e.skew > 0.0 || e.skew < 0.0

-- | Check if both warp distortions are active.
hasWarpBothDistortions :: WarpEffect -> Boolean
hasWarpBothDistortions e =
  (e.horizontalDistortion > 0.0 || e.horizontalDistortion < 0.0) &&
  (e.verticalDistortion > 0.0 || e.verticalDistortion < 0.0)
