-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brush // scatter // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scatter Atoms — Bounded numeric parameters for scatter and jitter.
-- |
-- | ## Design Philosophy
-- |
-- | Scatter and jitter add randomization to brush strokes for natural,
-- | organic behavior. Scatter displaces dabs perpendicular to the stroke.
-- | Jitter randomizes individual parameters like size, angle, and color.
-- |
-- | ## Key Properties
-- |
-- | - **Scatter**: Perpendicular displacement (0-1000%, clamps)
-- | - **ScatterCount**: Dabs per spacing interval (1-16, clamps)
-- | - **SizeJitter**: Random size variation (0-100%, clamps)
-- | - **AngleJitter**: Random rotation variation (0-100%, clamps)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Scatter.Atoms
  ( -- * Scatter (0 to 1000)
    Scatter(Scatter)
  , scatter
  , scatterBounds
  , unwrapScatter
  , noScatter
  , lightScatter
  , heavyScatter
  , extremeScatter
  , scatterDebugInfo
  
  -- * ScatterCount (1 to 16)
  , ScatterCount(ScatterCount)
  , scatterCount
  , scatterCountBounds
  , unwrapScatterCount
  , singleDab
  , fewDabs
  , manyDabs
  , maxDabs
  , scatterCountDebugInfo
  
  -- * SizeJitter (0 to 100)
  , SizeJitter(SizeJitter)
  , sizeJitter
  , sizeJitterBounds
  , unwrapSizeJitter
  , noSizeJitter
  , subtleSizeJitter
  , moderateSizeJitter
  , extremeSizeJitter
  , sizeJitterDebugInfo
  
  -- * AngleJitter (0 to 100)
  , AngleJitter(AngleJitter)
  , angleJitter
  , angleJitterBounds
  , unwrapAngleJitter
  , noAngleJitter
  , subtleAngleJitter
  , moderateAngleJitter
  , fullAngleJitter
  , angleJitterDebugInfo
  
  -- * RoundnessJitter (0 to 100)
  , RoundnessJitter(RoundnessJitter)
  , roundnessJitter
  , roundnessJitterBounds
  , unwrapRoundnessJitter
  , noRoundnessJitter
  , subtleRoundnessJitter
  , roundnessJitterDebugInfo
  
  -- * OpacityJitter (0 to 100)
  , OpacityJitter(OpacityJitter)
  , opacityJitter
  , opacityJitterBounds
  , unwrapOpacityJitter
  , noOpacityJitter
  , subtleOpacityJitter
  , opacityJitterDebugInfo
  
  -- * FlowJitter (0 to 100)
  , FlowJitter(FlowJitter)
  , flowJitter
  , flowJitterBounds
  , unwrapFlowJitter
  , noFlowJitter
  , subtleFlowJitter
  , flowJitterDebugInfo
  
  -- * MinimumSize (0 to 100)
  , MinimumSize(MinimumSize)
  , minimumSize
  , minimumSizeBounds
  , unwrapMinimumSize
  , noMinimumSize
  , quarterMinimumSize
  , halfMinimumSize
  , minimumSizeDebugInfo
  
  -- * MinimumRoundness (0 to 100)
  , MinimumRoundness(MinimumRoundness)
  , minimumRoundness
  , minimumRoundnessBounds
  , unwrapMinimumRoundness
  , noMinimumRoundness
  , minimumRoundnessDebugInfo
  
  -- * Range Queries
  , scatterInRange
  , hasSignificantScatter
  , hasSignificantJitter
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
  , (>=)
  , (<=)
  , (&&)
  , (||)
  )

import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , IntBounds
  , clampNumber
  , clampInt
  , numberBounds
  , intBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // scatter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scatter percentage (0-1000).
-- |
-- | Controls perpendicular displacement of dabs from the stroke path.
-- | 0% = no scatter, 100% = displace up to one brush diameter,
-- | 1000% = displace up to ten brush diameters.
-- | Clamps to bounds.
newtype Scatter = Scatter Number

derive instance eqScatter :: Eq Scatter
derive instance ordScatter :: Ord Scatter

instance showScatter :: Show Scatter where
  show (Scatter n) = "(Scatter " <> show n <> "%)"

-- | Bounds for Scatter: 0 to 1000, clamps.
scatterBounds :: NumberBounds
scatterBounds = numberBounds 0.0 1000.0 Clamps "scatter" "Perpendicular displacement percentage"

-- | Smart constructor that clamps to bounds.
scatter :: Number -> Scatter
scatter n = Scatter (clampNumber 0.0 1000.0 n)

-- | Extract the raw Number value.
unwrapScatter :: Scatter -> Number
unwrapScatter (Scatter n) = n

-- | No scatter (precise strokes).
noScatter :: Scatter
noScatter = Scatter 0.0

-- | Light scatter (subtle variation).
lightScatter :: Scatter
lightScatter = Scatter 50.0

-- | Heavy scatter (loose, organic strokes).
heavyScatter :: Scatter
heavyScatter = Scatter 200.0

-- | Extreme scatter (widely dispersed dabs).
extremeScatter :: Scatter
extremeScatter = Scatter 500.0

-- | Generate debug info string.
scatterDebugInfo :: Scatter -> String
scatterDebugInfo s =
  show s <> " [bounds: 0-1000%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scatter count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scatter count (1-16).
-- |
-- | Number of dabs placed per spacing interval.
-- | 1 = single dab per interval (normal), 16 = dense spray effect.
-- | Clamps to bounds.
newtype ScatterCount = ScatterCount Int

derive instance eqScatterCount :: Eq ScatterCount
derive instance ordScatterCount :: Ord ScatterCount

instance showScatterCount :: Show ScatterCount where
  show (ScatterCount n) = "(ScatterCount " <> show n <> ")"

-- | Bounds for ScatterCount: 1 to 16, clamps.
scatterCountBounds :: IntBounds
scatterCountBounds = intBounds 1 16 Clamps "scatterCount" "Dabs per spacing interval"

-- | Smart constructor that clamps to bounds.
scatterCount :: Int -> ScatterCount
scatterCount n = ScatterCount (clampInt 1 16 n)

-- | Extract the raw Int value.
unwrapScatterCount :: ScatterCount -> Int
unwrapScatterCount (ScatterCount n) = n

-- | Single dab per interval (default).
singleDab :: ScatterCount
singleDab = ScatterCount 1

-- | Few dabs (light spray).
fewDabs :: ScatterCount
fewDabs = ScatterCount 3

-- | Many dabs (dense spray).
manyDabs :: ScatterCount
manyDabs = ScatterCount 8

-- | Maximum dabs (very dense).
maxDabs :: ScatterCount
maxDabs = ScatterCount 16

-- | Generate debug info string.
scatterCountDebugInfo :: ScatterCount -> String
scatterCountDebugInfo c =
  show c <> " [bounds: 1-16, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // size jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size jitter percentage (0-100).
-- |
-- | Random variation in brush diameter per dab.
-- | 0% = no variation, 100% = 0% to 100% of base size.
-- | Clamps to bounds.
newtype SizeJitter = SizeJitter Number

derive instance eqSizeJitter :: Eq SizeJitter
derive instance ordSizeJitter :: Ord SizeJitter

instance showSizeJitter :: Show SizeJitter where
  show (SizeJitter n) = "(SizeJitter " <> show n <> "%)"

-- | Bounds for SizeJitter: 0 to 100, clamps.
sizeJitterBounds :: NumberBounds
sizeJitterBounds = numberBounds 0.0 100.0 Clamps "sizeJitter" "Random size variation percentage"

-- | Smart constructor that clamps to bounds.
sizeJitter :: Number -> SizeJitter
sizeJitter n = SizeJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapSizeJitter :: SizeJitter -> Number
unwrapSizeJitter (SizeJitter n) = n

-- | No size variation.
noSizeJitter :: SizeJitter
noSizeJitter = SizeJitter 0.0

-- | Subtle size variation.
subtleSizeJitter :: SizeJitter
subtleSizeJitter = SizeJitter 10.0

-- | Moderate size variation.
moderateSizeJitter :: SizeJitter
moderateSizeJitter = SizeJitter 50.0

-- | Extreme size variation.
extremeSizeJitter :: SizeJitter
extremeSizeJitter = SizeJitter 100.0

-- | Generate debug info string.
sizeJitterDebugInfo :: SizeJitter -> String
sizeJitterDebugInfo j =
  show j <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // angle jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Angle jitter percentage (0-100).
-- |
-- | Random variation in brush tip rotation per dab.
-- | 0% = no rotation, 100% = ±180° random rotation.
-- | Clamps to bounds.
newtype AngleJitter = AngleJitter Number

derive instance eqAngleJitter :: Eq AngleJitter
derive instance ordAngleJitter :: Ord AngleJitter

instance showAngleJitter :: Show AngleJitter where
  show (AngleJitter n) = "(AngleJitter " <> show n <> "%)"

-- | Bounds for AngleJitter: 0 to 100, clamps.
angleJitterBounds :: NumberBounds
angleJitterBounds = numberBounds 0.0 100.0 Clamps "angleJitter" "Random rotation variation percentage"

-- | Smart constructor that clamps to bounds.
angleJitter :: Number -> AngleJitter
angleJitter n = AngleJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapAngleJitter :: AngleJitter -> Number
unwrapAngleJitter (AngleJitter n) = n

-- | No angle variation.
noAngleJitter :: AngleJitter
noAngleJitter = AngleJitter 0.0

-- | Subtle angle variation.
subtleAngleJitter :: AngleJitter
subtleAngleJitter = AngleJitter 10.0

-- | Moderate angle variation.
moderateAngleJitter :: AngleJitter
moderateAngleJitter = AngleJitter 50.0

-- | Full random rotation.
fullAngleJitter :: AngleJitter
fullAngleJitter = AngleJitter 100.0

-- | Generate debug info string.
angleJitterDebugInfo :: AngleJitter -> String
angleJitterDebugInfo j =
  show j <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // roundness jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Roundness jitter percentage (0-100).
-- |
-- | Random variation in brush tip aspect ratio per dab.
-- | 0% = no variation, 100% = 0% to base roundness.
-- | Clamps to bounds.
newtype RoundnessJitter = RoundnessJitter Number

derive instance eqRoundnessJitter :: Eq RoundnessJitter
derive instance ordRoundnessJitter :: Ord RoundnessJitter

instance showRoundnessJitter :: Show RoundnessJitter where
  show (RoundnessJitter n) = "(RoundnessJitter " <> show n <> "%)"

-- | Bounds for RoundnessJitter: 0 to 100, clamps.
roundnessJitterBounds :: NumberBounds
roundnessJitterBounds = numberBounds 0.0 100.0 Clamps "roundnessJitter" "Random roundness variation percentage"

-- | Smart constructor that clamps to bounds.
roundnessJitter :: Number -> RoundnessJitter
roundnessJitter n = RoundnessJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapRoundnessJitter :: RoundnessJitter -> Number
unwrapRoundnessJitter (RoundnessJitter n) = n

-- | No roundness variation.
noRoundnessJitter :: RoundnessJitter
noRoundnessJitter = RoundnessJitter 0.0

-- | Subtle roundness variation.
subtleRoundnessJitter :: RoundnessJitter
subtleRoundnessJitter = RoundnessJitter 25.0

-- | Generate debug info string.
roundnessJitterDebugInfo :: RoundnessJitter -> String
roundnessJitterDebugInfo j =
  show j <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // opacity jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity jitter percentage (0-100).
-- |
-- | Random variation in dab opacity.
-- | 0% = no variation, 100% = 0% to base opacity.
-- | Clamps to bounds.
newtype OpacityJitter = OpacityJitter Number

derive instance eqOpacityJitter :: Eq OpacityJitter
derive instance ordOpacityJitter :: Ord OpacityJitter

instance showOpacityJitter :: Show OpacityJitter where
  show (OpacityJitter n) = "(OpacityJitter " <> show n <> "%)"

-- | Bounds for OpacityJitter: 0 to 100, clamps.
opacityJitterBounds :: NumberBounds
opacityJitterBounds = numberBounds 0.0 100.0 Clamps "opacityJitter" "Random opacity variation percentage"

-- | Smart constructor that clamps to bounds.
opacityJitter :: Number -> OpacityJitter
opacityJitter n = OpacityJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapOpacityJitter :: OpacityJitter -> Number
unwrapOpacityJitter (OpacityJitter n) = n

-- | No opacity variation.
noOpacityJitter :: OpacityJitter
noOpacityJitter = OpacityJitter 0.0

-- | Subtle opacity variation.
subtleOpacityJitter :: OpacityJitter
subtleOpacityJitter = OpacityJitter 20.0

-- | Generate debug info string.
opacityJitterDebugInfo :: OpacityJitter -> String
opacityJitterDebugInfo j =
  show j <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // flow jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flow jitter percentage (0-100).
-- |
-- | Random variation in dab flow rate.
-- | 0% = no variation, 100% = 0% to base flow.
-- | Clamps to bounds.
newtype FlowJitter = FlowJitter Number

derive instance eqFlowJitter :: Eq FlowJitter
derive instance ordFlowJitter :: Ord FlowJitter

instance showFlowJitter :: Show FlowJitter where
  show (FlowJitter n) = "(FlowJitter " <> show n <> "%)"

-- | Bounds for FlowJitter: 0 to 100, clamps.
flowJitterBounds :: NumberBounds
flowJitterBounds = numberBounds 0.0 100.0 Clamps "flowJitter" "Random flow variation percentage"

-- | Smart constructor that clamps to bounds.
flowJitter :: Number -> FlowJitter
flowJitter n = FlowJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapFlowJitter :: FlowJitter -> Number
unwrapFlowJitter (FlowJitter n) = n

-- | No flow variation.
noFlowJitter :: FlowJitter
noFlowJitter = FlowJitter 0.0

-- | Subtle flow variation.
subtleFlowJitter :: FlowJitter
subtleFlowJitter = FlowJitter 20.0

-- | Generate debug info string.
flowJitterDebugInfo :: FlowJitter -> String
flowJitterDebugInfo j =
  show j <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // minimum size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum size percentage (0-100).
-- |
-- | Floor for size jitter — the smallest size allowed.
-- | When size jitter is 100%, dabs range from MinimumSize to 100%.
-- | Clamps to bounds.
newtype MinimumSize = MinimumSize Number

derive instance eqMinimumSize :: Eq MinimumSize
derive instance ordMinimumSize :: Ord MinimumSize

instance showMinimumSize :: Show MinimumSize where
  show (MinimumSize n) = "(MinimumSize " <> show n <> "%)"

-- | Bounds for MinimumSize: 0 to 100, clamps.
minimumSizeBounds :: NumberBounds
minimumSizeBounds = numberBounds 0.0 100.0 Clamps "minimumSize" "Floor for size jitter percentage"

-- | Smart constructor that clamps to bounds.
minimumSize :: Number -> MinimumSize
minimumSize n = MinimumSize (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapMinimumSize :: MinimumSize -> Number
unwrapMinimumSize (MinimumSize n) = n

-- | No minimum (can shrink to 0%).
noMinimumSize :: MinimumSize
noMinimumSize = MinimumSize 0.0

-- | Quarter minimum (shrink to 25% at most).
quarterMinimumSize :: MinimumSize
quarterMinimumSize = MinimumSize 25.0

-- | Half minimum (shrink to 50% at most).
halfMinimumSize :: MinimumSize
halfMinimumSize = MinimumSize 50.0

-- | Generate debug info string.
minimumSizeDebugInfo :: MinimumSize -> String
minimumSizeDebugInfo m =
  show m <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // minimum roundness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum roundness percentage (0-100).
-- |
-- | Floor for roundness jitter — the thinnest ellipse allowed.
-- | Clamps to bounds.
newtype MinimumRoundness = MinimumRoundness Number

derive instance eqMinimumRoundness :: Eq MinimumRoundness
derive instance ordMinimumRoundness :: Ord MinimumRoundness

instance showMinimumRoundness :: Show MinimumRoundness where
  show (MinimumRoundness n) = "(MinimumRoundness " <> show n <> "%)"

-- | Bounds for MinimumRoundness: 0 to 100, clamps.
minimumRoundnessBounds :: NumberBounds
minimumRoundnessBounds = numberBounds 0.0 100.0 Clamps "minimumRoundness" "Floor for roundness jitter percentage"

-- | Smart constructor that clamps to bounds.
minimumRoundness :: Number -> MinimumRoundness
minimumRoundness n = MinimumRoundness (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapMinimumRoundness :: MinimumRoundness -> Number
unwrapMinimumRoundness (MinimumRoundness n) = n

-- | No minimum (can become a line).
noMinimumRoundness :: MinimumRoundness
noMinimumRoundness = MinimumRoundness 0.0

-- | Generate debug info string.
minimumRoundnessDebugInfo :: MinimumRoundness -> String
minimumRoundnessDebugInfo m =
  show m <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if scatter is in a custom range.
scatterInRange :: Number -> Number -> Scatter -> Boolean
scatterInRange minVal maxVal (Scatter n) = n >= minVal && n <= maxVal

-- | Check if scatter amount is significant (>= 10%).
hasSignificantScatter :: Scatter -> Boolean
hasSignificantScatter (Scatter n) = n >= 10.0

-- | Check if any jitter parameter is significant.
-- | Returns true if size or angle jitter is >= 5%.
hasSignificantJitter :: SizeJitter -> AngleJitter -> Boolean
hasSignificantJitter (SizeJitter s) (AngleJitter a) = s >= 5.0 || a >= 5.0
