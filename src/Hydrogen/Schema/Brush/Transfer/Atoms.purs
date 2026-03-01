-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brush // transfer // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transfer Atoms — Bounded numeric parameters for paint transfer.
-- |
-- | ## Design Philosophy
-- |
-- | Transfer parameters control how paint is deposited from brush to canvas.
-- | Opacity determines maximum darkness, Flow controls deposit rate,
-- | Wetness affects blending behavior, Mix determines color pickup.
-- |
-- | ## Key Properties
-- |
-- | - **Opacity**: Maximum stroke transparency (0-100%, clamps)
-- | - **Flow**: Paint deposited per dab (0-100%, clamps)
-- | - **Wetness**: How wet the paint behaves (0-100%, clamps)
-- | - **Mix**: Color pickup from existing canvas (0-100%, clamps)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Transfer.Atoms
  ( -- * Opacity (0 to 100)
    Opacity(Opacity)
  , opacity
  , opacityBounds
  , unwrapOpacity
  , noOpacity
  , halfOpacity
  , fullOpacity
  , opacityDebugInfo
  
  -- * Flow (0 to 100)
  , Flow(Flow)
  , flow
  , flowBounds
  , unwrapFlow
  , noFlow
  , lowFlow
  , standardFlow
  , fullFlow
  , flowDebugInfo
  
  -- * Wetness (0 to 100)
  , Wetness(Wetness)
  , wetness
  , wetnessBounds
  , unwrapWetness
  , dry
  , damp
  , wet
  , soaking
  , wetnessDebugInfo
  
  -- * Mix (0 to 100)
  , Mix(Mix)
  , mix
  , mixBounds
  , unwrapMix
  , noMix
  , subtleMix
  , moderateMix
  , heavyMix
  , mixDebugInfo
  
  -- * Range Queries
  , opacityInRange
  , flowInRange
  , wetnessInRange
  , mixInRange
  , isWetMediaCompatible
  , willProduceOutput
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
  )

import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , clampNumber
  , numberBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity percentage (0-100).
-- |
-- | Controls maximum darkness achievable in a single stroke.
-- | 100% = fully opaque, 0% = fully transparent.
-- | Clamps to bounds.
newtype Opacity = Opacity Number

derive instance eqOpacity :: Eq Opacity
derive instance ordOpacity :: Ord Opacity

instance showOpacity :: Show Opacity where
  show (Opacity n) = "(Opacity " <> show n <> "%)"

-- | Bounds for Opacity: 0 to 100, clamps.
opacityBounds :: NumberBounds
opacityBounds = numberBounds 0.0 100.0 Clamps "opacity" "Paint opacity percentage"

-- | Smart constructor that clamps to bounds.
opacity :: Number -> Opacity
opacity n = Opacity (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapOpacity :: Opacity -> Number
unwrapOpacity (Opacity n) = n

-- | Fully transparent.
noOpacity :: Opacity
noOpacity = Opacity 0.0

-- | Half transparent.
halfOpacity :: Opacity
halfOpacity = Opacity 50.0

-- | Fully opaque.
fullOpacity :: Opacity
fullOpacity = Opacity 100.0

-- | Generate debug info string.
opacityDebugInfo :: Opacity -> String
opacityDebugInfo o =
  show o <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // flow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flow percentage (0-100).
-- |
-- | Controls how much paint is deposited per dab.
-- | High flow = quickly reaches opacity, low flow = gradual buildup.
-- | Clamps to bounds.
newtype Flow = Flow Number

derive instance eqFlow :: Eq Flow
derive instance ordFlow :: Ord Flow

instance showFlow :: Show Flow where
  show (Flow n) = "(Flow " <> show n <> "%)"

-- | Bounds for Flow: 0 to 100, clamps.
flowBounds :: NumberBounds
flowBounds = numberBounds 0.0 100.0 Clamps "flow" "Paint flow rate percentage"

-- | Smart constructor that clamps to bounds.
flow :: Number -> Flow
flow n = Flow (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapFlow :: Flow -> Number
unwrapFlow (Flow n) = n

-- | No paint flow.
noFlow :: Flow
noFlow = Flow 0.0

-- | Low flow for airbrush effects.
lowFlow :: Flow
lowFlow = Flow 10.0

-- | Standard flow for general painting.
standardFlow :: Flow
standardFlow = Flow 50.0

-- | Maximum paint flow.
fullFlow :: Flow
fullFlow = Flow 100.0

-- | Generate debug info string.
flowDebugInfo :: Flow -> String
flowDebugInfo f =
  show f <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // wetness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wetness percentage (0-100).
-- |
-- | Controls how wet the paint behaves.
-- | Affects blending, pooling, and edge behavior.
-- | Clamps to bounds.
newtype Wetness = Wetness Number

derive instance eqWetness :: Eq Wetness
derive instance ordWetness :: Ord Wetness

instance showWetness :: Show Wetness where
  show (Wetness n) = "(Wetness " <> show n <> "%)"

-- | Bounds for Wetness: 0 to 100, clamps.
wetnessBounds :: NumberBounds
wetnessBounds = numberBounds 0.0 100.0 Clamps "wetness" "Paint wetness percentage"

-- | Smart constructor that clamps to bounds.
wetness :: Number -> Wetness
wetness n = Wetness (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapWetness :: Wetness -> Number
unwrapWetness (Wetness n) = n

-- | Completely dry paint.
dry :: Wetness
dry = Wetness 0.0

-- | Slightly damp paint.
damp :: Wetness
damp = Wetness 25.0

-- | Moderately wet paint.
wet :: Wetness
wet = Wetness 60.0

-- | Very wet, pooling paint.
soaking :: Wetness
soaking = Wetness 100.0

-- | Generate debug info string.
wetnessDebugInfo :: Wetness -> String
wetnessDebugInfo w =
  show w <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // mix
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mix percentage (0-100).
-- |
-- | Controls color pickup from the existing canvas.
-- | 0% = pure brush color, 100% = fully picks up canvas color.
-- | Clamps to bounds.
newtype Mix = Mix Number

derive instance eqMix :: Eq Mix
derive instance ordMix :: Ord Mix

instance showMix :: Show Mix where
  show (Mix n) = "(Mix " <> show n <> "%)"

-- | Bounds for Mix: 0 to 100, clamps.
mixBounds :: NumberBounds
mixBounds = numberBounds 0.0 100.0 Clamps "mix" "Color pickup percentage"

-- | Smart constructor that clamps to bounds.
mix :: Number -> Mix
mix n = Mix (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapMix :: Mix -> Number
unwrapMix (Mix n) = n

-- | No color pickup (pure brush color).
noMix :: Mix
noMix = Mix 0.0

-- | Subtle color pickup.
subtleMix :: Mix
subtleMix = Mix 20.0

-- | Moderate color mixing.
moderateMix :: Mix
moderateMix = Mix 50.0

-- | Heavy color pickup from canvas.
heavyMix :: Mix
heavyMix = Mix 80.0

-- | Generate debug info string.
mixDebugInfo :: Mix -> String
mixDebugInfo m =
  show m <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if opacity is in a custom range.
opacityInRange :: Number -> Number -> Opacity -> Boolean
opacityInRange minVal maxVal (Opacity n) = n >= minVal && n <= maxVal

-- | Check if flow is in a custom range.
flowInRange :: Number -> Number -> Flow -> Boolean
flowInRange minVal maxVal (Flow n) = n >= minVal && n <= maxVal

-- | Check if wetness is in a custom range.
wetnessInRange :: Number -> Number -> Wetness -> Boolean
wetnessInRange minVal maxVal (Wetness n) = n >= minVal && n <= maxVal

-- | Check if mix is in a custom range.
mixInRange :: Number -> Number -> Mix -> Boolean
mixInRange minVal maxVal (Mix n) = n >= minVal && n <= maxVal

-- | Check if transfer settings are compatible with wet media simulation.
-- | Requires wetness above 25% for wet media effects.
isWetMediaCompatible :: Wetness -> Boolean
isWetMediaCompatible (Wetness n) = n >= 25.0

-- | Check if settings will produce visible output.
-- | Requires both opacity and flow to be non-zero.
willProduceOutput :: Opacity -> Flow -> Boolean
willProduceOutput (Opacity o) (Flow f) = o >= 1.0 && f >= 1.0
