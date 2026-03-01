-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // smoothing // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Smoothing Atoms — Bounded numeric parameters for stroke smoothing.
-- |
-- | ## Design Philosophy
-- |
-- | Smoothing parameters control the strength and behavior of stroke
-- | stabilization. These atoms provide bounded values for smoothing
-- | strength, string length (for pulled-string), and One Euro Filter
-- | parameters.
-- |
-- | ## Key Properties
-- |
-- | - **SmoothingStrength**: How much smoothing to apply (0-100%)
-- | - **StringLength**: Distance for pulled-string stabilizer (0-500px)
-- | - **WindowSize**: Samples for moving average (1-32)
-- | - **CatchUpSpeed**: How fast cursor catches up on release (0-1)
-- | - **MinCutoff**: One Euro Filter minimum cutoff (0.1-10)
-- | - **Beta**: One Euro Filter speed coefficient (0-1)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Smoothing.Atoms
  ( -- * SmoothingStrength (0 to 100)
    SmoothingStrength(SmoothingStrength)
  , smoothingStrength
  , smoothingStrengthBounds
  , unwrapSmoothingStrength
  , noStrength
  , lightStrength
  , moderateStrength
  , heavyStrength
  , maxStrength
  , smoothingStrengthDebugInfo
  
  -- * StringLength (0 to 500)
  , StringLength(StringLength)
  , stringLength
  , stringLengthBounds
  , unwrapStringLength
  , noString
  , shortString
  , mediumString
  , longString
  , stringLengthDebugInfo
  
  -- * WindowSize (1 to 32)
  , WindowSize(WindowSize)
  , windowSize
  , windowSizeBounds
  , unwrapWindowSize
  , minimalWindow
  , smallWindow
  , mediumWindow
  , largeWindow
  , windowSizeDebugInfo
  
  -- * CatchUpSpeed (0 to 1)
  , CatchUpSpeed(CatchUpSpeed)
  , catchUpSpeed
  , catchUpSpeedBounds
  , unwrapCatchUpSpeed
  , slowCatchUp
  , normalCatchUp
  , fastCatchUp
  , instantCatchUp
  , catchUpSpeedDebugInfo
  
  -- * MinCutoff (0.1 to 10) for One Euro Filter
  , MinCutoff(MinCutoff)
  , minCutoff
  , minCutoffBounds
  , unwrapMinCutoff
  , lowCutoff
  , defaultCutoff
  , highCutoff
  , minCutoffDebugInfo
  
  -- * Beta (0 to 1) for One Euro Filter
  , Beta(Beta)
  , beta
  , betaBounds
  , unwrapBeta
  , lowBeta
  , defaultBeta
  , highBeta
  , betaDebugInfo
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
--                                                        // smoothing strength
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smoothing strength as percentage (0 to 100).
-- |
-- | Controls how much smoothing is applied:
-- | - 0%: No smoothing (raw input)
-- | - 50%: Moderate smoothing
-- | - 100%: Maximum smoothing (may feel laggy)
newtype SmoothingStrength = SmoothingStrength Number

derive instance eqSmoothingStrength :: Eq SmoothingStrength
derive instance ordSmoothingStrength :: Ord SmoothingStrength

instance showSmoothingStrength :: Show SmoothingStrength where
  show (SmoothingStrength s) = "(SmoothingStrength " <> show s <> "%)"

-- | Bounded specification for SmoothingStrength.
smoothingStrengthBounds :: Bounded.NumberBounds
smoothingStrengthBounds = Bounded.numberBounds 0.0 100.0 Bounded.Clamps
  "smoothingStrength" "Smoothing intensity (0=none, 100=max)"

-- | Create a SmoothingStrength value (clamped to 0-100).
smoothingStrength :: Number -> SmoothingStrength
smoothingStrength n = SmoothingStrength (Bounded.clampNumber 0.0 100.0 n)

-- | Extract the raw SmoothingStrength value.
unwrapSmoothingStrength :: SmoothingStrength -> Number
unwrapSmoothingStrength (SmoothingStrength s) = s

-- | No smoothing (0%).
noStrength :: SmoothingStrength
noStrength = SmoothingStrength 0.0

-- | Light smoothing (20%) — natural feel.
lightStrength :: SmoothingStrength
lightStrength = SmoothingStrength 20.0

-- | Moderate smoothing (50%) — clean lines.
moderateStrength :: SmoothingStrength
moderateStrength = SmoothingStrength 50.0

-- | Heavy smoothing (70%) — precise curves.
heavyStrength :: SmoothingStrength
heavyStrength = SmoothingStrength 70.0

-- | Maximum smoothing (95%) — technical drawing.
maxStrength :: SmoothingStrength
maxStrength = SmoothingStrength 95.0

-- | Debug info string for SmoothingStrength.
smoothingStrengthDebugInfo :: SmoothingStrength -> String
smoothingStrengthDebugInfo s = show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // string length
-- ═════════════════════════════════════════════════════════════════════════════

-- | String length in pixels for pulled-string stabilizer (0 to 500).
-- |
-- | The lazy cursor follows at this distance from the actual input.
-- | Longer strings provide more stabilization but increase latency.
newtype StringLength = StringLength Number

derive instance eqStringLength :: Eq StringLength
derive instance ordStringLength :: Ord StringLength

instance showStringLength :: Show StringLength where
  show (StringLength l) = "(StringLength " <> show l <> "px)"

-- | Bounded specification for StringLength.
stringLengthBounds :: Bounded.NumberBounds
stringLengthBounds = Bounded.numberBounds 0.0 500.0 Bounded.Clamps
  "stringLength" "Pulled-string distance in pixels (0-500)"

-- | Create a StringLength value (clamped to 0-500).
stringLength :: Number -> StringLength
stringLength n = StringLength (Bounded.clampNumber 0.0 500.0 n)

-- | Extract the raw StringLength value.
unwrapStringLength :: StringLength -> Number
unwrapStringLength (StringLength l) = l

-- | No string (0px) — disabled.
noString :: StringLength
noString = StringLength 0.0

-- | Short string (10px) — slight smoothing.
shortString :: StringLength
shortString = StringLength 10.0

-- | Medium string (50px) — moderate control.
mediumString :: StringLength
mediumString = StringLength 50.0

-- | Long string (100px) — strong control.
longString :: StringLength
longString = StringLength 100.0

-- | Debug info string for StringLength.
stringLengthDebugInfo :: StringLength -> String
stringLengthDebugInfo l = show l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // window size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample window size for averaging algorithms (1 to 32).
-- |
-- | Number of past samples to include in moving average.
-- | Larger windows produce smoother output but add latency.
newtype WindowSize = WindowSize Int

derive instance eqWindowSize :: Eq WindowSize
derive instance ordWindowSize :: Ord WindowSize

instance showWindowSize :: Show WindowSize where
  show (WindowSize w) = "(WindowSize " <> show w <> " samples)"

-- | Bounded specification for WindowSize.
windowSizeBounds :: Bounded.IntBounds
windowSizeBounds = Bounded.intBounds 1 32 Bounded.Clamps
  "windowSize" "Moving average samples (1-32)"

-- | Create a WindowSize value (clamped to 1-32).
windowSize :: Int -> WindowSize
windowSize n = WindowSize (Bounded.clampInt 1 32 n)

-- | Extract the raw WindowSize value.
unwrapWindowSize :: WindowSize -> Int
unwrapWindowSize (WindowSize w) = w

-- | Minimal window (1) — no averaging.
minimalWindow :: WindowSize
minimalWindow = WindowSize 1

-- | Small window (4) — light averaging.
smallWindow :: WindowSize
smallWindow = WindowSize 4

-- | Medium window (8) — balanced.
mediumWindow :: WindowSize
mediumWindow = WindowSize 8

-- | Large window (16) — heavy averaging.
largeWindow :: WindowSize
largeWindow = WindowSize 16

-- | Debug info string for WindowSize.
windowSizeDebugInfo :: WindowSize -> String
windowSizeDebugInfo w = show w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // catch up speed
-- ═════════════════════════════════════════════════════════════════════════════

-- | Catch-up speed for stabilizer on stroke release (0 to 1).
-- |
-- | When the stylus is lifted, the cursor catches up to the final position.
-- | Higher values make the catch-up faster.
newtype CatchUpSpeed = CatchUpSpeed Number

derive instance eqCatchUpSpeed :: Eq CatchUpSpeed
derive instance ordCatchUpSpeed :: Ord CatchUpSpeed

instance showCatchUpSpeed :: Show CatchUpSpeed where
  show (CatchUpSpeed s) = "(CatchUpSpeed " <> show s <> ")"

-- | Bounded specification for CatchUpSpeed.
catchUpSpeedBounds :: Bounded.NumberBounds
catchUpSpeedBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "catchUpSpeed" "Stabilizer catch-up rate (0=slow, 1=instant)"

-- | Create a CatchUpSpeed value (clamped to 0-1).
catchUpSpeed :: Number -> CatchUpSpeed
catchUpSpeed n = CatchUpSpeed (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw CatchUpSpeed value.
unwrapCatchUpSpeed :: CatchUpSpeed -> Number
unwrapCatchUpSpeed (CatchUpSpeed s) = s

-- | Slow catch-up (0.2) — smooth finish.
slowCatchUp :: CatchUpSpeed
slowCatchUp = CatchUpSpeed 0.2

-- | Normal catch-up (0.5) — balanced.
normalCatchUp :: CatchUpSpeed
normalCatchUp = CatchUpSpeed 0.5

-- | Fast catch-up (0.8) — quick finish.
fastCatchUp :: CatchUpSpeed
fastCatchUp = CatchUpSpeed 0.8

-- | Instant catch-up (1.0) — immediate.
instantCatchUp :: CatchUpSpeed
instantCatchUp = CatchUpSpeed 1.0

-- | Debug info string for CatchUpSpeed.
catchUpSpeedDebugInfo :: CatchUpSpeed -> String
catchUpSpeedDebugInfo s = show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // one euro filter: min cutoff
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum cutoff frequency for One Euro Filter (0.1 to 10).
-- |
-- | Controls baseline smoothing. Lower values = more smoothing.
-- | The filter adapts based on input speed.
newtype MinCutoff = MinCutoff Number

derive instance eqMinCutoff :: Eq MinCutoff
derive instance ordMinCutoff :: Ord MinCutoff

instance showMinCutoff :: Show MinCutoff where
  show (MinCutoff c) = "(MinCutoff " <> show c <> "Hz)"

-- | Bounded specification for MinCutoff.
minCutoffBounds :: Bounded.NumberBounds
minCutoffBounds = Bounded.numberBounds 0.1 10.0 Bounded.Clamps
  "minCutoff" "One Euro Filter min cutoff Hz (0.1-10)"

-- | Create a MinCutoff value (clamped to 0.1-10).
minCutoff :: Number -> MinCutoff
minCutoff n = MinCutoff (Bounded.clampNumber 0.1 10.0 n)

-- | Extract the raw MinCutoff value.
unwrapMinCutoff :: MinCutoff -> Number
unwrapMinCutoff (MinCutoff c) = c

-- | Low cutoff (0.5) — more smoothing.
lowCutoff :: MinCutoff
lowCutoff = MinCutoff 0.5

-- | Default cutoff (1.0) — balanced.
defaultCutoff :: MinCutoff
defaultCutoff = MinCutoff 1.0

-- | High cutoff (3.0) — less smoothing, more responsive.
highCutoff :: MinCutoff
highCutoff = MinCutoff 3.0

-- | Debug info string for MinCutoff.
minCutoffDebugInfo :: MinCutoff -> String
minCutoffDebugInfo c = show c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // one euro filter: beta
-- ═════════════════════════════════════════════════════════════════════════════

-- | Beta (speed coefficient) for One Euro Filter (0 to 1).
-- |
-- | Controls how much input speed affects the cutoff frequency.
-- | Higher beta = more responsive to fast movements.
newtype Beta = Beta Number

derive instance eqBeta :: Eq Beta
derive instance ordBeta :: Ord Beta

instance showBeta :: Show Beta where
  show (Beta b) = "(Beta " <> show b <> ")"

-- | Bounded specification for Beta.
betaBounds :: Bounded.NumberBounds
betaBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "beta" "One Euro Filter speed coefficient (0-1)"

-- | Create a Beta value (clamped to 0-1).
beta :: Number -> Beta
beta n = Beta (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw Beta value.
unwrapBeta :: Beta -> Number
unwrapBeta (Beta b) = b

-- | Low beta (0.0) — constant smoothing regardless of speed.
lowBeta :: Beta
lowBeta = Beta 0.0

-- | Default beta (0.5) — balanced speed adaptation.
defaultBeta :: Beta
defaultBeta = Beta 0.5

-- | High beta (0.9) — very responsive to fast movement.
highBeta :: Beta
highBeta = Beta 0.9

-- | Debug info string for Beta.
betaDebugInfo :: Beta -> String
betaDebugInfo b = show b
