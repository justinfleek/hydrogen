-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // shapes // modifiers // wave
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stroke wave properties.
-- |
-- | Applies a wave deformation to the stroke path.
-- | Professional motion graphics tools introduced this in CC 2020 for shape layers.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Wave
  ( -- * Wave Type
    WaveType(WTSine, WTSquare, WTTriangle, WTSawtooth)
  , waveTypeToString
  
  -- * Stroke Wave
  , StrokeWave
  , strokeWave
  , noWave
  , defaultWave
  , sineWave
  , squareWave
  , triangleWave
  , sawtoothWave
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( PositiveNumber
  , positiveNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stroke // wave
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wave type — shape of wave pattern.
data WaveType
  = WTSine             -- ^ Smooth sine wave
  | WTSquare           -- ^ Square wave
  | WTTriangle         -- ^ Triangle wave
  | WTSawtooth         -- ^ Sawtooth wave

derive instance eqWaveType :: Eq WaveType
derive instance ordWaveType :: Ord WaveType

instance showWaveType :: Show WaveType where
  show WTSine = "sine"
  show WTSquare = "square"
  show WTTriangle = "triangle"
  show WTSawtooth = "sawtooth"

-- | Convert wave type to string.
waveTypeToString :: WaveType -> String
waveTypeToString wt = show wt

-- | Stroke wave properties.
-- |
-- | Applies a wave deformation to the stroke path.
-- | Professional motion graphics tools introduced this in CC 2020 for shape layers.
-- |
-- | ## Properties
-- |
-- | - **amount**: Wave amplitude (0-500)
-- | - **frequency**: Number of waves (0-50)
-- | - **phase**: Phase offset (0-360 degrees)
-- | - **waveType**: Shape of wave
type StrokeWave =
  { enabled :: Boolean           -- ^ Whether wave is active
  , amount :: PositiveNumber     -- ^ Wave amplitude (0-500)
  , frequency :: PositiveNumber  -- ^ Number of waves (0-50)
  , phase :: Number              -- ^ Phase offset (0-360 degrees)
  , waveType :: WaveType         -- ^ Wave shape
  }

-- | Create stroke wave with explicit values.
strokeWave
  :: Boolean     -- ^ Enabled
  -> Number      -- ^ Amount
  -> Number      -- ^ Frequency
  -> Number      -- ^ Phase (degrees)
  -> WaveType
  -> StrokeWave
strokeWave en a f p wt =
  { enabled: en
  , amount: positiveNumber (clampNumber 0.0 500.0 a)
  , frequency: positiveNumber (clampNumber 0.0 50.0 f)
  , phase: clampNumber 0.0 360.0 p
  , waveType: wt
  }

-- | No wave (straight stroke).
noWave :: StrokeWave
noWave =
  { enabled: false
  , amount: positiveNumber 0.0
  , frequency: positiveNumber 0.0
  , phase: 0.0
  , waveType: WTSine
  }

-- | Default wave: moderate sine wave.
defaultWave :: StrokeWave
defaultWave =
  { enabled: true
  , amount: positiveNumber 10.0
  , frequency: positiveNumber 5.0
  , phase: 0.0
  , waveType: WTSine
  }

-- | Create sine wave.
sineWave :: Number -> Number -> StrokeWave
sineWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTSine
  }

-- | Create square wave.
squareWave :: Number -> Number -> StrokeWave
squareWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTSquare
  }

-- | Create triangle wave.
triangleWave :: Number -> Number -> StrokeWave
triangleWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTTriangle
  }

-- | Create sawtooth wave.
sawtoothWave :: Number -> Number -> StrokeWave
sawtoothWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTSawtooth
  }
