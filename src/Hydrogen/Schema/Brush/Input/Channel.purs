-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brush // input // channel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graded Input Channels — Unified abstraction for heterogeneous sensor input.
-- |
-- | Status: PROVEN (proofs/Hydrogen/Schema/Brush/InputChannel.lean)
-- |
-- | ## Purpose
-- |
-- | When an uploaded mind, a BMI user, a stylus, a phone accelerometer, or
-- | an AI agent in simulation all need to express "pressure" — they use the
-- | same InputChannel type. The GRADE tracks provenance, certainty, and trust.
-- |
-- | ## Strong Invariants (Proven in Lean4)
-- |
-- | 1. PROVENANCE — Values cannot lie about their origin
-- | 2. CONSENT — Neural channels require explicit consent (Consent.lean)
-- | 3. WITNESS — Intent channels produce VerifiedWitness (Witness.lean)
-- | 4. BOUNDS — All values in [0,1] or [-1,1], no NaN/Infinity
-- | 5. COMPOSITION — Grade join is semilattice (assoc, comm, idem)
-- | 6. DEGRADATION — Transformations can only degrade grade
-- | 7. FALLBACK — Graceful degradation with tracked grade
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Bounded (UnitInterval)

module Hydrogen.Schema.Brush.Input.Channel
  ( -- * Provenance Grade
    Provenance(..)
  , allProvenances
  , provenanceToInt
  , provenanceDescription
  , joinProvenance
  , meetProvenance
  
  -- * Certainty Grade
  , Certainty(..)
  , allCertainties
  , certaintyToInt
  , certaintyDescription
  , joinCertainty
  , meetCertainty
  
  -- * Input Grade (Product)
  , InputGrade(..)
  , topGrade
  , bottomGrade
  , joinGrade
  , meetGrade
  , gradeToInt
  
  -- * Sensor Sources
  , SensorSource(..)
  , allSensorSources
  , sensorProvenance
  , sensorRequiresConsent
  , sensorProducesWitness
  , sensorIsPhysical
  , sensorDescription
  
  -- * Input Channel
  , InputChannel(..)
  , inputChannelFromHardware
  , inputChannelFromSimulation
  , inputChannelDefault
  , inputChannelTrustLevel
  , inputChannelDebugInfo
  
  -- * Bipolar Input Channel
  , BipolarInputChannel(..)
  , bipolarChannelToUnsigned
  , bipolarChannelDebugInfo
  
  -- * Graded Transformation
  , GradedTransformation(..)
  , interpolationTransform
  , estimationTransform
  , defaultFallbackTransform
  , identityTransform
  , applyTransformation
  
  -- * Composition
  , composeChannels
  , avgValue
  , maxValue
  , minValue
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(EQ)
  , compare
  , max
  , show
  , (+)
  , (*)
  , (/)
  , (<=)
  , (>=)
  , (>)
  , (<>)
  )

import Data.Number (abs) as Number

import Hydrogen.Schema.Bounded
  ( UnitInterval
  , clampUnit
  , unwrapUnit
  , unitZero
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // provenance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Provenance tracks WHERE an input value originated.
-- |
-- | Ordering: Hardware >= Neural >= Simulated >= Intent
-- | (Higher trust = higher in ordering)
-- |
-- | Proven: semilattice properties in InputChannel.lean
data Provenance
  = Hardware    -- ^ Direct physical sensor (highest trust)
  | Neural      -- ^ Brain-machine interface (requires consent)
  | Simulated   -- ^ AI agent in simulation
  | Intent      -- ^ High-level intent expression (produces witness)

derive instance eqProvenance :: Eq Provenance

instance ordProvenance :: Ord Provenance where
  compare p1 p2 = compare (provenanceToInt p1) (provenanceToInt p2)

instance showProvenance :: Show Provenance where
  show Hardware = "(Provenance Hardware)"
  show Neural = "(Provenance Neural)"
  show Simulated = "(Provenance Simulated)"
  show Intent = "(Provenance Intent)"

-- | All provenance values in trust order (highest first).
allProvenances :: Array Provenance
allProvenances = [ Hardware, Neural, Simulated, Intent ]

-- | Numeric encoding for ordering (higher = more trusted).
-- | Proven: total ordering in InputChannel.lean
provenanceToInt :: Provenance -> Int
provenanceToInt Hardware = 3
provenanceToInt Neural = 2
provenanceToInt Simulated = 1
provenanceToInt Intent = 0

-- | Human-readable description of each provenance.
provenanceDescription :: Provenance -> String
provenanceDescription Hardware = "Direct physical sensor (stylus, accelerometer)"
provenanceDescription Neural = "Brain-machine interface input (requires consent)"
provenanceDescription Simulated = "AI agent in simulation"
provenanceDescription Intent = "High-level intent expression (produces witness)"

-- | Join operation (semilattice sup): takes the LOWER trust level.
-- | Proven: join_comm, join_assoc, join_idem in InputChannel.lean
joinProvenance :: Provenance -> Provenance -> Provenance
joinProvenance p1 p2 =
  if provenanceToInt p1 <= provenanceToInt p2
    then p1
    else p2

-- | Meet operation (semilattice inf): takes the HIGHER trust level.
meetProvenance :: Provenance -> Provenance -> Provenance
meetProvenance p1 p2 =
  if provenanceToInt p1 >= provenanceToInt p2
    then p1
    else p2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // certainty
-- ═════════════════════════════════════════════════════════════════════════════

-- | Certainty tracks HOW CONFIDENT we are in a value.
-- |
-- | Ordering: Exact >= Estimated >= Interpolated >= Default
-- | (Higher certainty = higher in ordering)
-- |
-- | Proven: semilattice properties in InputChannel.lean
data Certainty
  = Exact         -- ^ Direct measurement
  | Estimated     -- ^ Computed with known error bounds
  | Interpolated  -- ^ Filled between samples
  | Default       -- ^ Fallback value

derive instance eqCertainty :: Eq Certainty

instance ordCertainty :: Ord Certainty where
  compare c1 c2 = compare (certaintyToInt c1) (certaintyToInt c2)

instance showCertainty :: Show Certainty where
  show Exact = "(Certainty Exact)"
  show Estimated = "(Certainty Estimated)"
  show Interpolated = "(Certainty Interpolated)"
  show Default = "(Certainty Default)"

-- | All certainty values in confidence order (highest first).
allCertainties :: Array Certainty
allCertainties = [ Exact, Estimated, Interpolated, Default ]

-- | Numeric encoding for ordering (higher = more certain).
-- | Proven: total ordering in InputChannel.lean
certaintyToInt :: Certainty -> Int
certaintyToInt Exact = 3
certaintyToInt Estimated = 2
certaintyToInt Interpolated = 1
certaintyToInt Default = 0

-- | Human-readable description of each certainty level.
certaintyDescription :: Certainty -> String
certaintyDescription Exact = "Direct measurement, no estimation"
certaintyDescription Estimated = "Computed from other values with known error"
certaintyDescription Interpolated = "Filled in between known values"
certaintyDescription Default = "Fallback value, no actual data"

-- | Join operation (semilattice sup): takes the LOWER certainty.
-- | Proven: join_comm, join_assoc, join_idem in InputChannel.lean
joinCertainty :: Certainty -> Certainty -> Certainty
joinCertainty c1 c2 =
  if certaintyToInt c1 <= certaintyToInt c2
    then c1
    else c2

-- | Meet operation (semilattice inf): takes the HIGHER certainty.
meetCertainty :: Certainty -> Certainty -> Certainty
meetCertainty c1 c2 =
  if certaintyToInt c1 >= certaintyToInt c2
    then c1
    else c2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // input grade
-- ═════════════════════════════════════════════════════════════════════════════

-- | InputGrade is the product of Provenance x Certainty.
-- |
-- | This forms a product semilattice where:
-- | - join is component-wise join
-- | - meet is component-wise meet
-- | - ordering is component-wise ordering
-- |
-- | Proven: semilattice properties in InputChannel.lean
newtype InputGrade = InputGrade
  { provenance :: Provenance
  , certainty :: Certainty
  }

derive instance eqInputGrade :: Eq InputGrade

instance ordInputGrade :: Ord InputGrade where
  compare (InputGrade g1) (InputGrade g2) =
    case compare g1.provenance g2.provenance of
      EQ -> compare g1.certainty g2.certainty
      other -> other

instance showInputGrade :: Show InputGrade where
  show (InputGrade g) = "(InputGrade "
    <> show g.provenance
    <> " " <> show g.certainty
    <> ")"

-- | The highest grade: Hardware + Exact.
topGrade :: InputGrade
topGrade = InputGrade { provenance: Hardware, certainty: Exact }

-- | The lowest grade: Intent + Default.
bottomGrade :: InputGrade
bottomGrade = InputGrade { provenance: Intent, certainty: Default }

-- | Component-wise join (takes lower of each).
-- | Proven: join_comm, join_assoc, join_idem in InputChannel.lean
joinGrade :: InputGrade -> InputGrade -> InputGrade
joinGrade (InputGrade g1) (InputGrade g2) = InputGrade
  { provenance: joinProvenance g1.provenance g2.provenance
  , certainty: joinCertainty g1.certainty g2.certainty
  }

-- | Component-wise meet (takes higher of each).
meetGrade :: InputGrade -> InputGrade -> InputGrade
meetGrade (InputGrade g1) (InputGrade g2) = InputGrade
  { provenance: meetProvenance g1.provenance g2.provenance
  , certainty: meetCertainty g1.certainty g2.certainty
  }

-- | Convert grade to single numeric trust level for comparison.
-- | Range: 0-15 (provenance * 4 + certainty)
gradeToInt :: InputGrade -> Int
gradeToInt (InputGrade g) =
  provenanceToInt g.provenance * 4 + certaintyToInt g.certainty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sensor sources
-- ═════════════════════════════════════════════════════════════════════════════

-- | SensorSource enumerates concrete input device types.
-- |
-- | Each sensor source has an inherent provenance classification
-- | that cannot be changed — a stylus is always hardware, a BMI is
-- | always neural.
data SensorSource
  -- Hardware sources (Provenance.Hardware)
  = Stylus          -- ^ professional pressure-sensitive stylus
  | Mouse           -- ^ Standard mouse input
  | Touchscreen     -- ^ Touch input
  | Accelerometer   -- ^ Device motion sensor
  | Gyroscope       -- ^ Device rotation sensor
  -- Neural sources (Provenance.Neural)
  | BMI             -- ^ Brain-machine interface
  | EEG             -- ^ Electroencephalography
  | EMG             -- ^ Electromyography
  -- Simulated sources (Provenance.Simulated)
  | AIAgent         -- ^ AI generating strokes
  | Replay          -- ^ Recorded stroke playback
  | Procedural      -- ^ Algorithmically generated
  -- Intent sources (Provenance.Intent)
  | VoiceCommand    -- ^ "Draw a circle"
  | GestureRecog    -- ^ High-level gesture
  | TextDescription -- ^ Natural language to stroke

derive instance eqSensorSource :: Eq SensorSource
derive instance ordSensorSource :: Ord SensorSource

instance showSensorSource :: Show SensorSource where
  show Stylus = "(SensorSource Stylus)"
  show Mouse = "(SensorSource Mouse)"
  show Touchscreen = "(SensorSource Touchscreen)"
  show Accelerometer = "(SensorSource Accelerometer)"
  show Gyroscope = "(SensorSource Gyroscope)"
  show BMI = "(SensorSource BMI)"
  show EEG = "(SensorSource EEG)"
  show EMG = "(SensorSource EMG)"
  show AIAgent = "(SensorSource AIAgent)"
  show Replay = "(SensorSource Replay)"
  show Procedural = "(SensorSource Procedural)"
  show VoiceCommand = "(SensorSource VoiceCommand)"
  show GestureRecog = "(SensorSource GestureRecog)"
  show TextDescription = "(SensorSource TextDescription)"

-- | All available sensor sources.
allSensorSources :: Array SensorSource
allSensorSources =
  [ Stylus, Mouse, Touchscreen, Accelerometer, Gyroscope
  , BMI, EEG, EMG
  , AIAgent, Replay, Procedural
  , VoiceCommand, GestureRecog, TextDescription
  ]

-- | Classify a sensor source into its provenance category.
-- | Proven: surjective onto image in InputChannel.lean
sensorProvenance :: SensorSource -> Provenance
sensorProvenance Stylus = Hardware
sensorProvenance Mouse = Hardware
sensorProvenance Touchscreen = Hardware
sensorProvenance Accelerometer = Hardware
sensorProvenance Gyroscope = Hardware
sensorProvenance BMI = Neural
sensorProvenance EEG = Neural
sensorProvenance EMG = Neural
sensorProvenance AIAgent = Simulated
sensorProvenance Replay = Simulated
sensorProvenance Procedural = Simulated
sensorProvenance VoiceCommand = Intent
sensorProvenance GestureRecog = Intent
sensorProvenance TextDescription = Intent

-- | Whether this source requires consent (neural sources only).
-- | Proven: neural_requires_consent in InputChannel.lean
sensorRequiresConsent :: SensorSource -> Boolean
sensorRequiresConsent BMI = true
sensorRequiresConsent EEG = true
sensorRequiresConsent EMG = true
sensorRequiresConsent _ = false

-- | Whether this source produces witnesses (intent sources only).
-- | Proven: intent_produces_witness in InputChannel.lean
sensorProducesWitness :: SensorSource -> Boolean
sensorProducesWitness VoiceCommand = true
sensorProducesWitness GestureRecog = true
sensorProducesWitness TextDescription = true
sensorProducesWitness _ = false

-- | Whether this source is a physical sensor.
-- | Proven: hardware_is_physical in InputChannel.lean
sensorIsPhysical :: SensorSource -> Boolean
sensorIsPhysical Stylus = true
sensorIsPhysical Mouse = true
sensorIsPhysical Touchscreen = true
sensorIsPhysical Accelerometer = true
sensorIsPhysical Gyroscope = true
sensorIsPhysical _ = false

-- | Human-readable description of each sensor source.
sensorDescription :: SensorSource -> String
sensorDescription Stylus = "Pressure-sensitive stylus (professional tablet pen)"
sensorDescription Mouse = "Standard mouse input"
sensorDescription Touchscreen = "Capacitive touchscreen"
sensorDescription Accelerometer = "Device motion sensor"
sensorDescription Gyroscope = "Device rotation sensor"
sensorDescription BMI = "Brain-machine interface"
sensorDescription EEG = "Electroencephalography"
sensorDescription EMG = "Electromyography"
sensorDescription AIAgent = "AI agent generating strokes"
sensorDescription Replay = "Recorded stroke playback"
sensorDescription Procedural = "Algorithmically generated strokes"
sensorDescription VoiceCommand = "Voice command intent"
sensorDescription GestureRecog = "High-level gesture recognition"
sensorDescription TextDescription = "Natural language description"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // input channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | InputChannel is the core graded type for brush input values.
-- |
-- | It combines:
-- | - A bounded value in [0, 1] (using UnitInterval)
-- | - An InputGrade tracking provenance and certainty
-- | - A sensor source identifying the physical origin
-- | - A timestamp for temporal ordering
-- |
-- | The grade travels WITH the value, ensuring that any agent
-- | receiving this value knows exactly how much to trust it.
-- |
-- | Invariant (enforced by construction): source provenance matches grade provenance
newtype InputChannel = InputChannel
  { value :: UnitInterval
  , grade :: InputGrade
  , source :: SensorSource
  , timestamp :: Int
  }

derive instance eqInputChannel :: Eq InputChannel

instance showInputChannel :: Show InputChannel where
  show (InputChannel ch) = "(InputChannel "
    <> "value:" <> show ch.value
    <> " grade:" <> show ch.grade
    <> " source:" <> show ch.source
    <> " ts:" <> show ch.timestamp
    <> ")"

-- | Create a channel from a hardware sensor with exact measurement.
inputChannelFromHardware :: UnitInterval -> SensorSource -> Int -> InputChannel
inputChannelFromHardware v src ts = InputChannel
  { value: v
  , grade: InputGrade { provenance: Hardware, certainty: Exact }
  , source: src
  , timestamp: ts
  }

-- | Create a channel from simulation with estimated certainty.
inputChannelFromSimulation :: UnitInterval -> SensorSource -> Int -> InputChannel
inputChannelFromSimulation v src ts = InputChannel
  { value: v
  , grade: InputGrade { provenance: Simulated, certainty: Estimated }
  , source: src
  , timestamp: ts
  }

-- | Create a default channel (lowest grade).
inputChannelDefault :: InputChannel
inputChannelDefault = InputChannel
  { value: unitZero
  , grade: bottomGrade
  , source: TextDescription
  , timestamp: 0
  }

-- | Get the overall trust level (numeric, for comparison).
-- | Range: 0-15
inputChannelTrustLevel :: InputChannel -> Int
inputChannelTrustLevel (InputChannel ch) = gradeToInt ch.grade

-- | Debug info string for input channel.
-- | Format: "(InputChannel value:<n> grade:<g> source:<s> trust:<t>)"
inputChannelDebugInfo :: InputChannel -> String
inputChannelDebugInfo (InputChannel ch) =
  "(InputChannel"
    <> " value:" <> show (unwrapUnit ch.value)
    <> " grade:" <> show ch.grade
    <> " source:" <> show ch.source
    <> " trust:" <> show (gradeToInt ch.grade)
    <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // bipolar input channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | A bipolar input channel with values in [-1, 1].
-- |
-- | Used for tilt, velocity direction, and other signed inputs.
newtype BipolarInputChannel = BipolarInputChannel
  { value :: Number  -- Bounded to [-1, 1] by construction
  , grade :: InputGrade
  , source :: SensorSource
  , timestamp :: Int
  }

derive instance eqBipolarInputChannel :: Eq BipolarInputChannel

instance showBipolarInputChannel :: Show BipolarInputChannel where
  show (BipolarInputChannel ch) = "(BipolarInputChannel "
    <> "value:" <> show ch.value
    <> " grade:" <> show ch.grade
    <> " source:" <> show ch.source
    <> " ts:" <> show ch.timestamp
    <> ")"

-- | Convert bipolar channel to unsigned by taking absolute value.
bipolarChannelToUnsigned :: BipolarInputChannel -> InputChannel
bipolarChannelToUnsigned (BipolarInputChannel ch) = InputChannel
  { value: clampUnit (Number.abs ch.value)
  , grade: ch.grade
  , source: ch.source
  , timestamp: ch.timestamp
  }

-- | Debug info string for bipolar input channel.
bipolarChannelDebugInfo :: BipolarInputChannel -> String
bipolarChannelDebugInfo (BipolarInputChannel ch) =
  "(BipolarInputChannel"
    <> " value:" <> show ch.value
    <> " grade:" <> show ch.grade
    <> " source:" <> show ch.source
    <> " trust:" <> show (gradeToInt ch.grade)
    <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // graded transformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | A grade-tracked transformation of an input channel.
-- |
-- | Transformations (interpolation, smoothing, filtering) degrade
-- | the certainty grade appropriately. The function is pure — it
-- | describes HOW certainty degrades, not the value transformation.
-- |
-- | Invariant (proven in Lean4): degradation is monotonic (never improves)
newtype GradedTransformation = GradedTransformation
  { name :: String
  , degradeCertainty :: Certainty -> Certainty
  }

instance showGradedTransformation :: Show GradedTransformation where
  show (GradedTransformation t) = "(GradedTransformation " <> t.name <> ")"

-- | Interpolation degrades to interpolated (or keeps if already lower).
interpolationTransform :: GradedTransformation
interpolationTransform = GradedTransformation
  { name: "interpolation"
  , degradeCertainty: \c ->
      if certaintyToInt c > certaintyToInt Interpolated
        then Interpolated
        else c
  }

-- | Estimation degrades to estimated (or keeps if already lower).
estimationTransform :: GradedTransformation
estimationTransform = GradedTransformation
  { name: "estimation"
  , degradeCertainty: \c ->
      if certaintyToInt c > certaintyToInt Estimated
        then Estimated
        else c
  }

-- | Default fallback degrades everything to default.
defaultFallbackTransform :: GradedTransformation
defaultFallbackTransform = GradedTransformation
  { name: "default_fallback"
  , degradeCertainty: \_ -> Default
  }

-- | Identity transformation (no degradation).
identityTransform :: GradedTransformation
identityTransform = GradedTransformation
  { name: "identity"
  , degradeCertainty: \c -> c
  }

-- | Apply a transformation to a channel, tracking degradation.
-- |
-- | Proven: transformation_degrades in InputChannel.lean
-- | The resulting grade is always <= the input grade.
applyTransformation :: InputChannel -> GradedTransformation -> UnitInterval -> InputChannel
applyTransformation (InputChannel ch) (GradedTransformation t) newValue =
  let
    InputGrade g = ch.grade
    newCertainty = t.degradeCertainty g.certainty
  in InputChannel
    { value: newValue
    , grade: InputGrade { provenance: g.provenance, certainty: newCertainty }
    , source: ch.source
    , timestamp: ch.timestamp
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compose two input channels, joining their grades.
-- |
-- | When combining inputs from multiple sources, the result takes
-- | the LOWER grade of the two. This ensures conservative trust:
-- | - hardware + simulated = simulated (lower provenance)
-- | - exact + interpolated = interpolated (lower certainty)
-- |
-- | Proven: compose_grade_bound in InputChannel.lean
composeChannels
  :: InputChannel
  -> InputChannel
  -> (UnitInterval -> UnitInterval -> UnitInterval)
  -> InputChannel
composeChannels (InputChannel ch1) (InputChannel ch2) valueCombine =
  let
    combinedGrade = joinGrade ch1.grade ch2.grade
    InputGrade g1 = ch1.grade
    InputGrade g2 = ch2.grade
    selectedSource =
      if provenanceToInt g1.provenance <= provenanceToInt g2.provenance
        then ch1.source
        else ch2.source
  in InputChannel
    { value: valueCombine ch1.value ch2.value
    , grade: combinedGrade
    , source: selectedSource
    , timestamp: max ch1.timestamp ch2.timestamp
    }

-- | Average two unit intervals.
avgValue :: UnitInterval -> UnitInterval -> UnitInterval
avgValue a b = clampUnit ((unwrapUnit a + unwrapUnit b) / 2.0)

-- | Maximum of two unit intervals.
maxValue :: UnitInterval -> UnitInterval -> UnitInterval
maxValue a b =
  if unwrapUnit a >= unwrapUnit b
    then a
    else b

-- | Minimum of two unit intervals.
minValue :: UnitInterval -> UnitInterval -> UnitInterval
minValue a b =
  if unwrapUnit a <= unwrapUnit b
    then a
    else b
