-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // audio // daw // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DAW Types — Bounded Audio Primitives for CHAD
-- |
-- | Every audio parameter has STRICT BOUNDS. No one turns the volume to 100000dB.
-- | No frequencies outside human hearing. No BPM that causes seizures.
-- |
-- | These are the atoms CHAD uses to produce music safely.
-- |
-- | ## Safety Invariants
-- |
-- | - Decibel: -∞ to +12dB (master), -∞ to +24dB (channel)
-- | - Frequency: 20Hz to 20kHz (human hearing)
-- | - BPM: 20 to 300 (musical range)
-- | - Pan: -1.0 (left) to +1.0 (right)
-- |
-- | ## Reference
-- | CHAD autonomous DJ system — docs/INTERNAL/CHAD_DJ.md
module Hydrogen.Audio.DAW.Types
  ( -- * Volume & Gain
    Decibel
  , mkDecibel
  , mkDecibelMaster
  , mkDecibelChannel
  , decibelValue
  , decibelToLinear
  , linearToDecibel
  , silence
  , unity
    -- * Frequency
  , Frequency
  , mkFrequency
  , frequencyValue
  , frequencyHz
  , frequencyKHz
  , midiToFrequency
  , frequencyToMidi
  , freq1k
    -- * Tempo
  , BPM
  , mkBPM
  , bpmValue
  , beatsPerSecond
  , msPerBeat
    -- * Panning
  , Pan
  , mkPan
  , panValue
  , panLeft
  , panCenter
  , panRight
    -- * Time
  , SampleRate
  , mkSampleRate
  , sampleRateValue
  , standardRates
  , Samples
  , mkSamples
  , samplesValue
  , samplesToMs
  , msToSamples
    -- * Musical
  , Octave
  , mkOctave
  , octaveValue
  , Semitone
  , mkSemitone
  , semitoneValue
  , Cents
  , mkCents
  , centsValue
    -- * Dynamics
  , Velocity
  , mkVelocity
  , velocityValue
  , velocityToLinear
  ) where

import Prelude

import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(..))
import Data.Number (pow, log, ln2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // decibel (volume)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Decibel — Bounded volume level
-- |
-- | Range: -96dB (near silence) to +24dB (max boost)
-- | -96dB chosen because it's effectively inaudible (-∞ conceptually)
newtype Decibel = Decibel Number

derive instance eqDecibel :: Eq Decibel
derive instance ordDecibel :: Ord Decibel

instance showDecibel :: Show Decibel where
  show (Decibel db) = "(Decibel " <> show db <> ")"

-- | Create a Decibel with full range (-96 to +24)
mkDecibel :: Number -> Maybe Decibel
mkDecibel db
  | db >= -96.0 && db <= 24.0 = Just (Decibel db)
  | otherwise = Nothing

-- | Master bus limit: -96 to +12dB (protect ears)
mkDecibelMaster :: Number -> Maybe Decibel
mkDecibelMaster db
  | db >= -96.0 && db <= 12.0 = Just (Decibel db)
  | otherwise = Nothing

-- | Channel limit: -96 to +24dB (more headroom for mixing)
mkDecibelChannel :: Number -> Maybe Decibel
mkDecibelChannel db
  | db >= -96.0 && db <= 24.0 = Just (Decibel db)
  | otherwise = Nothing

decibelValue :: Decibel -> Number
decibelValue (Decibel db) = db

-- | Convert dB to linear amplitude (0.0 to ~15.85)
decibelToLinear :: Decibel -> Number
decibelToLinear (Decibel db) = pow 10.0 (db / 20.0)

-- | Convert linear amplitude to dB
linearToDecibel :: Number -> Maybe Decibel
linearToDecibel linear
  | linear <= 0.0 = Just (Decibel (-96.0))  -- Silence
  | otherwise = mkDecibel (20.0 * (log linear / ln10))
  where
    ln10 = log 10.0

-- | Silence (-96dB)
silence :: Decibel
silence = Decibel (-96.0)

-- | Unity gain (0dB)
unity :: Decibel
unity = Decibel 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // frequency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frequency — Bounded to human hearing range
-- |
-- | Range: 20Hz to 20,000Hz (20kHz)
-- | Subsonic and ultrasonic frequencies rejected
newtype Frequency = Frequency Number

derive instance eqFrequency :: Eq Frequency
derive instance ordFrequency :: Ord Frequency

instance showFrequency :: Show Frequency where
  show (Frequency hz) = "(Frequency " <> show hz <> "Hz)"

-- | Create a Frequency within human hearing (20Hz - 20kHz)
mkFrequency :: Number -> Maybe Frequency
mkFrequency hz
  | hz >= 20.0 && hz <= 20000.0 = Just (Frequency hz)
  | otherwise = Nothing

frequencyValue :: Frequency -> Number
frequencyValue (Frequency hz) = hz

-- | Create from Hz
frequencyHz :: Number -> Maybe Frequency
frequencyHz = mkFrequency

-- | Create from kHz
frequencyKHz :: Number -> Maybe Frequency
frequencyKHz khz = mkFrequency (khz * 1000.0)

-- | MIDI note to frequency (A4 = 440Hz = MIDI 69)
midiToFrequency :: Int -> Maybe Frequency
midiToFrequency midi
  | midi >= 0 && midi <= 127 = 
      let hz = 440.0 * pow 2.0 ((toNumber midi - 69.0) / 12.0)
      in mkFrequency hz
  | otherwise = Nothing

-- | Frequency to nearest MIDI note
frequencyToMidi :: Frequency -> Int
frequencyToMidi (Frequency hz) =
  floor (12.0 * (log (hz / 440.0) / ln2) + 69.0)

-- | 1kHz reference frequency (standard audio test tone)
freq1k :: Frequency
freq1k = Frequency 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                          // bpm
-- ═════════════════════════════════════════════════════════════════════════════

-- | BPM — Bounded tempo
-- |
-- | Range: 20 to 300 BPM
-- | Below 20: too slow to be musical
-- | Above 300: unsafe (strobing, seizure risk at high visual sync)
newtype BPM = BPM Number

derive instance eqBPM :: Eq BPM
derive instance ordBPM :: Ord BPM

instance showBPM :: Show BPM where
  show (BPM bpm) = "(BPM " <> show bpm <> ")"

-- | Create BPM within safe musical range
mkBPM :: Number -> Maybe BPM
mkBPM bpm
  | bpm >= 20.0 && bpm <= 300.0 = Just (BPM bpm)
  | otherwise = Nothing

bpmValue :: BPM -> Number
bpmValue (BPM bpm) = bpm

-- | Beats per second
beatsPerSecond :: BPM -> Number
beatsPerSecond (BPM bpm) = bpm / 60.0

-- | Milliseconds per beat
msPerBeat :: BPM -> Number
msPerBeat (BPM bpm) = 60000.0 / bpm

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                          // pan
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pan — Stereo position
-- |
-- | Range: -1.0 (hard left) to +1.0 (hard right)
-- | 0.0 = center
newtype Pan = Pan Number

derive instance eqPan :: Eq Pan
derive instance ordPan :: Ord Pan

instance showPan :: Show Pan where
  show (Pan p) = "(Pan " <> show p <> ")"

mkPan :: Number -> Maybe Pan
mkPan p
  | p >= -1.0 && p <= 1.0 = Just (Pan p)
  | otherwise = Nothing

panValue :: Pan -> Number
panValue (Pan p) = p

panLeft :: Pan
panLeft = Pan (-1.0)

panCenter :: Pan
panCenter = Pan 0.0

panRight :: Pan
panRight = Pan 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sample rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample Rate — Audio sampling frequency
-- |
-- | Common rates: 44100, 48000, 88200, 96000, 176400, 192000
newtype SampleRate = SampleRate Int

derive instance eqSampleRate :: Eq SampleRate
derive instance ordSampleRate :: Ord SampleRate

instance showSampleRate :: Show SampleRate where
  show (SampleRate sr) = "(SampleRate " <> show sr <> ")"

mkSampleRate :: Int -> Maybe SampleRate
mkSampleRate sr
  | sr >= 8000 && sr <= 384000 = Just (SampleRate sr)
  | otherwise = Nothing

sampleRateValue :: SampleRate -> Int
sampleRateValue (SampleRate sr) = sr

-- | Standard sample rates
standardRates :: { cd :: SampleRate, dvd :: SampleRate, hd :: SampleRate }
standardRates =
  { cd: SampleRate 44100
  , dvd: SampleRate 48000
  , hd: SampleRate 96000
  }

-- | Sample count
newtype Samples = Samples Int

derive instance eqSamples :: Eq Samples
derive instance ordSamples :: Ord Samples

mkSamples :: Int -> Maybe Samples
mkSamples s
  | s >= 0 = Just (Samples s)
  | otherwise = Nothing

samplesValue :: Samples -> Int
samplesValue (Samples s) = s

-- | Convert samples to milliseconds at given sample rate
samplesToMs :: SampleRate -> Samples -> Number
samplesToMs (SampleRate sr) (Samples s) =
  (toNumber s / toNumber sr) * 1000.0

-- | Convert milliseconds to samples at given sample rate
msToSamples :: SampleRate -> Number -> Samples
msToSamples (SampleRate sr) ms =
  Samples (floor ((ms / 1000.0) * toNumber sr))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // musical
-- ═════════════════════════════════════════════════════════════════════════════

-- | Octave — Musical octave (0-10)
-- |
-- | Octave 4 contains middle C (C4 = 261.63Hz)
newtype Octave = Octave Int

derive instance eqOctave :: Eq Octave
derive instance ordOctave :: Ord Octave

mkOctave :: Int -> Maybe Octave
mkOctave o
  | o >= 0 && o <= 10 = Just (Octave o)
  | otherwise = Nothing

octaveValue :: Octave -> Int
octaveValue (Octave o) = o

-- | Semitone — Half step (0-11 within octave)
newtype Semitone = Semitone Int

derive instance eqSemitone :: Eq Semitone
derive instance ordSemitone :: Ord Semitone

mkSemitone :: Int -> Maybe Semitone
mkSemitone s
  | s >= 0 && s <= 11 = Just (Semitone s)
  | otherwise = Nothing

semitoneValue :: Semitone -> Int
semitoneValue (Semitone s) = s

-- | Cents — Fine tuning (-100 to +100 cents)
-- |
-- | 100 cents = 1 semitone
newtype Cents = Cents Int

derive instance eqCents :: Eq Cents
derive instance ordCents :: Ord Cents

mkCents :: Int -> Maybe Cents
mkCents c
  | c >= -100 && c <= 100 = Just (Cents c)
  | otherwise = Nothing

centsValue :: Cents -> Int
centsValue (Cents c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity — MIDI velocity / key strike intensity
-- |
-- | Range: 0-127 (MIDI standard)
newtype Velocity = Velocity Int

derive instance eqVelocity :: Eq Velocity
derive instance ordVelocity :: Ord Velocity

instance showVelocity :: Show Velocity where
  show (Velocity v) = "(Velocity " <> show v <> ")"

mkVelocity :: Int -> Maybe Velocity
mkVelocity v
  | v >= 0 && v <= 127 = Just (Velocity v)
  | otherwise = Nothing

velocityValue :: Velocity -> Int
velocityValue (Velocity v) = v

-- | Convert velocity to linear amplitude (0.0 to 1.0)
velocityToLinear :: Velocity -> Number
velocityToLinear (Velocity v) = toNumber v / 127.0
