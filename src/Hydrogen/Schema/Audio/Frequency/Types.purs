-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // audio // frequency // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core frequency and pitch type definitions.
-- |
-- | This module contains all newtypes for frequency-related atoms:
-- | - Hertz/Kilohertz for frequency measurement
-- | - MidiNote/MidiPitch for MIDI pitch representation
-- | - Cent/Semitone/Octave for interval measurement
-- | - SampleRate/BitDepth for digital audio parameters

module Hydrogen.Schema.Audio.Frequency.Types
  ( -- * Frequency Types
    Hertz(Hertz)
  , Kilohertz(Kilohertz)
  
  -- * MIDI Types
  , MidiNote(MidiNote)
  , MidiPitch(MidiPitch)
  
  -- * Interval Types
  , Cent(Cent)
  , Semitone(Semitone)
  , Octave(Octave)
  
  -- * Digital Audio Types
  , SampleRate(SampleRate)
  , BitDepth(BitDepth)
  
  -- * Constructors
  , hertz
  , kilohertz
  , midiNote
  , midiPitch
  , cent
  , semitone
  , octave
  , sampleRate
  , bitDepth
  
  -- * Accessors
  , unwrapHertz
  , unwrapKilohertz
  , unwrapMidiNote
  , unwrapMidiPitch
  , unwrapCent
  , unwrapSemitone
  , unwrapOctave
  , unwrapSampleRate
  , unwrapBitDepth
  ) where

import Prelude (class Eq, class Ord, class Show, negate, otherwise, show, (<), (>), (<>))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // hertz
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hertz - frequency in cycles per second.
-- | Clamped to [0, ∞) - no negative frequencies.
-- | Practical audio range: 20Hz - 20000Hz (human hearing)
newtype Hertz = Hertz Number

derive instance eqHertz :: Eq Hertz
derive instance ordHertz :: Ord Hertz

instance showHertz :: Show Hertz where
  show (Hertz n) = show n <> " Hz"

-- | Create a Hertz value (clamped to non-negative)
hertz :: Number -> Hertz
hertz n
  | n < 0.0 = Hertz 0.0
  | otherwise = Hertz n

unwrapHertz :: Hertz -> Number
unwrapHertz (Hertz n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // kilohertz
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kilohertz - frequency in thousands of cycles per second.
-- | Useful for higher frequencies and sample rates.
newtype Kilohertz = Kilohertz Number

derive instance eqKilohertz :: Eq Kilohertz
derive instance ordKilohertz :: Ord Kilohertz

instance showKilohertz :: Show Kilohertz where
  show (Kilohertz n) = show n <> " kHz"

-- | Create a Kilohertz value (clamped to non-negative)
kilohertz :: Number -> Kilohertz
kilohertz n
  | n < 0.0 = Kilohertz 0.0
  | otherwise = Kilohertz n

unwrapKilohertz :: Kilohertz -> Number
unwrapKilohertz (Kilohertz n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // midi note
-- ═════════════════════════════════════════════════════════════════════════════

-- | MidiNote - MIDI note number (0-127).
-- | 60 = Middle C (C4), 69 = A4 (440Hz reference).
-- | Each increment is one semitone.
newtype MidiNote = MidiNote Int

derive instance eqMidiNote :: Eq MidiNote
derive instance ordMidiNote :: Ord MidiNote

instance showMidiNote :: Show MidiNote where
  show (MidiNote n) = "MIDI " <> show n

-- | Create a MidiNote value (clamped to 0-127)
midiNote :: Int -> MidiNote
midiNote n
  | n < 0 = MidiNote 0
  | n > 127 = MidiNote 127
  | otherwise = MidiNote n

unwrapMidiNote :: MidiNote -> Int
unwrapMidiNote (MidiNote n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // midi pitch
-- ═════════════════════════════════════════════════════════════════════════════

-- | MidiPitch - MIDI note with fractional pitch bend.
-- | Allows micro-tonal precision (e.g., 60.5 = C4 + 50 cents).
-- | Clamped to [0.0, 127.99].
newtype MidiPitch = MidiPitch Number

derive instance eqMidiPitch :: Eq MidiPitch
derive instance ordMidiPitch :: Ord MidiPitch

instance showMidiPitch :: Show MidiPitch where
  show (MidiPitch n) = "MIDI " <> show n

-- | Create a MidiPitch value (clamped to 0.0-127.99)
midiPitch :: Number -> MidiPitch
midiPitch n
  | n < 0.0 = MidiPitch 0.0
  | n > 127.99 = MidiPitch 127.99
  | otherwise = MidiPitch n

unwrapMidiPitch :: MidiPitch -> Number
unwrapMidiPitch (MidiPitch n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // cent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cent - pitch offset in cents (1/100 of a semitone).
-- | Clamped to [-100, 100] for single-semitone adjustments.
-- | 100 cents = 1 semitone.
newtype Cent = Cent Number

derive instance eqCent :: Eq Cent
derive instance ordCent :: Ord Cent

instance showCent :: Show Cent where
  show (Cent n) = show n <> " cents"

-- | Create a Cent value (clamped to -100 to 100)
cent :: Number -> Cent
cent n
  | n < (-100.0) = Cent (-100.0)
  | n > 100.0 = Cent 100.0
  | otherwise = Cent n

unwrapCent :: Cent -> Number
unwrapCent (Cent n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // semitone
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semitone - pitch offset in semitones (half steps).
-- | Clamped to [-12, 12] for single-octave adjustments.
-- | 12 semitones = 1 octave.
newtype Semitone = Semitone Number

derive instance eqSemitone :: Eq Semitone
derive instance ordSemitone :: Ord Semitone

instance showSemitone :: Show Semitone where
  show (Semitone n) = show n <> " semitones"

-- | Create a Semitone value (clamped to -12 to 12)
semitone :: Number -> Semitone
semitone n
  | n < (-12.0) = Semitone (-12.0)
  | n > 12.0 = Semitone 12.0
  | otherwise = Semitone n

unwrapSemitone :: Semitone -> Number
unwrapSemitone (Semitone n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // octave
-- ═════════════════════════════════════════════════════════════════════════════

-- | Octave - pitch offset in octaves.
-- | Clamped to [-10, 10] for practical range.
-- | 1 octave = 12 semitones = frequency × 2.
newtype Octave = Octave Number

derive instance eqOctave :: Eq Octave
derive instance ordOctave :: Ord Octave

instance showOctave :: Show Octave where
  show (Octave n) = show n <> " octaves"

-- | Create an Octave value (clamped to -10 to 10)
octave :: Number -> Octave
octave n
  | n < (-10.0) = Octave (-10.0)
  | n > 10.0 = Octave 10.0
  | otherwise = Octave n

unwrapOctave :: Octave -> Number
unwrapOctave (Octave n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sample rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | SampleRate - audio sample rate in Hz.
-- | Clamped to [8000, 192000] covering all practical rates.
-- | Common: 44100 (CD), 48000 (video), 96000 (hi-res).
newtype SampleRate = SampleRate Int

derive instance eqSampleRate :: Eq SampleRate
derive instance ordSampleRate :: Ord SampleRate

instance showSampleRate :: Show SampleRate where
  show (SampleRate n) = show n <> " Hz"

-- | Create a SampleRate value (clamped to 8000-192000)
sampleRate :: Int -> SampleRate
sampleRate n
  | n < 8000 = SampleRate 8000
  | n > 192000 = SampleRate 192000
  | otherwise = SampleRate n

unwrapSampleRate :: SampleRate -> Int
unwrapSampleRate (SampleRate n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bit depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | BitDepth - bits per sample.
-- | Clamped to [8, 32] covering all practical depths.
-- | Common: 16 (CD), 24 (professional), 32 (float).
newtype BitDepth = BitDepth Int

derive instance eqBitDepth :: Eq BitDepth
derive instance ordBitDepth :: Ord BitDepth

instance showBitDepth :: Show BitDepth where
  show (BitDepth n) = show n <> "-bit"

-- | Create a BitDepth value (clamped to 8-32)
bitDepth :: Int -> BitDepth
bitDepth n
  | n < 8 = BitDepth 8
  | n > 32 = BitDepth 32
  | otherwise = BitDepth n

unwrapBitDepth :: BitDepth -> Int
unwrapBitDepth (BitDepth n) = n
