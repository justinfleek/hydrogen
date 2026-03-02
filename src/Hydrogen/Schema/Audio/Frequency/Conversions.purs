-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // audio // frequency // conversions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Conversion functions between frequency and pitch types.
-- |
-- | This module provides bidirectional conversions between:
-- | - MIDI notes and Hertz
-- | - Hertz and Kilohertz
-- | - Cents, semitones, and octaves
-- | - Intervals and frequency ratios

module Hydrogen.Schema.Audio.Frequency.Conversions
  ( -- * MIDI Conversions
    midiToHertz
  , hertzToMidi
  , midiPitchToHertz
  , hertzToMidiPitch
  
  -- * Unit Conversions
  , hertzToKilohertz
  , kilohertzToHertz
  
  -- * Interval Conversions
  , centsToSemitones
  , semitonesToCents
  , semitonesToOctaves
  , octavesToSemitones
  
  -- * Ratio Conversions
  , centsToRatio
  , ratioToCents
  , semitonesToRatio
  , ratioToSemitones
  ) where

import Prelude (otherwise, (+), (*), (-), (/), (<=))

import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Audio.Frequency.Types 
  ( Hertz(Hertz)
  , Kilohertz(Kilohertz)
  , MidiNote(MidiNote)
  , MidiPitch(MidiPitch)
  , Cent(Cent)
  , Semitone(Semitone)
  , Octave(Octave)
  , midiNote
  , midiPitch
  , cent
  , semitone
  , octave
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // midi conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert MIDI note to frequency in Hz.
-- | Formula: 440 * 2^((note - 69) / 12)
midiToHertz :: MidiNote -> Hertz
midiToHertz (MidiNote n) =
  let noteNum = Int.toNumber n
  in Hertz (440.0 * Math.pow 2.0 ((noteNum - 69.0) / 12.0))

-- | Convert frequency to nearest MIDI note.
-- | Formula: round(12 * log2(freq / 440) + 69)
-- | Returns Nothing if frequency is non-positive.
hertzToMidi :: Hertz -> Maybe MidiNote
hertzToMidi (Hertz f)
  | f <= 0.0 = Nothing
  | otherwise =
      let noteNum = Math.round (12.0 * Math.log2 (f / 440.0) + 69.0)
          clamped = Int.round noteNum
      in Just (midiNote clamped)

-- | Convert MIDI pitch (with fractional part) to frequency.
-- | Allows microtonal precision.
midiPitchToHertz :: MidiPitch -> Hertz
midiPitchToHertz (MidiPitch p) =
  Hertz (440.0 * Math.pow 2.0 ((p - 69.0) / 12.0))

-- | Convert frequency to precise MIDI pitch.
-- | Returns Nothing if frequency is non-positive.
hertzToMidiPitch :: Hertz -> Maybe MidiPitch
hertzToMidiPitch (Hertz f)
  | f <= 0.0 = Nothing
  | otherwise =
      let pitch = 12.0 * Math.log2 (f / 440.0) + 69.0
      in Just (midiPitch pitch)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // unit conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Hertz to Kilohertz
hertzToKilohertz :: Hertz -> Kilohertz
hertzToKilohertz (Hertz f) = Kilohertz (f / 1000.0)

-- | Convert Kilohertz to Hertz
kilohertzToHertz :: Kilohertz -> Hertz
kilohertzToHertz (Kilohertz k) = Hertz (k * 1000.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // interval conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert cents to semitones (100 cents = 1 semitone)
centsToSemitones :: Cent -> Semitone
centsToSemitones (Cent c) = semitone (c / 100.0)

-- | Convert semitones to cents
semitonesToCents :: Semitone -> Cent
semitonesToCents (Semitone s) = cent (s * 100.0)

-- | Convert semitones to octaves (12 semitones = 1 octave)
semitonesToOctaves :: Semitone -> Octave
semitonesToOctaves (Semitone s) = octave (s / 12.0)

-- | Convert octaves to semitones
octavesToSemitones :: Octave -> Semitone
octavesToSemitones (Octave o) = semitone (o * 12.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // ratio conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert cents to frequency ratio.
-- | Formula: 2^(cents / 1200)
centsToRatio :: Cent -> Number
centsToRatio (Cent c) = Math.pow 2.0 (c / 1200.0)

-- | Convert frequency ratio to cents.
-- | Formula: 1200 * log2(ratio)
ratioToCents :: Number -> Cent
ratioToCents ratio
  | ratio <= 0.0 = Cent 0.0
  | otherwise = cent (1200.0 * Math.log2 ratio)

-- | Convert semitones to frequency ratio.
-- | Formula: 2^(semitones / 12)
semitonesToRatio :: Semitone -> Number
semitonesToRatio (Semitone s) = Math.pow 2.0 (s / 12.0)

-- | Convert frequency ratio to semitones.
-- | Formula: 12 * log2(ratio)
ratioToSemitones :: Number -> Semitone
ratioToSemitones ratio
  | ratio <= 0.0 = Semitone 0.0
  | otherwise = semitone (12.0 * Math.log2 ratio)
