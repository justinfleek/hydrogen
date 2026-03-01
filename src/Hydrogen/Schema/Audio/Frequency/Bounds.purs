-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // audio // frequency // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounds definitions for all frequency-related types.
-- |
-- | This module provides Bounded instances and bound specifications
-- | for use with the schema validation system.

module Hydrogen.Schema.Audio.Frequency.Bounds
  ( -- * Frequency Bounds
    hertzBounds
  , kilohertzBounds
  
  -- * MIDI Bounds
  , midiNoteBounds
  , midiPitchBounds
  
  -- * Interval Bounds
  , centBounds
  , semitoneBounds
  , octaveBounds
  
  -- * Digital Audio Bounds
  , sampleRateBounds
  , bitDepthBounds
  ) where

import Prelude (negate)

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // frequency bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Hertz (practical audio range)
-- |
-- | Min: 0.0
-- | Max: 20000.0 (human hearing upper limit)
hertzBounds :: Bounded.NumberBounds
hertzBounds = Bounded.numberBounds 0.0 20000.0 Bounded.Clamps "hertz" "Frequency in Hz (0-20000)"

-- | Bounds for Kilohertz
-- |
-- | Min: 0.0
-- | Max: 20.0 (20kHz human hearing limit)
kilohertzBounds :: Bounded.NumberBounds
kilohertzBounds = Bounded.numberBounds 0.0 20.0 Bounded.Clamps "kilohertz" "Frequency in kHz (0-20)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // midi bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for MidiNote
-- |
-- | Min: 0
-- | Max: 127
midiNoteBounds :: Bounded.IntBounds
midiNoteBounds = Bounded.intBounds 0 127 Bounded.Clamps "midiNote" "MIDI note number (0-127)"

-- | Bounds for MidiPitch
-- |
-- | Min: 0.0
-- | Max: 127.99
midiPitchBounds :: Bounded.NumberBounds
midiPitchBounds = Bounded.numberBounds 0.0 127.99 Bounded.Clamps "midiPitch" "MIDI pitch with microtonal (0-127.99)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // interval bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Cent
-- |
-- | Min: -100.0 (one semitone down)
-- | Max: 100.0 (one semitone up)
centBounds :: Bounded.NumberBounds
centBounds = Bounded.numberBounds (-100.0) 100.0 Bounded.Clamps "cent" "Pitch offset in cents (-100 to 100)"

-- | Bounds for Semitone
-- |
-- | Min: -12.0 (one octave down)
-- | Max: 12.0 (one octave up)
semitoneBounds :: Bounded.NumberBounds
semitoneBounds = Bounded.numberBounds (-12.0) 12.0 Bounded.Clamps "semitone" "Pitch offset in semitones (-12 to 12)"

-- | Bounds for Octave
-- |
-- | Min: -10.0
-- | Max: 10.0
octaveBounds :: Bounded.NumberBounds
octaveBounds = Bounded.numberBounds (-10.0) 10.0 Bounded.Clamps "octave" "Pitch offset in octaves (-10 to 10)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // digital audio bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for SampleRate
-- |
-- | Min: 8000 (telephony)
-- | Max: 96000 (high-resolution audio)
sampleRateBounds :: Bounded.IntBounds
sampleRateBounds = Bounded.intBounds 8000 96000 Bounded.Clamps "sampleRate" "Audio sample rate in Hz (8000-96000)"

-- | Bounds for BitDepth
-- |
-- | Min: 8 (lo-fi)
-- | Max: 32 (float)
bitDepthBounds :: Bounded.IntBounds
bitDepthBounds = Bounded.intBounds 8 32 Bounded.Clamps "bitDepth" "Bits per sample (8-32)"
