-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // audio // frequency // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frequency manipulation operations.
-- |
-- | This module provides functions for:
-- | - Transposition by octaves, semitones, or cents
-- | - Calculating frequency ratios and intervals

module Hydrogen.Schema.Audio.Frequency.Operations
  ( -- * Transposition
    transposeByOctave
  , transposeBySemitone
  , transposeByCent
  
  -- * Interval Calculation
  , frequencyRatio
  , intervalInCents
  , intervalInSemitones
  ) where

import Prelude (otherwise, (*), (/), (<=))

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Audio.Frequency.Types 
  ( Hertz(..)
  , Cent(..)
  , Semitone(..)
  , Octave(..)
  , hertz
  , cent
  , semitone
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // transposition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transpose a frequency by octaves.
-- | Positive = higher, negative = lower.
transposeByOctave :: Octave -> Hertz -> Hertz
transposeByOctave (Octave o) (Hertz f) =
  hertz (f * Math.pow 2.0 o)

-- | Transpose a frequency by semitones.
transposeBySemitone :: Semitone -> Hertz -> Hertz
transposeBySemitone (Semitone s) (Hertz f) =
  hertz (f * Math.pow 2.0 (s / 12.0))

-- | Transpose a frequency by cents.
transposeByCent :: Cent -> Hertz -> Hertz
transposeByCent (Cent c) (Hertz f) =
  hertz (f * Math.pow 2.0 (c / 1200.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // interval calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate the frequency ratio between two frequencies.
-- | Result is f2/f1. Returns 0 if f1 is zero.
frequencyRatio :: Hertz -> Hertz -> Number
frequencyRatio (Hertz f1) (Hertz f2)
  | f1 <= 0.0 = 0.0
  | otherwise = f2 / f1

-- | Calculate the interval in cents between two frequencies.
intervalInCents :: Hertz -> Hertz -> Cent
intervalInCents (Hertz f1) (Hertz f2)
  | f1 <= 0.0 = Cent 0.0
  | f2 <= 0.0 = Cent 0.0
  | otherwise = cent (1200.0 * Math.log2 (f2 / f1))

-- | Calculate the interval in semitones between two frequencies.
intervalInSemitones :: Hertz -> Hertz -> Semitone
intervalInSemitones (Hertz f1) (Hertz f2)
  | f1 <= 0.0 = Semitone 0.0
  | f2 <= 0.0 = Semitone 0.0
  | otherwise = semitone (12.0 * Math.log2 (f2 / f1))
