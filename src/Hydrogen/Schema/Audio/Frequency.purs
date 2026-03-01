-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // audio // frequency
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frequency and pitch atoms for audio processing.
-- |
-- | ## MIDI Note System
-- | MIDI note numbers span 0-127, where 60 is Middle C (C4) and 69 is A4 (440Hz).
-- | The formula: frequency = 440 * 2^((note - 69) / 12)
-- |
-- | ## Cents and Semitones
-- | Musical intervals are measured in semitones (half steps) and cents.
-- | 1 semitone = 100 cents = factor of 2^(1/12) ≈ 1.0595
-- | 1 octave = 12 semitones = 1200 cents = factor of 2
-- |
-- | ## Sample Rate and Bit Depth
-- | Digital audio parameters: CD quality is 44100Hz/16-bit,
-- | professional is 48000Hz or 96000Hz/24-bit.
-- |
-- | ## Module Structure
-- | This is a leader module that re-exports all submodules:
-- | - Types: Core newtypes and constructors
-- | - Presets: Predefined frequency/rate/depth constants
-- | - Conversions: Unit and format conversions
-- | - Operations: Transposition and interval calculations
-- | - Notes: Musical note names and MIDI mapping
-- | - Bounds: Bounded specifications for validation

module Hydrogen.Schema.Audio.Frequency
  ( module Types
  , module Presets
  , module Conversions
  , module Operations
  , module Notes
  , module Bounds
  ) where

import Hydrogen.Schema.Audio.Frequency.Types as Types
import Hydrogen.Schema.Audio.Frequency.Presets as Presets
import Hydrogen.Schema.Audio.Frequency.Conversions as Conversions
import Hydrogen.Schema.Audio.Frequency.Operations as Operations
import Hydrogen.Schema.Audio.Frequency.Notes as Notes
import Hydrogen.Schema.Audio.Frequency.Bounds as Bounds
