-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // audio // formant // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounds definitions for all formant-related atoms.
-- |
-- | ## Purpose
-- |
-- | Bounds define the valid ranges for each formant atom, enabling
-- | deterministic validation and clamping behavior.

module Hydrogen.Schema.Audio.Formant.Bounds
  ( -- * Formant Frequency Bounds
    f1Bounds
  , f2Bounds
  , f3Bounds
  , f4Bounds
  , f5Bounds
  
  -- * Formant Property Bounds
  , formantBandwidthBounds
  , formantAmplitudeBounds
  
  -- * Vocal Tract Bounds
  , tractLengthBounds
  , vocoderBandsBounds
  , formantShiftBounds
  ) where

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for F1
-- |
-- | Min: 150.0 Hz (close vowels)
-- | Max: 1200.0 Hz (very open vowels)
f1Bounds :: Bounded.NumberBounds
f1Bounds = Bounded.numberBounds 150.0 1200.0 Bounded.Clamps "f1" "First formant frequency in Hz (150-1200)"

-- | Bounds for F2
-- |
-- | Min: 400.0 Hz (back vowels)
-- | Max: 3000.0 Hz (front vowels)
f2Bounds :: Bounded.NumberBounds
f2Bounds = Bounded.numberBounds 400.0 3000.0 Bounded.Clamps "f2" "Second formant frequency in Hz (400-3000)"

-- | Bounds for F3
-- |
-- | Min: 1500.0 Hz
-- | Max: 4000.0 Hz
f3Bounds :: Bounded.NumberBounds
f3Bounds = Bounded.numberBounds 1500.0 4000.0 Bounded.Clamps "f3" "Third formant frequency in Hz (1500-4000)"

-- | Bounds for F4
-- |
-- | Min: 2500.0 Hz
-- | Max: 5000.0 Hz
f4Bounds :: Bounded.NumberBounds
f4Bounds = Bounded.numberBounds 2500.0 5000.0 Bounded.Clamps "f4" "Fourth formant frequency in Hz (2500-5000)"

-- | Bounds for F5
-- |
-- | Min: 3500.0 Hz
-- | Max: 6000.0 Hz
f5Bounds :: Bounded.NumberBounds
f5Bounds = Bounded.numberBounds 3500.0 6000.0 Bounded.Clamps "f5" "Fifth formant frequency in Hz (3500-6000)"

-- | Bounds for FormantBandwidth
-- |
-- | Min: 30.0 Hz (narrow)
-- | Max: 500.0 Hz (wide)
formantBandwidthBounds :: Bounded.NumberBounds
formantBandwidthBounds = Bounded.numberBounds 30.0 500.0 Bounded.Clamps "formantBandwidth" "Formant bandwidth in Hz (30-500)"

-- | Bounds for FormantAmplitude
-- |
-- | Min: 0.0 (silent)
-- | Max: 1.0 (full)
formantAmplitudeBounds :: Bounded.NumberBounds
formantAmplitudeBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "formantAmplitude" "Formant amplitude (0-1)"

-- | Bounds for TractLength
-- |
-- | Min: 8.0 cm (small child)
-- | Max: 22.0 cm (large adult)
tractLengthBounds :: Bounded.NumberBounds
tractLengthBounds = Bounded.numberBounds 8.0 22.0 Bounded.Clamps "tractLength" "Vocal tract length in cm (8-22)"

-- | Bounds for VocoderBands
-- |
-- | Min: 4 bands (low resolution)
-- | Max: 128 bands (high resolution)
vocoderBandsBounds :: Bounded.IntBounds
vocoderBandsBounds = Bounded.intBounds 4 128 Bounded.Clamps "vocoderBands" "Number of vocoder bands (4-128)"

-- | Bounds for FormantShift
-- |
-- | Min: 0.5 (lower/larger)
-- | Max: 2.0 (higher/smaller)
formantShiftBounds :: Bounded.NumberBounds
formantShiftBounds = Bounded.numberBounds 0.5 2.0 Bounded.Clamps "formantShift" "Formant shift ratio (0.5-2.0)"
