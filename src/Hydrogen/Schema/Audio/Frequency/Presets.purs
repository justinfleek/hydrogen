-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // audio // frequency // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Predefined frequency, sample rate, and bit depth constants.
-- |
-- | This module provides commonly-used audio reference values:
-- | - Standard frequencies (A4, Middle C, frequency bands)
-- | - Sample rates (CD quality, professional, hi-res)
-- | - Bit depths (8-bit through 32-bit float)

module Hydrogen.Schema.Audio.Frequency.Presets
  ( -- * Predefined Frequencies
    a4
  , middleC
  , subBass
  , bass
  , midrange
  , presence
  , brilliance
  , nyquistCD
  , nyquist48k
  
  -- * Predefined Sample Rates
  , rate44100
  , rate48000
  , rate88200
  , rate96000
  , rate192000
  
  -- * Predefined Bit Depths
  , bit8
  , bit16
  , bit24
  , bit32
  ) where

import Hydrogen.Schema.Audio.Frequency.Types (Hertz(..), SampleRate(..), BitDepth(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // predefined frequencies
-- ═════════════════════════════════════════════════════════════════════════════

-- | A4 = 440Hz (concert pitch standard)
a4 :: Hertz
a4 = Hertz 440.0

-- | Middle C = C4 ≈ 261.63Hz (MIDI note 60)
middleC :: Hertz
middleC = Hertz 261.6255653005986

-- | Sub-bass frequency range lower bound (20Hz)
subBass :: Hertz
subBass = Hertz 20.0

-- | Bass frequency range lower bound (60Hz)
bass :: Hertz
bass = Hertz 60.0

-- | Midrange frequency (1000Hz)
midrange :: Hertz
midrange = Hertz 1000.0

-- | Presence frequency range (4000Hz)
presence :: Hertz
presence = Hertz 4000.0

-- | Brilliance/air frequency range (10000Hz)
brilliance :: Hertz
brilliance = Hertz 10000.0

-- | Nyquist frequency for CD audio (22050Hz)
nyquistCD :: Hertz
nyquistCD = Hertz 22050.0

-- | Nyquist frequency for 48kHz audio (24000Hz)
nyquist48k :: Hertz
nyquist48k = Hertz 24000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // predefined sample rates
-- ═════════════════════════════════════════════════════════════════════════════

-- | CD quality sample rate
rate44100 :: SampleRate
rate44100 = SampleRate 44100

-- | Video/broadcast standard sample rate
rate48000 :: SampleRate
rate48000 = SampleRate 48000

-- | Double CD rate (high resolution)
rate88200 :: SampleRate
rate88200 = SampleRate 88200

-- | Double video rate (high resolution)
rate96000 :: SampleRate
rate96000 = SampleRate 96000

-- | Maximum common sample rate
rate192000 :: SampleRate
rate192000 = SampleRate 192000

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // predefined bit depths
-- ═════════════════════════════════════════════════════════════════════════════

-- | 8-bit audio (lo-fi, games)
bit8 :: BitDepth
bit8 = BitDepth 8

-- | 16-bit audio (CD quality)
bit16 :: BitDepth
bit16 = BitDepth 16

-- | 24-bit audio (professional standard)
bit24 :: BitDepth
bit24 = BitDepth 24

-- | 32-bit float audio (mixing/mastering)
bit32 :: BitDepth
bit32 = BitDepth 32
