-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // audio // formant // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core formant frequency atoms and related types.
-- |
-- | ## Formant Frequencies
-- |
-- | Formants F1-F5 represent resonant frequencies of the vocal tract.
-- | Each formant has bounded ranges based on acoustic phonetics research.

module Hydrogen.Schema.Audio.Formant.Types
  ( -- * Formant Frequency Atoms
    F1(F1)
  , F2(F2)
  , F3(F3)
  , F4(F4)
  , F5(F5)
  , f1
  , f2
  , f3
  , f4
  , f5
  , unwrapF1
  , unwrapF2
  , unwrapF3
  , unwrapF4
  , unwrapF5
  
  -- * Formant Bandwidth
  , FormantBandwidth(FormantBandwidth)
  , formantBandwidth
  , unwrapFormantBandwidth
  , bandwidthNarrow
  , bandwidthMedium
  , bandwidthWide
  
  -- * Formant Amplitude
  , FormantAmplitude(FormantAmplitude)
  , formantAmplitude
  , unwrapFormantAmplitude
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (*)
  , (<)
  , (>)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // formant frequencies
-- ═════════════════════════════════════════════════════════════════════════════

-- | F1 - First formant frequency in Hz.
-- | Corresponds to tongue height: low F1 = close (high tongue),
-- | high F1 = open (low tongue). Range ~200-1000 Hz.
newtype F1 = F1 Number

derive instance eqF1 :: Eq F1
derive instance ordF1 :: Ord F1

instance showF1 :: Show F1 where
  show (F1 n) = "F1: " <> show n <> " Hz"

-- | Create an F1 value (clamped to 150-1200)
f1 :: Number -> F1
f1 n
  | n < 150.0 = F1 150.0
  | n > 1200.0 = F1 1200.0
  | otherwise = F1 n

unwrapF1 :: F1 -> Number
unwrapF1 (F1 n) = n

-- | F2 - Second formant frequency in Hz.
-- | Corresponds to tongue frontness: high F2 = front vowel,
-- | low F2 = back vowel. Range ~500-2500 Hz.
newtype F2 = F2 Number

derive instance eqF2 :: Eq F2
derive instance ordF2 :: Ord F2

instance showF2 :: Show F2 where
  show (F2 n) = "F2: " <> show n <> " Hz"

-- | Create an F2 value (clamped to 400-3000)
f2 :: Number -> F2
f2 n
  | n < 400.0 = F2 400.0
  | n > 3000.0 = F2 3000.0
  | otherwise = F2 n

unwrapF2 :: F2 -> Number
unwrapF2 (F2 n) = n

-- | F3 - Third formant frequency in Hz.
-- | Affects vowel "color" and speaker identity. Range ~2000-3500 Hz.
newtype F3 = F3 Number

derive instance eqF3 :: Eq F3
derive instance ordF3 :: Ord F3

instance showF3 :: Show F3 where
  show (F3 n) = "F3: " <> show n <> " Hz"

-- | Create an F3 value (clamped to 1500-4000)
f3 :: Number -> F3
f3 n
  | n < 1500.0 = F3 1500.0
  | n > 4000.0 = F3 4000.0
  | otherwise = F3 n

unwrapF3 :: F3 -> Number
unwrapF3 (F3 n) = n

-- | F4 - Fourth formant frequency in Hz.
-- | Contributes to speaker identification and voice quality.
newtype F4 = F4 Number

derive instance eqF4 :: Eq F4
derive instance ordF4 :: Ord F4

instance showF4 :: Show F4 where
  show (F4 n) = "F4: " <> show n <> " Hz"

-- | Create an F4 value (clamped to 2500-5000)
f4 :: Number -> F4
f4 n
  | n < 2500.0 = F4 2500.0
  | n > 5000.0 = F4 5000.0
  | otherwise = F4 n

unwrapF4 :: F4 -> Number
unwrapF4 (F4 n) = n

-- | F5 - Fifth formant frequency in Hz.
-- | Higher formants add "presence" and naturalness.
newtype F5 = F5 Number

derive instance eqF5 :: Eq F5
derive instance ordF5 :: Ord F5

instance showF5 :: Show F5 where
  show (F5 n) = "F5: " <> show n <> " Hz"

-- | Create an F5 value (clamped to 3500-6000)
f5 :: Number -> F5
f5 n
  | n < 3500.0 = F5 3500.0
  | n > 6000.0 = F5 6000.0
  | otherwise = F5 n

unwrapF5 :: F5 -> Number
unwrapF5 (F5 n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // formant bandwidth
-- ═════════════════════════════════════════════════════════════════════════════

-- | FormantBandwidth - width of formant resonance in Hz.
-- | Narrow bandwidths = more resonant, nasal quality.
-- | Wide bandwidths = less resonant, more natural.
newtype FormantBandwidth = FormantBandwidth Number

derive instance eqFormantBandwidth :: Eq FormantBandwidth
derive instance ordFormantBandwidth :: Ord FormantBandwidth

instance showFormantBandwidth :: Show FormantBandwidth where
  show (FormantBandwidth n) = show n <> " Hz bandwidth"

-- | Create a FormantBandwidth value (clamped to 30-500)
formantBandwidth :: Number -> FormantBandwidth
formantBandwidth n
  | n < 30.0 = FormantBandwidth 30.0
  | n > 500.0 = FormantBandwidth 500.0
  | otherwise = FormantBandwidth n

unwrapFormantBandwidth :: FormantBandwidth -> Number
unwrapFormantBandwidth (FormantBandwidth n) = n

-- | Narrow bandwidth (resonant, focused)
bandwidthNarrow :: FormantBandwidth
bandwidthNarrow = FormantBandwidth 60.0

-- | Medium bandwidth (natural speech)
bandwidthMedium :: FormantBandwidth
bandwidthMedium = FormantBandwidth 120.0

-- | Wide bandwidth (relaxed, breathy)
bandwidthWide :: FormantBandwidth
bandwidthWide = FormantBandwidth 200.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // formant amplitude
-- ═════════════════════════════════════════════════════════════════════════════

-- | FormantAmplitude - relative amplitude of a formant.
-- | 0.0 = silent, 1.0 = full amplitude.
-- | Different formant amplitudes affect vowel perception.
newtype FormantAmplitude = FormantAmplitude Number

derive instance eqFormantAmplitude :: Eq FormantAmplitude
derive instance ordFormantAmplitude :: Ord FormantAmplitude

instance showFormantAmplitude :: Show FormantAmplitude where
  show (FormantAmplitude n) = show (n * 100.0) <> "% amplitude"

-- | Create a FormantAmplitude value (clamped to 0.0-1.0)
formantAmplitude :: Number -> FormantAmplitude
formantAmplitude n
  | n < 0.0 = FormantAmplitude 0.0
  | n > 1.0 = FormantAmplitude 1.0
  | otherwise = FormantAmplitude n

unwrapFormantAmplitude :: FormantAmplitude -> Number
unwrapFormantAmplitude (FormantAmplitude n) = n
