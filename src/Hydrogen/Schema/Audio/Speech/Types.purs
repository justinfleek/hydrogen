-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // audio // speech // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core speech analysis types: confidence, timing, and bounds.
-- |
-- | These atoms form the foundation for all speech recognition and analysis.
-- | Confidence scores, word timing, and phoneme duration are used throughout
-- | the speech processing pipeline.

module Hydrogen.Schema.Audio.Speech.Types
  ( -- * Confidence Atoms
    Confidence(..)
  , confidence
  , unwrapConfidence
  , confidenceHigh
  , confidenceMedium
  , confidenceLow
  
  -- * Timing Atoms
  , WordStart(..)
  , WordEnd(..)
  , PhonemeDuration(..)
  , wordStart
  , wordEnd
  , phonemeDuration
  , unwrapWordStart
  , unwrapWordEnd
  , unwrapPhonemeDuration
  
  -- * Bounds
  , confidenceBounds
  , wordStartBounds
  , wordEndBounds
  , phonemeDurationBounds
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

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // confidence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Confidence - recognition confidence score.
-- | 0.0 = no confidence (random guess), 1.0 = certain.
-- | Values below 0.5 typically indicate unreliable recognition.
newtype Confidence = Confidence Number

derive instance eqConfidence :: Eq Confidence
derive instance ordConfidence :: Ord Confidence

instance showConfidence :: Show Confidence where
  show (Confidence n) = show (n * 100.0) <> "% confidence"

-- | Create a Confidence value (clamped to 0.0-1.0)
confidence :: Number -> Confidence
confidence n
  | n < 0.0 = Confidence 0.0
  | n > 1.0 = Confidence 1.0
  | otherwise = Confidence n

unwrapConfidence :: Confidence -> Number
unwrapConfidence (Confidence n) = n

-- | High confidence (0.9)
confidenceHigh :: Confidence
confidenceHigh = Confidence 0.9

-- | Medium confidence (0.7)
confidenceMedium :: Confidence
confidenceMedium = Confidence 0.7

-- | Low confidence (0.5)
confidenceLow :: Confidence
confidenceLow = Confidence 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // timing atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | WordStart - start time of a word in seconds from audio beginning.
newtype WordStart = WordStart Number

derive instance eqWordStart :: Eq WordStart
derive instance ordWordStart :: Ord WordStart

instance showWordStart :: Show WordStart where
  show (WordStart n) = show n <> "s start"

-- | Create a WordStart value (clamped to non-negative)
wordStart :: Number -> WordStart
wordStart n
  | n < 0.0 = WordStart 0.0
  | otherwise = WordStart n

unwrapWordStart :: WordStart -> Number
unwrapWordStart (WordStart n) = n

-- | WordEnd - end time of a word in seconds from audio beginning.
newtype WordEnd = WordEnd Number

derive instance eqWordEnd :: Eq WordEnd
derive instance ordWordEnd :: Ord WordEnd

instance showWordEnd :: Show WordEnd where
  show (WordEnd n) = show n <> "s end"

-- | Create a WordEnd value (clamped to non-negative)
wordEnd :: Number -> WordEnd
wordEnd n
  | n < 0.0 = WordEnd 0.0
  | otherwise = WordEnd n

unwrapWordEnd :: WordEnd -> Number
unwrapWordEnd (WordEnd n) = n

-- | PhonemeDuration - duration of a phoneme in milliseconds.
-- | Most phonemes are 50-200ms.
newtype PhonemeDuration = PhonemeDuration Number

derive instance eqPhonemeDuration :: Eq PhonemeDuration
derive instance ordPhonemeDuration :: Ord PhonemeDuration

instance showPhonemeDuration :: Show PhonemeDuration where
  show (PhonemeDuration n) = show n <> " ms"

-- | Create a PhonemeDuration value (clamped to 0-500)
phonemeDuration :: Number -> PhonemeDuration
phonemeDuration n
  | n < 0.0 = PhonemeDuration 0.0
  | n > 500.0 = PhonemeDuration 500.0
  | otherwise = PhonemeDuration n

unwrapPhonemeDuration :: PhonemeDuration -> Number
unwrapPhonemeDuration (PhonemeDuration n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Confidence
-- |
-- | Min: 0.0 (no confidence)
-- | Max: 1.0 (certain)
confidenceBounds :: Bounded.NumberBounds
confidenceBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "confidence" "Recognition confidence (0-1)"

-- | Bounds for WordStart
-- |
-- | Min: 0.0 seconds
-- | Max: 86400.0 seconds (24 hours)
wordStartBounds :: Bounded.NumberBounds
wordStartBounds = Bounded.numberBounds 0.0 86400.0 Bounded.Clamps "wordStart" "Word start time in seconds (0+)"

-- | Bounds for WordEnd
-- |
-- | Min: 0.0 seconds
-- | Max: 86400.0 seconds (24 hours)
wordEndBounds :: Bounded.NumberBounds
wordEndBounds = Bounded.numberBounds 0.0 86400.0 Bounded.Clamps "wordEnd" "Word end time in seconds (0+)"

-- | Bounds for PhonemeDuration
-- |
-- | Typical phoneme: 30-300ms. Long sounds like vowels can be ~300ms.
phonemeDurationBounds :: Bounded.NumberBounds
phonemeDurationBounds = Bounded.numberBounds 0.0 500.0 Bounded.Clamps "phonemeDuration" "Phoneme duration in ms (0-500)"
