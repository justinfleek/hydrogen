-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // audio // speech // recognition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Speech recognition molecules: recognized phonemes, words, and utterances.
-- |
-- | These molecules combine timing, confidence, and content atoms to represent
-- | the output of speech recognition systems. They enable downstream processing
-- | of transcribed speech with full timing and confidence metadata.
-- |
-- | ## RecognizedPhoneme
-- | A detected phoneme with its IPA symbol, confidence, and timing.
-- |
-- | ## RecognizedWord
-- | A detected word with its text, confidence, and timing.
-- |
-- | ## Utterance
-- | A complete speech unit (sentence or phrase) containing words.

module Hydrogen.Schema.Audio.Speech.Recognition
  ( -- * Recognized Phoneme Molecule
    RecognizedPhoneme
  , recognizedPhoneme
  
  -- * Recognized Word Molecule
  , RecognizedWord
  , recognizedWord
  
  -- * Utterance Molecule
  , Utterance
  , utterance
  ) where

import Prelude
  ( otherwise
  , (<)
  )

import Hydrogen.Schema.Audio.Speech.Types
  ( Confidence
  , PhonemeDuration
  , WordStart
  , WordEnd
  , phonemeDuration
  )

import Hydrogen.Schema.Audio.Speech.Phonemes
  ( IPAPhoneme
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // recognized phoneme
-- ═════════════════════════════════════════════════════════════════════════════

-- | RecognizedPhoneme - a detected phoneme with timing and confidence.
type RecognizedPhoneme =
  { phoneme :: IPAPhoneme
  , confidence :: Confidence
  , startMs :: Number
  , durationMs :: PhonemeDuration
  }

-- | Create a recognized phoneme record.
recognizedPhoneme :: IPAPhoneme -> Confidence -> Number -> Number -> RecognizedPhoneme
recognizedPhoneme p c start dur =
  { phoneme: p
  , confidence: c
  , startMs: clampStart start
  , durationMs: phonemeDuration dur
  }
  where
    clampStart s
      | s < 0.0 = 0.0
      | otherwise = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // recognized word
-- ═════════════════════════════════════════════════════════════════════════════

-- | RecognizedWord - a detected word with timing and confidence.
type RecognizedWord =
  { text :: String
  , confidence :: Confidence
  , startTime :: WordStart
  , endTime :: WordEnd
  }

-- | Create a recognized word record.
recognizedWord :: String -> Confidence -> WordStart -> WordEnd -> RecognizedWord
recognizedWord txt c start end =
  { text: txt
  , confidence: c
  , startTime: start
  , endTime: end
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utterance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Utterance - a complete speech unit (sentence or phrase).
type Utterance =
  { text :: String
  , confidence :: Confidence
  , startTime :: WordStart
  , endTime :: WordEnd
  , words :: Array RecognizedWord
  , isFinal :: Boolean           -- ^ Final vs. interim result
  }

-- | Create an utterance record.
utterance :: String -> Confidence -> WordStart -> WordEnd -> Array RecognizedWord -> Boolean -> Utterance
utterance txt c start end ws final =
  { text: txt
  , confidence: c
  , startTime: start
  , endTime: end
  , words: ws
  , isFinal: final
  }
