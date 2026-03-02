-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // audio // speech // speaker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Speaker identity atoms and molecules for diarization.
-- |
-- | This module provides types for speaker identification and diarization
-- | (determining who spoke when). Speaker embeddings enable voice matching
-- | across audio segments.
-- |
-- | ## SpeakerId
-- | Unique identifier for a speaker within a transcript.
-- |
-- | ## SpeakerEmbedding
-- | Voice embedding vector for speaker recognition models.
-- |
-- | ## SpeakerTurn
-- | A segment of speech from one speaker, containing utterances.

module Hydrogen.Schema.Audio.Speech.Speaker
  ( -- * Speaker Identity Atoms
    SpeakerId(SpeakerId)
  , SpeakerEmbedding(SpeakerEmbedding)
  , SpeakerConfidence(SpeakerConfidence)
  , speakerId
  , speakerEmbedding
  , speakerConfidence
  , unwrapSpeakerId
  , unwrapSpeakerConfidence
  
  -- * Speaker Turn Molecule
  , SpeakerTurn
  , speakerTurn
  
  -- * Bounds
  , speakerConfidenceBounds
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

import Hydrogen.Schema.Audio.Speech.Types
  ( WordStart
  , WordEnd
  )

import Hydrogen.Schema.Audio.Speech.Recognition
  ( Utterance
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // speaker identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeakerId - unique identifier for a speaker.
-- | Used for diarization (who spoke when).
newtype SpeakerId = SpeakerId String

derive instance eqSpeakerId :: Eq SpeakerId
derive instance ordSpeakerId :: Ord SpeakerId

instance showSpeakerId :: Show SpeakerId where
  show (SpeakerId s) = "Speaker: " <> s

-- | Create a SpeakerId
speakerId :: String -> SpeakerId
speakerId = SpeakerId

unwrapSpeakerId :: SpeakerId -> String
unwrapSpeakerId (SpeakerId s) = s

-- | SpeakerEmbedding - voice embedding vector for speaker identification.
-- | Typically 128-512 dimensional vectors from speaker recognition models.
-- | Represented as array of numbers (normalized floats).
newtype SpeakerEmbedding = SpeakerEmbedding (Array Number)

derive instance eqSpeakerEmbedding :: Eq SpeakerEmbedding

instance showSpeakerEmbedding :: Show SpeakerEmbedding where
  show (SpeakerEmbedding _) = "[Speaker Embedding]"

-- | Create a SpeakerEmbedding
speakerEmbedding :: Array Number -> SpeakerEmbedding
speakerEmbedding = SpeakerEmbedding

-- | SpeakerConfidence - confidence that a segment belongs to a speaker.
newtype SpeakerConfidence = SpeakerConfidence Number

derive instance eqSpeakerConfidence :: Eq SpeakerConfidence
derive instance ordSpeakerConfidence :: Ord SpeakerConfidence

instance showSpeakerConfidence :: Show SpeakerConfidence where
  show (SpeakerConfidence n) = show (n * 100.0) <> "% speaker confidence"

-- | Create a SpeakerConfidence value (clamped to 0.0-1.0)
speakerConfidence :: Number -> SpeakerConfidence
speakerConfidence n
  | n < 0.0 = SpeakerConfidence 0.0
  | n > 1.0 = SpeakerConfidence 1.0
  | otherwise = SpeakerConfidence n

unwrapSpeakerConfidence :: SpeakerConfidence -> Number
unwrapSpeakerConfidence (SpeakerConfidence n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // speaker turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeakerTurn - a segment of speech from one speaker.
type SpeakerTurn =
  { speaker :: SpeakerId
  , confidence :: SpeakerConfidence
  , startTime :: WordStart
  , endTime :: WordEnd
  , utterances :: Array Utterance
  }

-- | Create a speaker turn record.
speakerTurn :: SpeakerId -> SpeakerConfidence -> WordStart -> WordEnd -> Array Utterance -> SpeakerTurn
speakerTurn spk c start end utts =
  { speaker: spk
  , confidence: c
  , startTime: start
  , endTime: end
  , utterances: utts
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for SpeakerConfidence
-- |
-- | Min: 0.0 (unknown speaker)
-- | Max: 1.0 (certain speaker)
speakerConfidenceBounds :: Bounded.NumberBounds
speakerConfidenceBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "speakerConfidence" "Speaker identification confidence (0-1)"
