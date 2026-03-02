-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // audio // speech
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Speech analysis atoms for recognition, transcription, and speaker identity.
-- |
-- | ## Design Philosophy
-- |
-- | Speech analysis primitives describe the OUTPUT of speech recognition systems,
-- | not the recognition process itself. These atoms enable agents to work with
-- | transcribed speech, speaker characteristics, and speech timing.
-- |
-- | ## Phoneme Recognition
-- | IPA phonemes with confidence scores enable downstream processing to handle
-- | ambiguity appropriately. Phoneme boundaries enable precise timing.
-- |
-- | ## Word and Utterance Segmentation
-- | Word boundaries, sentence detection, and turn-taking markers support
-- | conversational AI applications.
-- |
-- | ## Speaker Diarization
-- | Speaker identity, embeddings, and turn detection enable multi-speaker
-- | transcript analysis.
-- |
-- | ## Module Structure
-- |
-- | - `Speech.Types` — Core types: Confidence, WordStart, WordEnd, PhonemeDuration
-- | - `Speech.Phonemes` — IPA phonemes and phoneme categories
-- | - `Speech.Recognition` — RecognizedPhoneme, RecognizedWord, Utterance
-- | - `Speech.Speaker` — Speaker identity, embeddings, and turns
-- | - `Speech.Quality` — Signal quality metrics and language detection
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.Speech as Speech
-- |
-- | -- Process a recognized word
-- | word = Speech.recognizedWord
-- |   "hello"
-- |   (Speech.confidence 0.95)
-- |   (Speech.wordStart 1.5)
-- |   (Speech.wordEnd 2.1)
-- | ```

module Hydrogen.Schema.Audio.Speech
  ( module Types
  , module Phonemes
  , module Recognition
  , module Speaker
  , module Quality
  ) where

import Hydrogen.Schema.Audio.Speech.Types
  ( Confidence(Confidence)
  , PhonemeDuration(PhonemeDuration)
  , WordEnd(WordEnd)
  , WordStart(WordStart)
  , confidence
  , confidenceBounds
  , confidenceHigh
  , confidenceLow
  , confidenceMedium
  , phonemeDuration
  , phonemeDurationBounds
  , unwrapConfidence
  , unwrapPhonemeDuration
  , unwrapWordEnd
  , unwrapWordStart
  , wordEnd
  , wordEndBounds
  , wordStart
  , wordStartBounds
  ) as Types

import Hydrogen.Schema.Audio.Speech.Phonemes
  ( IPAPhoneme(PhonemeI, PhonemeE, PhonemeEpsilon, PhonemeAE, PhonemeA, PhonemeO, PhonemeU, PhonemeUpsilon, PhonemeSchwa, PhonemeWedge, PhonemeP, PhonemeB, PhonemeT, PhonemeD, PhonemeK, PhonemeG, PhonemeF, PhonemeV, PhonemeTheta, PhonemeEth, PhonemeS, PhonemeZ, PhonemeSH, PhonemeZH, PhonemeH, PhonemeCH, PhonemeJH, PhonemeM, PhonemeN, PhonemeNG, PhonemeW, PhonemeY, PhonemeR, PhonemeL, PhonemeSilence)
  , PhonemeCategory(CategoryVowel, CategoryPlosive, CategoryFricative, CategoryAffricate, CategoryNasal, CategoryApproximant, CategorySilence)
  , ipaPhonemeCategory
  , ipaPhonemeSymbol
  , phonemeCategoryName
  ) as Phonemes

import Hydrogen.Schema.Audio.Speech.Recognition
  ( RecognizedPhoneme
  , RecognizedWord
  , Utterance
  , recognizedPhoneme
  , recognizedWord
  , utterance
  ) as Recognition

import Hydrogen.Schema.Audio.Speech.Speaker
  ( SpeakerConfidence(SpeakerConfidence)
  , SpeakerEmbedding(SpeakerEmbedding)
  , SpeakerId(SpeakerId)
  , SpeakerTurn
  , speakerConfidence
  , speakerConfidenceBounds
  , speakerEmbedding
  , speakerId
  , speakerTurn
  , unwrapSpeakerConfidence
  , unwrapSpeakerId
  ) as Speaker

import Hydrogen.Schema.Audio.Speech.Quality
  ( DetectedLanguage
  , Intelligibility(Intelligibility)
  , LanguageCode(LangEN, LangES, LangFR, LangDE, LangIT, LangPT, LangRU, LangZH, LangJA, LangKO, LangAR, LangHI, LangOther)
  , SignalToNoise(SignalToNoise)
  , detectedLanguage
  , intelligibility
  , intelligibilityBounds
  , languageCodeISO
  , signalToNoise
  , signalToNoiseBounds
  , unwrapIntelligibility
  , unwrapSignalToNoise
  ) as Quality
