-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // audio // speech // quality
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Speech quality atoms and language detection.
-- |
-- | This module provides types for assessing speech quality (SNR, intelligibility)
-- | and detecting the spoken language. These metrics help downstream systems
-- | determine audio suitability and route to appropriate language models.
-- |
-- | ## Signal-to-Noise Ratio
-- | SNR in decibels indicates how clean the audio is. Values below 10dB
-- | typically indicate problematic audio quality.
-- |
-- | ## Intelligibility
-- | Acoustic-based intelligibility score (not transcription accuracy).
-- | Indicates how clearly the speech can be understood.
-- |
-- | ## Language Detection
-- | ISO 639-1 language codes with confidence scores for multi-language support.

module Hydrogen.Schema.Audio.Speech.Quality
  ( -- * Speech Quality Atoms
    SignalToNoise(SignalToNoise)
  , Intelligibility(Intelligibility)
  , signalToNoise
  , intelligibility
  , unwrapSignalToNoise
  , unwrapIntelligibility
  
  -- * Language Detection
  , LanguageCode(LangEN, LangES, LangFR, LangDE, LangIT, LangPT, LangRU, LangZH, LangJA, LangKO, LangAR, LangHI, LangOther)
  , DetectedLanguage
  , detectedLanguage
  , languageCodeISO
  
  -- * Bounds
  , signalToNoiseBounds
  , intelligibilityBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (*)
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Audio.Speech.Types
  ( Confidence
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // speech quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | SignalToNoise - speech signal to noise ratio in dB.
-- | Higher = cleaner audio. Below 10dB is typically problematic.
newtype SignalToNoise = SignalToNoise Number

derive instance eqSignalToNoise :: Eq SignalToNoise
derive instance ordSignalToNoise :: Ord SignalToNoise

instance showSignalToNoise :: Show SignalToNoise where
  show (SignalToNoise n) = show n <> " dB SNR"

-- | Create a SignalToNoise value (clamped to -10 to 60)
signalToNoise :: Number -> SignalToNoise
signalToNoise n
  | n < (negate 10.0) = SignalToNoise (negate 10.0)
  | n > 60.0 = SignalToNoise 60.0
  | otherwise = SignalToNoise n

unwrapSignalToNoise :: SignalToNoise -> Number
unwrapSignalToNoise (SignalToNoise n) = n

-- | Intelligibility - estimated speech intelligibility score.
-- | 0.0 = unintelligible, 1.0 = perfectly clear.
-- | Based on acoustic analysis (not transcription accuracy).
newtype Intelligibility = Intelligibility Number

derive instance eqIntelligibility :: Eq Intelligibility
derive instance ordIntelligibility :: Ord Intelligibility

instance showIntelligibility :: Show Intelligibility where
  show (Intelligibility n) = show (n * 100.0) <> "% intelligible"

-- | Create an Intelligibility value (clamped to 0.0-1.0)
intelligibility :: Number -> Intelligibility
intelligibility n
  | n < 0.0 = Intelligibility 0.0
  | n > 1.0 = Intelligibility 1.0
  | otherwise = Intelligibility n

unwrapIntelligibility :: Intelligibility -> Number
unwrapIntelligibility (Intelligibility n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // language detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | LanguageCode - ISO 639-1 language code.
-- | Common codes for speech recognition.
data LanguageCode
  = LangEN  -- ^ English
  | LangES  -- ^ Spanish
  | LangFR  -- ^ French
  | LangDE  -- ^ German
  | LangIT  -- ^ Italian
  | LangPT  -- ^ Portuguese
  | LangRU  -- ^ Russian
  | LangZH  -- ^ Chinese (Mandarin)
  | LangJA  -- ^ Japanese
  | LangKO  -- ^ Korean
  | LangAR  -- ^ Arabic
  | LangHI  -- ^ Hindi
  | LangOther String  -- ^ Other ISO 639-1 code

derive instance eqLanguageCode :: Eq LanguageCode
derive instance ordLanguageCode :: Ord LanguageCode

instance showLanguageCode :: Show LanguageCode where
  show = languageCodeISO

-- | Get ISO 639-1 code
languageCodeISO :: LanguageCode -> String
languageCodeISO LangEN = "en"
languageCodeISO LangES = "es"
languageCodeISO LangFR = "fr"
languageCodeISO LangDE = "de"
languageCodeISO LangIT = "it"
languageCodeISO LangPT = "pt"
languageCodeISO LangRU = "ru"
languageCodeISO LangZH = "zh"
languageCodeISO LangJA = "ja"
languageCodeISO LangKO = "ko"
languageCodeISO LangAR = "ar"
languageCodeISO LangHI = "hi"
languageCodeISO (LangOther code) = code

-- | DetectedLanguage - detected language with confidence.
type DetectedLanguage =
  { language :: LanguageCode
  , confidence :: Confidence
  , alternatives :: Array { language :: LanguageCode, confidence :: Confidence }
  }

-- | Create a detected language record.
detectedLanguage :: LanguageCode -> Confidence -> Array { language :: LanguageCode, confidence :: Confidence } -> DetectedLanguage
detectedLanguage lang c alts =
  { language: lang
  , confidence: c
  , alternatives: alts
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for SignalToNoise
-- |
-- | Min: -10.0 dB (very noisy)
-- | Max: 60.0 dB (very clean)
signalToNoiseBounds :: Bounded.NumberBounds
signalToNoiseBounds = Bounded.numberBounds (negate 10.0) 60.0 Bounded.Clamps "signalToNoise" "Speech SNR in dB (-10 to 60)"

-- | Bounds for Intelligibility
-- |
-- | Min: 0.0 (unintelligible)
-- | Max: 1.0 (perfectly clear)
intelligibilityBounds :: Bounded.NumberBounds
intelligibilityBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "intelligibility" "Speech intelligibility score (0-1)"
