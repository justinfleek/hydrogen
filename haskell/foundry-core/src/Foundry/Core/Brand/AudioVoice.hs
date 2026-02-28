{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // foundry // brand/audiovoice
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.AudioVoice
Description : TTS voice specification for brand audio generation
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the sonic characteristics of a brand's spoken voice for TTS systems.
This is DISTINCT from BrandVoice (textual personality via IS/NOT constraints).

== Relationship to BrandVoice

  BrandVoice   = WHAT to say (vocabulary, tone constraints, personality)
  AudioVoice   = HOW it sounds (timbre, cadence, pauses, emotion mapping)

The two work together: BrandVoice determines word choice and phrasing,
AudioVoice determines how those words are spoken.

== Target TTS Systems

Primary: CosyVoice 3 (Alibaba FunAudioLLM)
  - Zero-shot voice cloning from reference audio
  - Fine-grained control tags: [laughter], [breath], <strong>
  - Instruct mode: emotion, speed, dialect control
  - Pronunciation hotfixes: Pinyin/CMU phoneme overrides

Secondary: Qwen2.5-Omni (for real-time voice chat interfaces)

== Invariants

* Reference audio duration should be 3-10 seconds
* All emotion mappings use valid CosyVoice instruction format
* Pace values are bounded to [0.25, 4.0] relative speed
* Pronunciation overrides use valid phoneme notation

== Dependencies

Requires: Nothing (standalone)
Required by: Foundry.Core.Brand.Complete, Foundry.Generate.TTS

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.AudioVoice
  ( -- * Reference Audio (Voice Identity)
    ReferenceAudio (..)
  , mkReferenceAudio
  , SpeakerId (..)
  
    -- * Prosody Control
  , Pace (..)
  , PaceLevel (..)
  , mkPace
  , EmotionInstruction (..)
  , EmotionMapping (..)
  , mkEmotionMapping
  
    -- * Fine-Grained Tags
  , ControlTag (..)
  , allControlTags
  , EmphasisStyle (..)
  
    -- * Pronunciation Control
  , PhonemeNotation (..)
  , PronunciationOverride (..)
  , mkPronunciationOverride
  , PronunciationDict (..)
  , mkPronunciationDict
  , emptyPronunciationDict
  , lookupPronunciation
  
    -- * Dialect/Accent
  , Dialect (..)
  , commonDialects
  
    -- * Voice Character
  , VoiceCharacter (..)
  , VocalTick (..)
  , mkVoiceCharacter
  
    -- * Complete AudioVoice Specification
  , AudioVoice (..)
  , mkAudioVoice
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), (.:?), object, withObject, withText)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Word (Word16)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Reference Audio (Voice Identity)
--------------------------------------------------------------------------------

-- | Unique identifier for a saved voice profile
--
-- After zero-shot cloning, the voice can be saved and referenced by ID
-- for consistent generation without re-processing the reference audio.
newtype SpeakerId = SpeakerId { unSpeakerId :: Text }
  deriving stock (Eq, Ord, Show)

-- | Reference audio for voice cloning
--
-- CosyVoice extracts speaker characteristics from 3-10 seconds of audio.
-- The transcription is required for alignment during zero-shot synthesis.
data ReferenceAudio = ReferenceAudio
  { raFilePath     :: !Text
    -- ^ Path to reference audio file (WAV preferred, 16kHz+)
  , raTranscript   :: !Text
    -- ^ Transcription of what's spoken in the reference audio
  , raDurationMs   :: !Word16
    -- ^ Duration in milliseconds (3000-10000 optimal)
  , raSpeakerId    :: !(Maybe SpeakerId)
    -- ^ Saved speaker ID for reuse (after initial cloning)
  , raDescription  :: !(Maybe Text)
    -- ^ Human-readable description of the voice
  }
  deriving stock (Eq, Show)

-- | Create reference audio with validation
mkReferenceAudio 
  :: Text          -- ^ File path
  -> Text          -- ^ Transcript
  -> Word16        -- ^ Duration in ms
  -> Maybe Text    -- ^ Description
  -> Maybe ReferenceAudio
mkReferenceAudio path transcript dur desc
  | T.null path = Nothing
  | T.null transcript = Nothing
  | dur < 1000 = Nothing  -- Too short for good cloning
  | dur > 30000 = Nothing -- Too long, trim it
  | otherwise = Just ReferenceAudio
      { raFilePath = path
      , raTranscript = transcript
      , raDurationMs = dur
      , raSpeakerId = Nothing  -- Set after first cloning
      , raDescription = desc
      }

--------------------------------------------------------------------------------
-- Prosody Control
--------------------------------------------------------------------------------

-- | Discrete pace levels for CosyVoice instruct mode
data PaceLevel
  = VerySlow   -- ^ "非常慢速"
  | Slow       -- ^ "慢速"
  | Normal     -- ^ Default
  | Fast       -- ^ "快速"
  | VeryFast   -- ^ "非常快速"
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Speaking pace specification
data Pace = Pace
  { paceLevel    :: !PaceLevel
    -- ^ Discrete level for instruct mode
  , paceRelative :: !Double
    -- ^ Relative speed multiplier [0.25, 4.0], 1.0 = normal
  }
  deriving stock (Eq, Show)

-- | Create pace with validation
mkPace :: PaceLevel -> Double -> Maybe Pace
mkPace lvl rel
  | rel < 0.25 = Nothing
  | rel > 4.0 = Nothing
  | otherwise = Just Pace
      { paceLevel = lvl
      , paceRelative = rel
      }

-- | Emotion instruction template for CosyVoice
--
-- Format: "用{emotion}的语气说" or English equivalent
newtype EmotionInstruction = EmotionInstruction { unEmotionInstruction :: Text }
  deriving stock (Eq, Show)

-- | Mapping from semantic emotion to TTS instruction
--
-- The brand defines how emotions map to specific TTS instructions.
-- This enables consistent emotional expression across all audio.
data EmotionMapping = EmotionMapping
  { emJoyful       :: !EmotionInstruction
  , emEmpathetic   :: !EmotionInstruction  
  , emAuthoritative :: !EmotionInstruction
  , emExcited      :: !EmotionInstruction
  , emCalm         :: !EmotionInstruction
  , emConcerned    :: !EmotionInstruction
  , emConfident    :: !EmotionInstruction
  }
  deriving stock (Eq, Show)

-- | Create emotion mapping with validation
mkEmotionMapping
  :: Text -> Text -> Text -> Text -> Text -> Text -> Text
  -> Maybe EmotionMapping
mkEmotionMapping joy emp auth exc calm conc conf
  | any T.null [joy, emp, auth, exc, calm, conc, conf] = Nothing
  | otherwise = Just EmotionMapping
      { emJoyful = EmotionInstruction joy
      , emEmpathetic = EmotionInstruction emp
      , emAuthoritative = EmotionInstruction auth
      , emExcited = EmotionInstruction exc
      , emCalm = EmotionInstruction calm
      , emConcerned = EmotionInstruction conc
      , emConfident = EmotionInstruction conf
      }

--------------------------------------------------------------------------------
-- Fine-Grained Tags
--------------------------------------------------------------------------------

-- | Control tags that can be embedded in synthesis text
--
-- CosyVoice supports inserting these at specific points in text.
data ControlTag
  = Laughter           -- ^ [laughter] - insert laughter
  | Breath             -- ^ [breath] - insert breath pause  
  | LaughingWhile      -- ^ <laughter>text</laughter> - speak while laughing
  | StrongEmphasis     -- ^ <strong>text</strong> - emphasize
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | All available control tags
allControlTags :: [ControlTag]
allControlTags = [minBound .. maxBound]

-- | Style of emphasis to apply
data EmphasisStyle
  = EmphasisStrong     -- ^ Bold emphasis
  | EmphasisSubtle     -- ^ Slight emphasis
  | EmphasisDrawnOut   -- ^ Elongated pronunciation
  deriving stock (Eq, Show, Enum, Bounded)

--------------------------------------------------------------------------------
-- Pronunciation Control  
--------------------------------------------------------------------------------

-- | Phoneme notation system
data PhonemeNotation
  = Pinyin      -- ^ Chinese Pinyin: [pǐn][pái]
  | CMUArpabet  -- ^ CMU phoneme set: [IH1][N][V][AH0][L][IH0][D]
  | IPA         -- ^ International Phonetic Alphabet
  deriving stock (Eq, Show, Enum, Bounded)

-- | Override for specific word/phrase pronunciation
data PronunciationOverride = PronunciationOverride
  { poWord      :: !Text
    -- ^ The word/phrase as written
  , poPhonemes  :: !Text
    -- ^ Phoneme sequence in notation
  , poNotation  :: !PhonemeNotation
    -- ^ Which phoneme system
  }
  deriving stock (Eq, Show)

-- | Create pronunciation override with validation
mkPronunciationOverride :: Text -> Text -> PhonemeNotation -> Maybe PronunciationOverride
mkPronunciationOverride word phonemes notation
  | T.null word = Nothing
  | T.null phonemes = Nothing
  | otherwise = Just PronunciationOverride
      { poWord = word
      , poPhonemes = phonemes
      , poNotation = notation
      }

-- | Dictionary of pronunciation overrides for brand terms
newtype PronunciationDict = PronunciationDict
  { unPronunciationDict :: Map Text PronunciationOverride }
  deriving stock (Eq, Show)

-- | Create pronunciation dictionary from a list of overrides
mkPronunciationDict :: [PronunciationOverride] -> PronunciationDict
mkPronunciationDict overrides = PronunciationDict $
  Map.fromList [(poWord o, o) | o <- overrides]

-- | Empty pronunciation dictionary
emptyPronunciationDict :: PronunciationDict
emptyPronunciationDict = PronunciationDict Map.empty

-- | Look up pronunciation for a word
lookupPronunciation :: Text -> PronunciationDict -> Maybe PronunciationOverride
lookupPronunciation word (PronunciationDict m) = Map.lookup word m

--------------------------------------------------------------------------------
-- Dialect/Accent
--------------------------------------------------------------------------------

-- | Dialect or accent specification
--
-- CosyVoice supports Chinese dialects and various accents.
newtype Dialect = Dialect { unDialect :: Text }
  deriving stock (Eq, Ord, Show)

-- | Common supported dialects (CosyVoice)
commonDialects :: [Dialect]
commonDialects =
  [ Dialect "粤语"      -- Cantonese
  , Dialect "四川话"    -- Sichuan
  , Dialect "上海话"    -- Shanghainese
  , Dialect "天津话"    -- Tianjin
  , Dialect "西安话"    -- Xi'an
  , Dialect "standard"  -- Standard Mandarin/English
  ]

--------------------------------------------------------------------------------
-- Voice Character (The "Weird Ticks")
--------------------------------------------------------------------------------

-- | Spontaneous vocal behaviors and quirks
--
-- From SponTTS research: filled pauses, prolongation, spontaneous phenomena.
-- These make synthesized speech sound more natural and distinctive.
data VocalTick
  = FilledPause !Text
    -- ^ "um", "uh", "well" - hesitation markers
  | Prolongation !Text
    -- ^ Drawn-out sounds: "sooo", "reeeally"
  | SmileWhileSpeaking
    -- ^ Audible smile (raised cheeks affect formants)
  | SoftLaughter
    -- ^ Brief chuckle mid-sentence
  | BreathyOnset
    -- ^ Soft breath before starting phrases
  | TrailingOff
    -- ^ Voice fades at end of statements
  | UptalkPattern
    -- ^ Rising intonation at statement ends
  | CreakVoice
    -- ^ Vocal fry (glottal creak)
  | CustomTick !Text
    -- ^ Brand-specific verbal tic
  deriving stock (Eq, Show)

-- | Overall voice character profile
--
-- Captures the distinctive aspects of how a brand "speaks" beyond
-- mere words - the personality expressed through delivery.
data VoiceCharacter = VoiceCharacter
  { vcWarmth        :: !Double
    -- ^ Cold(0) to Warm(1) - affects overall tone
  , vcEnergy        :: !Double  
    -- ^ Low(0) to High(1) - affects dynamism
  , vcFormality     :: !Double
    -- ^ Casual(0) to Formal(1) - affects precision
  , vcTicks         :: !(Vector VocalTick)
    -- ^ Distinctive vocal behaviors
  , vcPauseStyle    :: !Text
    -- ^ How pauses are used: "dramatic", "thoughtful", "natural"
  , vcCadenceNotes  :: !Text
    -- ^ Free-form description of speech rhythm
  }
  deriving stock (Eq, Show)

-- | Create voice character with validation
mkVoiceCharacter
  :: Double     -- ^ Warmth [0,1]
  -> Double     -- ^ Energy [0,1]  
  -> Double     -- ^ Formality [0,1]
  -> Vector VocalTick
  -> Text       -- ^ Pause style
  -> Text       -- ^ Cadence notes
  -> Maybe VoiceCharacter
mkVoiceCharacter warmth energy formality ticks pause cadence
  | warmth < 0 || warmth > 1 = Nothing
  | energy < 0 || energy > 1 = Nothing
  | formality < 0 || formality > 1 = Nothing
  | otherwise = Just VoiceCharacter
      { vcWarmth = warmth
      , vcEnergy = energy
      , vcFormality = formality
      , vcTicks = ticks
      , vcPauseStyle = pause
      , vcCadenceNotes = cadence
      }

--------------------------------------------------------------------------------
-- Complete AudioVoice Specification
--------------------------------------------------------------------------------

-- | Complete specification for brand audio voice synthesis
--
-- This captures everything needed to generate brand-consistent spoken audio:
--
-- * Identity: Who is speaking (reference audio for cloning)
-- * Character: How they express (warmth, energy, quirks)
-- * Prosody: Pace and rhythm patterns
-- * Emotion: How emotions map to TTS instructions
-- * Pronunciation: Brand term pronunciations
--
-- Combined with BrandVoice (what to say), this enables fully
-- branded audio generation.
data AudioVoice = AudioVoice
  { avPrimaryVoice     :: !ReferenceAudio
    -- ^ Primary brand voice for cloning
  , avSecondaryVoices  :: !(Vector ReferenceAudio)
    -- ^ Additional voices (for variety, different contexts)
  , avCharacter        :: !VoiceCharacter
    -- ^ Voice personality and quirks
  , avDefaultPace      :: !Pace
    -- ^ Default speaking pace
  , avEmotions         :: !EmotionMapping
    -- ^ Emotion to TTS instruction mapping
  , avPronunciations   :: !PronunciationDict
    -- ^ Brand term pronunciations
  , avDialect          :: !(Maybe Dialect)
    -- ^ Optional dialect/accent
  , avLanguages        :: !(Set Text)
    -- ^ Supported languages (ISO 639-1 codes)
  , avDefaultInstruct  :: !Text
    -- ^ Default CosyVoice instruction prefix
    -- e.g., "温暖、专业、值得信赖"
  }
  deriving stock (Eq, Show)

-- | Create audio voice specification with validation
mkAudioVoice
  :: ReferenceAudio
  -> VoiceCharacter
  -> Pace
  -> EmotionMapping
  -> PronunciationDict
  -> Set Text          -- ^ Languages
  -> Text              -- ^ Default instruction
  -> Maybe AudioVoice
mkAudioVoice primary char pace emotions prons langs instr
  | T.null instr = Nothing
  | otherwise = Just AudioVoice
      { avPrimaryVoice = primary
      , avSecondaryVoices = V.empty
      , avCharacter = char
      , avDefaultPace = pace
      , avEmotions = emotions
      , avPronunciations = prons
      , avDialect = Nothing
      , avLanguages = langs
      , avDefaultInstruct = instr
      }

--------------------------------------------------------------------------------
-- JSON Instances
--------------------------------------------------------------------------------

-- Simple newtypes
instance ToJSON SpeakerId where
  toJSON (SpeakerId t) = toJSON t

instance FromJSON SpeakerId where
  parseJSON = withText "SpeakerId" (pure . SpeakerId)

instance ToJSON Dialect where
  toJSON (Dialect t) = toJSON t

instance FromJSON Dialect where
  parseJSON = withText "Dialect" (pure . Dialect)

instance ToJSON EmotionInstruction where
  toJSON (EmotionInstruction t) = toJSON t

instance FromJSON EmotionInstruction where
  parseJSON = withText "EmotionInstruction" (pure . EmotionInstruction)

-- ReferenceAudio
instance ToJSON ReferenceAudio where
  toJSON ra = object
    [ "filePath"    .= raFilePath ra
    , "transcript"  .= raTranscript ra
    , "durationMs"  .= raDurationMs ra
    , "speakerId"   .= raSpeakerId ra
    , "description" .= raDescription ra
    ]

instance FromJSON ReferenceAudio where
  parseJSON = withObject "ReferenceAudio" $ \v -> ReferenceAudio
    <$> v .: "filePath"
    <*> v .: "transcript"
    <*> v .: "durationMs"
    <*> v .:? "speakerId"
    <*> v .:? "description"

-- PaceLevel
instance ToJSON PaceLevel where
  toJSON VerySlow = "very_slow"
  toJSON Slow     = "slow"
  toJSON Normal   = "normal"
  toJSON Fast     = "fast"
  toJSON VeryFast = "very_fast"

instance FromJSON PaceLevel where
  parseJSON = withText "PaceLevel" $ \case
    "very_slow" -> pure VerySlow
    "slow"      -> pure Slow
    "normal"    -> pure Normal
    "fast"      -> pure Fast
    "very_fast" -> pure VeryFast
    other       -> fail $ "Unknown PaceLevel: " <> T.unpack other

-- Pace
instance ToJSON Pace where
  toJSON p = object
    [ "level"    .= paceLevel p
    , "relative" .= paceRelative p
    ]

instance FromJSON Pace where
  parseJSON = withObject "Pace" $ \v -> Pace
    <$> v .: "level"
    <*> v .: "relative"

-- EmotionMapping
instance ToJSON EmotionMapping where
  toJSON em = object
    [ "joyful"        .= emJoyful em
    , "empathetic"    .= emEmpathetic em
    , "authoritative" .= emAuthoritative em
    , "excited"       .= emExcited em
    , "calm"          .= emCalm em
    , "concerned"     .= emConcerned em
    , "confident"     .= emConfident em
    ]

instance FromJSON EmotionMapping where
  parseJSON = withObject "EmotionMapping" $ \v -> EmotionMapping
    <$> v .: "joyful"
    <*> v .: "empathetic"
    <*> v .: "authoritative"
    <*> v .: "excited"
    <*> v .: "calm"
    <*> v .: "concerned"
    <*> v .: "confident"

-- ControlTag
instance ToJSON ControlTag where
  toJSON Laughter       = "laughter"
  toJSON Breath         = "breath"
  toJSON LaughingWhile  = "laughing_while"
  toJSON StrongEmphasis = "strong_emphasis"

instance FromJSON ControlTag where
  parseJSON = withText "ControlTag" $ \case
    "laughter"        -> pure Laughter
    "breath"          -> pure Breath
    "laughing_while"  -> pure LaughingWhile
    "strong_emphasis" -> pure StrongEmphasis
    other             -> fail $ "Unknown ControlTag: " <> T.unpack other

-- EmphasisStyle
instance ToJSON EmphasisStyle where
  toJSON EmphasisStrong   = "strong"
  toJSON EmphasisSubtle   = "subtle"
  toJSON EmphasisDrawnOut = "drawn_out"

instance FromJSON EmphasisStyle where
  parseJSON = withText "EmphasisStyle" $ \case
    "strong"    -> pure EmphasisStrong
    "subtle"    -> pure EmphasisSubtle
    "drawn_out" -> pure EmphasisDrawnOut
    other       -> fail $ "Unknown EmphasisStyle: " <> T.unpack other

-- PhonemeNotation
instance ToJSON PhonemeNotation where
  toJSON Pinyin     = "pinyin"
  toJSON CMUArpabet = "cmu_arpabet"
  toJSON IPA        = "ipa"

instance FromJSON PhonemeNotation where
  parseJSON = withText "PhonemeNotation" $ \case
    "pinyin"      -> pure Pinyin
    "cmu_arpabet" -> pure CMUArpabet
    "ipa"         -> pure IPA
    other         -> fail $ "Unknown PhonemeNotation: " <> T.unpack other

-- PronunciationOverride
instance ToJSON PronunciationOverride where
  toJSON po = object
    [ "word"     .= poWord po
    , "phonemes" .= poPhonemes po
    , "notation" .= poNotation po
    ]

instance FromJSON PronunciationOverride where
  parseJSON = withObject "PronunciationOverride" $ \v -> PronunciationOverride
    <$> v .: "word"
    <*> v .: "phonemes"
    <*> v .: "notation"

-- PronunciationDict (as array of overrides for simplicity)
instance ToJSON PronunciationDict where
  toJSON (PronunciationDict m) = toJSON (Map.elems m)

instance FromJSON PronunciationDict where
  parseJSON v = do
    overrides <- parseJSON v
    pure $ mkPronunciationDict overrides

-- VocalTick
instance ToJSON VocalTick where
  toJSON (FilledPause t)   = object ["type" .= ("filled_pause" :: Text), "value" .= t]
  toJSON (Prolongation t)  = object ["type" .= ("prolongation" :: Text), "value" .= t]
  toJSON SmileWhileSpeaking = object ["type" .= ("smile_while_speaking" :: Text)]
  toJSON SoftLaughter      = object ["type" .= ("soft_laughter" :: Text)]
  toJSON BreathyOnset      = object ["type" .= ("breathy_onset" :: Text)]
  toJSON TrailingOff       = object ["type" .= ("trailing_off" :: Text)]
  toJSON UptalkPattern     = object ["type" .= ("uptalk_pattern" :: Text)]
  toJSON CreakVoice        = object ["type" .= ("creak_voice" :: Text)]
  toJSON (CustomTick t)    = object ["type" .= ("custom" :: Text), "value" .= t]

instance FromJSON VocalTick where
  parseJSON = withObject "VocalTick" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "filled_pause"        -> FilledPause <$> v .: "value"
      "prolongation"        -> Prolongation <$> v .: "value"
      "smile_while_speaking" -> pure SmileWhileSpeaking
      "soft_laughter"       -> pure SoftLaughter
      "breathy_onset"       -> pure BreathyOnset
      "trailing_off"        -> pure TrailingOff
      "uptalk_pattern"      -> pure UptalkPattern
      "creak_voice"         -> pure CreakVoice
      "custom"              -> CustomTick <$> v .: "value"
      other                 -> fail $ "Unknown VocalTick: " <> T.unpack other

-- VoiceCharacter
instance ToJSON VoiceCharacter where
  toJSON vc = object
    [ "warmth"       .= vcWarmth vc
    , "energy"       .= vcEnergy vc
    , "formality"    .= vcFormality vc
    , "ticks"        .= vcTicks vc
    , "pauseStyle"   .= vcPauseStyle vc
    , "cadenceNotes" .= vcCadenceNotes vc
    ]

instance FromJSON VoiceCharacter where
  parseJSON = withObject "VoiceCharacter" $ \v -> VoiceCharacter
    <$> v .: "warmth"
    <*> v .: "energy"
    <*> v .: "formality"
    <*> v .: "ticks"
    <*> v .: "pauseStyle"
    <*> v .: "cadenceNotes"

-- AudioVoice
instance ToJSON AudioVoice where
  toJSON av = object
    [ "primaryVoice"    .= avPrimaryVoice av
    , "secondaryVoices" .= avSecondaryVoices av
    , "character"       .= avCharacter av
    , "defaultPace"     .= avDefaultPace av
    , "emotions"        .= avEmotions av
    , "pronunciations"  .= avPronunciations av
    , "dialect"         .= avDialect av
    , "languages"       .= Set.toList (avLanguages av)
    , "defaultInstruct" .= avDefaultInstruct av
    ]

instance FromJSON AudioVoice where
  parseJSON = withObject "AudioVoice" $ \v -> AudioVoice
    <$> v .: "primaryVoice"
    <*> v .: "secondaryVoices"
    <*> v .: "character"
    <*> v .: "defaultPace"
    <*> v .: "emotions"
    <*> v .: "pronunciations"
    <*> v .:? "dialect"
    <*> (Set.fromList <$> v .: "languages")
    <*> v .: "defaultInstruct"
