{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // foundry // brand/sonicidentity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.SonicIdentity
Description : Music and audio generation specification for brand sonic identity
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the sonic characteristics for brand music generation - jingles,
background music, sonic logos, and ambient audio.

== Relationship to Other Audio Types

  BrandVoice   = WHAT to say (textual personality)
  AudioVoice   = HOW speech sounds (TTS parameters)
  SonicIdentity = WHAT music sounds like (composition parameters)

== Target Music Generation Systems

Primary: ACE-Step 1.5 (ACE Studio / StepFun)
  - Text-to-music with structured lyrics
  - Tags for genre, mood, tempo, instrumentation
  - LoRA fine-tuning for brand-specific styles
  - 2 seconds to 10 minutes duration

Secondary: Custom scoring systems, sample libraries

== Invariants

* Tempo range: 20-300 BPM
* All mood/genre tags are lowercase, comma-separated
* Forbidden instruments list is disjoint from preferred
* At least one preferred instrument
* Duration presets must be positive

== Dependencies

Requires: Nothing (standalone)
Required by: Foundry.Core.Brand.Complete, Foundry.Generate.Music

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.SonicIdentity
  ( -- * Tempo
    Tempo (..)
  , TempoRange (..)
  , mkTempo
  , mkTempoRange
  , TempoFeel (..)
  
    -- * Tonality
  , MusicalKey (..)
  , KeySignature (..)
  , Mode (..)
  , mkKeySignature
  
    -- * Mood & Genre
  , MoodTag (..)
  , GenreTag (..)
  , MoodPalette (..)
  , mkMoodPalette
  
    -- * Instrumentation
  , Instrument (..)
  , InstrumentCategory (..)
  , InstrumentationSpec (..)
  , mkInstrumentationSpec
  
    -- * Production Style
  , ProductionAesthetic (..)
  , Fidelity (..)
  , SpatialStyle (..)
  , LoudnessTarget (..)
  , ProductionSpec (..)
  
    -- * Generation Presets
  , ContentType (..)
  , DurationPreset (..)
  , GenerationPreset (..)
  , mkGenerationPreset
  
    -- * Reference Tracks (for LoRA training)
  , ReferenceTrack (..)
  , mkReferenceTrack
  
    -- * Complete Sonic Identity
  , SonicIdentity (..)
  , mkSonicIdentity
  
    -- * Prompt Generation
  , toACEStepTags
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), (.:?), object, withObject, withText)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Word (Word16, Word8)

--------------------------------------------------------------------------------
-- Tempo
--------------------------------------------------------------------------------

-- | Beats per minute
newtype Tempo = Tempo { unTempo :: Word16 }
  deriving stock (Eq, Ord, Show)

-- | Create tempo with validation (20-300 BPM)
mkTempo :: Word16 -> Maybe Tempo
mkTempo bpm
  | bpm < 20 = Nothing
  | bpm > 300 = Nothing
  | otherwise = Just (Tempo bpm)

-- | Tempo range for brand music
data TempoRange = TempoRange
  { trMin       :: !Tempo
  , trMax       :: !Tempo
  , trPreferred :: !Tempo
  }
  deriving stock (Eq, Show)

-- | Create tempo range with validation
mkTempoRange :: Tempo -> Tempo -> Tempo -> Maybe TempoRange
mkTempoRange minT maxT pref
  | unTempo minT > unTempo maxT = Nothing
  | unTempo pref < unTempo minT = Nothing
  | unTempo pref > unTempo maxT = Nothing
  | otherwise = Just TempoRange
      { trMin = minT
      , trMax = maxT
      , trPreferred = pref
      }

-- | Qualitative tempo feel
data TempoFeel
  = Languid     -- ^ Very slow, dreamy
  | Relaxed     -- ^ Slow, comfortable
  | Moderate    -- ^ Walking pace
  | Upbeat      -- ^ Energetic but controlled
  | Driving     -- ^ High energy
  | Frenetic    -- ^ Very fast, intense
  deriving stock (Eq, Ord, Show, Enum, Bounded)

--------------------------------------------------------------------------------
-- Tonality
--------------------------------------------------------------------------------

-- | Musical key root note
data MusicalKey
  = C | CSharp | D | DSharp | E | F
  | FSharp | G | GSharp | A | ASharp | B
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Major or minor mode
data Mode = Major | Minor | Dorian | Mixolydian | Lydian | Phrygian
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Complete key signature
data KeySignature = KeySignature
  { ksRoot :: !MusicalKey
  , ksMode :: !Mode
  }
  deriving stock (Eq, Show)

-- | Create key signature
mkKeySignature :: MusicalKey -> Mode -> KeySignature
mkKeySignature = KeySignature

--------------------------------------------------------------------------------
-- Mood & Genre
--------------------------------------------------------------------------------

-- | A single mood descriptor tag
newtype MoodTag = MoodTag { unMoodTag :: Text }
  deriving stock (Eq, Ord, Show)

-- | A single genre descriptor tag
newtype GenreTag = GenreTag { unGenreTag :: Text }
  deriving stock (Eq, Ord, Show)

-- | Palette of mood descriptors for the brand
--
-- These map directly to ACE-Step prompt tags.
data MoodPalette = MoodPalette
  { mpPrimary   :: !(Vector MoodTag)
    -- ^ Primary brand moods (always present)
  , mpSecondary :: !(Vector MoodTag)
    -- ^ Secondary moods (context-dependent)
  , mpForbidden :: !(Set MoodTag)
    -- ^ Moods to never use
  }
  deriving stock (Eq, Show)

-- | Create mood palette with validation
mkMoodPalette 
  :: Vector MoodTag 
  -> Vector MoodTag 
  -> Set MoodTag 
  -> Maybe MoodPalette
mkMoodPalette primary secondary forbidden
  | V.null primary = Nothing  -- Need at least one primary mood
  | any (`Set.member` forbidden) (V.toList primary) = Nothing
  | any (`Set.member` forbidden) (V.toList secondary) = Nothing
  | otherwise = Just MoodPalette
      { mpPrimary = primary
      , mpSecondary = secondary
      , mpForbidden = forbidden
      }

--------------------------------------------------------------------------------
-- Instrumentation
--------------------------------------------------------------------------------

-- | Instrument category
data InstrumentCategory
  = KeysCategory       -- ^ Piano, synth, organ
  | StringsCategory    -- ^ Violin, cello, guitar
  | BrassCategory      -- ^ Trumpet, trombone
  | WoodwindCategory   -- ^ Flute, clarinet, sax
  | PercussionCategory -- ^ Drums, percussion
  | ElectronicCategory -- ^ Synths, pads, leads
  | VocalCategory      -- ^ Choir, vocal samples
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Specific instrument
data Instrument = Instrument
  { instName     :: !Text
    -- ^ Instrument name for prompts (e.g., "acoustic piano", "synth pad")
  , instCategory :: !InstrumentCategory
    -- ^ Category classification
  }
  deriving stock (Eq, Show)

instance Ord Instrument where
  compare a b = compare (instName a, instCategory a) (instName b, instCategory b)

-- | Instrumentation specification
data InstrumentationSpec = InstrumentationSpec
  { isPreferred :: !(Vector Instrument)
    -- ^ Instruments that define the brand sound
  , isForbidden :: !(Set Text)
    -- ^ Instrument names to avoid
  , isLeadVoice :: !(Maybe Instrument)
    -- ^ Primary melodic instrument
  }
  deriving stock (Eq, Show)

-- | Create instrumentation spec with validation
mkInstrumentationSpec 
  :: Vector Instrument 
  -> Set Text 
  -> Maybe Instrument 
  -> Maybe InstrumentationSpec
mkInstrumentationSpec pref forbidden lead
  | V.null pref = Nothing  -- Need at least one preferred instrument
  | any ((`Set.member` forbidden) . instName) (V.toList pref) = Nothing
  | otherwise = Just InstrumentationSpec
      { isPreferred = pref
      , isForbidden = forbidden
      , isLeadVoice = lead
      }

--------------------------------------------------------------------------------
-- Production Style
--------------------------------------------------------------------------------

-- | Overall production aesthetic
data ProductionAesthetic
  = ModernClean      -- ^ Contemporary, polished
  | VintageAnalog    -- ^ Warm, retro
  | LoFi             -- ^ Deliberately degraded
  | Cinematic        -- ^ Epic, filmic
  | Minimalist       -- ^ Sparse, essential
  | Maximalist       -- ^ Dense, layered
  | Organic          -- ^ Natural, acoustic-feeling
  | Synthetic        -- ^ Electronic, artificial
  deriving stock (Eq, Show, Enum, Bounded)

-- | Audio fidelity level
data Fidelity
  = LoFidelity       -- ^ Intentionally degraded
  | StandardFidelity -- ^ Normal quality
  | HighFidelity     -- ^ Premium, detailed
  deriving stock (Eq, Show, Enum, Bounded)

-- | Spatial/stereo characteristics
data SpatialStyle
  = Mono             -- ^ Single channel
  | NarrowStereo     -- ^ Subtle width
  | WideStereo       -- ^ Full stereo spread
  | Immersive        -- ^ Surround/spatial audio
  deriving stock (Eq, Show, Enum, Bounded)

-- | Loudness target in LUFS (scaled to 0-255)
--
-- Maps roughly: 0 = -70 LUFS (silence), 255 = -0 LUFS (max)
-- Typical targets: 180 = -14 LUFS (streaming), 200 = -11 LUFS (broadcast)
newtype LoudnessTarget = LoudnessTarget { unLoudnessTarget :: Word8 }
  deriving stock (Eq, Ord, Show)

-- | Complete production specification
data ProductionSpec = ProductionSpec
  { psAesthetic :: !ProductionAesthetic
  , psFidelity  :: !Fidelity
  , psSpatial   :: !SpatialStyle
  , psLoudness  :: !LoudnessTarget
    -- ^ Target loudness level
  , psNotes     :: !Text
    -- ^ Additional production notes
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Generation Presets
--------------------------------------------------------------------------------

-- | Type of audio content to generate
data ContentType
  = SonicLogo        -- ^ 2-5 second audio logo
  | Jingle           -- ^ 10-30 second branded jingle
  | IntroOutro       -- ^ 15-60 second intro/outro music
  | BackgroundMusic  -- ^ 60-240 second ambient/background
  | FullTrack        -- ^ 3-10 minute complete composition
  | OnHoldMusic      -- ^ Loop-friendly hold music
  | NotificationSound -- ^ Short UI sound
  deriving stock (Eq, Show, Enum, Bounded)

-- | Duration preset in seconds
data DurationPreset = DurationPreset
  { dpMinSeconds :: !Word16
  , dpMaxSeconds :: !Word16
  , dpDefault    :: !Word16
  }
  deriving stock (Eq, Show)

-- | Generation preset for a content type
data GenerationPreset = GenerationPreset
  { gpContentType   :: !ContentType
  , gpDuration      :: !DurationPreset
  , gpGuidanceScale :: !Double
    -- ^ ACE-Step guidance scale (higher = more prompt adherence)
  , gpLyricTemplate :: !(Maybe Text)
    -- ^ Structured lyric template with [verse], [chorus] tags
  , gpSeed          :: !(Maybe Word16)
    -- ^ Fixed seed for reproducibility (Nothing = random)
  }
  deriving stock (Eq, Show)

-- | Create generation preset with validation
mkGenerationPreset 
  :: ContentType 
  -> DurationPreset 
  -> Double 
  -> Maybe Text 
  -> Maybe GenerationPreset
mkGenerationPreset ct dur guidance lyricTpl
  | dpMinSeconds dur > dpMaxSeconds dur = Nothing
  | dpDefault dur < dpMinSeconds dur = Nothing
  | dpDefault dur > dpMaxSeconds dur = Nothing
  | guidance < 1.0 = Nothing  -- Too low
  | guidance > 50.0 = Nothing -- Too high
  | otherwise = Just GenerationPreset
      { gpContentType = ct
      , gpDuration = dur
      , gpGuidanceScale = guidance
      , gpLyricTemplate = lyricTpl
      , gpSeed = Nothing
      }

--------------------------------------------------------------------------------
-- Reference Tracks (for LoRA training)
--------------------------------------------------------------------------------

-- | Reference track for brand sonic identity training
data ReferenceTrack = ReferenceTrack
  { rtFilePath    :: !Text
    -- ^ Path to reference audio file
  , rtTitle       :: !Text
    -- ^ Track title for identification
  , rtDescription :: !Text
    -- ^ Why this track represents the brand sound
  , rtDurationMs  :: !Word16
    -- ^ Duration in milliseconds
  , rtBPM         :: !(Maybe Tempo)
    -- ^ Detected/known tempo
  , rtKey         :: !(Maybe KeySignature)
    -- ^ Detected/known key
  }
  deriving stock (Eq, Show)

-- | Create reference track with validation
mkReferenceTrack
  :: Text    -- ^ File path
  -> Text    -- ^ Title
  -> Text    -- ^ Description
  -> Word16  -- ^ Duration ms
  -> Maybe ReferenceTrack
mkReferenceTrack path title desc dur
  | T.null path = Nothing
  | T.null title = Nothing
  | dur < 1000 = Nothing  -- Too short
  | otherwise = Just ReferenceTrack
      { rtFilePath = path
      , rtTitle = title
      , rtDescription = desc
      , rtDurationMs = dur
      , rtBPM = Nothing
      , rtKey = Nothing
      }

--------------------------------------------------------------------------------
-- Complete Sonic Identity
--------------------------------------------------------------------------------

-- | Complete sonic identity specification for a brand
--
-- This captures everything needed to generate brand-consistent music:
--
-- * Tempo: How fast the brand moves
-- * Tonality: Preferred keys and modes
-- * Mood: Emotional palette
-- * Instrumentation: Sound palette
-- * Production: Technical aesthetic
-- * Presets: Ready-to-use generation configs
-- * References: Training data for fine-tuning
data SonicIdentity = SonicIdentity
  { siTempo          :: !TempoRange
    -- ^ Tempo range and preference
  , siTempoFeel      :: !TempoFeel
    -- ^ Qualitative tempo description
  , siPreferredKeys  :: !(Vector KeySignature)
    -- ^ Preferred key signatures
  , siMoodPalette    :: !MoodPalette
    -- ^ Emotional palette
  , siGenres         :: !(Vector GenreTag)
    -- ^ Genre tags for generation
  , siInstrumentation :: !InstrumentationSpec
    -- ^ Instrument preferences
  , siProduction     :: !ProductionSpec
    -- ^ Production aesthetic
  , siPresets        :: !(Vector GenerationPreset)
    -- ^ Pre-configured generation presets
  , siReferenceTracks :: !(Vector ReferenceTrack)
    -- ^ Reference tracks for LoRA training
  , siLoRAPath       :: !(Maybe Text)
    -- ^ Path to trained LoRA weights (after training)
  }
  deriving stock (Eq, Show)

-- | Create sonic identity with validation
mkSonicIdentity
  :: TempoRange
  -> TempoFeel
  -> Vector KeySignature
  -> MoodPalette
  -> Vector GenreTag
  -> InstrumentationSpec
  -> ProductionSpec
  -> Maybe SonicIdentity
mkSonicIdentity tempo feel keys mood genres instr prod
  | V.null genres = Nothing  -- Need at least one genre
  | otherwise = Just SonicIdentity
      { siTempo = tempo
      , siTempoFeel = feel
      , siPreferredKeys = keys
      , siMoodPalette = mood
      , siGenres = genres
      , siInstrumentation = instr
      , siProduction = prod
      , siPresets = V.empty
      , siReferenceTracks = V.empty
      , siLoRAPath = Nothing
      }

--------------------------------------------------------------------------------
-- Prompt Generation
--------------------------------------------------------------------------------

-- | Generate ACE-Step compatible tags from SonicIdentity
--
-- Produces comma-separated tags for the model's prompt field.
toACEStepTags :: SonicIdentity -> Text
toACEStepTags si = T.intercalate ", " $ mconcat
  [ -- Genres
    V.toList (V.map unGenreTag (siGenres si))
    -- Primary moods
  , V.toList (V.map unMoodTag (mpPrimary (siMoodPalette si)))
    -- Tempo
  , [T.pack (show (unTempo (trPreferred (siTempo si)))) <> "bpm"]
    -- Production aesthetic
  , [aestheticTag (psAesthetic (siProduction si))]
    -- Preferred instruments
  , V.toList (V.map instName (isPreferred (siInstrumentation si)))
  ]
  where
    aestheticTag :: ProductionAesthetic -> Text
    aestheticTag ModernClean = "modern, clean, polished"
    aestheticTag VintageAnalog = "vintage, analog, warm"
    aestheticTag LoFi = "lo-fi, chill"
    aestheticTag Cinematic = "cinematic, epic, orchestral"
    aestheticTag Minimalist = "minimal, sparse"
    aestheticTag Maximalist = "dense, layered, complex"
    aestheticTag Organic = "organic, acoustic, natural"
    aestheticTag Synthetic = "electronic, synthetic"

--------------------------------------------------------------------------------
-- JSON Instances
--------------------------------------------------------------------------------

-- Simple newtypes
instance ToJSON Tempo where
  toJSON (Tempo bpm) = toJSON bpm

instance FromJSON Tempo where
  parseJSON v = Tempo <$> parseJSON v

instance ToJSON MoodTag where
  toJSON (MoodTag t) = toJSON t

instance FromJSON MoodTag where
  parseJSON = withText "MoodTag" (pure . MoodTag)

instance ToJSON GenreTag where
  toJSON (GenreTag t) = toJSON t

instance FromJSON GenreTag where
  parseJSON = withText "GenreTag" (pure . GenreTag)

instance ToJSON LoudnessTarget where
  toJSON (LoudnessTarget l) = toJSON l

instance FromJSON LoudnessTarget where
  parseJSON v = LoudnessTarget <$> parseJSON v

-- TempoRange
instance ToJSON TempoRange where
  toJSON tr = object
    [ "min"       .= trMin tr
    , "max"       .= trMax tr
    , "preferred" .= trPreferred tr
    ]

instance FromJSON TempoRange where
  parseJSON = withObject "TempoRange" $ \v -> TempoRange
    <$> v .: "min"
    <*> v .: "max"
    <*> v .: "preferred"

-- TempoFeel
instance ToJSON TempoFeel where
  toJSON Languid  = "languid"
  toJSON Relaxed  = "relaxed"
  toJSON Moderate = "moderate"
  toJSON Upbeat   = "upbeat"
  toJSON Driving  = "driving"
  toJSON Frenetic = "frenetic"

instance FromJSON TempoFeel where
  parseJSON = withText "TempoFeel" $ \case
    "languid"  -> pure Languid
    "relaxed"  -> pure Relaxed
    "moderate" -> pure Moderate
    "upbeat"   -> pure Upbeat
    "driving"  -> pure Driving
    "frenetic" -> pure Frenetic
    other      -> fail $ "Unknown TempoFeel: " <> T.unpack other

-- MusicalKey
instance ToJSON MusicalKey where
  toJSON C      = "C"
  toJSON CSharp = "C#"
  toJSON D      = "D"
  toJSON DSharp = "D#"
  toJSON E      = "E"
  toJSON F      = "F"
  toJSON FSharp = "F#"
  toJSON G      = "G"
  toJSON GSharp = "G#"
  toJSON A      = "A"
  toJSON ASharp = "A#"
  toJSON B      = "B"

instance FromJSON MusicalKey where
  parseJSON = withText "MusicalKey" $ \case
    "C"  -> pure C
    "C#" -> pure CSharp
    "D"  -> pure D
    "D#" -> pure DSharp
    "E"  -> pure E
    "F"  -> pure F
    "F#" -> pure FSharp
    "G"  -> pure G
    "G#" -> pure GSharp
    "A"  -> pure A
    "A#" -> pure ASharp
    "B"  -> pure B
    other -> fail $ "Unknown MusicalKey: " <> T.unpack other

-- Mode
instance ToJSON Mode where
  toJSON Major      = "major"
  toJSON Minor      = "minor"
  toJSON Dorian     = "dorian"
  toJSON Mixolydian = "mixolydian"
  toJSON Lydian     = "lydian"
  toJSON Phrygian   = "phrygian"

instance FromJSON Mode where
  parseJSON = withText "Mode" $ \case
    "major"      -> pure Major
    "minor"      -> pure Minor
    "dorian"     -> pure Dorian
    "mixolydian" -> pure Mixolydian
    "lydian"     -> pure Lydian
    "phrygian"   -> pure Phrygian
    other        -> fail $ "Unknown Mode: " <> T.unpack other

-- KeySignature
instance ToJSON KeySignature where
  toJSON ks = object
    [ "root" .= ksRoot ks
    , "mode" .= ksMode ks
    ]

instance FromJSON KeySignature where
  parseJSON = withObject "KeySignature" $ \v -> KeySignature
    <$> v .: "root"
    <*> v .: "mode"

-- MoodPalette
instance ToJSON MoodPalette where
  toJSON mp = object
    [ "primary"   .= mpPrimary mp
    , "secondary" .= mpSecondary mp
    , "forbidden" .= Set.toList (mpForbidden mp)
    ]

instance FromJSON MoodPalette where
  parseJSON = withObject "MoodPalette" $ \v -> MoodPalette
    <$> v .: "primary"
    <*> v .: "secondary"
    <*> (Set.fromList <$> v .: "forbidden")

-- InstrumentCategory
instance ToJSON InstrumentCategory where
  toJSON KeysCategory       = "keys"
  toJSON StringsCategory    = "strings"
  toJSON BrassCategory      = "brass"
  toJSON WoodwindCategory   = "woodwind"
  toJSON PercussionCategory = "percussion"
  toJSON ElectronicCategory = "electronic"
  toJSON VocalCategory      = "vocal"

instance FromJSON InstrumentCategory where
  parseJSON = withText "InstrumentCategory" $ \case
    "keys"       -> pure KeysCategory
    "strings"    -> pure StringsCategory
    "brass"      -> pure BrassCategory
    "woodwind"   -> pure WoodwindCategory
    "percussion" -> pure PercussionCategory
    "electronic" -> pure ElectronicCategory
    "vocal"      -> pure VocalCategory
    other        -> fail $ "Unknown InstrumentCategory: " <> T.unpack other

-- Instrument
instance ToJSON Instrument where
  toJSON inst = object
    [ "name"     .= instName inst
    , "category" .= instCategory inst
    ]

instance FromJSON Instrument where
  parseJSON = withObject "Instrument" $ \v -> Instrument
    <$> v .: "name"
    <*> v .: "category"

-- InstrumentationSpec
instance ToJSON InstrumentationSpec where
  toJSON is = object
    [ "preferred" .= isPreferred is
    , "forbidden" .= Set.toList (isForbidden is)
    , "leadVoice" .= isLeadVoice is
    ]

instance FromJSON InstrumentationSpec where
  parseJSON = withObject "InstrumentationSpec" $ \v -> InstrumentationSpec
    <$> v .: "preferred"
    <*> (Set.fromList <$> v .: "forbidden")
    <*> v .:? "leadVoice"

-- ProductionAesthetic
instance ToJSON ProductionAesthetic where
  toJSON ModernClean  = "modern_clean"
  toJSON VintageAnalog = "vintage_analog"
  toJSON LoFi         = "lofi"
  toJSON Cinematic    = "cinematic"
  toJSON Minimalist   = "minimalist"
  toJSON Maximalist   = "maximalist"
  toJSON Organic      = "organic"
  toJSON Synthetic    = "synthetic"

instance FromJSON ProductionAesthetic where
  parseJSON = withText "ProductionAesthetic" $ \case
    "modern_clean"   -> pure ModernClean
    "vintage_analog" -> pure VintageAnalog
    "lofi"           -> pure LoFi
    "cinematic"      -> pure Cinematic
    "minimalist"     -> pure Minimalist
    "maximalist"     -> pure Maximalist
    "organic"        -> pure Organic
    "synthetic"      -> pure Synthetic
    other            -> fail $ "Unknown ProductionAesthetic: " <> T.unpack other

-- Fidelity
instance ToJSON Fidelity where
  toJSON LoFidelity       = "lo"
  toJSON StandardFidelity = "standard"
  toJSON HighFidelity     = "high"

instance FromJSON Fidelity where
  parseJSON = withText "Fidelity" $ \case
    "lo"       -> pure LoFidelity
    "standard" -> pure StandardFidelity
    "high"     -> pure HighFidelity
    other      -> fail $ "Unknown Fidelity: " <> T.unpack other

-- SpatialStyle
instance ToJSON SpatialStyle where
  toJSON Mono         = "mono"
  toJSON NarrowStereo = "narrow_stereo"
  toJSON WideStereo   = "wide_stereo"
  toJSON Immersive    = "immersive"

instance FromJSON SpatialStyle where
  parseJSON = withText "SpatialStyle" $ \case
    "mono"          -> pure Mono
    "narrow_stereo" -> pure NarrowStereo
    "wide_stereo"   -> pure WideStereo
    "immersive"     -> pure Immersive
    other           -> fail $ "Unknown SpatialStyle: " <> T.unpack other

-- ProductionSpec
instance ToJSON ProductionSpec where
  toJSON ps = object
    [ "aesthetic" .= psAesthetic ps
    , "fidelity"  .= psFidelity ps
    , "spatial"   .= psSpatial ps
    , "loudness"  .= psLoudness ps
    , "notes"     .= psNotes ps
    ]

instance FromJSON ProductionSpec where
  parseJSON = withObject "ProductionSpec" $ \v -> ProductionSpec
    <$> v .: "aesthetic"
    <*> v .: "fidelity"
    <*> v .: "spatial"
    <*> v .: "loudness"
    <*> v .: "notes"

-- ContentType
instance ToJSON ContentType where
  toJSON SonicLogo         = "sonic_logo"
  toJSON Jingle            = "jingle"
  toJSON IntroOutro        = "intro_outro"
  toJSON BackgroundMusic   = "background_music"
  toJSON FullTrack         = "full_track"
  toJSON OnHoldMusic       = "on_hold_music"
  toJSON NotificationSound = "notification_sound"

instance FromJSON ContentType where
  parseJSON = withText "ContentType" $ \case
    "sonic_logo"         -> pure SonicLogo
    "jingle"             -> pure Jingle
    "intro_outro"        -> pure IntroOutro
    "background_music"   -> pure BackgroundMusic
    "full_track"         -> pure FullTrack
    "on_hold_music"      -> pure OnHoldMusic
    "notification_sound" -> pure NotificationSound
    other                -> fail $ "Unknown ContentType: " <> T.unpack other

-- DurationPreset
instance ToJSON DurationPreset where
  toJSON dp = object
    [ "minSeconds" .= dpMinSeconds dp
    , "maxSeconds" .= dpMaxSeconds dp
    , "default"    .= dpDefault dp
    ]

instance FromJSON DurationPreset where
  parseJSON = withObject "DurationPreset" $ \v -> DurationPreset
    <$> v .: "minSeconds"
    <*> v .: "maxSeconds"
    <*> v .: "default"

-- GenerationPreset
instance ToJSON GenerationPreset where
  toJSON gp = object
    [ "contentType"   .= gpContentType gp
    , "duration"      .= gpDuration gp
    , "guidanceScale" .= gpGuidanceScale gp
    , "lyricTemplate" .= gpLyricTemplate gp
    , "seed"          .= gpSeed gp
    ]

instance FromJSON GenerationPreset where
  parseJSON = withObject "GenerationPreset" $ \v -> GenerationPreset
    <$> v .: "contentType"
    <*> v .: "duration"
    <*> v .: "guidanceScale"
    <*> v .:? "lyricTemplate"
    <*> v .:? "seed"

-- ReferenceTrack
instance ToJSON ReferenceTrack where
  toJSON rt = object
    [ "filePath"    .= rtFilePath rt
    , "title"       .= rtTitle rt
    , "description" .= rtDescription rt
    , "durationMs"  .= rtDurationMs rt
    , "bpm"         .= rtBPM rt
    , "key"         .= rtKey rt
    ]

instance FromJSON ReferenceTrack where
  parseJSON = withObject "ReferenceTrack" $ \v -> ReferenceTrack
    <$> v .: "filePath"
    <*> v .: "title"
    <*> v .: "description"
    <*> v .: "durationMs"
    <*> v .:? "bpm"
    <*> v .:? "key"

-- SonicIdentity
instance ToJSON SonicIdentity where
  toJSON si = object
    [ "tempo"           .= siTempo si
    , "tempoFeel"       .= siTempoFeel si
    , "preferredKeys"   .= siPreferredKeys si
    , "moodPalette"     .= siMoodPalette si
    , "genres"          .= siGenres si
    , "instrumentation" .= siInstrumentation si
    , "production"      .= siProduction si
    , "presets"         .= siPresets si
    , "referenceTracks" .= siReferenceTracks si
    , "loraPath"        .= siLoRAPath si
    ]

instance FromJSON SonicIdentity where
  parseJSON = withObject "SonicIdentity" $ \v -> SonicIdentity
    <$> v .: "tempo"
    <*> v .: "tempoFeel"
    <*> v .: "preferredKeys"
    <*> v .: "moodPalette"
    <*> v .: "genres"
    <*> v .: "instrumentation"
    <*> v .: "production"
    <*> v .: "presets"
    <*> v .: "referenceTracks"
    <*> v .:? "loraPath"
