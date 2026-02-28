{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // brand/videoextraction
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.VideoExtraction
Description : Types for multimodal video brand signal extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types for extracting brand signals from video content using multimodal models.
Supports timestamped extraction of visual, textual, and audio brand elements.

== Target Analysis Systems

Primary: Qwen2.5-VL (72B) - Visual analysis with temporal grounding
  - Timestamped OCR with bounding boxes
  - Logo detection with coordinates
  - Scene composition analysis
  - Color palette extraction per frame

Audio: Qwen2-Audio (7B) - Audio analysis
  - Speech transcription
  - Speaker characteristics
  - Music/sound classification

Validation: Gemini 2.5 Pro (for cross-checking critical extractions)

== Invariants

* All timestamps are monotonically increasing
* Bounding boxes are within frame dimensions
* Confidence values in [0, 1]
* Color values are valid hex or RGB

== Dependencies

Requires: Foundry.Core.Brand.Color, Foundry.Core.Brand.Source
Required by: Foundry.Extract.Video, Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.VideoExtraction
  ( -- * Temporal Types
    VideoTimestamp (..)
  , mkVideoTimestamp
  , TimeRange (..)
  , mkTimeRange
  , FrameNumber (..)
  
    -- * Spatial Types
  , BoundingBox (..)
  , mkBoundingBox
  , Point (..)
  , FrameDimensions (..)
  
    -- * Text Extraction
  , ExtractedText (..)
  , TextType (..)
  , OCRConfidence (..)
  
    -- * Logo Detection
  , DetectedLogo (..)
  , LogoPlacement (..)
  
    -- * Color Extraction
  , FrameColorSample (..)
  , ColorRegion (..)
  , DominantColors (..)
  
    -- * Scene Analysis
  , ShotType (..)
  , CompositionStyle (..)
  , VisualMood (..)
  , SceneAnalysis (..)
  
    -- * Audio Extraction
  , SpeakerSegment (..)
  , SpeakerCharacteristics (..)
  , MusicSegment (..)
  , DetectedMood (..)
  
    -- * Aggregated Brand Signals
  , BrandSignal (..)
  , SignalType (..)
  , VideoAnalysisResult (..)
  , mkVideoAnalysisResult
  
    -- * Analysis Request
  , AnalysisType (..)
  , VideoAnalysisRequest (..)
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), (.:?), object, withObject, withText)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Word (Word16, Word32)

--------------------------------------------------------------------------------
-- Temporal Types
--------------------------------------------------------------------------------

-- | Timestamp in a video (milliseconds from start)
newtype VideoTimestamp = VideoTimestamp { unVideoTimestamp :: Word32 }
  deriving stock (Eq, Ord, Show)

-- | Create video timestamp
mkVideoTimestamp :: Word32 -> VideoTimestamp
mkVideoTimestamp = VideoTimestamp

-- | Time range within a video
data TimeRange = TimeRange
  { trStart :: !VideoTimestamp
  , trEnd   :: !VideoTimestamp
  }
  deriving stock (Eq, Show)

-- | Create time range with validation
mkTimeRange :: VideoTimestamp -> VideoTimestamp -> Maybe TimeRange
mkTimeRange start end
  | unVideoTimestamp start > unVideoTimestamp end = Nothing
  | otherwise = Just TimeRange { trStart = start, trEnd = end }

-- | Frame number (for frame-accurate positioning)
newtype FrameNumber = FrameNumber { unFrameNumber :: Word32 }
  deriving stock (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- Spatial Types
--------------------------------------------------------------------------------

-- | 2D point in frame coordinates
data Point = Point
  { pointX :: !Word16
  , pointY :: !Word16
  }
  deriving stock (Eq, Show)

-- | Bounding box in frame coordinates [x, y, width, height]
--
-- Follows Qwen2.5-VL bbox_2d format but normalized to our types.
data BoundingBox = BoundingBox
  { bbX      :: !Word16  -- ^ Left edge
  , bbY      :: !Word16  -- ^ Top edge
  , bbWidth  :: !Word16  -- ^ Width
  , bbHeight :: !Word16  -- ^ Height
  }
  deriving stock (Eq, Show)

-- | Create bounding box with validation
mkBoundingBox :: Word16 -> Word16 -> Word16 -> Word16 -> Maybe BoundingBox
mkBoundingBox x y w h
  | w == 0 = Nothing
  | h == 0 = Nothing
  | otherwise = Just BoundingBox
      { bbX = x, bbY = y, bbWidth = w, bbHeight = h }

-- | Video frame dimensions
data FrameDimensions = FrameDimensions
  { fdWidth  :: !Word16
  , fdHeight :: !Word16
  , fdFPS    :: !Double
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Text Extraction (OCR)
--------------------------------------------------------------------------------

-- | Type of text detected
data TextType
  = Tagline        -- ^ Brand tagline / slogan
  | Headline       -- ^ Prominent headline
  | BodyText       -- ^ Regular body text
  | CallToAction   -- ^ CTA button/text
  | LegalText      -- ^ Fine print, disclaimers
  | BrandName      -- ^ Company/product name
  | Unknown        -- ^ Unclassified text
  deriving stock (Eq, Show, Enum, Bounded)

-- | OCR confidence level
newtype OCRConfidence = OCRConfidence { unOCRConfidence :: Double }
  deriving stock (Eq, Ord, Show)

-- | Extracted text with temporal and spatial context
data ExtractedText = ExtractedText
  { etText       :: !Text
    -- ^ The extracted text content
  , etType       :: !TextType
    -- ^ Classification of the text
  , etTimestamp  :: !VideoTimestamp
    -- ^ When this text appears
  , etDuration   :: !(Maybe Word32)
    -- ^ How long it's visible (ms)
  , etBoundingBox :: !BoundingBox
    -- ^ Where in frame
  , etConfidence :: !OCRConfidence
    -- ^ OCR confidence [0, 1]
  , etFont       :: !(Maybe Text)
    -- ^ Detected font family (if identifiable)
  , etColor      :: !(Maybe Text)
    -- ^ Text color (hex)
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Logo Detection
--------------------------------------------------------------------------------

-- | Where in the frame the logo appears
data LogoPlacement
  = TopLeft | TopCenter | TopRight
  | MiddleLeft | Center | MiddleRight
  | BottomLeft | BottomCenter | BottomRight
  | Watermark  -- ^ Subtle overlay
  | FullScreen -- ^ Logo takes up most of frame
  deriving stock (Eq, Show, Enum, Bounded)

-- | Detected logo instance
data DetectedLogo = DetectedLogo
  { dlName        :: !Text
    -- ^ Identified logo/brand name
  , dlTimestamp   :: !VideoTimestamp
    -- ^ When it appears
  , dlDuration    :: !(Maybe Word32)
    -- ^ How long visible (ms)
  , dlBoundingBox :: !BoundingBox
    -- ^ Location in frame
  , dlPlacement   :: !LogoPlacement
    -- ^ Semantic position
  , dlConfidence  :: !Double
    -- ^ Detection confidence [0, 1]
  , dlVariant     :: !(Maybe Text)
    -- ^ Logo variant (e.g., "horizontal", "stacked", "icon-only")
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Color Extraction
--------------------------------------------------------------------------------

-- | Region of frame for color sampling
data ColorRegion
  = FullFrame      -- ^ Entire frame
  | UpperThird     -- ^ Top third
  | MiddleThird    -- ^ Middle third
  | LowerThird     -- ^ Bottom third
  | BackgroundArea -- ^ Detected background
  | ForegroundArea -- ^ Detected foreground
  | CustomRegion !BoundingBox
  deriving stock (Eq, Show)

-- | Dominant colors extracted from a frame
data DominantColors = DominantColors
  { dcPrimary    :: !Text  -- ^ Hex color
  , dcSecondary  :: !(Maybe Text)
  , dcTertiary   :: !(Maybe Text)
  , dcAccent     :: !(Maybe Text)
  , dcBackground :: !(Maybe Text)
  }
  deriving stock (Eq, Show)

-- | Color sample at a specific point in video
data FrameColorSample = FrameColorSample
  { fcsTimestamp :: !VideoTimestamp
  , fcsRegion    :: !ColorRegion
  , fcsColors    :: !DominantColors
  , fcsMethod    :: !Text
    -- ^ Extraction method (e.g., "k-means-5", "median-cut")
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Scene Analysis
--------------------------------------------------------------------------------

-- | Camera shot type
data ShotType
  = ExtremeWide    -- ^ Establishing shot
  | Wide           -- ^ Full scene
  | Medium         -- ^ Waist-up for people
  | CloseUp        -- ^ Face/detail
  | ExtremeCloseUp -- ^ Tight detail
  | OverTheShoulder
  | PointOfView
  | Aerial
  deriving stock (Eq, Show, Enum, Bounded)

-- | Visual composition style
data CompositionStyle
  = RuleOfThirds
  | Centered
  | Symmetrical
  | Asymmetrical
  | GoldenRatio
  | LeadingLines
  | FrameWithinFrame
  | Minimalist
  deriving stock (Eq, Show, Enum, Bounded)

-- | Visual mood/atmosphere
data VisualMood
  = Bright
  | Dark
  | HighContrast
  | LowContrast
  | Warm
  | Cool
  | Neutral
  | Dramatic
  | Soft
  | Energetic
  deriving stock (Eq, Show, Enum, Bounded)

-- | Scene analysis for a segment
data SceneAnalysis = SceneAnalysis
  { saTimeRange    :: !TimeRange
  , saShotType     :: !ShotType
  , saComposition  :: !CompositionStyle
  , saMood         :: !VisualMood
  , saDescription  :: !Text
    -- ^ Natural language scene description
  , saKeyElements  :: !(Vector Text)
    -- ^ Key visual elements identified
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Audio Extraction
--------------------------------------------------------------------------------

-- | Characteristics of a detected speaker
data SpeakerCharacteristics = SpeakerCharacteristics
  { scGender     :: !(Maybe Text)
    -- ^ Detected gender (or Nothing if uncertain)
  , scAgeRange   :: !(Maybe Text)
    -- ^ Estimated age range (e.g., "25-35")
  , scTone       :: !Text
    -- ^ Detected tone (e.g., "confident", "warm", "professional")
  , scEnergy     :: !Double
    -- ^ Energy level [0, 1]
  , scClarity    :: !Double
    -- ^ Speech clarity [0, 1]
  }
  deriving stock (Eq, Show)

-- | Detected speaker segment with transcription
data SpeakerSegment = SpeakerSegment
  { ssTimeRange      :: !TimeRange
  , ssTranscript     :: !Text
    -- ^ What was said
  , ssSpeakerId      :: !(Maybe Text)
    -- ^ Speaker identifier (for multi-speaker diarization)
  , ssCharacteristics :: !SpeakerCharacteristics
  , ssConfidence     :: !Double
    -- ^ Transcription confidence [0, 1]
  }
  deriving stock (Eq, Show)

-- | Detected mood in audio
data DetectedMood = DetectedMood
  { dmMood       :: !Text
    -- ^ Mood name (e.g., "uplifting", "tense", "calm")
  , dmConfidence :: !Double
    -- ^ Detection confidence [0, 1]
  }
  deriving stock (Eq, Show)

-- | Music segment analysis
data MusicSegment = MusicSegment
  { msTimeRange :: !TimeRange
  , msGenre     :: !(Maybe Text)
    -- ^ Detected genre
  , msTempo     :: !(Maybe Word16)
    -- ^ Detected BPM
  , msKey       :: !(Maybe Text)
    -- ^ Detected musical key
  , msMood      :: !DetectedMood
  , msEnergy    :: !Double
    -- ^ Energy level [0, 1]
  , msHasVocals :: !Bool
    -- ^ Whether vocals are present
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Aggregated Brand Signals
--------------------------------------------------------------------------------

-- | Type of brand signal detected
data SignalType
  = TextSignal
  | LogoSignal
  | ColorSignal
  | SceneSignal
  | SpeechSignal
  | MusicSignal
  deriving stock (Eq, Show, Enum, Bounded)

-- | A detected brand signal with timestamp
data BrandSignal
  = TextBrandSignal !ExtractedText
  | LogoBrandSignal !DetectedLogo
  | ColorBrandSignal !FrameColorSample
  | SceneBrandSignal !SceneAnalysis
  | SpeechBrandSignal !SpeakerSegment
  | MusicBrandSignal !MusicSegment
  deriving stock (Eq, Show)

-- | Complete video analysis result
data VideoAnalysisResult = VideoAnalysisResult
  { varVideoPath     :: !Text
    -- ^ Path to analyzed video
  , varDurationMs    :: !Word32
    -- ^ Total video duration
  , varDimensions    :: !FrameDimensions
    -- ^ Video dimensions and FPS
  , varTextSignals   :: !(Vector ExtractedText)
    -- ^ All extracted text
  , varLogoSignals   :: !(Vector DetectedLogo)
    -- ^ All detected logos
  , varColorSignals  :: !(Vector FrameColorSample)
    -- ^ Color samples over time
  , varSceneSignals  :: !(Vector SceneAnalysis)
    -- ^ Scene analyses
  , varSpeechSignals :: !(Vector SpeakerSegment)
    -- ^ Speech segments
  , varMusicSignals  :: !(Vector MusicSegment)
    -- ^ Music segments
  , varAnalyzedAt    :: !Text
    -- ^ ISO 8601 timestamp of analysis
  , varModelVersions :: !(Vector Text)
    -- ^ Models used (e.g., "qwen2.5-vl-72b", "qwen2-audio-7b")
  }
  deriving stock (Eq, Show)

-- | Create video analysis result with validation
mkVideoAnalysisResult
  :: Text          -- ^ Video path
  -> Word32        -- ^ Duration ms
  -> FrameDimensions
  -> Text          -- ^ Analyzed at timestamp
  -> Maybe VideoAnalysisResult
mkVideoAnalysisResult path dur dims timestamp
  | T.null path = Nothing
  | dur == 0 = Nothing
  | T.null timestamp = Nothing
  | otherwise = Just VideoAnalysisResult
      { varVideoPath = path
      , varDurationMs = dur
      , varDimensions = dims
      , varTextSignals = mempty
      , varLogoSignals = mempty
      , varColorSignals = mempty
      , varSceneSignals = mempty
      , varSpeechSignals = mempty
      , varMusicSignals = mempty
      , varAnalyzedAt = timestamp
      , varModelVersions = mempty
      }

--------------------------------------------------------------------------------
-- Analysis Request
--------------------------------------------------------------------------------

-- | Types of analysis to perform
data AnalysisType
  = OCRAnalysis          -- ^ Text/tagline extraction
  | LogoDetection        -- ^ Logo detection
  | ColorExtraction      -- ^ Color palette extraction
  | SceneAnalysis_       -- ^ Scene composition (underscore to avoid conflict)
  | SpeechTranscription  -- ^ Speech-to-text
  | MusicAnalysis        -- ^ Music characteristics
  | FullAnalysis         -- ^ All of the above
  deriving stock (Eq, Show, Enum, Bounded)

-- | Request for video analysis
data VideoAnalysisRequest = VideoAnalysisRequest
  { varqVideoPath     :: !Text
    -- ^ Path to video file
  , varqAnalysisTypes :: !(Vector AnalysisType)
    -- ^ Which analyses to perform
  , varqFrameRate     :: !Double
    -- ^ Sampling frame rate (e.g., 1.0 = 1 FPS)
  , varqMaxDuration   :: !(Maybe Word32)
    -- ^ Optional max duration to analyze (ms)
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- JSON Instances
--------------------------------------------------------------------------------

-- Simple newtypes
instance ToJSON VideoTimestamp where
  toJSON (VideoTimestamp ms) = toJSON ms

instance FromJSON VideoTimestamp where
  parseJSON v = VideoTimestamp <$> parseJSON v

instance ToJSON FrameNumber where
  toJSON (FrameNumber n) = toJSON n

instance FromJSON FrameNumber where
  parseJSON v = FrameNumber <$> parseJSON v

instance ToJSON OCRConfidence where
  toJSON (OCRConfidence c) = toJSON c

instance FromJSON OCRConfidence where
  parseJSON v = OCRConfidence <$> parseJSON v

-- Point
instance ToJSON Point where
  toJSON p = object
    [ "x" .= pointX p
    , "y" .= pointY p
    ]

instance FromJSON Point where
  parseJSON = withObject "Point" $ \v -> Point
    <$> v .: "x"
    <*> v .: "y"

-- TimeRange
instance ToJSON TimeRange where
  toJSON tr = object
    [ "start" .= trStart tr
    , "end"   .= trEnd tr
    ]

instance FromJSON TimeRange where
  parseJSON = withObject "TimeRange" $ \v -> TimeRange
    <$> v .: "start"
    <*> v .: "end"

-- BoundingBox
instance ToJSON BoundingBox where
  toJSON bb = object
    [ "x"      .= bbX bb
    , "y"      .= bbY bb
    , "width"  .= bbWidth bb
    , "height" .= bbHeight bb
    ]

instance FromJSON BoundingBox where
  parseJSON = withObject "BoundingBox" $ \v -> BoundingBox
    <$> v .: "x"
    <*> v .: "y"
    <*> v .: "width"
    <*> v .: "height"

-- FrameDimensions
instance ToJSON FrameDimensions where
  toJSON fd = object
    [ "width"  .= fdWidth fd
    , "height" .= fdHeight fd
    , "fps"    .= fdFPS fd
    ]

instance FromJSON FrameDimensions where
  parseJSON = withObject "FrameDimensions" $ \v -> FrameDimensions
    <$> v .: "width"
    <*> v .: "height"
    <*> v .: "fps"

-- TextType
instance ToJSON TextType where
  toJSON Tagline      = "tagline"
  toJSON Headline     = "headline"
  toJSON BodyText     = "body_text"
  toJSON CallToAction = "call_to_action"
  toJSON LegalText    = "legal_text"
  toJSON BrandName    = "brand_name"
  toJSON Unknown      = "unknown"

instance FromJSON TextType where
  parseJSON = withText "TextType" $ \case
    "tagline"        -> pure Tagline
    "headline"       -> pure Headline
    "body_text"      -> pure BodyText
    "call_to_action" -> pure CallToAction
    "legal_text"     -> pure LegalText
    "brand_name"     -> pure BrandName
    "unknown"        -> pure Unknown
    other            -> fail $ "Unknown TextType: " <> T.unpack other

-- LogoPlacement
instance ToJSON LogoPlacement where
  toJSON TopLeft      = "top_left"
  toJSON TopCenter    = "top_center"
  toJSON TopRight     = "top_right"
  toJSON MiddleLeft   = "middle_left"
  toJSON Center       = "center"
  toJSON MiddleRight  = "middle_right"
  toJSON BottomLeft   = "bottom_left"
  toJSON BottomCenter = "bottom_center"
  toJSON BottomRight  = "bottom_right"
  toJSON Watermark    = "watermark"
  toJSON FullScreen   = "full_screen"

instance FromJSON LogoPlacement where
  parseJSON = withText "LogoPlacement" $ \case
    "top_left"      -> pure TopLeft
    "top_center"    -> pure TopCenter
    "top_right"     -> pure TopRight
    "middle_left"   -> pure MiddleLeft
    "center"        -> pure Center
    "middle_right"  -> pure MiddleRight
    "bottom_left"   -> pure BottomLeft
    "bottom_center" -> pure BottomCenter
    "bottom_right"  -> pure BottomRight
    "watermark"     -> pure Watermark
    "full_screen"   -> pure FullScreen
    other           -> fail $ "Unknown LogoPlacement: " <> T.unpack other

-- ColorRegion
instance ToJSON ColorRegion where
  toJSON FullFrame      = object ["type" .= ("full_frame" :: Text)]
  toJSON UpperThird     = object ["type" .= ("upper_third" :: Text)]
  toJSON MiddleThird    = object ["type" .= ("middle_third" :: Text)]
  toJSON LowerThird     = object ["type" .= ("lower_third" :: Text)]
  toJSON BackgroundArea = object ["type" .= ("background_area" :: Text)]
  toJSON ForegroundArea = object ["type" .= ("foreground_area" :: Text)]
  toJSON (CustomRegion bb) = object ["type" .= ("custom" :: Text), "bbox" .= bb]

instance FromJSON ColorRegion where
  parseJSON = withObject "ColorRegion" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "full_frame"      -> pure FullFrame
      "upper_third"     -> pure UpperThird
      "middle_third"    -> pure MiddleThird
      "lower_third"     -> pure LowerThird
      "background_area" -> pure BackgroundArea
      "foreground_area" -> pure ForegroundArea
      "custom"          -> CustomRegion <$> v .: "bbox"
      other             -> fail $ "Unknown ColorRegion: " <> T.unpack other

-- DominantColors
instance ToJSON DominantColors where
  toJSON dc = object
    [ "primary"    .= dcPrimary dc
    , "secondary"  .= dcSecondary dc
    , "tertiary"   .= dcTertiary dc
    , "accent"     .= dcAccent dc
    , "background" .= dcBackground dc
    ]

instance FromJSON DominantColors where
  parseJSON = withObject "DominantColors" $ \v -> DominantColors
    <$> v .: "primary"
    <*> v .:? "secondary"
    <*> v .:? "tertiary"
    <*> v .:? "accent"
    <*> v .:? "background"

-- ShotType
instance ToJSON ShotType where
  toJSON ExtremeWide     = "extreme_wide"
  toJSON Wide            = "wide"
  toJSON Medium          = "medium"
  toJSON CloseUp         = "close_up"
  toJSON ExtremeCloseUp  = "extreme_close_up"
  toJSON OverTheShoulder = "over_the_shoulder"
  toJSON PointOfView     = "point_of_view"
  toJSON Aerial          = "aerial"

instance FromJSON ShotType where
  parseJSON = withText "ShotType" $ \case
    "extreme_wide"      -> pure ExtremeWide
    "wide"              -> pure Wide
    "medium"            -> pure Medium
    "close_up"          -> pure CloseUp
    "extreme_close_up"  -> pure ExtremeCloseUp
    "over_the_shoulder" -> pure OverTheShoulder
    "point_of_view"     -> pure PointOfView
    "aerial"            -> pure Aerial
    other               -> fail $ "Unknown ShotType: " <> T.unpack other

-- CompositionStyle
instance ToJSON CompositionStyle where
  toJSON RuleOfThirds    = "rule_of_thirds"
  toJSON Centered        = "centered"
  toJSON Symmetrical     = "symmetrical"
  toJSON Asymmetrical    = "asymmetrical"
  toJSON GoldenRatio     = "golden_ratio"
  toJSON LeadingLines    = "leading_lines"
  toJSON FrameWithinFrame = "frame_within_frame"
  toJSON Minimalist      = "minimalist"

instance FromJSON CompositionStyle where
  parseJSON = withText "CompositionStyle" $ \case
    "rule_of_thirds"     -> pure RuleOfThirds
    "centered"           -> pure Centered
    "symmetrical"        -> pure Symmetrical
    "asymmetrical"       -> pure Asymmetrical
    "golden_ratio"       -> pure GoldenRatio
    "leading_lines"      -> pure LeadingLines
    "frame_within_frame" -> pure FrameWithinFrame
    "minimalist"         -> pure Minimalist
    other                -> fail $ "Unknown CompositionStyle: " <> T.unpack other

-- VisualMood
instance ToJSON VisualMood where
  toJSON Bright       = "bright"
  toJSON Dark         = "dark"
  toJSON HighContrast = "high_contrast"
  toJSON LowContrast  = "low_contrast"
  toJSON Warm         = "warm"
  toJSON Cool         = "cool"
  toJSON Neutral      = "neutral"
  toJSON Dramatic     = "dramatic"
  toJSON Soft         = "soft"
  toJSON Energetic    = "energetic"

instance FromJSON VisualMood where
  parseJSON = withText "VisualMood" $ \case
    "bright"        -> pure Bright
    "dark"          -> pure Dark
    "high_contrast" -> pure HighContrast
    "low_contrast"  -> pure LowContrast
    "warm"          -> pure Warm
    "cool"          -> pure Cool
    "neutral"       -> pure Neutral
    "dramatic"      -> pure Dramatic
    "soft"          -> pure Soft
    "energetic"     -> pure Energetic
    other           -> fail $ "Unknown VisualMood: " <> T.unpack other

-- ExtractedText
instance ToJSON ExtractedText where
  toJSON et = object
    [ "text"        .= etText et
    , "type"        .= etType et
    , "timestamp"   .= etTimestamp et
    , "duration"    .= etDuration et
    , "boundingBox" .= etBoundingBox et
    , "confidence"  .= etConfidence et
    , "font"        .= etFont et
    , "color"       .= etColor et
    ]

instance FromJSON ExtractedText where
  parseJSON = withObject "ExtractedText" $ \v -> ExtractedText
    <$> v .: "text"
    <*> v .: "type"
    <*> v .: "timestamp"
    <*> v .:? "duration"
    <*> v .: "boundingBox"
    <*> v .: "confidence"
    <*> v .:? "font"
    <*> v .:? "color"

-- DetectedLogo
instance ToJSON DetectedLogo where
  toJSON dl = object
    [ "name"        .= dlName dl
    , "timestamp"   .= dlTimestamp dl
    , "duration"    .= dlDuration dl
    , "boundingBox" .= dlBoundingBox dl
    , "placement"   .= dlPlacement dl
    , "confidence"  .= dlConfidence dl
    , "variant"     .= dlVariant dl
    ]

instance FromJSON DetectedLogo where
  parseJSON = withObject "DetectedLogo" $ \v -> DetectedLogo
    <$> v .: "name"
    <*> v .: "timestamp"
    <*> v .:? "duration"
    <*> v .: "boundingBox"
    <*> v .: "placement"
    <*> v .: "confidence"
    <*> v .:? "variant"

-- FrameColorSample
instance ToJSON FrameColorSample where
  toJSON fcs = object
    [ "timestamp" .= fcsTimestamp fcs
    , "region"    .= fcsRegion fcs
    , "colors"    .= fcsColors fcs
    , "method"    .= fcsMethod fcs
    ]

instance FromJSON FrameColorSample where
  parseJSON = withObject "FrameColorSample" $ \v -> FrameColorSample
    <$> v .: "timestamp"
    <*> v .: "region"
    <*> v .: "colors"
    <*> v .: "method"

-- SceneAnalysis
instance ToJSON SceneAnalysis where
  toJSON sa = object
    [ "timeRange"   .= saTimeRange sa
    , "shotType"    .= saShotType sa
    , "composition" .= saComposition sa
    , "mood"        .= saMood sa
    , "description" .= saDescription sa
    , "keyElements" .= saKeyElements sa
    ]

instance FromJSON SceneAnalysis where
  parseJSON = withObject "SceneAnalysis" $ \v -> SceneAnalysis
    <$> v .: "timeRange"
    <*> v .: "shotType"
    <*> v .: "composition"
    <*> v .: "mood"
    <*> v .: "description"
    <*> v .: "keyElements"

-- SpeakerCharacteristics
instance ToJSON SpeakerCharacteristics where
  toJSON sc = object
    [ "gender"   .= scGender sc
    , "ageRange" .= scAgeRange sc
    , "tone"     .= scTone sc
    , "energy"   .= scEnergy sc
    , "clarity"  .= scClarity sc
    ]

instance FromJSON SpeakerCharacteristics where
  parseJSON = withObject "SpeakerCharacteristics" $ \v -> SpeakerCharacteristics
    <$> v .:? "gender"
    <*> v .:? "ageRange"
    <*> v .: "tone"
    <*> v .: "energy"
    <*> v .: "clarity"

-- SpeakerSegment
instance ToJSON SpeakerSegment where
  toJSON ss = object
    [ "timeRange"        .= ssTimeRange ss
    , "transcript"       .= ssTranscript ss
    , "speakerId"        .= ssSpeakerId ss
    , "characteristics"  .= ssCharacteristics ss
    , "confidence"       .= ssConfidence ss
    ]

instance FromJSON SpeakerSegment where
  parseJSON = withObject "SpeakerSegment" $ \v -> SpeakerSegment
    <$> v .: "timeRange"
    <*> v .: "transcript"
    <*> v .:? "speakerId"
    <*> v .: "characteristics"
    <*> v .: "confidence"

-- DetectedMood
instance ToJSON DetectedMood where
  toJSON dm = object
    [ "mood"       .= dmMood dm
    , "confidence" .= dmConfidence dm
    ]

instance FromJSON DetectedMood where
  parseJSON = withObject "DetectedMood" $ \v -> DetectedMood
    <$> v .: "mood"
    <*> v .: "confidence"

-- MusicSegment
instance ToJSON MusicSegment where
  toJSON ms = object
    [ "timeRange" .= msTimeRange ms
    , "genre"     .= msGenre ms
    , "tempo"     .= msTempo ms
    , "key"       .= msKey ms
    , "mood"      .= msMood ms
    , "energy"    .= msEnergy ms
    , "hasVocals" .= msHasVocals ms
    ]

instance FromJSON MusicSegment where
  parseJSON = withObject "MusicSegment" $ \v -> MusicSegment
    <$> v .: "timeRange"
    <*> v .:? "genre"
    <*> v .:? "tempo"
    <*> v .:? "key"
    <*> v .: "mood"
    <*> v .: "energy"
    <*> v .: "hasVocals"

-- SignalType
instance ToJSON SignalType where
  toJSON TextSignal   = "text"
  toJSON LogoSignal   = "logo"
  toJSON ColorSignal  = "color"
  toJSON SceneSignal  = "scene"
  toJSON SpeechSignal = "speech"
  toJSON MusicSignal  = "music"

instance FromJSON SignalType where
  parseJSON = withText "SignalType" $ \case
    "text"   -> pure TextSignal
    "logo"   -> pure LogoSignal
    "color"  -> pure ColorSignal
    "scene"  -> pure SceneSignal
    "speech" -> pure SpeechSignal
    "music"  -> pure MusicSignal
    other    -> fail $ "Unknown SignalType: " <> T.unpack other

-- BrandSignal
instance ToJSON BrandSignal where
  toJSON (TextBrandSignal et)   = object ["type" .= ("text" :: Text), "data" .= et]
  toJSON (LogoBrandSignal dl)   = object ["type" .= ("logo" :: Text), "data" .= dl]
  toJSON (ColorBrandSignal fcs) = object ["type" .= ("color" :: Text), "data" .= fcs]
  toJSON (SceneBrandSignal sa)  = object ["type" .= ("scene" :: Text), "data" .= sa]
  toJSON (SpeechBrandSignal ss) = object ["type" .= ("speech" :: Text), "data" .= ss]
  toJSON (MusicBrandSignal ms)  = object ["type" .= ("music" :: Text), "data" .= ms]

instance FromJSON BrandSignal where
  parseJSON = withObject "BrandSignal" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "text"   -> TextBrandSignal <$> v .: "data"
      "logo"   -> LogoBrandSignal <$> v .: "data"
      "color"  -> ColorBrandSignal <$> v .: "data"
      "scene"  -> SceneBrandSignal <$> v .: "data"
      "speech" -> SpeechBrandSignal <$> v .: "data"
      "music"  -> MusicBrandSignal <$> v .: "data"
      other    -> fail $ "Unknown BrandSignal type: " <> T.unpack other

-- VideoAnalysisResult
instance ToJSON VideoAnalysisResult where
  toJSON var = object
    [ "videoPath"      .= varVideoPath var
    , "durationMs"     .= varDurationMs var
    , "dimensions"     .= varDimensions var
    , "textSignals"    .= varTextSignals var
    , "logoSignals"    .= varLogoSignals var
    , "colorSignals"   .= varColorSignals var
    , "sceneSignals"   .= varSceneSignals var
    , "speechSignals"  .= varSpeechSignals var
    , "musicSignals"   .= varMusicSignals var
    , "analyzedAt"     .= varAnalyzedAt var
    , "modelVersions"  .= varModelVersions var
    ]

instance FromJSON VideoAnalysisResult where
  parseJSON = withObject "VideoAnalysisResult" $ \v -> VideoAnalysisResult
    <$> v .: "videoPath"
    <*> v .: "durationMs"
    <*> v .: "dimensions"
    <*> v .: "textSignals"
    <*> v .: "logoSignals"
    <*> v .: "colorSignals"
    <*> v .: "sceneSignals"
    <*> v .: "speechSignals"
    <*> v .: "musicSignals"
    <*> v .: "analyzedAt"
    <*> v .: "modelVersions"

-- AnalysisType
instance ToJSON AnalysisType where
  toJSON OCRAnalysis         = "ocr"
  toJSON LogoDetection       = "logo_detection"
  toJSON ColorExtraction     = "color_extraction"
  toJSON SceneAnalysis_      = "scene_analysis"
  toJSON SpeechTranscription = "speech_transcription"
  toJSON MusicAnalysis       = "music_analysis"
  toJSON FullAnalysis        = "full"

instance FromJSON AnalysisType where
  parseJSON = withText "AnalysisType" $ \case
    "ocr"                  -> pure OCRAnalysis
    "logo_detection"       -> pure LogoDetection
    "color_extraction"     -> pure ColorExtraction
    "scene_analysis"       -> pure SceneAnalysis_
    "speech_transcription" -> pure SpeechTranscription
    "music_analysis"       -> pure MusicAnalysis
    "full"                 -> pure FullAnalysis
    other                  -> fail $ "Unknown AnalysisType: " <> T.unpack other

-- VideoAnalysisRequest
instance ToJSON VideoAnalysisRequest where
  toJSON req = object
    [ "videoPath"     .= varqVideoPath req
    , "analysisTypes" .= varqAnalysisTypes req
    , "frameRate"     .= varqFrameRate req
    , "maxDuration"   .= varqMaxDuration req
    ]

instance FromJSON VideoAnalysisRequest where
  parseJSON = withObject "VideoAnalysisRequest" $ \v -> VideoAnalysisRequest
    <$> v .: "videoPath"
    <*> v .: "analysisTypes"
    <*> v .: "frameRate"
    <*> v .:? "maxDuration"
