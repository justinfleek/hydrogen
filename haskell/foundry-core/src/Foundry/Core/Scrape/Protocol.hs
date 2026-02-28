{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // foundry // scrape/protocol
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Scrape.Protocol
Description : ZMQ message protocol for scraper communication
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the message types for communication between the Haskell backend
and scraping workers. Messages are serialized as JSON over ZMQ.

== Protocol Overview

The scraping system uses a request-response pattern with ZMQ DEALER/ROUTER:

  Backend (ROUTER) <---> Worker Pool (DEALER) <---> Workers

Request types:
  - JobRequest: Assign a job to a worker
  - HealthCheckRequest: Check worker health
  - CancelRequest: Cancel a running job
  - ShutdownRequest: Graceful worker shutdown

Response types:
  - JobResponse: Job completion result
  - HealthCheckResponse: Worker health status
  - ProgressUpdate: Streaming progress during job execution
  - ErrorResponse: Error occurred

== Wire Format

All messages are JSON-encoded with a type discriminator:

  { "type": "job_request", "payload": { ... } }

== Dependencies

Requires: Foundry.Core.Scrape.Job, Foundry.Core.Scrape.Worker
Required by: Foundry.Scrape.Orchestrator (when ZMQ is available)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Scrape.Protocol
  ( -- * Message Envelope
    MessageId (..)
  , mkMessageId
  , Envelope (..)
  
    -- * Request Types
  , Request (..)
  , JobRequest (..)
  , HealthCheckRequest (..)
  , CancelRequest (..)
  , ShutdownRequest (..)
  
    -- * Response Types
  , Response (..)
  , JobResponse (..)
  , HealthCheckResponse (..)
  , ProgressUpdate (..)
  , ErrorResponse (..)
  , ErrorCode (..)
  
    -- * Model Requests (for AI models)
  , ModelRequest (..)
  , VisionRequest (..)
  , AudioRequest (..)
  , TTSRequest (..)
  , MusicGenRequest (..)
  
    -- * Model Responses
  , ModelResponse (..)
  , VisionResponse (..)
  , AudioResponse (..)
  , TTSResponse (..)
  , MusicGenResponse (..)
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), (.:?), object, withObject, withText)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Word (Word32, Word64)
import Foundry.Core.Scrape.Job 
  ( JobId
  , ScrapeJob
  , ScrapeResult
  , JobStatus
  , ExtractionTarget
  )
import Foundry.Core.Scrape.Worker
  ( WorkerId
  , WorkerHealth
  , WorkerMetrics
  )

--------------------------------------------------------------------------------
-- Message Envelope
--------------------------------------------------------------------------------

-- | Unique message identifier for correlation
newtype MessageId = MessageId { unMessageId :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create message ID (should be UUID in real implementation)
mkMessageId :: Word64 -> Text -> MessageId
mkMessageId ts rand = MessageId $ T.pack (show ts) <> "-" <> rand

instance ToJSON MessageId where
  toJSON (MessageId t) = toJSON t

instance FromJSON MessageId where
  parseJSON = withText "MessageId" (pure . MessageId)

-- | Message envelope wrapping all protocol messages
--
-- Every message has an ID for correlation and a timestamp.
data Envelope a = Envelope
  { envId        :: !MessageId
    -- ^ Unique message ID
  , envTimestamp :: !Word64
    -- ^ Message creation timestamp (unix millis)
  , envSource    :: !Text
    -- ^ Source identifier (backend ID or worker ID)
  , envPayload   :: !a
    -- ^ The actual message
  }
  deriving stock (Eq, Show)

instance ToJSON a => ToJSON (Envelope a) where
  toJSON env = object
    [ "id"        .= envId env
    , "timestamp" .= envTimestamp env
    , "source"    .= envSource env
    , "payload"   .= envPayload env
    ]

instance FromJSON a => FromJSON (Envelope a) where
  parseJSON = withObject "Envelope" $ \v -> Envelope
    <$> v .: "id"
    <*> v .: "timestamp"
    <*> v .: "source"
    <*> v .: "payload"

--------------------------------------------------------------------------------
-- Request Types
--------------------------------------------------------------------------------

-- | Request to execute a scraping job
data JobRequest = JobRequest
  { jrJob         :: !ScrapeJob
    -- ^ The job to execute
  , jrPriority    :: !Word32
    -- ^ Numeric priority (higher = more urgent)
  , jrDeadline    :: !(Maybe Word64)
    -- ^ Optional deadline timestamp
  }
  deriving stock (Eq, Show)

instance ToJSON JobRequest where
  toJSON jr = object
    [ "job"      .= jrJob jr
    , "priority" .= jrPriority jr
    , "deadline" .= jrDeadline jr
    ]

instance FromJSON JobRequest where
  parseJSON = withObject "JobRequest" $ \v -> JobRequest
    <$> v .: "job"
    <*> v .: "priority"
    <*> v .:? "deadline"

-- | Request for worker health check
data HealthCheckRequest = HealthCheckRequest
  { hcrWorkerId :: !WorkerId
    -- ^ Which worker to check
  , hcrDeep     :: !Bool
    -- ^ Perform deep health check (slower but more thorough)
  }
  deriving stock (Eq, Show)

instance ToJSON HealthCheckRequest where
  toJSON hcr = object
    [ "workerId" .= hcrWorkerId hcr
    , "deep"     .= hcrDeep hcr
    ]

instance FromJSON HealthCheckRequest where
  parseJSON = withObject "HealthCheckRequest" $ \v -> HealthCheckRequest
    <$> v .: "workerId"
    <*> v .: "deep"

-- | Request to cancel a running job
data CancelRequest = CancelRequest
  { crJobId     :: !JobId
    -- ^ Job to cancel
  , crReason    :: !Text
    -- ^ Why the job is being cancelled
  , crForce     :: !Bool
    -- ^ Force immediate termination (vs graceful)
  }
  deriving stock (Eq, Show)

instance ToJSON CancelRequest where
  toJSON cr = object
    [ "jobId"  .= crJobId cr
    , "reason" .= crReason cr
    , "force"  .= crForce cr
    ]

instance FromJSON CancelRequest where
  parseJSON = withObject "CancelRequest" $ \v -> CancelRequest
    <$> v .: "jobId"
    <*> v .: "reason"
    <*> v .: "force"

-- | Request for graceful worker shutdown
data ShutdownRequest = ShutdownRequest
  { srWorkerId   :: !WorkerId
    -- ^ Which worker to shut down
  , srGracePeriod :: !Word32
    -- ^ Seconds to wait for current job
  , srReason     :: !Text
    -- ^ Why the worker is being shut down
  }
  deriving stock (Eq, Show)

instance ToJSON ShutdownRequest where
  toJSON sr = object
    [ "workerId"    .= srWorkerId sr
    , "gracePeriod" .= srGracePeriod sr
    , "reason"      .= srReason sr
    ]

instance FromJSON ShutdownRequest where
  parseJSON = withObject "ShutdownRequest" $ \v -> ShutdownRequest
    <$> v .: "workerId"
    <*> v .: "gracePeriod"
    <*> v .: "reason"

-- | All request types (sum type for protocol)
data Request
  = ReqJob !JobRequest
  | ReqHealthCheck !HealthCheckRequest
  | ReqCancel !CancelRequest
  | ReqShutdown !ShutdownRequest
  deriving stock (Eq, Show)

instance ToJSON Request where
  toJSON (ReqJob jr)        = object ["type" .= ("job" :: Text), "data" .= jr]
  toJSON (ReqHealthCheck h) = object ["type" .= ("health_check" :: Text), "data" .= h]
  toJSON (ReqCancel c)      = object ["type" .= ("cancel" :: Text), "data" .= c]
  toJSON (ReqShutdown s)    = object ["type" .= ("shutdown" :: Text), "data" .= s]

instance FromJSON Request where
  parseJSON = withObject "Request" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "job"          -> ReqJob <$> v .: "data"
      "health_check" -> ReqHealthCheck <$> v .: "data"
      "cancel"       -> ReqCancel <$> v .: "data"
      "shutdown"     -> ReqShutdown <$> v .: "data"
      other          -> fail $ "Unknown Request type: " <> T.unpack other

--------------------------------------------------------------------------------
-- Response Types
--------------------------------------------------------------------------------

-- | Standard error codes
data ErrorCode
  = ErrTimeout
    -- ^ Operation timed out
  | ErrNetworkFailure
    -- ^ Network error (DNS, connection, etc.)
  | ErrBrowserCrash
    -- ^ Browser process crashed
  | ErrResourceExhausted
    -- ^ Out of memory/CPU/etc.
  | ErrInvalidJob
    -- ^ Job configuration invalid
  | ErrCancelled
    -- ^ Job was cancelled
  | ErrInternal
    -- ^ Internal error
  | ErrUnknown
    -- ^ Unknown error
  deriving stock (Eq, Show, Enum, Bounded)

instance ToJSON ErrorCode where
  toJSON ErrTimeout           = "timeout"
  toJSON ErrNetworkFailure    = "network_failure"
  toJSON ErrBrowserCrash      = "browser_crash"
  toJSON ErrResourceExhausted = "resource_exhausted"
  toJSON ErrInvalidJob        = "invalid_job"
  toJSON ErrCancelled         = "cancelled"
  toJSON ErrInternal          = "internal"
  toJSON ErrUnknown           = "unknown"

instance FromJSON ErrorCode where
  parseJSON = withText "ErrorCode" $ \case
    "timeout"            -> pure ErrTimeout
    "network_failure"    -> pure ErrNetworkFailure
    "browser_crash"      -> pure ErrBrowserCrash
    "resource_exhausted" -> pure ErrResourceExhausted
    "invalid_job"        -> pure ErrInvalidJob
    "cancelled"          -> pure ErrCancelled
    "internal"           -> pure ErrInternal
    "unknown"            -> pure ErrUnknown
    other                -> fail $ "Unknown ErrorCode: " <> T.unpack other

-- | Response with job completion result
data JobResponse = JobResponse
  { jrespJobId   :: !JobId
    -- ^ Which job this is for
  , jrespResult  :: !ScrapeResult
    -- ^ The scraping result
  , jrespWorkerId :: !WorkerId
    -- ^ Which worker processed it
  }
  deriving stock (Eq, Show)

instance ToJSON JobResponse where
  toJSON jr = object
    [ "jobId"    .= jrespJobId jr
    , "result"   .= jrespResult jr
    , "workerId" .= jrespWorkerId jr
    ]

instance FromJSON JobResponse where
  parseJSON = withObject "JobResponse" $ \v -> JobResponse
    <$> v .: "jobId"
    <*> v .: "result"
    <*> v .: "workerId"

-- | Response to health check
data HealthCheckResponse = HealthCheckResponse
  { hcrespWorkerId :: !WorkerId
    -- ^ Which worker was checked
  , hcrespHealth   :: !WorkerHealth
    -- ^ Health status
  , hcrespMetrics  :: !WorkerMetrics
    -- ^ Current metrics
  , hcrespTimestamp :: !Word64
    -- ^ When the check was performed
  }
  deriving stock (Eq, Show)

instance ToJSON HealthCheckResponse where
  toJSON hcr = object
    [ "workerId"  .= hcrespWorkerId hcr
    , "health"    .= hcrespHealth hcr
    , "metrics"   .= hcrespMetrics hcr
    , "timestamp" .= hcrespTimestamp hcr
    ]

instance FromJSON HealthCheckResponse where
  parseJSON = withObject "HealthCheckResponse" $ \v -> HealthCheckResponse
    <$> v .: "workerId"
    <*> v .: "health"
    <*> v .: "metrics"
    <*> v .: "timestamp"

-- | Progress update during job execution (streaming)
data ProgressUpdate = ProgressUpdate
  { puJobId      :: !JobId
    -- ^ Which job this is for
  , puWorkerId   :: !WorkerId
    -- ^ Which worker is processing
  , puPhase      :: !Text
    -- ^ Current phase (e.g., "loading", "extracting")
  , puTarget     :: !(Maybe ExtractionTarget)
    -- ^ Current extraction target (if applicable)
  , puProgress   :: !Double
    -- ^ Progress 0.0 - 1.0
  , puMessage    :: !Text
    -- ^ Human-readable status
  , puTimestamp  :: !Word64
    -- ^ When this update was generated
  }
  deriving stock (Eq, Show)

instance ToJSON ProgressUpdate where
  toJSON pu = object
    [ "jobId"     .= puJobId pu
    , "workerId"  .= puWorkerId pu
    , "phase"     .= puPhase pu
    , "target"    .= puTarget pu
    , "progress"  .= puProgress pu
    , "message"   .= puMessage pu
    , "timestamp" .= puTimestamp pu
    ]

instance FromJSON ProgressUpdate where
  parseJSON = withObject "ProgressUpdate" $ \v -> ProgressUpdate
    <$> v .: "jobId"
    <*> v .: "workerId"
    <*> v .: "phase"
    <*> v .:? "target"
    <*> v .: "progress"
    <*> v .: "message"
    <*> v .: "timestamp"

-- | Error response
data ErrorResponse = ErrorResponse
  { erCode      :: !ErrorCode
    -- ^ Error code
  , erMessage   :: !Text
    -- ^ Human-readable message
  , erJobId     :: !(Maybe JobId)
    -- ^ Related job (if applicable)
  , erWorkerId  :: !(Maybe WorkerId)
    -- ^ Related worker (if applicable)
  , erRetryable :: !Bool
    -- ^ Can this be retried
  , erTimestamp :: !Word64
    -- ^ When the error occurred
  }
  deriving stock (Eq, Show)

instance ToJSON ErrorResponse where
  toJSON er = object
    [ "code"      .= erCode er
    , "message"   .= erMessage er
    , "jobId"     .= erJobId er
    , "workerId"  .= erWorkerId er
    , "retryable" .= erRetryable er
    , "timestamp" .= erTimestamp er
    ]

instance FromJSON ErrorResponse where
  parseJSON = withObject "ErrorResponse" $ \v -> ErrorResponse
    <$> v .: "code"
    <*> v .: "message"
    <*> v .:? "jobId"
    <*> v .:? "workerId"
    <*> v .: "retryable"
    <*> v .: "timestamp"

-- | All response types (sum type for protocol)
data Response
  = RespJob !JobResponse
  | RespHealthCheck !HealthCheckResponse
  | RespProgress !ProgressUpdate
  | RespError !ErrorResponse
  deriving stock (Eq, Show)

instance ToJSON Response where
  toJSON (RespJob jr)        = object ["type" .= ("job" :: Text), "data" .= jr]
  toJSON (RespHealthCheck h) = object ["type" .= ("health_check" :: Text), "data" .= h]
  toJSON (RespProgress p)    = object ["type" .= ("progress" :: Text), "data" .= p]
  toJSON (RespError e)       = object ["type" .= ("error" :: Text), "data" .= e]

instance FromJSON Response where
  parseJSON = withObject "Response" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "job"          -> RespJob <$> v .: "data"
      "health_check" -> RespHealthCheck <$> v .: "data"
      "progress"     -> RespProgress <$> v .: "data"
      "error"        -> RespError <$> v .: "data"
      other          -> fail $ "Unknown Response type: " <> T.unpack other

--------------------------------------------------------------------------------
-- Model Requests (for AI models like Qwen, CosyVoice, ACE-Step)
--------------------------------------------------------------------------------

-- | Request for vision model analysis (Qwen2.5-VL)
data VisionRequest = VisionRequest
  { vrImagePaths  :: !(Vector Text)
    -- ^ Paths to images to analyze
  , vrVideoPath   :: !(Maybe Text)
    -- ^ Path to video (alternative to images)
  , vrPrompt      :: !Text
    -- ^ Analysis prompt
  , vrMaxTokens   :: !Word32
    -- ^ Maximum output tokens
  , vrTemperature :: !Double
    -- ^ Sampling temperature
  }
  deriving stock (Eq, Show)

instance ToJSON VisionRequest where
  toJSON vr = object
    [ "imagePaths"  .= vrImagePaths vr
    , "videoPath"   .= vrVideoPath vr
    , "prompt"      .= vrPrompt vr
    , "maxTokens"   .= vrMaxTokens vr
    , "temperature" .= vrTemperature vr
    ]

instance FromJSON VisionRequest where
  parseJSON = withObject "VisionRequest" $ \v -> VisionRequest
    <$> v .: "imagePaths"
    <*> v .:? "videoPath"
    <*> v .: "prompt"
    <*> v .: "maxTokens"
    <*> v .: "temperature"

-- | Request for audio analysis (Qwen2-Audio)
data AudioRequest = AudioRequest
  { arAudioPath   :: !Text
    -- ^ Path to audio file
  , arPrompt      :: !Text
    -- ^ Analysis prompt
  , arTask        :: !Text
    -- ^ Task: "transcribe", "analyze", "classify"
  , arLanguage    :: !(Maybe Text)
    -- ^ Expected language (for transcription)
  }
  deriving stock (Eq, Show)

instance ToJSON AudioRequest where
  toJSON ar = object
    [ "audioPath" .= arAudioPath ar
    , "prompt"    .= arPrompt ar
    , "task"      .= arTask ar
    , "language"  .= arLanguage ar
    ]

instance FromJSON AudioRequest where
  parseJSON = withObject "AudioRequest" $ \v -> AudioRequest
    <$> v .: "audioPath"
    <*> v .: "prompt"
    <*> v .: "task"
    <*> v .:? "language"

-- | Request for TTS generation (CosyVoice)
data TTSRequest = TTSRequest
  { ttsText         :: !Text
    -- ^ Text to synthesize
  , ttsInstruction  :: !Text
    -- ^ CosyVoice instruction (emotion, pace, etc.)
  , ttsRefAudioPath :: !(Maybe Text)
    -- ^ Reference audio for voice cloning
  , ttsRefText      :: !(Maybe Text)
    -- ^ Transcript of reference audio
  , ttsSpeakerId    :: !(Maybe Text)
    -- ^ Saved speaker ID (alternative to reference audio)
  }
  deriving stock (Eq, Show)

instance ToJSON TTSRequest where
  toJSON tts = object
    [ "text"         .= ttsText tts
    , "instruction"  .= ttsInstruction tts
    , "refAudioPath" .= ttsRefAudioPath tts
    , "refText"      .= ttsRefText tts
    , "speakerId"    .= ttsSpeakerId tts
    ]

instance FromJSON TTSRequest where
  parseJSON = withObject "TTSRequest" $ \v -> TTSRequest
    <$> v .: "text"
    <*> v .: "instruction"
    <*> v .:? "refAudioPath"
    <*> v .:? "refText"
    <*> v .:? "speakerId"

-- | Request for music generation (ACE-Step)
data MusicGenRequest = MusicGenRequest
  { mgrTags          :: !Text
    -- ^ Comma-separated style tags
  , mgrLyrics        :: !(Maybe Text)
    -- ^ Structured lyrics (optional)
  , mgrDurationSec   :: !Word32
    -- ^ Desired duration
  , mgrGuidanceScale :: !Double
    -- ^ Guidance scale for prompt adherence
  , mgrSeed          :: !(Maybe Word32)
    -- ^ Random seed for reproducibility
  , mgrLoraPath      :: !(Maybe Text)
    -- ^ Path to LoRA weights
  }
  deriving stock (Eq, Show)

instance ToJSON MusicGenRequest where
  toJSON mgr = object
    [ "tags"          .= mgrTags mgr
    , "lyrics"        .= mgrLyrics mgr
    , "durationSec"   .= mgrDurationSec mgr
    , "guidanceScale" .= mgrGuidanceScale mgr
    , "seed"          .= mgrSeed mgr
    , "loraPath"      .= mgrLoraPath mgr
    ]

instance FromJSON MusicGenRequest where
  parseJSON = withObject "MusicGenRequest" $ \v -> MusicGenRequest
    <$> v .: "tags"
    <*> v .:? "lyrics"
    <*> v .: "durationSec"
    <*> v .: "guidanceScale"
    <*> v .:? "seed"
    <*> v .:? "loraPath"

-- | All model request types
data ModelRequest
  = MReqVision !VisionRequest
  | MReqAudio !AudioRequest
  | MReqTTS !TTSRequest
  | MReqMusicGen !MusicGenRequest
  deriving stock (Eq, Show)

instance ToJSON ModelRequest where
  toJSON (MReqVision vr)   = object ["type" .= ("vision" :: Text), "data" .= vr]
  toJSON (MReqAudio ar)    = object ["type" .= ("audio" :: Text), "data" .= ar]
  toJSON (MReqTTS tts)     = object ["type" .= ("tts" :: Text), "data" .= tts]
  toJSON (MReqMusicGen mg) = object ["type" .= ("music_gen" :: Text), "data" .= mg]

instance FromJSON ModelRequest where
  parseJSON = withObject "ModelRequest" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "vision"    -> MReqVision <$> v .: "data"
      "audio"     -> MReqAudio <$> v .: "data"
      "tts"       -> MReqTTS <$> v .: "data"
      "music_gen" -> MReqMusicGen <$> v .: "data"
      other       -> fail $ "Unknown ModelRequest type: " <> T.unpack other

--------------------------------------------------------------------------------
-- Model Responses
--------------------------------------------------------------------------------

-- | Response from vision model
data VisionResponse = VisionResponse
  { vrespText       :: !Text
    -- ^ Generated text/analysis
  , vrespTokens     :: !Word32
    -- ^ Tokens used
  , vrespDurationMs :: !Word32
    -- ^ Inference duration
  }
  deriving stock (Eq, Show)

instance ToJSON VisionResponse where
  toJSON vr = object
    [ "text"       .= vrespText vr
    , "tokens"     .= vrespTokens vr
    , "durationMs" .= vrespDurationMs vr
    ]

instance FromJSON VisionResponse where
  parseJSON = withObject "VisionResponse" $ \v -> VisionResponse
    <$> v .: "text"
    <*> v .: "tokens"
    <*> v .: "durationMs"

-- | Response from audio model
data AudioResponse = AudioResponse
  { arespText       :: !Text
    -- ^ Transcription or analysis result
  , arespLanguage   :: !(Maybe Text)
    -- ^ Detected language
  , arespDurationMs :: !Word32
    -- ^ Inference duration
  }
  deriving stock (Eq, Show)

instance ToJSON AudioResponse where
  toJSON ar = object
    [ "text"       .= arespText ar
    , "language"   .= arespLanguage ar
    , "durationMs" .= arespDurationMs ar
    ]

instance FromJSON AudioResponse where
  parseJSON = withObject "AudioResponse" $ \v -> AudioResponse
    <$> v .: "text"
    <*> v .:? "language"
    <*> v .: "durationMs"

-- | Response from TTS model
data TTSResponse = TTSResponse
  { ttsrespAudioPath :: !Text
    -- ^ Path to generated audio
  , ttsrespDurationMs :: !Word32
    -- ^ Audio duration in milliseconds
  , ttsrespSampleRate :: !Word32
    -- ^ Audio sample rate
  , ttsrespInferenceMs :: !Word32
    -- ^ Inference duration
  }
  deriving stock (Eq, Show)

instance ToJSON TTSResponse where
  toJSON tts = object
    [ "audioPath"   .= ttsrespAudioPath tts
    , "durationMs"  .= ttsrespDurationMs tts
    , "sampleRate"  .= ttsrespSampleRate tts
    , "inferenceMs" .= ttsrespInferenceMs tts
    ]

instance FromJSON TTSResponse where
  parseJSON = withObject "TTSResponse" $ \v -> TTSResponse
    <$> v .: "audioPath"
    <*> v .: "durationMs"
    <*> v .: "sampleRate"
    <*> v .: "inferenceMs"

-- | Response from music generation model
data MusicGenResponse = MusicGenResponse
  { mgrrespAudioPath  :: !Text
    -- ^ Path to generated audio
  , mgrrespDurationMs :: !Word32
    -- ^ Audio duration
  , mgrrespSeed       :: !Word32
    -- ^ Seed used (for reproducibility)
  , mgrrespInferenceMs :: !Word32
    -- ^ Inference duration
  }
  deriving stock (Eq, Show)

instance ToJSON MusicGenResponse where
  toJSON mgr = object
    [ "audioPath"   .= mgrrespAudioPath mgr
    , "durationMs"  .= mgrrespDurationMs mgr
    , "seed"        .= mgrrespSeed mgr
    , "inferenceMs" .= mgrrespInferenceMs mgr
    ]

instance FromJSON MusicGenResponse where
  parseJSON = withObject "MusicGenResponse" $ \v -> MusicGenResponse
    <$> v .: "audioPath"
    <*> v .: "durationMs"
    <*> v .: "seed"
    <*> v .: "inferenceMs"

-- | All model response types
data ModelResponse
  = MRespVision !VisionResponse
  | MRespAudio !AudioResponse
  | MRespTTS !TTSResponse
  | MRespMusicGen !MusicGenResponse
  | MRespError !ErrorResponse
  deriving stock (Eq, Show)

instance ToJSON ModelResponse where
  toJSON (MRespVision vr)   = object ["type" .= ("vision" :: Text), "data" .= vr]
  toJSON (MRespAudio ar)    = object ["type" .= ("audio" :: Text), "data" .= ar]
  toJSON (MRespTTS tts)     = object ["type" .= ("tts" :: Text), "data" .= tts]
  toJSON (MRespMusicGen mg) = object ["type" .= ("music_gen" :: Text), "data" .= mg]
  toJSON (MRespError e)     = object ["type" .= ("error" :: Text), "data" .= e]

instance FromJSON ModelResponse where
  parseJSON = withObject "ModelResponse" $ \v -> do
    typ <- v .: "type"
    case (typ :: Text) of
      "vision"    -> MRespVision <$> v .: "data"
      "audio"     -> MRespAudio <$> v .: "data"
      "tts"       -> MRespTTS <$> v .: "data"
      "music_gen" -> MRespMusicGen <$> v .: "data"
      "error"     -> MRespError <$> v .: "data"
      other       -> fail $ "Unknown ModelResponse type: " <> T.unpack other
