{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // foundry // scrape/job
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Scrape.Job
Description : Scraping job types and queue management
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the job queue types for brand scraping orchestration. Jobs are
pure data that describe what to scrape and how - no side effects here.

== Design Principles

1. Jobs are pure data - no IO, no side effects
2. Every job has a deterministic ID (UUID5 from URL + timestamp)
3. Jobs track their full lifecycle with timestamps
4. Results are typed - we know exactly what we extracted

== Isolation Levels

Jobs can request different isolation levels based on threat model:

* Container - Standard container (fastest, least isolated)
* GVisor - gVisor sandbox (balanced security/performance)
* Firecracker - Full microVM (strongest isolation, bare metal only)

== Dependencies

Requires: Nothing (standalone types)
Required by: Foundry.Core.Scrape.Worker, Foundry.Core.Scrape.Queue

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Scrape.Job
  ( -- * Job Identification
    JobId (..)
  , mkJobId
  
    -- * Job Configuration
  , ScrapeTarget (..)
  , mkScrapeTarget
  , IsolationLevel (..)
  , BrowserConfig (..)
  , defaultBrowserConfig
  , ResourceLimits (..)
  , defaultResourceLimits
  
    -- * Extraction Configuration
  , ExtractionConfig (..)
  , ExtractionTarget (..)
  , defaultExtractionConfig
  
    -- * Job Definition
  , ScrapeJob (..)
  , mkScrapeJob
  , JobPriority (..)
  
    -- * Job Lifecycle
  , JobStatus (..)
  , JobEvent (..)
  , JobTimestamps (..)
  
    -- * Job Results
  , ScrapeResult (..)
  , ExtractionResult (..)
  , ScrapeError (..)
  , ErrorSeverity (..)
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), (.:?), object, withObject, withText)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Word (Word16, Word32, Word64)

--------------------------------------------------------------------------------
-- Job Identification
--------------------------------------------------------------------------------

-- | Unique job identifier (UUID5 from URL + creation timestamp)
--
-- Deterministic: same URL + same timestamp = same JobId
-- This enables reproducibility and deduplication.
newtype JobId = JobId { unJobId :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create job ID (should be UUID5 in real implementation)
mkJobId :: Text -> Word64 -> JobId
mkJobId url timestamp = JobId $ url <> "-" <> T.pack (show timestamp)

instance ToJSON JobId where
  toJSON (JobId t) = toJSON t

instance FromJSON JobId where
  parseJSON = withText "JobId" (pure . JobId)

--------------------------------------------------------------------------------
-- Job Configuration
--------------------------------------------------------------------------------

-- | Target URL and metadata for scraping
data ScrapeTarget = ScrapeTarget
  { stUrl           :: !Text
    -- ^ URL to scrape (must be HTTPS)
  , stDomain        :: !Text
    -- ^ Extracted domain (e.g., "stripe.com")
  , stFollowLinks   :: !Bool
    -- ^ Whether to follow internal links
  , stMaxDepth      :: !Word16
    -- ^ Maximum link depth to follow (0 = just this page)
  , stMaxPages      :: !Word16
    -- ^ Maximum pages to scrape total
  , stAllowedPaths  :: !(Set Text)
    -- ^ Path prefixes to allow (empty = all)
  , stBlockedPaths  :: !(Set Text)
    -- ^ Path prefixes to block
  }
  deriving stock (Eq, Show)

-- | Create scrape target with validation
mkScrapeTarget :: Text -> Maybe ScrapeTarget
mkScrapeTarget url
  | not (T.isPrefixOf "https://" url) = Nothing  -- HTTPS only
  | otherwise = Just ScrapeTarget
      { stUrl = url
      , stDomain = extractDomain url
      , stFollowLinks = False
      , stMaxDepth = 0
      , stMaxPages = 1
      , stAllowedPaths = Set.empty
      , stBlockedPaths = Set.empty
      }
  where
    extractDomain :: Text -> Text
    extractDomain u = 
      let withoutScheme = T.drop 8 u  -- Drop "https://"
      in T.takeWhile (/= '/') withoutScheme

instance ToJSON ScrapeTarget where
  toJSON st = object
    [ "url"          .= stUrl st
    , "domain"       .= stDomain st
    , "followLinks"  .= stFollowLinks st
    , "maxDepth"     .= stMaxDepth st
    , "maxPages"     .= stMaxPages st
    , "allowedPaths" .= Set.toList (stAllowedPaths st)
    , "blockedPaths" .= Set.toList (stBlockedPaths st)
    ]

instance FromJSON ScrapeTarget where
  parseJSON = withObject "ScrapeTarget" $ \v -> ScrapeTarget
    <$> v .: "url"
    <*> v .: "domain"
    <*> v .: "followLinks"
    <*> v .: "maxDepth"
    <*> v .: "maxPages"
    <*> (Set.fromList <$> v .: "allowedPaths")
    <*> (Set.fromList <$> v .: "blockedPaths")

-- | Isolation level for browser environment
--
-- Higher isolation = more security, more overhead.
data IsolationLevel
  = ContainerIsolation
    -- ^ Standard OCI container (runc)
    -- Fastest, least isolated
    -- Use for: trusted domains, internal testing
  | GVisorIsolation
    -- ^ gVisor sandbox (runsc)
    -- Balanced security/performance
    -- Use for: most external scraping
  | FirecrackerIsolation
    -- ^ Firecracker microVM
    -- Strongest isolation, requires bare metal
    -- Use for: high-value targets, untrusted sites
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance ToJSON IsolationLevel where
  toJSON ContainerIsolation   = "container"
  toJSON GVisorIsolation      = "gvisor"
  toJSON FirecrackerIsolation = "firecracker"

instance FromJSON IsolationLevel where
  parseJSON = withText "IsolationLevel" $ \case
    "container"   -> pure ContainerIsolation
    "gvisor"      -> pure GVisorIsolation
    "firecracker" -> pure FirecrackerIsolation
    other         -> fail $ "Unknown IsolationLevel: " <> T.unpack other

-- | Browser configuration for scraping
data BrowserConfig = BrowserConfig
  { bcBrowser       :: !Text
    -- ^ Browser type: "chromium", "firefox", "webkit"
  , bcHeadless      :: !Bool
    -- ^ Run in headless mode (always true for production)
  , bcViewportWidth :: !Word16
    -- ^ Viewport width in pixels
  , bcViewportHeight :: !Word16
    -- ^ Viewport height in pixels
  , bcUserAgent     :: !(Maybe Text)
    -- ^ Custom user agent (Nothing = browser default)
  , bcLocale        :: !Text
    -- ^ Browser locale (e.g., "en-US")
  , bcTimezone      :: !Text
    -- ^ Timezone (e.g., "America/New_York")
  , bcTimeout       :: !Word32
    -- ^ Page load timeout in milliseconds
  }
  deriving stock (Eq, Show)

-- | Default browser configuration
defaultBrowserConfig :: BrowserConfig
defaultBrowserConfig = BrowserConfig
  { bcBrowser = "chromium"
  , bcHeadless = True
  , bcViewportWidth = 1920
  , bcViewportHeight = 1080
  , bcUserAgent = Nothing
  , bcLocale = "en-US"
  , bcTimezone = "UTC"
  , bcTimeout = 30000  -- 30 seconds
  }

instance ToJSON BrowserConfig where
  toJSON bc = object
    [ "browser"        .= bcBrowser bc
    , "headless"       .= bcHeadless bc
    , "viewportWidth"  .= bcViewportWidth bc
    , "viewportHeight" .= bcViewportHeight bc
    , "userAgent"      .= bcUserAgent bc
    , "locale"         .= bcLocale bc
    , "timezone"       .= bcTimezone bc
    , "timeout"        .= bcTimeout bc
    ]

instance FromJSON BrowserConfig where
  parseJSON = withObject "BrowserConfig" $ \v -> BrowserConfig
    <$> v .: "browser"
    <*> v .: "headless"
    <*> v .: "viewportWidth"
    <*> v .: "viewportHeight"
    <*> v .:? "userAgent"
    <*> v .: "locale"
    <*> v .: "timezone"
    <*> v .: "timeout"

-- | Resource limits for scraping container/VM
data ResourceLimits = ResourceLimits
  { rlMemoryMB    :: !Word32
    -- ^ Maximum memory in MB
  , rlCPUMillis   :: !Word32
    -- ^ CPU limit in millicores (1000 = 1 CPU)
  , rlTimeoutSec  :: !Word32
    -- ^ Maximum job duration in seconds
  , rlNetworkKBps :: !(Maybe Word32)
    -- ^ Network bandwidth limit (Nothing = unlimited)
  }
  deriving stock (Eq, Show)

-- | Default resource limits
defaultResourceLimits :: ResourceLimits
defaultResourceLimits = ResourceLimits
  { rlMemoryMB = 2048      -- 2GB
  , rlCPUMillis = 1000     -- 1 CPU
  , rlTimeoutSec = 300     -- 5 minutes
  , rlNetworkKBps = Nothing
  }

instance ToJSON ResourceLimits where
  toJSON rl = object
    [ "memoryMB"    .= rlMemoryMB rl
    , "cpuMillis"   .= rlCPUMillis rl
    , "timeoutSec"  .= rlTimeoutSec rl
    , "networkKBps" .= rlNetworkKBps rl
    ]

instance FromJSON ResourceLimits where
  parseJSON = withObject "ResourceLimits" $ \v -> ResourceLimits
    <$> v .: "memoryMB"
    <*> v .: "cpuMillis"
    <*> v .: "timeoutSec"
    <*> v .:? "networkKBps"

--------------------------------------------------------------------------------
-- Extraction Configuration
--------------------------------------------------------------------------------

-- | What to extract from the page
data ExtractionTarget
  = ExtractColors        -- ^ CSS colors, computed styles
  | ExtractTypography    -- ^ Font families, sizes, weights
  | ExtractSpacing       -- ^ Margins, padding, gaps
  | ExtractImages        -- ^ Image URLs, alt text, dimensions
  | ExtractLogos         -- ^ Logo detection via vision model
  | ExtractText          -- ^ All visible text content
  | ExtractMetadata      -- ^ Meta tags, OpenGraph, etc.
  | ExtractScreenshot    -- ^ Full page screenshot
  | ExtractDOM           -- ^ Serialized DOM structure
  | ExtractNetwork       -- ^ Network requests (fonts, assets)
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance ToJSON ExtractionTarget where
  toJSON ExtractColors     = "colors"
  toJSON ExtractTypography = "typography"
  toJSON ExtractSpacing    = "spacing"
  toJSON ExtractImages     = "images"
  toJSON ExtractLogos      = "logos"
  toJSON ExtractText       = "text"
  toJSON ExtractMetadata   = "metadata"
  toJSON ExtractScreenshot = "screenshot"
  toJSON ExtractDOM        = "dom"
  toJSON ExtractNetwork    = "network"

instance FromJSON ExtractionTarget where
  parseJSON = withText "ExtractionTarget" $ \case
    "colors"     -> pure ExtractColors
    "typography" -> pure ExtractTypography
    "spacing"    -> pure ExtractSpacing
    "images"     -> pure ExtractImages
    "logos"      -> pure ExtractLogos
    "text"       -> pure ExtractText
    "metadata"   -> pure ExtractMetadata
    "screenshot" -> pure ExtractScreenshot
    "dom"        -> pure ExtractDOM
    "network"    -> pure ExtractNetwork
    other        -> fail $ "Unknown ExtractionTarget: " <> T.unpack other

-- | Configuration for what to extract
data ExtractionConfig = ExtractionConfig
  { ecTargets         :: !(Set ExtractionTarget)
    -- ^ What to extract
  , ecWaitForSelector :: !(Maybe Text)
    -- ^ CSS selector to wait for before extraction
  , ecWaitForTimeout  :: !Word32
    -- ^ How long to wait for selector (ms)
  , ecScrollToBottom  :: !Bool
    -- ^ Scroll to bottom to trigger lazy loading
  , ecClickCookieBanner :: !Bool
    -- ^ Attempt to dismiss cookie banners
  }
  deriving stock (Eq, Show)

-- | Default extraction config (extract everything)
defaultExtractionConfig :: ExtractionConfig
defaultExtractionConfig = ExtractionConfig
  { ecTargets = Set.fromList [minBound .. maxBound]
  , ecWaitForSelector = Nothing
  , ecWaitForTimeout = 5000
  , ecScrollToBottom = True
  , ecClickCookieBanner = True
  }

instance ToJSON ExtractionConfig where
  toJSON ec = object
    [ "targets"           .= Set.toList (ecTargets ec)
    , "waitForSelector"   .= ecWaitForSelector ec
    , "waitForTimeout"    .= ecWaitForTimeout ec
    , "scrollToBottom"    .= ecScrollToBottom ec
    , "clickCookieBanner" .= ecClickCookieBanner ec
    ]

instance FromJSON ExtractionConfig where
  parseJSON = withObject "ExtractionConfig" $ \v -> ExtractionConfig
    <$> (Set.fromList <$> v .: "targets")
    <*> v .:? "waitForSelector"
    <*> v .: "waitForTimeout"
    <*> v .: "scrollToBottom"
    <*> v .: "clickCookieBanner"

--------------------------------------------------------------------------------
-- Job Definition
--------------------------------------------------------------------------------

-- | Job priority level
data JobPriority
  = LowPriority      -- ^ Background processing
  | NormalPriority   -- ^ Standard priority
  | HighPriority     -- ^ Expedited processing
  | CriticalPriority -- ^ Immediate processing
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance ToJSON JobPriority where
  toJSON LowPriority      = "low"
  toJSON NormalPriority   = "normal"
  toJSON HighPriority     = "high"
  toJSON CriticalPriority = "critical"

instance FromJSON JobPriority where
  parseJSON = withText "JobPriority" $ \case
    "low"      -> pure LowPriority
    "normal"   -> pure NormalPriority
    "high"     -> pure HighPriority
    "critical" -> pure CriticalPriority
    other      -> fail $ "Unknown JobPriority: " <> T.unpack other

-- | Complete scraping job definition
--
-- This is the unit of work in the scraping pipeline.
-- Jobs are immutable once created - any changes create a new job.
data ScrapeJob = ScrapeJob
  { sjId             :: !JobId
    -- ^ Unique job identifier
  , sjTarget         :: !ScrapeTarget
    -- ^ What to scrape
  , sjIsolation      :: !IsolationLevel
    -- ^ How isolated the browser should be
  , sjBrowser        :: !BrowserConfig
    -- ^ Browser configuration
  , sjExtraction     :: !ExtractionConfig
    -- ^ What to extract
  , sjResources      :: !ResourceLimits
    -- ^ Resource constraints
  , sjPriority       :: !JobPriority
    -- ^ Processing priority
  , sjRetryCount     :: !Word16
    -- ^ How many times this job has been retried
  , sjMaxRetries     :: !Word16
    -- ^ Maximum retry attempts
  , sjParentJob      :: !(Maybe JobId)
    -- ^ Parent job (for link-following jobs)
  , sjTags           :: !(Set Text)
    -- ^ Arbitrary tags for grouping/filtering
  }
  deriving stock (Eq, Show)

-- | Create a scrape job with defaults
mkScrapeJob :: JobId -> ScrapeTarget -> ScrapeJob
mkScrapeJob jid target = ScrapeJob
  { sjId = jid
  , sjTarget = target
  , sjIsolation = GVisorIsolation  -- Default to gVisor
  , sjBrowser = defaultBrowserConfig
  , sjExtraction = defaultExtractionConfig
  , sjResources = defaultResourceLimits
  , sjPriority = NormalPriority
  , sjRetryCount = 0
  , sjMaxRetries = 3
  , sjParentJob = Nothing
  , sjTags = Set.empty
  }

instance ToJSON ScrapeJob where
  toJSON sj = object
    [ "id"          .= sjId sj
    , "target"      .= sjTarget sj
    , "isolation"   .= sjIsolation sj
    , "browser"     .= sjBrowser sj
    , "extraction"  .= sjExtraction sj
    , "resources"   .= sjResources sj
    , "priority"    .= sjPriority sj
    , "retryCount"  .= sjRetryCount sj
    , "maxRetries"  .= sjMaxRetries sj
    , "parentJob"   .= sjParentJob sj
    , "tags"        .= Set.toList (sjTags sj)
    ]

instance FromJSON ScrapeJob where
  parseJSON = withObject "ScrapeJob" $ \v -> ScrapeJob
    <$> v .: "id"
    <*> v .: "target"
    <*> v .: "isolation"
    <*> v .: "browser"
    <*> v .: "extraction"
    <*> v .: "resources"
    <*> v .: "priority"
    <*> v .: "retryCount"
    <*> v .: "maxRetries"
    <*> v .:? "parentJob"
    <*> (Set.fromList <$> v .: "tags")

--------------------------------------------------------------------------------
-- Job Lifecycle
--------------------------------------------------------------------------------

-- | Current status of a job
data JobStatus
  = JobPending
    -- ^ Waiting in queue
  | JobScheduled
    -- ^ Assigned to a worker
  | JobRunning
    -- ^ Currently executing
  | JobCompleted
    -- ^ Finished successfully
  | JobFailed
    -- ^ Failed (may retry)
  | JobCancelled
    -- ^ Cancelled by user/system
  | JobTimedOut
    -- ^ Exceeded time limit
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance ToJSON JobStatus where
  toJSON JobPending   = "pending"
  toJSON JobScheduled = "scheduled"
  toJSON JobRunning   = "running"
  toJSON JobCompleted = "completed"
  toJSON JobFailed    = "failed"
  toJSON JobCancelled = "cancelled"
  toJSON JobTimedOut  = "timed_out"

instance FromJSON JobStatus where
  parseJSON = withText "JobStatus" $ \case
    "pending"   -> pure JobPending
    "scheduled" -> pure JobScheduled
    "running"   -> pure JobRunning
    "completed" -> pure JobCompleted
    "failed"    -> pure JobFailed
    "cancelled" -> pure JobCancelled
    "timed_out" -> pure JobTimedOut
    other       -> fail $ "Unknown JobStatus: " <> T.unpack other

-- | Events that occur during job lifecycle
data JobEvent
  = JobCreated !Word64
    -- ^ Job was created (timestamp)
  | JobQueued !Word64
    -- ^ Job entered the queue
  | JobAssigned !Text !Word64
    -- ^ Job assigned to worker (worker ID, timestamp)
  | JobStarted !Word64
    -- ^ Execution started
  | JobProgress !Text !Word64
    -- ^ Progress update (message, timestamp)
  | JobRetrying !Word16 !Word64
    -- ^ Retrying (attempt number, timestamp)
  | JobFinished !JobStatus !Word64
    -- ^ Job finished (final status, timestamp)
  deriving stock (Eq, Show)

instance ToJSON JobEvent where
  toJSON (JobCreated ts)       = object ["event" .= ("created" :: Text), "timestamp" .= ts]
  toJSON (JobQueued ts)        = object ["event" .= ("queued" :: Text), "timestamp" .= ts]
  toJSON (JobAssigned w ts)    = object ["event" .= ("assigned" :: Text), "worker" .= w, "timestamp" .= ts]
  toJSON (JobStarted ts)       = object ["event" .= ("started" :: Text), "timestamp" .= ts]
  toJSON (JobProgress msg ts)  = object ["event" .= ("progress" :: Text), "message" .= msg, "timestamp" .= ts]
  toJSON (JobRetrying n ts)    = object ["event" .= ("retrying" :: Text), "attempt" .= n, "timestamp" .= ts]
  toJSON (JobFinished st ts)   = object ["event" .= ("finished" :: Text), "status" .= st, "timestamp" .= ts]

instance FromJSON JobEvent where
  parseJSON = withObject "JobEvent" $ \v -> do
    evt <- v .: "event"
    case (evt :: Text) of
      "created"  -> JobCreated <$> v .: "timestamp"
      "queued"   -> JobQueued <$> v .: "timestamp"
      "assigned" -> JobAssigned <$> v .: "worker" <*> v .: "timestamp"
      "started"  -> JobStarted <$> v .: "timestamp"
      "progress" -> JobProgress <$> v .: "message" <*> v .: "timestamp"
      "retrying" -> JobRetrying <$> v .: "attempt" <*> v .: "timestamp"
      "finished" -> JobFinished <$> v .: "status" <*> v .: "timestamp"
      other      -> fail $ "Unknown JobEvent: " <> T.unpack other

-- | Timestamps for job lifecycle tracking
data JobTimestamps = JobTimestamps
  { jtCreated   :: !Word64
  , jtQueued    :: !(Maybe Word64)
  , jtStarted   :: !(Maybe Word64)
  , jtCompleted :: !(Maybe Word64)
  }
  deriving stock (Eq, Show)

instance ToJSON JobTimestamps where
  toJSON jt = object
    [ "created"   .= jtCreated jt
    , "queued"    .= jtQueued jt
    , "started"   .= jtStarted jt
    , "completed" .= jtCompleted jt
    ]

instance FromJSON JobTimestamps where
  parseJSON = withObject "JobTimestamps" $ \v -> JobTimestamps
    <$> v .: "created"
    <*> v .:? "queued"
    <*> v .:? "started"
    <*> v .:? "completed"

--------------------------------------------------------------------------------
-- Job Results
--------------------------------------------------------------------------------

-- | Error severity level
data ErrorSeverity
  = WarningError    -- ^ Non-fatal, partial results available
  | RecoverableError -- ^ Failed but can retry
  | FatalError       -- ^ Cannot recover
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance ToJSON ErrorSeverity where
  toJSON WarningError     = "warning"
  toJSON RecoverableError = "recoverable"
  toJSON FatalError       = "fatal"

instance FromJSON ErrorSeverity where
  parseJSON = withText "ErrorSeverity" $ \case
    "warning"     -> pure WarningError
    "recoverable" -> pure RecoverableError
    "fatal"       -> pure FatalError
    other         -> fail $ "Unknown ErrorSeverity: " <> T.unpack other

-- | Scraping error
data ScrapeError = ScrapeError
  { seCode     :: !Text
    -- ^ Error code (e.g., "TIMEOUT", "DNS_FAILED")
  , seMessage  :: !Text
    -- ^ Human-readable message
  , seSeverity :: !ErrorSeverity
    -- ^ How severe is this error
  , seRetryable :: !Bool
    -- ^ Can this be retried
  , seTimestamp :: !Word64
    -- ^ When the error occurred
  }
  deriving stock (Eq, Show)

instance ToJSON ScrapeError where
  toJSON se = object
    [ "code"      .= seCode se
    , "message"   .= seMessage se
    , "severity"  .= seSeverity se
    , "retryable" .= seRetryable se
    , "timestamp" .= seTimestamp se
    ]

instance FromJSON ScrapeError where
  parseJSON = withObject "ScrapeError" $ \v -> ScrapeError
    <$> v .: "code"
    <*> v .: "message"
    <*> v .: "severity"
    <*> v .: "retryable"
    <*> v .: "timestamp"

-- | Result of a single extraction target
data ExtractionResult = ExtractionResult
  { erTarget     :: !ExtractionTarget
    -- ^ What was extracted
  , erSuccess    :: !Bool
    -- ^ Whether extraction succeeded
  , erData       :: !(Maybe Text)
    -- ^ Extracted data as JSON (for now)
  , erError      :: !(Maybe ScrapeError)
    -- ^ Error if extraction failed
  , erDurationMs :: !Word32
    -- ^ How long extraction took
  }
  deriving stock (Eq, Show)

instance ToJSON ExtractionResult where
  toJSON er = object
    [ "target"     .= erTarget er
    , "success"    .= erSuccess er
    , "data"       .= erData er
    , "error"      .= erError er
    , "durationMs" .= erDurationMs er
    ]

instance FromJSON ExtractionResult where
  parseJSON = withObject "ExtractionResult" $ \v -> ExtractionResult
    <$> v .: "target"
    <*> v .: "success"
    <*> v .:? "data"
    <*> v .:? "error"
    <*> v .: "durationMs"

-- | Complete scraping result
data ScrapeResult = ScrapeResult
  { srJobId        :: !JobId
    -- ^ Which job this is for
  , srStatus       :: !JobStatus
    -- ^ Final status
  , srUrl          :: !Text
    -- ^ URL that was scraped
  , srFinalUrl     :: !Text
    -- ^ Final URL after redirects
  , srHttpStatus   :: !Word16
    -- ^ HTTP status code
  , srExtractions  :: !(Vector ExtractionResult)
    -- ^ Results per extraction target
  , srErrors       :: !(Vector ScrapeError)
    -- ^ Any errors encountered
  , srTimestamps   :: !JobTimestamps
    -- ^ Lifecycle timestamps
  , srDurationMs   :: !Word32
    -- ^ Total job duration
  , srWorker       :: !Text
    -- ^ Which worker processed this
  , srIsolation    :: !IsolationLevel
    -- ^ What isolation was used
  }
  deriving stock (Eq, Show)

instance ToJSON ScrapeResult where
  toJSON sr = object
    [ "jobId"       .= srJobId sr
    , "status"      .= srStatus sr
    , "url"         .= srUrl sr
    , "finalUrl"    .= srFinalUrl sr
    , "httpStatus"  .= srHttpStatus sr
    , "extractions" .= srExtractions sr
    , "errors"      .= srErrors sr
    , "timestamps"  .= srTimestamps sr
    , "durationMs"  .= srDurationMs sr
    , "worker"      .= srWorker sr
    , "isolation"   .= srIsolation sr
    ]

instance FromJSON ScrapeResult where
  parseJSON = withObject "ScrapeResult" $ \v -> ScrapeResult
    <$> v .: "jobId"
    <*> v .: "status"
    <*> v .: "url"
    <*> v .: "finalUrl"
    <*> v .: "httpStatus"
    <*> v .: "extractions"
    <*> v .: "errors"
    <*> v .: "timestamps"
    <*> v .: "durationMs"
    <*> v .: "worker"
    <*> v .: "isolation"
