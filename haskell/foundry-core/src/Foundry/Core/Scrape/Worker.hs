{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // scrape/worker
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Scrape.Worker
Description : Worker types for scraping VM/container lifecycle
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines types for managing scraping workers - the isolated browser environments
that execute scraping jobs. Workers can be containers (runc), gVisor sandboxes,
or Firecracker microVMs.

== Design Principles

1. Workers are ephemeral - created per job, destroyed after
2. All state is external - workers don't persist anything
3. Communication is typed - ZMQ messages are structured data
4. Lifecycle is explicit - every state transition is tracked

== Worker Types

Container   - Standard OCI container via containerd/runc
GVisor      - gVisor sandbox via runsc RuntimeClass  
Firecracker - microVM via Flintlock/firecracker-containerd

== Dependencies

Requires: Foundry.Core.Scrape.Job
Required by: Foundry.Core.Scrape.Orchestrator

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Scrape.Worker
  ( -- * Worker Identification
    WorkerId (..)
  , mkWorkerId
  
    -- * Worker Configuration
  , WorkerConfig (..)
  , ContainerConfig (..)
  , GVisorConfig (..)
  , FirecrackerConfig (..)
  
    -- * Worker State
  , WorkerState (..)
  , WorkerHealth (..)
  , WorkerMetrics (..)
  
    -- * Worker Lifecycle
  , WorkerEvent (..)
  , WorkerHandle (..)
  
    -- * Worker Pool
  , PoolConfig (..)
  , PoolState (..)
  , PoolMetrics (..)
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), (.:?), object, withObject, withText)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word16, Word32, Word64)
import Foundry.Core.Scrape.Job (IsolationLevel (..), JobId, ResourceLimits)

--------------------------------------------------------------------------------
-- Worker Identification
--------------------------------------------------------------------------------

-- | Unique worker identifier
--
-- Format: {isolation}-{timestamp}-{random}
-- e.g., "gvisor-1709234567-a1b2c3"
newtype WorkerId = WorkerId { unWorkerId :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create worker ID
mkWorkerId :: IsolationLevel -> Word64 -> Text -> WorkerId
mkWorkerId iso ts rand = WorkerId $ mconcat
  [ case iso of
      ContainerIsolation -> "container"
      GVisorIsolation -> "gvisor"
      FirecrackerIsolation -> "firecracker"
  , "-"
  , T.pack (show ts)
  , "-"
  , rand
  ]

instance ToJSON WorkerId where
  toJSON (WorkerId t) = toJSON t

instance FromJSON WorkerId where
  parseJSON = withText "WorkerId" (pure . WorkerId)

--------------------------------------------------------------------------------
-- Worker Configuration
--------------------------------------------------------------------------------

-- | Configuration for container-based workers (runc)
data ContainerConfig = ContainerConfig
  { ccImage          :: !Text
    -- ^ Container image (e.g., "ghcr.io/foundry/scraper:v1")
  , ccRuntime        :: !Text
    -- ^ Runtime to use (e.g., "runc")
  , ccNetworkMode    :: !Text
    -- ^ Network mode (e.g., "bridge", "host")
  , ccCapDrop        :: ![Text]
    -- ^ Capabilities to drop
  , ccSecurityOpt    :: ![Text]
    -- ^ Security options
  , ccReadOnlyRoot   :: !Bool
    -- ^ Read-only root filesystem
  }
  deriving stock (Eq, Show)

instance ToJSON ContainerConfig where
  toJSON cc = object
    [ "image"        .= ccImage cc
    , "runtime"      .= ccRuntime cc
    , "networkMode"  .= ccNetworkMode cc
    , "capDrop"      .= ccCapDrop cc
    , "securityOpt"  .= ccSecurityOpt cc
    , "readOnlyRoot" .= ccReadOnlyRoot cc
    ]

instance FromJSON ContainerConfig where
  parseJSON = withObject "ContainerConfig" $ \v -> ContainerConfig
    <$> v .: "image"
    <*> v .: "runtime"
    <*> v .: "networkMode"
    <*> v .: "capDrop"
    <*> v .: "securityOpt"
    <*> v .: "readOnlyRoot"

-- | Configuration for gVisor-based workers
data GVisorConfig = GVisorConfig
  { gvImage          :: !Text
    -- ^ Container image
  , gvPlatform       :: !Text
    -- ^ gVisor platform (e.g., "systrap", "kvm")
  , gvNetwork        :: !Text
    -- ^ Network mode (e.g., "sandbox", "host")
  , gvDirectFS       :: !Bool
    -- ^ Enable directfs for trusted mounts
  , gvDebugLog       :: !Bool
    -- ^ Enable debug logging
  }
  deriving stock (Eq, Show)

instance ToJSON GVisorConfig where
  toJSON gv = object
    [ "image"    .= gvImage gv
    , "platform" .= gvPlatform gv
    , "network"  .= gvNetwork gv
    , "directFS" .= gvDirectFS gv
    , "debugLog" .= gvDebugLog gv
    ]

instance FromJSON GVisorConfig where
  parseJSON = withObject "GVisorConfig" $ \v -> GVisorConfig
    <$> v .: "image"
    <*> v .: "platform"
    <*> v .: "network"
    <*> v .: "directFS"
    <*> v .: "debugLog"

-- | Configuration for Firecracker microVM workers
data FirecrackerConfig = FirecrackerConfig
  { fcKernelPath     :: !Text
    -- ^ Path to kernel image
  , fcRootfsPath     :: !Text
    -- ^ Path to rootfs image
  , fcVCPUs          :: !Word16
    -- ^ Number of vCPUs
  , fcMemoryMB       :: !Word32
    -- ^ Memory in MB
  , fcNetworkTap     :: !Text
    -- ^ TAP device for networking
  , fcVsockCID       :: !Word32
    -- ^ vsock CID for host communication
  , fcJailerPath     :: !(Maybe Text)
    -- ^ Path to jailer binary (for extra isolation)
  }
  deriving stock (Eq, Show)

instance ToJSON FirecrackerConfig where
  toJSON fc = object
    [ "kernelPath"  .= fcKernelPath fc
    , "rootfsPath"  .= fcRootfsPath fc
    , "vcpus"       .= fcVCPUs fc
    , "memoryMB"    .= fcMemoryMB fc
    , "networkTap"  .= fcNetworkTap fc
    , "vsockCID"    .= fcVsockCID fc
    , "jailerPath"  .= fcJailerPath fc
    ]

instance FromJSON FirecrackerConfig where
  parseJSON = withObject "FirecrackerConfig" $ \v -> FirecrackerConfig
    <$> v .: "kernelPath"
    <*> v .: "rootfsPath"
    <*> v .: "vcpus"
    <*> v .: "memoryMB"
    <*> v .: "networkTap"
    <*> v .: "vsockCID"
    <*> v .:? "jailerPath"

-- | Complete worker configuration (sum type over isolation levels)
data WorkerConfig
  = ContainerWorker !ContainerConfig !ResourceLimits
  | GVisorWorker !GVisorConfig !ResourceLimits
  | FirecrackerWorker !FirecrackerConfig !ResourceLimits
  deriving stock (Eq, Show)

instance ToJSON WorkerConfig where
  toJSON (ContainerWorker cc rl) = object
    [ "type"      .= ("container" :: Text)
    , "config"    .= cc
    , "resources" .= rl
    ]
  toJSON (GVisorWorker gv rl) = object
    [ "type"      .= ("gvisor" :: Text)
    , "config"    .= gv
    , "resources" .= rl
    ]
  toJSON (FirecrackerWorker fc rl) = object
    [ "type"      .= ("firecracker" :: Text)
    , "config"    .= fc
    , "resources" .= rl
    ]

instance FromJSON WorkerConfig where
  parseJSON = withObject "WorkerConfig" $ \v -> do
    typ <- v .: "type"
    rl <- v .: "resources"
    case (typ :: Text) of
      "container"   -> ContainerWorker <$> v .: "config" <*> pure rl
      "gvisor"      -> GVisorWorker <$> v .: "config" <*> pure rl
      "firecracker" -> FirecrackerWorker <$> v .: "config" <*> pure rl
      other         -> fail $ "Unknown WorkerConfig type: " <> T.unpack other

--------------------------------------------------------------------------------
-- Worker State
--------------------------------------------------------------------------------

-- | Current state of a worker
data WorkerState
  = WorkerCreating
    -- ^ Being created (container starting, VM booting)
  | WorkerReady
    -- ^ Ready to accept jobs
  | WorkerBusy !JobId
    -- ^ Processing a job
  | WorkerDraining
    -- ^ Finishing current job, will not accept more
  | WorkerStopping
    -- ^ Shutting down
  | WorkerStopped
    -- ^ Fully stopped
  | WorkerFailed !Text
    -- ^ Failed with error message
  deriving stock (Eq, Show)

instance ToJSON WorkerState where
  toJSON WorkerCreating    = object ["state" .= ("creating" :: Text)]
  toJSON WorkerReady       = object ["state" .= ("ready" :: Text)]
  toJSON (WorkerBusy jid)  = object ["state" .= ("busy" :: Text), "jobId" .= jid]
  toJSON WorkerDraining    = object ["state" .= ("draining" :: Text)]
  toJSON WorkerStopping    = object ["state" .= ("stopping" :: Text)]
  toJSON WorkerStopped     = object ["state" .= ("stopped" :: Text)]
  toJSON (WorkerFailed e)  = object ["state" .= ("failed" :: Text), "error" .= e]

instance FromJSON WorkerState where
  parseJSON = withObject "WorkerState" $ \v -> do
    st <- v .: "state"
    case (st :: Text) of
      "creating" -> pure WorkerCreating
      "ready"    -> pure WorkerReady
      "busy"     -> WorkerBusy <$> v .: "jobId"
      "draining" -> pure WorkerDraining
      "stopping" -> pure WorkerStopping
      "stopped"  -> pure WorkerStopped
      "failed"   -> WorkerFailed <$> v .: "error"
      other      -> fail $ "Unknown WorkerState: " <> T.unpack other

-- | Health status of a worker
data WorkerHealth
  = Healthy
    -- ^ All systems nominal
  | Degraded !Text
    -- ^ Working but with issues
  | Unhealthy !Text
    -- ^ Not working properly
  | Unknown
    -- ^ Health unknown (not yet checked)
  deriving stock (Eq, Show)

instance ToJSON WorkerHealth where
  toJSON Healthy        = object ["health" .= ("healthy" :: Text)]
  toJSON (Degraded msg) = object ["health" .= ("degraded" :: Text), "message" .= msg]
  toJSON (Unhealthy msg) = object ["health" .= ("unhealthy" :: Text), "message" .= msg]
  toJSON Unknown        = object ["health" .= ("unknown" :: Text)]

instance FromJSON WorkerHealth where
  parseJSON = withObject "WorkerHealth" $ \v -> do
    h <- v .: "health"
    case (h :: Text) of
      "healthy"   -> pure Healthy
      "degraded"  -> Degraded <$> v .: "message"
      "unhealthy" -> Unhealthy <$> v .: "message"
      "unknown"   -> pure Unknown
      other       -> fail $ "Unknown WorkerHealth: " <> T.unpack other

-- | Runtime metrics for a worker
data WorkerMetrics = WorkerMetrics
  { wmMemoryUsedMB   :: !Word32
    -- ^ Current memory usage in MB
  , wmCPUPercent     :: !Double
    -- ^ CPU usage percentage (0-100)
  , wmNetworkRxBytes :: !Word64
    -- ^ Network bytes received
  , wmNetworkTxBytes :: !Word64
    -- ^ Network bytes transmitted
  , wmJobsCompleted  :: !Word32
    -- ^ Jobs completed by this worker
  , wmJobsFailed     :: !Word32
    -- ^ Jobs failed by this worker
  , wmUptimeSeconds  :: !Word64
    -- ^ How long this worker has been running
  , wmLastHealthCheck :: !Word64
    -- ^ Timestamp of last health check
  }
  deriving stock (Eq, Show)

instance ToJSON WorkerMetrics where
  toJSON wm = object
    [ "memoryUsedMB"   .= wmMemoryUsedMB wm
    , "cpuPercent"     .= wmCPUPercent wm
    , "networkRxBytes" .= wmNetworkRxBytes wm
    , "networkTxBytes" .= wmNetworkTxBytes wm
    , "jobsCompleted"  .= wmJobsCompleted wm
    , "jobsFailed"     .= wmJobsFailed wm
    , "uptimeSeconds"  .= wmUptimeSeconds wm
    , "lastHealthCheck" .= wmLastHealthCheck wm
    ]

instance FromJSON WorkerMetrics where
  parseJSON = withObject "WorkerMetrics" $ \v -> WorkerMetrics
    <$> v .: "memoryUsedMB"
    <*> v .: "cpuPercent"
    <*> v .: "networkRxBytes"
    <*> v .: "networkTxBytes"
    <*> v .: "jobsCompleted"
    <*> v .: "jobsFailed"
    <*> v .: "uptimeSeconds"
    <*> v .: "lastHealthCheck"

--------------------------------------------------------------------------------
-- Worker Lifecycle
--------------------------------------------------------------------------------

-- | Events in worker lifecycle
data WorkerEvent
  = WorkerRequested !Word64
    -- ^ Worker creation requested
  | WorkerCreated !Word64
    -- ^ Worker created (container/VM started)
  | WorkerBootComplete !Word64
    -- ^ Worker ready for jobs
  | WorkerJobAssigned !JobId !Word64
    -- ^ Job assigned to worker
  | WorkerJobCompleted !JobId !Word64
    -- ^ Job completed
  | WorkerJobFailed !JobId !Text !Word64
    -- ^ Job failed (job ID, error, timestamp)
  | WorkerHealthChecked !WorkerHealth !Word64
    -- ^ Health check performed
  | WorkerDrainStarted !Word64
    -- ^ Worker starting to drain
  | WorkerShutdownStarted !Word64
    -- ^ Worker shutdown initiated
  | WorkerDestroyed !Word64
    -- ^ Worker fully destroyed
  deriving stock (Eq, Show)

instance ToJSON WorkerEvent where
  toJSON (WorkerRequested ts)       = object ["event" .= ("requested" :: Text), "timestamp" .= ts]
  toJSON (WorkerCreated ts)         = object ["event" .= ("created" :: Text), "timestamp" .= ts]
  toJSON (WorkerBootComplete ts)    = object ["event" .= ("boot_complete" :: Text), "timestamp" .= ts]
  toJSON (WorkerJobAssigned j ts)   = object ["event" .= ("job_assigned" :: Text), "jobId" .= j, "timestamp" .= ts]
  toJSON (WorkerJobCompleted j ts)  = object ["event" .= ("job_completed" :: Text), "jobId" .= j, "timestamp" .= ts]
  toJSON (WorkerJobFailed j e ts)   = object ["event" .= ("job_failed" :: Text), "jobId" .= j, "error" .= e, "timestamp" .= ts]
  toJSON (WorkerHealthChecked h ts) = object ["event" .= ("health_checked" :: Text), "health" .= h, "timestamp" .= ts]
  toJSON (WorkerDrainStarted ts)    = object ["event" .= ("drain_started" :: Text), "timestamp" .= ts]
  toJSON (WorkerShutdownStarted ts) = object ["event" .= ("shutdown_started" :: Text), "timestamp" .= ts]
  toJSON (WorkerDestroyed ts)       = object ["event" .= ("destroyed" :: Text), "timestamp" .= ts]

instance FromJSON WorkerEvent where
  parseJSON = withObject "WorkerEvent" $ \v -> do
    evt <- v .: "event"
    ts <- v .: "timestamp"
    case (evt :: Text) of
      "requested"        -> pure $ WorkerRequested ts
      "created"          -> pure $ WorkerCreated ts
      "boot_complete"    -> pure $ WorkerBootComplete ts
      "job_assigned"     -> WorkerJobAssigned <$> v .: "jobId" <*> pure ts
      "job_completed"    -> WorkerJobCompleted <$> v .: "jobId" <*> pure ts
      "job_failed"       -> WorkerJobFailed <$> v .: "jobId" <*> v .: "error" <*> pure ts
      "health_checked"   -> WorkerHealthChecked <$> v .: "health" <*> pure ts
      "drain_started"    -> pure $ WorkerDrainStarted ts
      "shutdown_started" -> pure $ WorkerShutdownStarted ts
      "destroyed"        -> pure $ WorkerDestroyed ts
      other              -> fail $ "Unknown WorkerEvent: " <> T.unpack other

-- | Handle to a running worker
--
-- This is the runtime representation of a worker.
-- Contains all metadata needed to communicate with and manage the worker.
data WorkerHandle = WorkerHandle
  { whId          :: !WorkerId
    -- ^ Worker identifier
  , whConfig      :: !WorkerConfig
    -- ^ How the worker was configured
  , whState       :: !WorkerState
    -- ^ Current state
  , whHealth      :: !WorkerHealth
    -- ^ Current health
  , whMetrics     :: !WorkerMetrics
    -- ^ Runtime metrics
  , whEndpoint    :: !Text
    -- ^ How to reach this worker (e.g., "tcp://10.0.0.5:5555" or "vsock://3:5555")
  , whCreatedAt   :: !Word64
    -- ^ When the worker was created
  }
  deriving stock (Eq, Show)

instance ToJSON WorkerHandle where
  toJSON wh = object
    [ "id"        .= whId wh
    , "config"    .= whConfig wh
    , "state"     .= whState wh
    , "health"    .= whHealth wh
    , "metrics"   .= whMetrics wh
    , "endpoint"  .= whEndpoint wh
    , "createdAt" .= whCreatedAt wh
    ]

instance FromJSON WorkerHandle where
  parseJSON = withObject "WorkerHandle" $ \v -> WorkerHandle
    <$> v .: "id"
    <*> v .: "config"
    <*> v .: "state"
    <*> v .: "health"
    <*> v .: "metrics"
    <*> v .: "endpoint"
    <*> v .: "createdAt"

--------------------------------------------------------------------------------
-- Worker Pool
--------------------------------------------------------------------------------

-- | Configuration for a pool of workers
data PoolConfig = PoolConfig
  { pcMinWorkers     :: !Word16
    -- ^ Minimum workers to keep warm
  , pcMaxWorkers     :: !Word16
    -- ^ Maximum workers allowed
  , pcScaleUpThreshold :: !Double
    -- ^ Queue depth ratio to trigger scale up (0-1)
  , pcScaleDownThreshold :: !Double
    -- ^ Idle ratio to trigger scale down (0-1)
  , pcHealthCheckInterval :: !Word32
    -- ^ Seconds between health checks
  , pcMaxJobsPerWorker :: !Word32
    -- ^ Max jobs before recycling worker (0 = unlimited)
  , pcDefaultIsolation :: !IsolationLevel
    -- ^ Default isolation for new workers
  }
  deriving stock (Eq, Show)

instance ToJSON PoolConfig where
  toJSON pc = object
    [ "minWorkers"          .= pcMinWorkers pc
    , "maxWorkers"          .= pcMaxWorkers pc
    , "scaleUpThreshold"    .= pcScaleUpThreshold pc
    , "scaleDownThreshold"  .= pcScaleDownThreshold pc
    , "healthCheckInterval" .= pcHealthCheckInterval pc
    , "maxJobsPerWorker"    .= pcMaxJobsPerWorker pc
    , "defaultIsolation"    .= pcDefaultIsolation pc
    ]

instance FromJSON PoolConfig where
  parseJSON = withObject "PoolConfig" $ \v -> PoolConfig
    <$> v .: "minWorkers"
    <*> v .: "maxWorkers"
    <*> v .: "scaleUpThreshold"
    <*> v .: "scaleDownThreshold"
    <*> v .: "healthCheckInterval"
    <*> v .: "maxJobsPerWorker"
    <*> v .: "defaultIsolation"

-- | Current state of a worker pool
data PoolState = PoolState
  { psReadyWorkers   :: !Word16
    -- ^ Workers ready for jobs
  , psBusyWorkers    :: !Word16
    -- ^ Workers currently processing
  , psCreatingWorkers :: !Word16
    -- ^ Workers being created
  , psDrainingWorkers :: !Word16
    -- ^ Workers being drained
  , psQueuedJobs     :: !Word32
    -- ^ Jobs waiting in queue
  , psLastScaleEvent :: !(Maybe Word64)
    -- ^ Timestamp of last scale up/down
  }
  deriving stock (Eq, Show)

instance ToJSON PoolState where
  toJSON ps = object
    [ "readyWorkers"    .= psReadyWorkers ps
    , "busyWorkers"     .= psBusyWorkers ps
    , "creatingWorkers" .= psCreatingWorkers ps
    , "drainingWorkers" .= psDrainingWorkers ps
    , "queuedJobs"      .= psQueuedJobs ps
    , "lastScaleEvent"  .= psLastScaleEvent ps
    ]

instance FromJSON PoolState where
  parseJSON = withObject "PoolState" $ \v -> PoolState
    <$> v .: "readyWorkers"
    <*> v .: "busyWorkers"
    <*> v .: "creatingWorkers"
    <*> v .: "drainingWorkers"
    <*> v .: "queuedJobs"
    <*> v .:? "lastScaleEvent"

-- | Aggregate metrics for a worker pool
data PoolMetrics = PoolMetrics
  { pmTotalJobsCompleted :: !Word64
    -- ^ Total jobs completed by pool
  , pmTotalJobsFailed    :: !Word64
    -- ^ Total jobs failed
  , pmTotalWorkersCreated :: !Word64
    -- ^ Total workers ever created
  , pmTotalWorkersDestroyed :: !Word64
    -- ^ Total workers destroyed
  , pmAvgJobDurationMs   :: !Double
    -- ^ Average job duration
  , pmAvgWorkerLifetimeSec :: !Double
    -- ^ Average worker lifetime
  , pmCurrentQPS         :: !Double
    -- ^ Current jobs per second
  }
  deriving stock (Eq, Show)

instance ToJSON PoolMetrics where
  toJSON pm = object
    [ "totalJobsCompleted"    .= pmTotalJobsCompleted pm
    , "totalJobsFailed"       .= pmTotalJobsFailed pm
    , "totalWorkersCreated"   .= pmTotalWorkersCreated pm
    , "totalWorkersDestroyed" .= pmTotalWorkersDestroyed pm
    , "avgJobDurationMs"      .= pmAvgJobDurationMs pm
    , "avgWorkerLifetimeSec"  .= pmAvgWorkerLifetimeSec pm
    , "currentQPS"            .= pmCurrentQPS pm
    ]

instance FromJSON PoolMetrics where
  parseJSON = withObject "PoolMetrics" $ \v -> PoolMetrics
    <$> v .: "totalJobsCompleted"
    <*> v .: "totalJobsFailed"
    <*> v .: "totalWorkersCreated"
    <*> v .: "totalWorkersDestroyed"
    <*> v .: "avgJobDurationMs"
    <*> v .: "avgWorkerLifetimeSec"
    <*> v .: "currentQPS"
