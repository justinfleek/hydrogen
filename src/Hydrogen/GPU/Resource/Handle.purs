-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // gpu // resource // handle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Resource Handles — Identity and Generation Tracking
-- |
-- | ## Purpose
-- |
-- | Provides the foundational types for GPU resource identification:
-- |
-- | - **ResourceId**: Content-addressed unique identifier
-- | - **ResourceHandle**: Identity + generation for cache invalidation
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Resource identity is content-addressed:
-- | - Same resource specification → same ResourceId
-- | - Multiple agents can share resources by identity
-- | - Generation tracking enables efficient cache invalidation

module Hydrogen.GPU.Resource.Handle
  ( -- * Resource Identity
    ResourceId
      ( ResourceId )
  , mkResourceId
  , resourceIdToString
  
  -- * Resource Handles
  , ResourceHandle
      ( ResourceHandle )
  , handleId
  , handleGeneration
  , mkResourceHandle
  , incrementGeneration
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , ($)
  , (+)
  , (<>)
  )

import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // resource identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a GPU resource.
-- |
-- | Uses content-based addressing for determinism:
-- | - Same resource specification → same ResourceId
-- | - Enables cross-agent resource sharing
-- | - Supports cache invalidation via generation
newtype ResourceId = ResourceId String

derive instance eqResourceId :: Eq ResourceId
derive instance ordResourceId :: Ord ResourceId

instance showResourceId :: Show ResourceId where
  show (ResourceId s) = "(ResourceId " <> show s <> ")"

-- | Create a resource ID from a content string.
-- |
-- | In a full implementation, this would compute UUID5.
-- | For now, we use the content directly as a deterministic ID.
mkResourceId :: String -> ResourceId
mkResourceId = ResourceId

-- | Convert resource ID to string.
resourceIdToString :: ResourceId -> String
resourceIdToString (ResourceId s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // resource handles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU resource with generation tracking.
-- |
-- | ## Generation Semantics
-- |
-- | Generation increments when resource content changes:
-- | - gen 0: Initial creation
-- | - gen 1: First modification
-- | - gen N: Nth modification
-- |
-- | Cache entries are invalidated when generation mismatches.
newtype ResourceHandle = ResourceHandle
  { id :: ResourceId
  , generation :: Int
  }

derive instance eqResourceHandle :: Eq ResourceHandle

instance ordResourceHandle :: Ord ResourceHandle where
  compare (ResourceHandle a) (ResourceHandle b) =
    compare (Tuple a.id a.generation) (Tuple b.id b.generation)

instance showResourceHandle :: Show ResourceHandle where
  show (ResourceHandle h) = 
    "(ResourceHandle " <> show h.id <> " gen:" <> show h.generation <> ")"

-- | Get resource ID from handle.
handleId :: ResourceHandle -> ResourceId
handleId (ResourceHandle h) = h.id

-- | Get generation from handle.
handleGeneration :: ResourceHandle -> Int
handleGeneration (ResourceHandle h) = h.generation

-- | Create a new resource handle.
mkResourceHandle :: String -> ResourceHandle
mkResourceHandle contentKey = ResourceHandle
  { id: mkResourceId contentKey
  , generation: 0
  }

-- | Increment handle generation (for modifications).
incrementGeneration :: ResourceHandle -> ResourceHandle
incrementGeneration (ResourceHandle h) = ResourceHandle
  { id: h.id
  , generation: h.generation + 1
  }
