-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gpu // limits // compute
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Compute Limits — Bounded types for WebGPU compute shader constraints.
-- |
-- | ## Compute Model
-- |
-- | WebGPU compute shaders execute in a 3D grid of workgroups:
-- | - Each workgroup contains invocations (threads)
-- | - Workgroups share local memory
-- | - Workgroups are dispatched in a 3D grid
-- |
-- | ## Limits
-- |
-- | - maxComputeWorkgroupSizeX/Y: 256 (guaranteed minimum)
-- | - maxComputeWorkgroupSizeZ: 64 (guaranteed minimum)
-- | - maxComputeWorkgroupsPerDimension: 65535 (guaranteed minimum)
-- | - maxComputeWorkgroupStorageSize: 16384 (16 KB)
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits
-- |
-- | ## Co-Effect Semantics
-- |
-- | Workgroup co-effects combine with MAX (parallel capacity), not SUM.
-- | If two compute passes each need 128 workgroups, they can share
-- | GPU resources rather than requiring 256 workgroups simultaneously.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.GPU.Limits.Compute
  ( -- * Workgroup Size
    WorkgroupSize
  , workgroupSize
  , clampWorkgroupSize
  , unwrapWorkgroupSize
  , workgroupSizeBounds
  
  -- * Workgroup Count
  , WorkgroupCount
  , workgroupCount
  , clampWorkgroupCount
  , unwrapWorkgroupCount
  , workgroupCountBounds
  
  -- * Workgroup Storage Size
  , WorkgroupStorageSize
  , workgroupStorageSize
  , clampWorkgroupStorageSize
  , unwrapWorkgroupStorageSize
  , workgroupStorageSizeBounds
  
  -- * Color Attachment Count
  , ColorAttachmentCount
  , colorAttachmentCount
  , clampColorAttachmentCount
  , unwrapColorAttachmentCount
  , colorAttachmentCountBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , IntBounds
  , intBounds
  , clampInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // workgroup size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size (per dimension).
-- |
-- | Bounds: 1 to 256 (WebGPU guaranteed minimum for X/Y, 64 for Z)
-- |
-- | We use 256 as the max for all dimensions for simplicity. The actual
-- | Z dimension limit is 64 on some hardware.
-- |
-- | Common workgroup sizes:
-- | - (64, 1, 1): Linear processing
-- | - (8, 8, 1): 2D image processing
-- | - (4, 4, 4): 3D volume processing
-- |
-- | Total invocations per workgroup must not exceed 256.
newtype WorkgroupSize = WorkgroupSize Int

derive instance eqWorkgroupSize :: Eq WorkgroupSize
derive instance ordWorkgroupSize :: Ord WorkgroupSize

instance showWorkgroupSize :: Show WorkgroupSize where
  show (WorkgroupSize n) = "WorkgroupSize(" <> show n <> ")"

-- | Bounds specification for workgroup size.
workgroupSizeBounds :: IntBounds
workgroupSizeBounds = intBounds 1 256 Clamps "workgroupSize" "Workgroup size (1-256)"

-- | Smart constructor with validation.
workgroupSize :: Int -> Maybe WorkgroupSize
workgroupSize n
  | n >= 1 && n <= 256 = Just (WorkgroupSize n)
  | otherwise = Nothing

-- | Clamping constructor.
clampWorkgroupSize :: Int -> WorkgroupSize
clampWorkgroupSize n = WorkgroupSize (clampInt 1 256 n)

-- | Extract the underlying Int value.
unwrapWorkgroupSize :: WorkgroupSize -> Int
unwrapWorkgroupSize (WorkgroupSize n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // workgroup count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup count (per dimension).
-- |
-- | Bounds: 0 to 65535 (WebGPU guaranteed minimum)
-- |
-- | The total number of workgroups in a dispatch is X * Y * Z.
-- | With max 65535 per dimension, this allows up to ~281 trillion
-- | workgroups in a single dispatch (though practical limits apply).
-- |
-- | For a 4K image (3840x2160) with 8x8 workgroups:
-- | - X = 3840 / 8 = 480 workgroups
-- | - Y = 2160 / 8 = 270 workgroups
-- | - Total = 129,600 workgroups
newtype WorkgroupCount = WorkgroupCount Int

derive instance eqWorkgroupCount :: Eq WorkgroupCount
derive instance ordWorkgroupCount :: Ord WorkgroupCount

instance showWorkgroupCount :: Show WorkgroupCount where
  show (WorkgroupCount n) = "WorkgroupCount(" <> show n <> ")"

-- | Bounds specification for workgroup count.
workgroupCountBounds :: IntBounds
workgroupCountBounds = intBounds 0 65535 Clamps "workgroupCount" "Workgroup count (0-65535)"

-- | Smart constructor with validation.
workgroupCount :: Int -> Maybe WorkgroupCount
workgroupCount n
  | n >= 0 && n <= 65535 = Just (WorkgroupCount n)
  | otherwise = Nothing

-- | Clamping constructor.
clampWorkgroupCount :: Int -> WorkgroupCount
clampWorkgroupCount n = WorkgroupCount (clampInt 0 65535 n)

-- | Extract the underlying Int value.
unwrapWorkgroupCount :: WorkgroupCount -> Int
unwrapWorkgroupCount (WorkgroupCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // workgroup storage size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup storage size.
-- |
-- | Bounds: 0 to 16384 (16 KB, WebGPU guaranteed minimum)
-- |
-- | Workgroup-local memory is shared between all invocations in a workgroup.
-- | It's faster than global memory but limited in size.
-- |
-- | Common uses:
-- | - Tile-based processing (load tile into shared memory)
-- | - Reduction operations (parallel sum, min, max)
-- | - Prefix scans
-- | - Histogram computation
newtype WorkgroupStorageSize = WorkgroupStorageSize Int

derive instance eqWorkgroupStorageSize :: Eq WorkgroupStorageSize
derive instance ordWorkgroupStorageSize :: Ord WorkgroupStorageSize

instance showWorkgroupStorageSize :: Show WorkgroupStorageSize where
  show (WorkgroupStorageSize n) = "WorkgroupStorage(" <> show n <> ")"

-- | Bounds specification for workgroup storage size.
workgroupStorageSizeBounds :: IntBounds
workgroupStorageSizeBounds = intBounds 0 16384 Clamps "workgroupStorageSize" "Workgroup storage size (0-16KB)"

-- | Smart constructor with validation.
workgroupStorageSize :: Int -> Maybe WorkgroupStorageSize
workgroupStorageSize n
  | n >= 0 && n <= 16384 = Just (WorkgroupStorageSize n)
  | otherwise = Nothing

-- | Clamping constructor.
clampWorkgroupStorageSize :: Int -> WorkgroupStorageSize
clampWorkgroupStorageSize n = WorkgroupStorageSize (clampInt 0 16384 n)

-- | Extract the underlying Int value.
unwrapWorkgroupStorageSize :: WorkgroupStorageSize -> Int
unwrapWorkgroupStorageSize (WorkgroupStorageSize n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // color attachment count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color attachment count.
-- |
-- | Bounds: 0 to 8 (WebGPU guaranteed minimum)
-- |
-- | Multiple render targets (MRT) allow a single render pass to output
-- | to multiple textures simultaneously.
-- |
-- | Common uses:
-- | - Deferred rendering (albedo, normal, depth, etc.)
-- | - G-buffer generation
-- | - Post-processing effects
newtype ColorAttachmentCount = ColorAttachmentCount Int

derive instance eqColorAttachmentCount :: Eq ColorAttachmentCount
derive instance ordColorAttachmentCount :: Ord ColorAttachmentCount

instance showColorAttachmentCount :: Show ColorAttachmentCount where
  show (ColorAttachmentCount n) = "ColorAttachments(" <> show n <> ")"

-- | Bounds specification for color attachment count.
colorAttachmentCountBounds :: IntBounds
colorAttachmentCountBounds = intBounds 0 8 Clamps "colorAttachmentCount" "Color attachments (0-8)"

-- | Smart constructor with validation.
colorAttachmentCount :: Int -> Maybe ColorAttachmentCount
colorAttachmentCount n
  | n >= 0 && n <= 8 = Just (ColorAttachmentCount n)
  | otherwise = Nothing

-- | Clamping constructor.
clampColorAttachmentCount :: Int -> ColorAttachmentCount
clampColorAttachmentCount n = ColorAttachmentCount (clampInt 0 8 n)

-- | Extract the underlying Int value.
unwrapColorAttachmentCount :: ColorAttachmentCount -> Int
unwrapColorAttachmentCount (ColorAttachmentCount n) = n
