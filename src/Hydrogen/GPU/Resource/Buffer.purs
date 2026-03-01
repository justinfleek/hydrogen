-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // gpu // resource // buffer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Buffer Pool — GPU Buffer Pooling with Size Buckets
-- |
-- | ## Purpose
-- |
-- | GPU buffer allocation is expensive. This module provides:
-- |
-- | - **Size-bucketed pooling**: Reuse buffers by size class
-- | - **Free list management**: O(1) acquire/release
-- | - **Memory statistics**: Track allocation patterns
-- |
-- | ## Bucket Strategy
-- |
-- | Buffers are allocated in power-of-4 sizes (1KB, 4KB, 16KB, ...):
-- | - Reduces fragmentation
-- | - Enables fast bucket lookup
-- | - Supports custom sizes for large allocations
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Buffer pools reduce per-frame allocation to near-zero:
-- | - Agents share buffer pools within render contexts
-- | - Reuse rate approaches 100% for steady-state workloads
-- | - Custom buckets handle outlier sizes without fragmentation

module Hydrogen.GPU.Resource.Buffer
  ( -- * Buffer Size Buckets
    BufferBucket
      ( Bucket1KB
      , Bucket4KB
      , Bucket16KB
      , Bucket64KB
      , Bucket256KB
      , Bucket1MB
      , Bucket4MB
      , Bucket16MB
      , BucketCustom
      )
  , bucketSize
  , bucketForSize
  
  -- * Buffer Specification
  , BufferSpec
  , mkBufferSpec
  
  -- * Buffer Handle
  , BufferHandle
      ( BufferHandle )
  
  -- * Buffer Pool
  , BufferPool
      ( BufferPool )
  , mkBufferPool
  , defaultBufferPool
  , bufferAcquire
  , bufferRelease
  
  -- * Pool Statistics
  , PoolStats
  , bufferPoolStats
  
  -- * Memory Estimation
  , estimateBufferMemory
  , bufferPoolMemoryUsed
  
  -- * Pool Queries
  , mapFreeBuffers
  , allFreeBuffers
  , bufferCountByBucket
  , largeBuffers
  , bufferPoolUnderThreshold
  , findSmallestFittingBuffer
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
  , map
  , otherwise
  , ($)
  , (+)
  , (-)
  , (/)
  , (*)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (<>)
  , (>>=)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.GPU.WebGPU.Types (GPUBufferUsage)
import Hydrogen.GPU.Resource.Handle 
  ( ResourceHandle
  , ResourceId
  , handleId
  , mkResourceHandle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // buffer size buckets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer size buckets for pooling.
-- |
-- | ## Bucket Strategy
-- |
-- | Buffers are allocated in power-of-4 sizes:
-- | - Reduces fragmentation
-- | - Enables fast bucket lookup
-- | - Supports custom sizes for large allocations
data BufferBucket
  = Bucket1KB       -- 1,024 bytes
  | Bucket4KB       -- 4,096 bytes
  | Bucket16KB      -- 16,384 bytes
  | Bucket64KB      -- 65,536 bytes
  | Bucket256KB     -- 262,144 bytes
  | Bucket1MB       -- 1,048,576 bytes
  | Bucket4MB       -- 4,194,304 bytes
  | Bucket16MB      -- 16,777,216 bytes
  | BucketCustom Int  -- Custom size

derive instance eqBufferBucket :: Eq BufferBucket

instance ordBufferBucket :: Ord BufferBucket where
  compare a b = compare (bucketSize a) (bucketSize b)

instance showBufferBucket :: Show BufferBucket where
  show Bucket1KB = "Bucket1KB"
  show Bucket4KB = "Bucket4KB"
  show Bucket16KB = "Bucket16KB"
  show Bucket64KB = "Bucket64KB"
  show Bucket256KB = "Bucket256KB"
  show Bucket1MB = "Bucket1MB"
  show Bucket4MB = "Bucket4MB"
  show Bucket16MB = "Bucket16MB"
  show (BucketCustom n) = "(BucketCustom " <> show n <> ")"

-- | Get bucket size in bytes.
bucketSize :: BufferBucket -> Int
bucketSize Bucket1KB = 1024
bucketSize Bucket4KB = 4096
bucketSize Bucket16KB = 16384
bucketSize Bucket64KB = 65536
bucketSize Bucket256KB = 262144
bucketSize Bucket1MB = 1048576
bucketSize Bucket4MB = 4194304
bucketSize Bucket16MB = 16777216
bucketSize (BucketCustom n) = n

-- | Find smallest bucket that fits requested size.
bucketForSize :: Int -> BufferBucket
bucketForSize size
  | size <= 1024 = Bucket1KB
  | size <= 4096 = Bucket4KB
  | size <= 16384 = Bucket16KB
  | size <= 65536 = Bucket64KB
  | size <= 262144 = Bucket256KB
  | size <= 1048576 = Bucket1MB
  | size <= 4194304 = Bucket4MB
  | size <= 16777216 = Bucket16MB
  | otherwise = BucketCustom size

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // buffer specification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer specification for allocation.
type BufferSpec =
  { size :: Int
  , usage :: Array GPUBufferUsage
  , label :: String
  }

-- | Create a buffer specification.
mkBufferSpec :: Int -> Array GPUBufferUsage -> String -> BufferSpec
mkBufferSpec size usage label = { size, usage, label }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // buffer handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a pooled buffer.
newtype BufferHandle = BufferHandle
  { handle :: ResourceHandle
  , bucket :: BufferBucket
  , actualSize :: Int
  }

derive instance eqBufferHandle :: Eq BufferHandle

instance showBufferHandle :: Show BufferHandle where
  show (BufferHandle h) = 
    "(BufferHandle " <> show h.bucket <> " size:" <> show h.actualSize <> ")"

-- | Extract resource handle from buffer handle.
unwrapBufferHandle :: BufferHandle -> ResourceHandle
unwrapBufferHandle (BufferHandle h) = h.handle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // buffer pool
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer pool for efficient reuse.
-- |
-- | ## Pool Structure
-- |
-- | - Separate free list per bucket
-- | - Acquired buffers tracked for release
-- | - Statistics for monitoring
newtype BufferPool = BufferPool
  { freeLists :: Map.Map BufferBucket (Array BufferHandle)
  , acquired :: Set.Set ResourceId
  , totalAllocated :: Int
  , totalAcquired :: Int
  , totalReleased :: Int
  }

derive instance eqBufferPool :: Eq BufferPool

instance showBufferPool :: Show BufferPool where
  show (BufferPool p) = 
    "(BufferPool allocated:" <> show p.totalAllocated <> 
    " acquired:" <> show (Set.size p.acquired) <> ")"

-- | Create a new buffer pool.
mkBufferPool :: BufferPool
mkBufferPool = BufferPool
  { freeLists: Map.empty
  , acquired: Set.empty
  , totalAllocated: 0
  , totalAcquired: 0
  , totalReleased: 0
  }

-- | Default buffer pool.
defaultBufferPool :: BufferPool
defaultBufferPool = mkBufferPool

-- | Pool statistics.
type PoolStats =
  { freeCount :: Int
  , acquiredCount :: Int
  , totalAllocated :: Int
  , reuseRate :: Number
  }

-- | Acquire a buffer from the pool.
-- |
-- | Returns a buffer handle and updated pool.
-- | If no suitable buffer is free, creates a new one.
bufferAcquire :: BufferSpec -> BufferPool -> { handle :: BufferHandle, pool :: BufferPool }
bufferAcquire spec (BufferPool p) =
  let bucket = bucketForSize spec.size
      freeList = Map.lookup bucket p.freeLists
  in case freeList >>= Array.head of
       Just existingHandle ->
         -- Reuse existing buffer
         let newFreeList = case freeList of
               Nothing -> []
               Just arr -> Array.drop 1 arr
             newFreeLists = Map.insert bucket newFreeList p.freeLists
             newAcquired = Set.insert (handleId (unwrapBufferHandle existingHandle)) p.acquired
         in
           { handle: existingHandle
           , pool: BufferPool (p 
               { freeLists = newFreeLists
               , acquired = newAcquired
               , totalAcquired = p.totalAcquired + 1
               })
           }
       Nothing ->
         -- Allocate new buffer
         let contentKey = spec.label <> "-" <> show spec.size <> "-" <> show p.totalAllocated
             newHandle = BufferHandle
               { handle: mkResourceHandle contentKey
               , bucket
               , actualSize: bucketSize bucket
               }
             newAcquired = Set.insert (handleId (unwrapBufferHandle newHandle)) p.acquired
         in
           { handle: newHandle
           , pool: BufferPool (p 
               { acquired = newAcquired
               , totalAllocated = p.totalAllocated + 1
               , totalAcquired = p.totalAcquired + 1
               })
           }

-- | Release a buffer back to the pool.
bufferRelease :: BufferHandle -> BufferPool -> BufferPool
bufferRelease bufHandle@(BufferHandle h) (BufferPool p) =
  let resourceId = handleId h.handle
      newAcquired = Set.delete resourceId p.acquired
      currentList = case Map.lookup h.bucket p.freeLists of
                      Nothing -> []
                      Just arr -> arr
      newFreeList = Array.cons bufHandle currentList
      newFreeLists = Map.insert h.bucket newFreeList p.freeLists
  in
    BufferPool (p 
      { freeLists = newFreeLists
      , acquired = newAcquired
      , totalReleased = p.totalReleased + 1
      })

-- | Get pool statistics.
bufferPoolStats :: BufferPool -> PoolStats
bufferPoolStats (BufferPool p) =
  let freeCount = foldl (\acc arr -> acc + Array.length arr) 0 
                        (Map.values p.freeLists)
      acquiredCount = Set.size p.acquired
      totalReused = p.totalAcquired - p.totalAllocated
      reuseRate = if p.totalAcquired > 0
                  then Int.toNumber totalReused / Int.toNumber p.totalAcquired
                  else 0.0
  in
    { freeCount
    , acquiredCount
    , totalAllocated: p.totalAllocated
    , reuseRate
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // memory estimation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimate memory usage of a buffer specification in bytes.
-- |
-- | Uses bucket size (actual allocation) not requested size.
estimateBufferMemory :: BufferSpec -> Int
estimateBufferMemory spec = bucketSize $ bucketForSize spec.size

-- | Total estimated memory for all acquired buffers.
bufferPoolMemoryUsed :: BufferPool -> Int
bufferPoolMemoryUsed (BufferPool p) =
  -- Each acquired buffer uses its bucket size
  -- We don't track individual sizes, so estimate from total allocated
  p.totalAllocated * averageBucketSize
  where
    averageBucketSize = bucketSize Bucket64KB  -- Conservative estimate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pool queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over all free buffer handles.
-- |
-- | Useful for batch operations like resetting state or logging.
mapFreeBuffers :: (BufferHandle -> BufferHandle) -> BufferPool -> BufferPool
mapFreeBuffers f (BufferPool p) =
  let newFreeLists = map (map f) p.freeLists
  in BufferPool (p { freeLists = newFreeLists })

-- | Get all free buffer handles across all buckets.
allFreeBuffers :: BufferPool -> Array BufferHandle
allFreeBuffers (BufferPool p) =
  foldl (\acc arr -> acc <> arr) [] (Map.values p.freeLists)

-- | Count buffers by bucket.
bufferCountByBucket :: BufferPool -> Array { bucket :: BufferBucket, count :: Int }
bufferCountByBucket (BufferPool p) =
  map (\(Tuple bucket handles) -> { bucket, count: Array.length handles }) $
    Map.toUnfoldable p.freeLists

-- | Get buffers larger than a threshold.
largeBuffers :: Int -> BufferPool -> Array BufferHandle
largeBuffers thresholdBytes pool =
  Array.filter (\(BufferHandle h) -> h.actualSize > thresholdBytes) $
    allFreeBuffers pool

-- | Check if buffer pool is below a memory threshold.
-- |
-- | Returns true if estimated memory usage is below threshold bytes.
bufferPoolUnderThreshold :: Int -> BufferPool -> Boolean
bufferPoolUnderThreshold thresholdBytes pool =
  bufferPoolMemoryUsed pool < thresholdBytes

-- | Find smallest buffer that fits the requested size.
-- |
-- | Returns the first free buffer with actual size >= requested,
-- | sorted by size ascending to minimize waste.
findSmallestFittingBuffer :: Int -> BufferPool -> Maybe BufferHandle
findSmallestFittingBuffer requestedSize pool =
  let allFree = allFreeBuffers pool
      fitting = Array.filter (\(BufferHandle h) -> h.actualSize >= requestedSize) allFree
      sorted = Array.sortBy (\(BufferHandle a) (BufferHandle b) -> 
                 compare a.actualSize b.actualSize) fitting
  in Array.head sorted
