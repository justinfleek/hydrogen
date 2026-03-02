-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // compute // dispatch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Dispatch Primitives — workgroup sizes, grid dimensions, dispatch config.
-- |
-- | ## Design Philosophy
-- |
-- | GPU compute dispatches operate in a 3D grid of workgroups, where each
-- | workgroup contains a 3D grid of threads. This module provides bounded
-- | types for these dimensions, ensuring valid dispatch configurations.
-- |
-- | ## Hardware Constraints
-- |
-- | Different GPUs have different limits:
-- |
-- | | Limit | WebGPU | CUDA | Metal |
-- | |-------|--------|------|-------|
-- | | Max workgroup size (x) | 1024 | 1024 | 1024 |
-- | | Max workgroup size (y) | 1024 | 1024 | 1024 |
-- | | Max workgroup size (z) | 64 | 64 | 64 |
-- | | Max total threads/workgroup | 1024 | 1024 | 1024 |
-- | | Max grid size (x) | 65535 | 2^31-1 | 2^32-1 |
-- | | Max grid size (y) | 65535 | 65535 | 65535 |
-- | | Max grid size (z) | 65535 | 65535 | 65535 |
-- | | Max shared memory | 16KB-48KB | 48KB | 32KB |
-- |
-- | We use WebGPU-compatible limits as the baseline for portability.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Bounded (clampInt, IntBounds)
-- |
-- | ## Dependents
-- |
-- | - Compute.Graph (dispatch config for kernel nodes)
-- | - Target.WebGPU (actual dispatch execution)
-- | - Target.WASM (CPU fallback simulation)

module Hydrogen.Schema.Compute.Dispatch
  ( -- * Workgroup Dimensions
    WorkgroupDimX(WorkgroupDimX)
  , WorkgroupDimY(WorkgroupDimY)
  , WorkgroupDimZ(WorkgroupDimZ)
  , workgroupDimX
  , workgroupDimY
  , workgroupDimZ
  , unwrapWorkgroupDimX
  , unwrapWorkgroupDimY
  , unwrapWorkgroupDimZ
  , workgroupDimXBounds
  , workgroupDimYBounds
  , workgroupDimZBounds
  
  -- * Workgroup Size (Molecule)
  , WorkgroupSize
  , workgroupSize
  , workgroupSize1D
  , workgroupSize2D
  , workgroupSize3D
  , defaultWorkgroupSize
  , totalThreads
  , isValidWorkgroupSize
  , getWorkgroupDimX
  , getWorkgroupDimY
  , getWorkgroupDimZ
  
  -- * Grid Dimensions
  , GridDimX(GridDimX)
  , GridDimY(GridDimY)
  , GridDimZ(GridDimZ)
  , gridDimX
  , gridDimY
  , gridDimZ
  , unwrapGridDimX
  , unwrapGridDimY
  , unwrapGridDimZ
  , gridDimXBounds
  , gridDimYBounds
  , gridDimZBounds
  
  -- * Grid Size (Molecule)
  , GridSize
  , gridSize
  , gridSize1D
  , gridSize2D
  , gridSize3D
  , gridSizeForElements
  , totalWorkgroups
  , getGridDimX
  , getGridDimY
  , getGridDimZ
  
  -- * Shared Memory
  , SharedMemoryBytes(SharedMemoryBytes)
  , sharedMemoryBytes
  , unwrapSharedMemoryBytes
  , sharedMemoryBounds
  , noSharedMemory
  , maxSharedMemory
  
  -- * Dispatch Configuration (Compound)
  , DispatchConfig
  , dispatchConfig
  , defaultDispatch1D
  , defaultDispatch2D
  , totalInvocations
  , estimateOccupancy
  
  -- * Dispatch Strategies
  , DispatchStrategy(ElementWise, TileWise, ReductionTree, MatrixTile, Custom)
  , dispatchStrategyFor
  , optimalWorkgroupForStrategy
  
  -- * Presets
  , warpSize
  , wavefrontSize
  , commonWorkgroups
  
  -- * Validation
  , isWarpAligned
  , isWavefrontAligned
  , validateDispatch
  , isValidDispatch
  
  -- * Utilities
  , ceilDiv
  , gridSizeForElements2D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , max
  , min
  , mod
  , (==)
  , (<>)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<=)
  , (>=)
  , (>)
  , (&&)
  )

import Data.Int (toNumber, ceil)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps)) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // workgroup dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup dimension X [1, 1024]
-- |
-- | The number of threads in the X dimension of a workgroup.
-- | Must be at least 1 (no empty workgroups).
newtype WorkgroupDimX = WorkgroupDimX Int

derive instance eqWorkgroupDimX :: Eq WorkgroupDimX
derive instance ordWorkgroupDimX :: Ord WorkgroupDimX

instance showWorkgroupDimX :: Show WorkgroupDimX where
  show (WorkgroupDimX n) = show n

-- | Create workgroup X dimension (clamps to [1, 1024])
workgroupDimX :: Int -> WorkgroupDimX
workgroupDimX n = WorkgroupDimX (Bounded.clampInt 1 1024 n)

-- | Unwrap workgroup X dimension
unwrapWorkgroupDimX :: WorkgroupDimX -> Int
unwrapWorkgroupDimX (WorkgroupDimX n) = n

-- | Bounds for WorkgroupDimX
workgroupDimXBounds :: Bounded.IntBounds
workgroupDimXBounds = Bounded.intBounds 1 1024 Bounded.Clamps 
  "workgroupDimX" 
  "Threads in X dimension of workgroup (1-1024)"

-- | Workgroup dimension Y [1, 1024]
newtype WorkgroupDimY = WorkgroupDimY Int

derive instance eqWorkgroupDimY :: Eq WorkgroupDimY
derive instance ordWorkgroupDimY :: Ord WorkgroupDimY

instance showWorkgroupDimY :: Show WorkgroupDimY where
  show (WorkgroupDimY n) = show n

-- | Create workgroup Y dimension (clamps to [1, 1024])
workgroupDimY :: Int -> WorkgroupDimY
workgroupDimY n = WorkgroupDimY (Bounded.clampInt 1 1024 n)

-- | Unwrap workgroup Y dimension
unwrapWorkgroupDimY :: WorkgroupDimY -> Int
unwrapWorkgroupDimY (WorkgroupDimY n) = n

-- | Bounds for WorkgroupDimY
workgroupDimYBounds :: Bounded.IntBounds
workgroupDimYBounds = Bounded.intBounds 1 1024 Bounded.Clamps 
  "workgroupDimY" 
  "Threads in Y dimension of workgroup (1-1024)"

-- | Workgroup dimension Z [1, 64]
-- |
-- | Z dimension is more limited on most hardware.
newtype WorkgroupDimZ = WorkgroupDimZ Int

derive instance eqWorkgroupDimZ :: Eq WorkgroupDimZ
derive instance ordWorkgroupDimZ :: Ord WorkgroupDimZ

instance showWorkgroupDimZ :: Show WorkgroupDimZ where
  show (WorkgroupDimZ n) = show n

-- | Create workgroup Z dimension (clamps to [1, 64])
workgroupDimZ :: Int -> WorkgroupDimZ
workgroupDimZ n = WorkgroupDimZ (Bounded.clampInt 1 64 n)

-- | Unwrap workgroup Z dimension
unwrapWorkgroupDimZ :: WorkgroupDimZ -> Int
unwrapWorkgroupDimZ (WorkgroupDimZ n) = n

-- | Bounds for WorkgroupDimZ
workgroupDimZBounds :: Bounded.IntBounds
workgroupDimZBounds = Bounded.intBounds 1 64 Bounded.Clamps 
  "workgroupDimZ" 
  "Threads in Z dimension of workgroup (1-64)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // workgroup size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size (3D thread count within a workgroup).
-- |
-- | Total threads (x * y * z) must not exceed 1024.
type WorkgroupSize =
  { x :: WorkgroupDimX
  , y :: WorkgroupDimY
  , z :: WorkgroupDimZ
  }

-- | Create a workgroup size with validation.
-- |
-- | If total threads exceed 1024, z is reduced first, then y, then x.
workgroupSize :: Int -> Int -> Int -> WorkgroupSize
workgroupSize x y z =
  let
    -- Clamp individual dimensions first
    cx = Bounded.clampInt 1 1024 x
    cy = Bounded.clampInt 1 1024 y
    cz = Bounded.clampInt 1 64 z
    -- Check total and reduce if needed
    total = cx * cy * cz
  in
    if total <= 1024 then
      { x: WorkgroupDimX cx
      , y: WorkgroupDimY cy
      , z: WorkgroupDimZ cz
      }
    else
      -- Reduce dimensions to fit 1024 limit
      -- Strategy: prefer keeping x*y high, reduce z first
      let
        maxZ = 1024 / (cx * cy)
        newZ = max 1 (min cz maxZ)
        newTotal = cx * cy * newZ
      in
        if newTotal <= 1024 then
          { x: WorkgroupDimX cx
          , y: WorkgroupDimY cy
          , z: WorkgroupDimZ newZ
          }
        else
          -- Still too large, reduce y
          let
            maxY = 1024 / cx
            newY = max 1 (min cy maxY)
          in
            { x: WorkgroupDimX cx
            , y: WorkgroupDimY newY
            , z: WorkgroupDimZ 1
            }

-- | 1D workgroup (threads only in X)
workgroupSize1D :: Int -> WorkgroupSize
workgroupSize1D threads = workgroupSize threads 1 1

-- | 2D workgroup (threads in X and Y)
workgroupSize2D :: Int -> Int -> WorkgroupSize
workgroupSize2D x y = workgroupSize x y 1

-- | 3D workgroup
workgroupSize3D :: Int -> Int -> Int -> WorkgroupSize
workgroupSize3D = workgroupSize

-- | Default workgroup size: 256 threads (16x16x1)
-- |
-- | 256 is a good default:
-- | - 8 warps on NVIDIA (32 threads/warp)
-- | - 4 wavefronts on AMD (64 threads/wavefront)
-- | - Fits 1024 thread limit with room for larger 3D workgroups
defaultWorkgroupSize :: WorkgroupSize
defaultWorkgroupSize = workgroupSize2D 16 16

-- | Total number of threads in a workgroup
totalThreads :: WorkgroupSize -> Int
totalThreads wg = 
  unwrapWorkgroupDimX wg.x * unwrapWorkgroupDimY wg.y * unwrapWorkgroupDimZ wg.z

-- | Check if workgroup size is valid (total <= 1024)
isValidWorkgroupSize :: WorkgroupSize -> Boolean
isValidWorkgroupSize wg = totalThreads wg <= 1024

-- | Get X dimension from workgroup size
getWorkgroupDimX :: WorkgroupSize -> WorkgroupDimX
getWorkgroupDimX wg = wg.x

-- | Get Y dimension from workgroup size
getWorkgroupDimY :: WorkgroupSize -> WorkgroupDimY
getWorkgroupDimY wg = wg.y

-- | Get Z dimension from workgroup size
getWorkgroupDimZ :: WorkgroupSize -> WorkgroupDimZ
getWorkgroupDimZ wg = wg.z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // grid dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid dimension X [1, 65535]
-- |
-- | Number of workgroups in the X dimension.
newtype GridDimX = GridDimX Int

derive instance eqGridDimX :: Eq GridDimX
derive instance ordGridDimX :: Ord GridDimX

instance showGridDimX :: Show GridDimX where
  show (GridDimX n) = show n

-- | Create grid X dimension (clamps to [1, 65535])
gridDimX :: Int -> GridDimX
gridDimX n = GridDimX (Bounded.clampInt 1 65535 n)

-- | Unwrap grid X dimension
unwrapGridDimX :: GridDimX -> Int
unwrapGridDimX (GridDimX n) = n

-- | Bounds for GridDimX
gridDimXBounds :: Bounded.IntBounds
gridDimXBounds = Bounded.intBounds 1 65535 Bounded.Clamps 
  "gridDimX" 
  "Workgroups in X dimension of dispatch grid (1-65535)"

-- | Grid dimension Y [1, 65535]
newtype GridDimY = GridDimY Int

derive instance eqGridDimY :: Eq GridDimY
derive instance ordGridDimY :: Ord GridDimY

instance showGridDimY :: Show GridDimY where
  show (GridDimY n) = show n

-- | Create grid Y dimension (clamps to [1, 65535])
gridDimY :: Int -> GridDimY
gridDimY n = GridDimY (Bounded.clampInt 1 65535 n)

-- | Unwrap grid Y dimension
unwrapGridDimY :: GridDimY -> Int
unwrapGridDimY (GridDimY n) = n

-- | Bounds for GridDimY
gridDimYBounds :: Bounded.IntBounds
gridDimYBounds = Bounded.intBounds 1 65535 Bounded.Clamps 
  "gridDimY" 
  "Workgroups in Y dimension of dispatch grid (1-65535)"

-- | Grid dimension Z [1, 65535]
newtype GridDimZ = GridDimZ Int

derive instance eqGridDimZ :: Eq GridDimZ
derive instance ordGridDimZ :: Ord GridDimZ

instance showGridDimZ :: Show GridDimZ where
  show (GridDimZ n) = show n

-- | Create grid Z dimension (clamps to [1, 65535])
gridDimZ :: Int -> GridDimZ
gridDimZ n = GridDimZ (Bounded.clampInt 1 65535 n)

-- | Unwrap grid Z dimension
unwrapGridDimZ :: GridDimZ -> Int
unwrapGridDimZ (GridDimZ n) = n

-- | Bounds for GridDimZ
gridDimZBounds :: Bounded.IntBounds
gridDimZBounds = Bounded.intBounds 1 65535 Bounded.Clamps 
  "gridDimZ" 
  "Workgroups in Z dimension of dispatch grid (1-65535)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // grid size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid size (3D count of workgroups).
type GridSize =
  { x :: GridDimX
  , y :: GridDimY
  , z :: GridDimZ
  }

-- | Create a grid size.
gridSize :: Int -> Int -> Int -> GridSize
gridSize x y z =
  { x: gridDimX x
  , y: gridDimY y
  , z: gridDimZ z
  }

-- | 1D grid
gridSize1D :: Int -> GridSize
gridSize1D x = gridSize x 1 1

-- | 2D grid
gridSize2D :: Int -> Int -> GridSize
gridSize2D x y = gridSize x y 1

-- | 3D grid
gridSize3D :: Int -> Int -> Int -> GridSize
gridSize3D = gridSize

-- | Calculate grid size needed to process N elements.
-- |
-- | Given the number of elements and threads per workgroup,
-- | returns the minimum grid size (1D) to cover all elements.
gridSizeForElements :: Int -> Int -> GridSize
gridSizeForElements elements threadsPerWorkgroup =
  let
    -- Ceiling division: (a + b - 1) / b
    workgroups = if threadsPerWorkgroup <= 0 
                 then 1 
                 else (elements + threadsPerWorkgroup - 1) / threadsPerWorkgroup
  in
    gridSize1D (max 1 workgroups)

-- | Total number of workgroups in the grid
totalWorkgroups :: GridSize -> Int
totalWorkgroups g = 
  unwrapGridDimX g.x * unwrapGridDimY g.y * unwrapGridDimZ g.z

-- | Get X dimension from grid size
getGridDimX :: GridSize -> GridDimX
getGridDimX g = g.x

-- | Get Y dimension from grid size
getGridDimY :: GridSize -> GridDimY
getGridDimY g = g.y

-- | Get Z dimension from grid size
getGridDimZ :: GridSize -> GridDimZ
getGridDimZ g = g.z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shared memory
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shared memory allocation in bytes [0, 49152]
-- |
-- | Shared memory (also called local memory or workgroup memory) is fast
-- | on-chip memory shared between threads in a workgroup.
-- |
-- | WebGPU limit: 16KB (16384 bytes) guaranteed
-- | CUDA limit: 48KB (49152 bytes) typical
-- | We use 48KB as max to enable high-performance kernels.
newtype SharedMemoryBytes = SharedMemoryBytes Int

derive instance eqSharedMemoryBytes :: Eq SharedMemoryBytes
derive instance ordSharedMemoryBytes :: Ord SharedMemoryBytes

instance showSharedMemoryBytes :: Show SharedMemoryBytes where
  show (SharedMemoryBytes n) = show n <> " bytes"

-- | Create shared memory allocation (clamps to [0, 49152])
sharedMemoryBytes :: Int -> SharedMemoryBytes
sharedMemoryBytes n = SharedMemoryBytes (Bounded.clampInt 0 49152 n)

-- | Unwrap shared memory bytes
unwrapSharedMemoryBytes :: SharedMemoryBytes -> Int
unwrapSharedMemoryBytes (SharedMemoryBytes n) = n

-- | Bounds for SharedMemoryBytes
sharedMemoryBounds :: Bounded.IntBounds
sharedMemoryBounds = Bounded.intBounds 0 49152 Bounded.Clamps 
  "sharedMemoryBytes" 
  "Shared memory allocation per workgroup (0-49152 bytes)"

-- | No shared memory allocation
noSharedMemory :: SharedMemoryBytes
noSharedMemory = SharedMemoryBytes 0

-- | Maximum shared memory (48KB)
maxSharedMemory :: SharedMemoryBytes
maxSharedMemory = SharedMemoryBytes 49152

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dispatch config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete dispatch configuration (Compound).
-- |
-- | Contains everything needed to dispatch a GPU compute kernel:
-- | - Workgroup size (threads per workgroup)
-- | - Grid size (number of workgroups)
-- | - Shared memory allocation
type DispatchConfig =
  { workgroup :: WorkgroupSize
  , grid :: GridSize
  , sharedMemory :: SharedMemoryBytes
  }

-- | Create a dispatch configuration.
dispatchConfig :: WorkgroupSize -> GridSize -> SharedMemoryBytes -> DispatchConfig
dispatchConfig workgroup grid sharedMemory =
  { workgroup
  , grid
  , sharedMemory
  }

-- | Default 1D dispatch for N elements.
-- |
-- | Uses 256 threads per workgroup (good for most elementwise ops).
defaultDispatch1D :: Int -> DispatchConfig
defaultDispatch1D elements =
  let
    wg = workgroupSize1D 256
    gr = gridSizeForElements elements 256
  in
    dispatchConfig wg gr noSharedMemory

-- | Default 2D dispatch for MxN elements.
-- |
-- | Uses 16x16 workgroups (256 threads, good for 2D operations).
defaultDispatch2D :: Int -> Int -> DispatchConfig
defaultDispatch2D rows cols =
  let
    wg = workgroupSize2D 16 16
    -- Calculate grid dimensions
    gridX = (cols + 15) / 16  -- Ceiling division
    gridY = (rows + 15) / 16
    gr = gridSize2D gridX gridY
  in
    dispatchConfig wg gr noSharedMemory

-- | Total number of thread invocations.
totalInvocations :: DispatchConfig -> Int
totalInvocations dc = totalThreads dc.workgroup * totalWorkgroups dc.grid

-- | Estimate occupancy (threads per SM).
-- |
-- | Returns a ratio [0.0, 1.0] where 1.0 means full occupancy.
-- | This is a simplified estimate based on thread count.
estimateOccupancy :: DispatchConfig -> Number
estimateOccupancy dc =
  let
    threads = totalThreads dc.workgroup
    -- Assume 2048 max threads per SM (common on modern GPUs)
    maxThreadsPerSM = 2048
  in
    toNumber threads / toNumber maxThreadsPerSM

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dispatch strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dispatch strategy for different operation types.
-- |
-- | Different operations benefit from different dispatch patterns.
data DispatchStrategy
  = ElementWise           -- ^ One thread per element
  | TileWise              -- ^ Process data in tiles (for memory coalescing)
  | ReductionTree         -- ^ Tree-based reduction (sum, max, etc.)
  | MatrixTile            -- ^ Tiled matrix operations
  | Custom                -- ^ Custom strategy (manual configuration)

derive instance eqDispatchStrategy :: Eq DispatchStrategy

instance showDispatchStrategy :: Show DispatchStrategy where
  show ElementWise = "ElementWise"
  show TileWise = "TileWise"
  show ReductionTree = "ReductionTree"
  show MatrixTile = "MatrixTile"
  show Custom = "Custom"

-- | Recommend dispatch strategy based on operation type.
dispatchStrategyFor :: String -> DispatchStrategy
dispatchStrategyFor opName = case opName of
  "Add" -> ElementWise
  "Mul" -> ElementWise
  "Sub" -> ElementWise
  "Div" -> ElementWise
  "ReLU" -> ElementWise
  "GELU" -> ElementWise
  "SiLU" -> ElementWise
  "Sigmoid" -> ElementWise
  "Tanh" -> ElementWise
  "Exp" -> ElementWise
  "Log" -> ElementWise
  "Sqrt" -> ElementWise
  "Neg" -> ElementWise
  "Abs" -> ElementWise
  "ReduceSum" -> ReductionTree
  "ReduceMean" -> ReductionTree
  "ReduceMax" -> ReductionTree
  "ReduceMin" -> ReductionTree
  "MatMul" -> MatrixTile
  "Linear" -> MatrixTile
  "Conv1D" -> TileWise
  "Conv2D" -> TileWise
  "Conv3D" -> TileWise
  "Softmax" -> TileWise
  "LayerNorm" -> TileWise
  "BatchNorm" -> TileWise
  "RMSNorm" -> TileWise
  _ -> Custom

-- | Optimal workgroup size for dispatch strategy.
optimalWorkgroupForStrategy :: DispatchStrategy -> WorkgroupSize
optimalWorkgroupForStrategy ElementWise = workgroupSize1D 256
optimalWorkgroupForStrategy TileWise = workgroupSize2D 16 16
optimalWorkgroupForStrategy ReductionTree = workgroupSize1D 256
optimalWorkgroupForStrategy MatrixTile = workgroupSize2D 16 16
optimalWorkgroupForStrategy Custom = defaultWorkgroupSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | NVIDIA warp size: 32 threads
-- |
-- | Threads in a warp execute in lockstep.
warpSize :: Int
warpSize = 32

-- | AMD wavefront size: 64 threads
-- |
-- | Threads in a wavefront execute in lockstep.
wavefrontSize :: Int
wavefrontSize = 64

-- | Common workgroup size presets.
-- |
-- | These are optimized for different scenarios:
-- |
-- | - `warp`: Single warp (NVIDIA) — minimal overhead
-- | - `wavefront`: Single wavefront (AMD) — minimal overhead
-- | - `small`: 128 threads — balanced
-- | - `medium`: 256 threads — default for most operations
-- | - `large`: 512 threads — high throughput
-- | - `max`: 1024 threads — maximum parallelism
-- | - `tile8`: 8x8 — small 2D tile
-- | - `tile16`: 16x16 — standard 2D tile
-- | - `tile32`: 32x32 — large 2D tile (reaches 1024 limit)
commonWorkgroups :: 
  { warp :: WorkgroupSize
  , wavefront :: WorkgroupSize
  , small :: WorkgroupSize
  , medium :: WorkgroupSize
  , large :: WorkgroupSize
  , max :: WorkgroupSize
  , tile8 :: WorkgroupSize
  , tile16 :: WorkgroupSize
  , tile32 :: WorkgroupSize
  }
commonWorkgroups =
  { warp: workgroupSize1D 32
  , wavefront: workgroupSize1D 64
  , small: workgroupSize1D 128
  , medium: workgroupSize1D 256
  , large: workgroupSize1D 512
  , max: workgroupSize1D 1024
  , tile8: workgroupSize2D 8 8
  , tile16: workgroupSize2D 16 16
  , tile32: workgroupSize2D 32 32
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if workgroup size is aligned to warp/wavefront boundaries.
-- |
-- | For optimal performance, workgroup sizes should be multiples of 32 (NVIDIA)
-- | or 64 (AMD). This checks alignment to either.
isWarpAligned :: WorkgroupSize -> Boolean
isWarpAligned wg = 
  let threads = totalThreads wg
  in threads >= warpSize && mod threads warpSize == 0

-- | Check if workgroup size is aligned to wavefront boundaries.
isWavefrontAligned :: WorkgroupSize -> Boolean
isWavefrontAligned wg = 
  let threads = totalThreads wg
  in threads >= wavefrontSize && mod threads wavefrontSize == 0

-- | Validate dispatch configuration for WebGPU compatibility.
-- |
-- | Returns Nothing if valid, Just error message if invalid.
validateDispatch :: DispatchConfig -> Maybe String
validateDispatch dc =
  let
    threads = totalThreads dc.workgroup
    workgroups = totalWorkgroups dc.grid
    sharedMem = unwrapSharedMemoryBytes dc.sharedMemory
  in
    if threads > 1024 then
      Just "Workgroup exceeds 1024 threads"
    else if unwrapWorkgroupDimZ dc.workgroup.z > 64 then
      Just "Workgroup Z dimension exceeds 64"
    else if unwrapGridDimX dc.grid.x > 65535 then
      Just "Grid X dimension exceeds 65535"
    else if unwrapGridDimY dc.grid.y > 65535 then
      Just "Grid Y dimension exceeds 65535"
    else if unwrapGridDimZ dc.grid.z > 65535 then
      Just "Grid Z dimension exceeds 65535"
    else if sharedMem > 49152 then
      Just "Shared memory exceeds 48KB"
    else if workgroups > 2147483647 then
      -- Sanity check: prevent overflow when computing total invocations
      Just "Total workgroups exceeds Int32 max"
    else
      Nothing

-- | Check if dispatch is valid (no errors).
isValidDispatch :: DispatchConfig -> Boolean
isValidDispatch dc = case validateDispatch dc of
  Nothing -> true
  Just _ -> false

-- | Calculate ceiling division using proper ceiling function.
-- |
-- | Returns the smallest integer >= a/b.
ceilDiv :: Int -> Int -> Int
ceilDiv a b =
  if b <= 0 then 1
  else ceil (toNumber a / toNumber b)

-- | Create grid size using ceiling division for element coverage.
-- |
-- | Ensures all elements are covered even if not evenly divisible.
gridSizeForElements2D :: Int -> Int -> Int -> Int -> GridSize
gridSizeForElements2D rows cols threadsX threadsY =
  let
    gridX = ceilDiv cols threadsX
    gridY = ceilDiv rows threadsY
  in
    gridSize2D (max 1 gridX) (max 1 gridY)
