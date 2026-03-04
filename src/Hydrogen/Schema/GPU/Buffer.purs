-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // gpu // buffer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Buffer Schema — Bounded buffer descriptors with graded co-effects.
-- |
-- | ## Design Philosophy
-- |
-- | Buffers are the primary mechanism for transferring data between CPU and GPU.
-- | This module provides:
-- |
-- | 1. **Bounded types**: All sizes use bounded `BufferSize` (0-256MB)
-- | 2. **Usage flags**: Type-safe buffer usage specification
-- | 3. **Co-effects**: Track memory requirements for constraint solving
-- |
-- | ## Co-Effect Semantics
-- |
-- | Buffer co-effects are ADDITIVE: creating two buffers of 1MB each
-- | requires 2MB total. This enables Presburger constraint solving:
-- |
-- | ```
-- | totalMemory = Σ bufferSize_i ≤ deviceLimit.maxBufferSize
-- | ```
-- |
-- | ## WebGPU Buffer Usage
-- |
-- | Each buffer has a set of usage flags that determine valid operations:
-- |
-- | | Usage       | Description                              |
-- | |-------------|------------------------------------------|
-- | | MapRead     | Can be mapped for CPU read               |
-- | | MapWrite    | Can be mapped for CPU write              |
-- | | CopySrc     | Can be source of copy operation          |
-- | | CopyDst     | Can be destination of copy operation     |
-- | | Index       | Can be used as index buffer              |
-- | | Vertex      | Can be used as vertex buffer             |
-- | | Uniform     | Can be used as uniform buffer            |
-- | | Storage     | Can be used as storage buffer            |
-- | | Indirect    | Can be used for indirect draw/dispatch   |
-- | | QueryResolve| Can receive query results                |
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.GPU.Limits.Buffer
-- | - Hydrogen.Schema.GPU.Effect

module Hydrogen.Schema.GPU.Buffer
  ( -- * Buffer Usage Flags
    BufferUsage
      ( UsageMapRead
      , UsageMapWrite
      , UsageCopySrc
      , UsageCopyDst
      , UsageIndex
      , UsageVertex
      , UsageUniform
      , UsageStorage
      , UsageIndirect
      , UsageQueryResolve
      )
  , allBufferUsages
  , usageToString
  , usageToBitmask
  , usageSetToBitmask
  , hasUsage
  , addUsage
  , removeUsage
  
  -- * Buffer Map Mode
  , MapMode(MapModeRead, MapModeWrite)
  , mapModeToBitmask
  , combinedMapMode
  
  -- * Buffer Descriptor
  , BufferDescriptor
  , bufferDescriptor
  , bufferDescriptorValidated
  , descriptorSize
  , descriptorUsages
  , descriptorMappedAtCreation
  , descriptorLabel
  , descriptorWithLabel
  , descriptorWithUsage
  
  -- * Co-Effect Calculation
  , bufferCoEffect
  , combineBufferCoEffects
  , totalBufferMemory
  , totalBufferCoEffect
  
  -- * Common Buffer Patterns
  , vertexBufferDescriptor
  , indexBufferDescriptor
  , uniformBufferDescriptor
  , storageBufferDescriptor
  , stagingBufferDescriptor
  , readbackBufferDescriptor
  
  -- * Buffer Validation
  , validateDescriptor
  , hasMappingUsage
  , BufferValidationError
      ( ErrorSizeZero
      , ErrorNoUsages
      , ErrorInvalidMappingUsage
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , map
  , not
  , (==)
  , (&&)
  , (||)
  , (+)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldr, any, elem)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Either (Either(Left, Right))

import Hydrogen.Schema.GPU.Limits.Buffer
  ( BufferSize
  , bufferSize
  , bufferSizeKB
  , bufferSizeMB
  , bufferSizeZero
  , unwrapBufferSize
  )

import Hydrogen.Schema.GPU.Effect
  ( GPUCoEffect
      ( CoEffectNone
      , CoEffectMemory
      , CoEffectComposite
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // buffer usage
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer usage flags.
-- |
-- | These determine what operations can be performed on the buffer.
-- | Multiple usages can be combined.
data BufferUsage
  = UsageMapRead
    -- ^ Buffer can be mapped for CPU read
  | UsageMapWrite
    -- ^ Buffer can be mapped for CPU write
  | UsageCopySrc
    -- ^ Buffer can be source of copy operation
  | UsageCopyDst
    -- ^ Buffer can be destination of copy operation
  | UsageIndex
    -- ^ Buffer can be used as index buffer in draw calls
  | UsageVertex
    -- ^ Buffer can be used as vertex buffer in draw calls
  | UsageUniform
    -- ^ Buffer can be bound as uniform buffer in shaders
  | UsageStorage
    -- ^ Buffer can be bound as storage buffer in shaders
  | UsageIndirect
    -- ^ Buffer can be used for indirect draw/dispatch arguments
  | UsageQueryResolve
    -- ^ Buffer can receive GPU query results

derive instance eqBufferUsage :: Eq BufferUsage
derive instance ordBufferUsage :: Ord BufferUsage

instance showBufferUsage :: Show BufferUsage where
  show = usageToString

-- | All buffer usage values.
allBufferUsages :: Array BufferUsage
allBufferUsages =
  [ UsageMapRead
  , UsageMapWrite
  , UsageCopySrc
  , UsageCopyDst
  , UsageIndex
  , UsageVertex
  , UsageUniform
  , UsageStorage
  , UsageIndirect
  , UsageQueryResolve
  ]

-- | Convert usage to WebGPU string representation.
usageToString :: BufferUsage -> String
usageToString UsageMapRead = "MAP_READ"
usageToString UsageMapWrite = "MAP_WRITE"
usageToString UsageCopySrc = "COPY_SRC"
usageToString UsageCopyDst = "COPY_DST"
usageToString UsageIndex = "INDEX"
usageToString UsageVertex = "VERTEX"
usageToString UsageUniform = "UNIFORM"
usageToString UsageStorage = "STORAGE"
usageToString UsageIndirect = "INDIRECT"
usageToString UsageQueryResolve = "QUERY_RESOLVE"

-- | Convert usage to WebGPU bitmask value.
usageToBitmask :: BufferUsage -> Int
usageToBitmask UsageMapRead = 1
usageToBitmask UsageMapWrite = 2
usageToBitmask UsageCopySrc = 4
usageToBitmask UsageCopyDst = 8
usageToBitmask UsageIndex = 16
usageToBitmask UsageVertex = 32
usageToBitmask UsageUniform = 64
usageToBitmask UsageStorage = 128
usageToBitmask UsageIndirect = 256
usageToBitmask UsageQueryResolve = 512

-- | Combine usage array into a bitmask.
usageSetToBitmask :: Array BufferUsage -> Int
usageSetToBitmask = foldr (\u acc -> acc + usageToBitmask u) 0

-- | Check if a usage set contains a specific usage.
hasUsage :: BufferUsage -> Array BufferUsage -> Boolean
hasUsage usage usages = elem usage usages

-- | Add a usage to a usage set (idempotent).
addUsage :: BufferUsage -> Array BufferUsage -> Array BufferUsage
addUsage usage usages =
  if hasUsage usage usages
    then usages
    else Array.snoc usages usage

-- | Remove a usage from a usage set.
removeUsage :: BufferUsage -> Array BufferUsage -> Array BufferUsage
removeUsage usage = Array.filter (\u -> not (u == usage))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // map mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer map modes.
-- |
-- | When mapping a buffer for CPU access, specify read, write, or both.
data MapMode
  = MapModeRead
    -- ^ Map for reading
  | MapModeWrite
    -- ^ Map for writing

derive instance eqMapMode :: Eq MapMode
derive instance ordMapMode :: Ord MapMode

instance showMapMode :: Show MapMode where
  show MapModeRead = "READ"
  show MapModeWrite = "WRITE"

-- | Convert map mode to bitmask.
mapModeToBitmask :: MapMode -> Int
mapModeToBitmask MapModeRead = 1
mapModeToBitmask MapModeWrite = 2

-- | Combine multiple map modes into a bitmask.
combinedMapMode :: Array MapMode -> Int
combinedMapMode = foldr (\m acc -> acc + mapModeToBitmask m) 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // buffer descriptor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer descriptor with bounded size and typed usage.
-- |
-- | This is the specification for creating a GPU buffer.
-- | All sizes are bounded by `BufferSize` (0-256MB).
type BufferDescriptor =
  { size :: BufferSize
    -- ^ Size in bytes (bounded 0-256MB)
  , usages :: Array BufferUsage
    -- ^ Usage flags (what operations are allowed)
  , mappedAtCreation :: Boolean
    -- ^ Whether to map the buffer immediately on creation
  , label :: Maybe String
    -- ^ Optional debug label
  }

-- | Create a buffer descriptor.
bufferDescriptor
  :: BufferSize
  -> Array BufferUsage
  -> Boolean
  -> Maybe String
  -> BufferDescriptor
bufferDescriptor sz usages mapped lbl =
  { size: sz
  , usages: usages
  , mappedAtCreation: mapped
  , label: lbl
  }

-- | Create a buffer descriptor with size validation.
-- |
-- | Returns Nothing if the size is invalid (outside 0-256MB).
bufferDescriptorValidated
  :: Int
  -> Array BufferUsage
  -> Boolean
  -> Maybe String
  -> Maybe BufferDescriptor
bufferDescriptorValidated sizeBytes usages mapped lbl =
  map (\sz -> bufferDescriptor sz usages mapped lbl) (bufferSize sizeBytes)

-- | Get the size from a descriptor.
descriptorSize :: BufferDescriptor -> BufferSize
descriptorSize d = d.size

-- | Get usages from a descriptor.
descriptorUsages :: BufferDescriptor -> Array BufferUsage
descriptorUsages d = d.usages

-- | Check if buffer is mapped at creation.
descriptorMappedAtCreation :: BufferDescriptor -> Boolean
descriptorMappedAtCreation d = d.mappedAtCreation

-- | Get the label from a descriptor.
descriptorLabel :: BufferDescriptor -> Maybe String
descriptorLabel d = d.label

-- | Create a new descriptor with an updated label.
descriptorWithLabel :: String -> BufferDescriptor -> BufferDescriptor
descriptorWithLabel lbl d = d { label = Just lbl }

-- | Create a new descriptor with an additional usage.
descriptorWithUsage :: BufferUsage -> BufferDescriptor -> BufferDescriptor
descriptorWithUsage usage d = d { usages = addUsage usage d.usages }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // co-effect calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate the co-effect (resource requirement) for a buffer.
-- |
-- | Buffer creation requires memory allocation. The co-effect captures
-- | the memory requirement for constraint solving.
bufferCoEffect :: BufferDescriptor -> GPUCoEffect
bufferCoEffect desc =
  let bytes = unwrapBufferSize desc.size
  in if bytes == 0
       then CoEffectNone
       else CoEffectMemory bytes

-- | Combine co-effects from two buffer operations.
-- |
-- | Memory co-effects are ADDITIVE.
combineBufferCoEffects :: GPUCoEffect -> GPUCoEffect -> GPUCoEffect
combineBufferCoEffects CoEffectNone eff = eff
combineBufferCoEffects eff CoEffectNone = eff
combineBufferCoEffects (CoEffectMemory a) (CoEffectMemory b) = CoEffectMemory (a + b)
combineBufferCoEffects a b = CoEffectComposite [a, b]

-- | Calculate total memory requirement for multiple buffers.
-- |
-- | Memory co-effects are ADDITIVE: two buffers of 1MB = 2MB total.
totalBufferMemory :: Array BufferDescriptor -> Int
totalBufferMemory = foldr (\d acc -> acc + unwrapBufferSize d.size) 0

-- | Calculate combined co-effect for multiple buffers.
totalBufferCoEffect :: Array BufferDescriptor -> GPUCoEffect
totalBufferCoEffect descriptors =
  let total = totalBufferMemory descriptors
  in if total == 0
       then CoEffectNone
       else CoEffectMemory total

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // common buffer patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a vertex buffer descriptor.
-- |
-- | Vertex buffers hold vertex attribute data (positions, normals, UVs).
-- | Typical usage: VERTEX | COPY_DST for static geometry.
vertexBufferDescriptor :: BufferSize -> Maybe String -> BufferDescriptor
vertexBufferDescriptor sz lbl =
  { size: sz
  , usages: [UsageVertex, UsageCopyDst]
  , mappedAtCreation: false
  , label: lbl
  }

-- | Create an index buffer descriptor.
-- |
-- | Index buffers hold indices for indexed drawing.
-- | Typical usage: INDEX | COPY_DST for static geometry.
indexBufferDescriptor :: BufferSize -> Maybe String -> BufferDescriptor
indexBufferDescriptor sz lbl =
  { size: sz
  , usages: [UsageIndex, UsageCopyDst]
  , mappedAtCreation: false
  , label: lbl
  }

-- | Create a uniform buffer descriptor.
-- |
-- | Uniform buffers hold shader constants (matrices, material properties).
-- | Note: Uniform buffers have a separate limit (64KB).
-- | Typical usage: UNIFORM | COPY_DST for frequently updated data.
uniformBufferDescriptor :: BufferSize -> Maybe String -> BufferDescriptor
uniformBufferDescriptor sz lbl =
  { size: sz
  , usages: [UsageUniform, UsageCopyDst]
  , mappedAtCreation: false
  , label: lbl
  }

-- | Create a storage buffer descriptor.
-- |
-- | Storage buffers are for larger, shader-readable/writable data.
-- | Typical usage: STORAGE | COPY_DST | COPY_SRC for compute shaders.
storageBufferDescriptor :: BufferSize -> Maybe String -> BufferDescriptor
storageBufferDescriptor sz lbl =
  { size: sz
  , usages: [UsageStorage, UsageCopyDst, UsageCopySrc]
  , mappedAtCreation: false
  , label: lbl
  }

-- | Create a staging buffer descriptor for uploading data to GPU.
-- |
-- | Staging buffers are used for CPU-GPU data transfer.
-- | Mapped at creation for immediate write access.
-- | Typical usage: MAP_WRITE | COPY_SRC for upload.
stagingBufferDescriptor :: BufferSize -> Maybe String -> BufferDescriptor
stagingBufferDescriptor sz lbl =
  { size: sz
  , usages: [UsageMapWrite, UsageCopySrc]
  , mappedAtCreation: true
  , label: lbl
  }

-- | Create a readback buffer descriptor for downloading data from GPU.
-- |
-- | Readback buffers receive data from GPU for CPU access.
-- | Typical usage: MAP_READ | COPY_DST for download.
readbackBufferDescriptor :: BufferSize -> Maybe String -> BufferDescriptor
readbackBufferDescriptor sz lbl =
  { size: sz
  , usages: [UsageMapRead, UsageCopyDst]
  , mappedAtCreation: false
  , label: lbl
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // buffer validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer validation errors.
data BufferValidationError
  = ErrorSizeZero
    -- ^ Buffer size is zero (usually a mistake)
  | ErrorNoUsages
    -- ^ Buffer has no usage flags (can't be used for anything)
  | ErrorInvalidMappingUsage
    -- ^ mappedAtCreation=true but no MAP_READ or MAP_WRITE usage

derive instance eqBufferValidationError :: Eq BufferValidationError

instance showBufferValidationError :: Show BufferValidationError where
  show ErrorSizeZero = "Buffer size is zero"
  show ErrorNoUsages = "Buffer has no usage flags"
  show ErrorInvalidMappingUsage = "mappedAtCreation requires MAP_READ or MAP_WRITE usage"

-- | Check if usage set includes mapping capability.
hasMappingUsage :: Array BufferUsage -> Boolean
hasMappingUsage usages = hasUsage UsageMapRead usages || hasUsage UsageMapWrite usages

-- | Validate a buffer descriptor.
-- |
-- | Checks for common errors:
-- | - Zero size (usually a mistake)
-- | - No usage flags
-- | - Mapping without MAP_READ or MAP_WRITE
validateDescriptor :: BufferDescriptor -> Either BufferValidationError BufferDescriptor
validateDescriptor desc
  | unwrapBufferSize desc.size == 0 = Left ErrorSizeZero
  | Array.null desc.usages = Left ErrorNoUsages
  | desc.mappedAtCreation && not (hasMappingUsage desc.usages) = Left ErrorInvalidMappingUsage
  | true = Right desc
