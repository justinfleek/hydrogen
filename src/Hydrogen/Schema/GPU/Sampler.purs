-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // gpu // sampler
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Sampler Schema — Bounded sampler descriptors for texture sampling.
-- |
-- | ## Design Philosophy
-- |
-- | Samplers define HOW textures are sampled in shaders:
-- | - Address modes: What happens at texture edges
-- | - Filter modes: How to interpolate between texels
-- | - Mipmap modes: How to select mip levels
-- | - Comparison: For shadow/depth sampling
-- |
-- | ## Co-Effect Model
-- |
-- | Samplers are lightweight objects (no significant memory footprint).
-- | Co-effects track sampler binding slot usage, not memory.
-- |
-- | ## Bounded Values
-- |
-- | - `maxAnisotropy`: 1-16 (clamped)
-- | - `lodMinClamp`: 0.0-16.0
-- | - `lodMaxClamp`: 0.0-16.0
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#GPUSamplerDescriptor

module Hydrogen.Schema.GPU.Sampler
  ( -- * Address Mode
    AddressMode
      ( AddressClampToEdge
      , AddressRepeat
      , AddressMirrorRepeat
      )
  , addressModeToString
  
  -- * Filter Mode
  , FilterMode
      ( FilterNearest
      , FilterLinear
      )
  , filterModeToString
  
  -- * Mipmap Filter Mode
  , MipmapFilterMode
      ( MipmapFilterNearest
      , MipmapFilterLinear
      )
  , mipmapFilterModeToString
  
  -- * Compare Function
  , CompareFunction
      ( CompareNever
      , CompareLess
      , CompareEqual
      , CompareLessEqual
      , CompareGreater
      , CompareNotEqual
      , CompareGreaterEqual
      , CompareAlways
      )
  , compareFunctionToString
  
  -- * Bounded Anisotropy
  , MaxAnisotropy
  , maxAnisotropy
  , clampMaxAnisotropy
  , unwrapMaxAnisotropy
  , anisotropyBounds
  
  -- * Bounded LOD
  , LodClamp
  , lodClamp
  , clampLodClamp
  , unwrapLodClamp
  
  -- * Sampler Descriptor
  , SamplerDescriptor
  , samplerDescriptor
  , defaultSamplerDescriptor
  , linearSamplerDescriptor
  , nearestSamplerDescriptor
  , shadowSamplerDescriptor
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
  , min
  , max
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // address mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture address mode.
-- |
-- | Determines what happens when sampling outside [0, 1] UV range.
data AddressMode
  = AddressClampToEdge
    -- ^ Clamp to edge texel color
  | AddressRepeat
    -- ^ Repeat (tile) the texture
  | AddressMirrorRepeat
    -- ^ Mirror and repeat

derive instance eqAddressMode :: Eq AddressMode
derive instance ordAddressMode :: Ord AddressMode

instance showAddressMode :: Show AddressMode where
  show = addressModeToString

-- | Convert address mode to WebGPU string.
addressModeToString :: AddressMode -> String
addressModeToString AddressClampToEdge = "clamp-to-edge"
addressModeToString AddressRepeat = "repeat"
addressModeToString AddressMirrorRepeat = "mirror-repeat"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // filter mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture filter mode.
-- |
-- | Determines how texels are interpolated when sampling.
data FilterMode
  = FilterNearest
    -- ^ No interpolation (blocky)
  | FilterLinear
    -- ^ Linear interpolation (smooth)

derive instance eqFilterMode :: Eq FilterMode
derive instance ordFilterMode :: Ord FilterMode

instance showFilterMode :: Show FilterMode where
  show = filterModeToString

-- | Convert filter mode to WebGPU string.
filterModeToString :: FilterMode -> String
filterModeToString FilterNearest = "nearest"
filterModeToString FilterLinear = "linear"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // mipmap filter mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mipmap filter mode.
-- |
-- | Determines how mip levels are selected.
data MipmapFilterMode
  = MipmapFilterNearest
    -- ^ Use nearest mip level
  | MipmapFilterLinear
    -- ^ Blend between mip levels

derive instance eqMipmapFilterMode :: Eq MipmapFilterMode
derive instance ordMipmapFilterMode :: Ord MipmapFilterMode

instance showMipmapFilterMode :: Show MipmapFilterMode where
  show = mipmapFilterModeToString

-- | Convert mipmap filter mode to WebGPU string.
mipmapFilterModeToString :: MipmapFilterMode -> String
mipmapFilterModeToString MipmapFilterNearest = "nearest"
mipmapFilterModeToString MipmapFilterLinear = "linear"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // compare function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Comparison function for depth/stencil operations.
-- |
-- | Used for shadow mapping and depth testing.
data CompareFunction
  = CompareNever
    -- ^ Comparison always fails
  | CompareLess
    -- ^ Pass if reference < sampled
  | CompareEqual
    -- ^ Pass if reference == sampled
  | CompareLessEqual
    -- ^ Pass if reference <= sampled
  | CompareGreater
    -- ^ Pass if reference > sampled
  | CompareNotEqual
    -- ^ Pass if reference != sampled
  | CompareGreaterEqual
    -- ^ Pass if reference >= sampled
  | CompareAlways
    -- ^ Comparison always passes

derive instance eqCompareFunction :: Eq CompareFunction
derive instance ordCompareFunction :: Ord CompareFunction

instance showCompareFunction :: Show CompareFunction where
  show = compareFunctionToString

-- | Convert compare function to WebGPU string.
compareFunctionToString :: CompareFunction -> String
compareFunctionToString CompareNever = "never"
compareFunctionToString CompareLess = "less"
compareFunctionToString CompareEqual = "equal"
compareFunctionToString CompareLessEqual = "less-equal"
compareFunctionToString CompareGreater = "greater"
compareFunctionToString CompareNotEqual = "not-equal"
compareFunctionToString CompareGreaterEqual = "greater-equal"
compareFunctionToString CompareAlways = "always"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bounded anisotropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum anisotropy level.
-- |
-- | Bounds: 1 to 16 (WebGPU limit)
-- |
-- | Anisotropic filtering improves texture quality at glancing angles.
-- | Higher values = better quality but more expensive.
newtype MaxAnisotropy = MaxAnisotropy Int

derive instance eqMaxAnisotropy :: Eq MaxAnisotropy
derive instance ordMaxAnisotropy :: Ord MaxAnisotropy

instance showMaxAnisotropy :: Show MaxAnisotropy where
  show (MaxAnisotropy n) = "MaxAnisotropy(" <> show n <> ")"

-- | Bounds record for anisotropy (for documentation).
anisotropyBounds :: { min :: Int, max :: Int }
anisotropyBounds = { min: 1, max: 16 }

-- | Smart constructor with validation.
maxAnisotropy :: Int -> Maybe MaxAnisotropy
maxAnisotropy n
  | n >= 1 && n <= 16 = Just (MaxAnisotropy n)
  | otherwise = Nothing

-- | Clamping constructor.
clampMaxAnisotropy :: Int -> MaxAnisotropy
clampMaxAnisotropy n = MaxAnisotropy (max 1 (min 16 n))

-- | Extract the underlying Int value.
unwrapMaxAnisotropy :: MaxAnisotropy -> Int
unwrapMaxAnisotropy (MaxAnisotropy n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bounded lod
-- ═════════════════════════════════════════════════════════════════════════════

-- | LOD (Level of Detail) clamp value.
-- |
-- | Bounds: 0.0 to 16.0
-- |
-- | Controls which mip levels are accessible.
newtype LodClamp = LodClamp Number

derive instance eqLodClamp :: Eq LodClamp
derive instance ordLodClamp :: Ord LodClamp

instance showLodClamp :: Show LodClamp where
  show (LodClamp n) = "LodClamp(" <> show n <> ")"

-- | Smart constructor with validation.
lodClamp :: Number -> Maybe LodClamp
lodClamp n
  | n >= 0.0 && n <= 16.0 = Just (LodClamp n)
  | otherwise = Nothing

-- | Clamping constructor.
clampLodClamp :: Number -> LodClamp
clampLodClamp n = LodClamp (max 0.0 (min 16.0 n))

-- | Extract the underlying Number value.
unwrapLodClamp :: LodClamp -> Number
unwrapLodClamp (LodClamp n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // sampler descriptor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sampler descriptor with bounded values.
type SamplerDescriptor =
  { addressModeU :: AddressMode
  , addressModeV :: AddressMode
  , addressModeW :: AddressMode
  , magFilter :: FilterMode
  , minFilter :: FilterMode
  , mipmapFilter :: MipmapFilterMode
  , lodMinClamp :: LodClamp
  , lodMaxClamp :: LodClamp
  , compare :: Maybe CompareFunction
  , maxAnisotropy :: MaxAnisotropy
  , label :: Maybe String
  }

-- | Create a sampler descriptor.
samplerDescriptor
  :: AddressMode
  -> FilterMode
  -> FilterMode
  -> MipmapFilterMode
  -> Maybe String
  -> SamplerDescriptor
samplerDescriptor addressMode magF minF mipF lbl =
  { addressModeU: addressMode
  , addressModeV: addressMode
  , addressModeW: addressMode
  , magFilter: magF
  , minFilter: minF
  , mipmapFilter: mipF
  , lodMinClamp: clampLodClamp 0.0
  , lodMaxClamp: clampLodClamp 16.0
  , compare: Nothing
  , maxAnisotropy: clampMaxAnisotropy 1
  , label: lbl
  }

-- | Default sampler (linear filtering, clamp to edge).
defaultSamplerDescriptor :: SamplerDescriptor
defaultSamplerDescriptor =
  { addressModeU: AddressClampToEdge
  , addressModeV: AddressClampToEdge
  , addressModeW: AddressClampToEdge
  , magFilter: FilterLinear
  , minFilter: FilterLinear
  , mipmapFilter: MipmapFilterLinear
  , lodMinClamp: clampLodClamp 0.0
  , lodMaxClamp: clampLodClamp 16.0
  , compare: Nothing
  , maxAnisotropy: clampMaxAnisotropy 1
  , label: Nothing
  }

-- | Linear sampler (smooth, repeating).
linearSamplerDescriptor :: SamplerDescriptor
linearSamplerDescriptor = defaultSamplerDescriptor
  { addressModeU = AddressRepeat
  , addressModeV = AddressRepeat
  , addressModeW = AddressRepeat
  }

-- | Nearest sampler (no interpolation, for pixel art).
nearestSamplerDescriptor :: SamplerDescriptor
nearestSamplerDescriptor = defaultSamplerDescriptor
  { magFilter = FilterNearest
  , minFilter = FilterNearest
  , mipmapFilter = MipmapFilterNearest
  }

-- | Shadow sampler (for shadow mapping).
shadowSamplerDescriptor :: SamplerDescriptor
shadowSamplerDescriptor = defaultSamplerDescriptor
  { compare = Just CompareLess
  , magFilter = FilterLinear
  , minFilter = FilterLinear
  }
