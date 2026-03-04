-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // gpu // texture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Texture Schema — Bounded texture descriptors with graded co-effects.
-- |
-- | ## Design Philosophy
-- |
-- | Textures are images stored on the GPU for sampling in shaders.
-- | This module provides:
-- |
-- | 1. **Bounded dimensions**: All sizes use bounded types (1-8192, 1-2048)
-- | 2. **Format enumeration**: Complete WebGPU texture format coverage
-- | 3. **Co-effects**: Track memory requirements based on dimensions and format
-- |
-- | ## Memory Calculation
-- |
-- | Texture memory is calculated as:
-- | ```
-- | memory = width × height × depth × bytesPerPixel × mipFactor
-- | ```
-- |
-- | Where mipFactor ≈ 1.33 for full mip chain (1 + 1/4 + 1/16 + ...).
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.GPU.Limits.Texture
-- | - Hydrogen.Schema.GPU.Texture.Format

module Hydrogen.Schema.GPU.Texture
  ( -- * Re-exports from Format
    module Hydrogen.Schema.GPU.Texture.Format
  
  -- * Texture Dimension Type
  , TextureDimensionType
      ( Texture1D
      , Texture2D
      , Texture3D
      )
  , dimensionTypeToString
  
  -- * Texture Usage Flags
  , TextureUsage
      ( TextureUsageCopySrc
      , TextureUsageCopyDst
      , TextureUsageTextureBinding
      , TextureUsageStorageBinding
      , TextureUsageRenderAttachment
      )
  , allTextureUsages
  , textureUsageToString
  , textureUsageToBitmask
  , textureUsageSetToBitmask
  
  -- * Bounded Texture Size
  , TextureSize2D
  , textureSize2D
  , textureSizeWidth
  , textureSizeHeight
  
  , TextureSize3D
  , textureSize3D
  , textureSize3DWidth
  , textureSize3DHeight
  , textureSize3DDepth
  
  -- * Texture Descriptor
  , TextureDescriptor2D
  , textureDescriptor2D
  
  -- * Co-Effect Calculation
  , textureMemoryBytes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (+)
  , (<>)
  )

import Data.Foldable (foldr)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.GPU.Limits.Texture
  ( TextureDimension2D
  , TextureDimension3D
  , TextureArrayLayers
  , clampTextureArrayLayers
  , unwrapTextureDimension2D
  , unwrapTextureDimension3D
  , unwrapTextureArrayLayers
  )

import Hydrogen.Schema.GPU.Texture.Format
  ( TextureFormat
      ( FormatR8Unorm
      , FormatR8Snorm
      , FormatR8Uint
      , FormatR8Sint
      , FormatR16Uint
      , FormatR16Sint
      , FormatR16Float
      , FormatRG8Unorm
      , FormatRG8Snorm
      , FormatRG8Uint
      , FormatRG8Sint
      , FormatR32Uint
      , FormatR32Sint
      , FormatR32Float
      , FormatRG16Uint
      , FormatRG16Sint
      , FormatRG16Float
      , FormatRGBA8Unorm
      , FormatRGBA8UnormSrgb
      , FormatRGBA8Snorm
      , FormatRGBA8Uint
      , FormatRGBA8Sint
      , FormatBGRA8Unorm
      , FormatBGRA8UnormSrgb
      , FormatRGB9E5Ufloat
      , FormatRGB10A2Uint
      , FormatRGB10A2Unorm
      , FormatRG11B10Ufloat
      , FormatRG32Uint
      , FormatRG32Sint
      , FormatRG32Float
      , FormatRGBA16Uint
      , FormatRGBA16Sint
      , FormatRGBA16Float
      , FormatRGBA32Uint
      , FormatRGBA32Sint
      , FormatRGBA32Float
      , FormatStencil8
      , FormatDepth16Unorm
      , FormatDepth24Plus
      , FormatDepth24PlusStencil8
      , FormatDepth32Float
      , FormatDepth32FloatStencil8
      )
  , textureFormatToString
  , textureFormatFromString
  , textureFormatBytesPerPixel
  , isDepthFormat
  , isStencilFormat
  , isCompressedFormat
  , isSrgbFormat
  , isFloatFormat
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // texture dimension type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture dimension type.
-- |
-- | Determines how the texture is addressed in shaders:
-- | - 1D: Single row of pixels (u coordinate)
-- | - 2D: Grid of pixels (u, v coordinates)
-- | - 3D: Volume of pixels (u, v, w coordinates)
data TextureDimensionType
  = Texture1D
  | Texture2D
  | Texture3D

derive instance eqTextureDimensionType :: Eq TextureDimensionType
derive instance ordTextureDimensionType :: Ord TextureDimensionType

instance showTextureDimensionType :: Show TextureDimensionType where
  show = dimensionTypeToString

-- | Convert dimension type to WebGPU string.
dimensionTypeToString :: TextureDimensionType -> String
dimensionTypeToString Texture1D = "1d"
dimensionTypeToString Texture2D = "2d"
dimensionTypeToString Texture3D = "3d"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // texture usage
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture usage flags.
-- |
-- | These determine what operations can be performed on the texture.
data TextureUsage
  = TextureUsageCopySrc
    -- ^ Texture can be source of copy operation
  | TextureUsageCopyDst
    -- ^ Texture can be destination of copy operation
  | TextureUsageTextureBinding
    -- ^ Texture can be bound for sampling in shaders
  | TextureUsageStorageBinding
    -- ^ Texture can be bound as storage texture in shaders
  | TextureUsageRenderAttachment
    -- ^ Texture can be used as render target

derive instance eqTextureUsage :: Eq TextureUsage
derive instance ordTextureUsage :: Ord TextureUsage

instance showTextureUsage :: Show TextureUsage where
  show = textureUsageToString

-- | All texture usage values.
allTextureUsages :: Array TextureUsage
allTextureUsages =
  [ TextureUsageCopySrc
  , TextureUsageCopyDst
  , TextureUsageTextureBinding
  , TextureUsageStorageBinding
  , TextureUsageRenderAttachment
  ]

-- | Convert usage to WebGPU string.
textureUsageToString :: TextureUsage -> String
textureUsageToString TextureUsageCopySrc = "COPY_SRC"
textureUsageToString TextureUsageCopyDst = "COPY_DST"
textureUsageToString TextureUsageTextureBinding = "TEXTURE_BINDING"
textureUsageToString TextureUsageStorageBinding = "STORAGE_BINDING"
textureUsageToString TextureUsageRenderAttachment = "RENDER_ATTACHMENT"

-- | Convert usage to bitmask.
textureUsageToBitmask :: TextureUsage -> Int
textureUsageToBitmask TextureUsageCopySrc = 1
textureUsageToBitmask TextureUsageCopyDst = 2
textureUsageToBitmask TextureUsageTextureBinding = 4
textureUsageToBitmask TextureUsageStorageBinding = 8
textureUsageToBitmask TextureUsageRenderAttachment = 16

-- | Combine usage array into bitmask.
textureUsageSetToBitmask :: Array TextureUsage -> Int
textureUsageSetToBitmask = foldr (\u acc -> acc + textureUsageToBitmask u) 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bounded texture size
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D texture size with bounded dimensions.
type TextureSize2D =
  { width :: TextureDimension2D
  , height :: TextureDimension2D
  }

-- | Create a 2D texture size.
textureSize2D :: TextureDimension2D -> TextureDimension2D -> TextureSize2D
textureSize2D w h = { width: w, height: h }

-- | Get width from 2D size.
textureSizeWidth :: TextureSize2D -> TextureDimension2D
textureSizeWidth s = s.width

-- | Get height from 2D size.
textureSizeHeight :: TextureSize2D -> TextureDimension2D
textureSizeHeight s = s.height

-- | 3D texture size with bounded dimensions.
type TextureSize3D =
  { width :: TextureDimension3D
  , height :: TextureDimension3D
  , depth :: TextureDimension3D
  }

-- | Create a 3D texture size.
textureSize3D
  :: TextureDimension3D
  -> TextureDimension3D
  -> TextureDimension3D
  -> TextureSize3D
textureSize3D w h d = { width: w, height: h, depth: d }

-- | Get width from 3D size.
textureSize3DWidth :: TextureSize3D -> TextureDimension3D
textureSize3DWidth s = s.width

-- | Get height from 3D size.
textureSize3DHeight :: TextureSize3D -> TextureDimension3D
textureSize3DHeight s = s.height

-- | Get depth from 3D size.
textureSize3DDepth :: TextureSize3D -> TextureDimension3D
textureSize3DDepth s = s.depth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // texture descriptor
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Texture descriptor with bounded dimensions.
type TextureDescriptor2D =
  { size :: TextureSize2D
  , arrayLayers :: TextureArrayLayers
  , mipLevelCount :: Int
  , sampleCount :: Int
  , format :: TextureFormat
  , usages :: Array TextureUsage
  , label :: Maybe String
  }

-- | Create a 2D texture descriptor.
textureDescriptor2D
  :: TextureSize2D
  -> TextureFormat
  -> Array TextureUsage
  -> Maybe String
  -> TextureDescriptor2D
textureDescriptor2D sz fmt usages lbl =
  { size: sz
  , arrayLayers: clampTextureArrayLayers 1
  , mipLevelCount: 1
  , sampleCount: 1
  , format: fmt
  , usages: usages
  , label: lbl
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // co-effect calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate approximate memory usage for a 2D texture in bytes.
-- |
-- | This is an approximation assuming no mipmaps.
textureMemoryBytes :: TextureDescriptor2D -> Int
textureMemoryBytes desc =
  let
    w = unwrapTextureDimension2D desc.size.width
    h = unwrapTextureDimension2D desc.size.height
    layers = unwrapTextureArrayLayers desc.arrayLayers
    bpp = textureFormatBytesPerPixel desc.format
  in
    w * h * layers * bpp
