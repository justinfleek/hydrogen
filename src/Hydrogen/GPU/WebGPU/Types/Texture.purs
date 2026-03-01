-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // webgpu // types // texture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU texture types for WebGPU.
-- Textures are 2D/3D images used for rendering and compute.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.Texture
  ( -- Texture
    GPUTextureDescriptor
  , GPUTextureFormat(..)
  , GPUTextureUsage(..)
  , GPUTextureDimension(..)
  , GPUTextureViewDescriptor
  , GPUTextureViewDimension(..)
  , GPUTextureAspect(..)
  , combineTextureUsage
  ) where

import Prelude

import Data.Foldable (foldr)
import Data.Maybe (Maybe)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- TEXTURE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture creation descriptor.
type GPUTextureDescriptor =
  { size :: { width :: Int, height :: Int, depthOrArrayLayers :: Int }
  , mipLevelCount :: Int
  , sampleCount :: Int
  , dimension :: GPUTextureDimension
  , format :: GPUTextureFormat
  , usage :: Array GPUTextureUsage
  , viewFormats :: Array GPUTextureFormat
  , label :: Maybe String
  }

-- | Texture dimension.
data GPUTextureDimension
  = Dimension1D
  | Dimension2D
  | Dimension3D

derive instance eqGPUTextureDimension :: Eq GPUTextureDimension
derive instance ordGPUTextureDimension :: Ord GPUTextureDimension

-- | Texture formats (subset — add more as needed).
data GPUTextureFormat
  -- 8-bit formats
  = R8Unorm
  | R8Snorm
  | R8Uint
  | R8Sint
  -- 16-bit formats
  | R16Uint
  | R16Sint
  | R16Float
  | RG8Unorm
  | RG8Snorm
  | RG8Uint
  | RG8Sint
  -- 32-bit formats
  | R32Uint
  | R32Sint
  | R32Float
  | RG16Uint
  | RG16Sint
  | RG16Float
  | RGBA8Unorm
  | RGBA8UnormSrgb
  | RGBA8Snorm
  | RGBA8Uint
  | RGBA8Sint
  | BGRA8Unorm
  | BGRA8UnormSrgb
  -- Packed 32-bit formats
  | RGB9E5Ufloat
  | RGB10A2Uint
  | RGB10A2Unorm
  | RG11B10Ufloat
  -- 64-bit formats
  | RG32Uint
  | RG32Sint
  | RG32Float
  | RGBA16Uint
  | RGBA16Sint
  | RGBA16Float
  -- 128-bit formats
  | RGBA32Uint
  | RGBA32Sint
  | RGBA32Float
  -- Depth/stencil formats
  | Stencil8
  | Depth16Unorm
  | Depth24Plus
  | Depth24PlusStencil8
  | Depth32Float
  | Depth32FloatStencil8

derive instance eqGPUTextureFormat :: Eq GPUTextureFormat
derive instance ordGPUTextureFormat :: Ord GPUTextureFormat

-- | Texture usage flags (combinable).
data GPUTextureUsage
  = TextureCopySrc
  | TextureCopyDst
  | TextureBinding
  | StorageBinding
  | RenderAttachment

derive instance eqGPUTextureUsage :: Eq GPUTextureUsage
derive instance ordGPUTextureUsage :: Ord GPUTextureUsage

-- | Combine texture usage flags into a bitmask.
combineTextureUsage :: Array GPUTextureUsage -> Int
combineTextureUsage = foldr (\u acc -> acc + usageToInt u) 0
  where
  usageToInt :: GPUTextureUsage -> Int
  usageToInt = case _ of
    TextureCopySrc -> 1
    TextureCopyDst -> 2
    TextureBinding -> 4
    StorageBinding -> 8
    RenderAttachment -> 16

-- | Texture view descriptor.
type GPUTextureViewDescriptor =
  { format :: Maybe GPUTextureFormat
  , dimension :: Maybe GPUTextureViewDimension
  , aspect :: GPUTextureAspect
  , baseMipLevel :: Int
  , mipLevelCount :: Maybe Int
  , baseArrayLayer :: Int
  , arrayLayerCount :: Maybe Int
  , label :: Maybe String
  }

-- | Texture view dimension.
data GPUTextureViewDimension
  = View1D
  | View2D
  | View2DArray
  | ViewCube
  | ViewCubeArray
  | View3D

derive instance eqGPUTextureViewDimension :: Eq GPUTextureViewDimension
derive instance ordGPUTextureViewDimension :: Ord GPUTextureViewDimension

-- | Texture aspect.
data GPUTextureAspect
  = AspectAll
  | AspectStencilOnly
  | AspectDepthOnly

derive instance eqGPUTextureAspect :: Eq GPUTextureAspect
derive instance ordGPUTextureAspect :: Ord GPUTextureAspect
