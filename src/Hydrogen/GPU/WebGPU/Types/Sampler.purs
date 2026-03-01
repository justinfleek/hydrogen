-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // webgpu // types // sampler
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU sampler types for WebGPU.
-- Samplers define how textures are sampled in shaders.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.Sampler
  ( -- Sampler
    GPUSamplerDescriptor
  , GPUAddressMode(..)
  , GPUFilterMode(..)
  , GPUMipmapFilterMode(..)
  , GPUCompareFunction(..)
  ) where

import Prelude

import Data.Maybe (Maybe)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SAMPLER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sampler descriptor.
type GPUSamplerDescriptor =
  { addressModeU :: GPUAddressMode
  , addressModeV :: GPUAddressMode
  , addressModeW :: GPUAddressMode
  , magFilter :: GPUFilterMode
  , minFilter :: GPUFilterMode
  , mipmapFilter :: GPUMipmapFilterMode
  , lodMinClamp :: Number
  , lodMaxClamp :: Number
  , compare :: Maybe GPUCompareFunction
  , maxAnisotropy :: Int
  , label :: Maybe String
  }

-- | Texture address mode.
data GPUAddressMode
  = ClampToEdge
  | Repeat
  | MirrorRepeat

derive instance eqGPUAddressMode :: Eq GPUAddressMode
derive instance ordGPUAddressMode :: Ord GPUAddressMode

-- | Texture filter mode.
data GPUFilterMode
  = FilterNearest
  | FilterLinear

derive instance eqGPUFilterMode :: Eq GPUFilterMode
derive instance ordGPUFilterMode :: Ord GPUFilterMode

-- | Mipmap filter mode.
data GPUMipmapFilterMode
  = MipmapNearest
  | MipmapLinear

derive instance eqGPUMipmapFilterMode :: Eq GPUMipmapFilterMode
derive instance ordGPUMipmapFilterMode :: Ord GPUMipmapFilterMode

-- | Comparison function for depth/stencil operations.
data GPUCompareFunction
  = CompareNever
  | CompareLess
  | CompareEqual
  | CompareLessEqual
  | CompareGreater
  | CompareNotEqual
  | CompareGreaterEqual
  | CompareAlways

derive instance eqGPUCompareFunction :: Eq GPUCompareFunction
derive instance ordGPUCompareFunction :: Ord GPUCompareFunction
