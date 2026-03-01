-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // webgpu // types // shader
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU shader types for WebGPU.
-- Shaders are programs that run on the GPU.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.Shader
  ( -- Shader
    GPUShaderModuleDescriptor
  , WGSLSource(..)
  ) where

import Prelude

import Data.Maybe (Maybe)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SHADER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shader module descriptor.
type GPUShaderModuleDescriptor =
  { code :: WGSLSource
  , label :: Maybe String
  }

-- | WGSL source code (pure String wrapper for type safety).
newtype WGSLSource = WGSLSource String

derive instance eqWGSLSource :: Eq WGSLSource
derive instance ordWGSLSource :: Ord WGSLSource

instance showWGSLSource :: Show WGSLSource where
  show (WGSLSource s) = "(WGSLSource " <> show s <> ")"
