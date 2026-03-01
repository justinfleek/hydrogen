-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // webgpu // shader
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- WGSL shaders as pure PureScript strings.
--
-- Shaders are PURE DATA — deterministic, composable, auditable.
-- No runtime shader compilation from external files.
-- Same shader = same GPU behavior (always).
--
-- PROOF REFERENCE:
-- PBR BRDF mathematics: proofs/Hydrogen/Material/BRDF.lean
-- - fresnel_schlick
-- - ggx_distribution  
-- - smith_geometry
-- - cook_torrance
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- LEADER MODULE
--
-- Re-exports all shader submodules for unified access.
--
-- Submodules:
-- - Shader.Types       — WGSLSource type and combinators
-- - Shader.Basic       — Basic/unlit shaders
-- - Shader.PBR         — Physically Based Rendering shaders
-- - Shader.Shadow      — Shadow mapping shaders
-- - Shader.Pick        — GPU picking shaders
-- - Shader.Text        — SDF text shaders
-- - Shader.Skybox      — Skybox/environment shaders
-- - Shader.Wireframe   — Wireframe debug shaders
-- - Shader.PostProcess — Fullscreen/tonemapping shaders
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader
  ( -- WGSL Source type (from Types)
    module Hydrogen.GPU.WebGPU.Shader.Types
    -- Basic (unlit) shaders (from Basic)
  , module Hydrogen.GPU.WebGPU.Shader.Basic
    -- PBR shaders (from PBR)
  , module Hydrogen.GPU.WebGPU.Shader.PBR
    -- Shadow mapping shaders (from Shadow)
  , module Hydrogen.GPU.WebGPU.Shader.Shadow
    -- GPU picking shaders (from Pick)
  , module Hydrogen.GPU.WebGPU.Shader.Pick
    -- SDF text shaders (from Text)
  , module Hydrogen.GPU.WebGPU.Shader.Text
    -- Skybox shaders (from Skybox)
  , module Hydrogen.GPU.WebGPU.Shader.Skybox
    -- Wireframe shaders (from Wireframe)
  , module Hydrogen.GPU.WebGPU.Shader.Wireframe
    -- Fullscreen quad (post-processing) (from PostProcess)
  , module Hydrogen.GPU.WebGPU.Shader.PostProcess
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types
  ( WGSLSource(WGSLSource)
  , shaderSourceToString
  , combineShaderSource
  )

import Hydrogen.GPU.WebGPU.Shader.Basic
  ( basicVertexShader
  , basicFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.PBR
  ( pbrVertexShader
  , pbrFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.Shadow
  ( shadowVertexShader
  , shadowFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.Pick
  ( pickVertexShader
  , pickFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.Text
  ( sdfTextVertexShader
  , sdfTextFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.Skybox
  ( skyboxVertexShader
  , skyboxFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.Wireframe
  ( wireframeVertexShader
  , wireframeFragmentShader
  )

import Hydrogen.GPU.WebGPU.Shader.PostProcess
  ( fullscreenVertexShader
  , tonemapFragmentShader
  )
