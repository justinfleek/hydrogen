-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // webgpu // shader // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- WGSL shader source type and combinators.
--
-- Pure data wrapper for type safety — shaders are deterministic, composable,
-- auditable strings that compile to GPU bytecode.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.Types
  ( WGSLSource(..)
  , shaderSourceToString
  , combineShaderSource
  ) where

import Prelude
  ( class Eq
  , class Semigroup
  , (<>)
  )

import Data.Foldable (foldl)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- WGSL SOURCE TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WGSL shader source code.
-- | Pure data wrapper for type safety.
newtype WGSLSource = WGSLSource String

derive instance eqWGSLSource :: Eq WGSLSource

instance semigroupWGSLSource :: Semigroup WGSLSource where
  append (WGSLSource a) (WGSLSource b) = WGSLSource (a <> "\n" <> b)

-- | Extract the raw WGSL string.
shaderSourceToString :: WGSLSource -> String
shaderSourceToString (WGSLSource s) = s

-- | Combine multiple shader source fragments.
combineShaderSource :: Array WGSLSource -> WGSLSource
combineShaderSource sources = foldl combineTwoSources emptySource sources
  where
    emptySource :: WGSLSource
    emptySource = WGSLSource ""
    
    combineTwoSources :: WGSLSource -> WGSLSource -> WGSLSource
    combineTwoSources (WGSLSource a) (WGSLSource b) = 
      case a of
        "" -> WGSLSource b
        _ -> WGSLSource (a <> "\n" <> b)
