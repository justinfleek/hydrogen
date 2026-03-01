-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // webgpu // types // buffer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU buffer types for WebGPU.
-- Buffers are the primary way to transfer data to/from the GPU.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.Buffer
  ( -- Buffer
    GPUBufferDescriptor
  , GPUBufferUsage(..)
  , GPUMapMode(..)
  , combineBufferUsage
  , combineMapMode
  ) where

import Prelude

import Data.Foldable (foldr)
import Data.Maybe (Maybe)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BUFFER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Buffer creation descriptor.
type GPUBufferDescriptor =
  { size :: Int
  , usage :: Array GPUBufferUsage
  , mappedAtCreation :: Boolean
  , label :: Maybe String
  }

-- | Buffer usage flags (combinable).
data GPUBufferUsage
  = MapRead
  | MapWrite
  | CopySrc
  | CopyDst
  | Index
  | Vertex
  | Uniform
  | Storage
  | Indirect
  | QueryResolve

derive instance eqGPUBufferUsage :: Eq GPUBufferUsage
derive instance ordGPUBufferUsage :: Ord GPUBufferUsage

-- | Combine buffer usage flags into a bitmask.
combineBufferUsage :: Array GPUBufferUsage -> Int
combineBufferUsage = foldr (\u acc -> acc + usageToInt u) 0
  where
  usageToInt :: GPUBufferUsage -> Int
  usageToInt = case _ of
    MapRead -> 1
    MapWrite -> 2
    CopySrc -> 4
    CopyDst -> 8
    Index -> 16
    Vertex -> 32
    Uniform -> 64
    Storage -> 128
    Indirect -> 256
    QueryResolve -> 512

-- | Buffer map modes.
data GPUMapMode
  = MapModeRead
  | MapModeWrite

derive instance eqGPUMapMode :: Eq GPUMapMode
derive instance ordGPUMapMode :: Ord GPUMapMode

-- | Combine map modes into a bitmask.
combineMapMode :: Array GPUMapMode -> Int
combineMapMode = foldr (\m acc -> acc + modeToInt m) 0
  where
  modeToInt :: GPUMapMode -> Int
  modeToInt = case _ of
    MapModeRead -> 1
    MapModeWrite -> 2
