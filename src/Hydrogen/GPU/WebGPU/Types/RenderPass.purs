-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // gpu // webgpu // types // renderpass
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU render pass and canvas types for WebGPU.
-- Render passes configure a single rendering operation.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.RenderPass
  ( -- Render Pass
    GPURenderPassDescriptor
  , GPURenderPassColorAttachment
  , GPURenderPassDepthStencilAttachment
  , GPULoadOp
      ( LoadOpLoad
      , LoadOpClear
      )
  , GPUStoreOp
      ( StoreOpStore
      , StoreOpDiscard
      )
    -- Canvas Configuration
  , GPUCanvasConfiguration
  , GPUCanvasAlphaMode
      ( AlphaOpaque
      , AlphaPremultiplied
      )
  ) where

import Prelude

import Data.Maybe (Maybe)

import Hydrogen.GPU.WebGPU.Types.Texture (GPUTextureFormat, GPUTextureUsage)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER PASS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render pass descriptor.
type GPURenderPassDescriptor =
  { colorAttachments :: Array GPURenderPassColorAttachment
  , depthStencilAttachment :: Maybe GPURenderPassDepthStencilAttachment
  , timestampWrites :: Maybe { querySet :: Int, beginningOfPassWriteIndex :: Int, endOfPassWriteIndex :: Int }
  , label :: Maybe String
  }

-- | Color attachment for render pass.
type GPURenderPassColorAttachment =
  { loadOp :: GPULoadOp
  , storeOp :: GPUStoreOp
  , clearValue :: { r :: Number, g :: Number, b :: Number, a :: Number }
  }

-- | Depth/stencil attachment for render pass.
type GPURenderPassDepthStencilAttachment =
  { depthLoadOp :: Maybe GPULoadOp
  , depthStoreOp :: Maybe GPUStoreOp
  , depthClearValue :: Number
  , depthReadOnly :: Boolean
  , stencilLoadOp :: Maybe GPULoadOp
  , stencilStoreOp :: Maybe GPUStoreOp
  , stencilClearValue :: Int
  , stencilReadOnly :: Boolean
  }

-- | Load operation.
data GPULoadOp
  = LoadOpLoad
  | LoadOpClear

derive instance eqGPULoadOp :: Eq GPULoadOp
derive instance ordGPULoadOp :: Ord GPULoadOp

-- | Store operation.
data GPUStoreOp
  = StoreOpStore
  | StoreOpDiscard

derive instance eqGPUStoreOp :: Eq GPUStoreOp
derive instance ordGPUStoreOp :: Ord GPUStoreOp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CANVAS CONFIGURATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas configuration.
type GPUCanvasConfiguration =
  { format :: GPUTextureFormat
  , usage :: Array GPUTextureUsage
  , viewFormats :: Array GPUTextureFormat
  , colorSpace :: String
  , alphaMode :: GPUCanvasAlphaMode
  }

-- | Canvas alpha mode.
data GPUCanvasAlphaMode
  = AlphaOpaque
  | AlphaPremultiplied

derive instance eqGPUCanvasAlphaMode :: Eq GPUCanvasAlphaMode
derive instance ordGPUCanvasAlphaMode :: Ord GPUCanvasAlphaMode
