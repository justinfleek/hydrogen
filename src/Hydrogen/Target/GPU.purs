-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // target // gpu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Target Adapter — Unified rendering interface with automatic fallback.
-- |
-- | ## Design Philosophy
-- |
-- | Provides a single API that works across GPU backends:
-- |
-- | ```
-- | WebGPU (preferred, 100K+ particles)
-- |    ↓ fallback
-- | WebGL2 (wide support, 10K+ particles)
-- |    ↓ fallback
-- | Canvas2D (universal, 1K particles)
-- | ```
-- |
-- | ## Architecture
-- |
-- | Wraps Hydrogen.GPU.WebGPU.Device with:
-- | - Automatic capability detection
-- | - Backend fallback chain
-- | - Unified render/clear/dispose API
-- |
-- | ## Grade
-- |
-- | All operations are GPU-graded (require GPU effect permission).
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.GPU.WebGPU.Device
-- | - Hydrogen.GPU.DrawCommand.Types

module Hydrogen.Target.GPU
  ( -- * Backend Detection
    Backend(..)
  , detectCapabilities
  , Capabilities
  
  -- * Renderer
  , Renderer
  , createRenderer
  , dispose
  , getBackend
  
  -- * Rendering
  , render
  , clear
  
  -- * Info
  , GPUInfo
  , getGPUInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , Unit
  , bind
  , discard
  , map
  , pure
  , show
  , unit
  , ($)
  , (<>)
  , (>>=)
  )

import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Aff (Aff, attempt, makeAff)
import Effect.Class (liftEffect)

import Foreign (Foreign)

import Hydrogen.GPU.WebGPU.Device as WebGPU
import Hydrogen.GPU.DrawCommand.Types (DrawCommand)
import Hydrogen.GPU.WebGPU.Types 
  ( GPUAdapterDescriptor
  , GPUCanvasAlphaMode(AlphaOpaque)
  , GPUCanvasConfiguration
  , GPUTextureFormat(BGRA8Unorm)
  , GPUTextureUsage(RenderAttachment)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // default configs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default adapter descriptor (no power preference, no fallback).
defaultAdapterDescriptor :: GPUAdapterDescriptor
defaultAdapterDescriptor =
  { powerPreference: Nothing
  , forceFallbackAdapter: false
  }

-- | Default device descriptor (no required features).
defaultDeviceDescriptor :: { requiredFeatures :: Array String, label :: Maybe String }
defaultDeviceDescriptor =
  { requiredFeatures: []
  , label: Nothing
  }

-- | Default canvas configuration (BGRA8 format, opaque alpha).
defaultCanvasConfig :: GPUCanvasConfiguration
defaultCanvasConfig =
  { format: BGRA8Unorm
  , usage: [ RenderAttachment ]
  , viewFormats: []
  , colorSpace: "srgb"
  , alphaMode: AlphaOpaque
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // backend
-- ═════════════════════════════════════════════════════════════════════════════

-- | Available GPU backends in preference order.
data Backend
  = WebGPU      -- ^ Modern WebGPU API (best performance)
  | WebGL2      -- ^ WebGL 2.0 (wide compatibility)
  | Canvas2D    -- ^ Canvas 2D fallback (universal)

derive instance eqBackend :: Eq Backend

instance showBackend :: Show Backend where
  show WebGPU = "WebGPU"
  show WebGL2 = "WebGL2"
  show Canvas2D = "Canvas2D"

-- | GPU capabilities detected at runtime.
type Capabilities =
  { webgpu :: Boolean      -- ^ WebGPU supported
  , webgl2 :: Boolean      -- ^ WebGL2 supported
  , canvas2d :: Boolean    -- ^ Canvas2D supported (always true)
  , maxTextureSize :: Int  -- ^ Maximum texture dimension
  , maxParticles :: Int    -- ^ Recommended particle limit
  , bestBackend :: Backend -- ^ Recommended backend based on capabilities
  }

-- | Detect available GPU capabilities.
-- |
-- | Checks browser support for each backend and returns
-- | capability information for runtime decisions.
detectCapabilities :: Effect Capabilities
detectCapabilities = do
  webgpuSupported <- WebGPU.isWebGPUSupported
  -- WebGL2 and Canvas2D detection would need additional FFI
  -- For now, assume WebGL2 available if not WebGPU, Canvas2D always
  let best = if webgpuSupported then WebGPU else WebGL2
  pure
    { webgpu: webgpuSupported
    , webgl2: true           -- Assume available (actual detection requires FFI)
    , canvas2d: true         -- Always available in browsers
    , maxTextureSize: if webgpuSupported then 8192 else 4096
    , maxParticles: if webgpuSupported then 100000 else 10000
    , bestBackend: best
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // renderer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opaque renderer handle.
-- |
-- | Wraps the underlying GPU context (WebGPU device, WebGL context, etc.)
-- | and provides a unified interface for rendering.
type Renderer =
  { backend :: Backend
  , canvasId :: String
  , device :: Maybe WebGPU.GPUDevice
  , context :: Maybe WebGPU.GPUCanvasContext
  , queue :: Maybe WebGPU.GPUQueue
  }

-- | Create a renderer attached to a canvas element.
-- |
-- | The canvas element must be provided as a Foreign value (from DOM).
-- | Attempts backends in order: WebGPU → WebGL2 → Canvas2D
-- | Returns Left with error message on failure.
-- |
-- | The canvasId is stored for debugging/logging only.
createRenderer :: Foreign -> String -> Aff (Either String Renderer)
createRenderer canvas canvasId = do
  caps <- liftEffect detectCapabilities
  
  if caps.webgpu
    then createWebGPURenderer canvas canvasId
    else if caps.webgl2
      then createWebGL2Renderer canvas canvasId
      else createCanvas2DRenderer canvas canvasId

-- | Create WebGPU-backed renderer.
createWebGPURenderer :: Foreign -> String -> Aff (Either String Renderer)
createWebGPURenderer canvas canvasId = do
  -- Request adapter
  adapterResult <- WebGPU.requestAdapter defaultAdapterDescriptor
  case adapterResult of
    Left err -> pure $ Left $ "WebGPU adapter request failed: " <> show err
    Right adapter -> do
      -- Request device
      deviceResult <- WebGPU.requestDevice adapter defaultDeviceDescriptor
      case deviceResult of
        Left err -> pure $ Left $ "WebGPU device request failed: " <> show err
        Right device -> do
          -- Configure canvas
          contextResult <- liftEffect $ WebGPU.configureCanvas device canvas defaultCanvasConfig
          case contextResult of
            Left err -> pure $ Left $ "Canvas configuration failed: " <> show err
            Right context -> do
                  queue <- liftEffect $ WebGPU.getQueue device
                  pure $ Right
                    { backend: WebGPU
                    , canvasId: canvasId
                    , device: Just device
                    , context: Just context
                    , queue: Just queue
                    }

-- | Create WebGL2-backed renderer.
-- |
-- | WebGL2 backend not yet implemented. Returns stub renderer.
createWebGL2Renderer :: Foreign -> String -> Aff (Either String Renderer)
createWebGL2Renderer _canvas canvasId = do
  pure $ Right
    { backend: WebGL2
    , canvasId: canvasId
    , device: Nothing
    , context: Nothing
    , queue: Nothing
    }

-- | Create Canvas2D-backed renderer.
-- |
-- | Canvas2D backend not yet implemented. Returns stub renderer.
createCanvas2DRenderer :: Foreign -> String -> Aff (Either String Renderer)
createCanvas2DRenderer _canvas canvasId = do
  pure $ Right
    { backend: Canvas2D
    , canvasId: canvasId
    , device: Nothing
    , context: Nothing
    , queue: Nothing
    }

-- | Get the active backend for a renderer.
getBackend :: Renderer -> Backend
getBackend r = r.backend

-- | Dispose of renderer resources.
dispose :: Renderer -> Effect Unit
dispose _renderer = do
  -- TODO: Cleanup GPU resources
  pure unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an array of draw commands.
-- |
-- | Dispatches to the appropriate backend based on renderer type.
render :: forall msg. Renderer -> Array (DrawCommand msg) -> Effect Unit
render renderer commands = case renderer.backend of
  WebGPU -> renderWebGPU renderer commands
  WebGL2 -> renderWebGL2 renderer commands
  Canvas2D -> renderCanvas2D renderer commands

-- | WebGPU render implementation.
renderWebGPU :: forall msg. Renderer -> Array (DrawCommand msg) -> Effect Unit
renderWebGPU _renderer _commands = do
  -- TODO: Implement WebGPU rendering
  -- 1. Create command encoder
  -- 2. Begin render pass
  -- 3. Process each DrawCommand
  -- 4. End render pass
  -- 5. Submit to queue
  pure unit

-- | WebGL2 render implementation (stub).
renderWebGL2 :: forall msg. Renderer -> Array (DrawCommand msg) -> Effect Unit
renderWebGL2 _renderer _commands = do
  -- TODO: Implement WebGL2 rendering
  pure unit

-- | Canvas2D render implementation (stub).
renderCanvas2D :: forall msg. Renderer -> Array (DrawCommand msg) -> Effect Unit
renderCanvas2D _renderer _commands = do
  -- TODO: Implement Canvas2D rendering
  pure unit

-- | Clear color type (RGBA 0-1).
type ClearColor =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- | Clear the canvas with a color.
clear :: Renderer -> ClearColor -> Effect Unit
clear renderer color = case renderer.backend of
  WebGPU -> clearWebGPU renderer color
  WebGL2 -> clearWebGL2 renderer color
  Canvas2D -> clearCanvas2D renderer color

-- | WebGPU clear implementation.
clearWebGPU :: Renderer -> ClearColor -> Effect Unit
clearWebGPU _renderer _color = do
  -- TODO: Implement WebGPU clear
  pure unit

-- | WebGL2 clear implementation (stub).
clearWebGL2 :: Renderer -> ClearColor -> Effect Unit
clearWebGL2 _renderer _color = do
  -- TODO: Implement WebGL2 clear
  pure unit

-- | Canvas2D clear implementation (stub).
clearCanvas2D :: Renderer -> ClearColor -> Effect Unit
clearCanvas2D _renderer _color = do
  -- TODO: Implement Canvas2D clear
  pure unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // info
-- ═════════════════════════════════════════════════════════════════════════════

-- | GPU information for debugging and telemetry.
-- |
-- | Provides details about the active GPU backend, useful for:
-- | - Performance monitoring
-- | - Bug reports
-- | - Adaptive quality settings
type GPUInfo =
  { backend :: Backend          -- ^ Active rendering backend
  , capabilities :: Capabilities -- ^ Detected GPU capabilities
  , vendor :: String            -- ^ GPU vendor (if available)
  , renderer :: String          -- ^ GPU renderer string (if available)
  , maxTextureSize :: Int       -- ^ Maximum texture dimension
  , supportsCompute :: Boolean  -- ^ Compute shader support
  }

-- | Get GPU information from a renderer.
-- |
-- | Returns details about the active backend and capabilities.
getGPUInfo :: Renderer -> Effect GPUInfo
getGPUInfo r = do
  caps <- detectCapabilities
  pure
    { backend: r.backend
    , capabilities: caps
    , vendor: "Unknown"        -- Would need WebGPU adapter info
    , renderer: "Unknown"      -- Would need WebGPU adapter info
    , maxTextureSize: caps.maxTextureSize
    , supportsCompute: caps.webgpu  -- Only WebGPU has compute shaders
    }
