-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // target // gpu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Target Adapter — Pure data rendering configuration.
-- |
-- | ## Design Philosophy
-- |
-- | Provides pure data types describing GPU rendering configuration.
-- | The actual GPU execution happens in the Haskell runtime, which
-- | interprets this pure data and executes against WebGPU.
-- |
-- | ```
-- | PureScript (pure data)
-- |    ↓ serialization
-- | Haskell Runtime
-- |    ↓ interpretation
-- | WebGPU API
-- | ```
-- |
-- | ## Architecture
-- |
-- | No FFI. No effects. Pure data structures that describe:
-- | - Backend preferences
-- | - Device configuration
-- | - Render commands
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.GPU.WebGPU.Device (pure data)
-- | - Hydrogen.GPU.DrawCommand.Types

module Hydrogen.Target.GPU
  ( -- * Backend Selection
    Backend(..)
  , Capabilities
  , defaultCapabilities
  
  -- * Renderer Configuration
  , RendererConfig
  , defaultRendererConfig
  , webgpuRendererConfig
  , webgl2RendererConfig
  , canvas2dRendererConfig
  
  -- * Render Requests (Pure Data)
  , RenderRequest(..)
  , ClearColor
  , ClearRequest
  , DrawRequest
  
  -- * Info
  , GPUInfo
  , defaultGPUInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.WebGPU.Device as Device
import Hydrogen.GPU.WebGPU.Types
  ( GPUCanvasAlphaMode(AlphaOpaque)
  , GPUTextureFormat(BGRA8Unorm)
  )
import Hydrogen.GPU.DrawCommand.Types (DrawCommand)

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

-- | GPU capabilities — pure data describing what's available.
-- |
-- | In the pure data model, capabilities are either:
-- | 1. Provided by the Haskell runtime after probing
-- | 2. Assumed based on target platform
-- |
-- | This type is serializable and can be transmitted between
-- | agents as pure data.
type Capabilities =
  { webgpu :: Boolean      -- ^ WebGPU supported
  , webgl2 :: Boolean      -- ^ WebGL2 supported
  , canvas2d :: Boolean    -- ^ Canvas2D supported (always true)
  , maxTextureSize :: Int  -- ^ Maximum texture dimension
  , maxParticles :: Int    -- ^ Recommended particle limit
  , bestBackend :: Backend -- ^ Recommended backend based on capabilities
  }

-- | Default capabilities assuming WebGPU is available.
-- |
-- | The Haskell runtime overrides this with actual detected values.
defaultCapabilities :: Capabilities
defaultCapabilities =
  { webgpu: true
  , webgl2: true
  , canvas2d: true
  , maxTextureSize: 8192
  , maxParticles: 100000
  , bestBackend: WebGPU
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // renderer configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Renderer configuration — pure data describing how to set up rendering.
-- |
-- | This replaces the old opaque Renderer type. Instead of holding
-- | FFI handles to GPU objects, it holds pure data that describes
-- | the desired configuration. The Haskell runtime interprets this.
type RendererConfig =
  { backend :: Backend
  , canvasId :: String
  , deviceConfig :: Device.GPUDeviceConfig
  , canvasConfig :: Device.GPUCanvasConfig
  , label :: Maybe String
  }

-- | Default renderer configuration using WebGPU.
defaultRendererConfig :: String -> RendererConfig
defaultRendererConfig canvasId =
  { backend: WebGPU
  , canvasId: canvasId
  , deviceConfig:
      { requiredFeatures: Device.emptyFeatureSet
      , requiredLimits: Device.defaultLimits
      , label: Just "hydrogen-device"
      }
  , canvasConfig:
      { format: BGRA8Unorm
      , alphaMode: AlphaOpaque
      , width: 800
      , height: 600
      }
  , label: Just "hydrogen-renderer"
  }

-- | WebGPU-specific renderer configuration.
webgpuRendererConfig :: String -> Int -> Int -> RendererConfig
webgpuRendererConfig canvasId width height =
  { backend: WebGPU
  , canvasId: canvasId
  , deviceConfig:
      { requiredFeatures: Device.emptyFeatureSet
      , requiredLimits: Device.defaultLimits
      , label: Just "hydrogen-webgpu-device"
      }
  , canvasConfig:
      { format: BGRA8Unorm
      , alphaMode: AlphaOpaque
      , width: width
      , height: height
      }
  , label: Just "hydrogen-webgpu-renderer"
  }

-- | WebGL2 fallback renderer configuration.
webgl2RendererConfig :: String -> Int -> Int -> RendererConfig
webgl2RendererConfig canvasId width height =
  { backend: WebGL2
  , canvasId: canvasId
  , deviceConfig:
      { requiredFeatures: Device.emptyFeatureSet
      , requiredLimits: Device.minLimits  -- Lower limits for WebGL2
      , label: Just "hydrogen-webgl2-device"
      }
  , canvasConfig:
      { format: BGRA8Unorm
      , alphaMode: AlphaOpaque
      , width: width
      , height: height
      }
  , label: Just "hydrogen-webgl2-renderer"
  }

-- | Canvas2D fallback renderer configuration.
canvas2dRendererConfig :: String -> Int -> Int -> RendererConfig
canvas2dRendererConfig canvasId width height =
  { backend: Canvas2D
  , canvasId: canvasId
  , deviceConfig:
      { requiredFeatures: Device.emptyFeatureSet
      , requiredLimits: Device.minLimits  -- Minimal limits for Canvas2D
      , label: Just "hydrogen-canvas2d-device"
      }
  , canvasConfig:
      { format: BGRA8Unorm
      , alphaMode: AlphaOpaque
      , width: width
      , height: height
      }
  , label: Just "hydrogen-canvas2d-renderer"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // render requests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear color type (RGBA 0-1).
type ClearColor =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- | A request to clear the canvas.
type ClearRequest =
  { color :: ClearColor
  }

-- | A request to draw commands.
type DrawRequest msg =
  { commands :: Array (DrawCommand msg)
  }

-- | Render request — pure data describing what to render.
-- |
-- | The Haskell runtime interprets these requests and executes
-- | the appropriate GPU commands.
data RenderRequest msg
  = ClearCanvas ClearRequest
  | DrawCommands (DrawRequest msg)
  | ClearAndDraw ClearRequest (DrawRequest msg)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // info
-- ═════════════════════════════════════════════════════════════════════════════

-- | GPU information — pure data for debugging and telemetry.
type GPUInfo =
  { backend :: Backend          -- ^ Active rendering backend
  , capabilities :: Capabilities -- ^ GPU capabilities
  , vendor :: String            -- ^ GPU vendor (if available)
  , renderer :: String          -- ^ GPU renderer string (if available)
  , maxTextureSize :: Int       -- ^ Maximum texture dimension
  , supportsCompute :: Boolean  -- ^ Compute shader support
  }

-- | Default GPU info assuming WebGPU.
-- |
-- | The Haskell runtime populates actual values.
defaultGPUInfo :: GPUInfo
defaultGPUInfo =
  { backend: WebGPU
  , capabilities: defaultCapabilities
  , vendor: "Unknown"
  , renderer: "Unknown"
  , maxTextureSize: 8192
  , supportsCompute: true
  }
