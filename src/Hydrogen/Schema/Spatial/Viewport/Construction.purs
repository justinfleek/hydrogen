-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // viewport // construction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport construction functions.
-- |
-- | Provides multiple ways to construct ViewportTensor values:
-- | - From explicit shapes
-- | - From pixel dimensions
-- | - From physical dimensions and PPI
-- |
-- | Also provides setters for modifying viewport properties.

module Hydrogen.Schema.Spatial.Viewport.Construction
  ( -- * Construction
    viewport
  , viewportFromPixels
  , viewportFromPhysical
  
  -- * Common Viewports
  , viewport1080p
  , viewport4K
  , viewportMobile
  , viewportWatch
  
  -- * Setters
  , setPhysicalExtent
  , setDevicePixelRatio
  , setColorSpace
  , setFrameRate
  , setMemoryLayout
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (/)
  , (*)
  )

import Data.Int (floor)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.Shape (Shape)
import Hydrogen.Schema.Tensor.Shape (shape4d) as Shape
import Hydrogen.Schema.Tensor.Dimension (dim) as Dim
import Hydrogen.Schema.Dimension.Device (DevicePixelRatio, PixelsPerInch)
import Hydrogen.Schema.Dimension.Device (dpr, unwrapPpi) as Device
import Hydrogen.Schema.Dimension.Temporal (FrameRate)
import Hydrogen.Schema.Dimension.Temporal (fps60) as FPS

import Hydrogen.Schema.Spatial.Viewport.Types 
  ( ViewportTensor(ViewportTensor)
  , PhysicalExtent
  , ColorSpace(SRGB)
  , MemoryLayout(NCHW)
  , extentFromMeters
  , unwrapExtent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a viewport from explicit shapes.
viewport 
  :: Shape           -- ^ Pixel shape [batch, channels, height, width]
  -> Shape           -- ^ Latent shape [batch, latent_channels, h', w']
  -> ViewportTensor
viewport pShape lShape = ViewportTensor
  { pixelShape: pShape
  , latentShape: lShape
  , physicalExtent: Nothing
  , devicePixelRatio: Device.dpr 1.0
  , colorSpace: SRGB
  , frameRate: FPS.fps60
  , memoryLayout: NCHW
  , downsampleFactor: 8
  }

-- | Create a viewport from pixel dimensions with default latent downsample.
-- |
-- | Uses 8× downsample factor (standard for Stable Diffusion).
viewportFromPixels :: Int -> Int -> ViewportTensor
viewportFromPixels width height = 
  let
    pShape = Shape.shape4d (Dim.dim 1) (Dim.dim 4) (Dim.dim height) (Dim.dim width)
    lShape = Shape.shape4d (Dim.dim 1) (Dim.dim 4) (Dim.dim (height / 8)) (Dim.dim (width / 8))
  in
    viewport pShape lShape

-- | Create a viewport from physical dimensions and PPI.
-- |
-- | Calculates pixel dimensions from physical size and PPI.
viewportFromPhysical 
  :: PhysicalExtent 
  -> PixelsPerInch 
  -> ViewportTensor
viewportFromPhysical extent targetPPI =
  let
    e = unwrapExtent extent
    ppiVal = Device.unwrapPpi targetPPI
    widthInches = e.widthMeters / 0.0254
    heightInches = e.heightMeters / 0.0254
    width = floor (widthInches * ppiVal)
    height = floor (heightInches * ppiVal)
    vp = viewportFromPixels width height
  in
    setPhysicalExtent (Just extent) vp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common viewports
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1080p viewport (1920×1080)
viewport1080p :: ViewportTensor
viewport1080p = viewportFromPixels 1920 1080

-- | 4K viewport (3840×2160)
viewport4K :: ViewportTensor
viewport4K = viewportFromPixels 3840 2160

-- | Mobile viewport (390×844, iPhone 14 logical size)
viewportMobile :: ViewportTensor
viewportMobile = 
  let vp = viewportFromPixels 390 844
  in setDevicePixelRatio (Device.dpr 3.0) vp

-- | Watch viewport (368×448, Apple Watch)
viewportWatch :: ViewportTensor
viewportWatch =
  let 
    vp = viewportFromPixels 368 448
    extent = extentFromMeters 0.040 0.034  -- ~40mm × 34mm
  in setPhysicalExtent (Just extent) vp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set physical extent
setPhysicalExtent :: Maybe PhysicalExtent -> ViewportTensor -> ViewportTensor
setPhysicalExtent ext (ViewportTensor v) = ViewportTensor (v { physicalExtent = ext })

-- | Set device pixel ratio
setDevicePixelRatio :: DevicePixelRatio -> ViewportTensor -> ViewportTensor
setDevicePixelRatio dprVal (ViewportTensor v) = ViewportTensor (v { devicePixelRatio = dprVal })

-- | Set color space
setColorSpace :: ColorSpace -> ViewportTensor -> ViewportTensor
setColorSpace cs (ViewportTensor v) = ViewportTensor (v { colorSpace = cs })

-- | Set frame rate
setFrameRate :: FrameRate -> ViewportTensor -> ViewportTensor
setFrameRate fr (ViewportTensor v) = ViewportTensor (v { frameRate = fr })

-- | Set memory layout
setMemoryLayout :: MemoryLayout -> ViewportTensor -> ViewportTensor
setMemoryLayout ml (ViewportTensor v) = ViewportTensor (v { memoryLayout = ml })
