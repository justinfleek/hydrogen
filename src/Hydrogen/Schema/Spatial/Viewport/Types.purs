-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // viewport // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for viewport tensor representation.
-- |
-- | ## Design Philosophy
-- |
-- | A viewport is not a rectangle of pixels. It's a **tensor computation target**:
-- |
-- | ```
-- | ViewportTensor
-- |   { pixelShape: [1, 4, 1080, 1920]      -- What the display shows
-- |   , latentShape: [1, 4, 135, 240]       -- What we compute (8× downsample)
-- |   , physicalExtent: meters 0.53 × 0.30  -- Physical size (optional)
-- |   }
-- | ```
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale with diffusion rendering:
-- | - Same latent shape can render to any physical size
-- | - 20ft LED wall and smartwatch use same tensor computation
-- | - Resolution independence is built-in

module Hydrogen.Schema.Spatial.Viewport.Types
  ( -- * Physical Extent
    PhysicalExtent(PhysicalExtent)
  , physicalExtent
  , extentFromInches
  , extentFromMeters
  , extentFromFeet
  , unwrapExtent
  
  -- * Color Space  
  , ColorSpace(SRGB, DisplayP3, AdobeRGB, Rec2020, LinearRGB)
  
  -- * Memory Layout
  , MemoryLayout(NCHW, NHWC, CHWN)
  
  -- * Viewport Tensor
  , ViewportTensor(ViewportTensor)
  , unwrapViewport
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (*)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.Shape (Shape)
import Hydrogen.Schema.Dimension.Device (DevicePixelRatio)
import Hydrogen.Schema.Dimension.Temporal (FrameRate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // physical extent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physical extent in meters.
-- |
-- | We use meters as the canonical unit for physical dimensions.
-- | Conversion from inches, feet, etc. happens at construction.
newtype PhysicalExtent = PhysicalExtent
  { widthMeters :: Number
  , heightMeters :: Number
  }

derive instance eqPhysicalExtent :: Eq PhysicalExtent

instance showPhysicalExtent :: Show PhysicalExtent where
  show (PhysicalExtent e) = 
    show e.widthMeters <> "m × " <> show e.heightMeters <> "m"

-- | Unwrap physical extent to access fields.
unwrapExtent :: PhysicalExtent -> { widthMeters :: Number, heightMeters :: Number }
unwrapExtent (PhysicalExtent e) = e

-- | Create physical extent from meters
physicalExtent :: Number -> Number -> PhysicalExtent
physicalExtent w h = PhysicalExtent { widthMeters: w, heightMeters: h }

-- | Create physical extent from inches
extentFromInches :: Number -> Number -> PhysicalExtent
extentFromInches wInches hInches = PhysicalExtent
  { widthMeters: wInches * 0.0254
  , heightMeters: hInches * 0.0254
  }

-- | Create physical extent from meters
extentFromMeters :: Number -> Number -> PhysicalExtent
extentFromMeters = physicalExtent

-- | Create physical extent from feet
extentFromFeet :: Number -> Number -> PhysicalExtent
extentFromFeet wFeet hFeet = PhysicalExtent
  { widthMeters: wFeet * 0.3048
  , heightMeters: hFeet * 0.3048
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // color space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color space for the viewport.
-- |
-- | Determines how color values are interpreted and displayed.
data ColorSpace
  = SRGB          -- ^ Standard RGB (web, most monitors)
  | DisplayP3     -- ^ Apple Display P3 (wider gamut)
  | AdobeRGB      -- ^ Adobe RGB (print workflows)
  | Rec2020       -- ^ ITU-R BT.2020 (HDR video)
  | LinearRGB     -- ^ Linear RGB (GPU computation)

derive instance eqColorSpace :: Eq ColorSpace
derive instance ordColorSpace :: Ord ColorSpace

instance showColorSpace :: Show ColorSpace where
  show SRGB = "sRGB"
  show DisplayP3 = "Display P3"
  show AdobeRGB = "Adobe RGB"
  show Rec2020 = "Rec.2020"
  show LinearRGB = "Linear RGB"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // memory layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Memory layout for tensor data.
-- |
-- | Affects GPU kernel dispatch and cache efficiency.
data MemoryLayout
  = NCHW    -- ^ Batch, Channels, Height, Width (PyTorch default)
  | NHWC    -- ^ Batch, Height, Width, Channels (TensorFlow default)
  | CHWN    -- ^ Channels, Height, Width, Batch (some NVIDIA optimizations)

derive instance eqMemoryLayout :: Eq MemoryLayout
derive instance ordMemoryLayout :: Ord MemoryLayout

instance showMemoryLayout :: Show MemoryLayout where
  show NCHW = "NCHW"
  show NHWC = "NHWC"
  show CHWN = "CHWN"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport tensor
-- ═════════════════════════════════════════════════════════════════════════════

-- | A viewport as a tensor computation target.
-- |
-- | This is the fundamental abstraction for resolution-independent rendering.
-- | The pixelShape is what the display shows; the latentShape is what we compute.
newtype ViewportTensor = ViewportTensor
  { -- | Pixel-space shape: [batch, channels, height, width]
    -- | This is what the display hardware receives.
    pixelShape :: Shape
    
    -- | Latent-space shape: [batch, latent_channels, h/factor, w/factor]
    -- | This is what diffusion/compute operates on.
  , latentShape :: Shape
  
    -- | Physical extent (optional)
    -- | For DPI-aware rendering and accessibility.
  , physicalExtent :: Maybe PhysicalExtent
  
    -- | Device pixel ratio (CSS pixels to device pixels)
    -- | Standard: 1.0, Retina: 2.0, Retina HD: 3.0
  , devicePixelRatio :: DevicePixelRatio
  
    -- | Color space for output
  , colorSpace :: ColorSpace
  
    -- | Target frame rate
  , frameRate :: FrameRate
  
    -- | Memory layout for tensor data
  , memoryLayout :: MemoryLayout
  
    -- | Latent downsample factor (typically 8 for SD, 4 for some models)
  , downsampleFactor :: Int
  }

derive instance eqViewportTensor :: Eq ViewportTensor

instance showViewportTensor :: Show ViewportTensor where
  show (ViewportTensor v) = 
    "(Viewport pixel:" <> show v.pixelShape 
      <> " latent:" <> show v.latentShape
      <> " " <> show v.colorSpace
      <> physicalStr
      <> ")"
    where
      physicalStr = case v.physicalExtent of
        Nothing -> ""
        Just ext -> " physical:" <> show ext

-- | Unwrap viewport to access fields.
unwrapViewport 
  :: ViewportTensor 
  -> { pixelShape :: Shape
     , latentShape :: Shape
     , physicalExtent :: Maybe PhysicalExtent
     , devicePixelRatio :: DevicePixelRatio
     , colorSpace :: ColorSpace
     , frameRate :: FrameRate
     , memoryLayout :: MemoryLayout
     , downsampleFactor :: Int
     }
unwrapViewport (ViewportTensor v) = v
