-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // compositor // materiallayer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MaterialLayer — Diffusion Surface with 8px Grid Alignment
-- |
-- | ## Design Philosophy
-- |
-- | The material layer is the background surface of a viewport. It is
-- | **always aligned to an 8px grid** because diffusion models operate on
-- | 8×8 tile boundaries (the latent space constraint).
-- |
-- | On pinch zoom: the material layer snaps to the nearest 8px boundary
-- | and scales the texture, while the shape layer above clips pixel-perfect.

module Hydrogen.Compositor.MaterialLayer
  ( -- * MaterialLayer Type
    MaterialLayer(MaterialLayer)
  , materialLayer
  , defaultMaterialLayer
  
  -- * MaterialLayer Queries
  , getSource
  , getOpacity
  , getWidth
  , getHeight
  , getAlignment
  , isMaterialVisible
  , unwrapMaterialLayer
  
  -- * MaterialLayer Operations
  , setSource
  , setOpacity
  , resize
  , resizeSnapped
  , setAlignment
  , setMaterialVisible
  , toggleMaterialVisible
  
  -- * Material Source
  , MaterialSource
      ( SolidColor
      , ImageSource
      , VideoSource
      , SVGSource
      , ShaderSource
      , DiffusionSource
      , NoiseSource
      )
  
  -- * Grid Alignment
  , GridAlignment(GridAlignment)
  , defaultGridAlignment
  , snapToGrid
  
  -- * Diffusion Settings
  , DiffusionSettings(DiffusionSettings)
  , defaultDiffusionSettings
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude 
  ( class Eq
  , class Show
  , show
  , max
  , min
  , (*)
  , (/)
  , (<>)
  )

import Data.Int (floor, toNumber)

-- Schema color type (bounded Channel atoms, Opacity atom)
import Hydrogen.Schema.Color.RGB (RGBA, rgba)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid alignment configuration for material layers.
-- |
-- | The tile size determines the grid boundary. Default is 8px for
-- | standard diffusion models (SD 1.5, SDXL). Some models use 64px.
newtype GridAlignment = GridAlignment
  { tileSize :: Int        -- ^ Grid tile size in pixels (8, 16, 32, 64)
  , snapOnScale :: Boolean -- ^ Whether to snap to grid during scale operations
  }

derive instance eqGridAlignment :: Eq GridAlignment

instance showGridAlignment :: Show GridAlignment where
  show (GridAlignment g) = "GridAlignment { tile: " <> show g.tileSize <> "px }"

-- | Default grid alignment — 8px tiles, snap on scale
defaultGridAlignment :: GridAlignment
defaultGridAlignment = GridAlignment
  { tileSize: 8
  , snapOnScale: true
  }

-- | Snap a pixel value to the nearest grid boundary.
-- |
-- | ```purescript
-- | snapToGrid (GridAlignment { tileSize: 8, snapOnScale: true }) 123.0
-- | -- Returns 120.0 (nearest multiple of 8)
-- | ```
snapToGrid :: GridAlignment -> Number -> Number
snapToGrid (GridAlignment g) value =
  let 
    tile = toNumber g.tileSize
    snapped = toNumber (floor (value / tile)) * tile
  in snapped

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // diffusion settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diffusion model settings for generative material surfaces.
-- |
-- | When a material layer uses a diffusion model as its source, these
-- | settings control the generation parameters.
newtype DiffusionSettings = DiffusionSettings
  { -- | Number of inference steps (1-150, higher = better quality, slower)
    steps :: Int
    
    -- | Classifier-free guidance scale (1.0-30.0, higher = more prompt adherence)
  , cfgScale :: Number
  
    -- | Denoising strength for img2img (0.0-1.0)
  , denoisingStrength :: Number
  
    -- | Random seed for reproducibility (Nothing = random)
  , seed :: Int
  
    -- | Whether to use tiled generation for seamless textures
  , tiledGeneration :: Boolean
  }

derive instance eqDiffusionSettings :: Eq DiffusionSettings

instance showDiffusionSettings :: Show DiffusionSettings where
  show (DiffusionSettings d) = 
    "DiffusionSettings { steps: " <> show d.steps 
      <> ", cfg: " <> show d.cfgScale <> " }"

-- | Default diffusion settings — balanced quality/speed
defaultDiffusionSettings :: DiffusionSettings
defaultDiffusionSettings = DiffusionSettings
  { steps: 20
  , cfgScale: 7.5
  , denoisingStrength: 0.75
  , seed: 42
  , tiledGeneration: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // material source
-- ═════════════════════════════════════════════════════════════════════════════

-- | The source content for a material layer.
-- |
-- | A material layer can display many types of content, all subject to
-- | the same 8px grid alignment constraint.
-- |
-- | All color values use Schema RGBA (bounded Channel atoms, Opacity atom).
data MaterialSource
  = SolidColor RGBA
      -- ^ Solid color (Schema RGBA: r/g/b 0-255, alpha 0-100%)
  | ImageSource String
      -- ^ Image from URL or data URI
  | VideoSource String
      -- ^ Video from URL
  | SVGSource String
      -- ^ Inline SVG content
  | ShaderSource String
      -- ^ WebGL shader (GLSL fragment shader source)
  | DiffusionSource String DiffusionSettings
      -- ^ AI-generated from prompt with settings
  | NoiseSource Int Number
      -- ^ Procedural noise (seed, frequency)

derive instance eqMaterialSource :: Eq MaterialSource

instance showMaterialSource :: Show MaterialSource where
  show (SolidColor color) = "SolidColor(" <> show color <> ")"
  show (ImageSource url) = "ImageSource(" <> url <> ")"
  show (VideoSource url) = "VideoSource(" <> url <> ")"
  show (SVGSource _) = "SVGSource(...)"
  show (ShaderSource _) = "ShaderSource(...)"
  show (DiffusionSource prompt _) = "DiffusionSource(" <> prompt <> ")"
  show (NoiseSource seed freq) = "NoiseSource(" <> show seed <> ", " <> show freq <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // material layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | The material layer — background surface of a viewport.
-- |
-- | This layer is always aligned to an 8px grid. During scale operations,
-- | dimensions snap to grid boundaries while the shape layer above clips
-- | at exact pixels.
newtype MaterialLayer = MaterialLayer
  { -- | The content source for this material
    source :: MaterialSource
    
    -- | Grid alignment configuration
  , alignment :: GridAlignment
  
    -- | Width in pixels (will be snapped to grid)
  , width :: Number
  
    -- | Height in pixels (will be snapped to grid)
  , height :: Number
  
    -- | Opacity (0.0-1.0)
  , opacity :: Number
  
    -- | Whether this layer is visible
  , visible :: Boolean
  }

derive instance eqMaterialLayer :: Eq MaterialLayer

instance showMaterialLayer :: Show MaterialLayer where
  show (MaterialLayer m) = 
    "MaterialLayer { " <> show m.source 
      <> ", " <> show m.width <> "×" <> show m.height <> " }"

-- | Create a material layer with a specific source
materialLayer :: MaterialSource -> MaterialLayer
materialLayer src = MaterialLayer
  { source: src
  , alignment: defaultGridAlignment
  , width: 256.0
  , height: 256.0
  , opacity: 1.0
  , visible: true
  }

-- | Default material layer — solid gray (50% gray, fully opaque)
defaultMaterialLayer :: MaterialLayer
defaultMaterialLayer = materialLayer (SolidColor (rgba 128 128 128 100))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // materiallayer queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the material source
getSource :: MaterialLayer -> MaterialSource
getSource (MaterialLayer m) = m.source

-- | Extract the opacity (0.0-1.0)
getOpacity :: MaterialLayer -> Number
getOpacity (MaterialLayer m) = m.opacity

-- | Extract the width in pixels
getWidth :: MaterialLayer -> Number
getWidth (MaterialLayer m) = m.width

-- | Extract the height in pixels
getHeight :: MaterialLayer -> Number
getHeight (MaterialLayer m) = m.height

-- | Extract the grid alignment configuration
getAlignment :: MaterialLayer -> GridAlignment
getAlignment (MaterialLayer m) = m.alignment

-- | Check if the material layer is visible
isMaterialVisible :: MaterialLayer -> Boolean
isMaterialVisible (MaterialLayer m) = m.visible

-- | Unwrap to access the full record
unwrapMaterialLayer 
  :: MaterialLayer 
  -> { source :: MaterialSource
     , alignment :: GridAlignment
     , width :: Number
     , height :: Number
     , opacity :: Number
     , visible :: Boolean
     }
unwrapMaterialLayer (MaterialLayer m) = m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // materiallayer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the material source
setSource :: MaterialSource -> MaterialLayer -> MaterialLayer
setSource src (MaterialLayer m) = MaterialLayer (m { source = src })

-- | Set the opacity, clamped to [0.0, 1.0]
-- |
-- | Opacity uses unit interval (0.0 = transparent, 1.0 = opaque)
-- | This is clamped to prevent invalid states.
setOpacity :: Number -> MaterialLayer -> MaterialLayer
setOpacity o (MaterialLayer m) = 
  MaterialLayer (m { opacity = clampUnit o })
  where
  clampUnit n = max 0.0 (min 1.0 n)

-- | Resize the layer (does NOT snap to grid)
-- |
-- | Use `resizeSnapped` if you want grid-aligned dimensions.
resize :: Number -> Number -> MaterialLayer -> MaterialLayer
resize w h (MaterialLayer m) = 
  MaterialLayer (m { width = max 0.0 w, height = max 0.0 h })

-- | Resize the layer, snapping dimensions to grid alignment
-- |
-- | Dimensions are snapped to the nearest grid boundary based on
-- | the layer's alignment configuration. This is what you want when
-- | working with diffusion model surfaces.
resizeSnapped :: Number -> Number -> MaterialLayer -> MaterialLayer
resizeSnapped w h (MaterialLayer m) = 
  MaterialLayer 
    (m { width = snapToGrid m.alignment (max 0.0 w)
       , height = snapToGrid m.alignment (max 0.0 h)
       })

-- | Set the grid alignment configuration
setAlignment :: GridAlignment -> MaterialLayer -> MaterialLayer
setAlignment a (MaterialLayer m) = MaterialLayer (m { alignment = a })

-- | Set material layer visibility
setMaterialVisible :: Boolean -> MaterialLayer -> MaterialLayer
setMaterialVisible v (MaterialLayer m) = MaterialLayer (m { visible = v })

-- | Toggle material layer visibility
toggleMaterialVisible :: MaterialLayer -> MaterialLayer
toggleMaterialVisible (MaterialLayer m) = MaterialLayer (m { visible = not m.visible })
  where
  not true = false
  not false = true
