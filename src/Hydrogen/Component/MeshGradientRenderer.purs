-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // mesh gradient renderer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MeshGradientRenderer component
-- |
-- | Renders mesh gradients as a simple preview using CSS gradients approximation.
-- | True mesh gradient rendering requires SVG or Canvas with FFI.
-- |
-- | This component provides a fallback visualization by sampling the mesh
-- | at the 4 corners and creating a rough approximation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.MeshGradientRenderer as MeshRenderer
-- | import Hydrogen.Schema.Color.Gradient (meshGradient)
-- | import Hydrogen.Schema.Color.RGB (rgb)
-- |
-- | MeshRenderer.meshGradientPreview
-- |   [ MeshRenderer.mesh (meshGradient
-- |       (rgb 255 0 0)   -- top left
-- |       (rgb 0 255 0)   -- top right
-- |       (rgb 0 0 255)   -- bottom left
-- |       (rgb 255 255 0) -- bottom right
-- |     )
-- |   ]
-- | ```
-- |
-- | For production use, implement proper mesh rendering with:
-- | - SVG with gradient meshes (requires halogen-svg package)
-- | - Canvas 2D with FFI for pixel manipulation
-- | - WebGL for GPU-accelerated rendering

module Hydrogen.Component.MeshGradientRenderer
  ( -- * Component
    meshGradientPreview
    -- * Props
  , MeshPreviewProps
  , MeshPreviewProp
  , defaultProps
    -- * Prop Builders
  , mesh
  , width
  , height
  , className
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.Schema.Color.Gradient (MeshGradient, meshGradient, sampleMeshAt)
import Hydrogen.Schema.Color.RGB (RGB, rgb, rgbToLegacyCss)
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | MeshPreview properties
type MeshPreviewProps i =
  { gradient :: MeshGradient
  , width :: Int
  , height :: Int
  , className :: String
  }

-- | Property modifier
type MeshPreviewProp i = MeshPreviewProps i -> MeshPreviewProps i

-- | Default mesh preview properties
defaultProps :: forall i. MeshPreviewProps i
defaultProps =
  { gradient: meshGradient
      (rgb 255 0 0)
      (rgb 0 255 0)
      (rgb 0 0 255)
      (rgb 255 255 0)
  , width: 400
  , height: 300
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set mesh gradient
mesh :: forall i. MeshGradient -> MeshPreviewProp i
mesh g props = props { gradient = g }

-- | Set width in pixels
width :: forall i. Int -> MeshPreviewProp i
width w props = props { width = w }

-- | Set height in pixels
height :: forall i. Int -> MeshPreviewProp i
height h props = props { height = h }

-- | Add custom class
className :: forall i. String -> MeshPreviewProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a simplified mesh gradient preview
-- | Shows the 4 corner colors with a note that true mesh rendering requires SVG/Canvas
meshGradientPreview :: forall w i. Array (MeshPreviewProp i) -> HH.HTML w i
meshGradientPreview propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Sample colors at corners
    topLeft = sampleMeshAt 0.0 0.0 props.gradient
    topRight = sampleMeshAt 1.0 0.0 props.gradient
    bottomLeft = sampleMeshAt 0.0 1.0 props.gradient
    bottomRight = sampleMeshAt 1.0 1.0 props.gradient
    center = sampleMeshAt 0.5 0.5 props.gradient
    
  in
    HH.div 
      [ cls [ "mesh-gradient-preview border border-white/20 rounded", props.className ]
      , HP.style ("width: " <> show props.width <> "px; height: " <> show props.height <> "px;")
      ]
      [ -- Corner swatches to show the gradient colors
        HH.div [ cls [ "grid grid-cols-3 grid-rows-3 h-full" ] ]
          [ renderSwatch topLeft
          , HH.div [] []
          , renderSwatch topRight
          , HH.div [] []
          , renderSwatch center
          , HH.div [] []
          , renderSwatch bottomLeft
          , HH.div [] []
          , renderSwatch bottomRight
          ]
        
        -- Note about true rendering
        , HH.div 
            [ cls [ "absolute inset-0 flex items-center justify-center bg-black/50 text-white text-sm p-4 text-center" ] ]
            [ HH.text "Mesh gradient preview. Full rendering requires SVG or Canvas." ]
      ]

-- | Render a color swatch
renderSwatch :: forall w i. RGB -> HH.HTML w i
renderSwatch color =
  HH.div
    [ HP.style ("background-color: " <> rgbToLegacyCss color)
    , cls [ "w-full h-full" ]
    ]
    []
