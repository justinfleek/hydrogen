-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // compositor // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport — Bento Widget Container with Layer Stack
-- |
-- | ## Design Philosophy
-- |
-- | A Viewport is a bento-style widget container that can display anything:
-- | - Buttons, dashboards, world models
-- | - Games, simulations, point clouds
-- | - Shaders, videos, images, SVGs
-- |
-- | Each viewport has a layer stack:
-- | - ShapeLayer (top) — strokes, elevation, effects
-- | - MaterialLayer (middle) — diffusion surface, 8px aligned
-- | - ContentLayer (bottom) — the actual content

module Hydrogen.Compositor.Viewport
  ( -- * Viewport Type
    Viewport(Viewport)
  , viewport
  , defaultViewport
  
  -- * Viewport Identity (re-exported from Schema)
  , module ReExportViewportId
  
  -- * Viewport Queries
  , getId
  , getConfig
  , getMaterialLayer
  , getShapeLayer
  , getChildren
  , getTransform
  , isViewportVisible
  , childCount
  , unwrapViewport
  
  -- * Viewport Operations
  , setConfig
  , setMaterialLayer
  , setShapeLayer
  , setTransform
  , setViewportVisible
  , toggleViewportVisible
  , addChild
  , addChildren
  , removeChildAt
  , clearChildren
  , resizeViewport
  , moveViewport
  
  -- * Viewport Configuration
  , ViewportConfig(ViewportConfig)
  , defaultViewportConfig
  
  -- * Grid Snapping
  , SnapConfig(SnapConfig)
  , defaultSnapConfig
  , noSnap
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude 
  ( class Eq
  , class Show
  , show
  , max
  , (<>)
  , ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Compositor.MaterialLayer 
  ( MaterialLayer
  , defaultMaterialLayer
  ) as ML
import Hydrogen.Compositor.ShapeLayer 
  ( ShapeLayer
  , defaultShapeLayer
  ) as SL
import Hydrogen.Compositor.Transform (Transform, identityTransform)

-- Viewport identifier from Schema (deterministic, UUID5-compatible)
import Hydrogen.Schema.Reactive.Viewport.Types 
  ( ViewportId(ViewportId)
  , viewportIdFromString
  ) as ReExportViewportId
import Hydrogen.Schema.Reactive.Viewport.Types 
  ( ViewportId
  , viewportIdFromString
  ) as VPId


-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // snap configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid snap configuration for viewport positioning and sizing.
newtype SnapConfig = SnapConfig
  { -- | Grid size in pixels (0 = no snapping)
    gridSize :: Int
    
    -- | Whether to snap position to grid
  , snapPosition :: Boolean
  
    -- | Whether to snap size to grid
  , snapSize :: Boolean
  }

derive instance eqSnapConfig :: Eq SnapConfig

instance showSnapConfig :: Show SnapConfig where
  show (SnapConfig s) = "SnapConfig { grid: " <> show s.gridSize <> "px }"

-- | Default snap config — 8px grid, snap both position and size
defaultSnapConfig :: SnapConfig
defaultSnapConfig = SnapConfig
  { gridSize: 8
  , snapPosition: true
  , snapSize: true
  }

-- | No snapping
noSnap :: SnapConfig
noSnap = SnapConfig
  { gridSize: 0
  , snapPosition: false
  , snapSize: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport configuration — sizing and behavior settings.
newtype ViewportConfig = ViewportConfig
  { -- | Width in pixels (subject to snap config)
    width :: Number
    
    -- | Height in pixels (subject to snap config)
  , height :: Number
  
    -- | X position in pixels
  , x :: Number
  
    -- | Y position in pixels
  , y :: Number
  
    -- | Grid snapping configuration
  , snap :: SnapConfig
  
    -- | Padding inside the viewport (in pixels)
  , padding :: { top :: Number, right :: Number, bottom :: Number, left :: Number }
  
    -- | Corner radius for the viewport container
  , cornerRadius :: Number
  }

derive instance eqViewportConfig :: Eq ViewportConfig

instance showViewportConfig :: Show ViewportConfig where
  show (ViewportConfig c) = 
    "ViewportConfig { " <> show c.width <> "×" <> show c.height 
      <> " @ (" <> show c.x <> ", " <> show c.y <> ") }"

-- | Default viewport config — 256×256 at origin
defaultViewportConfig :: ViewportConfig
defaultViewportConfig = ViewportConfig
  { width: 256.0
  , height: 256.0
  , x: 0.0
  , y: 0.0
  , snap: defaultSnapConfig
  , padding: { top: 0.0, right: 0.0, bottom: 0.0, left: 0.0 }
  , cornerRadius: 8.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // viewport
-- ═════════════════════════════════════════════════════════════════════════════

-- | The Viewport — a bento-style widget container.
-- |
-- | A viewport contains three layers:
-- | 1. ShapeLayer (z+1) — strokes, elevation, glow
-- | 2. MaterialLayer (z+0.5) — background surface, 8px aligned
-- | 3. Children viewports (z+0) — nested content
-- |
-- | The viewport ID uses the Schema's ViewportId type — a deterministic
-- | identifier that can be derived from UUID5 namespace + name.
newtype Viewport = Viewport
  { -- | Deterministic identifier (from Schema.Reactive.Viewport.Types)
    id :: VPId.ViewportId
    
    -- | Configuration (size, position, snap)
  , config :: ViewportConfig
  
    -- | Material layer (background surface)
  , materialLayer :: ML.MaterialLayer
  
    -- | Shape layer (strokes, elevation)
  , shapeLayer :: SL.ShapeLayer
  
    -- | Nested child viewports
  , children :: Array Viewport
  
    -- | Transform applied to this viewport
  , transform :: Transform
  
    -- | Whether this viewport is visible
  , visible :: Boolean
  }

derive instance eqViewport :: Eq Viewport

instance showViewport :: Show Viewport where
  show (Viewport v) = 
    "Viewport { id: " <> show v.id <> ", " <> show v.config <> " }"

-- | Create a viewport with explicit configuration
viewport 
  :: { id :: VPId.ViewportId
     , config :: ViewportConfig
     , materialLayer :: ML.MaterialLayer
     , shapeLayer :: SL.ShapeLayer
     }
  -> Viewport
viewport cfg = Viewport
  { id: cfg.id
  , config: cfg.config
  , materialLayer: cfg.materialLayer
  , shapeLayer: cfg.shapeLayer
  , children: []
  , transform: identityTransform
  , visible: true
  }

-- | Default viewport — 256×256 solid gray background
-- |
-- | Takes a String and wraps it in ViewportId. For deterministic UUIDs,
-- | use UUID5 to generate the identifier string first.
defaultViewport :: String -> Viewport
defaultViewport viewportIdStr = Viewport
  { id: VPId.viewportIdFromString viewportIdStr
  , config: defaultViewportConfig
  , materialLayer: ML.defaultMaterialLayer
  , shapeLayer: SL.defaultShapeLayer
  , children: []
  , transform: identityTransform
  , visible: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the viewport ID
getId :: Viewport -> VPId.ViewportId
getId (Viewport v) = v.id

-- | Get the viewport configuration
getConfig :: Viewport -> ViewportConfig
getConfig (Viewport v) = v.config

-- | Get the material layer
getMaterialLayer :: Viewport -> ML.MaterialLayer
getMaterialLayer (Viewport v) = v.materialLayer

-- | Get the shape layer
getShapeLayer :: Viewport -> SL.ShapeLayer
getShapeLayer (Viewport v) = v.shapeLayer

-- | Get child viewports
getChildren :: Viewport -> Array Viewport
getChildren (Viewport v) = v.children

-- | Get the transform
getTransform :: Viewport -> Transform
getTransform (Viewport v) = v.transform

-- | Check if the viewport is visible
isViewportVisible :: Viewport -> Boolean
isViewportVisible (Viewport v) = v.visible

-- | Count the number of children
childCount :: Viewport -> Int
childCount (Viewport v) = Array.length v.children

-- | Unwrap to access the full record
unwrapViewport 
  :: Viewport 
  -> { id :: VPId.ViewportId
     , config :: ViewportConfig
     , materialLayer :: ML.MaterialLayer
     , shapeLayer :: SL.ShapeLayer
     , children :: Array Viewport
     , transform :: Transform
     , visible :: Boolean
     }
unwrapViewport (Viewport v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the viewport configuration
setConfig :: ViewportConfig -> Viewport -> Viewport
setConfig cfg (Viewport v) = Viewport (v { config = cfg })

-- | Set the material layer
setMaterialLayer :: ML.MaterialLayer -> Viewport -> Viewport
setMaterialLayer ml (Viewport v) = Viewport (v { materialLayer = ml })

-- | Set the shape layer
setShapeLayer :: SL.ShapeLayer -> Viewport -> Viewport
setShapeLayer sl (Viewport v) = Viewport (v { shapeLayer = sl })

-- | Set the transform
setTransform :: Transform -> Viewport -> Viewport
setTransform t (Viewport v) = Viewport (v { transform = t })

-- | Set visibility
setViewportVisible :: Boolean -> Viewport -> Viewport
setViewportVisible vis (Viewport v) = Viewport (v { visible = vis })

-- | Toggle visibility
toggleViewportVisible :: Viewport -> Viewport
toggleViewportVisible (Viewport v) = Viewport (v { visible = not v.visible })
  where
  not true = false
  not false = true

-- | Add a child viewport
addChild :: Viewport -> Viewport -> Viewport
addChild child (Viewport v) = 
  Viewport (v { children = Array.snoc v.children child })

-- | Add multiple child viewports
addChildren :: Array Viewport -> Viewport -> Viewport
addChildren newChildren (Viewport v) = 
  Viewport (v { children = v.children <> newChildren })

-- | Remove a child at a specific index
removeChildAt :: Int -> Viewport -> Maybe Viewport
removeChildAt idx (Viewport v) =
  case Array.deleteAt idx v.children of
    Just newChildren -> Just $ Viewport (v { children = newChildren })
    Nothing -> Nothing

-- | Remove all children
clearChildren :: Viewport -> Viewport
clearChildren (Viewport v) = Viewport (v { children = [] })

-- | Resize the viewport (updates config width/height)
resizeViewport :: Number -> Number -> Viewport -> Viewport
resizeViewport width height (Viewport v) = 
  let ViewportConfig cfg = v.config
      newConfig = ViewportConfig (cfg { width = max 0.0 width, height = max 0.0 height })
  in Viewport (v { config = newConfig })

-- | Move the viewport (updates config x/y position)
moveViewport :: Number -> Number -> Viewport -> Viewport
moveViewport x y (Viewport v) = 
  let ViewportConfig cfg = v.config
      newConfig = ViewportConfig (cfg { x = x, y = y })
  in Viewport (v { config = newConfig })
