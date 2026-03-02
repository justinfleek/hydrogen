-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // compositor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Compositor — Layered Rendering Architecture
-- |
-- | ## Design Philosophy
-- |
-- | The Compositor is a pure data model for layered rendering, inspired by
-- | professional compositing software (After Effects, Nuke, Fusion). It provides
-- | a z-depth stack where every element has physics, temporal behavior, and
-- | can contain any content.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Canvas (z=0)
-- | ├── Ultimate boundary container
-- | ├── Receives shadows from above
-- | ├── Nothing goes "behind"
-- | └── Critical for 3D scenes, VR/AR, game worlds
-- |
-- | Viewport (z=1+)
-- | ├── ShapeLayer (z+1) — Pure math, pixel-perfect clipping at any scale
-- | ├── MaterialLayer (z+0.5) — Diffusion surface, 8px grid aligned
-- | └── ContentLayer (z+0) — Anything: buttons, dashboards, world models
-- | ```
-- |
-- | ## Key Insight: Scale Behavior
-- |
-- | On pinch zoom:
-- | - **MaterialLayer**: Snaps to nearest 8px boundary (diffusion tile alignment)
-- | - **ShapeLayer**: Pure math recalculation, clips at exact pixel
-- |
-- | This is because diffusion models operate on 8×8 (or 64×64) tile boundaries
-- | (the latent space constraint), while shape layers are vector math and
-- | resolution-independent.
-- |
-- | ## Bento Widget Model
-- |
-- | Viewports are bento-style widget boxes:
-- | - Can snap to grid or be dynamic
-- | - Have padding, effects, glows, animated strokes
-- | - Support temporal, gestural, and physics behaviors
-- | - Frame.io style hyper-responsive widgets
-- |
-- | A **button** is just a mini-viewport (length divisible by 8) with a shape
-- | layer on top. It has the same material background system — could be a
-- | diffusion model layer, SVG, image, video, or generated world model element.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Because everything is pure data:
-- | - 12 viewports on a display, each running different world model simulations
-- | - Lottie path animations between elements with proper occlusion
-- | - Physics interactions across the z-depth stack
-- | - Same viewport definition = same rendering (always)
-- |
-- | ## Module Structure
-- |
-- | - `Compositor.Canvas` — Base layer (z=0), shadow receiver, boundary
-- | - `Compositor.Viewport` — Bento widget container with layer stack
-- | - `Compositor.MaterialLayer` — Diffusion surface, 8px grid aligned
-- | - `Compositor.ShapeLayer` — Pure math, pixel-perfect clipping
-- | - `Compositor.Stack` — Z-depth ordering, occlusion, physics
-- | - `Compositor.Transform` — Scale, rotation, translation with proper layer behavior

module Hydrogen.Compositor
  ( -- * Re-exports from Canvas
    module Canvas
  
  -- * Re-exports from Viewport
  , module Viewport
  
  -- * Re-exports from MaterialLayer
  , module MaterialLayer
  
  -- * Re-exports from ShapeLayer
  , module ShapeLayer
  
  -- * Re-exports from Stack
  , module Stack
  
  -- * Re-exports from Transform
  , module Transform
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Compositor.Canvas 
  ( Canvas(Canvas)
  , CanvasDimension(Pixels, Percentage, ViewportRelative)
  , ClearColor(Transparent, Solid, Gradient)
  , ShadowConfig(ShadowConfig)
  , canvas
  , defaultCanvas
  , unwrapCanvas
  , pixels
  , percentage
  , viewportRelative
  , dimensionToPixels
  , transparent
  , solid
  , gradient
  , shadowConfig
  , defaultShadowConfig
  , disabledShadowConfig
  , canvasWidth
  , canvasHeight
  , canvasBounds
  , acceptsShadows
  , isTransparent
  , resizeCanvas
  , setClearColor
  , setShadowConfig
  ) as Canvas

import Hydrogen.Compositor.Viewport 
  ( Viewport(Viewport)
  , ViewportConfig(ViewportConfig)
  , SnapConfig(SnapConfig)
  , ViewportId(ViewportId)
  , viewport
  , defaultViewport
  , defaultViewportConfig
  , defaultSnapConfig
  , noSnap
  , viewportIdFromString
  ) as Viewport

import Hydrogen.Compositor.MaterialLayer 
  ( MaterialLayer(MaterialLayer)
  , MaterialSource
      ( SolidColor
      , ImageSource
      , VideoSource
      , SVGSource
      , ShaderSource
      , DiffusionSource
      , NoiseSource
      )
  , GridAlignment(GridAlignment)
  , DiffusionSettings(DiffusionSettings)
  , materialLayer
  , defaultMaterialLayer
  , defaultGridAlignment
  , snapToGrid
  , defaultDiffusionSettings
  , getSource
  , getOpacity
  , getWidth
  , getHeight
  , getAlignment
  , isMaterialVisible
  , unwrapMaterialLayer
  , setSource
  , setOpacity
  , resize
  , resizeSnapped
  , setAlignment
  , setMaterialVisible
  , toggleMaterialVisible
  ) as MaterialLayer

import Hydrogen.Compositor.ShapeLayer 
  ( ShapeLayer(ShapeLayer)
  , ShapePrimitive
      ( Rectangle
      , Ellipse
      , Path
      , RoundedRect
      , RegularPolygon
      , Star
      , Line
      , Polyline
      , Polygon
      )
  , PathCommand(MoveTo, LineTo, QuadTo, CubicTo, ClosePath)
  , StrokeConfig(StrokeConfig)
  , LineCap(CapButt, CapRound, CapSquare)
  , LineJoin(JoinMiter, JoinRound, JoinBevel)
  , defaultShapeLayer
  , defaultStrokeConfig
  , noShadow
  , elevationShadow
  , rectangle
  , ellipse
  , path
  , roundedRect
  , regularPolygon
  , triangle
  , pentagon
  , hexagon
  , star
  , line
  , polyline
  , polygon
  , getShapes
  , getStroke
  , getFill
  , getShadow
  , getGlowRadius
  , getGlowColor
  , isShapeVisible
  , shapeCount
  , unwrapShapeLayer
  , addShape
  , addShapes
  , removeShapeAt
  , clearShapes
  , setStroke
  , setFill
  , setShadow
  , setGlow
  , setGlowRadius
  , setGlowColor
  , setShapeVisible
  , toggleShapeVisible
  ) as ShapeLayer

import Hydrogen.Compositor.Stack 
  ( Stack(Stack)
  , StackEntry
  , ZDepth(ZDepth)
  , emptyStack
  , zDepth
  , baseDepth
  , addDepth
  , pushLayer
  , popLayer
  , getLayerAt
  , getTopVisibleLayer
  , getHiddenLayers
  , incrementLayerDepth
  , toggleLayerVisibility
  , sortByDepth
  -- Additional Stack Operations
  , layerCount
  , getLayerById
  , removeById
  , updateContent
  , insertAt
  , reorderLayers
  , bringToFront
  , sendToBack
  , moveUp
  , moveDown
  ) as Stack

import Hydrogen.Compositor.Transform 
  ( Transform(Transform)
  , Translation(Translation)
  , Scale(Scale)
  , Rotation(Rotation)
  , identityTransform
  , translate
  , scale
  , rotate
  , compose
  -- Component Accessors
  , getTranslation
  , getScale
  , getRotation
  , setTranslation
  , setScale
  , setRotation
  -- Uniform Scale
  , uniformScale
  , scaleBy
  -- Point Operations
  , applyToPoint
  , applyInverseToPoint
  -- Transform Inversion
  , invert
  -- Interpolation
  , lerp
  -- Bounded Operations
  , clampScale
  , clampTranslation
  -- Identity Check
  , isIdentity
  -- Matrix Representation
  , Matrix3x3(Matrix3x3)
  , toMatrix
  , fromMatrix
  , multiplyMatrices
  , determinant
  ) as Transform
