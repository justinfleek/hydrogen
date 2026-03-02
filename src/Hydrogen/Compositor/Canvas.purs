-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // compositor // canvas
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas — The Base Compositor Layer (z=0)
-- |
-- | ## Design Philosophy
-- |
-- | The Canvas is the **ultimate boundary container**. It is z=0, the back layer
-- | that starts on load. Nothing ever goes "behind" it.
-- |
-- | ## Responsibilities
-- |
-- | 1. **Shadow Receiver**: Accepts shadows cast from all layers above
-- | 2. **Boundary Definition**: Defines the rendering bounds for the compositor
-- | 3. **Memory Boundary**: Critical for 3D scenes, game worlds, VR/AR where
-- |    content outside the canvas should be culled for memory efficiency
-- | 4. **Clear Color**: The background when nothing is rendered
-- |
-- | ## At Billion-Agent Scale
-- |
-- | The Canvas is pure data describing the compositor's root:
-- | - Same Canvas config = same rendering behavior (always)
-- | - Agents can reason about bounds without executing rendering
-- | - Memory management hints for culling off-canvas content
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Compositor.Canvas as Canvas
-- |
-- | myCanvas :: Canvas.Canvas
-- | myCanvas = Canvas.canvas
-- |   { width: Canvas.pixels 1920
-- |   , height: Canvas.pixels 1080
-- |   , clearColor: Canvas.transparent
-- |   , shadowConfig: Canvas.defaultShadowConfig
-- |   }
-- | ```

module Hydrogen.Compositor.Canvas
  ( -- * Canvas Type
    Canvas(Canvas)
  , canvas
  , defaultCanvas
  , unwrapCanvas
  
  -- * Dimensions
  , CanvasDimension(Pixels, Percentage, ViewportRelative)
  , pixels
  , percentage
  , viewportRelative
  , dimensionToPixels
  
  -- * Clear Color
  , ClearColor(Transparent, Solid, Gradient)
  , transparent
  , solid
  , gradient
  
  -- * Shadow Configuration
  , ShadowConfig(ShadowConfig)
  , shadowConfig
  , defaultShadowConfig
  , disabledShadowConfig
  
  -- * Canvas Queries
  , canvasWidth
  , canvasHeight
  , canvasBounds
  , acceptsShadows
  , isTransparent
  
  -- * Canvas Operations
  , resizeCanvas
  , setClearColor
  , setShadowConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (*)
  , (/)
  , (<>)
  )

import Hydrogen.Schema.Color.RGB (RGBA, rgba)
import Hydrogen.Schema.Geometry.Point (Point2D, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // canvas dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Canvas dimension — how width/height are specified.
-- |
-- | Supports absolute pixels, percentage of parent, or viewport-relative units.
data CanvasDimension
  = Pixels Number
      -- ^ Absolute pixel value (e.g., 1920.0 pixels)
  | Percentage Number
      -- ^ Percentage of parent container (0-100)
  | ViewportRelative Number
      -- ^ Percentage of viewport (vw/vh style, 0-100)

derive instance eqCanvasDimension :: Eq CanvasDimension

instance showCanvasDimension :: Show CanvasDimension where
  show (Pixels n) = show n <> "px"
  show (Percentage n) = show n <> "%"
  show (ViewportRelative n) = show n <> "vw"

-- | Create pixel dimension
pixels :: Number -> CanvasDimension
pixels = Pixels

-- | Create percentage dimension
percentage :: Number -> CanvasDimension
percentage = Percentage

-- | Create viewport-relative dimension
viewportRelative :: Number -> CanvasDimension
viewportRelative = ViewportRelative

-- | Resolve dimension to pixels given parent and viewport sizes.
-- |
-- | For Pixels, returns the value directly.
-- | For Percentage, computes based on parent size.
-- | For ViewportRelative, computes based on viewport size.
dimensionToPixels 
  :: { parentSize :: Number, viewportSize :: Number } 
  -> CanvasDimension 
  -> Number
dimensionToPixels ctx = case _ of
  Pixels n -> n
  Percentage p -> ctx.parentSize * (p / 100.0)
  ViewportRelative v -> ctx.viewportSize * (v / 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // clear color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear color — what the canvas shows when nothing is rendered.
-- |
-- | This is the "background" of the compositor, but it's more than cosmetic:
-- | - Transparent allows compositing over other content (WebGL overlays)
-- | - Solid is fastest for GPU clear operations
-- | - Gradient requires a draw call but provides visual richness
data ClearColor
  = Transparent
      -- ^ Fully transparent (alpha = 0)
  | Solid RGBA
      -- ^ Solid color fill
  | Gradient RGBA RGBA Number
      -- ^ Linear gradient from color A to B at angle (degrees)

derive instance eqClearColor :: Eq ClearColor

instance showClearColor :: Show ClearColor where
  show Transparent = "transparent"
  show (Solid c) = "solid(" <> show c <> ")"
  show (Gradient a b angle) = 
    "gradient(" <> show a <> " → " <> show b <> " @ " <> show angle <> "°)"

-- | Transparent clear color
transparent :: ClearColor
transparent = Transparent

-- | Solid clear color
solid :: RGBA -> ClearColor
solid = Solid

-- | Gradient clear color
gradient :: RGBA -> RGBA -> Number -> ClearColor
gradient = Gradient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shadow configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow configuration — how the canvas receives shadows from layers above.
-- |
-- | The canvas is the ultimate shadow receiver. All viewports cast shadows
-- | that land on the canvas (or on viewports below them).
newtype ShadowConfig = ShadowConfig
  { -- | Whether shadows are rendered at all
    enabled :: Boolean
    
    -- | Shadow blur radius in pixels (0 = hard shadow)
  , blurRadius :: Number
  
    -- | Shadow opacity multiplier (0-1)
  , opacity :: Number
  
    -- | Shadow color tint (multiplied with shadow)
  , tint :: RGBA
  
    -- | Maximum shadow distance (for performance culling)
  , maxDistance :: Number
  }

derive instance eqShadowConfig :: Eq ShadowConfig

instance showShadowConfig :: Show ShadowConfig where
  show (ShadowConfig s) = 
    "ShadowConfig { enabled: " <> show s.enabled 
      <> ", blur: " <> show s.blurRadius <> "px }"

-- | Create shadow configuration
shadowConfig 
  :: { enabled :: Boolean
     , blurRadius :: Number
     , opacity :: Number
     , tint :: RGBA
     , maxDistance :: Number
     }
  -> ShadowConfig
shadowConfig = ShadowConfig

-- | Default shadow configuration — shadows enabled with soft blur
defaultShadowConfig :: ShadowConfig
defaultShadowConfig = ShadowConfig
  { enabled: true
  , blurRadius: 16.0
  , opacity: 0.25
  , tint: rgba 0 0 0 255  -- Black tint
  , maxDistance: 256.0
  }

-- | Disabled shadow configuration — no shadows rendered
disabledShadowConfig :: ShadowConfig
disabledShadowConfig = ShadowConfig
  { enabled: false
  , blurRadius: 0.0
  , opacity: 0.0
  , tint: rgba 0 0 0 0
  , maxDistance: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // canvas
-- ═════════════════════════════════════════════════════════════════════════════

-- | The Canvas — base compositor layer at z=0.
-- |
-- | This is pure data describing the compositor's root container.
-- | The runtime interprets this to set up the rendering context.
newtype Canvas = Canvas
  { -- | Canvas width
    width :: CanvasDimension
    
    -- | Canvas height
  , height :: CanvasDimension
  
    -- | Clear color (background)
  , clearColor :: ClearColor
  
    -- | Shadow receiving configuration
  , shadowConfig :: ShadowConfig
  
    -- | Whether content outside canvas bounds should be culled
    -- | Critical for memory management in game worlds
  , cullOutOfBounds :: Boolean
  
    -- | Canvas origin point (for coordinate system)
  , origin :: Point2D
  }

derive instance eqCanvas :: Eq Canvas

instance showCanvas :: Show Canvas where
  show (Canvas c) =
    "Canvas { " <> show c.width <> " × " <> show c.height 
      <> ", " <> show c.clearColor <> " }"

-- | Create a canvas with explicit configuration
canvas 
  :: { width :: CanvasDimension
     , height :: CanvasDimension
     , clearColor :: ClearColor
     , shadowConfig :: ShadowConfig
     }
  -> Canvas
canvas cfg = Canvas
  { width: cfg.width
  , height: cfg.height
  , clearColor: cfg.clearColor
  , shadowConfig: cfg.shadowConfig
  , cullOutOfBounds: true
  , origin: point2D 0.0 0.0
  }

-- | Default canvas — 1920×1080, transparent, shadows enabled
defaultCanvas :: Canvas
defaultCanvas = Canvas
  { width: Pixels 1920.0
  , height: Pixels 1080.0
  , clearColor: Transparent
  , shadowConfig: defaultShadowConfig
  , cullOutOfBounds: true
  , origin: point2D 0.0 0.0
  }

-- | Unwrap canvas to access fields
unwrapCanvas 
  :: Canvas 
  -> { width :: CanvasDimension
     , height :: CanvasDimension
     , clearColor :: ClearColor
     , shadowConfig :: ShadowConfig
     , cullOutOfBounds :: Boolean
     , origin :: Point2D
     }
unwrapCanvas (Canvas c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // canvas queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get canvas width dimension
canvasWidth :: Canvas -> CanvasDimension
canvasWidth (Canvas c) = c.width

-- | Get canvas height dimension
canvasHeight :: Canvas -> CanvasDimension
canvasHeight (Canvas c) = c.height

-- | Get canvas bounds as a rectangle (requires resolution context)
canvasBounds 
  :: { parentWidth :: Number
     , parentHeight :: Number
     , viewportWidth :: Number
     , viewportHeight :: Number
     }
  -> Canvas 
  -> { x :: Number, y :: Number, width :: Number, height :: Number }
canvasBounds ctx (Canvas c) =
  let
    w = dimensionToPixels 
      { parentSize: ctx.parentWidth, viewportSize: ctx.viewportWidth } 
      c.width
    h = dimensionToPixels 
      { parentSize: ctx.parentHeight, viewportSize: ctx.viewportHeight } 
      c.height
  in
    { x: 0.0, y: 0.0, width: w, height: h }

-- | Check if canvas accepts shadows
acceptsShadows :: Canvas -> Boolean
acceptsShadows (Canvas c) = 
  let ShadowConfig s = c.shadowConfig
  in s.enabled

-- | Check if canvas is transparent
isTransparent :: Canvas -> Boolean
isTransparent (Canvas c) = c.clearColor == Transparent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // canvas operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resize canvas to new dimensions
resizeCanvas :: CanvasDimension -> CanvasDimension -> Canvas -> Canvas
resizeCanvas newWidth newHeight (Canvas c) =
  Canvas (c { width = newWidth, height = newHeight })

-- | Set canvas clear color
setClearColor :: ClearColor -> Canvas -> Canvas
setClearColor newColor (Canvas c) =
  Canvas (c { clearColor = newColor })

-- | Set canvas shadow configuration
setShadowConfig :: ShadowConfig -> Canvas -> Canvas
setShadowConfig newConfig (Canvas c) =
  Canvas (c { shadowConfig = newConfig })
