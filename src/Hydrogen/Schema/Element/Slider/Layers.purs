-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // element // slider // layers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SliderLayers — Compositor layer stack for diffusion-native slider rendering.
-- |
-- | ## Architecture
-- |
-- | Following the After Effects compositor mental model, a slider is modeled
-- | as a composition of stacked layers. Each layer has:
-- | - Shape mask (what clips the layer)
-- | - Material fill (what fills the shape)
-- | - Blend mode (how it composites with layers below)
-- | - Opacity (transparency)
-- | - Z-index (stacking order)
-- |
-- | ## Layer Stack
-- |
-- | ```
-- |      Z-Index ↑
-- |          │
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 7: Focus Ring                    │ ← Stroke, glow
-- |          │   │  (keyboard focus indicator)             │
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 6: Thumb Shadow                  │ ← Elevation.Shadow
-- |          │   │  (drop shadow for thumb depth)          │
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 5: Thumb Material                │ ← Surface.Fill
-- |          │   │  (thumb fill - solid/gradient)          │   (white, colored)
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 4: Thumb Shape Mask              │ ← Geometry.Shape
-- |          │   │  (circle, square, pill)                 │
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 3: Progress Material             │ ← Surface.Fill
-- |          │   │  (filled portion of track)              │   (solid color)
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 2: Track Material                │ ← Surface.Fill
-- |          │   │  (full track fill - gradient for hue!)  │   (gradient, solid)
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 1: Track Shape Mask              │ ← Geometry.Shape
-- |          │   │  (rounded rectangle, pill)              │
-- |          │   └─────────────────────────────────────────┘
-- |          │   ┌─────────────────────────────────────────┐
-- |          │   │  Layer 0: Background (optional)         │ ← Surface.Fill
-- |          │   │  (checkerboard for opacity slider)      │
-- |          │   └─────────────────────────────────────────┘
-- |          │
-- |          ▼ Z = 0
-- | ```
-- |
-- | ## Diffusion Rendering
-- |
-- | Each layer is described as pure data that diffusion models can interpret:
-- | - Shape masks become alpha masks
-- | - Materials become texture samples
-- | - Gradients are fully specified (stops, positions, angles)
-- | - Shadows have physical parameters (blur, offset, color)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Shape (shape masks)
-- | - Hydrogen.Schema.Geometry.CornerRadii (track/thumb corners)
-- | - Hydrogen.Schema.Surface.Fill (material fills)
-- | - Hydrogen.Schema.Color.Gradient (gradient fills for hue/sat/etc.)
-- | - Hydrogen.Schema.Elevation.Shadow (thumb shadows)
-- | - Hydrogen.Schema.Elevation.ZIndex (layer ordering)
-- | - Hydrogen.Schema.Motion.Composition (blend modes)

module Hydrogen.Schema.Element.Slider.Layers
  ( -- * Layer Types
    SliderLayer
      ( LayerBackground
      , LayerTrackMask
      , LayerTrackMaterial
      , LayerProgressMaterial
      , LayerThumbMask
      , LayerThumbMaterial
      , LayerThumbShadow
      , LayerFocusRing
      )
  
  -- * Layer Stack
  , SliderLayerStack
  , defaultLayerStack
  , hueSliderLayers
  , saturationSliderLayers
  , lightnessSliderLayers
  , volumeSliderLayers
  , opacitySliderLayers
  , temperatureSliderLayers
  
  -- * Layer Base
  , LayerBase
  , defaultLayerBase
  
  -- * Individual Layer Types
  , BackgroundLayer
  , TrackMaskLayer
  , TrackMaterialLayer
  , ProgressMaterialLayer
  , ThumbMaskLayer
  , ThumbMaterialLayer
  , ThumbShadowLayer
  , FocusRingLayer
  
  -- * Layer Constructors
  , backgroundLayer
  , trackMaskLayer
  , trackMaterialLayer
  , progressMaterialLayer
  , thumbMaskLayer
  , thumbMaterialLayer
  , thumbShadowLayer
  , focusRingLayer
  
  -- * Layer Accessors
  , getZIndex
  , getBlendMode
  , getOpacity
  , isVisible
  
  -- * Gradient Presets for Sliders
  , hueRainbowGradient
  , saturationGradient
  , lightnessGradient
  , temperatureGradient
  , checkerboardPattern
  
  -- * Default Shapes
  , defaultTrackShape
  , defaultThumbShape
  , defaultFocusRingShape
  , defaultThumbShadow
  
  -- * Shape Helpers (for creating custom shapes)
  , trackShape
  , thumbShape
  , defaultCorners
  , pillCorners
  , squareCorners
  
  -- * Re-exports
  , module Hydrogen.Schema.Geometry.Shape
  , module Hydrogen.Schema.Surface.Fill
  , module Hydrogen.Schema.Color.Gradient
  , module Hydrogen.Schema.Elevation.Shadow
  , module Hydrogen.Schema.Elevation.ZIndex
  , module Hydrogen.Schema.Motion.Composition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  , (/)
  )

import Prim (Boolean, Int, Number)

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Shape
  ( Shape(ShapeRectangle, ShapeEllipse)
  , RectangleShape
  , EllipseShape
  )

import Hydrogen.Schema.Geometry.Shape.Primitives
  ( rectangleShape
  , ellipseShape
  , circleShape
  )

import Hydrogen.Schema.Geometry.Shape.Types
  ( PixelPoint2D
  )

import Hydrogen.Schema.Geometry.Radius
  ( Corners
  , Radius(RadiusPx)
  , px
  ) as Radius

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  , none
  )

import Hydrogen.Schema.Surface.Fill
  ( Fill(FillNone, FillSolid, FillGradient, FillPattern)
  , fillSolid
  , fillGradient
  , fillNone
  )

import Hydrogen.Schema.Color.RGB
  ( RGB
  , RGBA
  , rgb
  , rgba
  )

import Hydrogen.Schema.Color.Gradient
  ( Gradient(Linear, Conic)
  , LinearGradient
  , ConicGradient
  , ColorStop(ColorStop)
  , colorStop
  , linearGradient
  , linearGradientFromAngle
  , conicGradient
  )

import Hydrogen.Schema.Color.Hue as Hue

import Hydrogen.Schema.Elevation.Shadow
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  )

import Hydrogen.Schema.Elevation.ZIndex
  ( ZIndex
  , z
  )

import Hydrogen.Schema.Motion.Composition
  ( BlendMode(BMNormal, BMMultiply, BMScreen)
  )

import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // layer base type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base layer properties shared by all slider layers.
-- |
-- | Every layer in the compositor stack has:
-- | - zIndex: Stacking order (higher = on top)
-- | - blendMode: How it composites with layers below
-- | - opacity: Transparency (0.0-1.0)
-- | - visible: Whether to render
type LayerBase =
  { zIndex :: ZIndex
  , blendMode :: BlendMode
  , opacity :: Number
  , visible :: Boolean
  }

-- | Default layer base — visible, normal blend, full opacity.
defaultLayerBase :: Int -> LayerBase
defaultLayerBase zVal =
  { zIndex: z zVal
  , blendMode: BMNormal
  , opacity: 1.0
  , visible: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // individual layers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Background layer — optional pattern for opacity sliders.
-- |
-- | Z-index: 0 (bottom)
-- | Shape is self-describing (rectangle, star, gear — whatever).
-- | Fill is self-describing (solid, gradient, pattern, noise).
type BackgroundLayer =
  { base :: LayerBase
  , shape :: Shape          -- ^ Background shape (clips the fill)
  , fill :: Fill            -- ^ Checkerboard pattern, solid, etc.
  }

-- | Track shape mask layer — defines the track outline.
-- |
-- | Z-index: 1
-- | This is a mask layer — it clips the material layer above it.
-- | The shape is completely polymorphic — could be rectangle, star,
-- | gear, spiral, compound boolean shape, etc.
type TrackMaskLayer =
  { base :: LayerBase
  , shape :: Shape          -- ^ Any shape from Geometry.Shape
  }

-- | Track material layer — fills the track shape.
-- |
-- | Z-index: 2
-- | For hue sliders, this is a rainbow gradient.
-- | For saturation sliders, this is a saturation gradient.
-- | For simple sliders, this is a solid gray.
-- | Fill is polymorphic — solid, gradient, pattern, procedural noise.
type TrackMaterialLayer =
  { base :: LayerBase
  , fill :: Fill            -- ^ Solid, gradient, pattern, noise
  }

-- | Progress material layer — shows current value.
-- |
-- | Z-index: 3
-- | Overlays the track to show "filled" portion.
-- | The shape is clipped by progressPercent (0.0-1.0).
type ProgressMaterialLayer =
  { base :: LayerBase
  , shape :: Shape          -- ^ Shape for progress (usually same as track)
  , fill :: Fill            -- ^ Progress fill (usually solid brand color)
  , progressPercent :: Number  -- ^ 0.0-1.0 how much is filled
  }

-- | Thumb shape mask layer — defines the thumb outline.
-- |
-- | Z-index: 4
-- | Shape is polymorphic — circle, star, triangle, gear, etc.
type ThumbMaskLayer =
  { base :: LayerBase
  , shape :: Shape          -- ^ Any shape from Geometry.Shape
  }

-- | Thumb material layer — fills the thumb.
-- |
-- | Z-index: 5
-- | Fill is polymorphic — solid white, gradient, pattern, etc.
type ThumbMaterialLayer =
  { base :: LayerBase
  , fill :: Fill            -- ^ Solid, gradient, pattern
  }

-- | Thumb shadow layer — drop shadow for depth.
-- |
-- | Z-index: 6
-- | Shadow is a layered shadow (multiple box shadows for realism).
type ThumbShadowLayer =
  { base :: LayerBase
  , shadow :: LayeredShadow
  }

-- | Focus ring layer — keyboard focus indicator.
-- |
-- | Z-index: 7 (top)
-- | Shape defines the ring outline — typically matches thumb shape but
-- | expanded by offset. Could be any shape.
type FocusRingLayer =
  { base :: LayerBase
  , shape :: Shape          -- ^ Ring shape (usually expanded thumb shape)
  , strokeColor :: RGB      -- ^ Ring stroke color
  , strokeWidth :: Pixel    -- ^ Ring stroke width
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // slider layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum type for all slider layer variants.
-- |
-- | This enables heterogeneous arrays and pattern matching.
data SliderLayer
  = LayerBackground BackgroundLayer
  | LayerTrackMask TrackMaskLayer
  | LayerTrackMaterial TrackMaterialLayer
  | LayerProgressMaterial ProgressMaterialLayer
  | LayerThumbMask ThumbMaskLayer
  | LayerThumbMaterial ThumbMaterialLayer
  | LayerThumbShadow ThumbShadowLayer
  | LayerFocusRing FocusRingLayer

derive instance eqSliderLayer :: Eq SliderLayer

instance showSliderLayer :: Show SliderLayer where
  show (LayerBackground _) = "LayerBackground"
  show (LayerTrackMask _) = "LayerTrackMask"
  show (LayerTrackMaterial _) = "LayerTrackMaterial"
  show (LayerProgressMaterial _) = "LayerProgressMaterial"
  show (LayerThumbMask _) = "LayerThumbMask"
  show (LayerThumbMaterial _) = "LayerThumbMaterial"
  show (LayerThumbShadow _) = "LayerThumbShadow"
  show (LayerFocusRing _) = "LayerFocusRing"

-- | Get z-index from any layer.
getZIndex :: SliderLayer -> ZIndex
getZIndex = case _ of
  LayerBackground l -> l.base.zIndex
  LayerTrackMask l -> l.base.zIndex
  LayerTrackMaterial l -> l.base.zIndex
  LayerProgressMaterial l -> l.base.zIndex
  LayerThumbMask l -> l.base.zIndex
  LayerThumbMaterial l -> l.base.zIndex
  LayerThumbShadow l -> l.base.zIndex
  LayerFocusRing l -> l.base.zIndex

-- | Get blend mode from any layer.
getBlendMode :: SliderLayer -> BlendMode
getBlendMode = case _ of
  LayerBackground l -> l.base.blendMode
  LayerTrackMask l -> l.base.blendMode
  LayerTrackMaterial l -> l.base.blendMode
  LayerProgressMaterial l -> l.base.blendMode
  LayerThumbMask l -> l.base.blendMode
  LayerThumbMaterial l -> l.base.blendMode
  LayerThumbShadow l -> l.base.blendMode
  LayerFocusRing l -> l.base.blendMode

-- | Get opacity from any layer.
getOpacity :: SliderLayer -> Number
getOpacity = case _ of
  LayerBackground l -> l.base.opacity
  LayerTrackMask l -> l.base.opacity
  LayerTrackMaterial l -> l.base.opacity
  LayerProgressMaterial l -> l.base.opacity
  LayerThumbMask l -> l.base.opacity
  LayerThumbMaterial l -> l.base.opacity
  LayerThumbShadow l -> l.base.opacity
  LayerFocusRing l -> l.base.opacity

-- | Check if layer is visible.
isVisible :: SliderLayer -> Boolean
isVisible = case _ of
  LayerBackground l -> l.base.visible
  LayerTrackMask l -> l.base.visible
  LayerTrackMaterial l -> l.base.visible
  LayerProgressMaterial l -> l.base.visible
  LayerThumbMask l -> l.base.visible
  LayerThumbMaterial l -> l.base.visible
  LayerThumbShadow l -> l.base.visible
  LayerFocusRing l -> l.base.visible

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layer constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a background layer.
-- |
-- | Shape defines the background boundary (clips the fill).
-- | Fill is what appears inside the shape.
backgroundLayer :: Shape -> Fill -> BackgroundLayer
backgroundLayer shape fill =
  { base: defaultLayerBase 0
  , shape: shape
  , fill: fill
  }

-- | Create a track mask layer.
-- |
-- | Shape can be any shape — rectangle, star, gear, spiral, etc.
trackMaskLayer :: Shape -> TrackMaskLayer
trackMaskLayer shape =
  { base: defaultLayerBase 1
  , shape: shape
  }

-- | Create a track material layer.
-- |
-- | Fill can be solid, gradient, pattern, or procedural noise.
trackMaterialLayer :: Fill -> TrackMaterialLayer
trackMaterialLayer fill =
  { base: defaultLayerBase 2
  , fill: fill
  }

-- | Create a progress material layer.
-- |
-- | Shape defines what gets filled up to progressPercent.
-- | Fill is the color/gradient of the progress indicator.
progressMaterialLayer :: Shape -> Fill -> Number -> ProgressMaterialLayer
progressMaterialLayer shape fill percent =
  { base: defaultLayerBase 3
  , shape: shape
  , fill: fill
  , progressPercent: percent
  }

-- | Create a thumb mask layer.
-- |
-- | Shape can be circle, star, triangle, gear, etc.
thumbMaskLayer :: Shape -> ThumbMaskLayer
thumbMaskLayer shape =
  { base: defaultLayerBase 4
  , shape: shape
  }

-- | Create a thumb material layer.
-- |
-- | Fill defines the thumb appearance.
thumbMaterialLayer :: Fill -> ThumbMaterialLayer
thumbMaterialLayer fill =
  { base: defaultLayerBase 5
  , fill: fill
  }

-- | Create a thumb shadow layer.
-- |
-- | Shadow is a multi-layer box shadow for realistic depth.
thumbShadowLayer :: LayeredShadow -> ThumbShadowLayer
thumbShadowLayer shadow =
  { base: defaultLayerBase 6
  , shadow: shadow
  }

-- | Create a focus ring layer.
-- |
-- | Shape defines the ring outline.
-- | Stroke color and width define the ring appearance.
focusRingLayer :: Shape -> RGB -> Pixel -> FocusRingLayer
focusRingLayer shape color strokeWidth =
  { base: (defaultLayerBase 7) { visible = false }  -- Hidden by default
  , shape: shape
  , strokeColor: color
  , strokeWidth: strokeWidth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // slider layer stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete layer stack for a slider.
-- |
-- | All layers from bottom to top. Optional layers use Maybe.
type SliderLayerStack =
  { background :: Maybe BackgroundLayer      -- ^ Optional (for opacity)
  , trackMask :: TrackMaskLayer              -- ^ Required
  , trackMaterial :: TrackMaterialLayer      -- ^ Required
  , progressMaterial :: ProgressMaterialLayer -- ^ Required
  , thumbMask :: ThumbMaskLayer              -- ^ Required
  , thumbMaterial :: ThumbMaterialLayer      -- ^ Required
  , thumbShadow :: ThumbShadowLayer          -- ^ Required
  , focusRing :: FocusRingLayer              -- ^ Required (hidden until focused)
  }

-- | Default slider layer stack.
-- |
-- | Horizontal slider with:
-- | - 200×8px rounded rectangle track (gray)
-- | - 20px circle thumb (white with shadow)
-- | - Blue progress fill
-- | - Blue focus ring
-- |
-- | All shapes are configurable — this is just a sensible default.
defaultLayerStack :: SliderLayerStack
defaultLayerStack =
  { background: Nothing
  , trackMask: trackMaskLayer defaultTrackShape
  , trackMaterial: trackMaterialLayer (fillSolid (rgb 209 213 219))
  , progressMaterial: progressMaterialLayer defaultTrackShape (fillSolid (rgb 59 130 246)) 0.5
  , thumbMask: thumbMaskLayer defaultThumbShape
  , thumbMaterial: thumbMaterialLayer (fillSolid (rgb 255 255 255))
  , thumbShadow: thumbShadowLayer defaultThumbShadow
  , focusRing: focusRingLayer defaultFocusRingShape (rgb 96 165 250) (Pixel 2.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gradient presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rainbow hue gradient for hue slider.
-- |
-- | Full spectrum: red → yellow → green → cyan → blue → magenta → red
hueRainbowGradient :: Gradient
hueRainbowGradient = Linear (linearGradientFromAngle 90.0
  [ colorStop (rgb 255 0 0) 0.0        -- Red (0°)
  , colorStop (rgb 255 255 0) 0.167    -- Yellow (60°)
  , colorStop (rgb 0 255 0) 0.333      -- Green (120°)
  , colorStop (rgb 0 255 255) 0.5      -- Cyan (180°)
  , colorStop (rgb 0 0 255) 0.667      -- Blue (240°)
  , colorStop (rgb 255 0 255) 0.833    -- Magenta (300°)
  , colorStop (rgb 255 0 0) 1.0        -- Red (360°)
  ])

-- | Saturation gradient from gray to full color.
-- |
-- | Takes the hue to create gradient for.
saturationGradient :: RGB -> Gradient
saturationGradient fullColor = Linear (linearGradientFromAngle 90.0
  [ colorStop (rgb 128 128 128) 0.0    -- Gray (0% saturation)
  , colorStop fullColor 1.0            -- Full color (100% saturation)
  ])

-- | Lightness gradient from black through color to white.
-- |
-- | Takes the hue to create gradient for.
lightnessGradient :: RGB -> Gradient
lightnessGradient midColor = Linear (linearGradientFromAngle 90.0
  [ colorStop (rgb 0 0 0) 0.0          -- Black (0% lightness)
  , colorStop midColor 0.5              -- Color (50% lightness)
  , colorStop (rgb 255 255 255) 1.0    -- White (100% lightness)
  ])

-- | Temperature gradient from warm to cool.
-- |
-- | Candlelight (1800K) → Daylight (6500K) → Blue sky (10000K)
temperatureGradient :: Gradient
temperatureGradient = Linear (linearGradientFromAngle 90.0
  [ colorStop (rgb 255 147 41) 0.0     -- Warm candlelight
  , colorStop (rgb 255 214 170) 0.25   -- Tungsten
  , colorStop (rgb 255 244 229) 0.5    -- Neutral
  , colorStop (rgb 201 226 255) 0.75   -- Cool daylight
  , colorStop (rgb 138 173 222) 1.0    -- Blue sky
  ])

-- | Checkerboard pattern for opacity slider background.
-- |
-- | Returns a fill representing the checkerboard (via noise or pattern).
checkerboardPattern :: Fill
checkerboardPattern = 
  -- Use a solid gray for now — full pattern would need Pattern fill with image
  fillSolid (rgb 204 204 204)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // preset layer stacks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue slider layers — rainbow gradient track.
hueSliderLayers :: SliderLayerStack
hueSliderLayers = defaultLayerStack
  { trackMaterial = trackMaterialLayer (fillGradient hueRainbowGradient)
  , progressMaterial = (defaultLayerStack.progressMaterial) { base { visible = false } }
  }

-- | Saturation slider layers — gray to color gradient.
saturationSliderLayers :: RGB -> SliderLayerStack
saturationSliderLayers color = defaultLayerStack
  { trackMaterial = trackMaterialLayer (fillGradient (saturationGradient color))
  , progressMaterial = (defaultLayerStack.progressMaterial) { base { visible = false } }
  }

-- | Lightness slider layers — black to white through color.
lightnessSliderLayers :: RGB -> SliderLayerStack
lightnessSliderLayers color = defaultLayerStack
  { trackMaterial = trackMaterialLayer (fillGradient (lightnessGradient color))
  , progressMaterial = (defaultLayerStack.progressMaterial) { base { visible = false } }
  }

-- | Volume slider layers — standard progress slider.
volumeSliderLayers :: SliderLayerStack
volumeSliderLayers = defaultLayerStack

-- | Opacity slider layers — checkerboard background.
opacitySliderLayers :: SliderLayerStack
opacitySliderLayers = defaultLayerStack
  { background = Just (backgroundLayer defaultTrackShape checkerboardPattern)
  }

-- | Temperature slider layers — warm to cool gradient.
temperatureSliderLayers :: SliderLayerStack
temperatureSliderLayers = defaultLayerStack
  { trackMaterial = trackMaterialLayer (fillGradient temperatureGradient)
  , progressMaterial = (defaultLayerStack.progressMaterial) { base { visible = false } }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shadow preset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default thumb shadow — subtle elevation.
-- |
-- | Two-layer shadow for realistic depth:
-- | - Soft ambient shadow
-- | - Directional key light shadow
defaultThumbShadow :: LayeredShadow
defaultThumbShadow = layered
  [ boxShadow
      { offsetX: 0.0
      , offsetY: 1.0
      , blur: 3.0
      , spread: 0.0
      , color: rgba 0 0 0 51    -- ~20% opacity
      , inset: false
      }
  , boxShadow
      { offsetX: 0.0
      , offsetY: 2.0
      , blur: 4.0
      , spread: -1.0
      , color: rgba 0 0 0 26    -- ~10% opacity
      , inset: false
      }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shape helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default corners for slider track — 4px radius on all corners.
-- |
-- | Uses Radius.Corners from Geometry.Radius for Shape primitives.
defaultCorners :: Radius.Corners
defaultCorners =
  { topLeft: Radius.px 4.0
  , topRight: Radius.px 4.0
  , bottomRight: Radius.px 4.0
  , bottomLeft: Radius.px 4.0
  }

-- | Pill corners — full radius (half of height).
-- |
-- | For a track of height h, radius = h/2 creates a pill shape.
pillCorners :: Number -> Radius.Corners
pillCorners halfHeight =
  { topLeft: Radius.px halfHeight
  , topRight: Radius.px halfHeight
  , bottomRight: Radius.px halfHeight
  , bottomLeft: Radius.px halfHeight
  }

-- | Square corners — no radius.
squareCorners :: Radius.Corners
squareCorners =
  { topLeft: Radius.px 0.0
  , topRight: Radius.px 0.0
  , bottomRight: Radius.px 0.0
  , bottomLeft: Radius.px 0.0
  }

-- | Create a track shape with given dimensions.
-- |
-- | Track is centered at (width/2, height/2) with given dimensions and corners.
trackShape :: Pixel -> Pixel -> Radius.Corners -> RectangleShape
trackShape width height corners = 
  let
    centerX = case width of Pixel w -> Pixel (w / 2.0)
    centerY = case height of Pixel h -> Pixel (h / 2.0)
  in
    rectangleShape { x: centerX, y: centerY } width height corners

-- | Create a thumb shape (circle) with given diameter.
-- |
-- | Thumb is centered at origin — position is controlled by the layer transform.
thumbShape :: Pixel -> EllipseShape
thumbShape diameter =
  let
    radius = case diameter of Pixel d -> Pixel (d / 2.0)
  in
    circleShape { x: Pixel 0.0, y: Pixel 0.0 } radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // default shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default track shape — 200×8px rounded rectangle.
-- |
-- | This is the standard horizontal slider track.
-- | For different sizes or shapes, create your own Shape and pass it to the
-- | layer constructors.
defaultTrackShape :: Shape
defaultTrackShape = ShapeRectangle (trackShape (Pixel 200.0) (Pixel 8.0) defaultCorners)

-- | Default thumb shape — 20px circle.
-- |
-- | This is the standard circular thumb.
-- | For star thumbs, gear thumbs, triangle thumbs — create your own Shape.
defaultThumbShape :: Shape
defaultThumbShape = ShapeEllipse (thumbShape (Pixel 20.0))

-- | Default focus ring shape — 24px circle (thumb + 2px offset each side).
-- |
-- | Focus ring is typically the thumb shape expanded slightly.
defaultFocusRingShape :: Shape
defaultFocusRingShape = ShapeEllipse (thumbShape (Pixel 24.0))
