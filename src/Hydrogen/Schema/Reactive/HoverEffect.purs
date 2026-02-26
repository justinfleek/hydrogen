-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // reactive // hover-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverEffect — Interactive hover behaviors for UI elements.
-- |
-- | ## Design Philosophy
-- |
-- | Hover effects are declarative descriptions of what happens when a user
-- | hovers over an element. The runtime interprets these into actual
-- | event handlers and animations.
-- |
-- | ## Effect Categories
-- |
-- | - **Transform**: Scale, translate, rotate on hover
-- | - **Style**: Color, opacity, filter changes
-- | - **Audio**: Sound triggers on enter/leave
-- | - **Animation**: Lottie/CSS animation triggers
-- | - **Particle**: Particle burst effects
-- |
-- | ## State Machine
-- |
-- | ```
-- | idle → entering → hovering → leaving → idle
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Temporal (timing)
-- | - Schema.Color.RGB (color changes)
-- | - Schema.Motion.Easing (transition curves)

module Hydrogen.Schema.Reactive.HoverEffect
  ( -- * Hover State
    HoverState
      ( HoverIdle
      , HoverEntering
      , HoverActive
      , HoverLeaving
      )
  
  -- * Transform Effects
  , HoverTransform(..)
  , TransformOrigin(..)
  , hoverTransform
  , identityTransform
  , defaultHoverTransform
  , liftTransform
  , pressTransform
  , scaleUpTransform
  , elevatedHoverTransform
  
  -- * Style Effects
  , HoverStyle(..)
  , OpacityChange(..)
  , hoverStyle
  , identityStyle
  , defaultHoverStyle
  , subtleHoverStyle
  , prominentHoverStyle
  , glowHoverStyle
  , dimHoverStyle
  
  -- * Audio Trigger
  , HoverAudio
  , hoverAudio
  
  -- * Animation Trigger
  , HoverAnimation
  , hoverAnimation
  
  -- * Particle Trigger
  , HoverParticle
  , hoverParticle
  
  -- * Combined Hover Effect
  , HoverEffect
  , hoverEffect
  , defaultHoverEffect
  , noHoverEffect
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
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current hover state of an element
data HoverState
  = HoverIdle       -- ^ Not being hovered
  | HoverEntering   -- ^ Mouse just entered, transition starting
  | HoverActive     -- ^ Actively being hovered
  | HoverLeaving    -- ^ Mouse just left, transition ending

derive instance eqHoverState :: Eq HoverState
derive instance ordHoverState :: Ord HoverState

instance showHoverState :: Show HoverState where
  show HoverIdle = "idle"
  show HoverEntering = "entering"
  show HoverActive = "active"
  show HoverLeaving = "leaving"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hover transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform applied on hover
-- |
-- | Based on research from Linear, Vercel, and Apple design systems:
-- | - Best timing: 100-200ms
-- | - Optimal hover lift: translateY(-1px) + subtle shadow increase
-- | - Active state: scale(0.98) for tactile feedback
-- | - Use easeOut for enter, easeIn for exit
-- |
-- | ## Transform Properties
-- |
-- | - **translateX/Y**: Pixel offset (negative Y = lift effect)
-- | - **scale**: Uniform scale factor (1.0 = no change)
-- | - **scaleX/Y**: Non-uniform scale
-- | - **rotate**: Rotation in degrees
-- | - **skewX/Y**: Skew angles in degrees
newtype HoverTransform = HoverTransform
  { translateX :: Number     -- ^ Horizontal offset in pixels
  , translateY :: Number     -- ^ Vertical offset in pixels (negative = lift)
  , scale :: Number          -- ^ Uniform scale factor (1.0 = normal)
  , scaleX :: Number         -- ^ Horizontal scale factor
  , scaleY :: Number         -- ^ Vertical scale factor
  , rotate :: Number         -- ^ Rotation in degrees
  , skewX :: Number          -- ^ Horizontal skew in degrees
  , skewY :: Number          -- ^ Vertical skew in degrees
  , transformOrigin :: TransformOrigin -- ^ Origin point for transforms
  }

derive instance eqHoverTransform :: Eq HoverTransform

instance showHoverTransform :: Show HoverTransform where
  show (HoverTransform t) = 
    "HoverTransform(" <>
    "translateY:" <> show t.translateY <>
    ", scale:" <> show t.scale <> ")"

-- | Transform origin point
data TransformOrigin
  = OriginCenter        -- ^ Center of element (default)
  | OriginTop           -- ^ Top center
  | OriginBottom        -- ^ Bottom center
  | OriginLeft          -- ^ Left center
  | OriginRight         -- ^ Right center
  | OriginTopLeft       -- ^ Top left corner
  | OriginTopRight      -- ^ Top right corner
  | OriginBottomLeft    -- ^ Bottom left corner
  | OriginBottomRight   -- ^ Bottom right corner
  | OriginCustom Number Number -- ^ Custom X Y percentages (0-100)

derive instance eqTransformOrigin :: Eq TransformOrigin

instance showTransformOrigin :: Show TransformOrigin where
  show OriginCenter = "center"
  show OriginTop = "top"
  show OriginBottom = "bottom"
  show OriginLeft = "left"
  show OriginRight = "right"
  show OriginTopLeft = "top-left"
  show OriginTopRight = "top-right"
  show OriginBottomLeft = "bottom-left"
  show OriginBottomRight = "bottom-right"
  show (OriginCustom x y) = show x <> "% " <> show y <> "%"

-- | Identity transform (no change)
identityTransform :: HoverTransform
identityTransform = HoverTransform
  { translateX: 0.0
  , translateY: 0.0
  , scale: 1.0
  , scaleX: 1.0
  , scaleY: 1.0
  , rotate: 0.0
  , skewX: 0.0
  , skewY: 0.0
  , transformOrigin: OriginCenter
  }

-- | Create hover transform with specified values
hoverTransform 
  :: { translateY :: Number, scale :: Number } 
  -> HoverTransform
hoverTransform { translateY: ty, scale: s } = HoverTransform
  { translateX: 0.0
  , translateY: ty
  , scale: s
  , scaleX: 1.0
  , scaleY: 1.0
  , rotate: 0.0
  , skewX: 0.0
  , skewY: 0.0
  , transformOrigin: OriginCenter
  }

-- | Default hover transform (slight lift - Linear/Vercel style)
-- |
-- | Research finding: translateY(-1px) provides subtle lift effect
-- | that feels tactile without being jarring
defaultHoverTransform :: HoverTransform
defaultHoverTransform = hoverTransform { translateY: (-1.0), scale: 1.0 }

-- | Lift transform for button hover (raises element)
liftTransform :: HoverTransform
liftTransform = hoverTransform { translateY: (-2.0), scale: 1.0 }

-- | Press transform for active state (slight scale down)
-- |
-- | Research finding: scale(0.98) provides tactile press feedback
pressTransform :: HoverTransform
pressTransform = hoverTransform { translateY: 0.0, scale: 0.98 }

-- | Scale up transform (grow on hover)
scaleUpTransform :: HoverTransform
scaleUpTransform = hoverTransform { translateY: 0.0, scale: 1.02 }

-- | Combined lift and scale for elevated buttons
elevatedHoverTransform :: HoverTransform
elevatedHoverTransform = hoverTransform { translateY: (-2.0), scale: 1.01 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style changes on hover
-- |
-- | Describes visual property changes that occur during hover:
-- | - Opacity adjustments
-- | - Background color changes
-- | - Border color changes
-- | - Shadow intensity changes
-- | - Filter effects (brightness, saturation)
-- |
-- | ## Layered Shadows on Hover
-- |
-- | Research finding: best hover shadows use multiple layers:
-- | - Base shadow stays constant
-- | - Additional "lift" shadow appears on hover
-- | - Creates more realistic depth perception
newtype HoverStyle = HoverStyle
  { opacity :: OpacityChange        -- ^ Opacity adjustment
  , brightness :: Number            -- ^ Filter brightness (1.0 = normal)
  , saturation :: Number            -- ^ Filter saturation (1.0 = normal)
  , contrast :: Number              -- ^ Filter contrast (1.0 = normal)
  , shadowIntensity :: Number       -- ^ Shadow opacity multiplier (1.0 = normal)
  , shadowSpread :: Number          -- ^ Additional shadow spread in pixels
  , backgroundLighten :: Number     -- ^ Background lightness adjustment (-100 to 100)
  , borderLighten :: Number         -- ^ Border lightness adjustment (-100 to 100)
  }

derive instance eqHoverStyle :: Eq HoverStyle

instance showHoverStyle :: Show HoverStyle where
  show (HoverStyle s) = 
    "HoverStyle(brightness:" <> show s.brightness <> 
    ", shadowIntensity:" <> show s.shadowIntensity <> ")"

-- | Opacity change modes
data OpacityChange
  = OpacityAbsolute Number  -- ^ Set to specific opacity (0.0-1.0)
  | OpacityRelative Number  -- ^ Multiply current opacity
  | OpacityUnchanged        -- ^ Keep current opacity

derive instance eqOpacityChange :: Eq OpacityChange

instance showOpacityChange :: Show OpacityChange where
  show (OpacityAbsolute v) = "opacity:" <> show v
  show (OpacityRelative v) = "opacity*" <> show v
  show OpacityUnchanged = "opacity:unchanged"

-- | Create hover style with common options
hoverStyle 
  :: { brightness :: Number, shadowIntensity :: Number }
  -> HoverStyle
hoverStyle { brightness: b, shadowIntensity: si } = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: b
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: si
  , shadowSpread: 0.0
  , backgroundLighten: 0.0
  , borderLighten: 0.0
  }

-- | Identity style (no visual changes)
identityStyle :: HoverStyle
identityStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.0
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.0
  , shadowSpread: 0.0
  , backgroundLighten: 0.0
  , borderLighten: 0.0
  }

-- | Default hover style (subtle brightness increase + shadow lift)
-- |
-- | Research finding: 5-10% brightness increase is perceptible
-- | but not jarring. Shadow increase of 20-30% adds depth.
defaultHoverStyle :: HoverStyle
defaultHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.05
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.25
  , shadowSpread: 2.0
  , backgroundLighten: 3.0
  , borderLighten: 0.0
  }

-- | Subtle hover style (minimal change)
subtleHoverStyle :: HoverStyle
subtleHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.02
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.1
  , shadowSpread: 1.0
  , backgroundLighten: 2.0
  , borderLighten: 0.0
  }

-- | Prominent hover style (more noticeable)
prominentHoverStyle :: HoverStyle
prominentHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.1
  , saturation: 1.05
  , contrast: 1.0
  , shadowIntensity: 1.5
  , shadowSpread: 4.0
  , backgroundLighten: 5.0
  , borderLighten: 5.0
  }

-- | Glow hover style (emissive appearance)
glowHoverStyle :: HoverStyle
glowHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.15
  , saturation: 1.1
  , contrast: 1.0
  , shadowIntensity: 2.0
  , shadowSpread: 8.0
  , backgroundLighten: 0.0
  , borderLighten: 10.0
  }

-- | Dim hover style (for secondary elements)
dimHoverStyle :: HoverStyle
dimHoverStyle = HoverStyle
  { opacity: OpacityRelative 0.7
  , brightness: 0.95
  , saturation: 0.9
  , contrast: 1.0
  , shadowIntensity: 0.8
  , shadowSpread: 0.0
  , backgroundLighten: (-3.0)
  , borderLighten: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover audio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio triggered on hover
data HoverAudio = HoverAudioPlaceholder

derive instance eqHoverAudio :: Eq HoverAudio

instance showHoverAudio :: Show HoverAudio where
  show _ = "HoverAudio"

-- | Create hover audio (placeholder)
hoverAudio :: HoverAudio
hoverAudio = HoverAudioPlaceholder

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hover animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation triggered on hover
data HoverAnimation = HoverAnimationPlaceholder

derive instance eqHoverAnimation :: Eq HoverAnimation

instance showHoverAnimation :: Show HoverAnimation where
  show _ = "HoverAnimation"

-- | Create hover animation (placeholder)
hoverAnimation :: HoverAnimation
hoverAnimation = HoverAnimationPlaceholder

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover particle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle effect triggered on hover
data HoverParticle = HoverParticlePlaceholder

derive instance eqHoverParticle :: Eq HoverParticle

instance showHoverParticle :: Show HoverParticle where
  show _ = "HoverParticle"

-- | Create hover particle (placeholder)
hoverParticle :: HoverParticle
hoverParticle = HoverParticlePlaceholder

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined hover effect configuration
data HoverEffect = HoverEffectPlaceholder

derive instance eqHoverEffect :: Eq HoverEffect

instance showHoverEffect :: Show HoverEffect where
  show _ = "HoverEffect"

-- | Create hover effect (placeholder)
hoverEffect :: HoverEffect
hoverEffect = HoverEffectPlaceholder

-- | Default hover effect (subtle scale + opacity)
defaultHoverEffect :: HoverEffect
defaultHoverEffect = HoverEffectPlaceholder

-- | No hover effect
noHoverEffect :: HoverEffect
noHoverEffect = HoverEffectPlaceholder
