-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // reactive // hovereffect
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
  , HoverTransform
  , hoverTransform
  , defaultHoverTransform
  
  -- * Style Effects
  , HoverStyle
  , hoverStyle
  , defaultHoverStyle
  
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // hover state
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // hover transform
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Transform applied on hover
data HoverTransform = HoverTransformPlaceholder

derive instance eqHoverTransform :: Eq HoverTransform

instance showHoverTransform :: Show HoverTransform where
  show _ = "HoverTransform"

-- | Create hover transform (placeholder)
hoverTransform :: HoverTransform
hoverTransform = HoverTransformPlaceholder

-- | Default hover transform (slight scale up)
defaultHoverTransform :: HoverTransform
defaultHoverTransform = HoverTransformPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // hover style
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Style changes on hover
data HoverStyle = HoverStylePlaceholder

derive instance eqHoverStyle :: Eq HoverStyle

instance showHoverStyle :: Show HoverStyle where
  show _ = "HoverStyle"

-- | Create hover style (placeholder)
hoverStyle :: HoverStyle
hoverStyle = HoverStylePlaceholder

-- | Default hover style
defaultHoverStyle :: HoverStyle
defaultHoverStyle = HoverStylePlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // hover audio
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Audio triggered on hover
data HoverAudio = HoverAudioPlaceholder

derive instance eqHoverAudio :: Eq HoverAudio

instance showHoverAudio :: Show HoverAudio where
  show _ = "HoverAudio"

-- | Create hover audio (placeholder)
hoverAudio :: HoverAudio
hoverAudio = HoverAudioPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // hover animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animation triggered on hover
data HoverAnimation = HoverAnimationPlaceholder

derive instance eqHoverAnimation :: Eq HoverAnimation

instance showHoverAnimation :: Show HoverAnimation where
  show _ = "HoverAnimation"

-- | Create hover animation (placeholder)
hoverAnimation :: HoverAnimation
hoverAnimation = HoverAnimationPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // hover particle
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Particle effect triggered on hover
data HoverParticle = HoverParticlePlaceholder

derive instance eqHoverParticle :: Eq HoverParticle

instance showHoverParticle :: Show HoverParticle where
  show _ = "HoverParticle"

-- | Create hover particle (placeholder)
hoverParticle :: HoverParticle
hoverParticle = HoverParticlePlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // hover effect
-- ═══════════════════════════════════════════════════════════════════════════════

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
