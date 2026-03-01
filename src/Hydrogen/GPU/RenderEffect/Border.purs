-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // render-effect/border
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Border effects for the RenderEffect system.
-- |
-- | Provides four border variants for dynamic edge styling:
-- | - **Gradient**: Fill stroke with linear/radial/conic gradient
-- | - **Conic**: Linear-style rotating spotlight border
-- | - **AnimatedDash**: Marching ants, flowing energy
-- | - **Glowing**: Border with outer glow halo

module Hydrogen.GPU.RenderEffect.Border
  ( -- * Border Effect Type
    BorderEffect(..)
  
  -- * Border Variants
  , GradientBorder(..)
  , ConicBorder(..)
  , AnimatedDashBorder(..)
  , GlowingBorder(..)
  
  -- * Border Configuration
  , BorderGradientType(..)
  , DashDirection(..)
  
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.RenderEffect.Types (GlowColor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // border effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border effect variants
-- |
-- | Borders are rendered as stroke operations with various fill patterns.
-- | Animated variants receive time from FrameState for determinism.
data BorderEffect
  = BorderGradient GradientBorder
  | BorderConic ConicBorder
  | BorderAnimatedDash AnimatedDashBorder
  | BorderGlowing GlowingBorder

derive instance eqBorderEffect :: Eq BorderEffect

instance showBorderEffect :: Show BorderEffect where
  show (BorderGradient b) = "(BorderGradient " <> show b <> ")"
  show (BorderConic b) = "(BorderConic " <> show b <> ")"
  show (BorderAnimatedDash b) = "(BorderAnimatedDash " <> show b <> ")"
  show (BorderGlowing b) = "(BorderGlowing " <> show b <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // border variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gradient border — fill stroke with gradient
-- |
-- | Supports linear, radial, and conic gradients. Colors are sampled
-- | along the gradient and mapped to the stroke path.
newtype GradientBorder = GradientBorder
  { width :: Number          -- Border width in pixels
  , gradientType :: BorderGradientType
  , colors :: Array GlowColor
  , angle :: Number          -- Gradient angle for linear (degrees)
  }

derive instance eqGradientBorder :: Eq GradientBorder

instance showGradientBorder :: Show GradientBorder where
  show (GradientBorder b) = "(GradientBorder width:" <> show b.width <> ")"

-- | Conic border — Linear-style rotating gradient
-- |
-- | The signature effect from Linear app: a conic gradient that rotates
-- | around the element, optionally tracking the mouse cursor for spotlight.
newtype ConicBorder = ConicBorder
  { width :: Number
  , colors :: Array GlowColor
  , rotationSpeed :: Number  -- Degrees per second (0 = static)
  , blurRadius :: Number     -- Glow around border
  , mouseTracking :: Boolean -- Follow mouse position
  , spotlightAngle :: Number -- Spotlight cone width (degrees)
  }

derive instance eqConicBorder :: Eq ConicBorder

instance showConicBorder :: Show ConicBorder where
  show (ConicBorder b) = "(ConicBorder speed:" <> show b.rotationSpeed <> ")"

-- | Animated dash border — marching ants, flowing energy
-- |
-- | Dashed stroke with animated offset. Direction controls whether
-- | dashes move forward, backward, or alternate.
newtype AnimatedDashBorder = AnimatedDashBorder
  { width :: Number
  , dashLength :: Number
  , gapLength :: Number
  , speed :: Number          -- Pixels per second
  , direction :: DashDirection
  , color :: GlowColor
  }

derive instance eqAnimatedDashBorder :: Eq AnimatedDashBorder

instance showAnimatedDashBorder :: Show AnimatedDashBorder where
  show (AnimatedDashBorder b) = "(AnimatedDashBorder speed:" <> show b.speed <> ")"

-- | Glowing border — border with outer glow
-- |
-- | Solid stroke with a soft glow halo. Optional pulsing animation
-- | for attention-grabbing effects.
newtype GlowingBorder = GlowingBorder
  { width :: Number
  , borderColor :: GlowColor
  , glowColor :: GlowColor
  , glowRadius :: Number
  , glowIntensity :: Number
  , animated :: Boolean      -- Pulse glow
  , pulseSpeed :: Number     -- Pulse period in ms
  }

derive instance eqGlowingBorder :: Eq GlowingBorder

instance showGlowingBorder :: Show GlowingBorder where
  show (GlowingBorder b) = "(GlowingBorder width:" <> show b.width <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // border configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border gradient type
data BorderGradientType
  = BorderGradientLinear
  | BorderGradientRadial
  | BorderGradientConic

derive instance eqBorderGradientType :: Eq BorderGradientType

-- | Dash animation direction
data DashDirection
  = DashDirectionForward
  | DashDirectionBackward
  | DashDirectionAlternate

derive instance eqDashDirection :: Eq DashDirection
