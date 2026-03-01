-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // render-effect/glow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Glow effects for the RenderEffect system.
-- |
-- | Provides four glow variants for different visual needs:
-- | - **Inner**: Glow inside element edges (depth effect)
-- | - **Outer**: Glow outside element edges (selection, hover)
-- | - **Pulsing**: Animated intensity for attention
-- | - **Neon**: Multi-layer vibrant glow (cyberpunk aesthetic)

module Hydrogen.GPU.RenderEffect.Glow
  ( -- * Glow Effect Type
    GlowEffect(..)
  
  -- * Glow Variants
  , InnerGlow(..)
  , OuterGlow(..)
  , PulsingGlow(..)
  , NeonGlow(..)
  
  -- * Glow Configuration
  , GlowEasing(..)
  
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
--                                                               // glow effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect variants
-- |
-- | Glows are implemented as blurred alpha-masked layers composited
-- | with the source. Each variant optimizes for specific visual needs.
data GlowEffect
  = GlowInner InnerGlow
  | GlowOuter OuterGlow
  | GlowPulsing PulsingGlow
  | GlowNeon NeonGlow

derive instance eqGlowEffect :: Eq GlowEffect

instance showGlowEffect :: Show GlowEffect where
  show (GlowInner g) = "(GlowInner " <> show g <> ")"
  show (GlowOuter g) = "(GlowOuter " <> show g <> ")"
  show (GlowPulsing g) = "(GlowPulsing " <> show g <> ")"
  show (GlowNeon g) = "(GlowNeon " <> show g <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glow variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inner glow — glow inside element edges
-- |
-- | Creates depth and dimension by lighting the interior edges.
-- | Choke controls how sharply the glow follows the edge contour.
newtype InnerGlow = InnerGlow
  { color :: GlowColor
  , radius :: Number         -- Glow radius in pixels
  , intensity :: Number      -- Glow intensity (0.0-1.0)
  , choke :: Number          -- Edge definition (0.0-1.0)
  }

derive instance eqInnerGlow :: Eq InnerGlow

instance showInnerGlow :: Show InnerGlow where
  show (InnerGlow g) = "(InnerGlow radius:" <> show g.radius <> ")"

-- | Outer glow — glow outside element edges
-- |
-- | Standard selection/hover glow. Spread controls how far the glow
-- | extends before fading.
newtype OuterGlow = OuterGlow
  { color :: GlowColor
  , radius :: Number
  , intensity :: Number
  , spread :: Number         -- How far glow spreads (0.0-1.0)
  }

derive instance eqOuterGlow :: Eq OuterGlow

instance showOuterGlow :: Show OuterGlow where
  show (OuterGlow g) = "(OuterGlow radius:" <> show g.radius <> ")"

-- | Pulsing glow — animated intensity
-- |
-- | Oscillates between min and max values over time. Animation state
-- | comes from FrameState, making the effect deterministic and replay-safe.
newtype PulsingGlow = PulsingGlow
  { color :: GlowColor
  , minRadius :: Number
  , maxRadius :: Number
  , minIntensity :: Number
  , maxIntensity :: Number
  , periodMs :: Number       -- Pulse period in milliseconds
  , easing :: GlowEasing
  }

derive instance eqPulsingGlow :: Eq PulsingGlow

instance showPulsingGlow :: Show PulsingGlow where
  show (PulsingGlow g) = "(PulsingGlow period:" <> show g.periodMs <> ")"

-- | Neon glow — multi-layer vibrant glow
-- |
-- | Two-layer glow with distinct core and outer colors for that
-- | classic neon tube aesthetic. Optional flicker adds randomness.
newtype NeonGlow = NeonGlow
  { coreColor :: GlowColor   -- Inner core color
  , outerColor :: GlowColor  -- Outer glow color
  , coreRadius :: Number
  , outerRadius :: Number
  , intensity :: Number
  , flicker :: Boolean       -- Random intensity variation
  , flickerSpeed :: Number   -- Flicker rate if enabled
  }

derive instance eqNeonGlow :: Eq NeonGlow

instance showNeonGlow :: Show NeonGlow where
  show (NeonGlow g) = "(NeonGlow intensity:" <> show g.intensity <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // glow configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow easing type
-- |
-- | Controls how pulsing glows interpolate between min and max values.
data GlowEasing
  = GlowEaseLinear
  | GlowEaseSine
  | GlowEaseQuad
  | GlowEaseCubic

derive instance eqGlowEasing :: Eq GlowEasing
