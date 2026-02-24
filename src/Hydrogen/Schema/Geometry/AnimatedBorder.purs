-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // geometry // animatedborder
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AnimatedBorder — Dynamic border effects for interactive UI.
-- |
-- | ## Design Philosophy
-- |
-- | Static borders (Geometry.Border) handle CSS box borders.
-- | This module extends that with ANIMATED borders:
-- | - Gradient strokes (fill stroke with color gradient)
-- | - Animated dash patterns (marching ants, flowing energy)
-- | - Pulsing strokes (width oscillation over time)
-- | - Glowing strokes (animated outer glow)
-- |
-- | These are SVG/Canvas-native effects. CSS borders don't support them.
-- | The runtime interprets these as SVG stroke properties or Canvas calls.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Color.Gradient (gradient fills for strokes)
-- | - Schema.Geometry.Stroke (line caps, joins)
-- | - Schema.Dimension.Device (Pixel)
-- | - Schema.Dimension.Temporal (Milliseconds for animation timing)

module Hydrogen.Schema.Geometry.AnimatedBorder
  ( -- * Gradient Stroke
    GradientStroke
  , gradientStroke
  
  -- * Animated Dash
  , DashPattern
  , dashPattern
  , DashAnimation
  , dashAnimation
  , AnimatedDash
  , animatedDash
  
  -- * Pulsing Stroke
  , PulseConfig
  , pulseConfig
  , PulsingStroke
  , pulsingStroke
  
  -- * Glowing Stroke
  , GlowConfig
  , glowConfig
  , GlowingStroke
  , glowingStroke
  
  -- * Combined Animated Border
  , AnimatedBorder
  , animatedBorder
  , defaultAnimatedBorder
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // gradient stroke
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Placeholder for GradientStroke
data GradientStroke = GradientStrokePlaceholder

derive instance eqGradientStroke :: Eq GradientStroke

instance showGradientStroke :: Show GradientStroke where
  show _ = "GradientStroke"

-- | Create gradient stroke (placeholder)
gradientStroke :: GradientStroke
gradientStroke = GradientStrokePlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // animated dash
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Placeholder for DashPattern
data DashPattern = DashPatternPlaceholder

derive instance eqDashPattern :: Eq DashPattern

instance showDashPattern :: Show DashPattern where
  show _ = "DashPattern"

-- | Create dash pattern (placeholder)
dashPattern :: DashPattern
dashPattern = DashPatternPlaceholder

-- | Placeholder for DashAnimation
data DashAnimation = DashAnimationPlaceholder

derive instance eqDashAnimation :: Eq DashAnimation

instance showDashAnimation :: Show DashAnimation where
  show _ = "DashAnimation"

-- | Create dash animation (placeholder)
dashAnimation :: DashAnimation
dashAnimation = DashAnimationPlaceholder

-- | Placeholder for AnimatedDash
data AnimatedDash = AnimatedDashPlaceholder

derive instance eqAnimatedDash :: Eq AnimatedDash

instance showAnimatedDash :: Show AnimatedDash where
  show _ = "AnimatedDash"

-- | Create animated dash (placeholder)
animatedDash :: AnimatedDash
animatedDash = AnimatedDashPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // pulsing stroke
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Placeholder for PulseConfig
data PulseConfig = PulseConfigPlaceholder

derive instance eqPulseConfig :: Eq PulseConfig

instance showPulseConfig :: Show PulseConfig where
  show _ = "PulseConfig"

-- | Create pulse config (placeholder)
pulseConfig :: PulseConfig
pulseConfig = PulseConfigPlaceholder

-- | Placeholder for PulsingStroke
data PulsingStroke = PulsingStrokePlaceholder

derive instance eqPulsingStroke :: Eq PulsingStroke

instance showPulsingStroke :: Show PulsingStroke where
  show _ = "PulsingStroke"

-- | Create pulsing stroke (placeholder)
pulsingStroke :: PulsingStroke
pulsingStroke = PulsingStrokePlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // glowing stroke
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Placeholder for GlowConfig
data GlowConfig = GlowConfigPlaceholder

derive instance eqGlowConfig :: Eq GlowConfig

instance showGlowConfig :: Show GlowConfig where
  show _ = "GlowConfig"

-- | Create glow config (placeholder)
glowConfig :: GlowConfig
glowConfig = GlowConfigPlaceholder

-- | Placeholder for GlowingStroke
data GlowingStroke = GlowingStrokePlaceholder

derive instance eqGlowingStroke :: Eq GlowingStroke

instance showGlowingStroke :: Show GlowingStroke where
  show _ = "GlowingStroke"

-- | Create glowing stroke (placeholder)
glowingStroke :: GlowingStroke
glowingStroke = GlowingStrokePlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // animated border
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Placeholder for AnimatedBorder
data AnimatedBorder = AnimatedBorderPlaceholder

derive instance eqAnimatedBorder :: Eq AnimatedBorder

instance showAnimatedBorder :: Show AnimatedBorder where
  show _ = "AnimatedBorder"

-- | Create animated border (placeholder)
animatedBorder :: AnimatedBorder
animatedBorder = AnimatedBorderPlaceholder

-- | Default animated border (placeholder)
defaultAnimatedBorder :: AnimatedBorder
defaultAnimatedBorder = AnimatedBorderPlaceholder
