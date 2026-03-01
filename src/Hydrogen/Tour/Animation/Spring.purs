-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // tour // animation // spring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spring Physics Configuration
-- |
-- | This module provides spring physics configuration for animations.
-- | Springs provide natural-feeling motion through damped harmonic oscillation.
-- |
-- | ## Physics Model
-- |
-- | The spring model is based on Hooke's Law with damping:
-- | - Stiffness (k): How "tight" the spring is
-- | - Damping (c): How much resistance to motion
-- | - Mass (m): How heavy the object feels
-- |
-- | ## Presets
-- |
-- | Named presets provide common spring behaviors:
-- | - Default: Balanced, general purpose
-- | - Snappy: Quick response, UI interactions
-- | - Gentle: Smooth, page transitions
-- | - Bouncy: Playful, attention-getting
-- | - Stiff: Immediate, toggles and switches

module Hydrogen.Tour.Animation.Spring
  ( -- * Construction
    springConfig
    -- * Presets
  , springPreset
  , springDefault
  , springSnappy
  , springGentle
  , springBouncy
  , springStiff
    -- * Re-exports
  , module Types
  ) where

import Prelude
  ( otherwise
  , (<)
  , (>)
  )

import Hydrogen.Tour.Animation.Types
  ( SpringConfig
  , SpringPreset(SpringDefault, SpringSnappy, SpringGentle, SpringBouncy, SpringStiff)
  ) as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create spring configuration with validation
-- |
-- | Clamps values to valid ranges to ensure stable physics simulation.
springConfig
  :: { stiffness :: Number, damping :: Number, mass :: Number }
  -> Types.SpringConfig
springConfig { stiffness, damping, mass } =
  { stiffness: clampRange 1.0 1000.0 stiffness
  , damping: clampRange 1.0 100.0 damping
  , mass: clampRange 0.1 10.0 mass
  , velocity: 0.0
  , precision: 0.01
  }
  where
  clampRange :: Number -> Number -> Number -> Number
  clampRange minVal maxVal val
    | val < minVal = minVal
    | val > maxVal = maxVal
    | otherwise = val

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert preset to spring config
springPreset :: Types.SpringPreset -> Types.SpringConfig
springPreset = case _ of
  Types.SpringDefault -> springDefault
  Types.SpringSnappy -> springSnappy
  Types.SpringGentle -> springGentle
  Types.SpringBouncy -> springBouncy
  Types.SpringStiff -> springStiff

-- | Default spring (balanced)
-- |
-- | Good for general-purpose animations. Similar to React Spring defaults.
springDefault :: Types.SpringConfig
springDefault = springConfig { stiffness: 170.0, damping: 26.0, mass: 1.0 }

-- | Snappy spring (quick, minimal bounce)
-- |
-- | Ideal for UI interactions like button presses and menu reveals.
springSnappy :: Types.SpringConfig
springSnappy = springConfig { stiffness: 300.0, damping: 30.0, mass: 1.0 }

-- | Gentle spring (smooth, slower)
-- |
-- | Good for page transitions and modal entrances.
springGentle :: Types.SpringConfig
springGentle = springConfig { stiffness: 120.0, damping: 14.0, mass: 1.0 }

-- | Bouncy spring (playful)
-- |
-- | Use for attention-getting animations and playful UI elements.
springBouncy :: Types.SpringConfig
springBouncy = springConfig { stiffness: 180.0, damping: 12.0, mass: 1.0 }

-- | Stiff spring (immediate)
-- |
-- | For toggle switches and immediate feedback.
springStiff :: Types.SpringConfig
springStiff = springConfig { stiffness: 400.0, damping: 40.0, mass: 1.0 }
