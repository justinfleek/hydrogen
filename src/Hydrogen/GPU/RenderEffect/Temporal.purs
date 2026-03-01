-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // render-effect/temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temporal effects for the RenderEffect system.
-- |
-- | Provides three time-based variants:
-- | - **MotionBlur**: Blur in direction of motion (shutter simulation)
-- | - **Echo**: Ghosting/trails (temporal accumulation)
-- | - **TimeWarp**: Time displacement effect (glitch aesthetic)

module Hydrogen.GPU.RenderEffect.Temporal
  ( -- * Temporal Effect Type
    TemporalEffect(..)
  
  -- * Temporal Variants
  , MotionBlur(..)
  , EchoEffect(..)
  , TimeWarp(..)
  
  -- * Temporal Configuration
  , EchoOperator(..)
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // temporal effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal effect variants
-- |
-- | Temporal effects operate across multiple frames, requiring frame history
-- | or motion vectors. The runtime manages temporal buffers; effects remain
-- | pure functions of FrameState.
data TemporalEffect
  = TemporalMotionBlur MotionBlur
  | TemporalEcho EchoEffect
  | TemporalTimeWarp TimeWarp

derive instance eqTemporalEffect :: Eq TemporalEffect

instance showTemporalEffect :: Show TemporalEffect where
  show (TemporalMotionBlur t) = "(TemporalMotionBlur " <> show t <> ")"
  show (TemporalEcho t) = "(TemporalEcho " <> show t <> ")"
  show (TemporalTimeWarp t) = "(TemporalTimeWarp " <> show t <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // temporal variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion blur — blur in direction of motion
-- |
-- | Simulates camera shutter blur. Samples are taken along the motion
-- | vector and blended. Shutter angle controls blur duration relative
-- | to frame time (180° = half frame, 360° = full frame).
newtype MotionBlur = MotionBlur
  { samples :: Int           -- Number of temporal samples
  , shutterAngle :: Number   -- Shutter angle in degrees (0-360)
  }

derive instance eqMotionBlur :: Eq MotionBlur

instance showMotionBlur :: Show MotionBlur where
  show (MotionBlur t) = "(MotionBlur samples:" <> show t.samples <> ")"

-- | Echo effect — ghosting/trails
-- |
-- | Retains and blends previous frames to create trails or ghosting.
-- | Delay controls frame spacing; decay controls opacity falloff.
newtype EchoEffect = EchoEffect
  { count :: Int             -- Number of echoes
  , delay :: Number          -- Delay between echoes (frames)
  , decay :: Number          -- Opacity decay per echo (0.0-1.0)
  , operator :: EchoOperator
  }

derive instance eqEchoEffect :: Eq EchoEffect

instance showEchoEffect :: Show EchoEffect where
  show (EchoEffect t) = "(EchoEffect count:" <> show t.count <> ")"

-- | Time warp — time displacement effect
-- |
-- | Samples different time offsets at different spatial positions,
-- | creating a glitchy temporal displacement. Noise controls the
-- | spatial variation of time offset.
newtype TimeWarp = TimeWarp
  { displacement :: Number   -- Time offset amount
  , noiseScale :: Number     -- Spatial frequency of displacement
  , animated :: Boolean      -- Animate displacement pattern
  }

derive instance eqTimeWarp :: Eq TimeWarp

instance showTimeWarp :: Show TimeWarp where
  show (TimeWarp t) = "(TimeWarp displacement:" <> show t.displacement <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // temporal configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Echo blend operator
-- |
-- | Controls how echoes are composited together:
-- | - **Add**: Additive blending (bright trails)
-- | - **Screen**: Screen blending (soft glow trails)
-- | - **Maximum**: Keep brightest pixel
-- | - **Minimum**: Keep darkest pixel
-- | - **Blend**: Standard alpha blending
data EchoOperator
  = EchoAdd
  | EchoScreen
  | EchoMaximum
  | EchoMinimum
  | EchoBlend

derive instance eqEchoOperator :: Eq EchoOperator
