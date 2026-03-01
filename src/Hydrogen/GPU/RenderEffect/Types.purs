-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // render-effect/types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for the RenderEffect system.
-- |
-- | This module defines the foundational types used throughout the effect
-- | pipeline: effect pass specifications, blend modes, condition types,
-- | and the shared color type used by all effects.

module Hydrogen.GPU.RenderEffect.Types
  ( -- * Shared Color Type
    GlowColor
  
  -- * Effect Pass Types
  , EffectPass
  , PassInput(..)
  , PassOutput(..)
  , BlendMode(..)
  
  -- * Condition Types
  , EffectCondition(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shared color type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect color specification
-- |
-- | Used across all effect types for color definition. Represents RGBA color
-- | with integer RGB channels (0-255) and floating-point alpha (0.0-1.0).
type GlowColor =
  { r :: Int                 -- Red (0-255)
  , g :: Int                 -- Green (0-255)
  , b :: Int                 -- Blue (0-255)
  , a :: Number              -- Alpha (0.0-1.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // effect passes
-- ═════════════════════════════════════════════════════════════════════════════

-- Forward declaration needed for EffectPass - actual RenderEffect defined in Core
-- This is a type alias, so we use a placeholder that will be unified at import
type EffectPass =
  { input :: PassInput
  , output :: PassOutput
  , blendMode :: BlendMode
  }

-- | Input source for effect pass
data PassInput
  = InputPrevious           -- Output of previous pass
  | InputOriginal           -- Original unprocessed input
  | InputTexture Int        -- Named texture by ID
  | InputMultiple (Array PassInput)  -- Multiple inputs for composite

derive instance eqPassInput :: Eq PassInput

-- | Output target for effect pass
data PassOutput
  = OutputNext              -- Input for next pass
  | OutputFinal             -- Final output
  | OutputTexture Int       -- Named texture for later use
  | OutputScreen            -- Direct to screen

derive instance eqPassOutput :: Eq PassOutput

-- | Blend mode for compositing
data BlendMode
  = BlendNormal
  | BlendAdd
  | BlendMultiply
  | BlendScreen
  | BlendOverlay
  | BlendSoftLight
  | BlendHardLight
  | BlendDifference
  | BlendExclusion

derive instance eqBlendMode :: Eq BlendMode

instance showBlendMode :: Show BlendMode where
  show BlendNormal = "BlendNormal"
  show BlendAdd = "BlendAdd"
  show BlendMultiply = "BlendMultiply"
  show BlendScreen = "BlendScreen"
  show BlendOverlay = "BlendOverlay"
  show BlendSoftLight = "BlendSoftLight"
  show BlendHardLight = "BlendHardLight"
  show BlendDifference = "BlendDifference"
  show BlendExclusion = "BlendExclusion"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // effect conditions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Condition for conditional effects
-- |
-- | These conditions enable responsive effects that change based on user
-- | interaction or viewport state. At billion-agent scale, conditions must
-- | be deterministic — given the same FrameState, same result.
data EffectCondition
  = ConditionHover           -- Mouse over element
  | ConditionActive          -- Element is active (pressed)
  | ConditionFocus           -- Element has focus
  | ConditionAnimationPhase  -- Based on animation progress
      { minProgress :: Number
      , maxProgress :: Number
      }
  | ConditionViewportSize    -- Based on viewport dimensions
      { minWidth :: Number
      , minHeight :: Number
      }
  | ConditionAlways          -- Always true (for else branch)

derive instance eqEffectCondition :: Eq EffectCondition

instance showEffectCondition :: Show EffectCondition where
  show ConditionHover = "ConditionHover"
  show ConditionActive = "ConditionActive"
  show ConditionFocus = "ConditionFocus"
  show (ConditionAnimationPhase _) = "(ConditionAnimationPhase ...)"
  show (ConditionViewportSize _) = "(ConditionViewportSize ...)"
  show ConditionAlways = "ConditionAlways"
