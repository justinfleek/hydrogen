-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // render-effect/core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core RenderEffect type and composition functions.
-- |
-- | This module defines the main RenderEffect ADT that unifies all effect
-- | categories, plus composition combinators for building complex effects
-- | from simpler ones.

module Hydrogen.GPU.RenderEffect.Core
  ( -- * Core Effect Type
    RenderEffect(EffectBlur, EffectGlow, EffectShadow, EffectBorder, EffectMaterial, EffectTemporal, EffectParticle, EffectSequence, EffectParallel, EffectConditional, EffectAnimated, EffectNone)
   
  -- * Effect Composition
  , effectSequence
  , effectParallel
  , effectConditional
  , effectWhen
  , effectIfThenElse
  , effectAnimated
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

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.GPU.RenderEffect.Types (EffectCondition)
import Hydrogen.GPU.RenderEffect.Blur (BlurEffect)
import Hydrogen.GPU.RenderEffect.Glow (GlowEffect)
import Hydrogen.GPU.RenderEffect.Shadow (ShadowEffect)
import Hydrogen.GPU.RenderEffect.Border (BorderEffect)
import Hydrogen.GPU.RenderEffect.Material (MaterialEffect)
import Hydrogen.GPU.RenderEffect.Temporal (TemporalEffect)
import Hydrogen.GPU.RenderEffect.Particle (ParticleEffect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // core effect type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A render effect — composable GPU operation.
-- |
-- | Effects are pure data describing visual transformations.
-- | The interpreter converts them to GPU render passes.
-- |
-- | ## Composition Model
-- |
-- | Effects compose in three ways:
-- | - **Sequence**: Apply effects one after another (chained textures)
-- | - **Parallel**: Apply effects simultaneously (blended output)
-- | - **Conditional**: Choose effects based on runtime state
-- |
-- | ## Determinism Guarantee
-- |
-- | Given the same RenderEffect value and FrameState, the output is
-- | identical. This enables billion-agent scale: agents can compute
-- | effect descriptions that produce predictable pixels.
data RenderEffect
  = EffectBlur BlurEffect
  | EffectGlow GlowEffect
  | EffectShadow ShadowEffect
  | EffectBorder BorderEffect
  | EffectMaterial MaterialEffect
  | EffectTemporal TemporalEffect
  | EffectParticle ParticleEffect
  | EffectSequence (Array RenderEffect)     -- Apply in order
  | EffectParallel (Array RenderEffect)     -- Apply simultaneously (blend)
  | EffectConditional                       -- Apply based on condition
      { condition :: EffectCondition
      , thenEffect :: RenderEffect
      , elseEffect :: Maybe RenderEffect
      }
  | EffectAnimated                          -- Interpolate between states
      { from :: RenderEffect
      , to :: RenderEffect
      , progress :: Number                  -- 0.0-1.0
      }
  | EffectNone                              -- Identity (no effect)

derive instance eqRenderEffect :: Eq RenderEffect

instance showRenderEffect :: Show RenderEffect where
  show (EffectBlur b) = "(EffectBlur " <> show b <> ")"
  show (EffectGlow g) = "(EffectGlow " <> show g <> ")"
  show (EffectShadow s) = "(EffectShadow " <> show s <> ")"
  show (EffectBorder b) = "(EffectBorder " <> show b <> ")"
  show (EffectMaterial m) = "(EffectMaterial " <> show m <> ")"
  show (EffectTemporal t) = "(EffectTemporal " <> show t <> ")"
  show (EffectParticle p) = "(EffectParticle " <> show p <> ")"
  show (EffectSequence _) = "(EffectSequence [...])"
  show (EffectParallel _) = "(EffectParallel [...])"
  show (EffectConditional _) = "(EffectConditional ...)"
  show (EffectAnimated _) = "(EffectAnimated ...)"
  show EffectNone = "EffectNone"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // effect composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence effects (apply in order)
-- |
-- | Each effect reads from the previous effect's output texture.
-- | The final effect's output becomes the overall result.
effectSequence :: Array RenderEffect -> RenderEffect
effectSequence = EffectSequence

-- | Parallel effects (apply simultaneously)
-- |
-- | All effects read from the same source texture. Outputs are
-- | blended together according to each effect's blend mode.
effectParallel :: Array RenderEffect -> RenderEffect
effectParallel = EffectParallel

-- | Conditional effect
-- |
-- | Evaluates condition against FrameState. If true, applies thenEffect.
-- | If false, applies elseEffect (if provided) or EffectNone.
effectConditional :: EffectCondition -> RenderEffect -> Maybe RenderEffect -> RenderEffect
effectConditional condition thenEffect elseEffect = EffectConditional
  { condition, thenEffect, elseEffect }

-- | Conditional effect with no else branch
-- |
-- | Shorthand for effectConditional when you only want the "then" case.
effectWhen :: EffectCondition -> RenderEffect -> RenderEffect
effectWhen condition thenEffect = EffectConditional
  { condition, thenEffect, elseEffect: Nothing }

-- | Conditional effect with both branches
-- |
-- | Shorthand for effectConditional with explicit else effect.
effectIfThenElse :: EffectCondition -> RenderEffect -> RenderEffect -> RenderEffect
effectIfThenElse condition thenEffect elseEffect = EffectConditional
  { condition, thenEffect, elseEffect: Just elseEffect }

-- | Animated effect (interpolate between states)
-- |
-- | Interpolates between two effect configurations based on progress.
-- | Progress is typically driven by animation state from FrameState.
-- |
-- | Note: Not all effect pairs can meaningfully interpolate. The runtime
-- | handles incompatible pairs by crossfading opacity.
effectAnimated :: RenderEffect -> RenderEffect -> Number -> RenderEffect
effectAnimated from to progress = EffectAnimated { from, to, progress }
