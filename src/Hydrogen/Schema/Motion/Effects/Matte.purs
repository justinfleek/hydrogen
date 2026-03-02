-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // motion // effects // matte
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matte Effects — Alpha channel and edge refinement effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's Matte effect category:
-- |
-- | - **Simple Choker**: Expand/contract matte edges
-- | - **Matte Choker**: Advanced matte edge refinement
-- | - **Refine Matte**: Professional edge refinement (Roto Brush output)
-- | - **Set Matte**: Use another layer's channel as matte
-- | - **Channel Combiner**: Combine channels from multiple sources
-- |
-- | ## GPU Shader Pattern
-- |
-- | Matte effects operate on alpha channels:
-- | ```glsl
-- | float newAlpha = refineAlpha(inputAlpha, edgeParams);
-- | outputColor = vec4(inputColor.rgb, newAlpha);
-- | ```
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Hydrogen.Schema.Motion.Effects.Matte.Types` — Core types and enums
-- | - `Hydrogen.Schema.Motion.Effects.Matte.Operations` — Constructors and serialization
-- | - `Hydrogen.Schema.Motion.Effects.Matte.Queries` — Predicates and utilities

module Hydrogen.Schema.Motion.Effects.Matte
  ( module Types
  , module Operations
  , module Queries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.Effects.Matte.Types
  ( SimpleChokerEffect
  , MatteChokerEffect
  , GeometricSoftness
  , geometricSoftness
  , unwrapGeometricSoftness
  , RefineMatteEffect
  , RefinementType(RTSmooth, RTFeather, RTChoke, RTShiftEdge, RTReduceChatter)
  , MotionBlurMode(MBMNone, MBMNormal, MBMHighQuality)
  , SetMatteEffect
  , SetMatteChannel(SMCRed, SMCGreen, SMCBlue, SMCAlpha, SMCLuminance, SMCHue, SMCSaturation, SMCLightness, SMCFullOn, SMCFullOff)
  , SetMatteStretch(SMSStretch, SMSTile, SMSCenter)
  , ChannelCombinerEffect
  , CombinerSource(CSSourceRed, CSSourceGreen, CSSourceBlue, CSSourceAlpha, CSSourceLuma, CSLayerRed, CSLayerGreen, CSLayerBlue, CSLayerAlpha, CSLayerLuma, CSFullOn, CSFullOff, CSInvert)
  , MatteCleanupEffect
  , CleanupOperation(COBlur, COContrast, COGamma, COShrink, COExpand, COSimplify)
  ) as Types

import Hydrogen.Schema.Motion.Effects.Matte.Operations
  ( defaultSimpleChoker
  , simpleChokerExpand
  , simpleChokerContract
  , simpleChokerWithAmount
  , defaultMatteChoker
  , matteChokerWithSpread
  , defaultRefineMatte
  , refineMatteWithSmooth
  , refineMatteWithFeather
  , defaultSetMatte
  , setMatteFromLayer
  , setMatteFromChannel
  , defaultChannelCombiner
  , channelCombinerWithSources
  , defaultMatteCleanup
  , matteCleanupWithBlur
  , refinementTypeToString
  , motionBlurModeToString
  , setMatteChannelToString
  , setMatteStretchToString
  , combinerSourceToString
  , cleanupOperationToString
  , simpleChokerEffectName
  , matteChokerEffectName
  , refineMatteEffectName
  , setMatteEffectName
  , channelCombinerEffectName
  , matteCleanupEffectName
  , describeSimpleChoker
  , describeMatteChoker
  , describeRefineMatte
  , describeSetMatte
  ) as Operations

import Hydrogen.Schema.Motion.Effects.Matte.Queries
  ( isChokerExpanding
  , isChokerContracting
  , hasRefineMotionBlur
  , hasRefineSmooth
  , hasRefineFeather
  , isSetMatteInverted
  , hasCleanupBlur
  , hasCleanupContrast
  , clampSimpleChokerValues
  , clampMatteChokerValues
  , clampRefineMatteValues
  , combineChokerAmounts
  , combineRefineSmooth
  , isChokerSignificant
  , isMatteChokerDualPass
  , isRefineMatteComplete
  , effectiveChokeAmount
  , chokerIntensityRatio
  , scaleChokerAmount
  , chokerDifference
  , compareChokerMagnitude
  , effectiveFeatherRadius
  , classifyRefineIntensity
  ) as Queries
