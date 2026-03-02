-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // effects // matte // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matte Effects Operations — Defaults, constructors, and serialization.
-- |
-- | This module provides:
-- |
-- | - **Defaults**: Default values for all matte effects
-- | - **Constructors**: Smart constructors with bounded validation
-- | - **Serialization**: String conversion for all enums
-- | - **Effect Names**: Human-readable effect identifiers
-- | - **Descriptions**: Detailed effect descriptions

module Hydrogen.Schema.Motion.Effects.Matte.Operations
  ( -- * Simple Choker Defaults/Constructors
    defaultSimpleChoker
  , simpleChokerExpand
  , simpleChokerContract
  , simpleChokerWithAmount
  
  -- * Matte Choker Defaults/Constructors
  , defaultMatteChoker
  , matteChokerWithSpread
  
  -- * Refine Matte Defaults/Constructors
  , defaultRefineMatte
  , refineMatteWithSmooth
  , refineMatteWithFeather
  
  -- * Set Matte Defaults/Constructors
  , defaultSetMatte
  , setMatteFromLayer
  , setMatteFromChannel
  
  -- * Channel Combiner Defaults/Constructors
  , defaultChannelCombiner
  , channelCombinerWithSources
  
  -- * Matte Cleanup Defaults/Constructors
  , defaultMatteCleanup
  , matteCleanupWithBlur
  
  -- * Serialization
  , refinementTypeToString
  , motionBlurModeToString
  , setMatteChannelToString
  , setMatteStretchToString
  , combinerSourceToString
  , cleanupOperationToString
  
  -- * Effect Names
  , simpleChokerEffectName
  , matteChokerEffectName
  , refineMatteEffectName
  , setMatteEffectName
  , channelCombinerEffectName
  , matteCleanupEffectName
  
  -- * Effect Descriptions
  , describeSimpleChoker
  , describeMatteChoker
  , describeRefineMatte
  , describeSetMatte
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (<>)
  , (<)
  , (>)
  , negate
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)

import Hydrogen.Schema.Motion.Effects.Matte.Types
  ( SimpleChokerEffect
  , MatteChokerEffect
  , geometricSoftness
  , unwrapGeometricSoftness
  , RefineMatteEffect
  , RefinementType
  , MotionBlurMode(MBMNone, MBMNormal, MBMHighQuality)
  , SetMatteEffect
  , SetMatteChannel(SMCRed, SMCGreen, SMCBlue, SMCAlpha, SMCLuminance, SMCHue, SMCSaturation, SMCLightness, SMCFullOn, SMCFullOff)
  , SetMatteStretch(SMSStretch, SMSTile, SMSCenter)
  , ChannelCombinerEffect
  , CombinerSource(CSSourceRed, CSSourceGreen, CSSourceBlue, CSSourceAlpha, CSSourceLuma, CSLayerRed, CSLayerGreen, CSLayerBlue, CSLayerAlpha, CSLayerLuma, CSFullOn, CSFullOff, CSInvert)
  , MatteCleanupEffect
  , CleanupOperation(COBlur, COContrast, COGamma, COShrink, COExpand, COSimplify)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // simple // choker // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default simple choker: no change.
defaultSimpleChoker :: SimpleChokerEffect
defaultSimpleChoker =
  { chokeMatte: 0.0
  }

-- | Create simple choker that expands matte.
simpleChokerExpand :: Number -> SimpleChokerEffect
simpleChokerExpand amt =
  { chokeMatte: clampNumber (-100.0) 0.0 $ negate amt
  }

-- | Create simple choker that contracts matte.
simpleChokerContract :: Number -> SimpleChokerEffect
simpleChokerContract amt =
  { chokeMatte: clampNumber 0.0 100.0 amt
  }

-- | Create simple choker with specific amount (positive = contract).
simpleChokerWithAmount :: Number -> SimpleChokerEffect
simpleChokerWithAmount amt =
  { chokeMatte: clampNumber (-100.0) 100.0 amt
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // matte // choker // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default matte choker: no change.
defaultMatteChoker :: MatteChokerEffect
defaultMatteChoker =
  { geometricSoftness1: geometricSoftness 0.0
  , choke1: 0.0
  , geometricSoftness2: geometricSoftness 0.0
  , choke2: 0.0
  , grayLevelSoftness: 0.0
  }

-- | Create matte choker with specific spread.
matteChokerWithSpread :: Number -> Number -> MatteChokerEffect
matteChokerWithSpread soft choke =
  { geometricSoftness1: geometricSoftness soft
  , choke1: clampNumber (-100.0) 100.0 choke
  , geometricSoftness2: geometricSoftness 0.0
  , choke2: 0.0
  , grayLevelSoftness: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // refine // matte // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default refine matte: minimal processing.
defaultRefineMatte :: RefineMatteEffect
defaultRefineMatte =
  { smooth: 0.0
  , feather: 0.0
  , choke: 0.0
  , shiftEdge: 0.0
  , reduceChatter: 0.0
  , motionBlurMode: MBMNone
  , motionBlurSamples: 16
  , motionBlurShutter: 180.0
  , decontaminate: false
  , decontaminateAmount: 100.0
  }

-- | Create refine matte with smooth.
refineMatteWithSmooth :: Number -> RefineMatteEffect
refineMatteWithSmooth amt =
  { smooth: clampNumber 0.0 100.0 amt
  , feather: 0.0
  , choke: 0.0
  , shiftEdge: 0.0
  , reduceChatter: 0.0
  , motionBlurMode: MBMNone
  , motionBlurSamples: 16
  , motionBlurShutter: 180.0
  , decontaminate: false
  , decontaminateAmount: 100.0
  }

-- | Create refine matte with feather.
refineMatteWithFeather :: Number -> RefineMatteEffect
refineMatteWithFeather amt =
  { smooth: 0.0
  , feather: clampNumber 0.0 250.0 amt
  , choke: 0.0
  , shiftEdge: 0.0
  , reduceChatter: 0.0
  , motionBlurMode: MBMNone
  , motionBlurSamples: 16
  , motionBlurShutter: 180.0
  , decontaminate: false
  , decontaminateAmount: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // set // matte // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default set matte: alpha from layer 1.
defaultSetMatte :: SetMatteEffect
defaultSetMatte =
  { takeMatteFromLayer: 1
  , useForMatte: SMCAlpha
  , invertMatte: false
  , stretchMode: SMSStretch
  , premultiplyMatte: false
  }

-- | Create set matte from specific layer.
setMatteFromLayer :: Int -> SetMatteEffect
setMatteFromLayer layer =
  { takeMatteFromLayer: layer
  , useForMatte: SMCAlpha
  , invertMatte: false
  , stretchMode: SMSStretch
  , premultiplyMatte: false
  }

-- | Create set matte from specific channel.
setMatteFromChannel :: Int -> SetMatteChannel -> SetMatteEffect
setMatteFromChannel layer channel =
  { takeMatteFromLayer: layer
  , useForMatte: channel
  , invertMatte: false
  , stretchMode: SMSStretch
  , premultiplyMatte: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                      // channel // combiner // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default channel combiner: passthrough.
defaultChannelCombiner :: ChannelCombinerEffect
defaultChannelCombiner =
  { redOutput: CSSourceRed
  , greenOutput: CSSourceGreen
  , blueOutput: CSSourceBlue
  , alphaOutput: CSSourceAlpha
  }

-- | Create channel combiner with custom sources.
channelCombinerWithSources :: CombinerSource -> CombinerSource -> CombinerSource -> CombinerSource -> ChannelCombinerEffect
channelCombinerWithSources r g b a =
  { redOutput: r
  , greenOutput: g
  , blueOutput: b
  , alphaOutput: a
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                        // matte // cleanup // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default matte cleanup: no change.
defaultMatteCleanup :: MatteCleanupEffect
defaultMatteCleanup =
  { blur: 0.0
  , contrast: 0.0
  , gamma: 1.0
  , sizeAdjust: 0.0
  , simplify: 0.0
  , primaryOperation: COBlur
  }

-- | Create matte cleanup with blur.
matteCleanupWithBlur :: Number -> MatteCleanupEffect
matteCleanupWithBlur amt =
  { blur: clampNumber 0.0 100.0 amt
  , contrast: 0.0
  , gamma: 1.0
  , sizeAdjust: 0.0
  , simplify: 0.0
  , primaryOperation: COBlur
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RefinementType to string.
refinementTypeToString :: RefinementType -> String
refinementTypeToString = show

-- | Convert MotionBlurMode to string.
motionBlurModeToString :: MotionBlurMode -> String
motionBlurModeToString = show

-- | Convert SetMatteChannel to string.
setMatteChannelToString :: SetMatteChannel -> String
setMatteChannelToString = show

-- | Convert SetMatteStretch to string.
setMatteStretchToString :: SetMatteStretch -> String
setMatteStretchToString = show

-- | Convert CombinerSource to string.
combinerSourceToString :: CombinerSource -> String
combinerSourceToString = show

-- | Convert CleanupOperation to string.
cleanupOperationToString :: CleanupOperation -> String
cleanupOperationToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Simple Choker.
simpleChokerEffectName :: SimpleChokerEffect -> String
simpleChokerEffectName _ = "Simple Choker"

-- | Effect name for Matte Choker.
matteChokerEffectName :: MatteChokerEffect -> String
matteChokerEffectName _ = "Matte Choker"

-- | Effect name for Refine Matte.
refineMatteEffectName :: RefineMatteEffect -> String
refineMatteEffectName _ = "Refine Matte"

-- | Effect name for Set Matte.
setMatteEffectName :: SetMatteEffect -> String
setMatteEffectName _ = "Set Matte"

-- | Effect name for Channel Combiner.
channelCombinerEffectName :: ChannelCombinerEffect -> String
channelCombinerEffectName _ = "Channel Combiner"

-- | Effect name for Matte Cleanup.
matteCleanupEffectName :: MatteCleanupEffect -> String
matteCleanupEffectName _ = "Matte Cleanup"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe simple choker effect.
describeSimpleChoker :: SimpleChokerEffect -> String
describeSimpleChoker e =
  let
    typeStr = if e.chokeMatte > 0.0 then "contract" else if e.chokeMatte < 0.0 then "expand" else "none"
  in
    "SimpleChoker(" <> typeStr <> ": " <> show e.chokeMatte <> ")"

-- | Describe matte choker effect.
describeMatteChoker :: MatteChokerEffect -> String
describeMatteChoker e =
  "MatteChoker(choke1: " <> show e.choke1 
    <> ", soft1: " <> show (unwrapGeometricSoftness e.geometricSoftness1)
    <> ", choke2: " <> show e.choke2
    <> ")"

-- | Describe refine matte effect.
describeRefineMatte :: RefineMatteEffect -> String
describeRefineMatte e =
  "RefineMatte(smooth: " <> show e.smooth
    <> ", feather: " <> show e.feather <> "px"
    <> ", choke: " <> show e.choke <> "%"
    <> ")"

-- | Describe set matte effect.
describeSetMatte :: SetMatteEffect -> String
describeSetMatte e =
  let
    invertStr = if e.invertMatte then " inverted" else ""
  in
    "SetMatte(layer: " <> show e.takeMatteFromLayer
      <> ", channel: " <> show e.useForMatte
      <> invertStr
      <> ")"
