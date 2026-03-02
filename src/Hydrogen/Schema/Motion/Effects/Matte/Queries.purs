-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // motion // effects // matte // queries
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matte Effects Queries — Predicates, clamping, and composition utilities.
-- |
-- | This module provides:
-- |
-- | - **Queries**: Boolean predicates for effect state
-- | - **Value Clamping**: Range enforcement for all effect types
-- | - **Composition**: Effect combination utilities
-- | - **Advanced Queries**: Computed properties, comparisons, and classifiers

module Hydrogen.Schema.Motion.Effects.Matte.Queries
  ( -- * Basic Queries
    isChokerExpanding
  , isChokerContracting
  , hasRefineMotionBlur
  , hasRefineSmooth
  , hasRefineFeather
  , isSetMatteInverted
  , hasCleanupBlur
  , hasCleanupContrast
  
  -- * Value Clamping
  , clampSimpleChokerValues
  , clampMatteChokerValues
  , clampRefineMatteValues
  
  -- * Composition
  , combineChokerAmounts
  , combineRefineSmooth
  
  -- * Advanced Queries
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( Ordering
  , ($)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , compare
  , min
  , max
  )

import Hydrogen.Schema.Bounded (clampNumber)

import Hydrogen.Schema.Motion.Effects.Matte.Types
  ( SimpleChokerEffect
  , MatteChokerEffect
  , geometricSoftness
  , unwrapGeometricSoftness
  , RefineMatteEffect
  , MotionBlurMode(MBMNone, MBMNormal, MBMHighQuality)
  , SetMatteEffect
  , MatteCleanupEffect
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // basic // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if choker is expanding (negative value).
isChokerExpanding :: SimpleChokerEffect -> Boolean
isChokerExpanding e = e.chokeMatte < 0.0

-- | Check if choker is contracting (positive value).
isChokerContracting :: SimpleChokerEffect -> Boolean
isChokerContracting e = e.chokeMatte > 0.0

-- | Check if refine matte has motion blur enabled.
hasRefineMotionBlur :: RefineMatteEffect -> Boolean
hasRefineMotionBlur e = case e.motionBlurMode of
  MBMNone -> false
  _ -> true

-- | Check if refine matte has smoothing.
hasRefineSmooth :: RefineMatteEffect -> Boolean
hasRefineSmooth e = e.smooth > 0.0

-- | Check if refine matte has feathering.
hasRefineFeather :: RefineMatteEffect -> Boolean
hasRefineFeather e = e.feather > 0.0

-- | Check if set matte is inverted.
isSetMatteInverted :: SetMatteEffect -> Boolean
isSetMatteInverted e = e.invertMatte

-- | Check if cleanup has blur.
hasCleanupBlur :: MatteCleanupEffect -> Boolean
hasCleanupBlur e = e.blur > 0.0

-- | Check if cleanup has contrast adjustment.
hasCleanupContrast :: MatteCleanupEffect -> Boolean
hasCleanupContrast e = e.contrast > 0.0 || e.contrast < 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // value // clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp simple choker values to valid ranges.
clampSimpleChokerValues :: SimpleChokerEffect -> SimpleChokerEffect
clampSimpleChokerValues e =
  { chokeMatte: clampNumber (-100.0) 100.0 e.chokeMatte
  }

-- | Clamp matte choker values to valid ranges.
clampMatteChokerValues :: MatteChokerEffect -> MatteChokerEffect
clampMatteChokerValues e =
  { geometricSoftness1: geometricSoftness $ unwrapGeometricSoftness e.geometricSoftness1
  , choke1: clampNumber (-100.0) 100.0 e.choke1
  , geometricSoftness2: geometricSoftness $ unwrapGeometricSoftness e.geometricSoftness2
  , choke2: clampNumber (-100.0) 100.0 e.choke2
  , grayLevelSoftness: clampNumber 0.0 100.0 e.grayLevelSoftness
  }

-- | Clamp refine matte values to valid ranges.
clampRefineMatteValues :: RefineMatteEffect -> RefineMatteEffect
clampRefineMatteValues e =
  { smooth: clampNumber 0.0 100.0 e.smooth
  , feather: clampNumber 0.0 250.0 e.feather
  , choke: clampNumber (-100.0) 100.0 e.choke
  , shiftEdge: clampNumber (-100.0) 100.0 e.shiftEdge
  , reduceChatter: clampNumber 0.0 100.0 e.reduceChatter
  , motionBlurMode: e.motionBlurMode
  , motionBlurSamples: min 64 $ max 1 e.motionBlurSamples
  , motionBlurShutter: clampNumber 0.0 720.0 e.motionBlurShutter
  , decontaminate: e.decontaminate
  , decontaminateAmount: clampNumber 0.0 100.0 e.decontaminateAmount
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two choker amounts (additive, clamped).
combineChokerAmounts :: SimpleChokerEffect -> SimpleChokerEffect -> SimpleChokerEffect
combineChokerAmounts a b =
  { chokeMatte: clampNumber (-100.0) 100.0 $ a.chokeMatte + b.chokeMatte
  }

-- | Combine two refine matte smooth amounts (max).
combineRefineSmooth :: RefineMatteEffect -> RefineMatteEffect -> Number
combineRefineSmooth a b = max a.smooth b.smooth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // advanced // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if choker amount is significant (>= 5 or <= -5).
isChokerSignificant :: SimpleChokerEffect -> Boolean
isChokerSignificant e = e.chokeMatte >= 5.0 || e.chokeMatte <= (-5.0)

-- | Check if matte choker uses both passes.
isMatteChokerDualPass :: MatteChokerEffect -> Boolean
isMatteChokerDualPass e = 
  (e.choke1 > 0.0 || e.choke1 < 0.0) && (e.choke2 > 0.0 || e.choke2 < 0.0)

-- | Check if refine matte is fully configured (smooth AND feather).
isRefineMatteComplete :: RefineMatteEffect -> Boolean
isRefineMatteComplete e = e.smooth >= 1.0 && e.feather >= 1.0

-- | Compute effective choke (taking into account all passes).
effectiveChokeAmount :: MatteChokerEffect -> Number
effectiveChokeAmount e = e.choke1 + e.choke2

-- | Compute choker intensity ratio (percentage of max).
chokerIntensityRatio :: SimpleChokerEffect -> Number
chokerIntensityRatio e
  | e.chokeMatte >= 0.0 = e.chokeMatte / 100.0
  | otherwise = negate e.chokeMatte / 100.0

-- | Scale a simple choker effect by a factor.
scaleChokerAmount :: Number -> SimpleChokerEffect -> SimpleChokerEffect
scaleChokerAmount factor e =
  { chokeMatte: clampNumber (-100.0) 100.0 $ e.chokeMatte * factor
  }

-- | Compute difference between two choker effects.
chokerDifference :: SimpleChokerEffect -> SimpleChokerEffect -> Number
chokerDifference a b = a.chokeMatte - b.chokeMatte

-- | Compare two simple choker effects by absolute magnitude.
compareChokerMagnitude :: SimpleChokerEffect -> SimpleChokerEffect -> Ordering
compareChokerMagnitude a b = 
  let
    absA = if a.chokeMatte >= 0.0 then a.chokeMatte else negate a.chokeMatte
    absB = if b.chokeMatte >= 0.0 then b.chokeMatte else negate b.chokeMatte
  in
    compare absA absB

-- | Compute the effective feather radius accounting for smooth.
effectiveFeatherRadius :: RefineMatteEffect -> Number
effectiveFeatherRadius e = e.feather + (e.smooth * 0.5)

-- | Classify refine matte by processing intensity.
classifyRefineIntensity :: RefineMatteEffect -> String
classifyRefineIntensity e
  | e.smooth >= 50.0 && e.feather >= 100.0 = "heavy"
  | e.smooth >= 20.0 || e.feather >= 50.0 = "medium"
  | e.smooth <= 5.0 && e.feather <= 10.0 = "light"
  | otherwise = "moderate"
