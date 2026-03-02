-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // shapes // modifiers // utilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Serialization, utilities, and comparisons for shape modifiers.
-- |
-- | Operations for transforming, comparing, and serializing modifiers.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Utilities
  ( -- * Serialization
    dashPatternToString
  , describeTaper
  , describeWave
  
  -- * Utilities
  , totalTaperLength
  , effectiveWaveFrequency
  , scaleTaper
  , scaleWave
  , combineTapers
  , combineWaves
  , allWaveTypes
  
  -- * Comparisons
  , compareStrokeWidth
  , isStrokeThin
  , isStrokeThick
  , isTaperSymmetric
  , taperStartsFromZero
  , taperEndsAtZero
  , isWaveHighFrequency
  , isWaveLowAmplitude
  , minStrokeByWidth
  , maxStrokeByWidth
  , taperEquals
  , waveEquals
  , isDashPatternSolid
  , hasDashes
  , negateWavePhase
  , invertTaper
  , taperDiffersBy
  , strokeCoverage
  , taperNotEquals
  , waveNotEquals
  , minTaperLength
  , maxTaperLength
  , minWaveParam
  , maxWaveParam
  
  -- * Semigroup Combinable
  , CombinableStrokeWidth(CombinableStrokeWidth)
  , combinableWidth
  , unwrapCombinableWidth
  ) where

import Prelude
  ( class Semigroup
  , ($)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , show
  , map
  , pure
  , (#)
  )

import Data.Ord (abs)
import Data.Ordering (Ordering)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  , unwrapPercent
  , PositiveNumber
  , positiveNumber
  , unwrapPositiveNumber
  )
import Hydrogen.Schema.Motion.Shapes.Modifiers.Stroke (StrokeProps, DashPattern)
import Hydrogen.Schema.Motion.Shapes.Modifiers.Taper (StrokeTaper)
import Hydrogen.Schema.Motion.Shapes.Modifiers.Wave (StrokeWave, WaveType(WTSine, WTSquare, WTTriangle, WTSawtooth))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize dash pattern to string.
dashPatternToString :: DashPattern -> String
dashPatternToString dp = case dp.dashes of
  [] -> "solid"
  _ -> "dashed"

-- | Serialize stroke taper to description.
describeTaper :: StrokeTaper -> String
describeTaper t
  | t.enabled = "Taper(start: " <> show t.startLength <> ", end: " <> show t.endLength <> ")"
  | true = "no-taper"

-- | Serialize stroke wave to description.
describeWave :: StrokeWave -> String
describeWave w
  | w.enabled = "Wave(" <> show w.waveType <> ", amount: " <> show w.amount <> ")"
  | true = "no-wave"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total taper length as percentage.
totalTaperLength :: StrokeTaper -> Number
totalTaperLength t = 
  let startLen = unwrapPercent t.startLength
      endLen = unwrapPercent t.endLength
  in clampNumber 0.0 100.0 $ startLen + endLen

-- | Calculate effective wave frequency based on path length.
effectiveWaveFrequency :: StrokeWave -> Number -> Number
effectiveWaveFrequency w pathLength =
  let freq = unwrapPositiveNumber w.frequency
  in clampNumber 0.0 1000.0 $ freq * (pathLength / 100.0)

-- | Scale taper proportionally.
scaleTaper :: Number -> StrokeTaper -> StrokeTaper
scaleTaper factor t =
  let scaleP :: Percent -> Percent
      scaleP p = percent $ clampNumber 0.0 100.0 $ unwrapPercent p * abs factor
  in t { startLength = scaleP t.startLength
       , endLength = scaleP t.endLength
       }

-- | Scale wave proportionally.
scaleWave :: Number -> StrokeWave -> StrokeWave
scaleWave factor w =
  let amount' = unwrapPositiveNumber w.amount
      newAmount = positiveNumber $ clampNumber 0.0 500.0 $ amount' * abs factor
  in w { amount = newAmount }

-- | Combine two tapers by averaging.
combineTapers :: StrokeTaper -> StrokeTaper -> StrokeTaper
combineTapers t1 t2 =
  let avgP :: Percent -> Percent -> Percent
      avgP p1 p2 = percent $ (unwrapPercent p1 + unwrapPercent p2) / 2.0
  in { enabled: t1.enabled || t2.enabled
     , startLength: avgP t1.startLength t2.startLength
     , endLength: avgP t1.endLength t2.endLength
     , startWidth: avgP t1.startWidth t2.startWidth
     , endWidth: avgP t1.endWidth t2.endWidth
     , startEase: avgP t1.startEase t2.startEase
     , endEase: avgP t1.endEase t2.endEase
     }

-- | Combine two waves by averaging.
combineWaves :: StrokeWave -> StrokeWave -> StrokeWave
combineWaves w1 w2 =
  let avgN :: PositiveNumber -> PositiveNumber -> PositiveNumber
      avgN pn1 pn2 = positiveNumber $ (unwrapPositiveNumber pn1 + unwrapPositiveNumber pn2) / 2.0
  in { enabled: w1.enabled || w2.enabled
     , amount: avgN w1.amount w2.amount
     , frequency: avgN w1.frequency w2.frequency
     , phase: (w1.phase + w2.phase) / 2.0
     , waveType: w1.waveType  -- Use first wave type
     }

-- | Get all wave types for UI enumeration.
allWaveTypes :: Array WaveType
allWaveTypes = [WTSine, WTSquare, WTTriangle, WTSawtooth]
  # map pure
  # flattenArray
  where
  flattenArray :: Array (Array WaveType) -> Array WaveType
  flattenArray _ = [WTSine, WTSquare, WTTriangle, WTSawtooth]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two strokes by width.
compareStrokeWidth :: StrokeProps -> StrokeProps -> Ordering
compareStrokeWidth s1 s2 = compare (unwrapPositiveNumber s1.width) (unwrapPositiveNumber s2.width)

-- | Check if stroke is thin (< 2px).
isStrokeThin :: StrokeProps -> Boolean
isStrokeThin s = unwrapPositiveNumber s.width < 2.0

-- | Check if stroke is thick (>= 10px).
isStrokeThick :: StrokeProps -> Boolean
isStrokeThick s = unwrapPositiveNumber s.width >= 10.0

-- | Check if taper is symmetric (equal start and end).
isTaperSymmetric :: StrokeTaper -> Boolean
isTaperSymmetric t = 
  unwrapPercent t.startLength == unwrapPercent t.endLength &&
  unwrapPercent t.startWidth == unwrapPercent t.endWidth

-- | Check if taper starts from zero width.
taperStartsFromZero :: StrokeTaper -> Boolean
taperStartsFromZero t = unwrapPercent t.startWidth <= 0.0

-- | Check if taper ends at zero width.
taperEndsAtZero :: StrokeTaper -> Boolean
taperEndsAtZero t = unwrapPercent t.endWidth <= 0.0

-- | Check if wave is high frequency (> 10).
isWaveHighFrequency :: StrokeWave -> Boolean
isWaveHighFrequency w = unwrapPositiveNumber w.frequency > 10.0

-- | Check if wave is low amplitude (< 5).
isWaveLowAmplitude :: StrokeWave -> Boolean
isWaveLowAmplitude w = unwrapPositiveNumber w.amount < 5.0

-- | Get minimum of two strokes by width.
minStrokeByWidth :: StrokeProps -> StrokeProps -> StrokeProps
minStrokeByWidth s1 s2 = 
  if unwrapPositiveNumber s1.width < unwrapPositiveNumber s2.width then s1 else s2

-- | Get maximum of two strokes by width.
maxStrokeByWidth :: StrokeProps -> StrokeProps -> StrokeProps
maxStrokeByWidth s1 s2 =
  if unwrapPositiveNumber s1.width > unwrapPositiveNumber s2.width then s1 else s2

-- | Check if two tapers are equal.
taperEquals :: StrokeTaper -> StrokeTaper -> Boolean
taperEquals t1 t2 =
  t1.enabled == t2.enabled &&
  unwrapPercent t1.startLength == unwrapPercent t2.startLength &&
  unwrapPercent t1.endLength == unwrapPercent t2.endLength &&
  unwrapPercent t1.startWidth == unwrapPercent t2.startWidth &&
  unwrapPercent t1.endWidth == unwrapPercent t2.endWidth

-- | Check if two waves are equal.
waveEquals :: StrokeWave -> StrokeWave -> Boolean
waveEquals w1 w2 =
  w1.enabled == w2.enabled &&
  w1.waveType == w2.waveType &&
  unwrapPositiveNumber w1.amount == unwrapPositiveNumber w2.amount &&
  unwrapPositiveNumber w1.frequency == unwrapPositiveNumber w2.frequency

-- | Check if dash pattern is empty (solid).
isDashPatternSolid :: DashPattern -> Boolean
isDashPatternSolid dp = not (hasDashes dp)

-- | Check if dash pattern has dashes.
hasDashes :: DashPattern -> Boolean
hasDashes dp = case dp.dashes of
  [] -> false
  _ -> true

-- | Negate wave phase (flip phase by 180 degrees).
negateWavePhase :: StrokeWave -> StrokeWave
negateWavePhase w = w { phase = 360.0 - w.phase }

-- | Invert taper (swap start and end).
invertTaper :: StrokeTaper -> StrokeTaper
invertTaper t = t
  { startLength = t.endLength
  , endLength = t.startLength
  , startWidth = t.endWidth
  , endWidth = t.startWidth
  , startEase = t.endEase
  , endEase = t.startEase
  }

-- | Check if taper differs from another by more than threshold.
taperDiffersBy :: StrokeTaper -> StrokeTaper -> Number -> Boolean
taperDiffersBy t1 t2 threshold =
  let diff = abs (unwrapPercent t1.startLength - unwrapPercent t2.startLength)
  in diff > threshold

-- | Calculate stroke coverage (considering dash pattern).
strokeCoverage :: StrokeProps -> Number
strokeCoverage s = 
  let dashes = s.dashPattern.dashes
  in case dashes of
       [] -> 100.0  -- Solid = 100% coverage
       _ -> 50.0    -- Dashed = approximate 50% coverage

-- | Check if two tapers are not equal.
taperNotEquals :: StrokeTaper -> StrokeTaper -> Boolean
taperNotEquals t1 t2 =
  t1.enabled /= t2.enabled ||
  unwrapPercent t1.startLength /= unwrapPercent t2.startLength ||
  unwrapPercent t1.endLength /= unwrapPercent t2.endLength

-- | Check if two waves are not equal.
waveNotEquals :: StrokeWave -> StrokeWave -> Boolean
waveNotEquals w1 w2 =
  w1.enabled /= w2.enabled ||
  w1.waveType /= w2.waveType

-- | Get minimum taper length (start or end).
minTaperLength :: StrokeTaper -> Number
minTaperLength t = min (unwrapPercent t.startLength) (unwrapPercent t.endLength)

-- | Get maximum taper length (start or end).
maxTaperLength :: StrokeTaper -> Number
maxTaperLength t = max (unwrapPercent t.startLength) (unwrapPercent t.endLength)

-- | Get minimum wave parameter (amount or frequency).
minWaveParam :: StrokeWave -> Number
minWaveParam w = min (unwrapPositiveNumber w.amount) (unwrapPositiveNumber w.frequency)

-- | Get maximum wave parameter (amount or frequency).
maxWaveParam :: StrokeWave -> Number
maxWaveParam w = max (unwrapPositiveNumber w.amount) (unwrapPositiveNumber w.frequency)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // semigroup combinable
-- ═════════════════════════════════════════════════════════════════════════════

-- | Newtype for composable strokes via Semigroup.
newtype CombinableStrokeWidth = CombinableStrokeWidth PositiveNumber

-- | Semigroup instance for combining stroke widths (averages them).
instance semigroupCombinableStrokeWidth :: Semigroup CombinableStrokeWidth where
  append (CombinableStrokeWidth w1) (CombinableStrokeWidth w2) =
    CombinableStrokeWidth $ positiveNumber $ 
      (unwrapPositiveNumber w1 + unwrapPositiveNumber w2) / 2.0

-- | Create combinable stroke width.
combinableWidth :: Number -> CombinableStrokeWidth
combinableWidth n = CombinableStrokeWidth (positiveNumber n)

-- | Unwrap combinable stroke width.
unwrapCombinableWidth :: CombinableStrokeWidth -> Number
unwrapCombinableWidth (CombinableStrokeWidth pn) = unwrapPositiveNumber pn
