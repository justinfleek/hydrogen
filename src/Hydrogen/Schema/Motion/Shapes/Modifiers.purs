-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // motion // shapes // modifiers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape modifier property records.
-- |
-- | Modifiers apply visual styling to shapes: Fill, Stroke, Gradients.
-- | All values are bounded and composable.
-- |
-- | This is a leader module that re-exports all modifier submodules.

module Hydrogen.Schema.Motion.Shapes.Modifiers
  ( -- * Fill
    module Hydrogen.Schema.Motion.Shapes.Modifiers.Fill
  
  -- * Stroke
  , module Hydrogen.Schema.Motion.Shapes.Modifiers.Stroke
  
  -- * Gradient
  , module Hydrogen.Schema.Motion.Shapes.Modifiers.Gradient
  
  -- * Taper
  , module Hydrogen.Schema.Motion.Shapes.Modifiers.Taper
  
  -- * Wave
  , module Hydrogen.Schema.Motion.Shapes.Modifiers.Wave
  
  -- * Advanced
  , module Hydrogen.Schema.Motion.Shapes.Modifiers.Advanced
  
  -- * Utilities
  , module Hydrogen.Schema.Motion.Shapes.Modifiers.Utilities
  ) where

import Hydrogen.Schema.Motion.Shapes.Modifiers.Fill
  ( FillProps
  , fillProps
  , defaultFill
  )

import Hydrogen.Schema.Motion.Shapes.Modifiers.Stroke
  ( StrokeDash
  , DashPattern
  , strokeDash
  , dashPattern
  , solidDash
  , dottedDash
  , dashedDash
  , StrokeProps
  , strokeProps
  , defaultStroke
  )

import Hydrogen.Schema.Motion.Shapes.Modifiers.Gradient
  ( GradientFillProps
  , gradientFillProps
  , defaultGradientFill
  , GradientStrokeProps
  , gradientStrokeProps
  , defaultGradientStroke
  )

import Hydrogen.Schema.Motion.Shapes.Modifiers.Taper
  ( StrokeTaper
  , strokeTaper
  , noTaper
  , defaultTaper
  , taperFromStart
  , taperToEnd
  , taperBothEnds
  )

import Hydrogen.Schema.Motion.Shapes.Modifiers.Wave
  ( WaveType(WTSine, WTSquare, WTTriangle, WTSawtooth)
  , waveTypeToString
  , StrokeWave
  , strokeWave
  , noWave
  , defaultWave
  , sineWave
  , squareWave
  , triangleWave
  , sawtoothWave
  )

import Hydrogen.Schema.Motion.Shapes.Modifiers.Advanced
  ( AdvancedStrokeProps
  , advancedStrokeProps
  , defaultAdvancedStroke
  , strokeWithTaper
  , strokeWithWave
  , strokeWithTaperAndWave
  , hasTaper
  , hasWave
  , hasAdvancedFeatures
  )

import Hydrogen.Schema.Motion.Shapes.Modifiers.Utilities
  ( dashPatternToString
  , describeTaper
  , describeWave
  , totalTaperLength
  , effectiveWaveFrequency
  , scaleTaper
  , scaleWave
  , combineTapers
  , combineWaves
  , allWaveTypes
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
  , CombinableStrokeWidth(CombinableStrokeWidth)
  , combinableWidth
  , unwrapCombinableWidth
  )
