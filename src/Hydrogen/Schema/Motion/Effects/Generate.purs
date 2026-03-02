-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // effects // generate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate Effects — Procedural content generation effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's Generate effect category:
-- |
-- | - **Gradient Ramp**: Linear/radial gradient fills
-- | - **Cell Pattern**: Procedural cellular textures
-- | - **Checkerboard**: Checkerboard pattern
-- | - **Grid**: Lines/rectangles grid pattern
-- | - **Circle**: Simple circle shape
-- | - **Ellipse**: Ellipse with separate dimensions
-- | - **Fill**: Solid color fill
-- | - **Stroke**: Path stroke effect
-- | - **Vegas**: Animated stroke along path
-- | - **Fractal**: Fractal noise pattern
-- | - **4-Color Gradient**: Four-corner gradient
-- | - **Lens Flare**: Optical lens flare effect
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `Generate.Gradient` — Gradient effects (Ramp, 4-Color)
-- | - `Generate.Patterns` — Pattern effects (Cell, Checkerboard, Grid, Fractal)
-- | - `Generate.Shapes` — Shape effects (Circle, Ellipse, Fill, Stroke)
-- | - `Generate.Animation` — Animation effects (Vegas, Lens Flare)
-- |
-- | ## GPU Shader Pattern
-- |
-- | Generate effects are fully procedural, ideal for GPU shaders:
-- | ```glsl
-- | vec4 generateColor = computePattern(uv, params);
-- | outputColor = blend(inputColor, generateColor, blendMode);
-- | ```
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Generate
  ( -- * Gradient Ramp
    module Gradient
  
  -- * Patterns (Cell, Checkerboard, Grid, Fractal)
  , module Patterns
  
  -- * Shapes (Circle, Ellipse, Fill, Stroke)
  , module Shapes
  
  -- * Animation (Vegas, Lens Flare)
  , module Animation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.Effects.Generate.Gradient
  ( GradientRampEffect
  , RampShape(..)
  , defaultGradientRamp
  , linearGradientRamp
  , radialGradientRamp
  , FourColorGradientEffect
  , defaultFourColorGradient
  , rampShapeToString
  , describeGradientRamp
  , gradientRampEffectName
  , fourColorGradientEffectName
  , hasGradientScatter
  , combineGradientScatter
  ) as Gradient

import Hydrogen.Schema.Motion.Effects.Generate.Patterns
  ( CellPatternEffect
  , CellType(..)
  , defaultCellPattern
  , cellPatternWithType
  , CheckerboardEffect
  , defaultCheckerboard
  , checkerboardWithSize
  , GridEffect
  , GridType(..)
  , defaultGrid
  , gridWithSize
  , FractalEffect
  , FractalNoiseType(..)
  , defaultFractal
  , fractalWithComplexity
  , cellTypeToString
  , gridTypeToString
  , fractalNoiseTypeToString
  , describeCellPattern
  , describeGrid
  , describeFractal
  , cellPatternEffectName
  , checkerboardEffectName
  , gridEffectName
  , fractalEffectName
  , isCellPatternInverted
  , isFractalInverted
  , combineCellEvolution
  , combineFractalEvolution
  ) as Patterns

import Hydrogen.Schema.Motion.Effects.Generate.Shapes
  ( CircleEffect
  , CircleEdgeType(..)
  , defaultCircle
  , circleWithRadius
  , EllipseEffect
  , defaultEllipse
  , ellipseWithSize
  , FillEffect
  , FillMaskMode(..)
  , defaultFill
  , fillWithColor
  , StrokeEffect
  , StrokePaintStyle(..)
  , defaultStroke
  , strokeWithWidth
  , circleEdgeTypeToString
  , fillMaskModeToString
  , strokePaintStyleToString
  , circleEffectName
  , ellipseEffectName
  , fillEffectName
  , strokeEffectName
  , isCircleInverted
  , isEllipseInverted
  ) as Shapes

import Hydrogen.Schema.Motion.Effects.Generate.Animation
  ( VegasEffect
  , VegasPathMode(..)
  , defaultVegas
  , vegasWithSegments
  , LensFlareEffect
  , LensType(..)
  , defaultLensFlare
  , lensFlareWithBrightness
  , vegasPathModeToString
  , lensTypeToString
  , describeVegas
  , describeLensFlare
  , vegasEffectName
  , lensFlareEffectName
  ) as Animation
