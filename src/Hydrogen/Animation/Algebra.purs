-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // animation // algebra
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure animation algebra for typography and element animations.
-- |
-- | All combinators are lawful (Semigroup, Monoid, Applicative).
-- | Time is bounded. Transforms compose. Everything is deterministic.
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - Algebra.Easing: Easing functions and configuration
-- | - Algebra.Transform: 2D/3D transform types
-- | - Algebra.Core: Animation type and instances
-- | - Algebra.Combinators: Sequential, parallel, stagger
-- | - Algebra.TransformAnimations: Factory functions
-- | - Algebra.Path: Bezier path animations
-- | - Algebra.Targeting: Character/word targeting

module Hydrogen.Animation.Algebra
  ( -- Re-exports from Time
    module Hydrogen.Animation.Time
  
  -- Re-exports from Easing
  , module Hydrogen.Animation.Algebra.Easing
  
  -- Re-exports from Transform
  , module Hydrogen.Animation.Algebra.Transform
  
  -- Re-exports from Core
  , module Hydrogen.Animation.Algebra.Core
  
  -- Re-exports from Combinators
  , module Hydrogen.Animation.Algebra.Combinators
  
  -- Re-exports from TransformAnimations
  , module Hydrogen.Animation.Algebra.TransformAnimations
  
  -- Re-exports from Path
  , module Hydrogen.Animation.Algebra.Path
  
  -- Re-exports from Targeting
  , module Hydrogen.Animation.Algebra.Targeting
  ) where

import Hydrogen.Animation.Time
  ( Duration(Duration)
  , Milliseconds
  , Progress(Progress)
  , normalizeProgress
  )

import Hydrogen.Animation.Algebra.Easing
  ( Easing
      ( Linear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseInQuad
      , EaseOutQuad
      , EaseInOutQuad
      , EaseInCubic
      , EaseOutCubic
      , EaseInOutCubic
      , EaseInQuart
      , EaseOutQuart
      , EaseInOutQuart
      , EaseInQuint
      , EaseOutQuint
      , EaseInOutQuint
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInCirc
      , EaseOutCirc
      , EaseInOutCirc
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseInElastic
      , EaseOutElastic
      , EaseInOutElastic
      , EaseInBounce
      , EaseOutBounce
      , EaseInOutBounce
      , Spring
      , CubicBezier
      , Steps
      , Custom
      )
  , EasingFunction
  , applyEasing
  , SpringConfig(SpringConfig)
  , BezierCurve(BezierCurve)
  )

import Hydrogen.Animation.Algebra.Transform
  ( Transform2D(Transform2D)
  , Transform3D(Transform3D)
  , TransformOrigin(TransformOrigin)
  , Opacity(Opacity)
  )

import Hydrogen.Animation.Algebra.Core
  ( Animation(Animation)
  , AnimationF
  , AnimationValue
      ( TransformValue
      , Transform3DValue
      , OpacityValue
      , CompositeValue
      )
  , runAnimation
  , duration
  )

import Hydrogen.Animation.Algebra.Combinators
  ( sequential
  , parallel
  , stagger
  , delay
  , timeScale
  , reverse
  , pingPong
  , repeat
  , StaggerPattern(LinearStagger, RandomStagger, CustomStagger)
  , StaggerDirection(LeftToRight, RightToLeft, CenterOut, EdgesIn)
  , applyStagger
  )

import Hydrogen.Animation.Algebra.TransformAnimations
  ( translateX
  , translateY
  , translate
  , scale
  , scaleXY
  , rotate
  , rotate3D
  , skewX
  , skewY
  , opacity
  )

import Hydrogen.Animation.Algebra.Path
  ( Point2D
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ArcTo, ClosePath)
  , AnimationPath(AnimationPath)
  , followPath
  , morphPath
  )

import Hydrogen.Animation.Algebra.Targeting
  ( AnimationTarget(TargetCharacter, TargetWord, TargetLine, TargetRange, TargetAll)
  , TargetSelector(SelectAll, SelectOdd, SelectEven, SelectEvery, SelectRange, SelectIndices, SelectWhere)
  , targeted
  )
