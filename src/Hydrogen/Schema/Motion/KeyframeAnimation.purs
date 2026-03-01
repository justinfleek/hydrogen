-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // keyframe // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KeyframeAnimation — Complete animation sequences for UI components.
-- |
-- | ## Design Philosophy
-- |
-- | A KeyframeAnimation is a **complete animation specification** as pure data:
-- | - Sequence of keyframes defining property values at specific times
-- | - Duration, iteration count, direction, fill mode
-- | - Can target any animatable property (opacity, transform, color, etc.)
-- |
-- | This is NOT CSS `@keyframes` (though it can export to that format).
-- | This is a Schema atom that describes animation **semantically**.
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from:
-- | - `KeyframeAnimation.Types` — Core enumerations and identifiers
-- | - `KeyframeAnimation.Keyframe` — PropertyKeyframe type and builders
-- | - `KeyframeAnimation.Core` — Main type with constructors and accessors
-- | - `KeyframeAnimation.Presets.Attention` — Attention-grabbing animations
-- | - `KeyframeAnimation.Presets.Enter` — Entry animations
-- | - `KeyframeAnimation.Presets.Exit` — Exit animations
-- | - `KeyframeAnimation.Presets.Loading` — Loading state animations
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Same KeyframeAnimation = same visual output. Deterministic.
-- | UUID5 derived from animation content ensures identity.

module Hydrogen.Schema.Motion.KeyframeAnimation
  ( -- * Core Types
    module Hydrogen.Schema.Motion.KeyframeAnimation.Types
  , module Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe
  , module Hydrogen.Schema.Motion.KeyframeAnimation.Core
  
  -- * Presets
  , module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Attention
  , module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Enter
  , module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Exit
  , module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Loading
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.KeyframeAnimation.Types
  ( AnimationId
  , animationId
  , AnimationProperty
      ( PropOpacity
      , PropTranslateX
      , PropTranslateY
      , PropTranslateZ
      , PropRotate
      , PropRotateX
      , PropRotateY
      , PropRotateZ
      , PropScale
      , PropScaleX
      , PropScaleY
      , PropSkewX
      , PropSkewY
      , PropBackgroundColor
      , PropBorderColor
      , PropShadowColor
      , PropBlur
      , PropBrightness
      , PropSaturate
      , PropCustom
      )
  , AnimationDirection
      ( DirectionNormal
      , DirectionReverse
      , DirectionAlternate
      , DirectionAlternateReverse
      )
  , allAnimationDirections
  , AnimationFillMode
      ( FillNone
      , FillForwards
      , FillBackwards
      , FillBoth
      )
  , allAnimationFillModes
  , AnimationPlayState
      ( PlayStatePlaying
      , PlayStatePaused
      )
  , allAnimationPlayStates
  )

import Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe
  ( PropertyKeyframe
  , propertyKeyframe
  , opacityKeyframe
  , translateXKeyframe
  , translateYKeyframe
  , rotateKeyframe
  , scaleKeyframe
  , colorKeyframe
  )

import Hydrogen.Schema.Motion.KeyframeAnimation.Core
  ( KeyframeAnimation
  , keyframeAnimation
  , simpleAnimation
  , withDuration
  , withDelay
  , withIterations
  , withInfinite
  , withDirection
  , withFillMode
  , withEasing
  , withProperty
  , addKeyframe
  , duration
  , delay
  , iterations
  , direction
  , fillMode
  , keyframes
  , property
  , isInfinite
  , isPaused
  , hasKeyframes
  )

import Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Attention
  ( bounce
  , flash
  , pulse
  , rubberBand
  , shake
  , swing
  , tada
  , wobble
  , jello
  , heartBeat
  )

import Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Enter
  ( fadeIn
  , fadeInUp
  , fadeInDown
  , fadeInLeft
  , fadeInRight
  , slideInUp
  , slideInDown
  , slideInLeft
  , slideInRight
  , zoomIn
  , bounceIn
  )

import Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Exit
  ( fadeOut
  , fadeOutUp
  , fadeOutDown
  , fadeOutLeft
  , fadeOutRight
  , slideOutUp
  , slideOutDown
  , slideOutLeft
  , slideOutRight
  , zoomOut
  , bounceOut
  )

import Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Loading
  ( spin
  , spinReverse
  , pingPong
  , breathe
  )
