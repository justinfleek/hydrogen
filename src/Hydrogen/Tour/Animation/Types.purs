-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // tour // animation // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Type Definitions for Animation System
-- |
-- | This module contains all the foundational types used by the animation
-- | system. Types are separated to avoid circular dependencies and provide
-- | a clean foundation for other animation modules.

module Hydrogen.Tour.Animation.Types
  ( -- * Easing Types
    EasingCurve(..)
  , EasingPreset(..)
    -- * Spring Types
  , SpringConfig
  , SpringPreset(..)
    -- * Morph Types
  , MorphConfig
  , MorphTarget(..)
    -- * Animation Types
  , TourAnimation(..)
  , AnimationDirection(..)
  , AnimationFill(..)
  , AnimationPlayState(..)
  , AnimationComposition(..)
    -- * Reduced Motion Types
  , ReducedMotionStrategy(..)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , show
  , (<>)
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Data.String (joinWith)
import Hydrogen.Tour.Types (Milliseconds, Pixel)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // easing types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing curve for animations
-- |
-- | Either a named preset or a custom cubic-bezier curve.
-- | All values are bounded to valid CSS ranges.
data EasingCurve
  = Preset EasingPreset
    -- ^ Named easing preset
  | CubicBezier Number Number Number Number
    -- ^ Custom cubic-bezier(x1, y1, x2, y2)
    -- | x1, x2 must be in [0, 1]
    -- | y1, y2 can exceed [0, 1] for overshoot

derive instance eqEasingCurve :: Eq EasingCurve
derive instance genericEasingCurve :: Generic EasingCurve _

instance showEasingCurve :: Show EasingCurve where
  show = genericShow

-- | Named easing presets
-- |
-- | These map to standard CSS timing functions or well-known curves.
data EasingPreset
  = EaseLinear
    -- ^ No easing (constant velocity)
  | EaseIn
    -- ^ Slow start, fast end
  | EaseOut
    -- ^ Fast start, slow end
  | EaseInOut
    -- ^ Slow start and end
  | EaseInQuad
    -- ^ Quadratic ease in
  | EaseOutQuad
    -- ^ Quadratic ease out
  | EaseInOutQuad
    -- ^ Quadratic ease in-out
  | EaseInCubic
    -- ^ Cubic ease in
  | EaseOutCubic
    -- ^ Cubic ease out
  | EaseInOutCubic
    -- ^ Cubic ease in-out
  | EaseInQuart
    -- ^ Quartic ease in
  | EaseOutQuart
    -- ^ Quartic ease out
  | EaseInOutQuart
    -- ^ Quartic ease in-out
  | EaseInExpo
    -- ^ Exponential ease in
  | EaseOutExpo
    -- ^ Exponential ease out
  | EaseInOutExpo
    -- ^ Exponential ease in-out
  | EaseInBack
    -- ^ Overshoot ease in
  | EaseOutBack
    -- ^ Overshoot ease out
  | EaseInOutBack
    -- ^ Overshoot ease in-out

derive instance eqEasingPreset :: Eq EasingPreset
derive instance ordEasingPreset :: Ord EasingPreset
derive instance genericEasingPreset :: Generic EasingPreset _

instance showEasingPreset :: Show EasingPreset where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spring types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring physics configuration
-- |
-- | Based on damped harmonic oscillator:
-- | - stiffness: Spring constant (higher = faster, more force)
-- | - damping: Resistance (higher = less bouncy)
-- | - mass: Inertia (higher = slower response)
-- | - velocity: Initial velocity for momentum
type SpringConfig =
  { stiffness :: Number
    -- ^ Spring constant [1, 1000]
  , damping :: Number
    -- ^ Damping coefficient [1, 100]
  , mass :: Number
    -- ^ Mass [0.1, 10]
  , velocity :: Number
    -- ^ Initial velocity [-100, 100]
  , precision :: Number
    -- ^ Rest threshold [0.001, 0.1]
  }

-- | Named spring presets
data SpringPreset
  = SpringDefault
    -- ^ Balanced spring (React Spring default)
  | SpringSnappy
    -- ^ Quick response, minimal bounce
  | SpringGentle
    -- ^ Smooth, slower transition
  | SpringBouncy
    -- ^ Playful bounce
  | SpringStiff
    -- ^ Immediate response

derive instance eqSpringPreset :: Eq SpringPreset
derive instance ordSpringPreset :: Ord SpringPreset
derive instance genericSpringPreset :: Generic SpringPreset _

instance showSpringPreset :: Show SpringPreset where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // morph types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for spotlight morph transitions
-- |
-- | Controls how the spotlight shape animates between targets.
type MorphConfig =
  { duration :: Milliseconds
    -- ^ Duration if using CSS transitions
  , spring :: Maybe SpringConfig
    -- ^ Optional spring physics (overrides duration)
  , easing :: EasingCurve
    -- ^ Easing curve (when not using spring)
  , morphPath :: Boolean
    -- ^ Whether to morph the path shape (vs. instant)
  }

-- | Target states for morph animation
data MorphTarget
  = MorphToRect
      { x :: Pixel
      , y :: Pixel
      , width :: Pixel
      , height :: Pixel
      , borderRadius :: Pixel
      }
  | MorphToCircle
      { cx :: Pixel
      , cy :: Pixel
      , r :: Pixel
      }
  | MorphToViewport
    -- ^ Full viewport (no spotlight)
  | MorphHidden
    -- ^ Invisible state

derive instance eqMorphTarget :: Eq MorphTarget
derive instance genericMorphTarget :: Generic MorphTarget _

instance showMorphTarget :: Show MorphTarget where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tour animation description
-- |
-- | Pure data describing an animation. The runtime interprets this.
data TourAnimation
  = AnimFade
      { opacity :: { from :: Number, to :: Number }
      , duration :: Milliseconds
      , easing :: EasingCurve
      }
  | AnimSlide
      { translate :: { fromX :: Pixel, fromY :: Pixel, toX :: Pixel, toY :: Pixel }
      , duration :: Milliseconds
      , easing :: EasingCurve
      }
  | AnimScale
      { scale :: { from :: Number, to :: Number }
      , transformOrigin :: String
      , duration :: Milliseconds
      , easing :: EasingCurve
      }
  | AnimSpring
      { property :: String
      , from :: Number
      , to :: Number
      , spring :: SpringConfig
      }
  | AnimComposite
      { animations :: Array TourAnimation
      , composition :: AnimationComposition
      }

derive instance eqTourAnimation :: Eq TourAnimation
derive instance genericTourAnimation :: Generic TourAnimation _

-- | Manual Show instance to handle recursive AnimComposite
instance showTourAnimation :: Show TourAnimation where
  show = case _ of
    AnimFade cfg -> 
      "(AnimFade { opacity: " <> show cfg.opacity <> 
      ", duration: " <> show cfg.duration <> 
      ", easing: " <> show cfg.easing <> " })"
    AnimSlide cfg ->
      "(AnimSlide { translate: " <> show cfg.translate <>
      ", duration: " <> show cfg.duration <>
      ", easing: " <> show cfg.easing <> " })"
    AnimScale cfg ->
      "(AnimScale { scale: " <> show cfg.scale <>
      ", transformOrigin: " <> show cfg.transformOrigin <>
      ", duration: " <> show cfg.duration <>
      ", easing: " <> show cfg.easing <> " })"
    AnimSpring cfg ->
      "(AnimSpring { property: " <> show cfg.property <>
      ", from: " <> show cfg.from <>
      ", to: " <> show cfg.to <>
      ", spring: " <> show cfg.spring <> " })"
    AnimComposite cfg ->
      "(AnimComposite { animations: [" <> 
      joinWith ", " (map show cfg.animations) <>
      "], composition: " <> show cfg.composition <> " })"

-- | Animation direction
data AnimationDirection
  = Normal
  | Reverse
  | Alternate
  | AlternateReverse

derive instance eqAnimationDirection :: Eq AnimationDirection
derive instance genericAnimationDirection :: Generic AnimationDirection _

instance showAnimationDirection :: Show AnimationDirection where
  show = genericShow

-- | Animation fill mode
data AnimationFill
  = FillNone
  | FillForwards
  | FillBackwards
  | FillBoth

derive instance eqAnimationFill :: Eq AnimationFill
derive instance genericAnimationFill :: Generic AnimationFill _

instance showAnimationFill :: Show AnimationFill where
  show = genericShow

-- | Animation play state
data AnimationPlayState
  = Playing
  | Paused

derive instance eqAnimationPlayState :: Eq AnimationPlayState
derive instance genericAnimationPlayState :: Generic AnimationPlayState _

instance showAnimationPlayState :: Show AnimationPlayState where
  show = genericShow

-- | How multiple animations compose
data AnimationComposition
  = Sequence
    -- ^ Play one after another
  | Parallel
    -- ^ Play simultaneously
  | Stagger Milliseconds
    -- ^ Parallel with delay between each

derive instance eqAnimationComposition :: Eq AnimationComposition
derive instance genericAnimationComposition :: Generic AnimationComposition _

instance showAnimationComposition :: Show AnimationComposition where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // reduced motion types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strategy for reduced motion preference
-- |
-- | Users can enable "prefers-reduced-motion" in their OS settings.
-- | We should respect this preference.
data ReducedMotionStrategy
  = InstantTransition
    -- ^ Instant state change, no animation
  | FadeOnly
    -- ^ Allow fade, but no movement
  | SlowerAnimation
    -- ^ Keep animation but make it slower
  | PreserveAnimation
    -- ^ Ignore preference (not recommended)

derive instance eqReducedMotionStrategy :: Eq ReducedMotionStrategy
derive instance genericReducedMotionStrategy :: Generic ReducedMotionStrategy _

instance showReducedMotionStrategy :: Show ReducedMotionStrategy where
  show = genericShow
