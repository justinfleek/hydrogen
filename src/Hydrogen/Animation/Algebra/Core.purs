-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // animation // algebra // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core animation type and lawful instances.
-- |
-- | Animation is a Functor, Applicative, Semigroup, and Monoid.
-- | All instances obey their respective laws.

module Hydrogen.Animation.Algebra.Core
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
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Apply
  , class Applicative
  , class Semigroup
  , class Monoid
  , mempty
  , max
  , (<>)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (==)
  )

import Data.Int as Int

import Hydrogen.Animation.Time (Duration(Duration), Progress(Progress))
import Hydrogen.Animation.Algebra.Easing (Easing(Linear), applyEasing)
import Hydrogen.Animation.Algebra.Transform (Transform2D, Transform3D, Opacity(Opacity))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Animation Value
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | The animation value type: what gets animated.
-- | This is a Semigroup/Monoid to allow composition.
data AnimationValue
  = TransformValue Transform2D
  | Transform3DValue Transform3D
  | OpacityValue Opacity
  | CompositeValue (Array AnimationValue)

derive instance Eq AnimationValue

instance Semigroup AnimationValue where
  append (TransformValue a) (TransformValue b) = TransformValue (a <> b)
  append (Transform3DValue a) (Transform3DValue b) = Transform3DValue (a <> b)
  append (OpacityValue (Opacity a)) (OpacityValue (Opacity b)) = 
    OpacityValue (Opacity (a * b))
  append (CompositeValue a) (CompositeValue b) = CompositeValue (a <> b)
  append a b = CompositeValue [a, b]

instance Monoid AnimationValue where
  mempty = CompositeValue []

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Animation Type
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core animation functor: Progress -> a
-- | An animation is a function from normalized time to a value.
type AnimationF a = Progress -> a

-- | Complete animation with duration, easing, and value function.
-- | This is the primary type for defining animations.
newtype Animation a = Animation
  { dur :: Duration
  , easing :: Easing
  , sample :: AnimationF a
  }

-- | Run an animation at a specific progress point.
runAnimation :: forall a. Animation a -> Progress -> a
runAnimation (Animation anim) progress =
  anim.sample (applyEasing anim.easing progress)

-- | Get the duration of an animation.
duration :: forall a. Animation a -> Duration
duration (Animation anim) = anim.dur

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Lawful Instances
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Functor: transform the output value.
instance Functor Animation where
  map f (Animation anim) = Animation
    { dur: anim.dur
    , easing: anim.easing
    , sample: \p -> f (anim.sample p)
    }

-- | Apply: parallel composition with matching durations.
-- | Takes the longer duration, runs both animations in parallel.
instance Apply Animation where
  apply (Animation f) (Animation a) = Animation
    { dur: max f.dur a.dur
    , easing: Linear
    , sample: \p -> (f.sample p) (a.sample p)
    }

-- | Applicative: lift a pure value into a zero-duration animation.
instance Applicative Animation where
  pure a = Animation
    { dur: Duration 0
    , easing: Linear
    , sample: \_ -> a
    }

-- | Semigroup: sequential composition.
-- | a <> b means "first a, then b".
instance Semigroup a => Semigroup (Animation a) where
  append (Animation a1) (Animation a2) = Animation
    { dur: a1.dur <> a2.dur
    , easing: Linear
    , sample: \(Progress p) ->
        let (Duration d1) = a1.dur
            (Duration d2) = a2.dur
            totalDur = Int.toNumber (d1 + d2)
            boundary = if totalDur == 0.0 then 0.5 else Int.toNumber d1 / totalDur
        in if p < boundary
             then a1.sample (Progress (if boundary == 0.0 then 0.0 else p / boundary))
             else let p2 = if boundary == 1.0 then 1.0 else (p - boundary) / (1.0 - boundary)
                  in a1.sample (Progress 1.0) <> a2.sample (Progress p2)
    }

-- | Monoid: empty animation (zero duration, identity value).
instance Monoid a => Monoid (Animation a) where
  mempty = Animation
    { dur: Duration 0
    , easing: Linear
    , sample: \_ -> mempty
    }
