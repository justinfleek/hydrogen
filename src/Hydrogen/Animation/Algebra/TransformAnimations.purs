-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // animation // algebra // transform-animations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform animation constructors.
-- |
-- | Factory functions for creating transform animations:
-- | translate, scale, rotate, skew, opacity.

module Hydrogen.Animation.Algebra.TransformAnimations
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
  ) where

import Prelude
  ( negate
  , max
  , min
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Hydrogen.Animation.Time (Duration, Progress(Progress))
import Hydrogen.Animation.Algebra.Easing (Easing, sin, cos)
import Hydrogen.Animation.Algebra.Transform (Transform2D(Transform2D), Transform3D(Transform3D), Opacity(Opacity))
import Hydrogen.Animation.Algebra.Core (Animation(Animation))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Translation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Translate along X axis.
translateX :: Number -> Number -> Duration -> Easing -> Animation Transform2D
translateX from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: value, f: 0.0 }
  }

-- | Translate along Y axis.
translateY :: Number -> Number -> Duration -> Easing -> Animation Transform2D
translateY from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: 0.0, f: value }
  }

-- | Translate in 2D.
translate 
  :: { fromX :: Number, fromY :: Number, toX :: Number, toY :: Number }
  -> Duration 
  -> Easing 
  -> Animation Transform2D
translate coords dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let x = coords.fromX + (coords.toX - coords.fromX) * p
          y = coords.fromY + (coords.toY - coords.fromY) * p
      in Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: x, f: y }
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Scaling
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Uniform scale animation.
scale :: Number -> Number -> Duration -> Easing -> Animation Transform2D
scale from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Transform2D { a: value, b: 0.0, c: 0.0, d: value, e: 0.0, f: 0.0 }
  }

-- | Non-uniform scale animation.
scaleXY 
  :: { fromX :: Number, fromY :: Number, toX :: Number, toY :: Number }
  -> Duration 
  -> Easing 
  -> Animation Transform2D
scaleXY coords dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let sx = coords.fromX + (coords.toX - coords.fromX) * p
          sy = coords.fromY + (coords.toY - coords.fromY) * p
      in Transform2D { a: sx, b: 0.0, c: 0.0, d: sy, e: 0.0, f: 0.0 }
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Rotation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 2D rotation animation (radians).
rotate :: Number -> Number -> Duration -> Easing -> Animation Transform2D
rotate from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          c = cos angle
          s = sin angle
      in Transform2D { a: c, b: s, c: negate s, d: c, e: 0.0, f: 0.0 }
  }

-- | 3D rotation animation around arbitrary axis.
rotate3D
  :: { x :: Number, y :: Number, z :: Number }  -- axis (normalized)
  -> Number  -- from angle (radians)
  -> Number  -- to angle (radians)
  -> Duration
  -> Easing
  -> Animation Transform3D
rotate3D axis from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          c = cos angle
          s = sin angle
          t = 1.0 - c
          x = axis.x
          y = axis.y
          z = axis.z
      in Transform3D
        { m11: t*x*x + c,     m12: t*x*y - s*z,   m13: t*x*z + s*y,   m14: 0.0
        , m21: t*x*y + s*z,   m22: t*y*y + c,     m23: t*y*z - s*x,   m24: 0.0
        , m31: t*x*z - s*y,   m32: t*y*z + s*x,   m33: t*z*z + c,     m34: 0.0
        , m41: 0.0,           m42: 0.0,           m43: 0.0,           m44: 1.0
        }
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Skew
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Skew along X axis.
skewX :: Number -> Number -> Duration -> Easing -> Animation Transform2D
skewX from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          t = tan angle
      in Transform2D { a: 1.0, b: 0.0, c: t, d: 1.0, e: 0.0, f: 0.0 }
  }
  where
    tan :: Number -> Number
    tan x = sin x / cos x

-- | Skew along Y axis.
skewY :: Number -> Number -> Duration -> Easing -> Animation Transform2D
skewY from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          t = tan angle
      in Transform2D { a: 1.0, b: t, c: 0.0, d: 1.0, e: 0.0, f: 0.0 }
  }
  where
    tan :: Number -> Number
    tan x = sin x / cos x

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Opacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Opacity fade animation.
opacity :: Number -> Number -> Duration -> Easing -> Animation Opacity
opacity from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Opacity (max 0.0 (min 1.0 value))
  }
