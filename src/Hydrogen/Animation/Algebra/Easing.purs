-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // animation // algebra // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing functions for animation timing.
-- |
-- | Easing transforms linear progress [0,1] into curved progress.
-- | All functions preserve boundaries: f(0) = 0, f(1) = 1.

module Hydrogen.Animation.Algebra.Easing
  ( -- Easing type
    Easing
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
  
  -- Configuration types
  , SpringConfig(SpringConfig)
  , BezierCurve(BezierCurve)
  
  -- Math utilities (exported for other modules)
  , pow
  , ln
  , exp
  , sqrt
  , sin
  , cos
  , pi
  ) where

import Prelude
  ( class Eq
  , eq
  , otherwise
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (==)
  , (&&)
  )

import Data.Newtype (class Newtype, unwrap)
import Data.Ord (abs)

import Hydrogen.Animation.Time (Progress(Progress))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Configuration Types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing function type: Progress -> Progress.
-- | Transforms linear time into curved time.
-- | Must satisfy: f(0) = 0, f(1) = 1 (boundary preservation).
type EasingFunction = Progress -> Progress

-- | Spring physics configuration.
-- | All parameters are bounded to physically meaningful ranges.
newtype SpringConfig = SpringConfig
  { tension :: Number    -- Stiffness [0, 1000], default 170
  , friction :: Number   -- Damping [0, 100], default 26
  , mass :: Number       -- Mass [0.1, 10], default 1
  }

derive instance Eq SpringConfig

-- | Cubic bezier control points for custom easing.
-- | P0 = (0, 0), P3 = (1, 1) are fixed.
-- | P1 and P2 are the control points we specify.
newtype BezierCurve = BezierCurve
  { x1 :: Number  -- P1.x in [0, 1]
  , y1 :: Number  -- P1.y in [-2, 2] (can overshoot)
  , x2 :: Number  -- P2.x in [0, 1]
  , y2 :: Number  -- P2.y in [-2, 2] (can overshoot)
  }

derive instance Eq BezierCurve

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Easing ADT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing algebraic data type.
-- | Each constructor represents a different time-warping function.
data Easing
  = Linear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseInQuad
  | EaseOutQuad
  | EaseInOutQuad
  | EaseInCubic
  | EaseOutCubic
  | EaseInOutCubic
  | EaseInQuart
  | EaseOutQuart
  | EaseInOutQuart
  | EaseInQuint
  | EaseOutQuint
  | EaseInOutQuint
  | EaseInExpo
  | EaseOutExpo
  | EaseInOutExpo
  | EaseInCirc
  | EaseOutCirc
  | EaseInOutCirc
  | EaseInBack
  | EaseOutBack
  | EaseInOutBack
  | EaseInElastic
  | EaseOutElastic
  | EaseInOutElastic
  | EaseInBounce
  | EaseOutBounce
  | EaseInOutBounce
  | Spring SpringConfig
  | CubicBezier BezierCurve
  | Steps Int           -- Step function with n steps
  | Custom EasingFunction

-- | Manual Eq instance because Custom contains a function type.
-- | Custom easings are never considered equal (functions aren't comparable).
instance Eq Easing where
  eq Linear Linear = true
  eq EaseIn EaseIn = true
  eq EaseOut EaseOut = true
  eq EaseInOut EaseInOut = true
  eq EaseInQuad EaseInQuad = true
  eq EaseOutQuad EaseOutQuad = true
  eq EaseInOutQuad EaseInOutQuad = true
  eq EaseInCubic EaseInCubic = true
  eq EaseOutCubic EaseOutCubic = true
  eq EaseInOutCubic EaseInOutCubic = true
  eq EaseInQuart EaseInQuart = true
  eq EaseOutQuart EaseOutQuart = true
  eq EaseInOutQuart EaseInOutQuart = true
  eq EaseInQuint EaseInQuint = true
  eq EaseOutQuint EaseOutQuint = true
  eq EaseInOutQuint EaseInOutQuint = true
  eq EaseInExpo EaseInExpo = true
  eq EaseOutExpo EaseOutExpo = true
  eq EaseInOutExpo EaseInOutExpo = true
  eq EaseInCirc EaseInCirc = true
  eq EaseOutCirc EaseOutCirc = true
  eq EaseInOutCirc EaseInOutCirc = true
  eq EaseInBack EaseInBack = true
  eq EaseOutBack EaseOutBack = true
  eq EaseInOutBack EaseInOutBack = true
  eq EaseInElastic EaseInElastic = true
  eq EaseOutElastic EaseOutElastic = true
  eq EaseInOutElastic EaseInOutElastic = true
  eq EaseInBounce EaseInBounce = true
  eq EaseOutBounce EaseOutBounce = true
  eq EaseInOutBounce EaseInOutBounce = true
  eq (Spring a) (Spring b) = a == b
  eq (CubicBezier a) (CubicBezier b) = a == b
  eq (Steps a) (Steps b) = a == b
  eq (Custom _) (Custom _) = false  -- Functions cannot be compared
  eq _ _ = false

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Easing Application
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Apply easing function to progress.
-- | Pure function: same progress + same easing = same output.
applyEasing :: Easing -> Progress -> Progress
applyEasing easing (Progress t) = Progress (applyEasingNumber easing t)

-- | Internal: apply easing to raw number.
applyEasingNumber :: Easing -> Number -> Number
applyEasingNumber Linear t = t
applyEasingNumber EaseIn t = t * t
applyEasingNumber EaseOut t = t * (2.0 - t)
applyEasingNumber EaseInOut t =
  if t < 0.5
    then 2.0 * t * t
    else (-1.0) + (4.0 - 2.0 * t) * t
applyEasingNumber EaseInQuad t = t * t
applyEasingNumber EaseOutQuad t = t * (2.0 - t)
applyEasingNumber EaseInOutQuad t =
  if t < 0.5
    then 2.0 * t * t
    else (-1.0) + (4.0 - 2.0 * t) * t
applyEasingNumber EaseInCubic t = t * t * t
applyEasingNumber EaseOutCubic t =
  let t' = t - 1.0
  in t' * t' * t' + 1.0
applyEasingNumber EaseInOutCubic t =
  if t < 0.5
    then 4.0 * t * t * t
    else (t - 1.0) * (2.0 * t - 2.0) * (2.0 * t - 2.0) + 1.0
applyEasingNumber EaseInQuart t = t * t * t * t
applyEasingNumber EaseOutQuart t =
  let t' = t - 1.0
  in 1.0 - t' * t' * t' * t'
applyEasingNumber EaseInOutQuart t =
  if t < 0.5
    then 8.0 * t * t * t * t
    else 1.0 - 8.0 * (t - 1.0) * (t - 1.0) * (t - 1.0) * (t - 1.0)
applyEasingNumber EaseInQuint t = t * t * t * t * t
applyEasingNumber EaseOutQuint t =
  let t' = t - 1.0
  in 1.0 + t' * t' * t' * t' * t'
applyEasingNumber EaseInOutQuint t =
  if t < 0.5
    then 16.0 * t * t * t * t * t
    else 1.0 + 16.0 * (t - 1.0) * (t - 1.0) * (t - 1.0) * (t - 1.0) * (t - 1.0)
applyEasingNumber EaseInExpo t =
  if t == 0.0 then 0.0 else pow 2.0 (10.0 * (t - 1.0))
applyEasingNumber EaseOutExpo t =
  if t == 1.0 then 1.0 else 1.0 - pow 2.0 ((-10.0) * t)
applyEasingNumber EaseInOutExpo t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = pow 2.0 (20.0 * t - 10.0) / 2.0
  | otherwise = (2.0 - pow 2.0 ((-20.0) * t + 10.0)) / 2.0
applyEasingNumber EaseInCirc t = 1.0 - sqrt (1.0 - t * t)
applyEasingNumber EaseOutCirc t = sqrt (1.0 - (t - 1.0) * (t - 1.0))
applyEasingNumber EaseInOutCirc t =
  if t < 0.5
    then (1.0 - sqrt (1.0 - 4.0 * t * t)) / 2.0
    else (sqrt (1.0 - ((-2.0) * t + 2.0) * ((-2.0) * t + 2.0)) + 1.0) / 2.0
applyEasingNumber EaseInBack t =
  let c1 = 1.70158
      c3 = c1 + 1.0
  in c3 * t * t * t - c1 * t * t
applyEasingNumber EaseOutBack t =
  let c1 = 1.70158
      c3 = c1 + 1.0
      t' = t - 1.0
  in 1.0 + c3 * t' * t' * t' + c1 * t' * t'
applyEasingNumber EaseInOutBack t =
  let c1 = 1.70158
      c2 = c1 * 1.525
  in if t < 0.5
    then (2.0 * t) * (2.0 * t) * ((c2 + 1.0) * 2.0 * t - c2) / 2.0
    else ((2.0 * t - 2.0) * (2.0 * t - 2.0) * ((c2 + 1.0) * (t * 2.0 - 2.0) + c2) + 2.0) / 2.0
applyEasingNumber EaseInElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise =
      let c4 = (2.0 * pi) / 3.0
      in (-(pow 2.0 (10.0 * t - 10.0))) * sin ((t * 10.0 - 10.75) * c4)
applyEasingNumber EaseOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise =
      let c4 = (2.0 * pi) / 3.0
      in pow 2.0 ((-10.0) * t) * sin ((t * 10.0 - 0.75) * c4) + 1.0
applyEasingNumber EaseInOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 =
      let c5 = (2.0 * pi) / 4.5
      in (-(pow 2.0 (20.0 * t - 10.0) * sin ((20.0 * t - 11.125) * c5))) / 2.0
  | otherwise =
      let c5 = (2.0 * pi) / 4.5
      in (pow 2.0 ((-20.0) * t + 10.0) * sin ((20.0 * t - 11.125) * c5)) / 2.0 + 1.0
applyEasingNumber EaseInBounce t = 1.0 - easeOutBounceImpl (1.0 - t)
applyEasingNumber EaseOutBounce t = easeOutBounceImpl t
applyEasingNumber EaseInOutBounce t =
  if t < 0.5
    then (1.0 - applyEasingNumber EaseOutBounce (1.0 - 2.0 * t)) / 2.0
    else (1.0 + applyEasingNumber EaseOutBounce (2.0 * t - 1.0)) / 2.0
applyEasingNumber (Spring (SpringConfig cfg)) t =
  -- Simplified spring approximation using damped harmonic oscillator
  let omega = sqrt cfg.tension / cfg.mass
      zeta = cfg.friction / (2.0 * sqrt (cfg.tension * cfg.mass))
      dampedFreq = omega * sqrt (1.0 - zeta * zeta)
      envelope = exp ((-zeta) * omega * t * 3.0)
  in 1.0 - envelope * cos (dampedFreq * t * 3.0)
applyEasingNumber (CubicBezier (BezierCurve b)) t =
  cubicBezierValue b.x1 b.y1 b.x2 b.y2 t
applyEasingNumber (Steps n) t =
  let step = nativeIntToNumber n
  in nativeFloor (t * step) / step
applyEasingNumber (Custom f) t = unwrap (f (Progress t))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Helper Functions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounce easing implementation.
easeOutBounceImpl :: Number -> Number
easeOutBounceImpl t =
  let n1 = 7.5625
      d1 = 2.75
  in if t < 1.0 / d1
       then n1 * t * t
       else if t < 2.0 / d1
         then
           let t' = t - 1.5 / d1
           in n1 * t' * t' + 0.75
         else if t < 2.5 / d1
           then
             let t' = t - 2.25 / d1
             in n1 * t' * t' + 0.9375
           else
             let t' = t - 2.625 / d1
             in n1 * t' * t' + 0.984375

-- | Cubic bezier evaluation using Newton-Raphson method.
cubicBezierValue :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezierValue x1 y1 x2 y2 t =
  let u = solveCubicBezierX x1 x2 t 8
  in bezierY y1 y2 u
  where
    bezierX :: Number -> Number -> Number -> Number
    bezierX p1 p2 u =
      let u2 = u * u
          u3 = u2 * u
          mt = 1.0 - u
          mt2 = mt * mt
      in 3.0 * mt2 * u * p1 + 3.0 * mt * u2 * p2 + u3

    bezierY :: Number -> Number -> Number -> Number
    bezierY p1 p2 u =
      let u2 = u * u
          u3 = u2 * u
          mt = 1.0 - u
          mt2 = mt * mt
      in 3.0 * mt2 * u * p1 + 3.0 * mt * u2 * p2 + u3

    solveCubicBezierX :: Number -> Number -> Number -> Int -> Number
    solveCubicBezierX p1 p2 target iterations =
      go t iterations
      where
        go :: Number -> Int -> Number
        go guess 0 = guess
        go guess n =
          let currentX = bezierX p1 p2 guess
              derivative = bezierDerivativeX p1 p2 guess
          in if abs derivative < 0.0001
               then guess
               else go (guess - (currentX - target) / derivative) (n - 1)

        bezierDerivativeX :: Number -> Number -> Number -> Number
        bezierDerivativeX pp1 pp2 u =
          let mt = 1.0 - u
          in 3.0 * mt * mt * pp1 + 6.0 * mt * u * (pp2 - pp1) + 3.0 * u * u * (1.0 - pp2)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Math Functions (FFI)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Power function for easing calculations.
pow :: Number -> Number -> Number
pow base exponent = 
  if base == 0.0 then 0.0
  else if exponent == 0.0 then 1.0
  else exp (exponent * ln base)

-- | Natural logarithm.
ln :: Number -> Number
ln x = nativeLog x

-- | Exponential function.
exp :: Number -> Number
exp x = nativeExp x

-- | Square root.
sqrt :: Number -> Number
sqrt x = nativeSqrt x

-- | Sine function.
sin :: Number -> Number
sin x = nativeSin x

-- | Cosine function.
cos :: Number -> Number
cos x = nativeCos x

-- | Pi constant.
pi :: Number
pi = 3.141592653589793

-- Native math functions (FFI to JavaScript Math)
foreign import nativeLog :: Number -> Number
foreign import nativeExp :: Number -> Number
foreign import nativeSqrt :: Number -> Number
foreign import nativeSin :: Number -> Number
foreign import nativeCos :: Number -> Number
foreign import nativeFloor :: Number -> Number
foreign import nativeIntToNumber :: Int -> Number
