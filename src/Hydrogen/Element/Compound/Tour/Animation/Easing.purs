-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // tour // animation // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing Curves — Acceleration curves for animations.
-- |
-- | Comprehensive set covering CSS standard easings and physics-based options.

module Hydrogen.Element.Compound.Tour.Animation.Easing
  ( EasingCurve
      ( EaseLinear
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
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseInBounce
      , EaseOutBounce
      , EaseInOutBounce
      , EaseSpring
      , EaseCustom
      )
  , easingToCss
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // easing curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing curve for animations.
-- |
-- | Comprehensive set covering CSS standard easings and physics-based options.
data EasingCurve
  = EaseLinear          -- ^ No acceleration
  | EaseIn              -- ^ Accelerate from zero
  | EaseOut             -- ^ Decelerate to zero
  | EaseInOut           -- ^ Accelerate then decelerate
  | EaseInQuad          -- ^ Quadratic ease in
  | EaseOutQuad         -- ^ Quadratic ease out
  | EaseInOutQuad       -- ^ Quadratic ease in-out
  | EaseInCubic         -- ^ Cubic ease in
  | EaseOutCubic        -- ^ Cubic ease out
  | EaseInOutCubic      -- ^ Cubic ease in-out
  | EaseInQuart         -- ^ Quartic ease in
  | EaseOutQuart        -- ^ Quartic ease out
  | EaseInOutQuart      -- ^ Quartic ease in-out
  | EaseInExpo          -- ^ Exponential ease in
  | EaseOutExpo         -- ^ Exponential ease out
  | EaseInOutExpo       -- ^ Exponential ease in-out
  | EaseInBack          -- ^ Back ease in (overshoot)
  | EaseOutBack         -- ^ Back ease out (overshoot)
  | EaseInOutBack       -- ^ Back ease in-out
  | EaseInBounce        -- ^ Bounce ease in
  | EaseOutBounce       -- ^ Bounce ease out
  | EaseInOutBounce     -- ^ Bounce ease in-out
  | EaseSpring          -- ^ Physics-based spring (see SpringConfig)
  | EaseCustom String   -- ^ Custom cubic-bezier string

derive instance eqEasingCurve :: Eq EasingCurve
derive instance ordEasingCurve :: Ord EasingCurve

instance showEasingCurve :: Show EasingCurve where
  show EaseLinear = "linear"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show EaseInQuad = "ease-in-quad"
  show EaseOutQuad = "ease-out-quad"
  show EaseInOutQuad = "ease-in-out-quad"
  show EaseInCubic = "ease-in-cubic"
  show EaseOutCubic = "ease-out-cubic"
  show EaseInOutCubic = "ease-in-out-cubic"
  show EaseInQuart = "ease-in-quart"
  show EaseOutQuart = "ease-out-quart"
  show EaseInOutQuart = "ease-in-out-quart"
  show EaseInExpo = "ease-in-expo"
  show EaseOutExpo = "ease-out-expo"
  show EaseInOutExpo = "ease-in-out-expo"
  show EaseInBack = "ease-in-back"
  show EaseOutBack = "ease-out-back"
  show EaseInOutBack = "ease-in-out-back"
  show EaseInBounce = "ease-in-bounce"
  show EaseOutBounce = "ease-out-bounce"
  show EaseInOutBounce = "ease-in-out-bounce"
  show EaseSpring = "spring"
  show (EaseCustom s) = "cubic-bezier(" <> s <> ")"

instance boundedEasingCurve :: Bounded EasingCurve where
  bottom = EaseLinear
  top = EaseCustom ""

-- | Convert easing to CSS timing function
easingToCss :: EasingCurve -> String
easingToCss = case _ of
  EaseLinear -> "linear"
  EaseIn -> "ease-in"
  EaseOut -> "ease-out"
  EaseInOut -> "ease-in-out"
  EaseInQuad -> "cubic-bezier(0.55, 0.085, 0.68, 0.53)"
  EaseOutQuad -> "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
  EaseInOutQuad -> "cubic-bezier(0.455, 0.03, 0.515, 0.955)"
  EaseInCubic -> "cubic-bezier(0.55, 0.055, 0.675, 0.19)"
  EaseOutCubic -> "cubic-bezier(0.215, 0.61, 0.355, 1)"
  EaseInOutCubic -> "cubic-bezier(0.645, 0.045, 0.355, 1)"
  EaseInQuart -> "cubic-bezier(0.895, 0.03, 0.685, 0.22)"
  EaseOutQuart -> "cubic-bezier(0.165, 0.84, 0.44, 1)"
  EaseInOutQuart -> "cubic-bezier(0.77, 0, 0.175, 1)"
  EaseInExpo -> "cubic-bezier(0.95, 0.05, 0.795, 0.035)"
  EaseOutExpo -> "cubic-bezier(0.19, 1, 0.22, 1)"
  EaseInOutExpo -> "cubic-bezier(1, 0, 0, 1)"
  EaseInBack -> "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
  EaseOutBack -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
  EaseInOutBack -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  EaseInBounce -> "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
  EaseOutBounce -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
  EaseInOutBounce -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  EaseSpring -> "cubic-bezier(0.5, 1.5, 0.5, 1)"
  EaseCustom s -> "cubic-bezier(" <> s <> ")"
