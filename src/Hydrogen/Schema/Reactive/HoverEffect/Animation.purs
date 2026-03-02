-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // reactive // hover-effect/animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverAnimation — Animation triggered on hover.
-- |
-- | ## Design Philosophy
-- |
-- | Describes animations to play when hovering:
-- | - Lottie animations (JSON-based vector animation)
-- | - CSS keyframe animation names
-- | - Spring-based transform animations
-- |
-- | ## Animation Timing
-- |
-- | - `playOnEnter`: Start animation when mouse enters
-- | - `playOnLeave`: Play reverse/exit animation when leaving
-- | - `loopWhileHovering`: Continuously loop while hovered
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Play Lottie animation on hover
-- | dogWag = hoverAnimationLottie "/animations/dog-wag.json"
-- |
-- | -- CSS animation
-- | pulse = hoverAnimationCss "pulse" 300.0
-- | ```

module Hydrogen.Schema.Reactive.HoverEffect.Animation
  ( HoverAnimation(HoverAnimation)
  , HoverAnimationType(HoverAnimNone, HoverAnimLottie, HoverAnimLottieInline, HoverAnimCss, HoverAnimSpring)
  , HoverSpringConfig
  , hoverAnimation
  , noHoverAnimation
  , hoverAnimationLottie
  , hoverAnimationCss
  , hoverAnimationSpring
  , defaultSpringConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // spring config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring animation configuration
type HoverSpringConfig =
  { stiffness :: Number      -- ^ Spring stiffness (higher = faster)
  , damping :: Number        -- ^ Damping ratio (1.0 = critically damped)
  , mass :: Number           -- ^ Virtual mass (affects momentum)
  }

-- | Default spring config (snappy, Apple-like feel)
defaultSpringConfig :: HoverSpringConfig
defaultSpringConfig =
  { stiffness: 300.0
  , damping: 20.0
  , mass: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of hover animation
data HoverAnimationType
  = HoverAnimNone                       -- ^ No animation
  | HoverAnimLottie String              -- ^ Lottie JSON URL
  | HoverAnimLottieInline String        -- ^ Inline Lottie JSON
  | HoverAnimCss String                 -- ^ CSS animation name
  | HoverAnimSpring HoverSpringConfig   -- ^ Spring physics animation

derive instance eqHoverAnimationType :: Eq HoverAnimationType

instance showHoverAnimationType :: Show HoverAnimationType where
  show HoverAnimNone = "none"
  show (HoverAnimLottie _) = "lottie"
  show (HoverAnimLottieInline _) = "lottie-inline"
  show (HoverAnimCss name) = "css:" <> name
  show (HoverAnimSpring _) = "spring"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hover animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation triggered on hover
newtype HoverAnimation = HoverAnimation
  { animationType :: HoverAnimationType  -- ^ Type of animation
  , playOnEnter :: Boolean               -- ^ Play when mouse enters
  , playOnLeave :: Boolean               -- ^ Play when mouse leaves
  , loopWhileHovering :: Boolean         -- ^ Loop while hovered
  , durationMs :: Number                 -- ^ Animation duration (milliseconds)
  , delayMs :: Number                    -- ^ Delay before starting (milliseconds)
  }

derive instance eqHoverAnimation :: Eq HoverAnimation

instance showHoverAnimation :: Show HoverAnimation where
  show (HoverAnimation a) = 
    "HoverAnimation(" <> show a.animationType <> 
    ", " <> show a.durationMs <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create hover animation with full configuration
hoverAnimation
  :: { animationType :: HoverAnimationType
     , playOnEnter :: Boolean
     , playOnLeave :: Boolean
     , loopWhileHovering :: Boolean
     , durationMs :: Number
     , delayMs :: Number
     }
  -> HoverAnimation
hoverAnimation cfg = HoverAnimation
  { animationType: cfg.animationType
  , playOnEnter: cfg.playOnEnter
  , playOnLeave: cfg.playOnLeave
  , loopWhileHovering: cfg.loopWhileHovering
  , durationMs: clampMs cfg.durationMs
  , delayMs: clampMs cfg.delayMs
  }
  where
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | No hover animation
noHoverAnimation :: HoverAnimation
noHoverAnimation = HoverAnimation
  { animationType: HoverAnimNone
  , playOnEnter: false
  , playOnLeave: false
  , loopWhileHovering: false
  , durationMs: 0.0
  , delayMs: 0.0
  }

-- | Play Lottie animation on hover
hoverAnimationLottie :: String -> HoverAnimation
hoverAnimationLottie url = HoverAnimation
  { animationType: HoverAnimLottie url
  , playOnEnter: true
  , playOnLeave: false
  , loopWhileHovering: false
  , durationMs: 1000.0
  , delayMs: 0.0
  }

-- | Play CSS animation on hover
hoverAnimationCss :: String -> Number -> HoverAnimation
hoverAnimationCss name duration = HoverAnimation
  { animationType: HoverAnimCss name
  , playOnEnter: true
  , playOnLeave: false
  , loopWhileHovering: false
  , durationMs: duration
  , delayMs: 0.0
  }

-- | Spring physics animation on hover
hoverAnimationSpring :: HoverSpringConfig -> HoverAnimation
hoverAnimationSpring spring = HoverAnimation
  { animationType: HoverAnimSpring spring
  , playOnEnter: true
  , playOnLeave: true
  , loopWhileHovering: false
  , durationMs: 500.0
  , delayMs: 0.0
  }
