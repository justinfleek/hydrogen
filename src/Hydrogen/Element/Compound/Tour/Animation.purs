-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // tour // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Animation — Transitions and timing for tour steps.
-- |
-- | ## Architecture
-- |
-- | Animations control how tour elements move and transition:
-- | - Tooltip entrance/exit animations
-- | - Step-to-step transitions
-- | - Highlight morphing
-- | - Scroll animations
-- |
-- | ## Schema Mapping
-- |
-- | | Type            | Pillar    | Purpose                              |
-- | |-----------------|-----------|--------------------------------------|
-- | | TransitionKind  | Temporal  | How elements animate between states  |
-- | | EasingCurve     | Temporal  | Acceleration curve for animations    |
-- | | Duration        | Temporal  | Animation duration                   |
-- | | Delay           | Temporal  | Delay before animation starts        |
-- | | EntranceKind    | Temporal  | How tooltip appears                  |
-- | | ExitKind        | Temporal  | How tooltip disappears               |

module Hydrogen.Element.Compound.Tour.Animation
  ( -- * Transition Kind
    TransitionKind
      ( TransitionNone
      , TransitionFade
      , TransitionSlide
      , TransitionZoom
      , TransitionFlip
      , TransitionMorph
      , TransitionCrossfade
      )
  
  -- * Re-export: Easing Curve
  , module ReexportEasing
  
  -- * Entrance Kind
  , EntranceKind
      ( EnterFade
      , EnterSlideUp
      , EnterSlideDown
      , EnterSlideLeft
      , EnterSlideRight
      , EnterZoomIn
      , EnterFlipX
      , EnterFlipY
      , EnterPop
      , EnterNone
      )
  
  -- * Exit Kind
  , ExitKind
      ( ExitFade
      , ExitSlideUp
      , ExitSlideDown
      , ExitSlideLeft
      , ExitSlideRight
      , ExitZoomOut
      , ExitFlipX
      , ExitFlipY
      , ExitPop
      , ExitNone
      )
  
  -- * Duration
  , Duration
  , duration
  , unwrapDuration
  , instant
  , fast
  , normal
  , slow
  , verySlow
  
  -- * Delay
  , Delay
  , delay
  , unwrapDelay
  , noDelay
  , shortDelay
  , mediumDelay
  , longDelay
  
  -- * Spring Config
  , SpringConfig
  , springConfig
  , defaultSpring
  , bouncySpring
  , stiffSpring
  , gentleSpring
  
  -- * Animation Config
  , AnimationConfig
  , defaultAnimationConfig
  , fastAnimationConfig
  , slowAnimationConfig
  , noAnimationConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , max
  , show
  , (<>)
  )

import Hydrogen.Element.Compound.Tour.Animation.Easing
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
  ) as ReexportEasing

-- Internal import for AnimationConfig defaults
import Hydrogen.Element.Compound.Tour.Animation.Easing (EasingCurve(EaseOutCubic, EaseOutBack, EaseInOutCubic))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transition kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How elements transition between steps.
-- |
-- | Applied to the entire tour container when changing steps.
data TransitionKind
  = TransitionNone       -- ^ Instant change
  | TransitionFade       -- ^ Crossfade between steps
  | TransitionSlide      -- ^ Slide in direction of navigation
  | TransitionZoom       -- ^ Zoom in/out between steps
  | TransitionFlip       -- ^ 3D flip animation
  | TransitionMorph      -- ^ Morph highlight shape to new target
  | TransitionCrossfade  -- ^ Overlap old/new with crossfade

derive instance eqTransitionKind :: Eq TransitionKind
derive instance ordTransitionKind :: Ord TransitionKind

instance showTransitionKind :: Show TransitionKind where
  show TransitionNone = "none"
  show TransitionFade = "fade"
  show TransitionSlide = "slide"
  show TransitionZoom = "zoom"
  show TransitionFlip = "flip"
  show TransitionMorph = "morph"
  show TransitionCrossfade = "crossfade"

instance boundedTransitionKind :: Bounded TransitionKind where
  bottom = TransitionNone
  top = TransitionCrossfade

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entrance kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How tooltip enters the view.
data EntranceKind
  = EnterFade        -- ^ Fade in
  | EnterSlideUp     -- ^ Slide from below
  | EnterSlideDown   -- ^ Slide from above
  | EnterSlideLeft   -- ^ Slide from right
  | EnterSlideRight  -- ^ Slide from left
  | EnterZoomIn      -- ^ Scale up from small
  | EnterFlipX       -- ^ Flip on horizontal axis
  | EnterFlipY       -- ^ Flip on vertical axis
  | EnterPop         -- ^ Pop in with overshoot
  | EnterNone        -- ^ Instant appearance

derive instance eqEntranceKind :: Eq EntranceKind
derive instance ordEntranceKind :: Ord EntranceKind

instance showEntranceKind :: Show EntranceKind where
  show EnterFade = "fade"
  show EnterSlideUp = "slide-up"
  show EnterSlideDown = "slide-down"
  show EnterSlideLeft = "slide-left"
  show EnterSlideRight = "slide-right"
  show EnterZoomIn = "zoom-in"
  show EnterFlipX = "flip-x"
  show EnterFlipY = "flip-y"
  show EnterPop = "pop"
  show EnterNone = "none"

instance boundedEntranceKind :: Bounded EntranceKind where
  bottom = EnterFade
  top = EnterNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // exit kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How tooltip exits the view.
data ExitKind
  = ExitFade        -- ^ Fade out
  | ExitSlideUp     -- ^ Slide upward
  | ExitSlideDown   -- ^ Slide downward
  | ExitSlideLeft   -- ^ Slide to left
  | ExitSlideRight  -- ^ Slide to right
  | ExitZoomOut     -- ^ Scale down to nothing
  | ExitFlipX       -- ^ Flip on horizontal axis
  | ExitFlipY       -- ^ Flip on vertical axis
  | ExitPop         -- ^ Pop out with undershoot
  | ExitNone        -- ^ Instant disappearance

derive instance eqExitKind :: Eq ExitKind
derive instance ordExitKind :: Ord ExitKind

instance showExitKind :: Show ExitKind where
  show ExitFade = "fade"
  show ExitSlideUp = "slide-up"
  show ExitSlideDown = "slide-down"
  show ExitSlideLeft = "slide-left"
  show ExitSlideRight = "slide-right"
  show ExitZoomOut = "zoom-out"
  show ExitFlipX = "flip-x"
  show ExitFlipY = "flip-y"
  show ExitPop = "pop"
  show ExitNone = "none"

instance boundedExitKind :: Bounded ExitKind where
  bottom = ExitFade
  top = ExitNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation duration in milliseconds.
newtype Duration = Duration Int

derive instance eqDuration :: Eq Duration
derive instance ordDuration :: Ord Duration

instance showDuration :: Show Duration where
  show (Duration ms) = "Duration(" <> show ms <> "ms)"

-- | Create a duration (clamped to non-negative)
duration :: Int -> Duration
duration ms = Duration (max 0 ms)

-- | Extract duration in milliseconds
unwrapDuration :: Duration -> Int
unwrapDuration (Duration ms) = ms

-- | Instant (0ms)
instant :: Duration
instant = Duration 0

-- | Fast (150ms)
fast :: Duration
fast = Duration 150

-- | Normal (300ms)
normal :: Duration
normal = Duration 300

-- | Slow (500ms)
slow :: Duration
slow = Duration 500

-- | Very slow (800ms)
verySlow :: Duration
verySlow = Duration 800

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // delay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation delay in milliseconds.
newtype Delay = Delay Int

derive instance eqDelay :: Eq Delay
derive instance ordDelay :: Ord Delay

instance showDelay :: Show Delay where
  show (Delay ms) = "Delay(" <> show ms <> "ms)"

-- | Create a delay (clamped to non-negative)
delay :: Int -> Delay
delay ms = Delay (max 0 ms)

-- | Extract delay in milliseconds
unwrapDelay :: Delay -> Int
unwrapDelay (Delay ms) = ms

-- | No delay (0ms)
noDelay :: Delay
noDelay = Delay 0

-- | Short delay (100ms)
shortDelay :: Delay
shortDelay = Delay 100

-- | Medium delay (300ms)
mediumDelay :: Delay
mediumDelay = Delay 300

-- | Long delay (500ms)
longDelay :: Delay
longDelay = Delay 500

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spring config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physics-based spring animation configuration.
-- |
-- | Based on Framer Motion's spring parameters.
type SpringConfig =
  { stiffness :: Number   -- ^ Spring stiffness (default: 100)
  , damping :: Number     -- ^ Damping ratio (default: 10)
  , mass :: Number        -- ^ Mass (default: 1)
  , velocity :: Number    -- ^ Initial velocity (default: 0)
  }

-- | Create a spring configuration
springConfig :: Number -> Number -> Number -> SpringConfig
springConfig stiff damp m =
  { stiffness: max 0.0 stiff
  , damping: max 0.0 damp
  , mass: max 0.1 m
  , velocity: 0.0
  }

-- | Default spring (balanced)
defaultSpring :: SpringConfig
defaultSpring = springConfig 100.0 10.0 1.0

-- | Bouncy spring (more oscillation)
bouncySpring :: SpringConfig
bouncySpring = springConfig 200.0 5.0 1.0

-- | Stiff spring (quick, less oscillation)
stiffSpring :: SpringConfig
stiffSpring = springConfig 400.0 30.0 1.0

-- | Gentle spring (slow, smooth)
gentleSpring :: SpringConfig
gentleSpring = springConfig 50.0 15.0 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete animation configuration for tour.
type AnimationConfig =
  { stepTransition :: TransitionKind    -- ^ Transition between steps
  , easing :: EasingCurve               -- ^ Default easing curve
  , duration :: Duration                -- ^ Default animation duration
  , entrance :: EntranceKind            -- ^ Tooltip entrance animation
  , exit :: ExitKind                    -- ^ Tooltip exit animation
  , entranceDelay :: Delay              -- ^ Delay before entrance
  , exitDelay :: Delay                  -- ^ Delay before exit
  , spring :: SpringConfig              -- ^ Spring config for spring easing
  , reduceMotion :: Boolean             -- ^ Respect prefers-reduced-motion
  , highlightMorph :: Boolean           -- ^ Morph highlight between targets
  }

-- | Default animation configuration
defaultAnimationConfig :: AnimationConfig
defaultAnimationConfig =
  { stepTransition: TransitionFade
  , easing: EaseOutCubic
  , duration: normal
  , entrance: EnterFade
  , exit: ExitFade
  , entranceDelay: noDelay
  , exitDelay: noDelay
  , spring: defaultSpring
  , reduceMotion: true
  , highlightMorph: true
  }

-- | Fast animation configuration
fastAnimationConfig :: AnimationConfig
fastAnimationConfig = defaultAnimationConfig
  { duration = fast
  , entrance = EnterPop
  , exit = ExitFade
  , easing = EaseOutBack
  }

-- | Slow animation configuration
slowAnimationConfig :: AnimationConfig
slowAnimationConfig = defaultAnimationConfig
  { duration = slow
  , entrance = EnterSlideUp
  , exit = ExitSlideDown
  , easing = EaseInOutCubic
  }

-- | No animation configuration
noAnimationConfig :: AnimationConfig
noAnimationConfig = defaultAnimationConfig
  { stepTransition = TransitionNone
  , duration = instant
  , entrance = EnterNone
  , exit = ExitNone
  , highlightMorph = false
  }
