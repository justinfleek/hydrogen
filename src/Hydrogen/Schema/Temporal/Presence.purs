-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // presence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Presence — Enter/exit animation state machine for component lifecycle.
-- |
-- | ## State Machine
-- |
-- | Components with presence animations transition through four states:
-- |
-- | ```
-- | Exited → Entering → Entered → Exiting → Exited
-- |            ↑                      ↓
-- |            └──────────────────────┘
-- | ```
-- |
-- | - **Exited**: Component is not rendered (or invisible)
-- | - **Entering**: Component is animating into view
-- | - **Entered**: Component is fully visible and interactive
-- | - **Exiting**: Component is animating out of view
-- |
-- | ## Use Cases
-- |
-- | - Modal dialogs (fade in/out)
-- | - Toast notifications (slide in, auto-dismiss)
-- | - Page transitions (cross-fade)
-- | - Conditional rendering with animation
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Temporal.Duration (animation timing)
-- | - Hydrogen.Schema.Temporal.Easing (animation curves)
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Modal, Dialog, Drawer components
-- | - Toast notification system
-- | - Route transition animations
-- | - AnimatePresence compound

module Hydrogen.Schema.Temporal.Presence
  ( -- * Presence State
    PresenceState(Exited, Entering, Entered, Exiting)
  , isVisible
  , isAnimating
  , isEntering
  , isExiting
  , isStable
  
  -- * Animation Specification
  , AnimationSpec
  , animationSpec
  , specDuration
  , specEasing
  , specDelay
  
  -- * Presence Configuration
  , PresenceConfig
  , presenceConfig
  , presenceSimple
  , presenceFade
  , presenceSlide
  , presenceScale
  
  -- * State Transitions
  , enter
  , exit
  , complete
  , reset
  
  -- * Accessors
  , configInitial
  , configEnter
  , configExit
  , configMode
  
  -- * Animation Mode
  , PresenceMode(Wait, PopLayout, Sync)
  , isWaitMode
  , isPopLayoutMode
  , isSyncMode
  
  -- * Common Presets
  , presenceModal
  , presenceToast
  , presenceDrawer
  , presencePageTransition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (||)
  , (<>)
  )

import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Duration (fromMilliseconds, zero) as Duration
import Hydrogen.Schema.Temporal.Easing (Easing)
import Hydrogen.Schema.Temporal.Easing (easeOut, easeIn, easeInOut) as Easing
import Hydrogen.Schema.Temporal.Delay (Delay)
import Hydrogen.Schema.Temporal.Delay (none) as Delay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // presence // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | The four phases of presence animation.
-- |
-- | This is a finite state machine that governs component visibility
-- | and animation state during mount/unmount lifecycle.
data PresenceState
  = Exited    -- ^ Component not rendered or invisible
  | Entering  -- ^ Component animating into view
  | Entered   -- ^ Component fully visible and interactive
  | Exiting   -- ^ Component animating out of view

derive instance eqPresenceState :: Eq PresenceState
derive instance ordPresenceState :: Ord PresenceState

instance showPresenceState :: Show PresenceState where
  show Exited = "(PresenceState Exited)"
  show Entering = "(PresenceState Entering)"
  show Entered = "(PresenceState Entered)"
  show Exiting = "(PresenceState Exiting)"

-- | Is the component visible (Entering, Entered, or Exiting)?
-- |
-- | During Entering and Exiting, the component should be rendered
-- | but may have reduced opacity or transformed position.
isVisible :: PresenceState -> Boolean
isVisible Exited = false
isVisible Entering = true
isVisible Entered = true
isVisible Exiting = true

-- | Is the component currently animating?
isAnimating :: PresenceState -> Boolean
isAnimating Entering = true
isAnimating Exiting = true
isAnimating _ = false

-- | Is the component entering?
isEntering :: PresenceState -> Boolean
isEntering Entering = true
isEntering _ = false

-- | Is the component exiting?
isExiting :: PresenceState -> Boolean
isExiting Exiting = true
isExiting _ = false

-- | Is the component in a stable state (not animating)?
isStable :: PresenceState -> Boolean
isStable Exited = true
isStable Entered = true
isStable _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animation // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for a single animation (enter or exit).
-- |
-- | Contains all timing parameters needed to execute the animation.
type AnimationSpec =
  { duration :: Duration
  , easing :: Easing
  , delay :: Delay
  }

-- | Create an animation specification.
animationSpec :: Duration -> Easing -> Delay -> AnimationSpec
animationSpec d e dl = { duration: d, easing: e, delay: dl }

-- | Get animation duration.
specDuration :: AnimationSpec -> Duration
specDuration s = s.duration

-- | Get animation easing.
specEasing :: AnimationSpec -> Easing
specEasing s = s.easing

-- | Get animation delay.
specDelay :: AnimationSpec -> Delay
specDelay s = s.delay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // presence // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to handle multiple presence changes.
-- |
-- | When a component's presence changes while already animating:
-- |
-- | - **Wait**: Complete current animation before starting next
-- | - **PopLayout**: Remove exiting elements from layout flow immediately
-- | - **Sync**: Cancel current animation and start new one immediately
data PresenceMode
  = Wait       -- ^ Queue animations, wait for completion
  | PopLayout  -- ^ Remove from layout during exit, allow overlap
  | Sync       -- ^ Interrupt and synchronize to new state

derive instance eqPresenceMode :: Eq PresenceMode
derive instance ordPresenceMode :: Ord PresenceMode

instance showPresenceMode :: Show PresenceMode where
  show Wait = "(PresenceMode Wait)"
  show PopLayout = "(PresenceMode PopLayout)"
  show Sync = "(PresenceMode Sync)"

-- | Is this Wait mode?
isWaitMode :: PresenceMode -> Boolean
isWaitMode Wait = true
isWaitMode _ = false

-- | Is this PopLayout mode?
isPopLayoutMode :: PresenceMode -> Boolean
isPopLayoutMode PopLayout = true
isPopLayoutMode _ = false

-- | Is this Sync mode?
isSyncMode :: PresenceMode -> Boolean
isSyncMode Sync = true
isSyncMode _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // presence // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete configuration for presence animations.
-- |
-- | Defines the initial visibility state and animations for enter/exit.
type PresenceConfig =
  { initial :: Boolean      -- ^ Start visible (Entered) or hidden (Exited)
  , enter :: AnimationSpec  -- ^ Animation when becoming visible
  , exit :: AnimationSpec   -- ^ Animation when becoming hidden
  , mode :: PresenceMode    -- ^ How to handle overlapping animations
  }

-- | Create a presence configuration with full control.
presenceConfig :: Boolean -> AnimationSpec -> AnimationSpec -> PresenceMode -> PresenceConfig
presenceConfig init ent ext m =
  { initial: init
  , enter: ent
  , exit: ext
  , mode: m
  }

-- | Create a simple presence with same animation for enter and exit.
presenceSimple :: Duration -> Easing -> PresenceConfig
presenceSimple dur eas =
  let spec = animationSpec dur eas Delay.none
  in presenceConfig false spec spec Wait

-- | Create a fade presence (opacity animation).
-- |
-- | Uses ease-out for enter, ease-in for exit (standard UI pattern).
presenceFade :: Duration -> PresenceConfig
presenceFade dur = presenceConfig false
  (animationSpec dur Easing.easeOut Delay.none)
  (animationSpec dur Easing.easeIn Delay.none)
  Wait

-- | Create a slide presence (transform animation).
-- |
-- | Uses ease-out for enter (decelerating), ease-in for exit (accelerating).
presenceSlide :: Duration -> PresenceConfig
presenceSlide dur = presenceConfig false
  (animationSpec dur Easing.easeOut Delay.none)
  (animationSpec dur Easing.easeIn Delay.none)
  PopLayout

-- | Create a scale presence (scale transform animation).
-- |
-- | Uses ease-in-out for both directions (symmetric feel).
presenceScale :: Duration -> PresenceConfig
presenceScale dur = presenceConfig false
  (animationSpec dur Easing.easeInOut Delay.none)
  (animationSpec dur Easing.easeInOut Delay.none)
  Wait

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // state // transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trigger enter transition.
-- |
-- | - From Exited: → Entering
-- | - From Exiting: → Entering (interrupt)
-- | - From Entering, Entered: no change
enter :: PresenceState -> PresenceState
enter Exited = Entering
enter Exiting = Entering
enter s = s

-- | Trigger exit transition.
-- |
-- | - From Entered: → Exiting
-- | - From Entering: → Exiting (interrupt)
-- | - From Exiting, Exited: no change
exit :: PresenceState -> PresenceState
exit Entered = Exiting
exit Entering = Exiting
exit s = s

-- | Complete current animation.
-- |
-- | - From Entering: → Entered
-- | - From Exiting: → Exited
-- | - From stable states: no change
complete :: PresenceState -> PresenceState
complete Entering = Entered
complete Exiting = Exited
complete s = s

-- | Reset to initial hidden state.
reset :: PresenceState
reset = Exited

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get initial visibility.
configInitial :: PresenceConfig -> Boolean
configInitial cfg = cfg.initial

-- | Get enter animation spec.
configEnter :: PresenceConfig -> AnimationSpec
configEnter cfg = cfg.enter

-- | Get exit animation spec.
configExit :: PresenceConfig -> AnimationSpec
configExit cfg = cfg.exit

-- | Get presence mode.
configMode :: PresenceConfig -> PresenceMode
configMode cfg = cfg.mode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset for modal dialogs.
-- |
-- | Fade with slight scale, 200ms duration.
presenceModal :: PresenceConfig
presenceModal = presenceConfig false
  (animationSpec (Duration.fromMilliseconds 200.0) Easing.easeOut Delay.none)
  (animationSpec (Duration.fromMilliseconds 150.0) Easing.easeIn Delay.none)
  Wait

-- | Preset for toast notifications.
-- |
-- | Slide animation with PopLayout mode for stack behavior.
presenceToast :: PresenceConfig
presenceToast = presenceConfig false
  (animationSpec (Duration.fromMilliseconds 300.0) Easing.easeOut Delay.none)
  (animationSpec (Duration.fromMilliseconds 200.0) Easing.easeIn Delay.none)
  PopLayout

-- | Preset for drawer/panel components.
-- |
-- | Slide with longer duration for larger elements.
presenceDrawer :: PresenceConfig
presenceDrawer = presenceConfig false
  (animationSpec (Duration.fromMilliseconds 350.0) Easing.easeOut Delay.none)
  (animationSpec (Duration.fromMilliseconds 250.0) Easing.easeIn Delay.none)
  Wait

-- | Preset for page/route transitions.
-- |
-- | Cross-fade with Sync mode for immediate response.
presencePageTransition :: PresenceConfig
presencePageTransition = presenceConfig false
  (animationSpec (Duration.fromMilliseconds 300.0) Easing.easeInOut Delay.none)
  (animationSpec (Duration.fromMilliseconds 200.0) Easing.easeInOut Delay.none)
  Sync
