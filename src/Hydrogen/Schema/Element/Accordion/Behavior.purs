-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // element // accordion // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AccordionBehavior — Compositor model for accordion interaction.
-- |
-- | ## Design Philosophy
-- |
-- | An Accordion is NOT a stateful component. It's a **COMPOSITION** where:
-- | - User gestures are **triggers** that start/stop layer animations
-- | - State transitions are **orchestrated** timelines
-- | - Motion is driven by **springs** or **easing curves**
-- | - Effects (haptic, audio) fire at specific points in the timeline
-- |
-- | ## Compositor Model
-- |
-- | ```
-- | GESTURE (click/tap/key) 
-- |    ↓
-- | TRIGGER (expand/collapse)
-- |    ↓
-- | ORCHESTRATION (parallel animations)
-- |    ├─→ Content layer: height 0→auto (spring physics)
-- |    ├─→ Chevron layer: rotate 0°→90° (easing curve)
-- |    └─→ Haptic: fire at t=0
-- |    ↓
-- | TIMELINE (60fps evaluation)
-- |    ↓
-- | RENDER (each frame)
-- | ```
-- |
-- | ## Pillar Atoms Used
-- |
-- | - Motion.Transition: TransitionConfig for expand/collapse
-- | - Motion.Orchestration: Parallel/Sequence/Stagger combinators
-- | - Temporal.Spring: SpringConfig for physics-based motion
-- | - Temporal.Duration: Animation timing
-- | - Haptic.Feedback: ImpactFeedback for tactile response
-- | - Haptic.Event: AudioCue for sound feedback
-- | - Gestural.Gesture: Tap, keyboard triggers

module Hydrogen.Schema.Element.Accordion.Behavior
  ( -- * Accordion Behavior Record
    AccordionBehavior
  , defaultBehavior
  
  -- * Expand/Collapse Transitions
  , ExpandTransition
  , defaultExpandTransition
  , springExpandTransition
  , CollapseTransition
  , defaultCollapseTransition
  
  -- * Chevron Animation
  , ChevronAnimation
  , defaultChevronAnimation
  
  -- * Trigger Configuration
  , TriggerConfig
  , defaultTriggerConfig
  
  -- * Feedback Configuration
  , FeedbackConfig
  , defaultFeedbackConfig
  , silentFeedback
  
  -- * Behavior Variants
  , instantBehavior
  , springyBehavior
  , smoothBehavior
  , snappyBehavior
  
  -- * Accessors
  , behExpandTransition
  , behCollapseTransition
  , behChevronAnimation
  , behTriggerConfig
  , behFeedbackConfig
  , behReducedMotion
  
  -- * Modifiers
  , setExpandTransition
  , setCollapseTransition
  , setChevronAnimation
  , setTriggerConfig
  , setFeedbackConfig
  , enableReducedMotion
  , disableReducedMotion
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Temporal pillar — durations
import Hydrogen.Schema.Temporal.Duration
  ( Duration
  , zero
  , ms
  , fast
  , normal
  ) as Duration

-- Temporal pillar — spring physics
import Hydrogen.Schema.Temporal.SpringConfig
  ( SpringConfig
  , gentle
  , wobbly
  , stiff
  , slow
  ) as Spring

-- Motion pillar — easing
import Hydrogen.Schema.Motion.Easing
  ( Easing
  , easeOut
  , easeInOut
  , easeOutCubic
  ) as Easing

-- Motion pillar — transitions
import Hydrogen.Schema.Motion.Transition
  ( TransitionConfig
  , TransitionType(Fade, Scale)
  , ScaleOrigin(ScaleFromCenter, ScaleFromEdge)
  , transitionConfig
  , noTransition
  ) as Transition

-- Geometry pillar — edges for scale origin
import Hydrogen.Schema.Geometry.Position (Edge(Top)) as Geo

-- Haptic pillar — impact feedback
import Hydrogen.Schema.Haptic.Feedback
  ( ImpactFeedback
      ( ImpactLight
      , ImpactMedium
      )
  ) as Haptic

-- Haptic pillar — audio cues
import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  , clickCue
  ) as Haptic

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // expand transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | How content expands when accordion opens.
-- |
-- | ## Animation Strategy
-- |
-- | - **height**: 0 → measured height (primary animation)
-- | - **opacity**: Optional fade-in
-- | - **scale**: Optional scale from top edge
-- |
-- | Uses either spring physics (natural) or bezier easing (predictable).
type ExpandTransition =
  { -- Spring-based (if present, overrides easing)
    spring :: Maybe Spring.SpringConfig
  
  -- Easing-based (fallback if no spring)
  , duration :: Duration.Duration
  , easing :: Easing.Easing
  
  -- Opacity animation (optional)
  , fadeIn :: Boolean
  , fadeDelay :: Duration.Duration
  
  -- Scale animation (optional, from top)
  , scaleFrom :: Maybe Number  -- 0.95 = start at 95% height
  }

-- | Default expand: 250ms ease-out, no fade, no scale.
defaultExpandTransition :: ExpandTransition
defaultExpandTransition =
  { spring: Nothing
  , duration: Duration.ms 250.0
  , easing: Easing.easeOut
  , fadeIn: false
  , fadeDelay: Duration.zero
  , scaleFrom: Nothing
  }

-- | Spring-based expand: gentle physics.
springExpandTransition :: ExpandTransition
springExpandTransition =
  { spring: Just Spring.gentle
  , duration: Duration.ms 250.0  -- Fallback if spring disabled
  , easing: Easing.easeOut
  , fadeIn: false
  , fadeDelay: Duration.zero
  , scaleFrom: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // collapse transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | How content collapses when accordion closes.
-- |
-- | Typically faster than expand (users expect quick response on close).
type CollapseTransition =
  { -- Spring-based (if present, overrides easing)
    spring :: Maybe Spring.SpringConfig
  
  -- Easing-based
  , duration :: Duration.Duration
  , easing :: Easing.Easing
  
  -- Opacity animation
  , fadeOut :: Boolean
  , fadeDelay :: Duration.Duration
  }

-- | Default collapse: 200ms ease-out (faster than expand).
defaultCollapseTransition :: CollapseTransition
defaultCollapseTransition =
  { spring: Nothing
  , duration: Duration.ms 200.0
  , easing: Easing.easeOut
  , fadeOut: false
  , fadeDelay: Duration.zero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // chevron animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chevron rotation animation configuration.
-- |
-- | The chevron rotates to indicate expanded state:
-- | - Collapsed: → (pointing right) or ▶ at 0°
-- | - Expanded: ↓ (pointing down) or ▼ at 90°
type ChevronAnimation =
  { duration :: Duration.Duration
  , easing :: Easing.Easing
  , collapsedRotation :: Number  -- Degrees
  , expandedRotation :: Number   -- Degrees
  }

-- | Default chevron: 200ms cubic ease-out, 0° → 90°.
defaultChevronAnimation :: ChevronAnimation
defaultChevronAnimation =
  { duration: Duration.ms 200.0
  , easing: Easing.easeOutCubic
  , collapsedRotation: 0.0
  , expandedRotation: 90.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // trigger configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | What triggers expand/collapse.
-- |
-- | ## Trigger Sources
-- |
-- | - Click/tap on trigger area
-- | - Enter/Space key when focused
-- | - Programmatic toggle
-- |
-- | ## Trigger Behavior
-- |
-- | - allowMultiple: Whether clicking another item collapses current
-- | - closeOnOutsideClick: Whether clicking outside collapses all
type TriggerConfig =
  { -- Gesture triggers
    triggerOnClick :: Boolean
  , triggerOnEnter :: Boolean
  , triggerOnSpace :: Boolean
  
  -- Behavior
  , allowMultiple :: Boolean      -- Multiple items can be open
  , closeOnOutsideClick :: Boolean
  , closeOnEscape :: Boolean
  
  -- Debounce (prevent rapid toggling)
  , debounceMs :: Number
  }

-- | Default triggers: click, Enter, Space; single expansion.
defaultTriggerConfig :: TriggerConfig
defaultTriggerConfig =
  { triggerOnClick: true
  , triggerOnEnter: true
  , triggerOnSpace: true
  , allowMultiple: false
  , closeOnOutsideClick: false
  , closeOnEscape: true
  , debounceMs: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // feedback configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Haptic and audio feedback for accordion actions.
-- |
-- | Feedback fires at specific points in the timeline:
-- | - t=0: On trigger (immediate feedback)
-- | - t=end: On animation complete (optional)
type FeedbackConfig =
  { -- Haptic feedback
    hapticOnExpand :: Maybe Haptic.ImpactFeedback
  , hapticOnCollapse :: Maybe Haptic.ImpactFeedback
  
  -- Audio feedback
  , audioOnExpand :: Maybe Haptic.AudioCue
  , audioOnCollapse :: Maybe Haptic.AudioCue
  }

-- | Default feedback: light haptic on both expand and collapse.
defaultFeedbackConfig :: FeedbackConfig
defaultFeedbackConfig =
  { hapticOnExpand: Just Haptic.ImpactLight
  , hapticOnCollapse: Just Haptic.ImpactLight
  , audioOnExpand: Nothing
  , audioOnCollapse: Nothing
  }

-- | Silent feedback: no haptic or audio.
silentFeedback :: FeedbackConfig
silentFeedback =
  { hapticOnExpand: Nothing
  , hapticOnCollapse: Nothing
  , audioOnExpand: Nothing
  , audioOnCollapse: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete accordion behavior — compositor configuration.
-- |
-- | This defines HOW the accordion animates and responds to input.
-- | The runtime interprets this as a timeline of effects.
type AccordionBehavior =
  { -- Expand/collapse animations
    expandTransition :: ExpandTransition
  , collapseTransition :: CollapseTransition
  
  -- Chevron indicator animation
  , chevronAnimation :: ChevronAnimation
  
  -- Trigger configuration
  , triggerConfig :: TriggerConfig
  
  -- Feedback (haptic, audio)
  , feedbackConfig :: FeedbackConfig
  
  -- Accessibility
  , reducedMotion :: Boolean  -- Respect prefers-reduced-motion
  }

-- | Default behavior: smooth animations, standard triggers, light haptic.
defaultBehavior :: AccordionBehavior
defaultBehavior =
  { expandTransition: defaultExpandTransition
  , collapseTransition: defaultCollapseTransition
  , chevronAnimation: defaultChevronAnimation
  , triggerConfig: defaultTriggerConfig
  , feedbackConfig: defaultFeedbackConfig
  , reducedMotion: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // behavior variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Instant behavior: no animations (for reduced motion preference).
instantBehavior :: AccordionBehavior
instantBehavior = defaultBehavior
  { expandTransition = defaultExpandTransition { duration = Duration.zero }
  , collapseTransition = defaultCollapseTransition { duration = Duration.zero }
  , chevronAnimation = defaultChevronAnimation { duration = Duration.zero }
  , reducedMotion = true
  }

-- | Springy behavior: physics-based, playful.
springyBehavior :: AccordionBehavior
springyBehavior = defaultBehavior
  { expandTransition = springExpandTransition { spring = Just Spring.wobbly }
  , collapseTransition = defaultCollapseTransition { spring = Just Spring.stiff }
  , feedbackConfig = defaultFeedbackConfig { hapticOnExpand = Just Haptic.ImpactMedium }
  }

-- | Smooth behavior: longer animations, gentle feel.
smoothBehavior :: AccordionBehavior
smoothBehavior = defaultBehavior
  { expandTransition = defaultExpandTransition 
      { duration = Duration.ms 350.0
      , easing = Easing.easeInOut
      , fadeIn = true
      }
  , collapseTransition = defaultCollapseTransition
      { duration = Duration.ms 300.0
      , easing = Easing.easeInOut
      , fadeOut = true
      }
  }

-- | Snappy behavior: quick, responsive.
snappyBehavior :: AccordionBehavior
snappyBehavior = defaultBehavior
  { expandTransition = defaultExpandTransition { duration = Duration.ms 150.0 }
  , collapseTransition = defaultCollapseTransition { duration = Duration.ms 100.0 }
  , chevronAnimation = defaultChevronAnimation { duration = Duration.ms 100.0 }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

behExpandTransition :: AccordionBehavior -> ExpandTransition
behExpandTransition b = b.expandTransition

behCollapseTransition :: AccordionBehavior -> CollapseTransition
behCollapseTransition b = b.collapseTransition

behChevronAnimation :: AccordionBehavior -> ChevronAnimation
behChevronAnimation b = b.chevronAnimation

behTriggerConfig :: AccordionBehavior -> TriggerConfig
behTriggerConfig b = b.triggerConfig

behFeedbackConfig :: AccordionBehavior -> FeedbackConfig
behFeedbackConfig b = b.feedbackConfig

behReducedMotion :: AccordionBehavior -> Boolean
behReducedMotion b = b.reducedMotion

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setExpandTransition :: ExpandTransition -> AccordionBehavior -> AccordionBehavior
setExpandTransition t b = b { expandTransition = t }

setCollapseTransition :: CollapseTransition -> AccordionBehavior -> AccordionBehavior
setCollapseTransition t b = b { collapseTransition = t }

setChevronAnimation :: ChevronAnimation -> AccordionBehavior -> AccordionBehavior
setChevronAnimation a b = b { chevronAnimation = a }

setTriggerConfig :: TriggerConfig -> AccordionBehavior -> AccordionBehavior
setTriggerConfig t b = b { triggerConfig = t }

setFeedbackConfig :: FeedbackConfig -> AccordionBehavior -> AccordionBehavior
setFeedbackConfig f b = b { feedbackConfig = f }

enableReducedMotion :: AccordionBehavior -> AccordionBehavior
enableReducedMotion b = b { reducedMotion = true }

disableReducedMotion :: AccordionBehavior -> AccordionBehavior
disableReducedMotion b = b { reducedMotion = false }

