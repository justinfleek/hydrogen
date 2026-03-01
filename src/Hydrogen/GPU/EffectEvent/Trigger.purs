-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // effect-event //
--                                                                      trigger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger Types — Conditions that start/stop effects
-- |
-- | Triggers are pure predicates evaluated against FrameState.
-- | No side effects. No callbacks. Just data.
-- |
-- | ## Trigger Categories
-- |
-- | - **Mouse**: hover, enter, leave, down, up, dragging, idle, region
-- | - **Keyboard**: key down, up, held, modifier active
-- | - **Focus**: gained, lost, within, visible
-- | - **Time**: delay, timestamp, interval, frame count, elapsed range
-- | - **Scroll**: position, progress, direction, velocity
-- | - **Viewport**: width, height, visible, orientation
-- | - **Animation**: progress range, complete, phase, spring at rest
-- |
-- | ## Composition
-- |
-- | Triggers compose with boolean algebra via TriggerCombinator:
-- | - `TriggerAnd`: Both must be true
-- | - `TriggerOr`: Either must be true
-- | - `TriggerNot`: Negation
-- | - `TriggerXor`: Exactly one true

module Hydrogen.GPU.EffectEvent.Trigger
  ( -- * Core Types
    EffectTrigger(..)
  , TriggerCondition(..)
  , TriggerCombinator(..)
  
  -- * Mouse Triggers
  , MouseTrigger(..)
  
  -- * Keyboard Triggers
  , KeyboardTrigger(..)
  , Modifier(..)
  
  -- * Focus Triggers
  , FocusTrigger(..)
  
  -- * Time Triggers
  , TimeTrigger(..)
  
  -- * Scroll Triggers
  , ScrollTrigger(..)
  , ScrollDir(..)
  
  -- * Viewport Triggers
  , ViewportTrigger(..)
  , Orientation(..)
  
  -- * Animation Triggers
  , AnimationTrigger(..)
  , AnimPhase(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect trigger — condition that starts/stops effects
-- |
-- | Triggers are pure predicates evaluated against FrameState.
-- | No side effects. No callbacks. Just data.
data EffectTrigger
  = TriggerMouse MouseTrigger
  | TriggerKeyboard KeyboardTrigger
  | TriggerFocus FocusTrigger
  | TriggerTime TimeTrigger
  | TriggerScroll ScrollTrigger
  | TriggerViewport ViewportTrigger
  | TriggerAnimation AnimationTrigger
  | TriggerCombined TriggerCombinator
  | TriggerAlways                      -- Always active
  | TriggerNever                       -- Never active

derive instance eqEffectTrigger :: Eq EffectTrigger

instance showEffectTrigger :: Show EffectTrigger where
  show (TriggerMouse m) = "(TriggerMouse " <> show m <> ")"
  show (TriggerKeyboard k) = "(TriggerKeyboard " <> show k <> ")"
  show (TriggerTime t) = "(TriggerTime " <> show t <> ")"
  show (TriggerScroll s) = "(TriggerScroll " <> show s <> ")"
  show (TriggerViewport v) = "(TriggerViewport " <> show v <> ")"
  show (TriggerAnimation a) = "(TriggerAnimation " <> show a <> ")"
  show (TriggerFocus f) = "(TriggerFocus " <> show f <> ")"
  show (TriggerCombined c) = "(TriggerCombined " <> show c <> ")"
  show TriggerAlways = "TriggerAlways"
  show TriggerNever = "TriggerNever"

-- | Trigger condition result
data TriggerCondition
  = ConditionMet        -- Trigger condition is true
  | ConditionNotMet     -- Trigger condition is false
  | ConditionUnknown    -- Cannot evaluate (missing state)

derive instance eqTriggerCondition :: Eq TriggerCondition

-- | Combinator for composing triggers
data TriggerCombinator
  = TriggerAnd EffectTrigger EffectTrigger   -- Both must be true
  | TriggerOr EffectTrigger EffectTrigger    -- Either must be true
  | TriggerNot EffectTrigger                 -- Negation
  | TriggerXor EffectTrigger EffectTrigger   -- Exactly one true

derive instance eqTriggerCombinator :: Eq TriggerCombinator

instance showTriggerCombinator :: Show TriggerCombinator where
  show (TriggerAnd a b) = "(TriggerAnd " <> show a <> " " <> show b <> ")"
  show (TriggerOr a b) = "(TriggerOr " <> show a <> " " <> show b <> ")"
  show (TriggerNot t) = "(TriggerNot " <> show t <> ")"
  show (TriggerXor a b) = "(TriggerXor " <> show a <> " " <> show b <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // mouse triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mouse-based triggers
data MouseTrigger
  = MouseHover Int               -- Hovering over element (PickId)
  | MouseNotHover Int            -- Not hovering over element
  | MouseEnter Int               -- Just started hovering
  | MouseLeave Int               -- Just stopped hovering
  | MouseDown Int                -- Button pressed on element
  | MouseUp Int                  -- Button released on element
  | MouseDragging                -- Currently dragging
  | MouseIdle Number             -- No movement for N ms
  | MouseInRegion                -- Mouse in defined region
      { x :: Number, y :: Number, width :: Number, height :: Number }

derive instance eqMouseTrigger :: Eq MouseTrigger

instance showMouseTrigger :: Show MouseTrigger where
  show (MouseHover id) = "(MouseHover " <> show id <> ")"
  show (MouseNotHover id) = "(MouseNotHover " <> show id <> ")"
  show (MouseEnter id) = "(MouseEnter " <> show id <> ")"
  show (MouseLeave id) = "(MouseLeave " <> show id <> ")"
  show (MouseDown id) = "(MouseDown " <> show id <> ")"
  show (MouseUp id) = "(MouseUp " <> show id <> ")"
  show MouseDragging = "MouseDragging"
  show (MouseIdle ms) = "(MouseIdle " <> show ms <> ")"
  show (MouseInRegion _) = "(MouseInRegion ...)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // keyboard triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard-based triggers
data KeyboardTrigger
  = KeyDown String               -- Key pressed (key code)
  | KeyUp String                 -- Key released
  | KeyHeld String Number        -- Key held for N ms
  | ModifierActive Modifier      -- Modifier key active

derive instance eqKeyboardTrigger :: Eq KeyboardTrigger

instance showKeyboardTrigger :: Show KeyboardTrigger where
  show (KeyDown k) = "(KeyDown " <> k <> ")"
  show (KeyUp k) = "(KeyUp " <> k <> ")"
  show (KeyHeld k ms) = "(KeyHeld " <> k <> " " <> show ms <> ")"
  show (ModifierActive m) = "(ModifierActive " <> show m <> ")"

-- | Modifier keys
data Modifier
  = ModShift
  | ModCtrl
  | ModAlt
  | ModMeta

derive instance eqModifier :: Eq Modifier

instance showModifier :: Show Modifier where
  show ModShift = "Shift"
  show ModCtrl = "Ctrl"
  show ModAlt = "Alt"
  show ModMeta = "Meta"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focus triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus-based triggers
-- |
-- | Focus triggers handle keyboard navigation and accessibility focus states.
-- | These work with the focus management system to track which element has
-- | keyboard focus, enabling proper keyboard-driven UI interactions.
data FocusTrigger
  = FocusGained Int              -- Element gained focus (PickId)
  | FocusLost Int                -- Element lost focus (PickId)
  | FocusWithin Int              -- Element or descendant has focus (PickId)
  | FocusVisible Int             -- Focus visible (keyboard navigation, not mouse)

derive instance eqFocusTrigger :: Eq FocusTrigger

instance showFocusTrigger :: Show FocusTrigger where
  show (FocusGained id) = "(FocusGained " <> show id <> ")"
  show (FocusLost id) = "(FocusLost " <> show id <> ")"
  show (FocusWithin id) = "(FocusWithin " <> show id <> ")"
  show (FocusVisible id) = "(FocusVisible " <> show id <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // time triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time-based triggers
data TimeTrigger
  = AfterDelay Number            -- After N ms since trigger registration
  | AtTime Number                -- At specific timestamp
  | Interval Number              -- Every N ms
  | FrameCount Int               -- After N frames
  | Elapsed Number Number        -- Between start and end time

derive instance eqTimeTrigger :: Eq TimeTrigger

instance showTimeTrigger :: Show TimeTrigger where
  show (AfterDelay ms) = "(AfterDelay " <> show ms <> ")"
  show (AtTime t) = "(AtTime " <> show t <> ")"
  show (Interval ms) = "(Interval " <> show ms <> ")"
  show (FrameCount n) = "(FrameCount " <> show n <> ")"
  show (Elapsed start end) = "(Elapsed " <> show start <> " " <> show end <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll-based triggers
data ScrollTrigger
  = ScrollPosition Number        -- Scroll position threshold (px)
  | ScrollProgress Number        -- Scroll progress (0.0-1.0)
  | ScrollDirection ScrollDir    -- Scrolling in direction
  | ScrollVelocity Number        -- Scroll velocity threshold

derive instance eqScrollTrigger :: Eq ScrollTrigger

instance showScrollTrigger :: Show ScrollTrigger where
  show (ScrollPosition px) = "(ScrollPosition " <> show px <> ")"
  show (ScrollProgress p) = "(ScrollProgress " <> show p <> ")"
  show (ScrollDirection d) = "(ScrollDirection " <> show d <> ")"
  show (ScrollVelocity v) = "(ScrollVelocity " <> show v <> ")"

-- | Scroll direction
data ScrollDir = ScrollUp | ScrollDown | ScrollLeft | ScrollRight

derive instance eqScrollDir :: Eq ScrollDir

instance showScrollDir :: Show ScrollDir where
  show ScrollUp = "ScrollUp"
  show ScrollDown = "ScrollDown"
  show ScrollLeft = "ScrollLeft"
  show ScrollRight = "ScrollRight"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport-based triggers
data ViewportTrigger
  = ViewportWidth Number Number    -- Min, max width
  | ViewportHeight Number Number   -- Min, max height
  | ViewportVisible Int            -- Element visible (PickId)
  | ViewportOrientation Orientation

derive instance eqViewportTrigger :: Eq ViewportTrigger

instance showViewportTrigger :: Show ViewportTrigger where
  show (ViewportWidth min' max') = "(ViewportWidth " <> show min' <> " " <> show max' <> ")"
  show (ViewportHeight min' max') = "(ViewportHeight " <> show min' <> " " <> show max' <> ")"
  show (ViewportVisible id) = "(ViewportVisible " <> show id <> ")"
  show (ViewportOrientation o) = "(ViewportOrientation " <> show o <> ")"

-- | Device orientation
data Orientation = Portrait | Landscape

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Portrait = "Portrait"
  show Landscape = "Landscape"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation-based triggers
data AnimationTrigger
  = AnimationProgress Number Number  -- Progress between min and max
  | AnimationComplete Int            -- Animation handle completed
  | AnimationPhaseIs AnimPhase       -- Current phase matches
  | SpringAtRest Int                 -- Spring handle at rest

derive instance eqAnimationTrigger :: Eq AnimationTrigger

instance showAnimationTrigger :: Show AnimationTrigger where
  show (AnimationProgress min' max') = "(AnimationProgress " <> show min' <> " " <> show max' <> ")"
  show (AnimationComplete h) = "(AnimationComplete " <> show h <> ")"
  show (AnimationPhaseIs p) = "(AnimationPhaseIs " <> show p <> ")"
  show (SpringAtRest h) = "(SpringAtRest " <> show h <> ")"

-- | Animation phase
data AnimPhase = PhaseIdle | PhaseRunning | PhaseComplete | PhasePaused

derive instance eqAnimPhase :: Eq AnimPhase

instance showAnimPhase :: Show AnimPhase where
  show PhaseIdle = "PhaseIdle"
  show PhaseRunning = "PhaseRunning"
  show PhaseComplete = "PhaseComplete"
  show PhasePaused = "PhasePaused"
