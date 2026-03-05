-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // element // badge // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BadgeBehavior — Pure composition of verified pillar atoms for interaction.
-- |
-- | ## Design Philosophy
-- |
-- | Badge behavior defines HOW the badge responds to events and triggers.
-- | Unlike buttons (press/release), badges have attention/notification semantics:
-- | - Pulse animation on count change
-- | - Glow intensification for urgency
-- | - Dismiss gesture (swipe, tap)
-- | - Haptic feedback on appear/dismiss
-- | - Audio cues for notifications
-- |
-- | All behavior is composed from existing verified pillar atoms.
-- |
-- | ## Pillar Atoms Used
-- |
-- | - Haptic.Feedback — Impact, notification, selection feedback
-- | - Haptic.Event — AudioCue for notification sounds
-- | - Gestural.Gesture — Tap, swipe, long press for dismiss
-- | - Motion.KeyframeAnimation — Pulse, bounce, shake, heartBeat, etc.
-- | - Temporal.Duration — Animation timing and delays
-- |
-- | ## Attention Animations Available
-- |
-- | From Motion.KeyframeAnimation.Presets.Attention:
-- | - pulse: Subtle scale breathing (default for notifications)
-- | - bounce: Vertical bounce (playful attention)
-- | - shake: Horizontal shake (error/warning)
-- | - heartBeat: Two-phase pulse (urgent/critical)
-- | - flash: Opacity flash (new item)
-- | - rubberBand: Elastic stretch
-- | - swing: Pendulum rotation
-- | - tada: Scale + rotation (celebration)
-- | - wobble: Tilt wobble
-- | - jello: Skew distortion

module Hydrogen.Schema.Element.Badge.Behavior
  ( -- * Badge Behavior Record
    BadgeBehavior
  , defaultBehavior
  
  -- * Behavior Variants (with actual animations)
  , silentBehavior
  , attentionBehavior
  , dismissableBehavior
  , notificationBehavior
  , urgentBehavior
  , celebrationBehavior
  , errorBehavior
  
  -- * Accessors
  , behHapticOnAppear
  , behHapticOnDismiss
  , behHapticOnCountChange
  , behAudioOnAppear
  , behAudioOnDismiss
  , behDismissGesture
  , behAttentionAnimation
  , behPulseOnCountChange
  , behAttentionDelay
  
  -- * Modifiers
  , setHapticOnAppear
  , setHapticOnDismiss
  , setHapticOnCountChange
  , setAudioOnAppear
  , setAudioOnDismiss
  , setDismissGesture
  , setAttentionAnimation
  , setAttentionDelay
  , enablePulse
  , disablePulse
  , clearHapticOnAppear
  , clearHapticOnDismiss
  , clearAudioOnAppear
  , clearAttentionAnimation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Haptic pillar — impact feedback types
import Hydrogen.Schema.Haptic.Feedback
  ( ImpactFeedback
      ( ImpactLight
      , ImpactMedium
      , ImpactHeavy
      , ImpactRigid
      , ImpactSoft
      )
  , NotificationFeedback
      ( NotifySuccess
      , NotifyWarning
      , NotifyError
      )
  , SelectionFeedback
      ( SelectionChanged
      )
  ) as Haptic

-- Haptic pillar — audio cues
import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  , clickCue
  , confirmCue
  , warnCue
  , errorCue
  , successCue
  ) as Haptic

-- Gestural pillar — gesture state tracking
import Hydrogen.Schema.Gestural.Gesture
  ( GestureState
  , initialGestureState
  ) as Gesture

-- Motion pillar — keyframe animation type and presets
import Hydrogen.Schema.Motion.KeyframeAnimation
  ( KeyframeAnimation
  -- Attention presets (the actual animations!)
  , pulse
  , bounce
  , shake
  , heartBeat
  , flash
  , rubberBand
  , swing
  , tada
  , wobble
  , jello
  ) as Anim

-- Temporal pillar — duration for delays
import Hydrogen.Schema.Temporal.Duration
  ( Duration
  , zero
  , ms
  , fast
  , normal
  ) as Duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // badge behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete badge behavior — composition of pillar atoms.
-- |
-- | Every field references verified atoms from Schema pillars.
-- | This is the FULL vocabulary for badge interaction.
type BadgeBehavior =
  { -- Haptic feedback (Haptic.Feedback)
    hapticOnAppear :: Maybe Haptic.ImpactFeedback
  , hapticOnDismiss :: Maybe Haptic.ImpactFeedback
  , hapticOnCountChange :: Maybe Haptic.ImpactFeedback
    
  -- Audio feedback (Haptic.Event)
  , audioOnAppear :: Maybe Haptic.AudioCue
  , audioOnDismiss :: Maybe Haptic.AudioCue
    
  -- Dismiss gesture (Gestural.Gesture)
  -- When set, badge can be dismissed via this gesture
  , dismissGesture :: Maybe Gesture.GestureState
    
  -- Attention animation (Motion.KeyframeAnimation)
  -- The actual animation to play (pulse, shake, heartBeat, etc.)
  , attentionAnimation :: Maybe Anim.KeyframeAnimation
    
  -- Timing configuration
  , pulseOnCountChange :: Boolean  -- Auto-trigger animation on count change
  , attentionDelay :: Duration.Duration  -- Delay before attention animation starts
  }

-- | Default badge behavior.
-- |
-- | Light haptic on appear, no animation. Safe baseline.
defaultBehavior :: BadgeBehavior
defaultBehavior =
  { hapticOnAppear: Just Haptic.ImpactLight
  , hapticOnDismiss: Nothing
  , hapticOnCountChange: Nothing
  , audioOnAppear: Nothing
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Nothing
  , pulseOnCountChange: false
  , attentionDelay: Duration.zero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // behavior variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Silent behavior — no haptics, no audio, no animation.
-- |
-- | For badges that should not draw attention (status dots, labels).
silentBehavior :: BadgeBehavior
silentBehavior =
  { hapticOnAppear: Nothing
  , hapticOnDismiss: Nothing
  , hapticOnCountChange: Nothing
  , audioOnAppear: Nothing
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Nothing
  , pulseOnCountChange: false
  , attentionDelay: Duration.zero
  }

-- | Attention behavior — PULSE animation, medium haptic.
-- |
-- | Uses the actual `pulse` animation from Motion.KeyframeAnimation.Presets.Attention.
-- | Subtle scale breathing that draws attention without being aggressive.
attentionBehavior :: BadgeBehavior
attentionBehavior =
  { hapticOnAppear: Just Haptic.ImpactMedium
  , hapticOnDismiss: Nothing
  , hapticOnCountChange: Just Haptic.ImpactLight
  , audioOnAppear: Nothing
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Just Anim.pulse  -- THE ACTUAL PULSE ANIMATION
  , pulseOnCountChange: true
  , attentionDelay: Duration.zero
  }

-- | Dismissable behavior — can be swiped/tapped away.
-- |
-- | Provides haptic feedback on dismiss, initial gesture state ready.
dismissableBehavior :: BadgeBehavior
dismissableBehavior =
  { hapticOnAppear: Just Haptic.ImpactLight
  , hapticOnDismiss: Just Haptic.ImpactLight
  , hapticOnCountChange: Nothing
  , audioOnAppear: Nothing
  , audioOnDismiss: Just Haptic.clickCue
  , dismissGesture: Just Gesture.initialGestureState  -- Ready for gesture recognition
  , attentionAnimation: Nothing
  , pulseOnCountChange: false
  , attentionDelay: Duration.zero
  }

-- | Notification behavior — sound + haptic + PULSE for new notifications.
-- |
-- | Full notification experience: audio cue, haptic feedback, and pulse animation.
notificationBehavior :: BadgeBehavior
notificationBehavior =
  { hapticOnAppear: Just Haptic.ImpactMedium
  , hapticOnDismiss: Just Haptic.ImpactLight
  , hapticOnCountChange: Just Haptic.ImpactLight
  , audioOnAppear: Just Haptic.confirmCue
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Just Anim.pulse
  , pulseOnCountChange: true
  , attentionDelay: Duration.zero
  }

-- | Urgent behavior — HEARTBEAT animation for critical notifications.
-- |
-- | Uses the `heartBeat` animation — two-phase pulse that demands attention.
-- | Strong haptic, alert sound, continuous animation.
urgentBehavior :: BadgeBehavior
urgentBehavior =
  { hapticOnAppear: Just Haptic.ImpactHeavy
  , hapticOnDismiss: Just Haptic.ImpactMedium
  , hapticOnCountChange: Just Haptic.ImpactMedium
  , audioOnAppear: Just Haptic.warnCue
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Just Anim.heartBeat  -- HEARTBEAT for urgency
  , pulseOnCountChange: true
  , attentionDelay: Duration.zero
  }

-- | Celebration behavior — TADA animation for achievements.
-- |
-- | Uses the `tada` animation — scale + rotation for celebration.
-- | Success sound, satisfying haptic.
celebrationBehavior :: BadgeBehavior
celebrationBehavior =
  { hapticOnAppear: Just Haptic.ImpactMedium
  , hapticOnDismiss: Nothing
  , hapticOnCountChange: Nothing
  , audioOnAppear: Just Haptic.successCue
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Just Anim.tada  -- TADA for celebration
  , pulseOnCountChange: false
  , attentionDelay: Duration.fast  -- Small delay for buildup
  }

-- | Error behavior — SHAKE animation for errors/warnings.
-- |
-- | Uses the `shake` animation — horizontal shake that signals something wrong.
-- | Error sound, rigid haptic.
errorBehavior :: BadgeBehavior
errorBehavior =
  { hapticOnAppear: Just Haptic.ImpactRigid
  , hapticOnDismiss: Nothing
  , hapticOnCountChange: Just Haptic.ImpactRigid
  , audioOnAppear: Just Haptic.errorCue
  , audioOnDismiss: Nothing
  , dismissGesture: Nothing
  , attentionAnimation: Just Anim.shake  -- SHAKE for error
  , pulseOnCountChange: true
  , attentionDelay: Duration.zero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

behHapticOnAppear :: BadgeBehavior -> Maybe Haptic.ImpactFeedback
behHapticOnAppear b = b.hapticOnAppear

behHapticOnDismiss :: BadgeBehavior -> Maybe Haptic.ImpactFeedback
behHapticOnDismiss b = b.hapticOnDismiss

behHapticOnCountChange :: BadgeBehavior -> Maybe Haptic.ImpactFeedback
behHapticOnCountChange b = b.hapticOnCountChange

behAudioOnAppear :: BadgeBehavior -> Maybe Haptic.AudioCue
behAudioOnAppear b = b.audioOnAppear

behAudioOnDismiss :: BadgeBehavior -> Maybe Haptic.AudioCue
behAudioOnDismiss b = b.audioOnDismiss

behDismissGesture :: BadgeBehavior -> Maybe Gesture.GestureState
behDismissGesture b = b.dismissGesture

behAttentionAnimation :: BadgeBehavior -> Maybe Anim.KeyframeAnimation
behAttentionAnimation b = b.attentionAnimation

behPulseOnCountChange :: BadgeBehavior -> Boolean
behPulseOnCountChange b = b.pulseOnCountChange

behAttentionDelay :: BadgeBehavior -> Duration.Duration
behAttentionDelay b = b.attentionDelay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set haptic feedback for badge appear.
setHapticOnAppear :: Haptic.ImpactFeedback -> BadgeBehavior -> BadgeBehavior
setHapticOnAppear h b = b { hapticOnAppear = Just h }

-- | Set haptic feedback for badge dismiss.
setHapticOnDismiss :: Haptic.ImpactFeedback -> BadgeBehavior -> BadgeBehavior
setHapticOnDismiss h b = b { hapticOnDismiss = Just h }

-- | Set haptic feedback for count change.
setHapticOnCountChange :: Haptic.ImpactFeedback -> BadgeBehavior -> BadgeBehavior
setHapticOnCountChange h b = b { hapticOnCountChange = Just h }

-- | Set audio cue for badge appear.
setAudioOnAppear :: Haptic.AudioCue -> BadgeBehavior -> BadgeBehavior
setAudioOnAppear a b = b { audioOnAppear = Just a }

-- | Set audio cue for badge dismiss.
setAudioOnDismiss :: Haptic.AudioCue -> BadgeBehavior -> BadgeBehavior
setAudioOnDismiss a b = b { audioOnDismiss = Just a }

-- | Set dismiss gesture state.
setDismissGesture :: Gesture.GestureState -> BadgeBehavior -> BadgeBehavior
setDismissGesture g b = b { dismissGesture = Just g }

-- | Set attention animation.
-- |
-- | Use animations from Motion.KeyframeAnimation:
-- | - Anim.pulse — subtle breathing
-- | - Anim.bounce — playful bounce
-- | - Anim.shake — error shake
-- | - Anim.heartBeat — urgent pulse
-- | - Anim.tada — celebration
-- | - Anim.flash — quick flash
-- | - Anim.wobble — tilt wobble
-- | - Anim.jello — elastic jello
-- | - Anim.rubberBand — stretch
-- | - Anim.swing — pendulum
setAttentionAnimation :: Anim.KeyframeAnimation -> BadgeBehavior -> BadgeBehavior
setAttentionAnimation a b = b { attentionAnimation = Just a }

-- | Set delay before attention animation starts.
setAttentionDelay :: Duration.Duration -> BadgeBehavior -> BadgeBehavior
setAttentionDelay d b = b { attentionDelay = d }

-- | Enable automatic pulse on count change.
enablePulse :: BadgeBehavior -> BadgeBehavior
enablePulse b = b { pulseOnCountChange = true }

-- | Disable automatic pulse on count change.
disablePulse :: BadgeBehavior -> BadgeBehavior
disablePulse b = b { pulseOnCountChange = false }

-- | Clear haptic on appear (set to Nothing).
clearHapticOnAppear :: BadgeBehavior -> BadgeBehavior
clearHapticOnAppear b = b { hapticOnAppear = Nothing }

-- | Clear haptic on dismiss (set to Nothing).
clearHapticOnDismiss :: BadgeBehavior -> BadgeBehavior
clearHapticOnDismiss b = b { hapticOnDismiss = Nothing }

-- | Clear audio on appear (set to Nothing).
clearAudioOnAppear :: BadgeBehavior -> BadgeBehavior
clearAudioOnAppear b = b { audioOnAppear = Nothing }

-- | Clear attention animation (set to Nothing).
clearAttentionAnimation :: BadgeBehavior -> BadgeBehavior
clearAttentionAnimation b = b { attentionAnimation = Nothing }
