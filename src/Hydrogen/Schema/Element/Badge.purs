-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // element // badge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Badge — STACKED compound composing atoms from all pillars.
-- |
-- | A badge is a bounded indicator of status, count, or attention. This compound
-- | includes EVERY atom a badge could ever need, enabling agents to compose any
-- | variant by selection.
-- |
-- | ## Architecture (5-Layer Model)
-- |
-- | Following the After Effects compositor mental model:
-- |
-- | 1. **State** — Data state (count, urgency, seen, visibility)
-- | 2. **Geometry** — Shape, size, anchor position
-- | 3. **Appearance** — Fill, border, shadow, transform, animation, effects
-- | 4. **Behavior** — Haptic, audio, dismiss gesture
-- | 5. **Semantics** — Purpose, accessibility, identity
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Element.Badge as Badge
-- |
-- | -- Simple notification badge
-- | myBadge = Badge.notificationBadge 5 "unread messages"
-- |
-- | -- Custom badge
-- | customBadge = Badge.badge
-- |   (Badge.notificationState 3)
-- |   Badge.mediumGeometry
-- |   Badge.dangerAppearance
-- |   Badge.urgentBehavior
-- |   (Badge.notificationSemantics "critical alerts")
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Badge.State (data and visibility flags)
-- | - Badge.Geometry (spatial layout)
-- | - Badge.Appearance (visual surface)
-- | - Badge.Behavior (interaction response)
-- | - Badge.Semantics (purpose and accessibility)

module Hydrogen.Schema.Element.Badge
  ( -- * Badge Compound Type
    Badge
  , badge
  , defaultBadge
  , notificationBadge
  , statusBadge
  , dotBadge
  
  -- * Badge Accessors
  , getState
  , getGeometry
  , getAppearance
  , getBehavior
  , getSemantics
  
  -- * State Accessors (convenience - delegates to State layer)
  , isVisible
  , isSeen
  , isAnimating
  , getCount
  , getUrgency
  , shouldPulse
  
  -- * Geometry Accessors (convenience - delegates to Geometry layer)
  , getShape
  , getSize
  , getAnchor
  
  -- * Appearance Accessors (convenience - delegates to Appearance layer)
  , getFill
  , getShadow
  , getTextColor
  , getOpacity
  
  -- * Behavior Accessors (convenience - delegates to Behavior layer)
  , getHapticOnAppear
  , getAudioOnAppear
  , getPulseOnCountChange
  
  -- * Semantics Accessors (convenience - delegates to Semantics layer)
  , getPurpose
  , getLabel
  , getLiveRegion
  
  -- * Badge Modifiers
  , setState
  , setGeometry
  , setAppearance
  , setBehavior
  , setSemantics
  
  -- * State Modifiers (convenience - updates State layer)
  , setVisible
  , setCount
  , setUrgency
  , setSeen
  , dismiss
  , markSeen
  
  -- * Sub-module Re-exports
  , module Hydrogen.Schema.Element.Badge.State
  , module Hydrogen.Schema.Element.Badge.Geometry
  , module Hydrogen.Schema.Element.Badge.Appearance
  , module Hydrogen.Schema.Element.Badge.Behavior
  , module Hydrogen.Schema.Element.Badge.Semantics
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)

-- Types needed for compound-level accessor return types
import Hydrogen.Schema.Surface.Fill (Fill) as Fill
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow) as Shadow
import Hydrogen.Schema.Color.RGB (RGB) as Color
import Hydrogen.Schema.Haptic.Feedback (ImpactFeedback) as Haptic
import Hydrogen.Schema.Haptic.Event (AudioCue) as Haptic
import Hydrogen.Schema.Motion.Transform (Opacity) as Opacity

import Hydrogen.Schema.Element.Badge.State
  ( BadgeElementState
  , BadgeCount
  , Urgency(Low, Medium, High, Critical)
  -- Preset states
  , defaultState
  , hiddenState
  , visibleState
  , notificationState
  -- Count operations
  , badgeCount
  , unwrapCount
  , incrementCount
  , decrementCount
  , zeroCount
  , maxCount
  , urgencyToNumber
  -- Accessors (used to implement compound-level accessors)
  , isVisible
  , isSeen
  , isAnimating
  , getCount
  , getUrgency
  , shouldPulse
  -- Modifiers (used to implement compound-level modifiers)
  , setVisible
  , setCount
  , setUrgency
  , setSeen
  , setAnimating
  , dismiss
  , markSeen
  ) as State

import Hydrogen.Schema.Element.Badge.State
  ( BadgeElementState
  , BadgeCount
  , Urgency(Low, Medium, High, Critical)
  , defaultState
  , hiddenState
  , visibleState
  , notificationState
  , badgeCount
  , unwrapCount
  , incrementCount
  , decrementCount
  , zeroCount
  , maxCount
  , urgencyToNumber
  )

import Hydrogen.Schema.Element.Badge.Geometry
  ( BadgeGeometry
  , BadgeShape(Dot, Circle, Pill, CustomShape)
  , AnchorPosition(TopRight, TopLeft, BottomRight, BottomLeft, Custom)
  , defaultGeometry
  , mkGeometry
  , shapeToCornerRadii
  , anchorOffset
  -- Presets
  , dotGeometry
  , smallGeometry
  , mediumGeometry
  , largeGeometry
  -- Accessors
  , geoShape
  , geoSize
  , geoAnchor
  , geoPadding
  , geoOffset
  -- Modifiers
  , setShape
  , setSize
  , setAnchor
  , setPadding
  , setOffset
  )

import Hydrogen.Schema.Element.Badge.Appearance
  ( BadgeAppearance
  , defaultAppearance
  , primaryAppearance
  , secondaryAppearance
  , successAppearance
  , warningAppearance
  , dangerAppearance
  , glowingAppearance
  , outlineAppearance
  -- Accessors
  , appFill
  , appBorder
  , appShadow
  , appTransform
  , appAnimation
  , appLottie
  , appEffects
  , appTextColor
  , appOpacity
  -- Modifiers
  , setFill
  , setBorder
  , setShadow
  , setTransform
  , setAnimation
  , setLottie
  , addEffect
  , setTextColor
  , setOpacity
  )

import Hydrogen.Schema.Element.Badge.Behavior
  ( BadgeBehavior
  , defaultBehavior
  , silentBehavior
  , attentionBehavior
  , dismissableBehavior
  , notificationBehavior
  , urgentBehavior
  -- Accessors
  , behHapticOnAppear
  , behHapticOnDismiss
  , behAudioOnAppear
  , behDismissGesture
  , behAttentionAnimation
  , behPulseOnCountChange
  -- Modifiers
  , setHapticOnAppear
  , setHapticOnDismiss
  , setAudioOnAppear
  , setDismissGesture
  , setAttentionAnimation
  , enablePulse
  , disablePulse
  )

import Hydrogen.Schema.Element.Badge.Semantics
  ( BadgeSemantics
  , BadgePurpose(NotificationBadge, StatusBadge, LabelBadge, CountBadge, PriorityBadge)
  , defaultSemantics
  , notificationSemantics
  , statusSemantics
  , labelSemantics
  , countSemantics
  , prioritySemantics
  -- Accessors
  , semPurpose
  , semLabel
  , semLiveRegion
  , semRole
  -- Modifiers
  , setPurpose
  , setLabel
  , setLiveRegion
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // badge type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | STACKED Badge compound — complete badge with all pillar atoms.
-- |
-- | Composes all 5 layers:
-- | - State (data and visibility flags)
-- | - Geometry (spatial layout)
-- | - Appearance (visual surface)
-- | - Behavior (interaction response)
-- | - Semantics (purpose and accessibility)
type Badge =
  { state :: State.BadgeElementState
  , geometry :: BadgeGeometry
  , appearance :: BadgeAppearance
  , behavior :: BadgeBehavior
  , semantics :: BadgeSemantics
  }

-- | Create a badge with all properties.
badge
  :: State.BadgeElementState
  -> BadgeGeometry
  -> BadgeAppearance
  -> BadgeBehavior
  -> BadgeSemantics
  -> Badge
badge st geo app beh sem =
  { state: st
  , geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default badge with sensible defaults.
-- |
-- | Visible, no count, pill shape, blue fill, "Badge" label.
defaultBadge :: String -> Badge
defaultBadge label =
  { state: State.defaultState
  , geometry: defaultGeometry
  , appearance: defaultAppearance
  , behavior: defaultBehavior
  , semantics: defaultSemantics label
  }

-- | Notification badge with count.
-- |
-- | Suitable for unread message indicators.
notificationBadge :: Int -> String -> Badge
notificationBadge count label =
  { state: State.notificationState count
  , geometry: if count > 9 then mediumGeometry else smallGeometry
  , appearance: dangerAppearance
  , behavior: notificationBehavior
  , semantics: notificationSemantics label
  }

-- | Status badge (online/offline indicator).
-- |
-- | Small dot without count.
statusBadge :: String -> Badge
statusBadge label =
  { state: State.visibleState
  , geometry: dotGeometry
  , appearance: successAppearance
  , behavior: silentBehavior
  , semantics: statusSemantics label
  }

-- | Dot badge — minimal presence indicator.
-- |
-- | No count, just a colored dot.
dotBadge :: Badge
dotBadge =
  { state: State.visibleState
  , geometry: dotGeometry
  , appearance: primaryAppearance
  , behavior: silentBehavior
  , semantics: labelSemantics "indicator"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get badge state.
getState :: Badge -> State.BadgeElementState
getState b = b.state

-- | Get badge geometry.
getGeometry :: Badge -> BadgeGeometry
getGeometry b = b.geometry

-- | Get badge appearance.
getAppearance :: Badge -> BadgeAppearance
getAppearance b = b.appearance

-- | Get badge behavior.
getBehavior :: Badge -> BadgeBehavior
getBehavior b = b.behavior

-- | Get badge semantics.
getSemantics :: Badge -> BadgeSemantics
getSemantics b = b.semantics

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // state accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Is the badge visible?
-- |
-- | Convenience function — delegates to State layer.
isVisible :: Badge -> Boolean
isVisible b = State.isVisible b.state

-- | Has the badge been seen/acknowledged?
-- |
-- | Convenience function — delegates to State layer.
isSeen :: Badge -> Boolean
isSeen b = State.isSeen b.state

-- | Is an animation in progress?
-- |
-- | Convenience function — delegates to State layer.
isAnimating :: Badge -> Boolean
isAnimating b = State.isAnimating b.state

-- | Get the badge count.
-- |
-- | Convenience function — delegates to State layer.
getCount :: Badge -> Int
getCount b = State.getCount b.state

-- | Get the urgency level.
-- |
-- | Convenience function — delegates to State layer.
getUrgency :: Badge -> State.Urgency
getUrgency b = State.getUrgency b.state

-- | Should the badge pulse for attention?
-- |
-- | Convenience function — delegates to State layer.
shouldPulse :: Badge -> Boolean
shouldPulse b = State.shouldPulse b.state

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // geometry accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get badge shape.
-- |
-- | Convenience function — delegates to Geometry layer.
getShape :: Badge -> BadgeShape
getShape b = geoShape b.geometry

-- | Get badge size as (width, height).
-- |
-- | Convenience function — delegates to Geometry layer.
getSize :: Badge -> { width :: Number, height :: Number }
getSize b = geoSize b.geometry

-- | Get anchor position.
-- |
-- | Convenience function — delegates to Geometry layer.
getAnchor :: Badge -> AnchorPosition
getAnchor b = geoAnchor b.geometry

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // appearance accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get badge fill.
-- |
-- | Convenience function — delegates to Appearance layer.
getFill :: Badge -> Fill.Fill
getFill b = appFill b.appearance

-- | Get badge shadow.
-- |
-- | Convenience function — delegates to Appearance layer.
getShadow :: Badge -> Shadow.LayeredShadow
getShadow b = appShadow b.appearance

-- | Get badge text color.
-- |
-- | Convenience function — delegates to Appearance layer.
getTextColor :: Badge -> Color.RGB
getTextColor b = appTextColor b.appearance

-- | Get badge opacity.
-- |
-- | Convenience function — delegates to Appearance layer.
getOpacity :: Badge -> Opacity.Opacity
getOpacity b = appOpacity b.appearance

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // behavior accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for appear.
-- |
-- | Convenience function — delegates to Behavior layer.
getHapticOnAppear :: Badge -> Maybe Haptic.ImpactFeedback
getHapticOnAppear b = behHapticOnAppear b.behavior

-- | Get audio cue for appear.
-- |
-- | Convenience function — delegates to Behavior layer.
getAudioOnAppear :: Badge -> Maybe Haptic.AudioCue
getAudioOnAppear b = behAudioOnAppear b.behavior

-- | Should badge pulse on count change?
-- |
-- | Convenience function — delegates to Behavior layer.
getPulseOnCountChange :: Badge -> Boolean
getPulseOnCountChange b = behPulseOnCountChange b.behavior

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // semantics accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get badge purpose.
-- |
-- | Convenience function — delegates to Semantics layer.
getPurpose :: Badge -> BadgePurpose
getPurpose b = semPurpose b.semantics

-- | Get badge label.
-- |
-- | Convenience function — delegates to Semantics layer.
getLabel :: Badge -> String
getLabel b = semLabel b.semantics

-- | Get live region politeness.
-- |
-- | Convenience function — delegates to Semantics layer.
getLiveRegion :: Badge -> String
getLiveRegion b = show (semLiveRegion b.semantics)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set badge state.
setState :: State.BadgeElementState -> Badge -> Badge
setState st b = b { state = st }

-- | Set badge geometry.
setGeometry :: BadgeGeometry -> Badge -> Badge
setGeometry geo b = b { geometry = geo }

-- | Set badge appearance.
setAppearance :: BadgeAppearance -> Badge -> Badge
setAppearance app b = b { appearance = app }

-- | Set badge behavior.
setBehavior :: BadgeBehavior -> Badge -> Badge
setBehavior beh b = b { behavior = beh }

-- | Set badge semantics.
setSemantics :: BadgeSemantics -> Badge -> Badge
setSemantics sem b = b { semantics = sem }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // state layer modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set visibility.
-- |
-- | Convenience function — updates state layer.
setVisible :: Boolean -> Badge -> Badge
setVisible visible b = b { state = State.setVisible visible b.state }

-- | Set count.
-- |
-- | Convenience function — updates state layer.
setCount :: Int -> Badge -> Badge
setCount count b = b { state = State.setCount count b.state }

-- | Set urgency.
-- |
-- | Convenience function — updates state layer.
setUrgency :: State.Urgency -> Badge -> Badge
setUrgency urgency b = b { state = State.setUrgency urgency b.state }

-- | Set seen flag.
-- |
-- | Convenience function — updates state layer.
setSeen :: Boolean -> Badge -> Badge
setSeen seen b = b { state = State.setSeen seen b.state }

-- | Dismiss the badge — hide and mark seen.
-- |
-- | Convenience function — updates state layer.
dismiss :: Badge -> Badge
dismiss b = b { state = State.dismiss b.state }

-- | Mark badge as seen — reduce attention effects.
-- |
-- | Convenience function — updates state layer.
markSeen :: Badge -> Badge
markSeen b = b { state = State.markSeen b.state }
