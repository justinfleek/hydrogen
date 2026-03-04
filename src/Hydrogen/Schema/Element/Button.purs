-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // element // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button — STACKED compound composing atoms from all pillars.
-- |
-- | A button is a bounded region of space-time where AI communicates
-- | intent, state, and need. This compound includes EVERY atom a button
-- | could ever need, enabling agents to compose any variant by selection.
-- |
-- | ## Architecture (5-Layer Model)
-- |
-- | Following the After Effects compositor mental model:
-- |
-- | 1. **State** — Interaction state (focused, hovered, pressed, loading)
-- | 2. **Geometry** — Size, padding, corner radii
-- | 3. **Appearance** — Fill, border, shadow, opacity
-- | 4. **Behavior** — Haptic, audio, timing
-- | 5. **Semantics** — Purpose, identity, accessibility
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Element.Button as Button
-- |
-- | -- Simple button
-- | myButton = Button.defaultButton "Click me"
-- |
-- | -- Custom button
-- | customButton = Button.button
-- |   Button.defaultState
-- |   Button.defaultGeometry
-- |   Button.defaultAppearance
-- |   Button.defaultBehavior
-- |   (Button.actionSemantics "Submit")
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Button.State (interaction flags)
-- | - Button.Geometry (spatial layout)
-- | - Button.Appearance (visual surface)
-- | - Button.Behavior (interaction response)
-- | - Button.Semantics (purpose and accessibility)

module Hydrogen.Schema.Element.Button
  ( -- * Button Compound Type
    Button
  , button
  , defaultButton
  
  -- * Button Accessors
  , getState
  , getGeometry
  , getAppearance
  , getBehavior
  , getSemantics
  
  -- * State Accessors (convenience - delegates to State layer)
  , isFocused
  , isHovered
  , isPressed
  , isLoading
  , isAnimating
  , isInteractive
  
  -- * Geometry Accessors (convenience - delegates to Geometry layer)
  , getWidth
  , getHeight
  , getPadding
  , getCornerRadii
  
  -- * Appearance Accessors (convenience - delegates to Appearance layer)
  , getFill
  , getShadow
  , getBorderWidth
  , getBorderColor
  , getOpacity
  
  -- * Behavior Accessors (convenience - delegates to Behavior layer)
  , getHapticPress
  , getHapticRelease
  , getAudioClick
  , getLongPressMs
  
  -- * Semantics Accessors (convenience - delegates to Semantics layer)
  , getPurpose
  , getLabel
  , getToggleState
  , isDisabled
  
  -- * Button Modifiers
  , setState
  , setGeometry
  , setAppearance
  , setBehavior
  , setSemantics
  
  -- * State Modifiers (convenience - updates State layer)
  , setFocused
  , setHovered
  , setPressed
  , setLoading
  , setAnimating
  , resetInteraction
  
  -- * Sub-module Types (qualified access for atoms)
  -- | For detailed atoms, import sub-modules directly:
  -- | - Hydrogen.Schema.Element.Button.State
  -- | - Hydrogen.Schema.Element.Button.Geometry
  -- | - Hydrogen.Schema.Element.Button.Appearance
  -- | - Hydrogen.Schema.Element.Button.Behavior
  -- | - Hydrogen.Schema.Element.Button.Semantics
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (<>)
  )

import Data.Maybe (Maybe)

-- Types needed for compound-level accessor return types
import Hydrogen.Schema.Geometry.Spacing (Padding) as Spacing
import Hydrogen.Schema.Geometry.CornerRadii (CornerRadii) as Corner
import Hydrogen.Schema.Surface.Fill (Fill) as Fill
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow) as Shadow
import Hydrogen.Schema.Color.RGB (RGB) as Color
import Hydrogen.Schema.Haptic.Feedback (ImpactFeedback) as Haptic
import Hydrogen.Schema.Haptic.Event (AudioCue) as Haptic
import Hydrogen.Schema.Reactive.ButtonSemantics (ButtonPurpose, ToggleState) as Sem

import Hydrogen.Schema.Element.Button.State
  ( ButtonElementState
  -- Preset states
  , defaultState
  , idleState
  , focusedState
  , hoveredState
  , pressedState
  , loadingState
  -- Accessors (used to implement compound-level accessors)
  , isFocused
  , isHovered
  , isPressed
  , isLoading
  , isAnimating
  , isInteractive
  -- Modifiers (used to implement compound-level modifiers)
  , setFocused
  , setHovered
  , setPressed
  , setLoading
  , setAnimating
  , resetInteraction
  ) as State

import Hydrogen.Schema.Element.Button.Geometry
  ( ButtonGeometry
  , defaultGeometry
  , mkGeometry
  , geoWidth
  , geoHeight
  , geoPadding
  , geoCornerRadii
  )

import Hydrogen.Schema.Element.Button.Appearance
  ( ButtonAppearance
  , defaultAppearance
  , appFill
  , appShadow
  , appBorderWidth
  , appBorderColor
  , appOpacity
  )

import Hydrogen.Schema.Element.Button.Behavior
  ( ButtonBehavior
  , defaultBehavior
  , behHapticPress
  , behHapticRelease
  , behAudioClick
  , behLongPressMs
  )

import Hydrogen.Schema.Element.Button.Semantics
  ( ButtonSemantics
  , defaultSemantics
  , actionSemantics
  , submitSemantics
  , toggleSemantics
  , semPurpose
  , semLabel
  , semToggleState
  , semDisabled
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // button type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | STACKED Button compound — complete button with all pillar atoms.
-- |
-- | Composes all 5 layers:
-- | - State (interaction flags)
-- | - Geometry (spatial layout)
-- | - Appearance (visual surface)
-- | - Behavior (interaction response)
-- | - Semantics (purpose and accessibility)
type Button =
  { state :: State.ButtonElementState
  , geometry :: ButtonGeometry
  , appearance :: ButtonAppearance
  , behavior :: ButtonBehavior
  , semantics :: ButtonSemantics
  }

-- | Create a button with all properties.
button
  :: State.ButtonElementState
  -> ButtonGeometry
  -> ButtonAppearance
  -> ButtonBehavior
  -> ButtonSemantics
  -> Button
button st geo app beh sem =
  { state: st
  , geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default button with sensible defaults.
-- |
-- | Idle state, blue fill, 8px corners, light haptic, "Button" label.
defaultButton :: String -> Button
defaultButton label =
  { state: State.defaultState
  , geometry: defaultGeometry
  , appearance: defaultAppearance
  , behavior: defaultBehavior
  , semantics: defaultSemantics label
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get button state.
getState :: Button -> State.ButtonElementState
getState b = b.state

-- | Get button geometry.
getGeometry :: Button -> ButtonGeometry
getGeometry b = b.geometry

-- | Get button appearance.
getAppearance :: Button -> ButtonAppearance
getAppearance b = b.appearance

-- | Get button behavior.
getBehavior :: Button -> ButtonBehavior
getBehavior b = b.behavior

-- | Get button semantics.
getSemantics :: Button -> ButtonSemantics
getSemantics b = b.semantics

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // state accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Does the button have keyboard focus?
-- |
-- | Convenience function — delegates to State layer.
isFocused :: Button -> Boolean
isFocused b = State.isFocused b.state

-- | Is the pointer hovering over the button?
-- |
-- | Convenience function — delegates to State layer.
isHovered :: Button -> Boolean
isHovered b = State.isHovered b.state

-- | Is the button being pressed?
-- |
-- | Convenience function — delegates to State layer.
isPressed :: Button -> Boolean
isPressed b = State.isPressed b.state

-- | Is the button in loading state?
-- |
-- | Convenience function — delegates to State layer.
isLoading :: Button -> Boolean
isLoading b = State.isLoading b.state

-- | Is a visual transition in progress?
-- |
-- | Convenience function — delegates to State layer.
isAnimating :: Button -> Boolean
isAnimating b = State.isAnimating b.state

-- | Is the button interactive?
-- |
-- | False when loading. Note: This does NOT check disabled from Semantics.
-- | For full interactivity check, also check Semantics.disabled.
isInteractive :: Button -> Boolean
isInteractive b = State.isInteractive b.state

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // geometry accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get button width.
-- |
-- | Nothing = auto sizing. Convenience function — delegates to Geometry layer.
getWidth :: Button -> Maybe Number
getWidth b = geoWidth b.geometry

-- | Get button height.
-- |
-- | Nothing = auto sizing. Convenience function — delegates to Geometry layer.
getHeight :: Button -> Maybe Number
getHeight b = geoHeight b.geometry

-- | Get button padding.
-- |
-- | Convenience function — delegates to Geometry layer.
getPadding :: Button -> Spacing.Padding
getPadding b = geoPadding b.geometry

-- | Get button corner radii.
-- |
-- | Convenience function — delegates to Geometry layer.
getCornerRadii :: Button -> Corner.CornerRadii
getCornerRadii b = geoCornerRadii b.geometry

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // appearance accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get button fill.
-- |
-- | Convenience function — delegates to Appearance layer.
getFill :: Button -> Fill.Fill
getFill b = appFill b.appearance

-- | Get button shadow.
-- |
-- | Convenience function — delegates to Appearance layer.
getShadow :: Button -> Shadow.LayeredShadow
getShadow b = appShadow b.appearance

-- | Get button border width.
-- |
-- | Convenience function — delegates to Appearance layer.
getBorderWidth :: Button -> Number
getBorderWidth b = appBorderWidth b.appearance

-- | Get button border color.
-- |
-- | Nothing = transparent. Convenience function — delegates to Appearance layer.
getBorderColor :: Button -> Maybe Color.RGB
getBorderColor b = appBorderColor b.appearance

-- | Get button opacity.
-- |
-- | Convenience function — delegates to Appearance layer.
getOpacity :: Button -> Number
getOpacity b = appOpacity b.appearance

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // behavior accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for press.
-- |
-- | Convenience function — delegates to Behavior layer.
getHapticPress :: Button -> Maybe Haptic.ImpactFeedback
getHapticPress b = behHapticPress b.behavior

-- | Get haptic feedback for release.
-- |
-- | Convenience function — delegates to Behavior layer.
getHapticRelease :: Button -> Maybe Haptic.ImpactFeedback
getHapticRelease b = behHapticRelease b.behavior

-- | Get audio cue for click.
-- |
-- | Convenience function — delegates to Behavior layer.
getAudioClick :: Button -> Maybe Haptic.AudioCue
getAudioClick b = behAudioClick b.behavior

-- | Get long press threshold in milliseconds.
-- |
-- | Convenience function — delegates to Behavior layer.
getLongPressMs :: Button -> Number
getLongPressMs b = behLongPressMs b.behavior

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // semantics accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get button purpose.
-- |
-- | Convenience function — delegates to Semantics layer.
getPurpose :: Button -> Sem.ButtonPurpose
getPurpose b = semPurpose b.semantics

-- | Get button label.
-- |
-- | Convenience function — delegates to Semantics layer.
getLabel :: Button -> String
getLabel b = semLabel b.semantics

-- | Get toggle state for toggle buttons.
-- |
-- | Nothing for non-toggle buttons. Convenience function — delegates to Semantics layer.
getToggleState :: Button -> Maybe Sem.ToggleState
getToggleState b = semToggleState b.semantics

-- | Is the button disabled?
-- |
-- | This is the ARIA semantic disabled, not the loading state.
-- | Convenience function — delegates to Semantics layer.
isDisabled :: Button -> Boolean
isDisabled b = semDisabled b.semantics

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set button state.
setState :: State.ButtonElementState -> Button -> Button
setState st b = b { state = st }

-- | Set button geometry.
setGeometry :: ButtonGeometry -> Button -> Button
setGeometry geo b = b { geometry = geo }

-- | Set button appearance.
setAppearance :: ButtonAppearance -> Button -> Button
setAppearance app b = b { appearance = app }

-- | Set button behavior.
setBehavior :: ButtonBehavior -> Button -> Button
setBehavior beh b = b { behavior = beh }

-- | Set button semantics.
setSemantics :: ButtonSemantics -> Button -> Button
setSemantics sem b = b { semantics = sem }

-- | Set loading state.
-- |
-- | Convenience function — updates state layer.
setLoading :: Boolean -> Button -> Button
setLoading loading b = b { state = State.setLoading loading b.state }

-- | Set focused state.
-- |
-- | Convenience function — updates state layer.
setFocused :: Boolean -> Button -> Button
setFocused focused b = b { state = State.setFocused focused b.state }

-- | Set hovered state.
-- |
-- | Convenience function — updates state layer.
setHovered :: Boolean -> Button -> Button
setHovered hovered b = b { state = State.setHovered hovered b.state }

-- | Set pressed state.
-- |
-- | Convenience function — updates state layer.
setPressed :: Boolean -> Button -> Button
setPressed pressed b = b { state = State.setPressed pressed b.state }

-- | Set animating state.
-- |
-- | Convenience function — updates state layer.
setAnimating :: Boolean -> Button -> Button
setAnimating animating b = b { state = State.setAnimating animating b.state }

-- | Reset all interaction flags to idle.
-- |
-- | Useful when button is programmatically disabled or hidden.
-- | Preserves loading state (that's async, not interaction).
resetInteraction :: Button -> Button
resetInteraction b = b { state = State.resetInteraction b.state }
