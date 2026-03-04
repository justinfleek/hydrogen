-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // element // toggle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toggle — STACKED compound composing atoms from all pillars.
-- |
-- | A toggle/switch is a binary on/off control. This compound includes
-- | EVERY atom a toggle could ever need, enabling agents to compose
-- | any variant by selection.
-- |
-- | ## Architecture (5-Layer Model)
-- |
-- | Following the After Effects compositor mental model:
-- |
-- | 1. **State** — Current value (checked/unchecked, animating)
-- | 2. **Geometry** — Track/thumb dimensions, spacing
-- | 3. **Appearance** — Fills, shadows, glow, opacity
-- | 4. **Behavior** — Haptics, timing, keyboard handling
-- | 5. **Semantics** — Purpose, ARIA, UUID5 identity
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Element.Toggle as Toggle
-- |
-- | -- Simple settings toggle
-- | darkModeToggle = Toggle.settingsToggle "dark-mode" "Dark mode"
-- |
-- | -- Feature flag with description
-- | betaToggle = Toggle.featureToggle "beta" "Beta features"
-- |   "Enable experimental features"
-- |
-- | -- Custom toggle
-- | customToggle = Toggle.toggle
-- |   { state: Toggle.checkedState
-- |   , geometry: Toggle.largeGeometry
-- |   , appearance: Toggle.iosAppearance
-- |   , behavior: Toggle.richBehavior
-- |   , semantics: Toggle.settingSemantics "custom" "Custom toggle"
-- |   }
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Toggle.State (verified flags, progress)
-- | - Toggle.Geometry (verified dimensions)
-- | - Toggle.Appearance (verified fills, shadows)
-- | - Toggle.Behavior (verified haptics, timing)
-- | - Toggle.Semantics (verified ARIA, UUID5)

module Hydrogen.Schema.Element.Toggle
  ( -- * Toggle Compound Type
    Toggle
  , toggle
  , defaultToggle
  
  -- * Preset Toggles
  , settingsToggle
  , featureToggle
  , visibilityToggle
  , notificationToggle
  , iosToggle
  , materialToggle
  , compactToggle
  
  -- * Toggle Accessors
  , getState
  , getGeometry
  , getAppearance
  , getBehavior
  , getSemantics
  , isOn
  , getId
  
  -- * Toggle Modifiers
  , setState
  , setGeometry
  , setAppearance
  , setBehavior
  , setSemantics
  , setChecked
  , setDisabled
  
  -- * Sub-module Types (qualified access for atoms)
  -- | For detailed atoms, import sub-modules directly:
  -- | - Hydrogen.Schema.Element.Toggle.State
  -- | - Hydrogen.Schema.Element.Toggle.Geometry
  -- | - Hydrogen.Schema.Element.Toggle.Appearance
  -- | - Hydrogen.Schema.Element.Toggle.Behavior
  -- | - Hydrogen.Schema.Element.Toggle.Semantics
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

import Hydrogen.Schema.Element.Toggle.State
  ( ToggleElementState
  , defaultState
  , checkedState
  , uncheckedState
  , isChecked
  , setChecked
  ) as State

import Hydrogen.Schema.Element.Toggle.Geometry
  ( ToggleGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  ) as Geometry

import Hydrogen.Schema.Element.Toggle.Appearance
  ( ToggleAppearance
  , defaultAppearance
  , iosAppearance
  , materialAppearance
  , minimalAppearance
  ) as Appearance

import Hydrogen.Schema.Element.Toggle.Behavior
  ( ToggleBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  ) as Behavior

import Hydrogen.Schema.Element.Toggle.Semantics
  ( ToggleSemantics
  , TogglePurpose
      ( PurposeSetting
      , PurposeFeature
      , PurposeVisibility
      , PurposeNotification
      )
  , defaultSemantics
  , settingSemantics
  , featureSemantics
  , visibilitySemantics
  , notificationSemantics
  , toggleIdString
  , setDisabled
  ) as Semantics



-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // toggle type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | STACKED Toggle compound — complete toggle with all pillar atoms.
-- |
-- | Composes all 5 layers:
-- | - State (current value, animation)
-- | - Geometry (spatial layout)
-- | - Appearance (visual surface)
-- | - Behavior (interaction response)
-- | - Semantics (purpose and accessibility)
type Toggle =
  { state :: State.ToggleElementState
  , geometry :: Geometry.ToggleGeometry
  , appearance :: Appearance.ToggleAppearance
  , behavior :: Behavior.ToggleBehavior
  , semantics :: Semantics.ToggleSemantics
  }

-- | Create a toggle with all properties.
toggle
  :: State.ToggleElementState
  -> Geometry.ToggleGeometry
  -> Appearance.ToggleAppearance
  -> Behavior.ToggleBehavior
  -> Semantics.ToggleSemantics
  -> Toggle
toggle st geo app beh sem =
  { state: st
  , geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default toggle with sensible defaults.
-- |
-- | Unchecked, medium size, default appearance, light haptic.
defaultToggle :: String -> Toggle
defaultToggle key =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // preset toggles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Settings toggle — for app/system settings.
-- |
-- | Default geometry and appearance, setting semantics.
settingsToggle :: String -> String -> Toggle
settingsToggle key label =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.settingSemantics key label
  }

-- | Feature flag toggle — for enabling/disabling features.
-- |
-- | Includes description for extended explanation.
featureToggle :: String -> String -> String -> Toggle
featureToggle key label description =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.featureSemantics key label description
  }

-- | Visibility toggle — for showing/hiding elements.
-- |
-- | Includes aria-controls for the controlled element.
visibilityToggle :: String -> String -> String -> Toggle
visibilityToggle key label controlsId =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.visibilitySemantics key label controlsId
  }

-- | Notification toggle — for notification settings.
notificationToggle :: String -> String -> Toggle
notificationToggle key label =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.notificationSemantics key label
  }

-- | iOS-style toggle — green/gray with shadow.
iosToggle :: String -> String -> Toggle
iosToggle key label =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.iosAppearance
  , behavior: Behavior.richBehavior
  , semantics: Semantics.settingSemantics key label
  }

-- | Material Design toggle — primary color.
materialToggle :: String -> String -> Toggle
materialToggle key label =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.materialAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.settingSemantics key label
  }

-- | Compact toggle — small size for dense UIs.
compactToggle :: String -> String -> Toggle
compactToggle key label =
  { state: State.defaultState
  , geometry: Geometry.compactGeometry
  , appearance: Appearance.minimalAppearance
  , behavior: Behavior.silentBehavior
  , semantics: Semantics.settingSemantics key label
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get toggle state.
getState :: Toggle -> State.ToggleElementState
getState t = t.state

-- | Get toggle geometry.
getGeometry :: Toggle -> Geometry.ToggleGeometry
getGeometry t = t.geometry

-- | Get toggle appearance.
getAppearance :: Toggle -> Appearance.ToggleAppearance
getAppearance t = t.appearance

-- | Get toggle behavior.
getBehavior :: Toggle -> Behavior.ToggleBehavior
getBehavior t = t.behavior

-- | Get toggle semantics.
getSemantics :: Toggle -> Semantics.ToggleSemantics
getSemantics t = t.semantics

-- | Is the toggle currently on (checked)?
isOn :: Toggle -> Boolean
isOn t = State.isChecked t.state

-- | Get the deterministic UUID5 ID for this toggle.
getId :: Toggle -> String
getId t = Semantics.toggleIdString t.semantics

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set toggle state.
setState :: State.ToggleElementState -> Toggle -> Toggle
setState st t = t { state = st }

-- | Set toggle geometry.
setGeometry :: Geometry.ToggleGeometry -> Toggle -> Toggle
setGeometry geo t = t { geometry = geo }

-- | Set toggle appearance.
setAppearance :: Appearance.ToggleAppearance -> Toggle -> Toggle
setAppearance app t = t { appearance = app }

-- | Set toggle behavior.
setBehavior :: Behavior.ToggleBehavior -> Toggle -> Toggle
setBehavior beh t = t { behavior = beh }

-- | Set toggle semantics.
setSemantics :: Semantics.ToggleSemantics -> Toggle -> Toggle
setSemantics sem t = t { semantics = sem }

-- | Set checked state.
setChecked :: Boolean -> Toggle -> Toggle
setChecked checked t = t { state = State.setChecked checked t.state }

-- | Set disabled state.
setDisabled :: Boolean -> Toggle -> Toggle
setDisabled disabled t = t { semantics = Semantics.setDisabled disabled t.semantics }
