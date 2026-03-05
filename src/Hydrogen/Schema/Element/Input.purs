-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // element // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input — Text input element compound.
-- |
-- | ## 5-Layer Architecture
-- |
-- | An Input element is composed of 5 layers:
-- | 1. **State**: Current value, validation, interaction flags
-- | 2. **Geometry**: Size, padding, border radius, multiline
-- | 3. **Appearance**: Fill, stroke, text colors, focus ring
-- | 4. **Behavior**: Debounce, autocomplete, clear button
-- | 5. **Semantics**: Purpose, ARIA, UUID5 identity
-- |
-- | ## Input Types
-- |
-- | Inputs are purpose-specific. A password input is NOT just a text input
-- | with dots — they have fundamentally different behaviors, autocomplete
-- | hints, and security requirements.
-- |
-- | This module provides purpose-aware presets:
-- | - `textInput`: General text entry
-- | - `passwordInput`: Masked, no spellcheck, autocomplete hints
-- | - `emailInput`: Email validation, keyboard hints
-- | - `searchInput`: Clear button, search-specific behavior
-- | - `urlInput`: URL validation
-- | - `phoneInput`: Phone keyboard, formatting
-- |
-- | ## Render Layer
-- |
-- | These 5 layers describe WHAT the input is, not HOW it renders.
-- | The actual visual representation is determined by the render target.
-- |
-- | ## Dependencies
-- |
-- | - Input.State (value, validation, interaction)
-- | - Input.Geometry (size, padding, multiline)
-- | - Input.Appearance (fills, borders, focus)
-- | - Input.Behavior (debounce, autocomplete)
-- | - Input.Semantics (purpose, ARIA, UUID5)

module Hydrogen.Schema.Element.Input
  ( -- * Input Compound Type
    Input
  
  -- * Constructors
  , input
  , defaultInput
  
  -- * Purpose Presets
  , textInput
  , passwordInput
  , emailInput
  , searchInput
  , urlInput
  , phoneInput
  , numberInput
  , multilineInput
  
  -- * Layer Accessors
  , getState
  , getGeometry
  , getAppearance
  , getBehavior
  , getSemantics
  
  -- * Layer Modifiers
  , setState
  , setGeometry
  , setAppearance
  , setBehavior
  , setSemantics
  
  -- * Convenience Accessors
  , getValue
  , getPlaceholder
  , getId
  , isDisabled
  , isFocused
  , hasError
  , isValid
  
  -- * Convenience Modifiers
  , setValue
  , setPlaceholder
  , setDisabled
  , setError
  , setValid
  , clearValidation
  
  -- * Sub-module re-exports
  -- | For detailed atoms, import sub-modules directly:
  -- | - Hydrogen.Schema.Element.Input.State
  -- | - Hydrogen.Schema.Element.Input.Geometry
  -- | - Hydrogen.Schema.Element.Input.Appearance
  -- | - Hydrogen.Schema.Element.Input.Behavior
  -- | - Hydrogen.Schema.Element.Input.Semantics
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

import Prim (Boolean, String)

import Hydrogen.Schema.Element.Input.State as State
import Hydrogen.Schema.Element.Input.Geometry as Geometry
import Hydrogen.Schema.Element.Input.Appearance as Appearance
import Hydrogen.Schema.Element.Input.Behavior as Behavior
import Hydrogen.Schema.Element.Input.Semantics as Semantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // input type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Input element — 5-layer compound.
-- |
-- | Composes all layers into a single type:
-- | - State (current value, validation, interaction flags)
-- | - Geometry (spatial layout, sizing)
-- | - Appearance (visual surface, colors)
-- | - Behavior (interaction response)
-- | - Semantics (purpose and accessibility)
type Input =
  { state :: State.InputElementState
  , geometry :: Geometry.InputGeometry
  , appearance :: Appearance.InputAppearance
  , behavior :: Behavior.InputBehavior
  , semantics :: Semantics.InputSemantics
  }

-- | Full constructor — assemble from all 5 layers.
input
  :: State.InputElementState
  -> Geometry.InputGeometry
  -> Appearance.InputAppearance
  -> Behavior.InputBehavior
  -> Semantics.InputSemantics
  -> Input
input st geo app beh sem =
  { state: st
  , geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default input with sensible defaults.
-- |
-- | Text type, medium size, outlined appearance.
defaultInput :: String -> Input
defaultInput key =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // purpose presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text input — general text entry.
textInput :: String -> Input
textInput key =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- | Password input — masked, secure entry.
passwordInput :: String -> Input
passwordInput key =
  { state: State.passwordState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.passwordBehavior
  , semantics: Semantics.passwordSemantics key
  }

-- | Email input — email validation, keyboard hints.
emailInput :: String -> Input
emailInput key =
  { state: State.emailState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.formBehavior
  , semantics: Semantics.emailSemantics key
  }

-- | Search input — clear button, debounced.
searchInput :: String -> Input
searchInput key =
  { state: State.searchState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.searchBehavior
  , semantics: Semantics.searchSemantics key
  }

-- | URL input — URL validation.
urlInput :: String -> Input
urlInput key =
  { state: State.defaultState { inputType = State.TypeUrl }
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.formBehavior
  , semantics: Semantics.urlSemantics key
  }

-- | Phone input — telephone keyboard.
phoneInput :: String -> Input
phoneInput key =
  { state: State.defaultState { inputType = State.TypeTel }
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.formBehavior
  , semantics: Semantics.phoneSemantics key
  }

-- | Number input — numeric keyboard.
numberInput :: String -> Input
numberInput key =
  { state: State.numberState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.formBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- | Multiline input — textarea style.
multilineInput :: String -> Input
multilineInput key =
  { state: State.defaultState
  , geometry: Geometry.multilineGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get input state.
getState :: Input -> State.InputElementState
getState i = i.state

-- | Get input geometry.
getGeometry :: Input -> Geometry.InputGeometry
getGeometry i = i.geometry

-- | Get input appearance.
getAppearance :: Input -> Appearance.InputAppearance
getAppearance i = i.appearance

-- | Get input behavior.
getBehavior :: Input -> Behavior.InputBehavior
getBehavior i = i.behavior

-- | Get input semantics.
getSemantics :: Input -> Semantics.InputSemantics
getSemantics i = i.semantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input state.
setState :: State.InputElementState -> Input -> Input
setState st i = i { state = st }

-- | Set input geometry.
setGeometry :: Geometry.InputGeometry -> Input -> Input
setGeometry geo i = i { geometry = geo }

-- | Set input appearance.
setAppearance :: Appearance.InputAppearance -> Input -> Input
setAppearance app i = i { appearance = app }

-- | Set input behavior.
setBehavior :: Behavior.InputBehavior -> Input -> Input
setBehavior beh i = i { behavior = beh }

-- | Set input semantics.
setSemantics :: Semantics.InputSemantics -> Input -> Input
setSemantics sem i = i { semantics = sem }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // convenience accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current value.
getValue :: Input -> String
getValue i = State.getValue i.state

-- | Get placeholder text.
getPlaceholder :: Input -> String
getPlaceholder i = State.getPlaceholder i.state

-- | Get deterministic UUID5 ID.
getId :: Input -> String
getId i = Semantics.inputIdString i.semantics

-- | Is the input disabled?
isDisabled :: Input -> Boolean
isDisabled i = State.isDisabled i.state

-- | Does the input have focus?
isFocused :: Input -> Boolean
isFocused i = State.isFocused i.state

-- | Does the input have an error?
hasError :: Input -> Boolean
hasError i = State.hasError i.state

-- | Is the input valid?
isValid :: Input -> Boolean
isValid i = State.isValid i.state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // convenience modifiers
-- ══════════════════════════════════════════════════��══════════════════════════

-- | Set value.
setValue :: String -> Input -> Input
setValue v i = i { state = State.setValue v i.state }

-- | Set placeholder.
setPlaceholder :: String -> Input -> Input
setPlaceholder p i = i { state = State.setPlaceholder p i.state }

-- | Set disabled state.
setDisabled :: Boolean -> Input -> Input
setDisabled d i = i { state = State.setDisabled d i.state }

-- | Set error validation state.
setError :: String -> Input -> Input
setError msg i = i { state = State.setError msg i.state }

-- | Set valid validation state.
setValid :: Input -> Input
setValid i = i { state = State.setValid i.state }

-- | Clear validation state.
clearValidation :: Input -> Input
clearValidation i = i { state = State.clearValidation i.state }
