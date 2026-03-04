-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // element // slider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider — STACKED compound composing atoms from all pillars.
-- |
-- | A slider is a range input control for selecting values within a range.
-- | This compound includes EVERY atom a slider could ever need, enabling
-- | agents to compose any variant by selection.
-- |
-- | ## Architecture (5-Layer Model)
-- |
-- | Following the After Effects compositor mental model:
-- |
-- | 1. **State** — Current value (hue, saturation, volume, etc.)
-- | 2. **Geometry** — Track/thumb dimensions, orientation
-- | 3. **Appearance** — Fills, gradients, shadows, opacity
-- | 4. **Behavior** — Haptics, timing, stepping, scroll
-- | 5. **Semantics** — Purpose, ARIA, UUID5 identity
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Element.Slider as Slider
-- |
-- | -- Hue picker slider
-- | hueSlider = Slider.hueSlider "color-picker-hue"
-- |
-- | -- Volume control
-- | volumeSlider = Slider.volumeSlider "player-volume"
-- |
-- | -- Custom slider
-- | customSlider = Slider.slider
-- |   { state: Slider.progressState 0.5
-- |   , geometry: Slider.largeGeometry
-- |   , appearance: Slider.hueAppearance
-- |   , behavior: Slider.precisionBehavior
-- |   , semantics: Slider.hueSemantics "custom-hue"
-- |   }
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Slider.State (verified value types)
-- | - Slider.Geometry (verified dimensions)
-- | - Slider.Appearance (verified fills, gradients)
-- | - Slider.Behavior (verified haptics, timing)
-- | - Slider.Semantics (verified ARIA, UUID5)

module Hydrogen.Schema.Element.Slider
  ( -- * Slider Compound Type
    Slider
  , slider
  , defaultSlider
  
  -- * Preset Sliders
  , hueSlider
  , saturationSlider
  , lightnessSlider
  , volumeSlider
  , opacitySlider
  , temperatureSlider
  , zoomSlider
  , progressSlider
  , compactSlider
  
  -- * Slider Accessors
  , getState
  , getGeometry
  , getAppearance
  , getBehavior
  , getSemantics
  , getValue
  , getProgressNormalized
  , getId
  
  -- * Slider Modifiers
  , setState
  , setGeometry
  , setAppearance
  , setBehavior
  , setSemantics
  , setDisabled
  
  -- * Sub-module Types (qualified access for atoms)
  -- | For detailed atoms, import sub-modules directly:
  -- | - Hydrogen.Schema.Element.Slider.State
  -- | - Hydrogen.Schema.Element.Slider.Geometry
  -- | - Hydrogen.Schema.Element.Slider.Appearance
  -- | - Hydrogen.Schema.Element.Slider.Behavior
  -- | - Hydrogen.Schema.Element.Slider.Semantics
  -- | - Hydrogen.Schema.Element.Slider.Layers (compositor layers)
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

import Prim (Boolean, Number, String)

import Hydrogen.Schema.Element.Slider.State
  ( SliderElementState
  , SliderValue
  , Progress
  , defaultState
  , hueState
  , saturationState
  , lightnessState
  , volumeState
  , progressState
  , getValue
  , getProgressNormalized
  ) as State

import Hydrogen.Schema.Element.Slider.Geometry
  ( SliderGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , verticalGeometry
  , colorPickerGeometry
  ) as Geometry

import Hydrogen.Schema.Element.Slider.Appearance
  ( SliderAppearance
  , defaultAppearance
  , minimalAppearance
  , hueAppearance
  , saturationAppearance
  , lightnessAppearance
  , volumeAppearance
  , temperatureAppearance
  ) as Appearance

import Hydrogen.Schema.Element.Slider.Behavior
  ( SliderBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  , precisionBehavior
  ) as Behavior

import Hydrogen.Schema.Element.Slider.Semantics
  ( SliderSemantics
  , SliderPurpose
      ( PurposeHue
      , PurposeSaturation
      , PurposeLightness
      , PurposeVolume
      , PurposeOpacity
      , PurposeTemperature
      , PurposeZoom
      , PurposeProgress
      )
  , defaultSemantics
  , hueSemantics
  , saturationSemantics
  , lightnessSemantics
  , volumeSemantics
  , opacitySemantics
  , temperatureSemantics
  , zoomSemantics
  , sliderIdString
  , setDisabled
  ) as Semantics

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // slider type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | STACKED Slider compound — complete slider with all pillar atoms.
-- |
-- | Composes all 5 layers:
-- | - State (current value, interaction flags)
-- | - Geometry (spatial layout)
-- | - Appearance (visual surface, gradients)
-- | - Behavior (interaction response)
-- | - Semantics (purpose and accessibility)
type Slider =
  { state :: State.SliderElementState
  , geometry :: Geometry.SliderGeometry
  , appearance :: Appearance.SliderAppearance
  , behavior :: Behavior.SliderBehavior
  , semantics :: Semantics.SliderSemantics
  }

-- | Create a slider with all properties.
slider
  :: State.SliderElementState
  -> Geometry.SliderGeometry
  -> Appearance.SliderAppearance
  -> Behavior.SliderBehavior
  -> Semantics.SliderSemantics
  -> Slider
slider st geo app beh sem =
  { state: st
  , geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default slider with sensible defaults.
-- |
-- | Progress type, 0-100 range, default appearance.
defaultSlider :: String -> Slider
defaultSlider key =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // preset sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hue slider — rainbow gradient for color selection.
-- |
-- | Range 0-360°, wrapping, rainbow track fill.
hueSlider :: String -> Slider
hueSlider key =
  { state: State.hueState
  , geometry: Geometry.colorPickerGeometry
  , appearance: Appearance.hueAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.hueSemantics key
  }

-- | Saturation slider — gray to saturated gradient.
-- |
-- | Range 0-100%, saturation gradient track.
saturationSlider :: String -> Slider
saturationSlider key =
  { state: State.saturationState
  , geometry: Geometry.colorPickerGeometry
  , appearance: Appearance.saturationAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.saturationSemantics key
  }

-- | Lightness slider — black to white gradient.
-- |
-- | Range 0-100%, lightness gradient track.
lightnessSlider :: String -> Slider
lightnessSlider key =
  { state: State.lightnessState
  , geometry: Geometry.colorPickerGeometry
  , appearance: Appearance.lightnessAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.lightnessSemantics key
  }

-- | Volume slider — green progress bar style.
-- |
-- | Range 0-100%, gray track with green progress.
volumeSlider :: String -> Slider
volumeSlider key =
  { state: State.volumeState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.volumeAppearance
  , behavior: Behavior.richBehavior
  , semantics: Semantics.volumeSemantics key
  }

-- | Opacity slider — checkered background with alpha gradient.
-- |
-- | Range 0-100%, transparent to opaque.
opacitySlider :: String -> Slider
opacitySlider key =
  { state: State.progressState
  , geometry: Geometry.colorPickerGeometry
  , appearance: Appearance.defaultAppearance  -- Could add opacity-specific appearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.opacitySemantics key
  }

-- | Temperature slider — warm to cool gradient.
-- |
-- | Range 1000-40000K, orange to blue gradient.
temperatureSlider :: String -> Slider
temperatureSlider key =
  { state: State.progressState
  , geometry: Geometry.colorPickerGeometry
  , appearance: Appearance.temperatureAppearance
  , behavior: Behavior.precisionBehavior
  , semantics: Semantics.temperatureSemantics key
  }

-- | Zoom slider — for zoom controls.
-- |
-- | Range 10-400%, step 10%.
zoomSlider :: String -> Slider
zoomSlider key =
  { state: State.progressState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.precisionBehavior
  , semantics: Semantics.zoomSemantics key
  }

-- | Progress slider — generic 0-100% slider.
-- |
-- | Standard appearance with progress fill.
progressSlider :: String -> String -> Slider
progressSlider key label =
  { state: State.progressState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: (Semantics.defaultSemantics key) { label = label }
  }

-- | Compact slider — small size for inline controls.
-- |
-- | Minimal appearance, silent behavior.
compactSlider :: String -> String -> Slider
compactSlider key label =
  { state: State.progressState
  , geometry: Geometry.compactGeometry
  , appearance: Appearance.minimalAppearance
  , behavior: Behavior.silentBehavior
  , semantics: (Semantics.defaultSemantics key) { label = label }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get slider state.
getState :: Slider -> State.SliderElementState
getState s = s.state

-- | Get slider geometry.
getGeometry :: Slider -> Geometry.SliderGeometry
getGeometry s = s.geometry

-- | Get slider appearance.
getAppearance :: Slider -> Appearance.SliderAppearance
getAppearance s = s.appearance

-- | Get slider behavior.
getBehavior :: Slider -> Behavior.SliderBehavior
getBehavior s = s.behavior

-- | Get slider semantics.
getSemantics :: Slider -> Semantics.SliderSemantics
getSemantics s = s.semantics

-- | Get the current slider value.
getValue :: Slider -> State.SliderValue
getValue s = State.getValue s.state

-- | Get the current value normalized to 0.0-1.0.
getProgressNormalized :: Slider -> State.Progress
getProgressNormalized s = State.getProgressNormalized s.state

-- | Get the deterministic UUID5 ID for this slider.
getId :: Slider -> String
getId s = Semantics.sliderIdString s.semantics

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set slider state.
setState :: State.SliderElementState -> Slider -> Slider
setState st s = s { state = st }

-- | Set slider geometry.
setGeometry :: Geometry.SliderGeometry -> Slider -> Slider
setGeometry geo s = s { geometry = geo }

-- | Set slider appearance.
setAppearance :: Appearance.SliderAppearance -> Slider -> Slider
setAppearance app s = s { appearance = app }

-- | Set slider behavior.
setBehavior :: Behavior.SliderBehavior -> Slider -> Slider
setBehavior beh s = s { behavior = beh }

-- | Set slider semantics.
setSemantics :: Semantics.SliderSemantics -> Slider -> Slider
setSemantics sem s = s { semantics = sem }

-- | Set disabled state.
setDisabled :: Boolean -> Slider -> Slider
setDisabled disabled s = s { semantics = Semantics.setDisabled disabled s.semantics }
