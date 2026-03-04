-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // element // knob
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Knob — Rotational control element compound.
-- |
-- | ## 5-Layer Architecture
-- |
-- | A Knob element is composed of 5 layers:
-- | 1. **State**: Current value, interaction flags, automation mode
-- | 2. **Geometry**: Size, arc angles, indicator positioning
-- | 3. **Appearance**: Fills, shadows, warning zones, bipolar display
-- | 4. **Behavior**: Drag modes, haptics, MIDI, fine control
-- | 5. **Semantics**: Purpose, ARIA, UUID5 identity, formatters
-- |
-- | ## Domain-Specific Presets
-- |
-- | Knobs are highly domain-specific. A hospital knob is NOT just an
-- | Ableton knob with different colors — they have fundamentally different
-- | state machines, behaviors, and semantic requirements.
-- |
-- | This module provides domain-aware presets:
-- | - `dawKnob`: Compact, linear-vertical drag, MIDI-ready
-- | - `medicalKnob`: Large, discrete steps, safety zones, confirmation
-- | - `gameKnob`: Circular drag, full feedback, glow effects
-- | - `mographKnob`: Keyframe-aware, expression support
-- |
-- | ## Graded Monad Integration
-- |
-- | Knob elements participate in the Orchard co-effect algebra:
-- | - Pure knobs require nothing (CoEffectNone)
-- | - MIDI-mapped knobs require HW access (CoEffectMIDI)
-- | - Automated knobs require timeline context (CoEffectTimeline)
-- | - Audio feedback requires audio context (CoEffectAudio)
-- |
-- | The co-effect is derived from the Behavior layer configuration.
-- |
-- | ## Render Layer
-- |
-- | These 5 layers describe WHAT the knob is, not HOW it renders.
-- | The actual visual representation (2D SVG, 3D mesh with PBR materials)
-- | is determined by the render target interpreting these atoms.
-- |
-- | A square knob with a diamond peak and real lighting is possible —
-- | the shape/mesh is defined separately in Hydrogen.Schema.Spatial.
-- |
-- | ## Dependencies
-- |
-- | - Knob.State (value, interaction, automation)
-- | - Knob.Geometry (size, arc, indicator)
-- | - Knob.Appearance (fills, zones, effects)
-- | - Knob.Behavior (drag, haptics, MIDI)
-- | - Knob.Semantics (purpose, ARIA, UUID5)

module Hydrogen.Schema.Element.Knob
  ( -- * Knob Compound Type
    Knob
  
  -- * Constructors
  , knob
  , defaultKnob
  
  -- * Domain Presets
  , dawKnob
  , medicalKnob
  , gameKnob
  , mographKnob
  
  -- * Purpose-Specific Presets
  , volumeKnob
  , panKnob
  , frequencyKnob
  , rateKnob
  , rotationKnob
  , hueKnob
  
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
  , getAngle
  , getId
  , isDisabled
  , isDragging
  , isBipolar
  , hasWarningZones
  
  -- * Convenience Modifiers
  , setValue
  , setDisabled
  , resetToDefault
  
  -- * Re-exports from layers
  , module Hydrogen.Schema.Element.Knob.State
  , module Hydrogen.Schema.Element.Knob.Geometry
  , module Hydrogen.Schema.Element.Knob.Appearance
  , module Hydrogen.Schema.Element.Knob.Behavior
  , module Hydrogen.Schema.Element.Knob.Semantics
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  , (==)
  )

import Prim (Boolean, String)

import Hydrogen.Schema.Element.Knob.State as State
import Hydrogen.Schema.Element.Knob.State
  ( KnobElementState
  , KnobValue(..)
  , AutomationMode(..)
  , KeyframePresence(..)
  , SafetyZone(..)
  , defaultState
  , volumeState
  , panState
  , frequencyState
  , rateState
  , rotationState
  , medicalState
  , toProgress
  -- NOTE: isBipolar intentionally NOT imported here.
  -- State.isBipolar checks if KnobValue is bipolar (Pan/Bipolar variants).
  -- This module defines its own isBipolar that checks KnobAppearance.
  -- The appearance-based check is the correct semantic at compound level.
  )

import Hydrogen.Schema.Element.Knob.Geometry as Geometry
import Hydrogen.Schema.Element.Knob.Geometry
  ( KnobGeometry
  , KnobSize(..)
  , ArcConfig
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , hugeGeometry
  , dawGeometry
  , medicalGeometry
  , gameGeometry
  , arcStandard
  , arcFull
  )

import Hydrogen.Schema.Element.Knob.Appearance as Appearance
import Hydrogen.Schema.Element.Knob.Appearance
  ( KnobAppearance
  , KnobVariant(..)
  , ZoneConfig
  , BipolarConfig
  , defaultAppearance
  , minimalAppearance
  , bipolarAppearance
  , medicalAppearance
  , dawAppearance
  , gameAppearance
  , mographAppearance
  )

import Hydrogen.Schema.Element.Knob.Behavior as Behavior
import Hydrogen.Schema.Element.Knob.Behavior
  ( KnobBehavior
  , DragMode(..)
  , SnapBehavior(..)
  , MIDIConfig
  , defaultBehavior
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  , dawBehavior
  , medicalBehavior
  , gameBehavior
  , midiDisabled
  , midiCC
  )

import Hydrogen.Schema.Element.Knob.Semantics as Semantics
import Hydrogen.Schema.Element.Knob.Semantics
  ( KnobSemantics
  , KnobPurpose(..)
  , KnobRange
  , ScaleType(..)
  , ValueFormatter
  , defaultSemantics
  , volumeSemantics
  , panSemantics
  , frequencySemantics
  , rateSemantics
  , rotationSemantics
  , medicalSemantics
  , knobId
  , knobIdString
  )

import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // knob compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Knob element — 5-layer compound.
-- |
-- | Each layer is independently configurable, but domain presets
-- | provide coherent combinations for specific use cases.
type Knob =
  { state :: KnobElementState
  , geometry :: KnobGeometry
  , appearance :: KnobAppearance
  , behavior :: KnobBehavior
  , semantics :: KnobSemantics
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full constructor — assemble from all 5 layers.
knob 
  :: KnobElementState 
  -> KnobGeometry 
  -> KnobAppearance 
  -> KnobBehavior 
  -> KnobSemantics 
  -> Knob
knob st geo app beh sem =
  { state: st
  , geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default knob with given key.
-- |
-- | Creates a general-purpose knob with sensible defaults:
-- | - Medium size, standard 270° arc
-- | - Linear-vertical drag (DAW style)
-- | - Blue value fill, white indicator
-- | - Light haptic feedback
defaultKnob :: String -> Knob
defaultKnob key =
  { state: State.defaultState
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.defaultSemantics key
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // domain presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | DAW (Digital Audio Workstation) knob.
-- |
-- | Optimized for professional audio workflows:
-- | - Compact size (28px) for dense parameter panels
-- | - Linear-vertical drag (Ableton/Logic style)
-- | - Fine control with Shift modifier
-- | - Double-click to reset
-- | - Dark theme, minimal visual noise
-- | - MIDI learn ready
-- | - No haptics (typical for desktop DAWs)
dawKnob :: String -> String -> Knob
dawKnob key label =
  { state: State.defaultState
  , geometry: Geometry.dawGeometry
  , appearance: Appearance.dawAppearance
  , behavior: Behavior.dawBehavior
  , semantics: (Semantics.defaultSemantics key)
      { label = label
      , purpose = PurposeCustom label
      }
  }

-- | Medical/Hospital dashboard knob.
-- |
-- | Optimized for life-critical applications:
-- | - HUGE size (80px) for glove operation
-- | - Circular drag (physical knob metaphor)
-- | - Discrete steps (100 positions)
-- | - Safety zones with color coding (green/yellow/red)
-- | - Confirmation required for danger zone values
-- | - Strong haptic feedback at every step
-- | - High contrast, large numeric display
-- | - aria-valuetext includes units: "120 milliliters per hour"
medicalKnob :: String -> String -> Knob
medicalKnob key label =
  { state: State.medicalState 0.0
  , geometry: Geometry.medicalGeometry
  , appearance: Appearance.medicalAppearance
  , behavior: Behavior.medicalBehavior
  , semantics: (Semantics.medicalSemantics key)
      { label = label
      }
  }

-- | Game UI knob.
-- |
-- | Optimized for fun, responsive interactions:
-- | - Medium size with glow effects
-- | - Circular drag (intuitive)
-- | - Full haptic and audio feedback
-- | - Optional wrap-around (for hue/rotation)
-- | - Fast animations, visual juice
-- | - Particle effects possible on max value
gameKnob :: String -> String -> Knob
gameKnob key label =
  { state: State.defaultState
  , geometry: Geometry.gameGeometry
  , appearance: Appearance.gameAppearance
  , behavior: Behavior.gameBehavior
  , semantics: (Semantics.defaultSemantics key)
      { label = label
      , purpose = PurposeCustom label
      }
  }

-- | Motion graphics knob (After Effects / Cinema 4D style).
-- |
-- | Optimized for animation workflows:
-- | - Compact size for property panels
-- | - Keyframe indicator support
-- | - Expression binding awareness
-- | - Scrubber-style interaction (click-drag on number)
-- | - Timeline integration
-- | - Dark theme (amber accent like AE)
mographKnob :: String -> String -> Knob
mographKnob key label =
  { state: State.defaultState
      { keyframePresence = KeyframeNone
      , automationMode = AutoManual
      }
  , geometry: Geometry.compactGeometry
  , appearance: Appearance.mographAppearance
  , behavior: Behavior.defaultBehavior
      { dragMode = DragLinearVertical
      , fineModifier = true
      , snap = SnapToDefault
      }
  , semantics: (Semantics.defaultSemantics key)
      { label = label
      , purpose = PurposeCustom label
      }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // purpose-specific presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Volume knob (0-100%, default 80%).
volumeKnob :: String -> Knob
volumeKnob key =
  { state: State.volumeState 80.0
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.volumeSemantics key
  }

-- | Pan knob (L64 to R64, center = 0).
panKnob :: String -> Knob
panKnob key =
  { state: State.panState 0.0
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.bipolarAppearance
  , behavior: Behavior.defaultBehavior
      { snap = SnapToCenter
      }
  , semantics: Semantics.panSemantics key
  }

-- | Frequency knob (20Hz to 20kHz, logarithmic).
frequencyKnob :: String -> Knob
frequencyKnob key =
  { state: State.frequencyState 1000.0
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
  , semantics: Semantics.frequencySemantics key
  }

-- | Playback rate knob (0.25x to 4.0x, default 1.0x).
rateKnob :: String -> Knob
rateKnob key =
  { state: State.rateState 1.0
  , geometry: Geometry.defaultGeometry
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
      { snap = SnapToDefault  -- Snap to 1.0x
      }
  , semantics: Semantics.rateSemantics key
  }

-- | Rotation knob (0-360 degrees, wraps).
rotationKnob :: String -> Knob
rotationKnob key =
  { state: State.rotationState 0.0
  , geometry: Geometry.defaultGeometry
      { arc = arcFull  -- Full 360 degree rotation
      }
  , appearance: Appearance.defaultAppearance
  , behavior: Behavior.defaultBehavior
      { wrapAround = true  -- Can wrap past 360 to 0
      }
  , semantics: Semantics.rotationSemantics key
  }

-- | Hue knob (0-360 degrees, wraps, rainbow arc).
hueKnob :: String -> Knob
hueKnob key =
  { state: State.rotationState 0.0
  , geometry: Geometry.gameGeometry  -- Full rotation, circular
  , appearance: Appearance.defaultAppearance
      { variant = VariantGame
      , valueFill = Appearance.fillNone  -- No value fill, track IS the hue
      }
  , behavior: Behavior.defaultBehavior
      { dragMode = DragCircular
      , wrapAround = true
      }
  , semantics: (Semantics.rotationSemantics key)
      { label = "Hue"
      , purpose = PurposeHue
      }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // layer accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get state layer.
getState :: Knob -> KnobElementState
getState k = k.state

-- | Get geometry layer.
getGeometry :: Knob -> KnobGeometry
getGeometry k = k.geometry

-- | Get appearance layer.
getAppearance :: Knob -> KnobAppearance
getAppearance k = k.appearance

-- | Get behavior layer.
getBehavior :: Knob -> KnobBehavior
getBehavior k = k.behavior

-- | Get semantics layer.
getSemantics :: Knob -> KnobSemantics
getSemantics k = k.semantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // layer modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set state layer.
setState :: KnobElementState -> Knob -> Knob
setState st k = k { state = st }

-- | Set geometry layer.
setGeometry :: KnobGeometry -> Knob -> Knob
setGeometry geo k = k { geometry = geo }

-- | Set appearance layer.
setAppearance :: KnobAppearance -> Knob -> Knob
setAppearance app k = k { appearance = app }

-- | Set behavior layer.
setBehavior :: KnobBehavior -> Knob -> Knob
setBehavior beh k = k { behavior = beh }

-- | Set semantics layer.
setSemantics :: KnobSemantics -> Knob -> Knob
setSemantics sem k = k { semantics = sem }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // convenience accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current value.
getValue :: Knob -> KnobValue
getValue k = State.getValue k.state

-- | Get current angle (value converted to degrees).
getAngle :: Knob -> Degrees
getAngle k = State.getAngle k.state

-- | Get knob UUID5 as string.
getId :: Knob -> String
getId k = knobIdString k.semantics

-- | Is knob disabled?
isDisabled :: Knob -> Boolean
isDisabled k = State.isDisabled k.state

-- | Is knob being dragged?
isDragging :: Knob -> Boolean
isDragging k = State.isDragging k.state

-- | Is this a bipolar knob (center = 0)?
isBipolar :: Knob -> Boolean
isBipolar k = Appearance.isBipolar k.appearance

-- | Does this knob have warning zones?
hasWarningZones :: Knob -> Boolean
hasWarningZones k = Appearance.hasWarningZones k.appearance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // convenience modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current value.
setValue :: KnobValue -> Knob -> Knob
setValue v k = k { state = State.setValue v k.state }

-- | Set disabled state.
setDisabled :: Boolean -> Knob -> Knob
setDisabled d k = k { state = State.setDisabled d k.state }

-- | Reset knob to default value.
resetToDefault :: Knob -> Knob
resetToDefault k = k { state = State.resetToDefault k.state }
