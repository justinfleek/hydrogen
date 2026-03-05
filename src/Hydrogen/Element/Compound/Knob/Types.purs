-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // knob // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Knob Types — Core type definitions for the Knob compound.
-- |
-- | This module defines:
-- | - `KnobVariant` — Visual variant (standard, bipolar, medical, game)
-- | - `DragMode` — Interaction mode (linear-vertical, circular)
-- | - `KnobProps` — Complete property record for knob configuration
-- | - `KnobProp` — Property modifier function type
-- |
-- | ## Design Philosophy
-- |
-- | Knobs are rotational continuous controls — the circular cousin of sliders.
-- | Unlike sliders (linear left-to-right), knobs map VALUE to ANGLE.
-- |
-- | The Knob compound renders the **visual representation** of knob state,
-- | while the Schema.Element.Knob defines the **semantic meaning**.

module Hydrogen.Element.Compound.Knob.Types
  ( -- * Types
    KnobVariant(VariantStandard, VariantBipolar, VariantMedical, VariantGame)
  , DragMode(DragLinearVertical, DragLinearHorizontal, DragCircular)
  , KnobProps
  , KnobProp
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  )

import Data.Maybe (Maybe)

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // knob variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual variant determining knob styling
-- |
-- | - `VariantStandard` — Single-ended value fill (0 to value)
-- | - `VariantBipolar` — Center-out fill (center to value, for pan/balance)
-- | - `VariantMedical` — Safety zone coloring (green/yellow/red)
-- | - `VariantGame` — Glow effects, full visual feedback
data KnobVariant
  = VariantStandard
  | VariantBipolar
  | VariantMedical
  | VariantGame

derive instance eqKnobVariant :: Eq KnobVariant

instance showKnobVariant :: Show KnobVariant where
  show VariantStandard = "standard"
  show VariantBipolar = "bipolar"
  show VariantMedical = "medical"
  show VariantGame = "game"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // drag mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interaction mode for knob manipulation
-- |
-- | - `DragLinearVertical` — DAW style: drag up/down to change value
-- | - `DragLinearHorizontal` — Alternative: drag left/right
-- | - `DragCircular` — Physical knob style: rotate around center
data DragMode
  = DragLinearVertical
  | DragLinearHorizontal
  | DragCircular

derive instance eqDragMode :: Eq DragMode

instance showDragMode :: Show DragMode where
  show DragLinearVertical = "linear-vertical"
  show DragLinearHorizontal = "linear-horizontal"
  show DragCircular = "circular"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // knob props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Knob properties
-- |
-- | All visual properties accept Schema atoms directly.
-- | Use `Maybe` for optional properties that should use defaults.
-- |
-- | ## Property Categories
-- |
-- | **Value Properties**
-- | - `value` — Current value (0.0-1.0 normalized)
-- | - `minVal`, `maxVal` — Display labels only (value is always normalized)
-- | - `disabled` — Interaction state
-- |
-- | **Visual Properties**
-- | - `variant` — Standard, bipolar, medical, game
-- | - `dragMode` — Linear-vertical, linear-horizontal, circular
-- | - `showValue` — Display numeric value
-- | - `showLabel` — Display label text
-- |
-- | **Arc Configuration**
-- | - `arcStartAngle` — Start angle in degrees (default 225 = 7 o'clock)
-- | - `arcEndAngle` — End angle in degrees (default 315 = 5 o'clock)
-- |
-- | **Color Atoms**
-- | - Track, value fill, indicator, center cap, labels
-- |
-- | **Dimension Atoms**
-- | - Size, track width, indicator dimensions
-- |
-- | **Motion Atoms**
-- | - Transition duration for smooth animations
-- |
-- | **Behavior**
-- | - Change handlers and accessibility labels
type KnobProps msg =
  { -- Value state
    value :: Number                              -- ^ Normalized 0.0-1.0
  , minVal :: Number                             -- ^ Display min (label only)
  , maxVal :: Number                             -- ^ Display max (label only)
  , disabled :: Boolean
  
  -- Visual configuration
  , variant :: KnobVariant
  , dragMode :: DragMode
  , showValue :: Boolean                         -- ^ Show numeric value
  , showLabel :: Boolean                         -- ^ Show label text
  , label :: String                              -- ^ Label text
  
  -- Arc configuration (in degrees)
  , arcStartAngle :: Number                      -- ^ Start angle (default 225)
  , arcEndAngle :: Number                        -- ^ End angle (default 315)
  
  -- Color atoms
  , trackColor :: Maybe Color.RGB                -- ^ Unfilled arc
  , valueColor :: Maybe Color.RGB                -- ^ Filled arc (value)
  , indicatorColor :: Maybe Color.RGB            -- ^ Indicator line/dot
  , centerCapColor :: Maybe Color.RGB            -- ^ Center cap fill
  , labelColor :: Maybe Color.RGB                -- ^ Value/label text
  , focusRingColor :: Maybe Color.RGB            -- ^ Focus indication
  
  -- Bipolar-specific colors
  , bipolarPositiveColor :: Maybe Color.RGB      -- ^ Fill for positive values
  , bipolarNegativeColor :: Maybe Color.RGB      -- ^ Fill for negative values
  
  -- Medical-specific colors
  , safeZoneColor :: Maybe Color.RGB             -- ^ Green zone
  , cautionZoneColor :: Maybe Color.RGB          -- ^ Yellow zone
  , dangerZoneColor :: Maybe Color.RGB           -- ^ Red zone
  
  -- Dimension atoms
  , size :: Maybe Device.Pixel                   -- ^ Overall diameter
  , trackWidth :: Maybe Device.Pixel             -- ^ Arc stroke width
  , indicatorLength :: Maybe Device.Pixel        -- ^ Indicator line length
  , indicatorWidth :: Maybe Device.Pixel         -- ^ Indicator stroke width
  , centerCapRadius :: Maybe Device.Pixel        -- ^ Center cap size
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onChange :: Maybe (Number -> msg)            -- ^ Value change handler
  , ariaLabel :: String                          -- ^ Accessibility label
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // knob prop
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property modifier function
-- |
-- | Knob configuration follows the builder pattern:
-- | ```purescript
-- | knob [ value 0.5, trackColor brand.surface, onChange HandleChange ]
-- | ```
-- |
-- | Each `KnobProp` modifies a single field of `KnobProps`.
type KnobProp msg = KnobProps msg -> KnobProps msg
