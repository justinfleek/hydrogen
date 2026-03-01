-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // brush // colordynamics // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Dynamics Types — ADTs for color source and variation control.
-- |
-- | ## Design Philosophy
-- |
-- | Color dynamics control how brush color changes during a stroke. Unlike
-- | static color, dynamic color responds to input (pressure, tilt, time) or
-- | varies randomly per dab. This creates rich, expressive marks that evoke
-- | traditional media where pigment naturally varies.
-- |
-- | ## Color Source
-- |
-- | Where does the brush get its color?
-- |
-- | - **Foreground**: Single selected color (most common)
-- | - **Background**: Secondary color
-- | - **ForegroundBackground**: Blend between FG and BG based on input
-- | - **Gradient**: Sample from a gradient spectrum
-- | - **ColorSet**: Random selection from a palette
-- | - **Canvas**: Pick up color from existing paint (wet mixing)
-- | - **Image**: Sample from a reference image
-- |
-- | ## Application Timing
-- |
-- | When does color change?
-- |
-- | - **PerStroke**: Color set once at stroke start
-- | - **PerDab**: Each dab gets fresh randomization
-- | - **Continuous**: Smooth interpolation along stroke
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.ColorDynamics.Types
  ( -- * ColorSource ADT
    ColorSource
      ( ForegroundColor
      , BackgroundColor
      , ForegroundBackground
      , GradientSource
      , ColorSetSource
      , CanvasPickup
      , ImageSource
      )
  , allColorSources
  , colorSourceDescription
  , isForegroundBased
  , isGradientBased
  , requiresExternalSource
  
  -- * ColorApplication ADT
  , ColorApplication
      ( PerStroke
      , PerDab
      , Continuous
      )
  , allColorApplications
  , colorApplicationDescription
  , isPerDab
  
  -- * ColorControl ADT
  , ColorControl
      ( ControlOff
      , ControlPressure
      , ControlTilt
      , ControlVelocity
      , ControlStylusWheel
      , ControlStrokeDistance
      , ControlStrokeTime
      , ControlRandom
      )
  , allColorControls
  , colorControlDescription
  , isInputBased
  , isComputedControl
  
  -- * Debug & Serialization Helpers
  , colorSourceDebugInfo
  , colorSourceToId
  , sameColorSourceKind
  , colorApplicationDebugInfo
  , colorApplicationToId
  , colorControlDebugInfo
  , colorControlToId
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source from which brush color is derived.
-- |
-- | Determines the origin of color used for each brush dab.
-- | Different sources enable different creative workflows.
data ColorSource
  = ForegroundColor        -- ^ Single foreground color (most common)
  | BackgroundColor        -- ^ Single background color
  | ForegroundBackground   -- ^ Interpolate between FG and BG
  | GradientSource         -- ^ Sample from gradient spectrum
  | ColorSetSource         -- ^ Random selection from palette
  | CanvasPickup           -- ^ Pick up color from canvas (wet mixing)
  | ImageSource            -- ^ Sample from reference image

derive instance eqColorSource :: Eq ColorSource
derive instance ordColorSource :: Ord ColorSource

instance showColorSource :: Show ColorSource where
  show ForegroundColor = "(ColorSource ForegroundColor)"
  show BackgroundColor = "(ColorSource BackgroundColor)"
  show ForegroundBackground = "(ColorSource ForegroundBackground)"
  show GradientSource = "(ColorSource GradientSource)"
  show ColorSetSource = "(ColorSource ColorSetSource)"
  show CanvasPickup = "(ColorSource CanvasPickup)"
  show ImageSource = "(ColorSource ImageSource)"

-- | All color source variants for enumeration.
allColorSources :: Array ColorSource
allColorSources =
  [ ForegroundColor
  , BackgroundColor
  , ForegroundBackground
  , GradientSource
  , ColorSetSource
  , CanvasPickup
  , ImageSource
  ]

-- | Human-readable description of each color source.
colorSourceDescription :: ColorSource -> String
colorSourceDescription ForegroundColor = 
  "Single foreground color, consistent throughout stroke"
colorSourceDescription BackgroundColor = 
  "Single background color, for erasing to BG or two-tone effects"
colorSourceDescription ForegroundBackground = 
  "Blend between foreground and background based on pressure/tilt/time"
colorSourceDescription GradientSource = 
  "Sample colors from a gradient spectrum along the stroke"
colorSourceDescription ColorSetSource = 
  "Random selection from a defined color palette"
colorSourceDescription CanvasPickup = 
  "Pick up existing color from canvas, simulating wet paint mixing"
colorSourceDescription ImageSource = 
  "Sample colors from a reference image based on brush position"

-- | Check if source uses foreground/background colors.
isForegroundBased :: ColorSource -> Boolean
isForegroundBased ForegroundColor = true
isForegroundBased BackgroundColor = true
isForegroundBased ForegroundBackground = true
isForegroundBased _ = false

-- | Check if source uses gradient sampling.
isGradientBased :: ColorSource -> Boolean
isGradientBased GradientSource = true
isGradientBased _ = false

-- | Check if source requires external data (canvas, image, palette).
requiresExternalSource :: ColorSource -> Boolean
requiresExternalSource CanvasPickup = true
requiresExternalSource ImageSource = true
requiresExternalSource ColorSetSource = true
requiresExternalSource _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // color application
-- ═════════════════════════════════════════════════════════════════════════════

-- | When color changes are applied during a stroke.
-- |
-- | Controls the granularity of color variation.
data ColorApplication
  = PerStroke    -- ^ Color set once at stroke start
  | PerDab       -- ^ Each dab gets fresh color (jitter/random)
  | Continuous   -- ^ Smooth interpolation along stroke path

derive instance eqColorApplication :: Eq ColorApplication
derive instance ordColorApplication :: Ord ColorApplication

instance showColorApplication :: Show ColorApplication where
  show PerStroke = "(ColorApplication PerStroke)"
  show PerDab = "(ColorApplication PerDab)"
  show Continuous = "(ColorApplication Continuous)"

-- | All color application variants.
allColorApplications :: Array ColorApplication
allColorApplications =
  [ PerStroke
  , PerDab
  , Continuous
  ]

-- | Human-readable description of each application mode.
colorApplicationDescription :: ColorApplication -> String
colorApplicationDescription PerStroke = 
  "Color determined once at stroke start, consistent throughout"
colorApplicationDescription PerDab = 
  "Each dab evaluates color independently (enables jitter)"
colorApplicationDescription Continuous = 
  "Smooth color interpolation along stroke path"

-- | Check if application mode evaluates per dab.
isPerDab :: ColorApplication -> Boolean
isPerDab PerDab = true
isPerDab _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color control
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input or computation that controls color parameters.
-- |
-- | Maps external input or computed values to color modulation.
-- | Multiple controls can affect different color properties.
data ColorControl
  = ControlOff           -- ^ No dynamic control (constant)
  | ControlPressure      -- ^ Pen pressure modulates color
  | ControlTilt          -- ^ Pen tilt angle modulates color
  | ControlVelocity      -- ^ Stroke speed modulates color
  | ControlStylusWheel   -- ^ Hardware wheel/dial control
  | ControlStrokeDistance -- ^ Distance along stroke path
  | ControlStrokeTime    -- ^ Time elapsed during stroke
  | ControlRandom        -- ^ Per-dab random variation

derive instance eqColorControl :: Eq ColorControl
derive instance ordColorControl :: Ord ColorControl

instance showColorControl :: Show ColorControl where
  show ControlOff = "(ColorControl Off)"
  show ControlPressure = "(ColorControl Pressure)"
  show ControlTilt = "(ColorControl Tilt)"
  show ControlVelocity = "(ColorControl Velocity)"
  show ControlStylusWheel = "(ColorControl StylusWheel)"
  show ControlStrokeDistance = "(ColorControl StrokeDistance)"
  show ControlStrokeTime = "(ColorControl StrokeTime)"
  show ControlRandom = "(ColorControl Random)"

-- | All color control variants.
allColorControls :: Array ColorControl
allColorControls =
  [ ControlOff
  , ControlPressure
  , ControlTilt
  , ControlVelocity
  , ControlStylusWheel
  , ControlStrokeDistance
  , ControlStrokeTime
  , ControlRandom
  ]

-- | Human-readable description of each control source.
colorControlDescription :: ColorControl -> String
colorControlDescription ControlOff = 
  "No dynamic control, color remains constant"
colorControlDescription ControlPressure = 
  "Pen pressure modulates color (light=one color, heavy=another)"
colorControlDescription ControlTilt = 
  "Pen tilt angle modulates color"
colorControlDescription ControlVelocity = 
  "Stroke speed modulates color (slow=one color, fast=another)"
colorControlDescription ControlStylusWheel = 
  "Hardware stylus wheel or dial directly controls color"
colorControlDescription ControlStrokeDistance = 
  "Distance traveled along stroke controls color (gradient along path)"
colorControlDescription ControlStrokeTime = 
  "Time elapsed during stroke controls color (fade over time)"
colorControlDescription ControlRandom = 
  "Random per-dab color variation within bounds"

-- | Check if control is based on hardware input.
isInputBased :: ColorControl -> Boolean
isInputBased ControlPressure = true
isInputBased ControlTilt = true
isInputBased ControlVelocity = true
isInputBased ControlStylusWheel = true
isInputBased _ = false

-- | Check if control is computed from stroke state.
isComputedControl :: ColorControl -> Boolean
isComputedControl ControlStrokeDistance = true
isComputedControl ControlStrokeTime = true
isComputedControl ControlRandom = true
isComputedControl _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for color source.
colorSourceDebugInfo :: ColorSource -> String
colorSourceDebugInfo src =
  "ColorSource: " <> colorSourceToId src <> " — " <> colorSourceDescription src

-- | Convert color source to string ID for serialization.
colorSourceToId :: ColorSource -> String
colorSourceToId ForegroundColor = "foreground"
colorSourceToId BackgroundColor = "background"
colorSourceToId ForegroundBackground = "fg-bg"
colorSourceToId GradientSource = "gradient"
colorSourceToId ColorSetSource = "color-set"
colorSourceToId CanvasPickup = "canvas"
colorSourceToId ImageSource = "image"

-- | Check if two color sources are the same kind.
sameColorSourceKind :: ColorSource -> ColorSource -> Boolean
sameColorSourceKind a b = colorSourceToId a == colorSourceToId b

-- | Generate debug info for color application.
colorApplicationDebugInfo :: ColorApplication -> String
colorApplicationDebugInfo app =
  "ColorApplication: " <> colorApplicationToId app <> " — " <> colorApplicationDescription app

-- | Convert color application to string ID for serialization.
colorApplicationToId :: ColorApplication -> String
colorApplicationToId PerStroke = "per-stroke"
colorApplicationToId PerDab = "per-dab"
colorApplicationToId Continuous = "continuous"

-- | Generate debug info for color control.
colorControlDebugInfo :: ColorControl -> String
colorControlDebugInfo ctrl =
  "ColorControl: " <> colorControlToId ctrl <> " — " <> colorControlDescription ctrl

-- | Convert color control to string ID for serialization.
colorControlToId :: ColorControl -> String
colorControlToId ControlOff = "off"
colorControlToId ControlPressure = "pressure"
colorControlToId ControlTilt = "tilt"
colorControlToId ControlVelocity = "velocity"
colorControlToId ControlStylusWheel = "stylus-wheel"
colorControlToId ControlStrokeDistance = "stroke-distance"
colorControlToId ControlStrokeTime = "stroke-time"
colorControlToId ControlRandom = "random"
