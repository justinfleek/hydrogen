-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // element // knob // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KnobAppearance — Visual atoms for rotational knob controls.
-- |
-- | ## Design Philosophy
-- |
-- | KnobAppearance describes the 2D SURFACE representation of a knob.
-- | This is the "flat" layer that works with SVG/Canvas rendering.
-- |
-- | For 3D knobs (WebGL/Spatial), these atoms inform the material properties:
-- | - trackFill -> base material color/albedo
-- | - valueFill -> emissive or highlight material
-- | - indicatorFill -> groove/notch color
-- | - glow -> bloom/emissive intensity
-- | - shadow -> ambient occlusion hints
-- |
-- | The actual 3D mesh (square, round, diamond, organic) is defined in
-- | Hydrogen.Schema.Spatial.Mesh and composed separately. This module
-- | provides the WHAT (colors, fills, zones) not the SHAPE (mesh topology).
-- |
-- | ## Warning Zones (Medical Domain)
-- |
-- | Medical knobs have clearly defined visual zones:
-- | - Safe zone: Green arc (normal operating range)
-- | - Caution zone: Yellow arc (elevated, monitor)
-- | - Danger zone: Red arc (requires confirmation)
-- |
-- | ## Bipolar Display (DAW Domain)
-- |
-- | Pan and balance knobs are bipolar (center = 0):
-- | - Center line indicator
-- | - Arc fills from center outward (left OR right, not from min)
-- | - Different colors for positive vs negative
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Fill (Surface.Fill) — Solid, gradient, pattern, noise fills
-- | - RGB/RGBA (Color.RGB) — Verified color channels [0-255]
-- | - Glow (Color.Glow) — Verified glow effects
-- | - LayeredShadow (Elevation.Shadow) — Multi-layer shadows
-- | - Gradient (Color.Gradient) — For arc fills
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Surface.Fill (Fill types)
-- | - Hydrogen.Schema.Color.RGB (color types)
-- | - Hydrogen.Schema.Color.Glow (glow effects)
-- | - Hydrogen.Schema.Color.Gradient (gradient types)
-- | - Hydrogen.Schema.Elevation.Shadow (shadow layers)

module Hydrogen.Schema.Element.Knob.Appearance
  ( -- * Knob Variant
    KnobVariant
      ( VariantDefault
      , VariantMinimal
      , VariantBipolar
      , VariantMedical
      , VariantGame
      , VariantDAW
      , VariantMograph
      )
  
  -- * Warning Zone Configuration
  , ZoneConfig
  , zoneConfigDisabled
  , zoneConfigMedical
  , zoneConfigCustom
  
  -- * Bipolar Configuration
  , BipolarConfig
  , bipolarDisabled
  , bipolarPan
  , bipolarBalance
  
  -- * Knob Appearance Record
  , KnobAppearance
  , defaultAppearance
  , minimalAppearance
  , bipolarAppearance
  , medicalAppearance
  , dawAppearance
  , gameAppearance
  , mographAppearance
  
  -- * Appearance Accessors
  , getVariant
  , getTrackFill
  , getValueFill
  , getIndicatorFill
  , getCenterCapFill
  , getFocusRingColor
  , getGlow
  , getShadow
  , getOpacity
  , getZoneConfig
  , getBipolarConfig
  , isBipolar
  , hasWarningZones
  
  -- * Appearance Modifiers
  , setVariant
  , setTrackFill
  , setValueFill
  , setIndicatorFill
  , setCenterCapFill
  , setFocusRingColor
  , setGlow
  , setShadow
  , setOpacity
  , setZoneConfig
  , setBipolarConfig
  , enableGlow
  , disableGlow
  , disableShadow
  
  -- * Color Presets
  , defaultTrackFill
  , defaultValueFill
  , defaultIndicatorFill
  , medicalSafeFill
  , medicalCautionFill
  , medicalDangerFill
  , bipolarPositiveFill
  , bipolarNegativeFill
  
  -- * Re-exports
  , module Hydrogen.Schema.Surface.Fill
  , module Hydrogen.Schema.Color.RGB
  , module Hydrogen.Schema.Color.Glow
  , module Hydrogen.Schema.Color.Gradient
  , module Hydrogen.Schema.Elevation.Shadow
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  , (==)
  , (&&)
  , (||)
  , (>)
  , (<)
  , (>=)
  , (<=)
  , not
  )

import Prim (Boolean, Int, Number)

import Data.Maybe (Maybe(Just, Nothing))
import Data.Maybe (isJust) as Maybe

import Hydrogen.Schema.Surface.Fill
  ( Fill
  , fillSolid
  , fillGradient
  , fillNone
  )

import Hydrogen.Schema.Color.RGB
  ( RGB
  , RGBA
  , rgb
  , rgba
  )

import Hydrogen.Schema.Color.Glow
  ( Glow
  , glow
  , warmGlow
  , coolGlow
  )

import Hydrogen.Schema.Color.Gradient
  ( Gradient(Linear)
  , LinearGradient
  , ColorStop(ColorStop)
  , colorStop
  , linearGradient
  , linearGradientFromAngle
  )

import Hydrogen.Schema.Elevation.Shadow
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // knob variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Knob visual variant — semantic styles for different domains.
-- |
-- | ## Variants
-- |
-- | - Default: Neutral, general purpose
-- | - Minimal: Low contrast, dense UIs
-- | - Bipolar: Center-zero (pan, balance)
-- | - Medical: Safety zones, high contrast
-- | - Game: Visual effects, glow, particles
-- | - DAW: Compact, monochrome, automation indicators
-- | - Mograph: Keyframe indicators, expressions
data KnobVariant
  = VariantDefault   -- ^ General purpose knob
  | VariantMinimal   -- ^ Subtle, low-contrast
  | VariantBipolar   -- ^ Center-zero (pan, balance)
  | VariantMedical   -- ^ Safety zones, high contrast
  | VariantGame      -- ^ Visual effects, glow
  | VariantDAW       -- ^ Compact, automation-aware
  | VariantMograph   -- ^ Keyframe/expression indicators

derive instance eqKnobVariant :: Eq KnobVariant
derive instance ordKnobVariant :: Ord KnobVariant

instance showKnobVariant :: Show KnobVariant where
  show VariantDefault = "default"
  show VariantMinimal = "minimal"
  show VariantBipolar = "bipolar"
  show VariantMedical = "medical"
  show VariantGame = "game"
  show VariantDAW = "daw"
  show VariantMograph = "mograph"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // warning zone config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warning zone configuration for medical knobs.
-- |
-- | Zones are defined by threshold percentages:
-- | - 0% to cautionStart: Safe (green)
-- | - cautionStart to dangerStart: Caution (yellow)
-- | - dangerStart to 100%: Danger (red)
type ZoneConfig =
  { enabled :: Boolean          -- ^ Are warning zones active?
  , cautionStart :: Number      -- ^ % where caution zone begins
  , dangerStart :: Number       -- ^ % where danger zone begins
  , safeFill :: Fill            -- ^ Safe zone fill (green)
  , cautionFill :: Fill         -- ^ Caution zone fill (yellow)
  , dangerFill :: Fill          -- ^ Danger zone fill (red)
  }

-- | Warning zones disabled.
zoneConfigDisabled :: ZoneConfig
zoneConfigDisabled =
  { enabled: false
  , cautionStart: 70.0
  , dangerStart: 90.0
  , safeFill: fillNone
  , cautionFill: fillNone
  , dangerFill: fillNone
  }

-- | Medical warning zones (0-30 safe, 30-60 caution, 60-100 danger).
zoneConfigMedical :: ZoneConfig
zoneConfigMedical =
  { enabled: true
  , cautionStart: 30.0
  , dangerStart: 60.0
  , safeFill: medicalSafeFill
  , cautionFill: medicalCautionFill
  , dangerFill: medicalDangerFill
  }

-- | Custom warning zone configuration.
zoneConfigCustom :: Number -> Number -> ZoneConfig
zoneConfigCustom caution danger =
  { enabled: true
  , cautionStart: Bounded.clampNumber 0.0 100.0 caution
  , dangerStart: Bounded.clampNumber caution 100.0 danger
  , safeFill: medicalSafeFill
  , cautionFill: medicalCautionFill
  , dangerFill: medicalDangerFill
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bipolar config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bipolar display configuration for center-zero knobs.
-- |
-- | Bipolar knobs (pan, balance) display differently:
-- | - Arc fills from CENTER outward (not from min)
-- | - Positive values fill clockwise (right)
-- | - Negative values fill counter-clockwise (left)
-- | - Center has a visible indicator line
type BipolarConfig =
  { enabled :: Boolean          -- ^ Is bipolar display active?
  , positiveFill :: Fill        -- ^ Fill for positive values (right)
  , negativeFill :: Fill        -- ^ Fill for negative values (left)
  , centerIndicator :: Boolean  -- ^ Show center line indicator?
  , centerWidth :: Number       -- ^ Width of center indicator (px)
  }

-- | Bipolar display disabled (unipolar knob).
bipolarDisabled :: BipolarConfig
bipolarDisabled =
  { enabled: false
  , positiveFill: fillNone
  , negativeFill: fillNone
  , centerIndicator: false
  , centerWidth: 2.0
  }

-- | Pan knob bipolar config (left = blue, right = orange).
bipolarPan :: BipolarConfig
bipolarPan =
  { enabled: true
  , positiveFill: bipolarPositiveFill    -- Orange for right
  , negativeFill: bipolarNegativeFill    -- Blue for left
  , centerIndicator: true
  , centerWidth: 2.0
  }

-- | Balance knob bipolar config (same as pan).
bipolarBalance :: BipolarConfig
bipolarBalance = bipolarPan

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default track fill (gray-300).
defaultTrackFill :: Fill
defaultTrackFill = fillSolid (rgb 209 213 219)

-- | Default value arc fill (blue-500).
defaultValueFill :: Fill
defaultValueFill = fillSolid (rgb 59 130 246)

-- | Default indicator fill (white).
defaultIndicatorFill :: Fill
defaultIndicatorFill = fillSolid (rgb 255 255 255)

-- | Default center cap fill (gray-100).
defaultCenterCapFill :: Fill
defaultCenterCapFill = fillSolid (rgb 243 244 246)

-- | Medical safe zone fill (green-500).
medicalSafeFill :: Fill
medicalSafeFill = fillSolid (rgb 34 197 94)

-- | Medical caution zone fill (yellow-500).
medicalCautionFill :: Fill
medicalCautionFill = fillSolid (rgb 234 179 8)

-- | Medical danger zone fill (red-500).
medicalDangerFill :: Fill
medicalDangerFill = fillSolid (rgb 239 68 68)

-- | Bipolar positive fill (orange-500, right side).
bipolarPositiveFill :: Fill
bipolarPositiveFill = fillSolid (rgb 249 115 22)

-- | Bipolar negative fill (blue-500, left side).
bipolarNegativeFill :: Fill
bipolarNegativeFill = fillSolid (rgb 59 130 246)

-- | DAW track fill (gray-700, dark theme).
dawTrackFill :: Fill
dawTrackFill = fillSolid (rgb 55 65 81)

-- | DAW value fill (cyan-400).
dawValueFill :: Fill
dawValueFill = fillSolid (rgb 34 211 238)

-- | Game glow fill (purple-500 with gradient).
gameGlowFill :: Fill
gameGlowFill = fillGradient (Linear (linearGradientFromAngle 90.0
  [ colorStop (rgb 168 85 247) 0.0   -- Purple-500
  , colorStop (rgb 236 72 153) 1.0   -- Pink-500
  ]))

-- | Default focus ring color (blue-400).
defaultFocusRingColor :: RGB
defaultFocusRingColor = rgb 96 165 250

-- | Default knob shadow — subtle elevation.
defaultKnobShadow :: LayeredShadow
defaultKnobShadow = layered
  [ boxShadow
      { offsetX: 0.0
      , offsetY: 2.0
      , blur: 4.0
      , spread: 0.0
      , color: rgba 0 0 0 38     -- ~15% opacity
      , inset: false
      }
  , boxShadow
      { offsetX: 0.0
      , offsetY: 1.0
      , blur: 2.0
      , spread: 0.0
      , color: rgba 0 0 0 26     -- ~10% opacity
      , inset: false
      }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // knob appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete knob appearance — all visual properties.
-- |
-- | This describes the 2D surface representation. For 3D rendering,
-- | these values inform material properties in the Spatial layer.
type KnobAppearance =
  { -- Variant
    variant :: KnobVariant          -- ^ Visual style variant
    -- Arc fills
  , trackFill :: Fill               -- ^ Background arc (the full range)
  , valueFill :: Fill               -- ^ Filled arc showing current value
    -- Indicator
  , indicatorFill :: Fill           -- ^ Pointer/notch fill
  , indicatorBorderWidth :: Number  -- ^ Border around indicator
  , indicatorBorderColor :: Maybe RGBA
    -- Center cap
  , centerCapFill :: Fill           -- ^ Center circle fill
  , centerCapBorderWidth :: Number
  , centerCapBorderColor :: Maybe RGBA
    -- Focus
  , focusRingColor :: RGB           -- ^ Focus ring color
  , focusRingWidth :: Number        -- ^ Focus ring width (bounded 0-10)
    -- Effects
  , glow :: Maybe Glow              -- ^ Optional glow effect (game)
  , shadow :: LayeredShadow         -- ^ Shadow layers
    -- Opacity
  , opacity :: Number               -- ^ Overall opacity (bounded 0-1)
  , disabledOpacity :: Number       -- ^ Opacity when disabled (bounded 0-1)
    -- Warning zones (medical)
  , zones :: ZoneConfig             -- ^ Safety zone configuration
    -- Bipolar display
  , bipolar :: BipolarConfig        -- ^ Center-zero display config
    -- Tick marks
  , showTickMarks :: Boolean        -- ^ Show tick marks around arc
  , tickMarkCount :: Int            -- ^ Number of tick marks
  , tickMarkColor :: RGB            -- ^ Tick mark color
  }

-- | Default knob appearance.
defaultAppearance :: KnobAppearance
defaultAppearance =
  { variant: VariantDefault
  , trackFill: defaultTrackFill
  , valueFill: defaultValueFill
  , indicatorFill: defaultIndicatorFill
  , indicatorBorderWidth: 0.0
  , indicatorBorderColor: Nothing
  , centerCapFill: defaultCenterCapFill
  , centerCapBorderWidth: 0.0
  , centerCapBorderColor: Nothing
  , focusRingColor: defaultFocusRingColor
  , focusRingWidth: 2.0
  , glow: Nothing
  , shadow: defaultKnobShadow
  , opacity: 1.0
  , disabledOpacity: 0.5
  , zones: zoneConfigDisabled
  , bipolar: bipolarDisabled
  , showTickMarks: false
  , tickMarkCount: 11
  , tickMarkColor: rgb 156 163 175  -- gray-400
  }

-- | Minimal appearance (low contrast, no shadow).
minimalAppearance :: KnobAppearance
minimalAppearance = defaultAppearance
  { variant = VariantMinimal
  , trackFill = fillSolid (rgb 229 231 235)   -- gray-200
  , valueFill = fillSolid (rgb 156 163 175)   -- gray-400
  , indicatorFill = fillSolid (rgb 107 114 128)  -- gray-500
  , shadow = noShadow
  }

-- | Bipolar appearance (pan/balance knobs).
bipolarAppearance :: KnobAppearance
bipolarAppearance = defaultAppearance
  { variant = VariantBipolar
  , valueFill = fillNone              -- No single value fill
  , bipolar = bipolarPan
  }

-- | Medical appearance (safety zones, high contrast).
medicalAppearance :: KnobAppearance
medicalAppearance = defaultAppearance
  { variant = VariantMedical
  , trackFill = fillSolid (rgb 243 244 246)   -- gray-100
  , valueFill = fillNone                       -- Zones handle fills
  , indicatorFill = fillSolid (rgb 17 24 39)  -- gray-900 (high contrast)
  , indicatorBorderWidth = 2.0
  , indicatorBorderColor = Just (rgba 255 255 255 255)
  , centerCapFill = fillSolid (rgb 255 255 255)
  , centerCapBorderWidth = 2.0
  , centerCapBorderColor = Just (rgba 17 24 39 255)
  , zones = zoneConfigMedical
  , showTickMarks = true
  , tickMarkCount = 11
  , tickMarkColor = rgb 17 24 39              -- gray-900
  }

-- | DAW appearance (compact, dark theme, automation-aware).
dawAppearance :: KnobAppearance
dawAppearance = defaultAppearance
  { variant = VariantDAW
  , trackFill = dawTrackFill
  , valueFill = dawValueFill
  , indicatorFill = fillSolid (rgb 255 255 255)
  , centerCapFill = fillSolid (rgb 31 41 55)  -- gray-800
  , shadow = noShadow                          -- Flat design
  , showTickMarks = false
  }

-- | Game appearance (glow effects, vibrant colors).
gameAppearance :: KnobAppearance
gameAppearance = defaultAppearance
  { variant = VariantGame
  , trackFill = fillSolid (rgb 31 41 55)      -- gray-800
  , valueFill = gameGlowFill
  , indicatorFill = fillSolid (rgb 255 255 255)
  , centerCapFill = fillSolid (rgb 17 24 39)  -- gray-900
  , glow = Just (coolGlow 200.0 20.0)         -- Strong glow
  }

-- | Motion graphics appearance (keyframe indicators).
mographAppearance :: KnobAppearance
mographAppearance = defaultAppearance
  { variant = VariantMograph
  , trackFill = fillSolid (rgb 55 65 81)      -- gray-700
  , valueFill = fillSolid (rgb 251 191 36)    -- amber-400 (AE style)
  , indicatorFill = fillSolid (rgb 255 255 255)
  , centerCapFill = fillSolid (rgb 31 41 55)  -- gray-800
  , shadow = noShadow
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get variant.
getVariant :: KnobAppearance -> KnobVariant
getVariant a = a.variant

-- | Get track fill.
getTrackFill :: KnobAppearance -> Fill
getTrackFill a = a.trackFill

-- | Get value arc fill.
getValueFill :: KnobAppearance -> Fill
getValueFill a = a.valueFill

-- | Get indicator fill.
getIndicatorFill :: KnobAppearance -> Fill
getIndicatorFill a = a.indicatorFill

-- | Get center cap fill.
getCenterCapFill :: KnobAppearance -> Fill
getCenterCapFill a = a.centerCapFill

-- | Get focus ring color.
getFocusRingColor :: KnobAppearance -> RGB
getFocusRingColor a = a.focusRingColor

-- | Get glow effect.
getGlow :: KnobAppearance -> Maybe Glow
getGlow a = a.glow

-- | Get shadow layers.
getShadow :: KnobAppearance -> LayeredShadow
getShadow a = a.shadow

-- | Get opacity (bounded 0-1).
getOpacity :: KnobAppearance -> Number
getOpacity a = Bounded.clampNumber 0.0 1.0 a.opacity

-- | Get zone configuration.
getZoneConfig :: KnobAppearance -> ZoneConfig
getZoneConfig a = a.zones

-- | Get bipolar configuration.
getBipolarConfig :: KnobAppearance -> BipolarConfig
getBipolarConfig a = a.bipolar

-- | Is this a bipolar display?
isBipolar :: KnobAppearance -> Boolean
isBipolar a = a.bipolar.enabled

-- | Are warning zones enabled?
hasWarningZones :: KnobAppearance -> Boolean
hasWarningZones a = a.zones.enabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set variant.
setVariant :: KnobVariant -> KnobAppearance -> KnobAppearance
setVariant v a = a { variant = v }

-- | Set track fill.
setTrackFill :: Fill -> KnobAppearance -> KnobAppearance
setTrackFill f a = a { trackFill = f }

-- | Set value arc fill.
setValueFill :: Fill -> KnobAppearance -> KnobAppearance
setValueFill f a = a { valueFill = f }

-- | Set indicator fill.
setIndicatorFill :: Fill -> KnobAppearance -> KnobAppearance
setIndicatorFill f a = a { indicatorFill = f }

-- | Set center cap fill.
setCenterCapFill :: Fill -> KnobAppearance -> KnobAppearance
setCenterCapFill f a = a { centerCapFill = f }

-- | Set focus ring color.
setFocusRingColor :: RGB -> KnobAppearance -> KnobAppearance
setFocusRingColor c a = a { focusRingColor = c }

-- | Set glow effect.
setGlow :: Maybe Glow -> KnobAppearance -> KnobAppearance
setGlow g a = a { glow = g }

-- | Set shadow layers.
setShadow :: LayeredShadow -> KnobAppearance -> KnobAppearance
setShadow s a = a { shadow = s }

-- | Set opacity (automatically bounded 0-1).
setOpacity :: Number -> KnobAppearance -> KnobAppearance
setOpacity o a = a { opacity = Bounded.clampNumber 0.0 1.0 o }

-- | Set zone configuration.
setZoneConfig :: ZoneConfig -> KnobAppearance -> KnobAppearance
setZoneConfig z a = a { zones = z }

-- | Set bipolar configuration.
setBipolarConfig :: BipolarConfig -> KnobAppearance -> KnobAppearance
setBipolarConfig b a = a { bipolar = b }

-- | Enable glow with default cool glow.
enableGlow :: KnobAppearance -> KnobAppearance
enableGlow a = a { glow = Just (coolGlow 150.0 15.0) }

-- | Disable glow.
disableGlow :: KnobAppearance -> KnobAppearance
disableGlow a = a { glow = Nothing }

-- | Disable shadow.
disableShadow :: KnobAppearance -> KnobAppearance
disableShadow a = a { shadow = noShadow }
