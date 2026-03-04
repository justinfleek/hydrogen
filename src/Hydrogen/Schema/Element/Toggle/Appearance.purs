-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // element // toggle // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ToggleAppearance — Visual atoms for toggle/switch surface and effects.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Fill (Surface.Fill) — Solid, gradient, pattern, noise fills
-- | - RGB/RGBA (Color.RGB) — Verified color channels [0-255]
-- | - Glow (Color.Glow) — Verified glow effects
-- | - LayeredShadow (Elevation.Shadow) — Multi-layer shadows
-- | - Opacity (Color.Opacity) — Verified opacity [0.0-1.0]
-- |
-- | ## Toggle Appearance Model
-- |
-- | A toggle has distinct visual states:
-- | - **Off state**: Track and thumb colors when unchecked
-- | - **On state**: Track and thumb colors when checked
-- | - **Hover state**: Colors when pointer is over toggle
-- | - **Focus state**: Focus ring when keyboard-focused
-- | - **Disabled state**: Reduced opacity, no interaction
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Surface.Fill (Fill, fillSolid)
-- | - Hydrogen.Schema.Color.RGB (RGB, RGBA)
-- | - Hydrogen.Schema.Color.Glow (Glow)
-- | - Hydrogen.Schema.Elevation.Shadow (LayeredShadow)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)

module Hydrogen.Schema.Element.Toggle.Appearance
  ( -- * Toggle Variant
    ToggleVariant
      ( VariantDefault
      , VariantMinimal
      , VariantFilled
      , VariantOutlined
      , VariantIOS
      , VariantMaterial
      )
  
  -- * Toggle Appearance Record
  , ToggleAppearance
  , defaultAppearance
  , minimalAppearance
  , iosAppearance
  , materialAppearance
  , outlinedAppearance
  
  -- * Appearance Accessors
  , getTrackOffFill
  , getTrackOnFill
  , getThumbFill
  , getFocusRingColor
  , getGlow
  , getShadow
  , getOpacity
  
  -- * Appearance Modifiers
  , setTrackOffFill
  , setTrackOnFill
  , setThumbFill
  , setFocusRingColor
  , setGlow
  , setShadow
  , setOpacity
  , enableGlow
  , disableShadow
  
  -- * Color Presets
  , iosGreenFill
  , iosGrayFill
  , materialPrimaryFill
  , materialSurfaceFill
  , whiteThumbFill
  
  -- * Re-exports
  , module Hydrogen.Schema.Surface.Fill
  , module Hydrogen.Schema.Color.RGB
  , module Hydrogen.Schema.Color.Glow
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
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Surface.Fill
  ( Fill
  , fillSolid
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

import Hydrogen.Schema.Elevation.Shadow
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // toggle variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle visual variant — platform-inspired visual styles.
-- |
-- | ## Variants
-- |
-- | - Default: Neutral gray/blue, works everywhere
-- | - Minimal: Subtle, low-contrast for dense UIs
-- | - Filled: High-contrast solid fills
-- | - Outlined: Border-only style
-- | - iOS: Apple HIG style (green on, gray off)
-- | - Material: Material Design 3 style
data ToggleVariant
  = VariantDefault     -- ^ Neutral style
  | VariantMinimal     -- ^ Subtle, low-contrast
  | VariantFilled      -- ^ High-contrast solid
  | VariantOutlined    -- ^ Border-only
  | VariantIOS         -- ^ iOS-style (green/gray)
  | VariantMaterial    -- ^ Material Design 3

derive instance eqToggleVariant :: Eq ToggleVariant
derive instance ordToggleVariant :: Ord ToggleVariant

instance showToggleVariant :: Show ToggleVariant where
  show VariantDefault = "default"
  show VariantMinimal = "minimal"
  show VariantFilled = "filled"
  show VariantOutlined = "outlined"
  show VariantIOS = "ios"
  show VariantMaterial = "material"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | iOS green on-state (rgb 52 199 89)
iosGreenFill :: Fill
iosGreenFill = fillSolid (rgb 52 199 89)

-- | iOS gray off-state (rgb 142 142 147)
iosGrayFill :: Fill
iosGrayFill = fillSolid (rgb 142 142 147)

-- | Material primary color (blue-600)
materialPrimaryFill :: Fill
materialPrimaryFill = fillSolid (rgb 25 118 210)

-- | Material surface color (gray-200)
materialSurfaceFill :: Fill
materialSurfaceFill = fillSolid (rgb 189 189 189)

-- | White thumb fill
whiteThumbFill :: Fill
whiteThumbFill = fillSolid (rgb 255 255 255)

-- | Default track off color (gray-300)
defaultTrackOffFill :: Fill
defaultTrackOffFill = fillSolid (rgb 209 213 219)

-- | Default track on color (blue-500)
defaultTrackOnFill :: Fill
defaultTrackOnFill = fillSolid (rgb 59 130 246)

-- | Default focus ring color (blue-400)
defaultFocusRingColor :: RGB
defaultFocusRingColor = rgb 96 165 250

-- | Default thumb shadow — subtle elevation for toggle thumb.
-- |
-- | Two-layer shadow mimicking Material/iOS toggle thumb:
-- | - Layer 1: Soft ambient shadow (0, 1px, 3px blur)
-- | - Layer 2: Key light shadow (0, 2px, 4px blur)
defaultThumbShadow :: LayeredShadow
defaultThumbShadow = layered
  [ boxShadow
      { offsetX: 0.0
      , offsetY: 1.0
      , blur: 3.0
      , spread: 0.0
      , color: rgba 0 0 0 51    -- ~20% opacity
      , inset: false
      }
  , boxShadow
      { offsetX: 0.0
      , offsetY: 2.0
      , blur: 4.0
      , spread: -1.0
      , color: rgba 0 0 0 26    -- ~10% opacity
      , inset: false
      }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // toggle appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete toggle appearance — all visual properties.
-- |
-- | ## Verified Bounded Types
-- |
-- | - All fills via Fill (verified color channels)
-- | - opacity: bounded [0.0-1.0]
-- | - focusRingWidth: bounded [0-10]
-- | - shadows via LayeredShadow
-- | - glow via Glow
-- |
-- | ## State-Based Colors
-- |
-- | The toggle has different colors for:
-- | - trackOffFill: Track color when off
-- | - trackOnFill: Track color when on
-- | - thumbFill: Thumb color (typically white)
type ToggleAppearance =
  { -- Variant
    variant :: ToggleVariant          -- ^ Visual style variant
    -- Track fills
  , trackOffFill :: Fill              -- ^ Track color when off
  , trackOnFill :: Fill               -- ^ Track color when on
  , trackBorderWidth :: Number        -- ^ Track border width (bounded 0-10)
  , trackBorderColor :: Maybe RGBA    -- ^ Track border color
    -- Thumb fills
  , thumbFill :: Fill                 -- ^ Thumb fill color
  , thumbBorderWidth :: Number        -- ^ Thumb border width (bounded 0-10)
  , thumbBorderColor :: Maybe RGBA    -- ^ Thumb border color
    -- Focus
  , focusRingColor :: RGB             -- ^ Focus ring color
  , focusRingWidth :: Number          -- ^ Focus ring width (bounded 0-10)
    -- Effects
  , glow :: Maybe Glow                -- ^ Optional glow effect
  , shadow :: LayeredShadow           -- ^ Shadow layers
    -- Opacity
  , opacity :: Number                 -- ^ Overall opacity (bounded 0-1)
  , disabledOpacity :: Number         -- ^ Opacity when disabled (bounded 0-1)
  }

-- | Default toggle appearance.
-- |
-- | Gray track off, blue track on, white thumb, no glow.
defaultAppearance :: ToggleAppearance
defaultAppearance =
  { variant: VariantDefault
  , trackOffFill: defaultTrackOffFill
  , trackOnFill: defaultTrackOnFill
  , trackBorderWidth: 0.0
  , trackBorderColor: Nothing
  , thumbFill: whiteThumbFill
  , thumbBorderWidth: 0.0
  , thumbBorderColor: Nothing
  , focusRingColor: defaultFocusRingColor
  , focusRingWidth: 2.0
  , glow: Nothing
  , shadow: defaultThumbShadow
  , opacity: 1.0
  , disabledOpacity: 0.5
  }

-- | Minimal toggle appearance.
-- |
-- | Subtle colors, no shadow.
minimalAppearance :: ToggleAppearance
minimalAppearance = defaultAppearance
  { variant = VariantMinimal
  , trackOffFill = fillSolid (rgb 229 231 235)   -- gray-200
  , trackOnFill = fillSolid (rgb 156 163 175)    -- gray-400
  , shadow = noShadow
  }

-- | iOS-style toggle appearance.
-- |
-- | Green on, gray off, white thumb, subtle shadow.
iosAppearance :: ToggleAppearance
iosAppearance = defaultAppearance
  { variant = VariantIOS
  , trackOffFill = iosGrayFill
  , trackOnFill = iosGreenFill
  , thumbFill = whiteThumbFill
  , shadow = defaultThumbShadow
  }

-- | Material Design 3 toggle appearance.
-- |
-- | Primary color on, surface off, white thumb.
materialAppearance :: ToggleAppearance
materialAppearance = defaultAppearance
  { variant = VariantMaterial
  , trackOffFill = materialSurfaceFill
  , trackOnFill = materialPrimaryFill
  , thumbFill = whiteThumbFill
  }

-- | Outlined toggle appearance.
-- |
-- | Transparent track with border, no shadow.
outlinedAppearance :: ToggleAppearance
outlinedAppearance = defaultAppearance
  { variant = VariantOutlined
  , trackOffFill = fillNone
  , trackOnFill = fillNone
  , trackBorderWidth = 2.0
  , trackBorderColor = Just (rgba 107 114 128 255)  -- gray-500
  , thumbFill = fillSolid (rgb 107 114 128)
  , shadow = noShadow
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get track fill when off.
getTrackOffFill :: ToggleAppearance -> Fill
getTrackOffFill a = a.trackOffFill

-- | Get track fill when on.
getTrackOnFill :: ToggleAppearance -> Fill
getTrackOnFill a = a.trackOnFill

-- | Get thumb fill.
getThumbFill :: ToggleAppearance -> Fill
getThumbFill a = a.thumbFill

-- | Get focus ring color.
getFocusRingColor :: ToggleAppearance -> RGB
getFocusRingColor a = a.focusRingColor

-- | Get glow effect.
getGlow :: ToggleAppearance -> Maybe Glow
getGlow a = a.glow

-- | Get shadow layers.
getShadow :: ToggleAppearance -> LayeredShadow
getShadow a = a.shadow

-- | Get opacity (bounded 0-1).
getOpacity :: ToggleAppearance -> Number
getOpacity a = Bounded.clampNumber 0.0 1.0 a.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track fill when off.
setTrackOffFill :: Fill -> ToggleAppearance -> ToggleAppearance
setTrackOffFill fill a = a { trackOffFill = fill }

-- | Set track fill when on.
setTrackOnFill :: Fill -> ToggleAppearance -> ToggleAppearance
setTrackOnFill fill a = a { trackOnFill = fill }

-- | Set thumb fill.
setThumbFill :: Fill -> ToggleAppearance -> ToggleAppearance
setThumbFill fill a = a { thumbFill = fill }

-- | Set focus ring color.
setFocusRingColor :: RGB -> ToggleAppearance -> ToggleAppearance
setFocusRingColor color a = a { focusRingColor = color }

-- | Set glow effect.
setGlow :: Glow -> ToggleAppearance -> ToggleAppearance
setGlow g a = a { glow = Just g }

-- | Set shadow layers.
setShadow :: LayeredShadow -> ToggleAppearance -> ToggleAppearance
setShadow s a = a { shadow = s }

-- | Set opacity (automatically bounded 0-1).
setOpacity :: Number -> ToggleAppearance -> ToggleAppearance
setOpacity o a = a { opacity = Bounded.clampNumber 0.0 1.0 o }

-- | Enable glow effect with default blue glow.
-- |
-- | Cool glow at 150 nits, 15px spread.
enableGlow :: ToggleAppearance -> ToggleAppearance
enableGlow a = a { glow = Just (coolGlow 150.0 15.0) }

-- | Disable shadow.
disableShadow :: ToggleAppearance -> ToggleAppearance
disableShadow a = a { shadow = noShadow }
