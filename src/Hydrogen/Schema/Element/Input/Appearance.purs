-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // element // input // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InputAppearance — Visual atoms for input surface and effects.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Fill (Surface.Fill) — Solid, gradient fills
-- | - RGB/RGBA (Color.RGB) — Verified color channels [0-255]
-- | - LayeredShadow (Elevation.Shadow) — Multi-layer shadows
-- |
-- | ## Input Appearance Model
-- |
-- | An input has multiple visual states:
-- | - Default: Idle state
-- | - Hover: Pointer over input
-- | - Focus: Has keyboard focus
-- | - Error: Validation error
-- | - Disabled: Cannot interact
-- |
-- | Each state can have different colors for:
-- | - Background fill
-- | - Border color
-- | - Text color
-- | - Placeholder color
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Surface.Fill (Fill)
-- | - Hydrogen.Schema.Color.RGB (RGB, RGBA)
-- | - Hydrogen.Schema.Elevation.Shadow (LayeredShadow)

module Hydrogen.Schema.Element.Input.Appearance
  ( -- * Input Variant
    InputVariant
      ( VariantOutlined
      , VariantFilled
      , VariantUnderlined
      , VariantGhost
      )
  
  -- * Input Appearance Record
  , InputAppearance
  , defaultAppearance
  , filledAppearance
  , underlinedAppearance
  , ghostAppearance
  
  -- * Appearance Accessors
  , getBackgroundFill
  , getBorderColor
  , getTextColor
  , getPlaceholderColor
  , getFocusBorderColor
  , getErrorBorderColor
  , getShadow
  , getOpacity
  
  -- * Appearance Modifiers
  , setBackgroundFill
  , setBorderColor
  , setTextColor
  , setPlaceholderColor
  , setFocusBorderColor
  , setErrorBorderColor
  , setShadow
  , setOpacity
  
  -- * Color Presets
  , defaultBackground
  , defaultBorder
  , defaultText
  , defaultPlaceholder
  , defaultFocusBorder
  , defaultErrorBorder
  
  -- * Re-exports
  , module Hydrogen.Schema.Surface.Fill
  , module Hydrogen.Schema.Color.RGB
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
  )

import Prim (Number)

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

import Hydrogen.Schema.Elevation.Shadow
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // input variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input visual variant — structural style for the input.
-- |
-- | ## Variants
-- |
-- | - Outlined: Border on all sides (default)
-- | - Filled: Solid background, no border
-- | - Underlined: Border only on bottom
-- | - Ghost: No background, no border until focus
data InputVariant
  = VariantOutlined       -- ^ Border on all sides
  | VariantFilled         -- ^ Solid background
  | VariantUnderlined     -- ^ Bottom border only
  | VariantGhost          -- ^ Invisible until focus

derive instance eqInputVariant :: Eq InputVariant
derive instance ordInputVariant :: Ord InputVariant

instance showInputVariant :: Show InputVariant where
  show VariantOutlined = "outlined"
  show VariantFilled = "filled"
  show VariantUnderlined = "underlined"
  show VariantGhost = "ghost"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default background fill (white).
defaultBackground :: Fill
defaultBackground = fillSolid (rgb 255 255 255)

-- | Default border color (gray-300).
defaultBorder :: RGB
defaultBorder = rgb 209 213 219

-- | Default text color (gray-900).
defaultText :: RGB
defaultText = rgb 17 24 39

-- | Default placeholder color (gray-400).
defaultPlaceholder :: RGB
defaultPlaceholder = rgb 156 163 175

-- | Default focus border color (blue-500).
defaultFocusBorder :: RGB
defaultFocusBorder = rgb 59 130 246

-- | Default error border color (red-500).
defaultErrorBorder :: RGB
defaultErrorBorder = rgb 239 68 68

-- | Default warning border color (yellow-500).
defaultWarningBorder :: RGB
defaultWarningBorder = rgb 234 179 8

-- | Default success border color (green-500).
defaultSuccessBorder :: RGB
defaultSuccessBorder = rgb 34 197 94

-- | Focus ring shadow — visible on focus.
defaultFocusShadow :: LayeredShadow
defaultFocusShadow = layered
  [ boxShadow
      { offsetX: 0.0
      , offsetY: 0.0
      , blur: 0.0
      , spread: 2.0
      , color: rgba 59 130 246 51  -- blue-500 at 20%
      , inset: false
      }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // input appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete input appearance — all visual properties.
-- |
-- | ## Verified Bounded Types
-- |
-- | - All fills via Fill (verified color channels)
-- | - opacity: bounded [0.0-1.0]
-- | - shadows via LayeredShadow
-- |
-- | ## State Colors
-- |
-- | Each interactive state has specific colors:
-- | - default: Idle state
-- | - hover: Pointer over
-- | - focus: Keyboard focus
-- | - error: Validation failed
-- | - disabled: Cannot interact
type InputAppearance =
  { -- Variant
    variant :: InputVariant          -- ^ Visual style variant
    -- Background
  , backgroundFill :: Fill           -- ^ Input background
  , backgroundHover :: Fill          -- ^ Background on hover
    -- Border (default state)
  , borderColor :: RGB               -- ^ Default border color
  , borderColorHover :: RGB          -- ^ Border on hover
  , borderColorFocus :: RGB          -- ^ Border on focus
  , borderColorError :: RGB          -- ^ Border on error
  , borderColorWarning :: RGB        -- ^ Border on warning
  , borderColorSuccess :: RGB        -- ^ Border on success
    -- Text
  , textColor :: RGB                 -- ^ Text color
  , placeholderColor :: RGB          -- ^ Placeholder text color
    -- Effects
  , shadow :: LayeredShadow          -- ^ Default shadow
  , focusShadow :: LayeredShadow     -- ^ Shadow on focus
    -- Opacity
  , opacity :: Number                -- ^ Overall opacity (bounded 0-1)
  , disabledOpacity :: Number        -- ^ Opacity when disabled
  }

-- | Default input appearance — outlined style with blue focus.
defaultAppearance :: InputAppearance
defaultAppearance =
  { variant: VariantOutlined
  , backgroundFill: defaultBackground
  , backgroundHover: defaultBackground
  , borderColor: defaultBorder
  , borderColorHover: rgb 156 163 175      -- gray-400
  , borderColorFocus: defaultFocusBorder
  , borderColorError: defaultErrorBorder
  , borderColorWarning: defaultWarningBorder
  , borderColorSuccess: defaultSuccessBorder
  , textColor: defaultText
  , placeholderColor: defaultPlaceholder
  , shadow: noShadow
  , focusShadow: defaultFocusShadow
  , opacity: 1.0
  , disabledOpacity: 0.5
  }

-- | Filled input appearance — solid gray background.
filledAppearance :: InputAppearance
filledAppearance = defaultAppearance
  { variant = VariantFilled
  , backgroundFill = fillSolid (rgb 243 244 246)  -- gray-100
  , backgroundHover = fillSolid (rgb 229 231 235) -- gray-200
  , borderColor = rgb 243 244 246                 -- same as background
  }

-- | Underlined input appearance — bottom border only.
underlinedAppearance :: InputAppearance
underlinedAppearance = defaultAppearance
  { variant = VariantUnderlined
  , backgroundFill = fillNone
  , backgroundHover = fillNone
  }

-- | Ghost input appearance — invisible until focus.
ghostAppearance :: InputAppearance
ghostAppearance = defaultAppearance
  { variant = VariantGhost
  , backgroundFill = fillNone
  , backgroundHover = fillSolid (rgb 243 244 246)  -- gray-100
  , borderColor = rgb 255 255 255                  -- invisible (white)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get background fill.
getBackgroundFill :: InputAppearance -> Fill
getBackgroundFill a = a.backgroundFill

-- | Get default border color.
getBorderColor :: InputAppearance -> RGB
getBorderColor a = a.borderColor

-- | Get text color.
getTextColor :: InputAppearance -> RGB
getTextColor a = a.textColor

-- | Get placeholder color.
getPlaceholderColor :: InputAppearance -> RGB
getPlaceholderColor a = a.placeholderColor

-- | Get focus border color.
getFocusBorderColor :: InputAppearance -> RGB
getFocusBorderColor a = a.borderColorFocus

-- | Get error border color.
getErrorBorderColor :: InputAppearance -> RGB
getErrorBorderColor a = a.borderColorError

-- | Get default shadow.
getShadow :: InputAppearance -> LayeredShadow
getShadow a = a.shadow

-- | Get opacity (bounded 0-1).
getOpacity :: InputAppearance -> Number
getOpacity a = Bounded.clampNumber 0.0 1.0 a.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background fill.
setBackgroundFill :: Fill -> InputAppearance -> InputAppearance
setBackgroundFill fill a = a { backgroundFill = fill }

-- | Set default border color.
setBorderColor :: RGB -> InputAppearance -> InputAppearance
setBorderColor color a = a { borderColor = color }

-- | Set text color.
setTextColor :: RGB -> InputAppearance -> InputAppearance
setTextColor color a = a { textColor = color }

-- | Set placeholder color.
setPlaceholderColor :: RGB -> InputAppearance -> InputAppearance
setPlaceholderColor color a = a { placeholderColor = color }

-- | Set focus border color.
setFocusBorderColor :: RGB -> InputAppearance -> InputAppearance
setFocusBorderColor color a = a { borderColorFocus = color }

-- | Set error border color.
setErrorBorderColor :: RGB -> InputAppearance -> InputAppearance
setErrorBorderColor color a = a { borderColorError = color }

-- | Set default shadow.
setShadow :: LayeredShadow -> InputAppearance -> InputAppearance
setShadow s a = a { shadow = s }

-- | Set opacity (automatically bounded 0-1).
setOpacity :: Number -> InputAppearance -> InputAppearance
setOpacity o a = a { opacity = Bounded.clampNumber 0.0 1.0 o }
