-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // password-input //
--                                                                        props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PasswordInput property types and default values.
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.

module Hydrogen.Element.Compound.PasswordInput.Props
  ( -- * Types
    PasswordInputProps
  , PasswordInputProp
  
  -- * Defaults
  , defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | PasswordInput properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type PasswordInputProps msg =
  { -- Content
    value :: String
  , visible :: Boolean
  , showToggle :: Boolean
  , showStrength :: Boolean
  , placeholder :: String
  , disabled :: Boolean
  , required :: Boolean
  , autoComplete :: String
  , minLength :: Maybe Int
  , maxLength :: Maybe Int
  , id :: Maybe String
  , name :: Maybe String
  , ariaLabel :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , toggleButtonColor :: Maybe Color.RGB
  , strengthVeryWeakColor :: Maybe Color.RGB
  , strengthWeakColor :: Maybe Color.RGB
  , strengthFairColor :: Maybe Color.RGB
  , strengthStrongColor :: Maybe Color.RGB
  , strengthVeryStrongColor :: Maybe Color.RGB
  , strengthLabelColor :: Maybe Color.RGB
  , strengthBarBgColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , strengthLabelFontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onToggle :: Maybe msg
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type PasswordInputProp msg = PasswordInputProps msg -> PasswordInputProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. PasswordInputProps msg
defaultProps =
  { value: ""
  , visible: false
  , showToggle: true
  , showStrength: false
  , placeholder: "Enter password"
  , disabled: false
  , required: false
  , autoComplete: "current-password"
  , minLength: Nothing
  , maxLength: Nothing
  , id: Nothing
  , name: Nothing
  , ariaLabel: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , toggleButtonColor: Nothing
  , strengthVeryWeakColor: Nothing
  , strengthWeakColor: Nothing
  , strengthFairColor: Nothing
  , strengthStrongColor: Nothing
  , strengthVeryStrongColor: Nothing
  , strengthLabelColor: Nothing
  , strengthBarBgColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , iconSize: Nothing
  , fontSize: Nothing
  , strengthLabelFontSize: Nothing
  , transitionDuration: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onToggle: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }
