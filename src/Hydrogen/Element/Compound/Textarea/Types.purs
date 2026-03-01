-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // textarea-types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea Types — Core type definitions for Textarea component.
-- |
-- | This module defines the `TextareaProps` record type and the default
-- | configuration. All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.

module Hydrogen.Element.Compound.Textarea.Types
  ( TextareaProps
  , TextareaProp
  , defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.LineHeight as LineHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Textarea properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type TextareaProps msg =
  { -- Content
    placeholder :: String
  , value :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  , minRows :: Int
  , maxRows :: Int
  , maxLength :: Maybe Int
  , autoResize :: Boolean
  
  -- Error state
  , error :: Boolean
  , errorMsg :: String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , errorBorderColor :: Maybe Color.RGB
  , errorTextColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  , counterColor :: Maybe Color.RGB
  , requiredColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , minHeight :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , lineHeight :: Maybe LineHeight.LineHeight
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  , counterFontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type TextareaProp msg = TextareaProps msg -> TextareaProps msg

-- | Default textarea properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. TextareaProps msg
defaultProps =
  { placeholder: ""
  , value: ""
  , disabled: false
  , readOnly: false
  , required: false
  , id: Nothing
  , name: Nothing
  , minRows: 3
  , maxRows: 10
  , maxLength: Nothing
  , autoResize: false
  , error: false
  , errorMsg: ""
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , errorBorderColor: Nothing
  , errorTextColor: Nothing
  , labelColor: Nothing
  , counterColor: Nothing
  , requiredColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , minHeight: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , lineHeight: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , counterFontSize: Nothing
  , transitionDuration: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }
