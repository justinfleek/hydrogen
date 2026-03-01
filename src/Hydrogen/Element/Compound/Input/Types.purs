-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // input // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input.Types — Core type definitions for Input components.
-- |
-- | This module defines:
-- | - InputType: HTML input type enumeration
-- | - InputProps: Complete property record for Input components
-- | - InputProp: Property modifier function type
-- | - defaultProps: Default property values

module Hydrogen.Element.Compound.Input.Types
  ( -- * Input Type
    InputType
      ( Text
      , Password
      , Email
      , Number
      , Tel
      , Url
      , Search
      , Date
      , Time
      , DatetimeLocal
      , Month
      , Week
      , Color
      , File
      , Hidden
      )
  , inputTypeToString
  
  -- * Props
  , InputProps
  , InputProp
  , defaultProps
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  )

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // input type
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML input types
-- |
-- | Comprehensive list of valid input types.
data InputType
  = Text
  | Password
  | Email
  | Number
  | Tel
  | Url
  | Search
  | Date
  | Time
  | DatetimeLocal
  | Month
  | Week
  | Color
  | File
  | Hidden

derive instance eqInputType :: Eq InputType

instance showInputType :: Show InputType where
  show Text = "text"
  show Password = "password"
  show Email = "email"
  show Number = "number"
  show Tel = "tel"
  show Url = "url"
  show Search = "search"
  show Date = "date"
  show Time = "time"
  show DatetimeLocal = "datetime-local"
  show Month = "month"
  show Week = "week"
  show Color = "color"
  show File = "file"
  show Hidden = "hidden"

-- | Convert InputType to HTML attribute value
inputTypeToString :: InputType -> String
inputTypeToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // input props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type InputProps msg =
  { -- Content
    inputType :: InputType
  , placeholder :: String
  , value :: String
  , disabled :: Boolean
  , required :: Boolean
  , readOnly :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  , rows :: Int
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , minHeight :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInputChange :: Maybe (String -> msg)
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type InputProp msg = InputProps msg -> InputProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (inherit from context/brand).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. InputProps msg
defaultProps =
  { inputType: Text
  , placeholder: ""
  , value: ""
  , disabled: false
  , required: false
  , readOnly: false
  , id: Nothing
  , name: Nothing
  , rows: 3
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , labelColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , minHeight: Nothing
  , fontSize: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , transitionDuration: Nothing
  , onInputChange: Nothing
  , extraAttributes: []
  }
