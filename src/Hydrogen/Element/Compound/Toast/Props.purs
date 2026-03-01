-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // toast // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast Props — Property types and defaults for toast notifications.
-- |
-- | This module defines the property records and default values for both
-- | individual toasts and toast containers.

module Hydrogen.Element.Compound.Toast.Props
  ( -- * Toast Props
    ToastProps
  , ToastProp
  , defaultProps
  
  -- * Container Props
  , ContainerProps
  , ContainerProp
  , defaultContainerProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Toast.Types (ToastPosition(TopRight), ToastActionConfig)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // toast props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast properties
-- |
-- | Complete property record for configuring an individual toast notification.
-- | All optional properties use Maybe to allow falling back to defaults.
type ToastProps msg =
  { -- Content
    title :: Maybe String
  , description :: Maybe String
  , dismissible :: Boolean
  , action :: Maybe (ToastActionConfig msg)
  , id :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , titleColor :: Maybe Color.RGB
  , descriptionColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Elevation atoms
  , shadow :: Maybe Shadow.LayeredShadow
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , maxWidth :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , titleFontSize :: Maybe FontSize.FontSize
  , titleFontWeight :: Maybe FontWeight.FontWeight
  , descriptionFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onDismiss :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
-- |
-- | Function type for modifying toast properties. Used with the builder pattern.
type ToastProp msg = ToastProps msg -> ToastProps msg

-- | Default properties
-- |
-- | Sensible defaults for toast notifications. Most visual properties are
-- | Nothing, allowing the render functions to apply appropriate defaults.
defaultProps :: forall msg. ToastProps msg
defaultProps =
  { title: Nothing
  , description: Nothing
  , dismissible: true
  , action: Nothing
  , id: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , iconColor: Nothing
  , titleColor: Nothing
  , descriptionColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , shadow: Nothing
  , padding: Nothing
  , maxWidth: Nothing
  , gap: Nothing
  , titleFontSize: Nothing
  , titleFontWeight: Nothing
  , descriptionFontSize: Nothing
  , onDismiss: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container properties
-- |
-- | Configuration for the toast container that holds multiple toasts.
type ContainerProps msg =
  { -- Position
    position :: ToastPosition
  
  -- Dimension atoms
  , gap :: Maybe Device.Pixel
  , padding :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Container property modifier
-- |
-- | Function type for modifying container properties.
type ContainerProp msg = ContainerProps msg -> ContainerProps msg

-- | Default container properties
-- |
-- | Places container in top-right corner with reasonable spacing.
defaultContainerProps :: forall msg. ContainerProps msg
defaultContainerProps =
  { position: TopRight
  , gap: Nothing
  , padding: Nothing
  , extraAttributes: []
  }
