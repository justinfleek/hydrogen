-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // toast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast — Schema-native notification component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Toast notifications display brief messages to users.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property            | Pillar     | Type                      | CSS Output              |
-- | |---------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor     | Color      | Color.RGB                 | background-color        |
-- | | textColor           | Color      | Color.RGB                 | color                   |
-- | | borderColor         | Color      | Color.RGB                 | border-color            |
-- | | iconColor           | Color      | Color.RGB                 | icon color              |
-- | | borderRadius        | Geometry   | Geometry.Corners          | border-radius           |
-- | | padding             | Dimension  | Device.Pixel              | padding                 |
-- | | shadow              | Elevation  | Shadow.LayeredShadow      | box-shadow              |
-- | | gap                 | Dimension  | Device.Pixel              | gap between toasts      |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Toast as Toast
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Toast container (place once at app root)
-- | Toast.toastContainer
-- |   [ Toast.position Toast.TopRight
-- |   , Toast.gap (Device.px 12.0)
-- |   ]
-- |   toastElements
-- |
-- | -- Individual toast with brand atoms
-- | Toast.toast
-- |   [ Toast.title "Success!"
-- |   , Toast.description "Your changes have been saved."
-- |   , Toast.backgroundColor brand.successBackground
-- |   , Toast.textColor brand.successText
-- |   , Toast.dismissible true
-- |   , Toast.onDismiss DismissToast
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Toast.Types` — Core type definitions
-- | - `Toast.Props` — Property records and defaults
-- | - `Toast.Builders` — Property builder functions
-- | - `Toast.Render` — Component rendering functions

module Hydrogen.Element.Compound.Toast
  ( module Types
  , module Props
  , module Builders
  , module Render
  ) where

import Hydrogen.Element.Compound.Toast.Types 
  ( ToastActionConfig
  , ToastPosition(TopRight, TopLeft, TopCenter, BottomRight, BottomLeft, BottomCenter)
  ) as Types

import Hydrogen.Element.Compound.Toast.Props 
  ( ContainerProp
  , ContainerProps
  , ToastProp
  , ToastProps
  , defaultContainerProps
  , defaultProps
  ) as Props

import Hydrogen.Element.Compound.Toast.Builders 
  ( action
  , backgroundColor
  , borderColor
  , borderRadius
  , borderWidth
  , containerGap
  , description
  , descriptionColor
  , descriptionFontSize
  , dismissible
  , extraAttributes
  , gap
  , iconColor
  , maxWidth
  , onDismiss
  , padding
  , position
  , shadow
  , textColor
  , title
  , titleColor
  , titleFontSize
  , titleFontWeight
  , toastId
  ) as Builders

import Hydrogen.Element.Compound.Toast.Render 
  ( toast
  , toastAction
  , toastClose
  , toastContainer
  , toastDescription
  , toastTitle
  ) as Render
