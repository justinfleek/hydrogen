-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // toast // builders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast Builders — Property builder functions for toast configuration.
-- |
-- | This module provides all the builder functions for constructing toast
-- | properties using the functional builder pattern.

module Hydrogen.Element.Compound.Toast.Builders
  ( -- * Content Props
    title
  , description
  , dismissible
  , action
  , toastId
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , iconColor
  , titleColor
  , descriptionColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Elevation Atoms
  , shadow
  
  -- * Dimension Atoms
  , padding
  , maxWidth
  , gap
  
  -- * Typography Atoms
  , titleFontSize
  , titleFontWeight
  , descriptionFontSize
  
  -- * Container Props
  , position
  , containerGap
  
  -- * Behavior Props
  , onDismiss
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude ((<>))

import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Toast.Types (ToastPosition, ToastActionConfig)
import Hydrogen.Element.Compound.Toast.Props (ToastProp, ContainerProp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toast title
title :: forall msg. String -> ToastProp msg
title t props = props { title = Just t }

-- | Set toast description
description :: forall msg. String -> ToastProp msg
description d props = props { description = Just d }

-- | Set whether toast is dismissible
dismissible :: forall msg. Boolean -> ToastProp msg
dismissible d props = props { dismissible = d }

-- | Set action button
action :: forall msg. ToastActionConfig msg -> ToastProp msg
action a props = props { action = Just a }

-- | Set toast ID
toastId :: forall msg. String -> ToastProp msg
toastId i props = props { id = Just i }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ToastProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ToastProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ToastProp msg
borderColor c props = props { borderColor = Just c }

-- | Set icon color (Color.RGB atom)
iconColor :: forall msg. Color.RGB -> ToastProp msg
iconColor c props = props { iconColor = Just c }

-- | Set title text color (Color.RGB atom)
titleColor :: forall msg. Color.RGB -> ToastProp msg
titleColor c props = props { titleColor = Just c }

-- | Set description text color (Color.RGB atom)
descriptionColor :: forall msg. Color.RGB -> ToastProp msg
descriptionColor c props = props { descriptionColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> ToastProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ToastProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set shadow (Shadow.LayeredShadow atom)
shadow :: forall msg. Shadow.LayeredShadow -> ToastProp msg
shadow s props = props { shadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ToastProp msg
padding p props = props { padding = Just p }

-- | Set max width (Device.Pixel atom)
maxWidth :: forall msg. Device.Pixel -> ToastProp msg
maxWidth w props = props { maxWidth = Just w }

-- | Set gap between title and description (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ToastProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set title font size (FontSize atom)
titleFontSize :: forall msg. FontSize.FontSize -> ToastProp msg
titleFontSize s props = props { titleFontSize = Just s }

-- | Set title font weight (FontWeight atom)
titleFontWeight :: forall msg. FontWeight.FontWeight -> ToastProp msg
titleFontWeight w props = props { titleFontWeight = Just w }

-- | Set description font size (FontSize atom)
descriptionFontSize :: forall msg. FontSize.FontSize -> ToastProp msg
descriptionFontSize s props = props { descriptionFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container position
position :: forall msg. ToastPosition -> ContainerProp msg
position p props = props { position = p }

-- | Set gap between toasts in container (Device.Pixel atom)
containerGap :: forall msg. Device.Pixel -> ContainerProp msg
containerGap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set dismiss handler
onDismiss :: forall msg. msg -> ToastProp msg
onDismiss handler props = props { onDismiss = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ToastProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
