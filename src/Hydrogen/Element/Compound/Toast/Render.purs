-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // toast // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast Render — Component rendering functions for toasts.
-- |
-- | This module contains all rendering logic for toast notifications,
-- | including the main toast component, sub-components, and the container.

module Hydrogen.Element.Compound.Toast.Render
  ( -- * Main Components
    toast
  , toastContainer
  
  -- * Sub-Components
  , toastTitle
  , toastDescription
  , toastAction
  , toastClose
  ) where

import Prelude
  ( show
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Toast.Types 
  ( ToastPosition(TopRight, TopLeft, TopCenter, BottomRight, BottomLeft, BottomCenter)
  , ToastActionConfig
  )
import Hydrogen.Element.Compound.Toast.Props 
  ( ToastProps
  , ToastProp
  , defaultProps
  , ContainerProps
  , ContainerProp
  , defaultContainerProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a toast notification
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
toast :: forall msg. Array (ToastProp msg) -> E.Element msg
toast propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      (buildToastAttrs props)
      (buildToastContent props)

-- | Build toast attributes
buildToastAttrs :: forall msg. ToastProps msg -> Array (E.Attribute msg)
buildToastAttrs props =
  let
    -- Default colors
    defaultBgColor = Color.rgb 255 255 255  -- White
    defaultBorderColor = Color.rgb 226 232 240  -- Light gray
    
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    
    -- Core styles
    coreStyles =
      [ E.role "alert"
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "pointer-events" "auto"
      ]
    
    -- Text color
    textColorStyle = case props.textColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    -- Border
    borderStyle =
      let bw = maybe "1px" show props.borderWidth
      in [ E.style "border-style" "solid"
         , E.style "border-width" bw
         , E.style "border-color" (Color.toLegacyCss brdColor)
         ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "8px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Shadow
    shadowStyle = case props.shadow of
      Nothing -> [ E.style "box-shadow" "0 4px 12px rgba(0, 0, 0, 0.15)" ]
      Just s ->
        if Shadow.isNoShadow s
          then []
          else [ E.style "box-shadow" (Shadow.layeredToLegacyCss s) ]
    
    -- Padding
    paddingStyle = case props.padding of
      Nothing -> [ E.style "padding" "16px" ]
      Just p -> [ E.style "padding" (show p) ]
    
    -- Max width
    maxWidthStyle = case props.maxWidth of
      Nothing -> [ E.style "max-width" "360px" ]
      Just w -> [ E.style "max-width" (show w) ]
    
    -- Gap
    gapStyle = case props.gap of
      Nothing -> [ E.style "gap" "4px" ]
      Just g -> [ E.style "gap" (show g) ]
  in
    coreStyles 
    <> textColorStyle 
    <> borderStyle 
    <> radiusStyle 
    <> shadowStyle 
    <> paddingStyle 
    <> maxWidthStyle 
    <> gapStyle
    <> props.extraAttributes

-- | Build toast content
buildToastContent :: forall msg. ToastProps msg -> Array (E.Element msg)
buildToastContent props =
  let
    -- Title
    titleEl = case props.title of
      Nothing -> E.empty
      Just t -> toastTitle props t
    
    -- Description
    descEl = case props.description of
      Nothing -> E.empty
      Just d -> toastDescription props d
    
    -- Action
    actionEl = case props.action of
      Nothing -> E.empty
      Just cfg -> toastAction props cfg
    
    -- Close button
    closeEl = if props.dismissible
      then case props.onDismiss of
        Nothing -> E.empty
        Just _ -> toastClose props
      else E.empty
  in
    [ E.div_
        [ E.style "display" "flex"
        , E.style "justify-content" "space-between"
        , E.style "align-items" "flex-start"
        ]
        [ E.div_
            [ E.style "flex" "1" ]
            [ titleEl, descEl ]
        , closeEl
        ]
    , actionEl
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sub-components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast title element
toastTitle :: forall msg. ToastProps msg -> String -> E.Element msg
toastTitle props titleText =
  let
    fontSizeStyle = case props.titleFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.titleFontWeight of
      Nothing -> [ E.style "font-weight" "600" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.titleColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.div_
      ( [ E.style "line-height" "1.4" ]
        <> fontSizeStyle
        <> fontWeightStyle
        <> colorStyle
      )
      [ E.text titleText ]

-- | Toast description element
toastDescription :: forall msg. ToastProps msg -> String -> E.Element msg
toastDescription props descText =
  let
    fontSizeStyle = case props.descriptionFontSize of
      Nothing -> [ E.style "font-size" "13px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    colorStyle = case props.descriptionColor of
      Nothing -> [ E.style "opacity" "0.8" ]
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.div_
      ( [ E.style "line-height" "1.5"
        , E.style "margin-top" "4px"
        ]
        <> fontSizeStyle
        <> colorStyle
      )
      [ E.text descText ]

-- | Toast action button
toastAction :: forall msg. ToastProps msg -> ToastActionConfig msg -> E.Element msg
toastAction _ cfg =
  E.button_
    [ E.onClick cfg.onAction
    , E.style "margin-top" "8px"
    , E.style "padding" "6px 12px"
    , E.style "font-size" "13px"
    , E.style "font-weight" "500"
    , E.style "background-color" "transparent"
    , E.style "border" "1px solid currentColor"
    , E.style "border-radius" "4px"
    , E.style "cursor" "pointer"
    , E.style "opacity" "0.8"
    ]
    [ E.text cfg.label ]

-- | Toast close button
toastClose :: forall msg. ToastProps msg -> E.Element msg
toastClose props =
  case props.onDismiss of
    Nothing -> E.empty
    Just handler ->
      E.button_
        [ E.onClick handler
        , E.style "background" "transparent"
        , E.style "border" "none"
        , E.style "cursor" "pointer"
        , E.style "padding" "4px"
        , E.style "margin-left" "8px"
        , E.style "opacity" "0.5"
        , E.style "font-size" "18px"
        , E.style "line-height" "1"
        ]
        [ E.text "×" ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // toast container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for multiple toasts
-- |
-- | Place once at app root. Position determines where toasts appear.
toastContainer :: forall msg. Array (ContainerProp msg) -> Array (E.Element msg) -> E.Element msg
toastContainer propMods children =
  let
    props = foldl (\p f -> f p) defaultContainerProps propMods
  in
    E.div_
      (buildContainerAttrs props)
      children

-- | Build container attributes
buildContainerAttrs :: forall msg. ContainerProps msg -> Array (E.Attribute msg)
buildContainerAttrs props =
  let
    -- Gap
    gapValue = maybe "12px" show props.gap
    
    -- Padding
    paddingValue = maybe "16px" show props.padding
    
    -- Position-specific styles
    positionStyles = case props.position of
      TopRight ->
        [ E.style "top" "0"
        , E.style "right" "0"
        , E.style "flex-direction" "column"
        ]
      TopLeft ->
        [ E.style "top" "0"
        , E.style "left" "0"
        , E.style "flex-direction" "column"
        ]
      TopCenter ->
        [ E.style "top" "0"
        , E.style "left" "50%"
        , E.style "transform" "translateX(-50%)"
        , E.style "flex-direction" "column"
        , E.style "align-items" "center"
        ]
      BottomRight ->
        [ E.style "bottom" "0"
        , E.style "right" "0"
        , E.style "flex-direction" "column-reverse"
        ]
      BottomLeft ->
        [ E.style "bottom" "0"
        , E.style "left" "0"
        , E.style "flex-direction" "column-reverse"
        ]
      BottomCenter ->
        [ E.style "bottom" "0"
        , E.style "left" "50%"
        , E.style "transform" "translateX(-50%)"
        , E.style "flex-direction" "column-reverse"
        , E.style "align-items" "center"
        ]
    
    -- Core styles
    coreStyles =
      [ E.style "position" "fixed"
      , E.style "z-index" "9999"
      , E.style "display" "flex"
      , E.style "gap" gapValue
      , E.style "padding" paddingValue
      , E.style "pointer-events" "none"
      , E.style "max-height" "100vh"
      , E.style "overflow" "hidden"
      ]
  in
    coreStyles <> positionStyles <> props.extraAttributes
