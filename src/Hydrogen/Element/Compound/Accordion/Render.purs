-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // accordion // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion Render — Element rendering using typed Schema atoms.
-- |
-- | NO STRINGS. All styles use bounded Schema atoms.

module Hydrogen.Element.Compound.Accordion.Render
  ( accordion
  , item
  , trigger
  , content
  , buildTriggerAttrs
  , chevronIcon
  ) where

import Prelude
  ( not
  , ($)
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Render.Element.Types
  ( Display(DisplayFlex)
  , FlexAlign(AlignCenter)
  , FlexJustify(JustifySpaceBetween)
  , Cursor(CursorPointer, CursorNotAllowed)
  , TextAlign(TextAlignLeft)
  , Visibility(VisibilityHidden)
  , Overflow(OverflowHidden)
  )
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.RGB (rgb)
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Geometry.Border as Border
import Hydrogen.Schema.Dimension.Device (px) as Device
import Hydrogen.Schema.Dimension.Percentage (percent) as Percent
import Hydrogen.Schema.Motion.Transform as Transform
import Hydrogen.Schema.Motion.Transition as Transition
import Hydrogen.Schema.Attestation.UUID5 as UUID5

import Hydrogen.Element.Compound.Accordion.Types
  ( AccordionProp
  , ItemProp
  , TriggerProps
  , TriggerProp
  , ContentProp
  )

import Hydrogen.Element.Compound.Accordion.Config
  ( defaultProps
  , defaultItemProps
  , defaultTriggerProps
  , defaultContentProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // accordion container
-- ═════════════════════════════════════════════════════════════════════════════

accordion :: forall msg. Array (AccordionProp msg) -> Array (E.Element msg) -> E.Element msg
accordion propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    ariaLabelAttr = case props.ariaLabel of
      Just label -> [ E.ariaLabel label ]
      Nothing -> []
    
    reducedMotionAttr = if props.reducedMotion
      then [ E.attr "data-reduced-motion" "true" ]
      else []
  in
    E.div_
      ( [ E.attr "data-accordion" "true" ]
        <> ariaLabelAttr
        <> reducedMotionAttr
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // accordion item
-- ═════════════════════════════════════════════════════════════════════════════

item :: forall msg. Array (ItemProp msg) -> Array (E.Element msg) -> E.Element msg
item propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    defaultBorderColor = rgb 226 232 240
    borderColorVal = maybe defaultBorderColor (\c -> c) props.borderColor
    borderWidthVal = maybe (Device.px 1.0) (\w -> w) props.borderWidth
    
    bottomBorder = Border.borderBottom
      { width: borderWidthVal
      , color: borderColorVal
      }
  in
    E.div_
      ( [ E.attr "data-accordion-item" "true"
        , E.attr "data-value" props.value
        , E.borderBottom bottomBorder
        ]
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion trigger
-- ═════════════════════════════════════════════════════════════════════════════

trigger :: forall msg. Array (TriggerProp msg) -> Array (E.Element msg) -> E.Element msg
trigger propMods children =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
  in
    E.h3_
      [ E.margin (Spacing.spacingZero)
      , E.display DisplayFlex
      ]
      [ E.button_
          (buildTriggerAttrs props)
          (children <> [ chevronIcon props ])
      ]

buildTriggerAttrs :: forall msg. TriggerProps msg -> Array (E.Attribute msg)
buildTriggerAttrs props =
  let
    triggerId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionTrigger props.value)
    contentId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionContent props.value)
    
    defaultTextColor = rgb 15 23 42
    defaultFocusRingColor = rgb 59 130 246
    
    textColorVal = maybe defaultTextColor (\c -> c) props.textColor
    focusColor = maybe defaultFocusRingColor (\c -> c) props.focusRingColor
    
    bgStyle = case props.backgroundColor of
      Just c -> [ E.backgroundColor c ]
      Nothing -> []
    
    paddingStyle = case props.paddingY of
      Just py -> [ E.padding py ]
      Nothing -> [ E.padding (Spacing.spacingMd) ]
    
    fontSizeStyle = case props.fontSize of
      Just s -> [ E.fontSize s ]
      Nothing -> []
    
    fontWeightStyle = case props.fontWeight of
      Just w -> [ E.fontWeight w ]
      Nothing -> [ E.fontWeight FontWeight.medium ]
    
    transitionStyle = if props.reducedMotion
      then []
      else [ E.transition Transition.defaultTransition ]
    
    cursorStyle = if props.disabled
      then [ E.cursor CursorNotAllowed ]
      else [ E.cursor CursorPointer ]
    
    opacityStyle = if props.disabled
      then [ E.opacity (Transform.mkOpacity 0.5) ]
      else []
    
    coreAttrs =
      [ E.id_ triggerId
      , E.type_ "button"
      , E.attr "aria-expanded" (if props.open then "true" else "false")
      , E.attr "aria-controls" contentId
      , E.attr "data-state" (if props.open then "open" else "closed")
      , E.attr "data-value" props.value
      , E.disabled props.disabled
      , E.display DisplayFlex
      , E.alignItems AlignCenter
      , E.justifyContent JustifySpaceBetween
      , E.width (Percent.percent 100.0)
      , E.color textColorVal
      , E.textAlign TextAlignLeft
      ]
    
    clickHandler = case props.onToggle of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
    
    keyDownHandler = case props.onKeyDown of
      Just handler -> if not props.disabled then [ E.onKeyDown handler ] else []
      Nothing -> []
  in
    coreAttrs 
    <> bgStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> transitionStyle
    <> cursorStyle
    <> opacityStyle
    <> clickHandler 
    <> keyDownHandler
    <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // chevron icon
-- ═════════════════════════════════════════════════════════════════════════════

chevronIcon :: forall msg. TriggerProps msg -> E.Element msg
chevronIcon props =
  let
    defaultIconColor = rgb 100 116 139
    iconColorVal = maybe defaultIconColor (\c -> c) props.iconColor
    
    rotation = if props.open
      then Transform.mkRotation 180.0
      else Transform.mkRotation 0.0
    
    transformVal = Transform.defaultTransform2D { rotation = rotation }
  in
    E.svg_
      [ E.attr "viewBox" "0 0 24 24"
      , E.attr "fill" "none"
      , E.attr "stroke" (Color.rgbToHex iconColorVal)
      , E.attr "stroke-width" "2"
      , E.attr "stroke-linecap" "round"
      , E.attr "stroke-linejoin" "round"
      , E.width (Device.px 16.0)
      , E.height (Device.px 16.0)
      , E.transform transformVal
      ]
      [ E.polyline_
          [ E.attr "points" "6 9 12 15 18 9" ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion content
-- ═════════════════════════════════════════════════════════════════════════════

content :: forall msg. Array (ContentProp msg) -> Array (E.Element msg) -> E.Element msg
content propMods children =
  let
    props = foldl (\p f -> f p) defaultContentProps propMods
    
    contentId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionContent props.value)
    triggerId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionTrigger props.value)
    
    visibilityStyles = if props.open
      then [ E.opacity Transform.opacityFull ]
      else [ E.opacity Transform.opacityZero
           , E.visibility VisibilityHidden
           ]
    
    paddingStyle = case props.paddingY of
      Just py -> [ E.padding py ]
      Nothing -> []
    
    bgStyle = case props.backgroundColor of
      Just c -> [ E.backgroundColor c ]
      Nothing -> []
    
    textStyle = case props.textColor of
      Just c -> [ E.color c ]
      Nothing -> []
    
    transitionStyle = if props.reducedMotion
      then []
      else [ E.transition Transition.defaultTransition ]
    
    coreAttrs =
      [ E.id_ contentId
      , E.role "region"
      , E.ariaLabelledBy triggerId
      , E.attr "data-state" (if props.open then "open" else "closed")
      , E.attr "data-value" props.value
      , E.overflow OverflowHidden
      ]
  in
    E.div_
      ( coreAttrs 
        <> visibilityStyles 
        <> paddingStyle 
        <> bgStyle 
        <> textStyle 
        <> transitionStyle
        <> props.extraAttributes
      )
      children
