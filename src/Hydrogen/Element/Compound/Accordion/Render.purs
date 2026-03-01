-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // accordion // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion Render — Element rendering functions.
-- |
-- | This module provides the pure rendering functions that transform
-- | accordion props into Element values. All functions are pure and
-- | produce target-agnostic Element data structures.

module Hydrogen.Element.Compound.Accordion.Render
  ( -- * Main Components
    accordion
  , item
  , trigger
  , content
  
  -- * Internal (exported for testing)
  , buildTriggerAttrs
  , chevronIcon
  ) where

import Prelude
  ( show
  , (<>)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
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

-- | Render the accordion container
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
accordion :: forall msg. Array (AccordionProp msg) -> Array (E.Element msg) -> E.Element msg
accordion propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- ARIA label for the accordion container
    ariaLabelAttr = case props.ariaLabel of
      Just label -> [ E.ariaLabel label ]
      Nothing -> []
    
    -- Reduced motion data attribute (for runtime CSS injection)
    reducedMotionAttr = if props.reducedMotion
      then [ E.attr "data-reduced-motion" "true" ]
      else []
  in
    E.div_
      ( [ E.attr "data-accordion" "true"
        ]
        <> ariaLabelAttr
        <> reducedMotionAttr
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // accordion item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an accordion item (section)
item :: forall msg. Array (ItemProp msg) -> Array (E.Element msg) -> E.Element msg
item propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    -- Default border
    defaultBorderColor = Color.rgb 226 232 240  -- Light gray
    
    -- Border style (bottom border for item separation)
    borderColorVal = maybe defaultBorderColor (\c -> c) props.borderColor
    borderWidthVal = maybe "1px" show props.borderWidth
  in
    E.div_
      ( [ E.attr "data-accordion-item" "true"
        , E.attr "data-value" props.value
        , E.style "border-bottom-style" "solid"
        , E.style "border-bottom-width" borderWidthVal
        , E.style "border-bottom-color" (Color.toLegacyCss borderColorVal)
        ]
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an accordion trigger (clickable header)
trigger :: forall msg. Array (TriggerProp msg) -> Array (E.Element msg) -> E.Element msg
trigger propMods children =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
  in
    -- Wrap in h3 for semantics
    E.h3_
      [ E.style "margin" "0"
      , E.style "display" "flex"
      ]
      [ E.button_
          (buildTriggerAttrs props)
          (children <> [ chevronIcon props ])
      ]

-- | Build trigger button attributes
buildTriggerAttrs :: forall msg. TriggerProps msg -> Array (E.Attribute msg)
buildTriggerAttrs props =
  let
    -- Generate deterministic IDs using UUID5
    -- Trigger ID: uuid5(nsAccordionTrigger, value)
    -- Content ID: uuid5(nsAccordionContent, value) — used for aria-controls
    triggerId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionTrigger props.value)
    contentId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionContent props.value)
    
    -- Default colors
    defaultTextColor = Color.rgb 15 23 42      -- Dark (foreground)
    defaultFocusRingColor = Color.rgb 59 130 246  -- Blue focus ring
    
    -- Text color
    textColorVal = maybe defaultTextColor (\c -> c) props.textColor
    
    -- Focus ring
    focusColor = maybe defaultFocusRingColor (\c -> c) props.focusRingColor
    focusWidth = maybe "2" show props.focusRingWidth
    
    -- Background (default transparent)
    bgStyle = case props.backgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> [ E.style "background-color" "transparent" ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "0" show props.paddingX
        py = maybe "16px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "inherit" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Transition (respects reducedMotion)
    transitionStyle = if props.reducedMotion
      then [ E.style "transition" "none" ]
      else [ E.style "transition" "all 150ms ease-out" ]
    
    -- Hover data attributes (runtime interprets for :hover styling)
    hoverAttrs = case props.hoverBackgroundColor of
      Just c -> [ E.attr "data-hover-bg" (Color.toLegacyCss c) ]
      Nothing -> []
    
    hoverTextAttrs = case props.hoverTextColor of
      Just c -> [ E.attr "data-hover-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    -- Focus ring data attributes (runtime interprets for :focus-visible)
    focusRingAttrs =
      [ E.attr "data-focus-ring-color" (Color.toLegacyCss focusColor)
      , E.attr "data-focus-ring-width" focusWidth
      ]
    
    -- ARIA controls: auto-generated from value, or explicit override
    ariaControlsAttr = case props.controlsContent of
      Just explicitId -> [ E.attr "aria-controls" explicitId ]
      Nothing -> [ E.attr "aria-controls" contentId ]  -- Auto-generated
    
    -- Core styles
    coreStyles =
      [ E.id_ triggerId  -- UUID5-generated deterministic ID
      , E.type_ "button"
      , E.attr "aria-expanded" (if props.open then "true" else "false")
      , E.attr "data-state" (if props.open then "open" else "closed")
      , E.attr "data-value" props.value
      , E.disabled props.disabled
      , E.style "display" "flex"
      , E.style "flex" "1"
      , E.style "align-items" "center"
      , E.style "justify-content" "space-between"
      , E.style "width" "100%"
      , E.style "border" "none"
      , E.style "color" (Color.toLegacyCss textColorVal)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "outline" "none"
      , E.style "text-align" "left"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onToggle of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
    
    -- Keyboard handler for arrow navigation
    keyDownHandler = case props.onKeyDown of
      Just handler -> if not props.disabled then [ E.onKeyDown handler ] else []
      Nothing -> []
  in
    coreStyles 
    <> transitionStyle
    <> bgStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> disabledStyle 
    <> hoverAttrs
    <> hoverTextAttrs
    <> focusRingAttrs
    <> ariaControlsAttr
    <> clickHandler 
    <> keyDownHandler
    <> props.extraAttributes

-- | Render the chevron icon
chevronIcon :: forall msg. TriggerProps msg -> E.Element msg
chevronIcon props =
  let
    -- Icon color
    defaultIconColor = Color.rgb 100 116 139  -- Muted gray
    iconColorVal = maybe defaultIconColor (\c -> c) props.iconColor
    
    -- Rotation transform based on open state
    rotationStyle = if props.open
      then "rotate(180deg)"
      else "rotate(0deg)"
    
    -- Transition (respects reducedMotion)
    transitionVal = if props.reducedMotion
      then "none"
      else "transform 200ms ease-out"
  in
    E.svg_
      [ E.attr "viewBox" "0 0 24 24"
      , E.attr "fill" "none"
      , E.attr "stroke" (Color.toLegacyCss iconColorVal)
      , E.attr "stroke-width" "2"
      , E.attr "stroke-linecap" "round"
      , E.attr "stroke-linejoin" "round"
      , E.style "width" "16px"
      , E.style "height" "16px"
      , E.style "flex-shrink" "0"
      , E.style "transition" transitionVal
      , E.style "transform" rotationStyle
      ]
      [ E.polyline_
          [ E.attr "points" "6 9 12 15 18 9" ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render accordion content (collapsible area)
content :: forall msg. Array (ContentProp msg) -> Array (E.Element msg) -> E.Element msg
content propMods children =
  let
    props = foldl (\p f -> f p) defaultContentProps propMods
    
    -- Generate deterministic IDs using UUID5
    -- Content ID: uuid5(nsAccordionContent, value)
    -- Trigger ID: uuid5(nsAccordionTrigger, value) — used for aria-labelledby
    contentId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionContent props.value)
    triggerId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionTrigger props.value)
    
    -- Transition duration (respects reducedMotion)
    transitionVal = if props.reducedMotion
      then "none"
      else "all " <> maybe "200ms" show props.transitionDuration <> " ease-out"
    
    -- Visibility styles
    visibilityStyles = if props.open
      then [ E.style "max-height" "1000px"
           , E.style "opacity" "1"
           ]
      else [ E.style "max-height" "0"
           , E.style "opacity" "0"
           , E.style "visibility" "hidden"
           ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "0" show props.paddingX
        py = maybe "0" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Colors
    bgStyle = case props.backgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    textStyle = case props.textColor of
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    -- ARIA labelledby: auto-generated from value, or explicit override
    labelledByAttr = case props.labelledBy of
      Just explicitId -> [ E.ariaLabelledBy explicitId ]
      Nothing -> [ E.ariaLabelledBy triggerId ]  -- Auto-generated
    
    -- Core styles
    coreStyles =
      [ E.id_ contentId  -- UUID5-generated deterministic ID
      , E.role "region"
      , E.attr "data-state" (if props.open then "open" else "closed")
      , E.attr "data-value" props.value
      , E.style "overflow" "hidden"
      , E.style "transition" transitionVal
      ]
  in
    E.div_
      ( coreStyles 
        <> labelledByAttr
        <> visibilityStyles 
        <> paddingStyle 
        <> bgStyle 
        <> textStyle 
        <> props.extraAttributes
      )
      [ -- Inner wrapper with padding for content
        E.div_
          [ E.style "padding-bottom" "16px"
          , E.style "font-size" "14px"
          ]
          children
      ]
