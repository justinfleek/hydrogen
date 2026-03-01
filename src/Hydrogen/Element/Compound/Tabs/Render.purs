-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // tabs // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tabs Render — Rendering functions for tabbed interface components.
-- |
-- | This module contains all rendering functions:
-- | - tabs — Render the tabs container
-- | - tabList — Render the tab list (container for tab triggers)
-- | - tab — Render an individual tab trigger
-- | - tabPanel — Render a tab panel (content area)

module Hydrogen.Element.Compound.Tabs.Render
  ( -- * Components
    tabs
  , tabList
  , tab
  , tabPanel
  ) where

import Prelude
  ( show
  , (<>)
  , not
  , negate
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Attestation.UUID5 as UUID5

import Hydrogen.Element.Compound.Tabs.Types
  ( TabsProp
  , ListProp
  , TabProps
  , TabProp
  , PanelProp
  )

import Hydrogen.Element.Compound.Tabs.Props
  ( defaultProps
  , defaultListProps
  , defaultTabProps
  , defaultPanelProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tabs container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the tabs container
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
tabs :: forall msg. Array (TabsProp msg) -> Array (E.Element msg) -> E.Element msg
tabs propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- ARIA label for the tabs container
    ariaLabelAttr = case props.ariaLabel of
      Just label -> [ E.ariaLabel label ]
      Nothing -> []
    
    -- Reduced motion data attribute (for runtime CSS injection)
    reducedMotionAttr = if props.reducedMotion
      then [ E.attr "data-reduced-motion" "true" ]
      else []
  in
    E.div_
      ( [ E.attr "data-active-tab" props.activeTab
        ]
        <> ariaLabelAttr
        <> reducedMotionAttr
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // tab list
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the tab list (container for tab triggers)
tabList :: forall msg. Array (ListProp msg) -> Array (E.Element msg) -> E.Element msg
tabList propMods children =
  let
    props = foldl (\p f -> f p) defaultListProps propMods
    
    -- Default colors
    defaultBgColor = Color.rgb 241 245 249  -- Light gray (muted)
    
    -- Background
    bgStyle = E.style "background-color" 
      (Color.toLegacyCss (maybe defaultBgColor (\c -> c) props.backgroundColor))
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> E.style "border-radius" "6px"
      Just r -> E.style "border-radius" (Geometry.cornersToLegacyCss r)
    
    -- Padding
    paddingStyle = E.style "padding" (maybe "4px" show props.padding)
    
    -- Gap
    gapStyle = E.style "gap" (maybe "4px" show props.gap)
  in
    E.div_
      ( [ E.role "tablist"
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , bgStyle
        , radiusStyle
        , paddingStyle
        , gapStyle
        ]
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // tab trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an individual tab trigger
tab :: forall msg. Array (TabProp msg) -> Array (E.Element msg) -> E.Element msg
tab propMods children =
  let
    props = foldl (\p f -> f p) defaultTabProps propMods
  in
    E.button_
      (buildTabAttrs props)
      children

-- | Build tab trigger attributes
buildTabAttrs :: forall msg. TabProps msg -> Array (E.Attribute msg)
buildTabAttrs props =
  let
    -- Generate deterministic IDs using UUID5
    -- Tab ID: uuid5(nsTab, value)
    -- Panel ID: uuid5(nsTabPanel, value) — used for aria-controls
    tabId = UUID5.toString (UUID5.uuid5 UUID5.nsTab props.value)
    panelId = UUID5.toString (UUID5.uuid5 UUID5.nsTabPanel props.value)
    
    -- Default colors (using RGB to match props types)
    defaultBgColor = Color.rgb 248 250 252         -- Very light gray (near white)
    defaultActiveBgColor = Color.rgb 255 255 255   -- White
    defaultTextColor = Color.rgb 100 116 139       -- Muted gray
    defaultActiveTextColor = Color.rgb 15 23 42    -- Dark (foreground)
    defaultFocusRingColor = Color.rgb 59 130 246   -- Blue focus ring
    
    -- Current colors based on active state
    currentBgColor = if props.active
      then maybe defaultActiveBgColor (\c -> c) props.activeBackgroundColor
      else maybe defaultBgColor (\c -> c) props.backgroundColor
    
    currentTextColor = if props.active
      then maybe defaultActiveTextColor (\c -> c) props.activeTextColor
      else maybe defaultTextColor (\c -> c) props.textColor
    
    -- Focus ring color for data attribute
    focusColor = maybe defaultFocusRingColor (\c -> c) props.focusRingColor
    focusWidth = maybe "2" show props.focusRingWidth
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "4px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Height
    heightStyle = case props.height of
      Nothing -> []
      Just h -> [ E.style "height" (show h) ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "12px" show props.paddingX
        py = maybe "6px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Shadow for active state
    shadowStyle = if props.active
      then [ E.style "box-shadow" "0 1px 2px rgba(0, 0, 0, 0.05)" ]
      else []
    
    -- Transition (respects reducedMotion)
    transitionStyle = if props.reducedMotion
      then [ E.style "transition" "none" ]
      else [ E.style "transition" "all 150ms ease-out" ]
    
    -- Hover data attributes (runtime interprets these for :hover styling)
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
    ariaControlsAttr = case props.controlsPanel of
      Just explicitId -> [ E.attr "aria-controls" explicitId ]
      Nothing -> [ E.attr "aria-controls" panelId ]  -- Auto-generated
    
    -- Core styles
    coreStyles =
      [ E.id_ tabId  -- UUID5-generated deterministic ID
      , E.role "tab"
      , E.type_ "button"
      , E.attr "aria-selected" (if props.active then "true" else "false")
      , E.attr "data-state" (if props.active then "active" else "inactive")
      , E.attr "data-value" props.value
      , E.tabIndex (if props.active then 0 else (negate 1))
      , E.disabled props.disabled
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "white-space" "nowrap"
      , E.style "background-color" (Color.toLegacyCss currentBgColor)
      , E.style "color" (Color.toLegacyCss currentTextColor)
      , E.style "border" "none"
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "outline" "none"
      , E.style "user-select" "none"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onSelect of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
    
    -- Keyboard handler for arrow navigation
    keyDownHandler = case props.onKeyDown of
      Just handler -> if not props.disabled then [ E.onKeyDown handler ] else []
      Nothing -> []
  in
    coreStyles 
    <> transitionStyle
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> shadowStyle 
    <> disabledStyle 
    <> hoverAttrs
    <> hoverTextAttrs
    <> focusRingAttrs
    <> ariaControlsAttr
    <> clickHandler 
    <> keyDownHandler
    <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tab panel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a tab panel (content area)
tabPanel :: forall msg. Array (PanelProp msg) -> Array (E.Element msg) -> E.Element msg
tabPanel propMods children =
  let
    props = foldl (\p f -> f p) defaultPanelProps propMods
    
    -- Generate deterministic IDs using UUID5
    -- Panel ID: uuid5(nsTabPanel, value)
    -- Tab ID: uuid5(nsTab, value) — used for aria-labelledby
    panelId = UUID5.toString (UUID5.uuid5 UUID5.nsTabPanel props.value)
    tabId = UUID5.toString (UUID5.uuid5 UUID5.nsTab props.value)
    
    -- Padding
    paddingStyle = E.style "padding" (maybe "16px 0" show props.padding)
    
    -- Visibility
    visibilityStyles = if props.active
      then []
      else [ E.style "display" "none" ]
    
    -- ARIA labelledby: auto-generated from value, or explicit override
    labelledByAttr = case props.labelledBy of
      Just explicitId -> [ E.ariaLabelledBy explicitId ]
      Nothing -> [ E.ariaLabelledBy tabId ]  -- Auto-generated
  in
    E.div_
      ( [ E.id_ panelId  -- UUID5-generated deterministic ID
        , E.role "tabpanel"
        , E.attr "data-state" (if props.active then "active" else "inactive")
        , E.attr "data-value" props.value
        , E.tabIndex 0
        , paddingStyle
        ]
        <> labelledByAttr
        <> visibilityStyles
        <> props.extraAttributes
      )
      children
