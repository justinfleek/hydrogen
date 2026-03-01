-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // ui // cta-button // component
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton Component — Rendering functions
-- |
-- | This module provides the main rendering functions for CTA buttons:
-- | - button: Renders a <button> element with full configuration
-- | - buttonLink: Renders an <a> element styled as a button
-- |
-- | ## Internal Helpers
-- |
-- | - renderIcon: Renders icon as text (SVG implementation pending)
-- | - loadingSpinner: Animated loading indicator

module Hydrogen.UI.CTAButton.Component
  ( button
  , buttonLink
  , renderIcon
  , loadingSpinner
  ) where

import Prelude
  ( ($)
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)

import Hydrogen.Render.Element as E

import Hydrogen.UI.CTAButton.Types
  ( CTAIcon(ArrowRight, ArrowLeft, ArrowUp, ArrowDown, Plus, Check, X, Menu, Search, Cart, User, Lock, Globe, ChevronDown, ChevronUp, NoIcon)
  , CTAGlowIntensity(Subtle)
  , IconPosition(IconLeft, IconRight, IconTop, IconBottom)
  )

import Hydrogen.UI.CTAButton.Config
  ( CTAConfig
  , ConfigMod
  , defaultConfig
  )

import Hydrogen.UI.CTAButton.Styles
  ( variantClasses
  , sizeClasses
  , shapeClasses
  , animationClasses
  , glowClasses
  , borderStyleClasses
  , buttonTypeStr
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render CTA button as pure Element
-- |
-- | Takes an array of config modifiers and children elements.
-- | Builds a fully styled button with:
-- | - Variant-based colors
-- | - Size-based spacing and typography
-- | - Shape-based border radius
-- | - Animation and glow effects
-- | - Elevation/shadow system
-- | - Loading state with spinner
-- | - Full event handler support
-- | - Comprehensive ARIA attributes
button :: forall msg. Array (ConfigMod msg) -> Array (E.Element msg) -> E.Element msg
button mods children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    variantStyle = variantClasses config.variant
    sizeStyle = sizeClasses config.size
    
    -- Base classes
    base = "inline-flex items-center justify-center whitespace-nowrap font-medium transition-all duration-200 focus:outline-none focus:ring-2 focus:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
    
    -- Variant classes
    vc = if config.disabled
      then ""
      else variantStyle.bg <> " " <> variantStyle.fg <> " " <> variantStyle.border
    
    -- Hover classes
    hc = if config.disabled || config.loading
      then ""
      else variantStyle.hoverBg <> " " <> variantStyle.hoverFg
    
    -- Focus classes  
    fc = "focus:ring-blue-500 focus:ring-offset-2"
    
    -- Active classes
    ac = if config.disabled || config.loading
      then ""
      else "active:scale-[0.98]"
    
    -- Size classes
    sc = sizeStyle.padding <> " " <> sizeStyle.font
    
    -- Shape classes
    shc = shapeClasses config.shape
    
    -- Compact override
    sc' = if config.compact
      then "px-3 py-1.5 text-sm"
      else sc
    
    -- Full width
    wsc = if config.fullWidth then "w-full" else ""
    
    -- Border style
    bsc = borderStyleClasses config.borderStyle
    
    -- Animation
    anc = animationClasses config.animate
    
    -- Glow
    gc = if config.glow /= Subtle && not config.disabled
      then glowClasses config.glow
      else ""
    
    -- Elevation
    ec = if config.elevation then "shadow-md" else ""
    ecH = if config.elevationHover && not config.disabled then "hover:shadow-lg" else ""
    ecF = if config.elevationFocus then "focus:shadow-lg" else ""
    ecA = if config.elevationActive && not config.disabled then "active:shadow-sm" else ""
    
    -- Gradient
    grc = if config.gradient
      then "bg-gradient-to-r from-blue-500 to-blue-600"
      else ""
    
    -- Custom styles
    customBg = fromMaybe "" config.backgroundColor
    customFg = fromMaybe "" config.foregroundColor
    customRadius = fromMaybe "" config.borderRadius
    customZ = fromMaybe "" config.zIndex
    customTd = fromMaybe "200" config.transitionDuration
    customTe = fromMaybe "ease-out" config.transitionEasing
    
    -- Build style string
    styleParts = []
      <> if customBg /= "" then ["background-color:" <> customBg] else []
      <> if customFg /= "" then ["color:" <> customFg] else []
      <> if customRadius /= "" then ["border-radius:" <> customRadius] else []
      <> if customZ /= "" then ["z-index:" <> customZ] else []
      <> if config.iconOnly && sizeStyle.padding == "px-8 py-4"
         then ["--i-button-size:3rem"]
         else []
      <> ["transition-duration:" <> customTd <> "ms"]
      <> ["transition-timing-function:" <> customTe]
    
    style = if null styleParts then Nothing else Just (joinWith "; " styleParts)
    
    -- Build class string
    allClasses = 
      base <> " " <> vc <> " " <> hc <> " " <> fc <> " " <> ac <> " " 
      <> sc' <> " " <> shc <> " " <> bsc <> " " <> anc <> " " <> gc 
      <> " " <> ec <> " " <> ecH <> " " <> ecF <> " " <> ecA <> " " 
      <> grc <> " " <> wsc <> " " <> config.className
    
    -- Loading state
    loadingClass = if config.loading then "opacity-70 cursor-wait" else ""
    
    -- Build attributes
    baseAttrs = 
      [ E.class_ (allClasses <> " " <> loadingClass)
      , E.type_ (buttonTypeStr config.type_)
      , E.disabled (config.disabled || config.loading)
      ]
      <> case config.id_ of
          Just idVal -> [ E.id_ idVal ]
          Nothing -> []
      <> case config.tabIndex of
          Just ti -> [ E.tabIndex ti ]
          Nothing -> []
      <> case config.title of
          Just t -> [ E.title t ]
          Nothing -> []
      <> case config.ariaLabel of
          Just al -> [ E.ariaLabel al ]
          Nothing -> []
      <> case config.ariaDescribedBy of
          Just ad -> [ E.ariaDescribedBy ad ]
          Nothing -> []
      <> case style of
          Just s -> [ E.style "custom" s ]
          Nothing -> []
    
    -- Add event handlers
    attrs = baseAttrs
      <> case config.onClick of
          Just msg -> [ E.onClick msg ]
          Nothing -> []
      <> case config.onFocus of
          Just msg -> [ E.onFocus msg ]
          Nothing -> []
      <> case config.onBlur of
          Just msg -> [ E.onBlur msg ]
          Nothing -> []
      <> case config.onMouseEnter of
          Just msg -> [ E.onMouseEnter msg ]
          Nothing -> []
      <> case config.onMouseLeave of
          Just msg -> [ E.onMouseLeave msg ]
          Nothing -> []
      <> case config.onMouseDown of
          Just msg -> [ E.onMouseDown msg ]
          Nothing -> []
      <> case config.onMouseUp of
          Just msg -> [ E.onMouseUp msg ]
          Nothing -> []
    
    -- Build content
    iconEl = if config.icon /= NoIcon
      then Just $ E.span_ [ E.class_ "inline-flex items-center" ] [ renderIcon config.icon ]
      else Nothing
    
    content = case iconEl of
      Just ie -> case config.iconPosition of
        IconLeft -> [ ie, E.span_ [ E.class_ sizeStyle.iconGap ] [] ] <> children
        IconRight -> children <> [ E.span_ [ E.class_ sizeStyle.iconGap ] [], ie ]
        IconTop -> [ E.div_ [ E.class_ "flex-col" ] [ ie, E.div_ [] children ] ]
        IconBottom -> [ E.div_ [ E.class_ "flex-col" ] [ E.div_ [] children, ie ] ]
      Nothing -> children
    
    -- Add loading spinner
    content' = if config.loading
      then [ loadingSpinner, E.span_ [ E.class_ "ml-2" ] content ]
      else content
  in
    E.button_ attrs content'

-- | Render button-styled link
-- |
-- | Creates an <a> element with button styling.
-- | Useful for navigation that should look like a button.
buttonLink :: forall msg. Array (ConfigMod msg) -> String -> Array (E.Element msg) -> E.Element msg
buttonLink mods url children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    variantStyle = variantClasses config.variant
    sizeStyle = sizeClasses config.size
    
    allClasses = 
      "inline-flex items-center justify-center whitespace-nowrap font-medium transition-all duration-200 focus:outline-none focus:ring-2 focus:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
      <> " " <> variantStyle.bg <> " " <> variantStyle.fg <> " " <> variantStyle.border
      <> " " <> variantStyle.hoverBg <> " " <> variantStyle.hoverFg
      <> " " <> sizeStyle.padding <> " " <> sizeStyle.font
      <> " " <> shapeClasses config.shape
      <> " " <> borderStyleClasses config.borderStyle
      <> " " <> if config.elevation then "shadow-md" else ""
      <> " " <> if config.fullWidth then "w-full" else ""
      <> " " <> config.className
  in
    E.a_
      [ E.class_ allClasses
      , E.href url
      ]
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render icon as text character
-- |
-- | Uses Unicode characters as icon placeholders.
-- | SVG icon implementation is planned for future enhancement.
renderIcon :: forall msg. CTAIcon -> E.Element msg
renderIcon iconType = case iconType of
  ArrowRight -> E.text "→"
  ArrowLeft -> E.text "←"
  ArrowUp -> E.text "↑"
  ArrowDown -> E.text "↓"
  Plus -> E.text "+"
  Check -> E.text "✓"
  X -> E.text "✕"
  Menu -> E.text "☰"
  Search -> E.text "🔍"
  Cart -> E.text "🛒"
  User -> E.text "👤"
  Lock -> E.text "🔒"
  Globe -> E.text "🌐"
  ChevronDown -> E.text "▼"
  ChevronUp -> E.text "▲"
  NoIcon -> E.text ""

-- | Loading spinner element
-- |
-- | Renders an animated spinning circle to indicate loading state.
loadingSpinner :: forall msg. E.Element msg
loadingSpinner =
  E.div_
    [ E.class_ "w-4 h-4 animate-spin rounded-full border-2 border-current border-t-transparent" ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // local utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Join array of strings with separator
joinWith :: String -> Array String -> String
joinWith _ [] = ""
joinWith sep arr = foldl (\acc x -> acc <> sep <> x) "" arr

-- | Check if array is empty
null :: Array String -> Boolean
null [] = true
null _ = false
