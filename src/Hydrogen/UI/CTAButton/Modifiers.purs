-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // ui // cta-button // modifiers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton Modifiers — Configuration modifier functions
-- |
-- | This module provides all the builder-pattern functions for configuring
-- | CTA buttons. Each function takes a value and returns a ConfigMod that
-- | updates the corresponding field in CTAConfig.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | button
-- |   [ variant Primary
-- |   , size Lg
-- |   , onClick SubmitForm
-- |   , icon ArrowRight
-- |   , glow Intense
-- |   ]
-- |   [ text "Submit" ]
-- | ```

module Hydrogen.UI.CTAButton.Modifiers
  ( -- * Core Modifiers
    variant
  , size
  , shape
  , disabled
  , loading
  , selected
  , compact
  , fullWidth
  , className
  , id_

  -- * Event Handlers
  , onClick
  , onFocus
  , onBlur
  , onMouseEnter
  , onMouseLeave
  , onMouseDown
  , onMouseUp

  -- * HTML Attributes
  , type_
  , href
  , target
  , download
  , tabIndex
  , title
  , ariaLabel
  , ariaDescribedBy
  , ariaExpanded
  , ariaControls

  -- * Visual Modifiers
  , icon
  , iconPosition
  , iconOnly
  , animate
  , glow
  , glowColor
  , noise
  , borderStyle
  , borderWidth
  , borderRadius
  , gradient
  , gradientDirection

  -- * State Colors
  , backgroundColor
  , foregroundColor
  , hoverBackgroundColor
  , hoverForegroundColor
  , focusBackgroundColor
  , activeBackgroundColor
  , disabledBackgroundColor
  , disabledForegroundColor

  -- * Typography
  , fontFamily
  , fontSize
  , fontWeight
  , letterSpacing
  , textTransform
  , lineHeight

  -- * Spacing
  , paddingX
  , paddingY
  , padding
  , margin
  , gap

  -- * Elevation
  , elevation
  , elevationHover
  , elevationFocus
  , elevationActive
  , zIndex

  -- * Motion
  , transitionDuration
  , transitionEasing
  , transitionProperty
  , animation
  , animationDelay
  , animationIteration

  -- * Purpose & Identity
  , purpose
  , purpose_
  , confirmDanger
  , confirmationText
  ) where

import Prelude
  ( (/=)
  , (<>)
  )

import Data.Maybe (Maybe(Just))

import Hydrogen.UI.CTAButton.Types
  ( CTAVariant
  , CTASize
  , CTAShape
  , IconPosition
  , CTAIcon(NoIcon)
  , CTAAnimation
  , CTAGlowIntensity
  , CTABorderStyle
  , CTAButtonType
  )

import Hydrogen.UI.CTAButton.Config (ConfigMod)

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ButtonPurpose
  ) as ButtonSemantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // core modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button variant
variant :: forall msg. CTAVariant -> ConfigMod msg
variant v config = config { variant = v }

-- | Set button size
size :: forall msg. CTASize -> ConfigMod msg
size s config = config { size = s }

-- | Set button shape
shape :: forall msg. CTAShape -> ConfigMod msg
shape s config = config { shape = s }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

-- | Set loading state (disables button)
loading :: forall msg. Boolean -> ConfigMod msg
loading l config = config { loading = l }

-- | Set selected/pressed state
selected :: forall msg. Boolean -> ConfigMod msg
selected s config = config { selected = s }

-- | Compact mode (reduced padding)
compact :: forall msg. Boolean -> ConfigMod msg
compact c config = config { compact = c }

-- | Full width button
fullWidth :: forall msg. Boolean -> ConfigMod msg
fullWidth fw config = config { fullWidth = fw }

-- | Add custom CSS class
className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

-- | Set element ID
id_ :: forall msg. String -> ConfigMod msg
id_ i config = config { id_ = Just i }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // event handlers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set click handler
onClick :: forall msg. msg -> ConfigMod msg
onClick msg config = config { onClick = Just msg }

-- | Set focus handler
onFocus :: forall msg. msg -> ConfigMod msg
onFocus msg config = config { onFocus = Just msg }

-- | Set blur handler
onBlur :: forall msg. msg -> ConfigMod msg
onBlur msg config = config { onBlur = Just msg }

-- | Set mouse enter handler
onMouseEnter :: forall msg. msg -> ConfigMod msg
onMouseEnter msg config = config { onMouseEnter = Just msg }

-- | Set mouse leave handler
onMouseLeave :: forall msg. msg -> ConfigMod msg
onMouseLeave msg config = config { onMouseLeave = Just msg }

-- | Set mouse down handler
onMouseDown :: forall msg. msg -> ConfigMod msg
onMouseDown msg config = config { onMouseDown = Just msg }

-- | Set mouse up handler
onMouseUp :: forall msg. msg -> ConfigMod msg
onMouseUp msg config = config { onMouseUp = Just msg }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // html attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set HTML button type
type_ :: forall msg. CTAButtonType -> ConfigMod msg
type_ t config = config { type_ = t }

-- | Set href for link buttons
href :: forall msg. String -> ConfigMod msg
href h config = config { href = Just h }

-- | Set target for link buttons
target :: forall msg. String -> ConfigMod msg
target t config = config { target = Just t }

-- | Set download attribute
download :: forall msg. String -> ConfigMod msg
download d config = config { download = Just d }

-- | Set tab index
tabIndex :: forall msg. Int -> ConfigMod msg
tabIndex ti config = config { tabIndex = Just ti }

-- | Set title attribute
title :: forall msg. String -> ConfigMod msg
title t config = config { title = Just t }

-- | Set aria-label
ariaLabel :: forall msg. String -> ConfigMod msg
ariaLabel al config = config { ariaLabel = Just al }

-- | Set aria-describedby
ariaDescribedBy :: forall msg. String -> ConfigMod msg
ariaDescribedBy ad config = config { ariaDescribedBy = Just ad }

-- | Set aria-expanded
ariaExpanded :: forall msg. Boolean -> ConfigMod msg
ariaExpanded ae config = config { ariaExpanded = Just ae }

-- | Set aria-controls
ariaControls :: forall msg. String -> ConfigMod msg
ariaControls ac config = config { ariaControls = Just ac }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // visual modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set icon
icon :: forall msg. CTAIcon -> ConfigMod msg
icon i config = config { icon = i, iconOnly = i /= NoIcon }

-- | Set icon position
iconPosition :: forall msg. IconPosition -> ConfigMod msg
iconPosition ip config = config { iconPosition = ip }

-- | Explicit icon-only mode
iconOnly :: forall msg. Boolean -> ConfigMod msg
iconOnly io config = config { iconOnly = io }

-- | Set animation
animate :: forall msg. CTAAnimation -> ConfigMod msg
animate a config = config { animate = a }

-- | Set glow intensity
glow :: forall msg. CTAGlowIntensity -> ConfigMod msg
glow g config = config { glow = g }

-- | Set custom glow color
glowColor :: forall msg. String -> ConfigMod msg
glowColor gc config = config { glowColor = Just gc }

-- | Enable noise texture
noise :: forall msg. Boolean -> ConfigMod msg
noise n config = config { noise = n }

-- | Set border style
borderStyle :: forall msg. CTABorderStyle -> ConfigMod msg
borderStyle bs config = config { borderStyle = bs }

-- | Set border width
borderWidth :: forall msg. String -> ConfigMod msg
borderWidth bw config = config { borderWidth = Just bw }

-- | Set border radius
borderRadius :: forall msg. String -> ConfigMod msg
borderRadius br config = config { borderRadius = Just br }

-- | Enable gradient background
gradient :: forall msg. Boolean -> ConfigMod msg
gradient g config = config { gradient = g }

-- | Set gradient direction
gradientDirection :: forall msg. String -> ConfigMod msg
gradientDirection gd config = config { gradientDirection = Just gd }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // state colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom background color
backgroundColor :: forall msg. String -> ConfigMod msg
backgroundColor bc config = config { backgroundColor = Just bc }

-- | Custom foreground/text color
foregroundColor :: forall msg. String -> ConfigMod msg
foregroundColor fc config = config { foregroundColor = Just fc }

-- | Custom hover background color
hoverBackgroundColor :: forall msg. String -> ConfigMod msg
hoverBackgroundColor hbc config = config { hoverBackgroundColor = Just hbc }

-- | Custom hover foreground color
hoverForegroundColor :: forall msg. String -> ConfigMod msg
hoverForegroundColor hfc config = config { hoverForegroundColor = Just hfc }

-- | Custom focus background color
focusBackgroundColor :: forall msg. String -> ConfigMod msg
focusBackgroundColor fbc config = config { focusBackgroundColor = Just fbc }

-- | Custom active/pressed background color
activeBackgroundColor :: forall msg. String -> ConfigMod msg
activeBackgroundColor abc config = config { activeBackgroundColor = Just abc }

-- | Custom disabled background color
disabledBackgroundColor :: forall msg. String -> ConfigMod msg
disabledBackgroundColor dbc config = config { disabledBackgroundColor = Just dbc }

-- | Custom disabled foreground color
disabledForegroundColor :: forall msg. String -> ConfigMod msg
disabledForegroundColor dfc config = config { disabledForegroundColor = Just dfc }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom font family
fontFamily :: forall msg. String -> ConfigMod msg
fontFamily ff config = config { fontFamily = Just ff }

-- | Custom font size
fontSize :: forall msg. String -> ConfigMod msg
fontSize fs config = config { fontSize = Just fs }

-- | Custom font weight
fontWeight :: forall msg. String -> ConfigMod msg
fontWeight fw config = config { fontWeight = Just fw }

-- | Custom letter spacing
letterSpacing :: forall msg. String -> ConfigMod msg
letterSpacing ls config = config { letterSpacing = Just ls }

-- | Custom text transform
textTransform :: forall msg. String -> ConfigMod msg
textTransform tt config = config { textTransform = Just tt }

-- | Custom line height
lineHeight :: forall msg. String -> ConfigMod msg
lineHeight lh config = config { lineHeight = Just lh }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom horizontal padding
paddingX :: forall msg. String -> ConfigMod msg
paddingX px config = config { paddingX = Just px }

-- | Custom vertical padding
paddingY :: forall msg. String -> ConfigMod msg
paddingY py config = config { paddingY = Just py }

-- | Custom padding (all sides)
padding :: forall msg. String -> ConfigMod msg
padding p config = config { padding = Just p }

-- | Custom margin
margin :: forall msg. String -> ConfigMod msg
margin m config = config { margin = Just m }

-- | Custom gap between elements
gap :: forall msg. String -> ConfigMod msg
gap g config = config { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable elevation/shadow
elevation :: forall msg. Boolean -> ConfigMod msg
elevation e config = config { elevation = e }

-- | Enable hover elevation
elevationHover :: forall msg. Boolean -> ConfigMod msg
elevationHover eh config = config { elevationHover = eh }

-- | Enable focus elevation
elevationFocus :: forall msg. Boolean -> ConfigMod msg
elevationFocus ef config = config { elevationFocus = ef }

-- | Enable active elevation
elevationActive :: forall msg. Boolean -> ConfigMod msg
elevationActive ea config = config { elevationActive = ea }

-- | Custom z-index
zIndex :: forall msg. String -> ConfigMod msg
zIndex zi config = config { zIndex = Just zi }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom transition duration
transitionDuration :: forall msg. String -> ConfigMod msg
transitionDuration td config = config { transitionDuration = Just td }

-- | Custom transition easing
transitionEasing :: forall msg. String -> ConfigMod msg
transitionEasing te config = config { transitionEasing = Just te }

-- | Custom transition properties
transitionProperty :: forall msg. String -> ConfigMod msg
transitionProperty tp config = config { transitionProperty = Just tp }

-- | Set animation type
animation :: forall msg. CTAAnimation -> ConfigMod msg
animation a config = config { animation = a }

-- | Set animation delay
animationDelay :: forall msg. String -> ConfigMod msg
animationDelay ad config = config { animationDelay = Just ad }

-- | Set animation iteration count
animationIteration :: forall msg. String -> ConfigMod msg
animationIteration ai config = config { animationIteration = Just ai }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // purpose & identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button purpose (semantic)
purpose :: forall msg. ButtonSemantics.ButtonPurpose -> ConfigMod msg
purpose p config = config { purpose = p }

-- | Shorthand for purpose
purpose_ :: forall msg. ButtonSemantics.ButtonPurpose -> ConfigMod msg
purpose_ = purpose

-- | Require confirmation for dangerous actions
confirmDanger :: forall msg. Boolean -> ConfigMod msg
confirmDanger cd config = config { confirmDanger = cd }

-- | Custom confirmation text
confirmationText :: forall msg. String -> ConfigMod msg
confirmationText ct config = config { confirmationText = Just ct }
