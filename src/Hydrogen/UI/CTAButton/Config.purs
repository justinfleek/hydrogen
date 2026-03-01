-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // ui // cta-button // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton Config — Configuration type and defaults
-- |
-- | This module defines:
-- | - CTAConfig: The comprehensive configuration record
-- | - defaultConfig: Sensible defaults for all options
-- | - ConfigMod: Type alias for config modifier functions

module Hydrogen.UI.CTAButton.Config
  ( CTAConfig
  , ConfigMod
  , defaultConfig
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.UI.CTAButton.Types
  ( CTAVariant(Primary)
  , CTASize(Md)
  , CTAShape(Rounded)
  , IconPosition(IconLeft)
  , CTAIcon(NoIcon)
  , CTAAnimation(NoAnimation)
  , CTAGlowIntensity(Subtle)
  , CTABorderStyle(Solid)
  , CTAButtonType(Button)
  )

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ButtonPurpose(ActionButton)
  ) as ButtonSemantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete CTA button configuration
-- |
-- | This record encompasses all possible button customizations:
-- | - Core: variant, size, shape, states
-- | - Event Handlers: click, focus, blur, mouse events
-- | - HTML Attributes: type, href, target, ARIA
-- | - Visual: icon, animation, glow, border, gradient
-- | - State Colors: full color customization per state
-- | - Typography: font family, size, weight, spacing
-- | - Spacing: padding, margin, gap
-- | - Elevation: shadows at various states
-- | - Motion: transitions and animations
-- | - Purpose: semantic identity and confirmation
type CTAConfig msg =
  { -- Core
    variant :: CTAVariant
  , size :: CTASize
  , shape :: CTAShape
  , disabled :: Boolean
  , loading :: Boolean
  , selected :: Boolean
  , compact :: Boolean
  , fullWidth :: Boolean
  , className :: String
  , id_ :: Maybe String

  -- Event Handlers
  , onClick :: Maybe msg
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  , onMouseEnter :: Maybe msg
  , onMouseLeave :: Maybe msg
  , onMouseDown :: Maybe msg
  , onMouseUp :: Maybe msg

  -- HTML Attributes
  , type_ :: CTAButtonType
  , href :: Maybe String
  , target :: Maybe String
  , download :: Maybe String
  , tabIndex :: Maybe Int
  , title :: Maybe String
  , ariaLabel :: Maybe String
  , ariaDescribedBy :: Maybe String
  , ariaExpanded :: Maybe Boolean
  , ariaControls :: Maybe String

  -- Visual
  , icon :: CTAIcon
  , iconPosition :: IconPosition
  , iconOnly :: Boolean
  , animate :: CTAAnimation
  , glow :: CTAGlowIntensity
  , glowColor :: Maybe String
  , noise :: Boolean
  , borderStyle :: CTABorderStyle
  , borderWidth :: Maybe String
  , borderRadius :: Maybe String
  , gradient :: Boolean
  , gradientDirection :: Maybe String

  -- State Colors (full customization)
  , backgroundColor :: Maybe String
  , foregroundColor :: Maybe String
  , hoverBackgroundColor :: Maybe String
  , hoverForegroundColor :: Maybe String
  , focusBackgroundColor :: Maybe String
  , activeBackgroundColor :: Maybe String
  , disabledBackgroundColor :: Maybe String
  , disabledForegroundColor :: Maybe String

  -- Typography
  , fontFamily :: Maybe String
  , fontSize :: Maybe String
  , fontWeight :: Maybe String
  , letterSpacing :: Maybe String
  , textTransform :: Maybe String
  , lineHeight :: Maybe String

  -- Spacing
  , paddingX :: Maybe String
  , paddingY :: Maybe String
  , padding :: Maybe String
  , margin :: Maybe String
  , gap :: Maybe String

  -- Elevation
  , elevation :: Boolean
  , elevationHover :: Boolean
  , elevationFocus :: Boolean
  , elevationActive :: Boolean
  , zIndex :: Maybe String

  -- Motion
  , transitionDuration :: Maybe String
  , transitionEasing :: Maybe String
  , transitionProperty :: Maybe String
  , animation :: CTAAnimation
  , animationDelay :: Maybe String
  , animationIteration :: Maybe String

  -- Purpose & Identity
  , purpose :: ButtonSemantics.ButtonPurpose
  , confirmDanger :: Boolean
  , confirmationText :: Maybe String
  }

-- | Configuration modifier type
-- |
-- | Functions of this type transform a config, allowing builder-pattern usage:
-- | ```purescript
-- | button [ variant Primary, size Lg, onClick Submit ] [ text "Go" ]
-- | ```
type ConfigMod msg = CTAConfig msg -> CTAConfig msg

-- | Default CTA button configuration
-- |
-- | Provides sensible defaults:
-- | - Primary variant, medium size, rounded shape
-- | - Not disabled, not loading, not selected
-- | - No icon, no animation, subtle glow
-- | - Standard elevation behavior (hover/focus only)
-- | - ActionButton purpose
defaultConfig :: forall msg. CTAConfig msg
defaultConfig =
  { -- Core
    variant: Primary
  , size: Md
  , shape: Rounded
  , disabled: false
  , loading: false
  , selected: false
  , compact: false
  , fullWidth: false
  , className: ""
  , id_: Nothing

  -- Event Handlers
  , onClick: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , onMouseEnter: Nothing
  , onMouseLeave: Nothing
  , onMouseDown: Nothing
  , onMouseUp: Nothing

  -- HTML Attributes
  , type_: Button
  , href: Nothing
  , target: Nothing
  , download: Nothing
  , tabIndex: Nothing
  , title: Nothing
  , ariaLabel: Nothing
  , ariaDescribedBy: Nothing
  , ariaExpanded: Nothing
  , ariaControls: Nothing

  -- Visual
  , icon: NoIcon
  , iconPosition: IconLeft
  , iconOnly: false
  , animate: NoAnimation
  , glow: Subtle
  , glowColor: Nothing
  , noise: false
  , borderStyle: Solid
  , borderWidth: Nothing
  , borderRadius: Nothing
  , gradient: false
  , gradientDirection: Nothing

  -- State Colors
  , backgroundColor: Nothing
  , foregroundColor: Nothing
  , hoverBackgroundColor: Nothing
  , hoverForegroundColor: Nothing
  , focusBackgroundColor: Nothing
  , activeBackgroundColor: Nothing
  , disabledBackgroundColor: Nothing
  , disabledForegroundColor: Nothing

  -- Typography
  , fontFamily: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , letterSpacing: Nothing
  , textTransform: Nothing
  , lineHeight: Nothing

  -- Spacing
  , paddingX: Nothing
  , paddingY: Nothing
  , padding: Nothing
  , margin: Nothing
  , gap: Nothing

  -- Elevation
  , elevation: false
  , elevationHover: true
  , elevationFocus: true
  , elevationActive: false
  , zIndex: Nothing

  -- Motion
  , transitionDuration: Nothing
  , transitionEasing: Nothing
  , transitionProperty: Nothing
  , animation: NoAnimation
  , animationDelay: Nothing
  , animationIteration: Nothing

  -- Purpose
  , purpose: ButtonSemantics.ActionButton
  , confirmDanger: false
  , confirmationText: Nothing
  }
