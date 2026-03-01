-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // ui // cta-button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton — Ultimate Call-to-Action Button
-- |
-- | The most comprehensive button component, incorporating:
-- | - Color: Background, foreground, hover, focus, active, disabled states
-- | - Dimension: Padding, sizing, spacing, min/max dimensions
-- | - Typography: Font family, size, weight, letter spacing
-- | - Material: Blur, glow, borders, noise texture
-- | - Elevation: Shadows at all states
-- | - Motion: Transitions, keyframe animations
-- | - Reactive: Full state machine (default, hover, focus, active, disabled, loading)
-- | - Gestural: Focus management, keyboard support
-- | - Attestation: UUID5 deterministic identity
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.UI.CTAButton as CTA
-- |
-- | myButton :: CTA.Element Action
-- | myButton = CTA.button
-- |   [ CTA.variant CTA.Primary
-- |   , CTA.size CTA.Large
-- |   , CTA.onClick SubmitForm
-- |   , CTA.icon CTA.ArrowRight
-- |   , CTA.animate CTA.Pulse
-- |   , CTA.glow CTA.Intense
-- |   ]
-- |   [ E.text "Get Started" ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from:
-- | - CTAButton.Types: All data types (variants, sizes, shapes, etc.)
-- | - CTAButton.Config: Configuration record and defaults
-- | - CTAButton.Modifiers: Builder-pattern modifier functions
-- | - CTAButton.Styles: Internal style helpers
-- | - CTAButton.Component: Rendering functions (button, buttonLink)
-- | - CTAButton.Utilities: Helper functions

module Hydrogen.UI.CTAButton
  ( -- * Re-export Types module
    module Types

  -- * Re-export Config module
  , module Config

  -- * Re-export Modifiers module
  , module Modifiers

  -- * Re-export Styles module
  , module Styles

  -- * Re-export Component module
  , module Component

  -- * Re-export Utilities module
  , module Utilities
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Types: All data types
import Hydrogen.UI.CTAButton.Types
  ( CTAVariant(Primary, Secondary, Tertiary, Destructive, Success, Warning, Info, Outline, Ghost, Link)
  , CTASize(Xs, Sm, Md, Lg, Xl, Full)
  , CTAShape(Pill, Rounded, Square, Circle, Blob)
  , IconPosition(IconLeft, IconRight, IconTop, IconBottom)
  , CTAIcon(ArrowRight, ArrowLeft, ArrowUp, ArrowDown, Plus, Check, X, Menu, Search, Cart, User, Lock, Globe, ChevronDown, ChevronUp, NoIcon)
  , CTAAnimation(NoAnimation, Pulse, Bounce, Shake, Glow, Spin, FadeIn, SlideIn, Ripple)
  , CTAGlowIntensity(Subtle, Moderate, Intense, Extreme)
  , CTABorderStyle(Solid, Dashed, Dotted, Double, NoBorder)
  , CTAButtonType(Button, Submit, Reset)
  ) as Types

-- Config: Configuration record and defaults
import Hydrogen.UI.CTAButton.Config
  ( CTAConfig
  , ConfigMod
  , defaultConfig
  ) as Config

-- Modifiers: All builder-pattern functions
import Hydrogen.UI.CTAButton.Modifiers
  ( variant
  , size
  , shape
  , disabled
  , loading
  , selected
  , compact
  , fullWidth
  , className
  , id_
  , onClick
  , onFocus
  , onBlur
  , onMouseEnter
  , onMouseLeave
  , onMouseDown
  , onMouseUp
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
  , backgroundColor
  , foregroundColor
  , hoverBackgroundColor
  , hoverForegroundColor
  , focusBackgroundColor
  , activeBackgroundColor
  , disabledBackgroundColor
  , disabledForegroundColor
  , fontFamily
  , fontSize
  , fontWeight
  , letterSpacing
  , textTransform
  , lineHeight
  , paddingX
  , paddingY
  , padding
  , margin
  , gap
  , elevation
  , elevationHover
  , elevationFocus
  , elevationActive
  , zIndex
  , transitionDuration
  , transitionEasing
  , transitionProperty
  , animation
  , animationDelay
  , animationIteration
  , purpose
  , purpose_
  , confirmDanger
  , confirmationText
  ) as Modifiers

-- Styles: Style helper functions
import Hydrogen.UI.CTAButton.Styles
  ( VariantStyle
  , SizeStyle
  , variantClasses
  , sizeClasses
  , shapeClasses
  , animationClasses
  , glowClasses
  , borderStyleClasses
  , buttonTypeStr
  ) as Styles

-- Component: Rendering functions
import Hydrogen.UI.CTAButton.Component
  ( button
  , buttonLink
  , renderIcon
  , loadingSpinner
  ) as Component

-- Utilities: Helper functions
import Hydrogen.UI.CTAButton.Utilities
  ( showVariant
  , showSize
  , showAnimation
  , variantFromString
  , isInteractive
  , validateConfig
  , buttonUUID
  , toggleStateLabel
  , popupTypeAria
  ) as Utilities
