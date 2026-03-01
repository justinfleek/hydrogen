-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // ui // cta-button // styles
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton Styles — Style helper functions
-- |
-- | This module provides functions that map CTA button types to CSS class names.
-- | These are internal helpers used by the Component module to build class strings.
-- |
-- | ## Style Categories
-- |
-- | - Variant styles: background, foreground, border, hover states
-- | - Size styles: padding, font size, icon gap
-- | - Shape styles: border radius
-- | - Animation styles: keyframe animations
-- | - Glow styles: shadow intensity
-- | - Border styles: solid, dashed, dotted, etc.

module Hydrogen.UI.CTAButton.Styles
  ( -- * Style Records
    VariantStyle
  , SizeStyle
  
  -- * Style Functions
  , variantClasses
  , sizeClasses
  , shapeClasses
  , animationClasses
  , glowClasses
  , borderStyleClasses
  , buttonTypeStr
  ) where

import Hydrogen.UI.CTAButton.Types
  ( CTAVariant(Primary, Secondary, Tertiary, Destructive, Success, Warning, Info, Outline, Ghost, Link)
  , CTASize(Xs, Sm, Md, Lg, Xl, Full)
  , CTAShape(Pill, Rounded, Square, Circle, Blob)
  , CTAAnimation(NoAnimation, Pulse, Bounce, Shake, Glow, Spin, FadeIn, SlideIn, Ripple)
  , CTAGlowIntensity(Subtle, Moderate, Intense, Extreme)
  , CTABorderStyle(Solid, Dashed, Dotted, Double, NoBorder)
  , CTAButtonType(Button, Submit, Reset)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // style records
-- ═════════════════════════════════════════════════════════════════════════════

-- | Variant style record containing all color-related classes
type VariantStyle =
  { bg :: String
  , fg :: String
  , border :: String
  , hoverBg :: String
  , hoverFg :: String
  }

-- | Size style record containing spacing and typography classes
type SizeStyle =
  { padding :: String
  , font :: String
  , iconGap :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // variant classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get base classes for variant
-- |
-- | Each variant defines a complete color palette including:
-- | - Background color (bg)
-- | - Foreground/text color (fg)
-- | - Border color (border)
-- | - Hover background (hoverBg)
-- | - Hover foreground (hoverFg)
variantClasses :: CTAVariant -> VariantStyle
variantClasses = case _ of
  Primary ->
    { bg: "bg-blue-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-blue-700", hoverFg: "hover:text-white" }
  Secondary ->
    { bg: "bg-gray-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-gray-700", hoverFg: "hover:text-white" }
  Tertiary ->
    { bg: "bg-gray-100", fg: "text-gray-900", border: "border-transparent"
    , hoverBg: "hover:bg-gray-200", hoverFg: "hover:text-gray-900" }
  Destructive ->
    { bg: "bg-red-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-red-700", hoverFg: "hover:text-white" }
  Success ->
    { bg: "bg-green-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-green-700", hoverFg: "hover:text-white" }
  Warning ->
    { bg: "bg-yellow-500", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-yellow-600", hoverFg: "hover:text-white" }
  Info ->
    { bg: "bg-cyan-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-cyan-700", hoverFg: "hover:text-white" }
  Outline ->
    { bg: "bg-transparent", fg: "text-gray-700", border: "border-gray-300"
    , hoverBg: "hover:bg-gray-50", hoverFg: "hover:text-gray-900" }
  Ghost ->
    { bg: "bg-transparent", fg: "text-gray-700", border: "border-transparent"
    , hoverBg: "hover:bg-gray-100", hoverFg: "hover:text-gray-900" }
  Link ->
    { bg: "bg-transparent", fg: "text-blue-600", border: "border-transparent"
    , hoverBg: "hover:bg-transparent", hoverFg: "hover:text-blue-800" }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // size classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get size classes
-- |
-- | Each size defines:
-- | - Padding (horizontal and vertical)
-- | - Font size
-- | - Gap between icon and text
sizeClasses :: CTASize -> SizeStyle
sizeClasses = case _ of
  Xs -> { padding: "px-2.5 py-1.5", font: "text-xs", iconGap: "gap-1" }
  Sm -> { padding: "px-3 py-2", font: "text-sm", iconGap: "gap-1.5" }
  Md -> { padding: "px-4 py-2", font: "text-sm", iconGap: "gap-2" }
  Lg -> { padding: "px-6 py-3", font: "text-base", iconGap: "gap-2" }
  Xl -> { padding: "px-8 py-4", font: "text-lg", iconGap: "gap-2.5" }
  Full -> { padding: "px-8 py-4", font: "text-lg", iconGap: "gap-3" }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shape classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get shape classes
-- |
-- | Maps shape variants to Tailwind border-radius utilities
shapeClasses :: CTAShape -> String
shapeClasses = case _ of
  Pill -> "rounded-full"
  Rounded -> "rounded-lg"
  Square -> "rounded-none"
  Circle -> "rounded-full"
  Blob -> "rounded-[2rem]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get animation classes
-- |
-- | Maps animation types to Tailwind/custom animation utilities
animationClasses :: CTAAnimation -> String
animationClasses = case _ of
  NoAnimation -> ""
  Pulse -> "animate-pulse"
  Bounce -> "animate-bounce"
  Shake -> "animate-shake"
  Glow -> "animate-glow"
  Spin -> "animate-spin"
  FadeIn -> "animate-fade-in"
  SlideIn -> "animate-slide-in"
  Ripple -> "animate-ripple"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // glow classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get glow classes
-- |
-- | Maps glow intensity to shadow utilities
glowClasses :: CTAGlowIntensity -> String
glowClasses = case _ of
  Subtle -> "shadow-sm"
  Moderate -> "shadow-md"
  Intense -> "shadow-lg shadow-blue-500/25"
  Extreme -> "shadow-xl shadow-blue-500/40"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // border classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get border style classes
-- |
-- | Maps border style variants to CSS border-style utilities
borderStyleClasses :: CTABorderStyle -> String
borderStyleClasses = case _ of
  Solid -> "border-solid"
  Dashed -> "border-dashed"
  Dotted -> "border-dotted"
  Double -> "border-double"
  NoBorder -> "border-none"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // button type str
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get button type string for HTML attribute
-- |
-- | Converts CTAButtonType to the string value for the HTML type attribute
buttonTypeStr :: CTAButtonType -> String
buttonTypeStr = case _ of
  Button -> "button"
  Submit -> "submit"
  Reset -> "reset"
