-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // ui // cta-button // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton Types — Core data types for CTA buttons
-- |
-- | This module defines all the ADTs used by the CTAButton component:
-- | - Variants (Primary, Secondary, Destructive, etc.)
-- | - Sizes (Xs through Full)
-- | - Shapes (Pill, Rounded, Square, Circle, Blob)
-- | - Icon types and positions
-- | - Animations and visual effects
-- | - Border styles and button types

module Hydrogen.UI.CTAButton.Types
  ( -- * Variants
    CTAVariant
      ( Primary
      , Secondary
      , Tertiary
      , Destructive
      , Success
      , Warning
      , Info
      , Outline
      , Ghost
      , Link
      )
  
  -- * Sizes
  , CTASize
      ( Xs
      , Sm
      , Md
      , Lg
      , Xl
      , Full
      )
  
  -- * Shapes
  , CTAShape
      ( Pill
      , Rounded
      , Square
      , Circle
      , Blob
      )
  
  -- * Icon Position
  , IconPosition
      ( IconLeft
      , IconRight
      , IconTop
      , IconBottom
      )
  
  -- * Icon Types
  , CTAIcon
      ( ArrowRight
      , ArrowLeft
      , ArrowUp
      , ArrowDown
      , Plus
      , Check
      , X
      , Menu
      , Search
      , Cart
      , User
      , Lock
      , Globe
      , ChevronDown
      , ChevronUp
      , NoIcon
      )
  
  -- * Animations
  , CTAAnimation
      ( NoAnimation
      , Pulse
      , Bounce
      , Shake
      , Glow
      , Spin
      , FadeIn
      , SlideIn
      , Ripple
      )
  
  -- * Glow Intensity
  , CTAGlowIntensity
      ( Subtle
      , Moderate
      , Intense
      , Extreme
      )
  
  -- * Border Styles
  , CTABorderStyle
      ( Solid
      , Dashed
      , Dotted
      , Double
      , NoBorder
      )
  
  -- * HTML Button Types
  , CTAButtonType
      ( Button
      , Submit
      , Reset
      )
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual variants for CTA buttons
data CTAVariant
  = Primary
  | Secondary
  | Tertiary
  | Destructive
  | Success
  | Warning
  | Info
  | Outline
  | Ghost
  | Link

derive instance eqCTAVariant :: Eq CTAVariant
derive instance ordCTAVariant :: Ord CTAVariant

instance showCTAVariant :: Show CTAVariant where
  show Primary = "Primary"
  show Secondary = "Secondary"
  show Tertiary = "Tertiary"
  show Destructive = "Destructive"
  show Success = "Success"
  show Warning = "Warning"
  show Info = "Info"
  show Outline = "Outline"
  show Ghost = "Ghost"
  show Link = "Link"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button sizes
data CTASize
  = Xs
  | Sm
  | Md
  | Lg
  | Xl
  | Full

derive instance eqCTASize :: Eq CTASize
derive instance ordCTASize :: Ord CTASize

instance showCTASize :: Show CTASize where
  show Xs = "Xs"
  show Sm = "Sm"
  show Md = "Md"
  show Lg = "Lg"
  show Xl = "Xl"
  show Full = "Full"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button shapes
data CTAShape
  = Pill
  | Rounded
  | Square
  | Circle
  | Blob

derive instance eqCTAShape :: Eq CTAShape
derive instance ordCTAShape :: Ord CTAShape

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // icon pos
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon position within button
data IconPosition
  = IconLeft
  | IconRight
  | IconTop
  | IconBottom

derive instance eqIconPosition :: Eq IconPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // icon types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Predefined icon types
data CTAIcon
  = ArrowRight
  | ArrowLeft
  | ArrowUp
  | ArrowDown
  | Plus
  | Check
  | X
  | Menu
  | Search
  | Cart
  | User
  | Lock
  | Globe
  | ChevronDown
  | ChevronUp
  | NoIcon

derive instance eqCTAIcon :: Eq CTAIcon

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // animations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button animations
data CTAAnimation
  = NoAnimation
  | Pulse
  | Bounce
  | Shake
  | Glow
  | Spin
  | FadeIn
  | SlideIn
  | Ripple

derive instance eqCTAAnimation :: Eq CTAAnimation

instance showCTAAnimation :: Show CTAAnimation where
  show NoAnimation = "NoAnimation"
  show Pulse = "Pulse"
  show Bounce = "Bounce"
  show Shake = "Shake"
  show Glow = "Glow"
  show Spin = "Spin"
  show FadeIn = "FadeIn"
  show SlideIn = "SlideIn"
  show Ripple = "Ripple"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // glow intensity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect intensity
data CTAGlowIntensity
  = Subtle
  | Moderate
  | Intense
  | Extreme

derive instance eqCTAGlowIntensity :: Eq CTAGlowIntensity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // border styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border styles
data CTABorderStyle
  = Solid
  | Dashed
  | Dotted
  | Double
  | NoBorder

derive instance eqCTABorderStyle :: Eq CTABorderStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // button types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML button type
data CTAButtonType
  = Button
  | Submit
  | Reset

derive instance eqCTAButtonType :: Eq CTAButtonType
