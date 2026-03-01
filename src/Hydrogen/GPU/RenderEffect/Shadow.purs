-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // render-effect/shadow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shadow effects for the RenderEffect system.
-- |
-- | Provides three shadow variants for depth and elevation:
-- | - **Drop**: Classic shadow following element shape
-- | - **Box**: CSS-style with spread for UI elevation
-- | - **Contact**: Grounded shadow beneath element (realism)

module Hydrogen.GPU.RenderEffect.Shadow
  ( -- * Shadow Effect Type
    ShadowEffect(..)
  
  -- * Shadow Variants
  , DropShadowEffect(..)
  , BoxShadowEffect(..)
  , ContactShadow(..)
  
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.RenderEffect.Types (GlowColor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // shadow effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow effect variants
-- |
-- | Shadows are implemented as offset, blurred copies of the element's
-- | alpha channel. Each variant optimizes for specific elevation needs.
data ShadowEffect
  = ShadowDrop DropShadowEffect
  | ShadowBox BoxShadowEffect
  | ShadowContact ContactShadow

derive instance eqShadowEffect :: Eq ShadowEffect

instance showShadowEffect :: Show ShadowEffect where
  show (ShadowDrop s) = "(ShadowDrop " <> show s <> ")"
  show (ShadowBox s) = "(ShadowBox " <> show s <> ")"
  show (ShadowContact s) = "(ShadowContact " <> show s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // shadow variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop shadow — follows element shape
-- |
-- | Simple offset shadow with blur. Good for icons, floating elements,
-- | and simple depth indication.
newtype DropShadowEffect = DropShadowEffect
  { offsetX :: Number        -- Horizontal offset in pixels
  , offsetY :: Number        -- Vertical offset in pixels
  , blur :: Number           -- Blur radius
  , color :: GlowColor
  }

derive instance eqDropShadowEffect :: Eq DropShadowEffect

instance showDropShadowEffect :: Show DropShadowEffect where
  show (DropShadowEffect s) = "(DropShadowEffect blur:" <> show s.blur <> ")"

-- | Box shadow — CSS-style with spread
-- |
-- | Full-featured shadow matching CSS box-shadow semantics. Spread
-- | expands or contracts the shadow before blur. Inset creates inner shadow.
newtype BoxShadowEffect = BoxShadowEffect
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , spread :: Number         -- Shadow expansion/contraction
  , color :: GlowColor
  , inset :: Boolean         -- Inner shadow
  }

derive instance eqBoxShadowEffect :: Eq BoxShadowEffect

instance showBoxShadowEffect :: Show BoxShadowEffect where
  show (BoxShadowEffect s) = "(BoxShadowEffect blur:" <> show s.blur <> ")"

-- | Contact shadow — grounded shadow beneath element
-- |
-- | Creates a shadow that appears where the element "touches" a surface.
-- | Scale controls shadow size relative to element (< 1.0 for perspective).
newtype ContactShadow = ContactShadow
  { blur :: Number
  , opacity :: Number        -- Shadow opacity (0.0-1.0)
  , offsetY :: Number        -- Vertical offset (typically negative)
  , scale :: Number          -- Shadow scale relative to element
  }

derive instance eqContactShadow :: Eq ContactShadow

instance showContactShadow :: Show ContactShadow where
  show (ContactShadow s) = "(ContactShadow blur:" <> show s.blur <> ")"
