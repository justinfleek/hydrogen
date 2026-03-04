-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // element // button // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonAppearance — visual atoms for button surface and elevation.
-- |
-- | ## Atoms Included
-- |
-- | - Fill (solid, gradient, noise)
-- | - Border (stroke width, color, style)
-- | - Shadow (layered box shadows)
-- | - Opacity

module Hydrogen.Schema.Element.Button.Appearance
  ( -- * Button Appearance Record
    ButtonAppearance
  , defaultAppearance
    -- * Appearance Variants
  , primaryAppearance
  , secondaryAppearance
  , outlineAppearance
  , ghostAppearance
  , dangerAppearance
  , successAppearance
  , ctaAppearance
  , mediaAppearance
  , fabAppearance
    -- * Accessors
  , appFill
  , appShadow
  , appBorderWidth
  , appBorderColor
  , appOpacity
    -- * Modifiers
  , setFill
  , setOpacity
  , setBorder
  , setShadow
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Surface.Fill (Fill, fillSolid, fillNone) as Fill
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow, noShadow, shadow, elevatedShadow) as Shadow
import Hydrogen.Schema.Color.RGB (RGB, rgb) as Color

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // button appearance
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Appearance atoms for button surface.
-- |
-- | Visual properties: fill, border, shadow, opacity.
type ButtonAppearance =
  { -- Surface
    fill :: Fill.Fill                   -- ^ Background fill
  , opacity :: Number                   -- ^ Overall opacity (0-1)
    -- Border
  , borderWidth :: Number               -- ^ Border width (0 = no border)
  , borderColor :: Maybe Color.RGB      -- ^ Border color (Nothing = transparent)
    -- Elevation
  , shadow :: Shadow.LayeredShadow      -- ^ Shadow layers
  }

-- | Default button appearance.
-- |
-- | Solid blue fill, no border, no shadow, full opacity.
defaultAppearance :: ButtonAppearance
defaultAppearance =
  { fill: Fill.fillSolid (Color.rgb 59 130 246)  -- Blue 500
  , opacity: 1.0
  , borderWidth: 0.0
  , borderColor: Nothing
  , shadow: Shadow.noShadow
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get fill.
appFill :: ButtonAppearance -> Fill.Fill
appFill a = a.fill

-- | Get shadow.
appShadow :: ButtonAppearance -> Shadow.LayeredShadow
appShadow a = a.shadow

-- | Get border width.
appBorderWidth :: ButtonAppearance -> Number
appBorderWidth a = a.borderWidth

-- | Get border color.
appBorderColor :: ButtonAppearance -> Maybe Color.RGB
appBorderColor a = a.borderColor

-- | Get opacity.
appOpacity :: ButtonAppearance -> Number
appOpacity a = a.opacity

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // appearance variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Primary button appearance (default blue).
-- |
-- | Solid fill, subtle shadow for depth.
primaryAppearance :: ButtonAppearance
primaryAppearance = defaultAppearance
  { shadow = Shadow.elevatedShadow 2
  }

-- | Secondary button appearance (gray/neutral).
-- |
-- | Less emphasis than primary, for secondary actions.
secondaryAppearance :: ButtonAppearance
secondaryAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 107 114 128)  -- Gray 500
  }

-- | Outline button appearance (border only).
-- |
-- | No fill, visible border, ghost-like with defined edge.
outlineAppearance :: ButtonAppearance
outlineAppearance = defaultAppearance
  { fill = Fill.fillNone
  , borderWidth = 1.0
  , borderColor = Just (Color.rgb 59 130 246)  -- Blue 500
  }

-- | Ghost button appearance (minimal).
-- |
-- | No fill, no border, just text. Hover reveals interaction.
ghostAppearance :: ButtonAppearance
ghostAppearance = defaultAppearance
  { fill = Fill.fillNone
  , borderWidth = 0.0
  , borderColor = Nothing
  }

-- | Danger button appearance (destructive actions).
-- |
-- | Red fill, signals caution/irreversible action.
dangerAppearance :: ButtonAppearance
dangerAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 239 68 68)  -- Red 500
  }

-- | Success button appearance (confirmations).
-- |
-- | Green fill, signals positive action/completion.
successAppearance :: ButtonAppearance
successAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 34 197 94)  -- Green 500
  }

-- | CTA (Call-to-Action) appearance.
-- |
-- | High-contrast, elevated, attention-grabbing.
-- | Uses amber/orange for urgency without danger semantics.
ctaAppearance :: ButtonAppearance
ctaAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 245 158 11)  -- Amber 500
  , shadow = Shadow.elevatedShadow 4
  }

-- | Media control button appearance.
-- |
-- | Circular, icon-centric, often transparent or glass.
mediaAppearance :: ButtonAppearance
mediaAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 31 31 31)  -- Near black
  , opacity = 0.9
  }

-- | FAB (Floating Action Button) appearance.
-- |
-- | Prominent elevation, circular (handled in geometry), strong shadow.
fabAppearance :: ButtonAppearance
fabAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 236 72 153)  -- Pink 500
  , shadow = Shadow.elevatedShadow 6
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set fill.
setFill :: Fill.Fill -> ButtonAppearance -> ButtonAppearance
setFill f a = a { fill = f }

-- | Set opacity (clamped to 0.0-1.0).
setOpacity :: Number -> ButtonAppearance -> ButtonAppearance
setOpacity o a = a { opacity = Bounded.clampNumber 0.0 1.0 o }

-- | Set border width and color.
setBorder :: Number -> Color.RGB -> ButtonAppearance -> ButtonAppearance
setBorder width color a = a
  { borderWidth = Bounded.clampNumber 0.0 10.0 width
  , borderColor = Just color
  }

-- | Set shadow.
setShadow :: Shadow.LayeredShadow -> ButtonAppearance -> ButtonAppearance
setShadow s a = a { shadow = s }
