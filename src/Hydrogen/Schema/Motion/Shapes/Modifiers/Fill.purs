-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // motion // shapes // modifiers // fill
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fill modifier properties.
-- |
-- | Fills a shape with a solid color. All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Fill
  ( -- * Fill
    FillProps
  , fillProps
  , defaultFill
  ) where

import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Motion.Shapes (FillRule(FRNonzero))
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill modifier properties.
-- |
-- | Fills a shape with a solid color.
type FillProps =
  { color :: RGB           -- ^ Fill color
  , opacity :: Percent     -- ^ Fill opacity (0-100%)
  , fillRule :: FillRule   -- ^ Nonzero or Evenodd
  }

-- | Create FillProps.
fillProps
  :: RGB
  -> Number     -- ^ Opacity (%)
  -> FillRule
  -> FillProps
fillProps c o r =
  { color: c
  , opacity: percent o
  , fillRule: r
  }

-- | Default Fill: white, fully opaque.
defaultFill :: FillProps
defaultFill =
  { color: rgb 255 255 255
  , opacity: percent 100.0
  , fillRule: FRNonzero
  }
