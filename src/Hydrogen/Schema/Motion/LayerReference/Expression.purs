-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // layer-reference // expression
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Expression links and mask modes.
-- |
-- | ## Expression Links
-- |
-- | Expression links allow one property to be driven by another property,
-- | optionally with an expression that transforms the value.
-- |
-- | - Direct link: Source property = target property value
-- | - Expression: Source property = expression(target property)
-- |
-- | ## Mask Modes
-- |
-- | Mask compositing modes determine how multiple masks combine:
-- | - Add: Combine mask areas
-- | - Subtract: Remove mask area from existing
-- | - Intersect: Keep only overlapping areas
-- | - Lighten/Darken: Per-pixel max/min alpha
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (PropertyRef)

module Hydrogen.Schema.Motion.LayerReference.Expression
  ( -- * Expression Link
    ExpressionLink(ExpressionLink)
  , mkExpressionLink
  , expressionLinkSource
  , expressionLinkTarget
  , expressionLinkExpression
  
  -- * Mask Mode
  , MaskMode(MMNone, MMAdd, MMSubtract, MMIntersect, MMLighten, MMDarken, MMDifference)
  , allMaskModes
  , maskModeToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<>)
  )

import Hydrogen.Schema.Motion.LayerReference.Types (PropertyRef)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // expression // link
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expression link between properties.
-- |
-- | Allows one property to be driven by a value or expression
-- | referencing another property.
newtype ExpressionLink = ExpressionLink
  { sourceProperty :: PropertyRef    -- Property being driven
  , targetProperty :: PropertyRef    -- Property providing the value
  , expression :: String             -- Expression code (empty = direct link)
  , enabled :: Boolean
  }

derive instance eqExpressionLink :: Eq ExpressionLink

instance showExpressionLink :: Show ExpressionLink where
  show (ExpressionLink el) = 
    show el.sourceProperty <> " = " <> 
    (if el.expression == "" then show el.targetProperty else "expr()")

-- | Create an expression link.
mkExpressionLink :: PropertyRef -> PropertyRef -> String -> ExpressionLink
mkExpressionLink sourceProperty targetProperty expression = ExpressionLink
  { sourceProperty, targetProperty, expression, enabled: true }

-- | Get source property of expression link.
expressionLinkSource :: ExpressionLink -> PropertyRef
expressionLinkSource (ExpressionLink el) = el.sourceProperty

-- | Get target property of expression link.
expressionLinkTarget :: ExpressionLink -> PropertyRef
expressionLinkTarget (ExpressionLink el) = el.targetProperty

-- | Get expression code.
expressionLinkExpression :: ExpressionLink -> String
expressionLinkExpression (ExpressionLink el) = el.expression

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mask // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask compositing mode.
-- |
-- | Determines how multiple masks combine.
data MaskMode
  = MMNone        -- Mask disabled
  | MMAdd         -- Add to existing mask
  | MMSubtract    -- Subtract from existing mask
  | MMIntersect   -- Intersect with existing mask
  | MMLighten     -- Lighten (max alpha)
  | MMDarken      -- Darken (min alpha)
  | MMDifference  -- Difference of masks

derive instance eqMaskMode :: Eq MaskMode
derive instance ordMaskMode :: Ord MaskMode

instance showMaskMode :: Show MaskMode where
  show = maskModeToString

-- | All mask modes for enumeration.
allMaskModes :: Array MaskMode
allMaskModes = [ MMNone, MMAdd, MMSubtract, MMIntersect, MMLighten, MMDarken, MMDifference ]

-- | Convert mask mode to string.
maskModeToString :: MaskMode -> String
maskModeToString MMNone = "none"
maskModeToString MMAdd = "add"
maskModeToString MMSubtract = "subtract"
maskModeToString MMIntersect = "intersect"
maskModeToString MMLighten = "lighten"
maskModeToString MMDarken = "darken"
maskModeToString MMDifference = "difference"
