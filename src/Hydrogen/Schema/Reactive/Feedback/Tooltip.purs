-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // reactive // feedback // tooltip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tooltip - hover hint molecule.
-- |
-- | Tooltips provide brief contextual information when users
-- | hover or focus on an element. They are non-blocking and
-- | disappear when the trigger loses focus.

module Hydrogen.Schema.Reactive.Feedback.Tooltip
  ( -- * Tooltip Placement
    TooltipPlacement(TooltipTop, TooltipTopStart, TooltipTopEnd, TooltipBottom, TooltipBottomStart, TooltipBottomEnd, TooltipLeft, TooltipLeftStart, TooltipLeftEnd, TooltipRight, TooltipRightStart, TooltipRightEnd)
  -- * Tooltip (Molecule)
  , Tooltip
  , tooltip
  , simpleTooltip
  , interactiveTooltip
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // tooltip molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tooltip placement relative to trigger
data TooltipPlacement
  = TooltipTop
  | TooltipTopStart
  | TooltipTopEnd
  | TooltipBottom
  | TooltipBottomStart
  | TooltipBottomEnd
  | TooltipLeft
  | TooltipLeftStart
  | TooltipLeftEnd
  | TooltipRight
  | TooltipRightStart
  | TooltipRightEnd

derive instance eqTooltipPlacement :: Eq TooltipPlacement
derive instance ordTooltipPlacement :: Ord TooltipPlacement

instance showTooltipPlacement :: Show TooltipPlacement where
  show TooltipTop = "top"
  show TooltipTopStart = "top-start"
  show TooltipTopEnd = "top-end"
  show TooltipBottom = "bottom"
  show TooltipBottomStart = "bottom-start"
  show TooltipBottomEnd = "bottom-end"
  show TooltipLeft = "left"
  show TooltipLeftStart = "left-start"
  show TooltipLeftEnd = "left-end"
  show TooltipRight = "right"
  show TooltipRightStart = "right-start"
  show TooltipRightEnd = "right-end"

-- | Tooltip configuration
type Tooltip =
  { content :: String             -- ^ Tooltip text
  , placement :: TooltipPlacement -- ^ Where to show relative to trigger
  , delay :: Number               -- ^ Delay before showing (ms)
  , hideDelay :: Number           -- ^ Delay before hiding (ms)
  , maxWidth :: Number            -- ^ Maximum width (px)
  , arrow :: Boolean              -- ^ Show arrow pointing to trigger
  , interactive :: Boolean        -- ^ Can tooltip be interacted with
  }

-- | Create tooltip
tooltip :: String -> TooltipPlacement -> Tooltip
tooltip content placement =
  { content
  , placement
  , delay: 200.0
  , hideDelay: 100.0
  , maxWidth: 300.0
  , arrow: true
  , interactive: false
  }

-- | Simple tooltip (top placement)
simpleTooltip :: String -> Tooltip
simpleTooltip content = tooltip content TooltipTop

-- | Interactive tooltip (can be hovered)
interactiveTooltip :: String -> TooltipPlacement -> Tooltip
interactiveTooltip content placement = (tooltip content placement)
  { interactive = true
  , hideDelay = 300.0
  }
