-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // reactive // feedback // popover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Popover - rich floating content molecule.
-- |
-- | Popovers display richer content than tooltips, including
-- | interactive elements, titles, and structured information.
-- | They persist until explicitly dismissed.

module Hydrogen.Schema.Reactive.Feedback.Popover
  ( -- * Popover Trigger
    PopoverTrigger(..)
  -- * Popover (Molecule)
  , Popover
  , popover
  , popoverWithTitle
  , isPopoverOpen
  , openPopover
  , closePopover
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Feedback.Tooltip (TooltipPlacement)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // popover molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Popover trigger mode
data PopoverTrigger
  = PopoverClick      -- ^ Open on click
  | PopoverHover      -- ^ Open on hover
  | PopoverFocus      -- ^ Open on focus
  | PopoverManual     -- ^ Controlled externally

derive instance eqPopoverTrigger :: Eq PopoverTrigger
derive instance ordPopoverTrigger :: Ord PopoverTrigger

instance showPopoverTrigger :: Show PopoverTrigger where
  show PopoverClick = "click"
  show PopoverHover = "hover"
  show PopoverFocus = "focus"
  show PopoverManual = "manual"

-- | Popover configuration (richer than tooltip)
type Popover =
  { id :: String                  -- ^ Unique identifier
  , placement :: TooltipPlacement -- ^ Reuse tooltip placement
  , trigger :: PopoverTrigger     -- ^ How to trigger
  , title :: Maybe String         -- ^ Optional title
  , closeButton :: Boolean        -- ^ Show close button
  , closeOnClickOutside :: Boolean -- ^ Close when clicking outside
  , closeOnEscape :: Boolean      -- ^ Close on Escape key
  , offset :: Number              -- ^ Distance from trigger (px)
  , isOpen :: Boolean             -- ^ Current open state
  }

-- | Create popover
popover :: String -> TooltipPlacement -> PopoverTrigger -> Popover
popover id placement trigger =
  { id
  , placement
  , trigger
  , title: Nothing
  , closeButton: true
  , closeOnClickOutside: true
  , closeOnEscape: true
  , offset: 8.0
  , isOpen: false
  }

-- | Popover with title
popoverWithTitle :: String -> String -> TooltipPlacement -> Popover
popoverWithTitle id title placement =
  (popover id placement PopoverClick)
    { title = Just title }

-- | Is popover open?
isPopoverOpen :: Popover -> Boolean
isPopoverOpen p = p.isOpen

-- | Open popover
openPopover :: Popover -> Popover
openPopover p = p { isOpen = true }

-- | Close popover
closePopover :: Popover -> Popover
closePopover p = p { isOpen = false }
