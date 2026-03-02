-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // reactive // feedback // overlay
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Overlay components - drawer and sheet molecules.
-- |
-- | Drawers slide in from screen edges to provide navigation
-- | or secondary content. Sheets slide up from the bottom
-- | (mobile pattern) with multiple snap points.

module Hydrogen.Schema.Reactive.Feedback.Overlay
  ( -- * Drawer (Molecule)
    DrawerPosition(DrawerLeft, DrawerRight, DrawerTop, DrawerBottom)
  , Drawer
  , drawer
  , navigationDrawer
  , sidePanelDrawer
  , isDrawerOpen
  , openDrawer
  , closeDrawer
  , toggleDrawer
  -- * Sheet (Molecule)
  , SheetSnapPoint(SheetMinimized, SheetPartial, SheetExpanded, SheetCustom)
  , Sheet
  , sheet
  , standardSheet
  , multiDetentSheet
  , isSheetOpen
  , openSheet
  , closeSheet
  , snapSheet
  ) where

import Prelude

import Data.Maybe (Maybe(Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drawer molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drawer position (which edge it slides from)
data DrawerPosition
  = DrawerLeft
  | DrawerRight
  | DrawerTop
  | DrawerBottom

derive instance eqDrawerPosition :: Eq DrawerPosition
derive instance ordDrawerPosition :: Ord DrawerPosition

instance showDrawerPosition :: Show DrawerPosition where
  show DrawerLeft = "left"
  show DrawerRight = "right"
  show DrawerTop = "top"
  show DrawerBottom = "bottom"

-- | Drawer configuration
type Drawer =
  { id :: String                  -- ^ Unique identifier
  , position :: DrawerPosition    -- ^ Which edge
  , size :: Number                -- ^ Width (left/right) or height (top/bottom) in px
  , title :: Maybe String         -- ^ Optional title
  , hasOverlay :: Boolean         -- ^ Show backdrop overlay
  , closeOnOverlayClick :: Boolean -- ^ Close when clicking overlay
  , closeOnEscape :: Boolean      -- ^ Close on Escape key
  , isOpen :: Boolean             -- ^ Current open state
  , isPush :: Boolean             -- ^ Push content vs overlay
  }

-- | Create drawer
drawer :: String -> DrawerPosition -> Number -> Drawer
drawer id position size =
  { id
  , position
  , size
  , title: Nothing
  , hasOverlay: true
  , closeOnOverlayClick: true
  , closeOnEscape: true
  , isOpen: false
  , isPush: false
  }

-- | Navigation drawer (left, 280px)
navigationDrawer :: String -> Drawer
navigationDrawer id = drawer id DrawerLeft 280.0

-- | Side panel drawer (right, 400px)
sidePanelDrawer :: String -> Drawer
sidePanelDrawer id = drawer id DrawerRight 400.0

-- | Is drawer open?
isDrawerOpen :: Drawer -> Boolean
isDrawerOpen d = d.isOpen

-- | Open drawer
openDrawer :: Drawer -> Drawer
openDrawer d = d { isOpen = true }

-- | Close drawer
closeDrawer :: Drawer -> Drawer
closeDrawer d = d { isOpen = false }

-- | Toggle drawer
toggleDrawer :: Drawer -> Drawer
toggleDrawer d = d { isOpen = not d.isOpen }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sheet molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheet snap point (height detents)
data SheetSnapPoint
  = SheetMinimized    -- ^ Just peek (e.g., 100px)
  | SheetPartial      -- ^ Half height
  | SheetExpanded     -- ^ Full height (minus safe area)
  | SheetCustom Number -- ^ Custom height in pixels

derive instance eqSheetSnapPoint :: Eq SheetSnapPoint

instance showSheetSnapPoint :: Show SheetSnapPoint where
  show SheetMinimized = "minimized"
  show SheetPartial = "partial"
  show SheetExpanded = "expanded"
  show (SheetCustom h) = "custom(" <> show h <> "px)"

-- | Bottom sheet configuration (mobile pattern)
type Sheet =
  { id :: String                      -- ^ Unique identifier
  , title :: Maybe String             -- ^ Optional title
  , snapPoints :: Array SheetSnapPoint -- ^ Available snap heights
  , currentSnap :: SheetSnapPoint     -- ^ Current snap position
  , hasOverlay :: Boolean             -- ^ Show backdrop
  , dismissible :: Boolean            -- ^ Can swipe down to dismiss
  , hasHandle :: Boolean              -- ^ Show drag handle
  , isOpen :: Boolean                 -- ^ Current open state
  }

-- | Create sheet
sheet :: String -> Array SheetSnapPoint -> Sheet
sheet id snapPoints =
  { id
  , title: Nothing
  , snapPoints
  , currentSnap: SheetPartial
  , hasOverlay: true
  , dismissible: true
  , hasHandle: true
  , isOpen: false
  }

-- | Standard bottom sheet (partial/expanded)
standardSheet :: String -> Sheet
standardSheet id = sheet id [SheetPartial, SheetExpanded]

-- | Multi-detent sheet (minimized/partial/expanded)
multiDetentSheet :: String -> Sheet
multiDetentSheet id = sheet id [SheetMinimized, SheetPartial, SheetExpanded]

-- | Is sheet open?
isSheetOpen :: Sheet -> Boolean
isSheetOpen s = s.isOpen

-- | Open sheet to snap point
openSheet :: SheetSnapPoint -> Sheet -> Sheet
openSheet snap s = s { isOpen = true, currentSnap = snap }

-- | Close sheet
closeSheet :: Sheet -> Sheet
closeSheet s = s { isOpen = false }

-- | Snap sheet to point
snapSheet :: SheetSnapPoint -> Sheet -> Sheet
snapSheet snap s = s { currentSnap = snap }
