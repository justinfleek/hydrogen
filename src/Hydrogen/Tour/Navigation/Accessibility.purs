-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // tour // navigation // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accessibility Configuration for Tours
-- |
-- | This module provides accessibility types and configuration:
-- | - ARIA roles and labels
-- | - Live regions for screen readers
-- | - Focus trap configuration
-- | - Screen reader announcements
module Hydrogen.Tour.Navigation.Accessibility
  ( -- * Accessibility Configuration
    A11yConfig
  , LiveRegion(..)
  , defaultA11yConfig
    -- * Screen Reader
  , screenReaderAnnouncement
    -- * Focus Trap
  , FocusTrapConfig
  , InitialFocus(..)
  , focusTrapConfig
  ) where

import Prelude (class Eq, class Show, (==), (<>), show)

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accessibility configuration
type A11yConfig =
  { role :: String
    -- ^ ARIA role for tour container
  , ariaLabel :: String
  , ariaModal :: Boolean
  , liveRegion :: LiveRegion
    -- ^ For screen reader announcements
  , focusTrap :: Boolean
  , restoreFocus :: Boolean
    -- ^ Return focus to original element after tour
  }

-- | Live region assertiveness
data LiveRegion
  = LiveOff
  | LivePolite
  | LiveAssertive

derive instance eqLiveRegion :: Eq LiveRegion
derive instance genericLiveRegion :: Generic LiveRegion _

instance showLiveRegion :: Show LiveRegion where
  show = genericShow

-- | Default accessibility configuration
defaultA11yConfig :: A11yConfig
defaultA11yConfig =
  { role: "dialog"
  , ariaLabel: "Product tour"
  , ariaModal: true
  , liveRegion: LivePolite
  , focusTrap: true
  , restoreFocus: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // screen reader
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate screen reader announcement
screenReaderAnnouncement :: Int -> Int -> String -> String
screenReaderAnnouncement current total title =
  "Step " <> show current <> " of " <> show total <> 
  (if title == "" then "" else ": " <> title)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // focus trap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus trap configuration
type FocusTrapConfig =
  { enabled :: Boolean
  , returnFocusOnDeactivate :: Boolean
  , initialFocus :: InitialFocus
  , escapeDeactivates :: Boolean
  }

-- | Initial focus target
data InitialFocus
  = FocusFirstTabbable
  | FocusContainer
  | FocusPrimaryButton
  | FocusNone

derive instance eqInitialFocus :: Eq InitialFocus
derive instance genericInitialFocus :: Generic InitialFocus _

instance showInitialFocus :: Show InitialFocus where
  show = genericShow

-- | Default focus trap configuration
focusTrapConfig :: FocusTrapConfig
focusTrapConfig =
  { enabled: true
  , returnFocusOnDeactivate: true
  , initialFocus: FocusPrimaryButton
  , escapeDeactivates: true
  }
