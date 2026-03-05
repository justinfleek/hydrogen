-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // badge // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BadgeSemantics — Pure composition of verified pillar atoms for accessibility.
-- |
-- | ## Design Philosophy
-- |
-- | Badge semantics defines WHAT the badge means, not how it looks or behaves.
-- | This enables:
-- | - Screen reader announcements (ARIA live regions)
-- | - Semantic HTML role mapping
-- | - Deterministic UUID5 identity
-- |
-- | ## Badge Types (semantic purpose)
-- |
-- | - Notification: Unread count (messages, alerts)
-- | - Status: Online/offline, active/inactive
-- | - Label: Category tag, version, feature flag
-- | - Count: Numeric indicator (cart items, followers)
-- | - Priority: Urgency level indicator
-- |
-- | ## Pillar Atoms Used
-- |
-- | - Accessibility.* — ARIA roles, live regions, labels
-- | - Identity.* — UUID5 deterministic identity

module Hydrogen.Schema.Element.Badge.Semantics
  ( -- * Badge Semantics Record
    BadgeSemantics
  , defaultSemantics
  
  -- * Badge Purpose
  , BadgePurpose
      ( NotificationBadge
      , StatusBadge
      , LabelBadge
      , CountBadge
      , PriorityBadge
      )
  
  -- * Live Region (for accessibility)
  , LiveRegion
      ( LiveOff
      , LivePolite
      , LiveAssertive
      )
  
  -- * Semantic Variants
  , notificationSemantics
  , statusSemantics
  , labelSemantics
  , countSemantics
  , prioritySemantics
  
  -- * Accessors
  , semPurpose
  , semLabel
  , semLiveRegion
  , semRole
  
  -- * Modifiers
  , setPurpose
  , setLabel
  , setLiveRegion
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Ord (Ordering(LT, GT, EQ))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // badge purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic purpose of the badge.
-- |
-- | Determines ARIA role and announcement behavior.
data BadgePurpose
  = NotificationBadge   -- ^ Unread count (role="status", aria-live="polite")
  | StatusBadge         -- ^ Online/active indicator (role="status")
  | LabelBadge          -- ^ Category/tag (no special ARIA)
  | CountBadge          -- ^ Numeric count (aria-label with count)
  | PriorityBadge       -- ^ Urgency indicator (aria-live="assertive" for critical)

derive instance eqBadgePurpose :: Eq BadgePurpose

instance ordBadgePurpose :: Ord BadgePurpose where
  compare NotificationBadge NotificationBadge = EQ
  compare NotificationBadge _ = LT
  compare StatusBadge NotificationBadge = GT
  compare StatusBadge StatusBadge = EQ
  compare StatusBadge _ = LT
  compare LabelBadge NotificationBadge = GT
  compare LabelBadge StatusBadge = GT
  compare LabelBadge LabelBadge = EQ
  compare LabelBadge _ = LT
  compare CountBadge PriorityBadge = LT
  compare CountBadge CountBadge = EQ
  compare CountBadge _ = GT
  compare PriorityBadge PriorityBadge = EQ
  compare PriorityBadge _ = GT

instance showBadgePurpose :: Show BadgePurpose where
  show NotificationBadge = "NotificationBadge"
  show StatusBadge = "StatusBadge"
  show LabelBadge = "LabelBadge"
  show CountBadge = "CountBadge"
  show PriorityBadge = "PriorityBadge"

-- | Map badge purpose to ARIA role.
purposeToRole :: BadgePurpose -> String
purposeToRole NotificationBadge = "status"
purposeToRole StatusBadge = "status"
purposeToRole LabelBadge = "note"
purposeToRole CountBadge = "status"
purposeToRole PriorityBadge = "alert"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // live region
-- ═════════════════════════════════════════════════════════════════════════════

-- | ARIA live region politeness level.
-- |
-- | Controls how urgently screen readers announce changes.
data LiveRegion
  = LiveOff           -- ^ No announcements
  | LivePolite        -- ^ Announce when convenient (default for notifications)
  | LiveAssertive     -- ^ Interrupt to announce (for urgent/critical)

derive instance eqLiveRegion :: Eq LiveRegion

instance showLiveRegion :: Show LiveRegion where
  show LiveOff = "off"
  show LivePolite = "polite"
  show LiveAssertive = "assertive"

-- | Map badge purpose to default live region.
purposeToLiveRegion :: BadgePurpose -> LiveRegion
purposeToLiveRegion NotificationBadge = LivePolite
purposeToLiveRegion StatusBadge = LivePolite
purposeToLiveRegion LabelBadge = LiveOff
purposeToLiveRegion CountBadge = LivePolite
purposeToLiveRegion PriorityBadge = LiveAssertive

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // badge semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete badge semantics — accessibility and identity.
-- |
-- | ## ARIA Mapping
-- |
-- | - purpose → role attribute
-- | - liveRegion → aria-live attribute
-- | - label → aria-label attribute
-- | - describedBy → aria-describedby attribute
type BadgeSemantics =
  { -- Purpose
    purpose :: BadgePurpose
    
  -- Accessibility
  , label :: String                   -- ^ Accessible label (aria-label)
  , liveRegion :: LiveRegion          -- ^ Live region politeness
  , describedBy :: Maybe String       -- ^ ID of describing element
  , atomic :: Boolean                 -- ^ Announce entire region on change
  , relevant :: String                -- ^ What changes to announce ("additions", "text", "all")
  }

-- | Default semantics — notification badge with polite announcements.
defaultSemantics :: String -> BadgeSemantics
defaultSemantics lbl =
  { purpose: NotificationBadge
  , label: lbl
  , liveRegion: LivePolite
  , describedBy: Nothing
  , atomic: true
  , relevant: "additions text"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // semantic variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Notification badge semantics.
-- |
-- | Announces count changes politely.
notificationSemantics :: String -> BadgeSemantics
notificationSemantics lbl = (defaultSemantics lbl)
  { purpose = NotificationBadge
  , liveRegion = LivePolite
  }

-- | Status badge semantics.
-- |
-- | For online/offline, active/inactive indicators.
statusSemantics :: String -> BadgeSemantics
statusSemantics lbl = (defaultSemantics lbl)
  { purpose = StatusBadge
  , liveRegion = LivePolite
  , relevant = "text"
  }

-- | Label badge semantics.
-- |
-- | For category tags, version badges, feature flags.
-- | No live announcements.
labelSemantics :: String -> BadgeSemantics
labelSemantics lbl = (defaultSemantics lbl)
  { purpose = LabelBadge
  , liveRegion = LiveOff
  }

-- | Count badge semantics.
-- |
-- | For cart items, follower counts, etc.
countSemantics :: String -> BadgeSemantics
countSemantics lbl = (defaultSemantics lbl)
  { purpose = CountBadge
  , liveRegion = LivePolite
  }

-- | Priority badge semantics.
-- |
-- | For urgent/critical notifications.
-- | Uses assertive announcements.
prioritySemantics :: String -> BadgeSemantics
prioritySemantics lbl = (defaultSemantics lbl)
  { purpose = PriorityBadge
  , liveRegion = LiveAssertive
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

semPurpose :: BadgeSemantics -> BadgePurpose
semPurpose s = s.purpose

semLabel :: BadgeSemantics -> String
semLabel s = s.label

semLiveRegion :: BadgeSemantics -> LiveRegion
semLiveRegion s = s.liveRegion

semRole :: BadgeSemantics -> String
semRole s = purposeToRole s.purpose

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setPurpose :: BadgePurpose -> BadgeSemantics -> BadgeSemantics
setPurpose p s = s 
  { purpose = p
  , liveRegion = purposeToLiveRegion p
  }

setLabel :: String -> BadgeSemantics -> BadgeSemantics
setLabel lbl s = s { label = lbl }

setLiveRegion :: LiveRegion -> BadgeSemantics -> BadgeSemantics
setLiveRegion lr s = s { liveRegion = lr }
