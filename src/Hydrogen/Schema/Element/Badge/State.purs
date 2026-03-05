-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // element // badge // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BadgeState — Interaction and data state atoms for badge indicators.
-- |
-- | ## Design Philosophy
-- |
-- | Badge state describes the CURRENT DATA AND VISIBILITY STATE. Unlike buttons
-- | which have interaction states (pressed, hovered), badges are primarily
-- | DATA INDICATORS with presence/absence semantics.
-- |
-- | Key state dimensions:
-- | - Visibility: Is the badge shown? (hidden when count=0, dismissed, etc.)
-- | - Count: Numeric value for notification badges (0-999, clamped)
-- | - Urgency: Priority level affecting attention behavior
-- | - Seen: Has the user acknowledged this badge?
-- | - Animating: Is an attention animation in progress?
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - VisibleFlag — Badge is rendered
-- | - AnimatingFlag — Pulse/glow animation in progress
-- |
-- | ## State Machine
-- |
-- | Badge visibility transitions:
-- | - Hidden → Visible (new notification arrives)
-- | - Visible → Hidden (count reaches 0, user dismisses)
-- | - Unseen → Seen (user interacts with parent element)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.Flags (verified boolean atoms)
-- | - Hydrogen.Schema.Bounded (clamping utilities)
-- |
-- | ## Dependents
-- |
-- | - Hydrogen.Schema.Element.Badge (compound type)
-- | - Behavior layer uses these for animation triggers

module Hydrogen.Schema.Element.Badge.State
  ( -- * Badge Element State Record
    BadgeElementState
  , defaultState
  , hiddenState
  , visibleState
  , notificationState
  
  -- * Count Type (bounded 0-999)
  , BadgeCount
  , badgeCount
  , unwrapCount
  , incrementCount
  , decrementCount
  , zeroCount
  , maxCount
  
  -- * Urgency Level
  , Urgency(Low, Medium, High, Critical)
  , urgencyToNumber
  
  -- * State Accessors
  , isVisible
  , isSeen
  , isAnimating
  , getCount
  , getUrgency
  , shouldPulse
  
  -- * State Modifiers
  , setVisible
  , setCount
  , setUrgency
  , setSeen
  , setAnimating
  , dismiss
  , markSeen
  
  -- * Re-exports from Reactive.Flags
  , module Hydrogen.Schema.Reactive.Flags
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
  , not
  , (&&)
  , (||)
  , (<>)
  , (>)
  , (<)
  , (+)
  , (-)
  , (>=)
  )

import Data.Ord (Ordering(LT, GT, EQ))

import Hydrogen.Schema.Reactive.Flags
  ( VisibleFlag(VisibleFlag)
  , AnimatingFlag(AnimatingFlag)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // badge count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded count value for notification badges.
-- |
-- | ## Bounds
-- |
-- | - Minimum: 0 (no notifications)
-- | - Maximum: 999 (displays as "999+" in UI)
-- |
-- | Values outside this range are clamped.
newtype BadgeCount = BadgeCount Int

derive instance eqBadgeCount :: Eq BadgeCount

instance ordBadgeCount :: Ord BadgeCount where
  compare (BadgeCount a) (BadgeCount b) = compare a b

instance showBadgeCount :: Show BadgeCount where
  show (BadgeCount n) = "(BadgeCount " <> show n <> ")"

-- | Create a badge count, clamped to 0-999.
badgeCount :: Int -> BadgeCount
badgeCount n
  | n < 0 = BadgeCount 0
  | n > 999 = BadgeCount 999
  | true = BadgeCount n

-- | Extract the raw count value.
unwrapCount :: BadgeCount -> Int
unwrapCount (BadgeCount n) = n

-- | Increment count by 1, clamped to max.
incrementCount :: BadgeCount -> BadgeCount
incrementCount (BadgeCount n) = badgeCount (n + 1)

-- | Decrement count by 1, clamped to 0.
decrementCount :: BadgeCount -> BadgeCount
decrementCount (BadgeCount n) = badgeCount (n - 1)

-- | Zero count.
zeroCount :: BadgeCount
zeroCount = BadgeCount 0

-- | Maximum displayable count.
maxCount :: BadgeCount
maxCount = BadgeCount 999

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // urgency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Urgency level affecting badge attention behavior.
-- |
-- | Higher urgency = more aggressive attention effects.
-- |
-- | - Low: Static badge, no animation
-- | - Medium: Subtle pulse on appear
-- | - High: Continuous pulse, stronger glow
-- | - Critical: Rapid pulse, maximum attention
data Urgency
  = Low        -- ^ No attention animation
  | Medium     -- ^ Subtle pulse on appear
  | High       -- ^ Continuous pulse
  | Critical   -- ^ Maximum attention (rapid pulse, glow)

derive instance eqUrgency :: Eq Urgency

instance ordUrgency :: Ord Urgency where
  compare Low Low = EQ
  compare Low _ = LT
  compare Medium Low = GT
  compare Medium Medium = EQ
  compare Medium _ = LT
  compare High Low = GT
  compare High Medium = GT
  compare High High = EQ
  compare High Critical = LT
  compare Critical Critical = EQ
  compare Critical _ = GT

instance showUrgency :: Show Urgency where
  show Low = "Low"
  show Medium = "Medium"
  show High = "High"
  show Critical = "Critical"

-- | Convert urgency to numeric value (0.0-1.0).
-- |
-- | Useful for interpolating animation intensity.
urgencyToNumber :: Urgency -> Number
urgencyToNumber Low = 0.0
urgencyToNumber Medium = 0.33
urgencyToNumber High = 0.66
urgencyToNumber Critical = 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // badge element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete badge element state — data and visibility flags.
-- |
-- | ## Verified Bounded Types
-- |
-- | - visible: VisibleFlag — Is badge rendered?
-- | - count: BadgeCount — Notification count (0-999)
-- | - urgency: Urgency — Attention level
-- | - seen: Boolean — Has user acknowledged?
-- | - animating: AnimatingFlag — Animation in progress
-- |
-- | ## Usage
-- |
-- | These flags drive visual state in the Appearance and Behavior layers:
-- | - visible → render/hide badge
-- | - count → display number or dot
-- | - urgency → animation intensity
-- | - seen → reduce attention effects
-- | - animating → don't interrupt animations
type BadgeElementState =
  { -- Visibility
    visible :: VisibleFlag        -- ^ Is badge rendered?
  -- Data
  , count :: BadgeCount           -- ^ Notification count (0-999)
  , urgency :: Urgency            -- ^ Attention priority
  -- Acknowledgment
  , seen :: Boolean               -- ^ User has seen this badge
  -- Animation
  , animating :: AnimatingFlag    -- ^ Animation in progress
  }

-- | Default badge state — visible, no count, low urgency.
-- |
-- | Suitable for status badges (dots, labels) without count.
defaultState :: BadgeElementState
defaultState =
  { visible: VisibleFlag true
  , count: zeroCount
  , urgency: Low
  , seen: false
  , animating: AnimatingFlag false
  }

-- | Hidden state — badge not rendered.
hiddenState :: BadgeElementState
hiddenState = defaultState { visible = VisibleFlag false }

-- | Visible state — badge rendered with default appearance.
visibleState :: BadgeElementState
visibleState = defaultState

-- | Notification state — visible with count and medium urgency.
-- |
-- | Creates a badge suitable for unread message counts.
notificationState :: Int -> BadgeElementState
notificationState n = defaultState
  { count = badgeCount n
  , urgency = if n > 10 then High else Medium
  , seen = false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the badge visible?
isVisible :: BadgeElementState -> Boolean
isVisible s = case s.visible of
  VisibleFlag b -> b

-- | Has the badge been seen/acknowledged?
isSeen :: BadgeElementState -> Boolean
isSeen s = s.seen

-- | Is an animation in progress?
isAnimating :: BadgeElementState -> Boolean
isAnimating s = case s.animating of
  AnimatingFlag b -> b

-- | Get the badge count.
getCount :: BadgeElementState -> Int
getCount s = unwrapCount s.count

-- | Get the urgency level.
getUrgency :: BadgeElementState -> Urgency
getUrgency s = s.urgency

-- | Should the badge pulse for attention?
-- |
-- | True when: visible AND (unseen OR urgency >= High)
shouldPulse :: BadgeElementState -> Boolean
shouldPulse s =
  isVisible s && (not s.seen || s.urgency >= High)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set visibility.
setVisible :: Boolean -> BadgeElementState -> BadgeElementState
setVisible b s = s { visible = VisibleFlag b }

-- | Set count (clamped to 0-999).
setCount :: Int -> BadgeElementState -> BadgeElementState
setCount n s = s { count = badgeCount n }

-- | Set urgency level.
setUrgency :: Urgency -> BadgeElementState -> BadgeElementState
setUrgency u s = s { urgency = u }

-- | Set seen flag.
setSeen :: Boolean -> BadgeElementState -> BadgeElementState
setSeen b s = s { seen = b }

-- | Set animating flag.
setAnimating :: Boolean -> BadgeElementState -> BadgeElementState
setAnimating b s = s { animating = AnimatingFlag b }

-- | Dismiss the badge — hide and mark seen.
dismiss :: BadgeElementState -> BadgeElementState
dismiss s = s
  { visible = VisibleFlag false
  , seen = true
  }

-- | Mark badge as seen — reduce attention effects.
markSeen :: BadgeElementState -> BadgeElementState
markSeen s = s { seen = true }
