-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // announce
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Screen reader announcements
-- |
-- | ARIA live regions for dynamic content announcements.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.A11y.Announce as Announce
-- |
-- | -- Polite announcement (doesn't interrupt)
-- | Announce.liveRegion Announce.Polite []
-- |   [ HH.text "Item added to cart" ]
-- |
-- | -- Assertive announcement (interrupts)
-- | Announce.liveRegion Announce.Assertive []
-- |   [ HH.text "Error: Invalid input" ]
-- |
-- | -- Status message
-- | Announce.status [ HH.text "Loading..." ]
-- |
-- | -- Alert message
-- | Announce.alert [ HH.text "Changes saved" ]
-- | ```
module Hydrogen.A11y.Announce
  ( -- * Live Regions
    liveRegion
  , Politeness(Off, Polite, Assertive)
    -- * Semantic Announcements
  , status
  , alert
  , log
  , timer
  , marquee
    -- * Visibility
  , visuallyHidden
  , srOnly
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // live regions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Live region politeness level
data Politeness
  = Off         -- No announcements
  | Polite      -- Wait for silence before announcing
  | Assertive   -- Interrupt current speech

derive instance eqPoliteness :: Eq Politeness

politenessValue :: Politeness -> String
politenessValue = case _ of
  Off -> "off"
  Polite -> "polite"
  Assertive -> "assertive"

type LiveRegionProps = { className :: String }
type LiveRegionProp = LiveRegionProps -> LiveRegionProps

defaultProps :: LiveRegionProps
defaultProps = { className: "" }

-- | ARIA live region for dynamic announcements
-- |
-- | Content changes are announced to screen readers.
liveRegion :: forall w i. Politeness -> Array LiveRegionProp -> Array (HH.HTML w i) -> HH.HTML w i
liveRegion politeness propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.live (politenessValue politeness)
    , ARIA.atomic "true"
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // semantic announcements
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Status message (polite announcement)
-- |
-- | For non-critical status updates.
status :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
status children =
  HH.div
    [ ARIA.role "status"
    , ARIA.live "polite"
    , ARIA.atomic "true"
    ]
    children

-- | Alert message (assertive announcement)
-- |
-- | For important, time-sensitive information.
alert :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
alert children =
  HH.div
    [ ARIA.role "alert"
    , ARIA.live "assertive"
    , ARIA.atomic "true"
    ]
    children

-- | Log region (polite, not atomic)
-- |
-- | For chat logs, activity feeds, etc.
log :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
log children =
  HH.div
    [ ARIA.role "log"
    , ARIA.live "polite"
    , ARIA.atomic "false"
    ]
    children

-- | Timer region
-- |
-- | For countdown timers.
timer :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
timer children =
  HH.div
    [ ARIA.role "timer"
    , ARIA.live "off"
    ]
    children

-- | Marquee region (auto-updating)
-- |
-- | For stock tickers, news scrollers, etc.
marquee :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
marquee children =
  HH.div
    [ ARIA.role "marquee"
    , ARIA.live "off"
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // visibility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visually hide content but keep it accessible to screen readers
-- |
-- | Use for labels, descriptions, or additional context.
visuallyHidden :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
visuallyHidden children =
  HH.span
    [ cls [ "sr-only" ] ]
    children

-- | Tailwind sr-only class string
srOnly :: String
srOnly = "sr-only"
