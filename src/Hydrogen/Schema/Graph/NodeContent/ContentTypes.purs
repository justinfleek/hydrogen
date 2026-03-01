-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // graph // content-types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ContentTypes — Badge, Action, and Progress content types.
-- |
-- | ## Overview
-- |
-- | Defines content types for interactive elements:
-- | - BadgeContent: Counters, status indicators, dots
-- | - ActionContent: Buttons, icon actions, menus
-- | - ProgressContent: Bars, circles, sparklines
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe

module Hydrogen.Schema.Graph.NodeContent.ContentTypes
  ( -- * Badge Content
    BadgeContent
  , badgeCount
  , badgeStatus
  , badgeDot
  
  -- * Action Content
  , ActionContent
  , buttonAction
  , iconAction
  , menuAction
  
  -- * Progress Content
  , ProgressContent
  , progressBar
  , progressCircle
  , progressSparkline
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // badge content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Badge/indicator content
type BadgeContent =
  { badgeType :: String          -- ^ "count" | "status" | "dot"
  , value :: Maybe Int
  , status :: Maybe String       -- ^ "success" | "warning" | "error" | "info"
  , label :: Maybe String
  , color :: Maybe String
  , maxCount :: Int              -- ^ Show "99+" if exceeded
  }

-- | Count badge
badgeCount :: Int -> BadgeContent
badgeCount n =
  { badgeType: "count"
  , value: Just n
  , status: Nothing
  , label: Nothing
  , color: Nothing
  , maxCount: 99
  }

-- | Status badge
badgeStatus :: String -> String -> BadgeContent
badgeStatus status label =
  { badgeType: "status"
  , value: Nothing
  , status: Just status
  , label: Just label
  , color: Nothing
  , maxCount: 99
  }

-- | Simple dot badge
badgeDot :: String -> BadgeContent
badgeDot color =
  { badgeType: "dot"
  , value: Nothing
  , status: Nothing
  , label: Nothing
  , color: Just color
  , maxCount: 99
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // action content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Action button/menu content
type ActionContent =
  { actionType :: String         -- ^ "button" | "icon" | "menu"
  , actionId :: String
  , label :: Maybe String
  , icon :: Maybe String
  , disabled :: Boolean
  , tooltip :: Maybe String
  }

-- | Button action
buttonAction :: String -> String -> ActionContent
buttonAction id label =
  { actionType: "button"
  , actionId: id
  , label: Just label
  , icon: Nothing
  , disabled: false
  , tooltip: Nothing
  }

-- | Icon-only action
iconAction :: String -> String -> ActionContent
iconAction id icon =
  { actionType: "icon"
  , actionId: id
  , label: Nothing
  , icon: Just icon
  , disabled: false
  , tooltip: Nothing
  }

-- | Menu action
menuAction :: String -> String -> ActionContent
menuAction id label =
  { actionType: "menu"
  , actionId: id
  , label: Just label
  , icon: Just "more"
  , disabled: false
  , tooltip: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // progress content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress indicator content
type ProgressContent =
  { progressType :: String       -- ^ "bar" | "circle" | "sparkline"
  , value :: Number              -- ^ 0-100 percentage
  , showLabel :: Boolean
  , color :: Maybe String
  , secondaryColor :: Maybe String
  , sparklineData :: Array Number  -- ^ For sparkline type
  }

-- | Progress bar
progressBar :: Number -> ProgressContent
progressBar pct =
  { progressType: "bar"
  , value: pct
  , showLabel: true
  , color: Nothing
  , secondaryColor: Nothing
  , sparklineData: []
  }

-- | Circular progress
progressCircle :: Number -> ProgressContent
progressCircle pct = (progressBar pct) { progressType = "circle" }

-- | Sparkline chart
progressSparkline :: Array Number -> ProgressContent
progressSparkline data_ =
  { progressType: "sparkline"
  , value: 0.0
  , showLabel: false
  , color: Nothing
  , secondaryColor: Nothing
  , sparklineData: data_
  }
