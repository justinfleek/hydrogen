-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // graph // slot-content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SlotContent — Content types that can appear in node slots.
-- |
-- | ## Overview
-- |
-- | Defines slot content and text content types with builders.
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe

module Hydrogen.Schema.Graph.NodeContent.SlotContent
  ( -- * Slot Content
    SlotContent(ContentText, ContentIcon, ContentBadge, ContentAction, ContentProgress, ContentImage, ContentCustom)
  , textContent
  , iconContent
  , badgeContent
  , actionContent
  , progressContent
  , customContent
  
  -- * Text Content
  , TextContent
  , simpleText
  , richText
  , editableText
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Graph.NodeContent.ContentTypes
  ( BadgeContent
  , ActionContent
  , ProgressContent
  , badgeCount
  , buttonAction
  , progressBar
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // slot content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content type that can appear in a slot
data SlotContent
  = ContentText TextContent
  | ContentIcon String              -- ^ Icon identifier
  | ContentBadge BadgeContent
  | ContentAction ActionContent
  | ContentProgress ProgressContent
  | ContentImage String             -- ^ Image URL
  | ContentCustom String            -- ^ Custom Element key

derive instance eqSlotContent :: Eq SlotContent

instance showSlotContent :: Show SlotContent where
  show (ContentText _) = "text"
  show (ContentIcon _) = "icon"
  show (ContentBadge _) = "badge"
  show (ContentAction _) = "action"
  show (ContentProgress _) = "progress"
  show (ContentImage _) = "image"
  show (ContentCustom _) = "custom"

-- | Create text slot content
textContent :: String -> SlotContent
textContent s = ContentText (simpleText s)

-- | Create icon slot content
iconContent :: String -> SlotContent
iconContent = ContentIcon

-- | Create badge slot content
badgeContent :: Int -> SlotContent
badgeContent n = ContentBadge (badgeCount n)

-- | Create action slot content
actionContent :: String -> String -> SlotContent
actionContent id label = ContentAction (buttonAction id label)

-- | Create progress slot content
progressContent :: Number -> SlotContent
progressContent pct = ContentProgress (progressBar pct)

-- | Create custom slot content
customContent :: String -> SlotContent
customContent = ContentCustom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text content with formatting options
type TextContent =
  { text :: String
  , editable :: Boolean
  , truncate :: Boolean
  , maxLines :: Int
  , highlight :: Maybe String    -- ^ Highlight matching text
  , fontWeight :: Maybe String
  , fontSize :: Maybe String
  , color :: Maybe String
  }

-- | Simple text content
simpleText :: String -> TextContent
simpleText s =
  { text: s
  , editable: false
  , truncate: true
  , maxLines: 1
  , highlight: Nothing
  , fontWeight: Nothing
  , fontSize: Nothing
  , color: Nothing
  }

-- | Rich text with styling
richText :: String -> String -> String -> TextContent
richText s weight size = (simpleText s)
  { fontWeight = Just weight
  , fontSize = Just size
  }

-- | Editable text
editableText :: String -> TextContent
editableText s = (simpleText s) { editable = true }
