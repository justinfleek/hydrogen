-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // element // accordion // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AccordionSemantics — Pure composition of ARIA and accessibility atoms.
-- |
-- | ## Design Philosophy
-- |
-- | Accordion semantics defines WHAT the accordion means, not how it looks or
-- | behaves. This enables:
-- | - Screen reader announcements via ARIA roles and states
-- | - Keyboard navigation patterns
-- | - Focus management
-- | - Live region announcements for state changes
-- |
-- | ## WAI-ARIA Pattern
-- |
-- | Accordion follows the WAI-ARIA Accordion Pattern:
-- | - Container has role="none" or implicit
-- | - Triggers are <button> with aria-expanded and aria-controls
-- | - Content regions have role="region" with aria-labelledby
-- | - Keyboard: Tab moves between triggers, Arrow keys optional
-- |
-- | ## Structure
-- |
-- | ```html
-- | <div class="accordion">
-- |   <h3>                                        <!-- heading level configurable -->
-- |     <button aria-expanded="true"             <!-- trigger -->
-- |             aria-controls="sect1"
-- |             id="accord1">
-- |       Section 1
-- |     </button>
-- |   </h3>
-- |   <div role="region"                         <!-- content -->
-- |        aria-labelledby="accord1"
-- |        id="sect1">
-- |     Content here...
-- |   </div>
-- | </div>
-- | ```

module Hydrogen.Schema.Element.Accordion.Semantics
  ( -- * Accordion Semantics Record
    AccordionSemantics
  , defaultSemantics
  
  -- * Item Semantics
  , AccordionItemSemantics
  , defaultItemSemantics
  
  -- * Heading Level
  , HeadingLevel
      ( H1
      , H2
      , H3
      , H4
      , H5
      , H6
      )
  , headingLevelToInt
  , headingLevelFromInt
  
  -- * Keyboard Navigation
  , KeyboardNavigation
      ( TabOnly
      , ArrowVertical
      , ArrowHomeEnd
      )
  
  -- * Focus Behavior
  , FocusBehavior
      ( FocusManual
      , FocusAutomatic
      , FocusFollowsExpansion
      )
  
  -- * Semantic Variants
  , faqSemantics
  , navigationSemantics
  , disclosureSemantics
  
  -- * Container Accessors
  , semLabel
  , semDescription
  , semHeadingLevel
  , semKeyboardNav
  , semFocusBehavior
  
  -- * Item Accessors
  , itemLabel
  , itemDescription
  , itemControlsId
  
  -- * Container Modifiers
  , setLabel
  , setDescription
  , setHeadingLevel
  , setKeyboardNav
  , setFocusBehavior
  
  -- * Item Modifiers
  , setItemLabel
  , setItemDescription
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
  , (==)
  , (<=)
  , (>=)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Ord (Ordering(LT, GT, EQ))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // heading level
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML heading level for accordion triggers.
-- |
-- | Accordions wrap triggers in heading elements for proper document outline.
-- | Choose based on page structure:
-- | - H2 for main content sections
-- | - H3 for subsections
-- | - H4+ for nested accordions
data HeadingLevel
  = H1
  | H2
  | H3
  | H4
  | H5
  | H6

derive instance eqHeadingLevel :: Eq HeadingLevel

instance ordHeadingLevel :: Ord HeadingLevel where
  compare H1 H1 = EQ
  compare H1 _ = LT
  compare H2 H1 = GT
  compare H2 H2 = EQ
  compare H2 _ = LT
  compare H3 H1 = GT
  compare H3 H2 = GT
  compare H3 H3 = EQ
  compare H3 _ = LT
  compare H4 H5 = LT
  compare H4 H6 = LT
  compare H4 H4 = EQ
  compare H4 _ = GT
  compare H5 H6 = LT
  compare H5 H5 = EQ
  compare H5 _ = GT
  compare H6 H6 = EQ
  compare H6 _ = GT

instance showHeadingLevel :: Show HeadingLevel where
  show H1 = "h1"
  show H2 = "h2"
  show H3 = "h3"
  show H4 = "h4"
  show H5 = "h5"
  show H6 = "h6"

-- | Convert heading level to integer (1-6).
headingLevelToInt :: HeadingLevel -> Int
headingLevelToInt H1 = 1
headingLevelToInt H2 = 2
headingLevelToInt H3 = 3
headingLevelToInt H4 = 4
headingLevelToInt H5 = 5
headingLevelToInt H6 = 6

-- | Convert integer to heading level (clamped to 1-6).
headingLevelFromInt :: Int -> HeadingLevel
headingLevelFromInt n
  | n <= 1 = H1
  | n == 2 = H2
  | n == 3 = H3
  | n == 4 = H4
  | n == 5 = H5
  | otherwise = H6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // keyboard navigation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard navigation pattern for accordion.
-- |
-- | WAI-ARIA allows multiple patterns:
-- | - TabOnly: Only Tab key navigates between triggers (simplest)
-- | - ArrowVertical: Arrow keys move between triggers
-- | - ArrowHomeEnd: Arrow + Home/End keys for full navigation
data KeyboardNavigation
  = TabOnly           -- ^ Tab between triggers (default)
  | ArrowVertical     -- ^ Up/Down arrows between triggers
  | ArrowHomeEnd      -- ^ Arrows + Home/End keys

derive instance eqKeyboardNavigation :: Eq KeyboardNavigation

instance showKeyboardNavigation :: Show KeyboardNavigation where
  show TabOnly = "tab-only"
  show ArrowVertical = "arrow-vertical"
  show ArrowHomeEnd = "arrow-home-end"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focus behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | How focus behaves when expanding/collapsing.
-- |
-- | - Manual: Focus stays where it is (default)
-- | - Automatic: Focus moves to content when expanded
-- | - FollowsExpansion: Focus follows based on which item was triggered
data FocusBehavior
  = FocusManual              -- ^ Focus stays on trigger
  | FocusAutomatic           -- ^ Focus moves to content on expand
  | FocusFollowsExpansion    -- ^ Focus follows expansion state

derive instance eqFocusBehavior :: Eq FocusBehavior

instance showFocusBehavior :: Show FocusBehavior where
  show FocusManual = "manual"
  show FocusAutomatic = "automatic"
  show FocusFollowsExpansion = "follows-expansion"

-- ═══════════════════════════════════════════════════════════════════���═════════
--                                                    // accordion item semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantics for a single accordion item.
-- |
-- | Each item needs:
-- | - Label for the trigger (visible and accessible)
-- | - Optional description
-- | - IDs for aria-controls/aria-labelledby relationship
type AccordionItemSemantics =
  { -- Accessible name
    label :: String
  
  -- Optional description (aria-describedby)
  , description :: Maybe String
  
  -- ID relationships (auto-generated if not provided)
  , triggerId :: Maybe String     -- ID for the trigger button
  , contentId :: Maybe String     -- ID for the content region
  
  -- Content semantics
  , contentRole :: String         -- Usually "region"
  }

-- | Default item semantics with empty label.
defaultItemSemantics :: String -> AccordionItemSemantics
defaultItemSemantics lbl =
  { label: lbl
  , description: Nothing
  , triggerId: Nothing
  , contentId: Nothing
  , contentRole: "region"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // accordion semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete accordion semantics — accessibility configuration.
-- |
-- | This defines the semantic structure that gets rendered as ARIA attributes.
type AccordionSemantics =
  { -- Container semantics
    label :: String                     -- aria-label for the accordion
  , description :: Maybe String         -- aria-describedby
  
  -- Document structure
  , headingLevel :: HeadingLevel        -- What heading level for triggers
  
  -- Keyboard behavior
  , keyboardNav :: KeyboardNavigation
  
  -- Focus behavior
  , focusBehavior :: FocusBehavior
  
  -- Announcements
  , announceExpansion :: Boolean        -- Announce expand/collapse to screen readers
  , announcePolitely :: Boolean         -- Use polite (true) or assertive (false)
  }

-- | Default accordion semantics.
defaultSemantics :: String -> AccordionSemantics
defaultSemantics lbl =
  { label: lbl
  , description: Nothing
  , headingLevel: H3
  , keyboardNav: TabOnly
  , focusBehavior: FocusManual
  , announceExpansion: true
  , announcePolitely: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // semantic variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | FAQ semantics — optimized for frequently asked questions.
-- |
-- | Uses H3 headings, tab-only navigation, announces changes politely.
faqSemantics :: String -> AccordionSemantics
faqSemantics lbl = (defaultSemantics lbl)
  { headingLevel = H3
  , keyboardNav = TabOnly
  , announceExpansion = true
  }

-- | Navigation semantics — for navigation menus.
-- |
-- | Uses H2 headings, arrow key navigation for faster browsing.
navigationSemantics :: String -> AccordionSemantics
navigationSemantics lbl = (defaultSemantics lbl)
  { headingLevel = H2
  , keyboardNav = ArrowVertical
  , focusBehavior = FocusFollowsExpansion
  }

-- | Disclosure semantics — for simple show/hide content.
-- |
-- | Minimal announcement, manual focus.
disclosureSemantics :: String -> AccordionSemantics
disclosureSemantics lbl = (defaultSemantics lbl)
  { headingLevel = H4
  , keyboardNav = TabOnly
  , announceExpansion = false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // container accessors
-- ═════════════════════════════════════════════════════════════════════════════

semLabel :: AccordionSemantics -> String
semLabel s = s.label

semDescription :: AccordionSemantics -> Maybe String
semDescription s = s.description

semHeadingLevel :: AccordionSemantics -> HeadingLevel
semHeadingLevel s = s.headingLevel

semKeyboardNav :: AccordionSemantics -> KeyboardNavigation
semKeyboardNav s = s.keyboardNav

semFocusBehavior :: AccordionSemantics -> FocusBehavior
semFocusBehavior s = s.focusBehavior

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // item accessors
-- ═════════════════════════════════════════════════════════════════════════════

itemLabel :: AccordionItemSemantics -> String
itemLabel i = i.label

itemDescription :: AccordionItemSemantics -> Maybe String
itemDescription i = i.description

itemControlsId :: AccordionItemSemantics -> Maybe String
itemControlsId i = i.contentId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // container modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setLabel :: String -> AccordionSemantics -> AccordionSemantics
setLabel l s = s { label = l }

setDescription :: String -> AccordionSemantics -> AccordionSemantics
setDescription d s = s { description = Just d }

setHeadingLevel :: HeadingLevel -> AccordionSemantics -> AccordionSemantics
setHeadingLevel h s = s { headingLevel = h }

setKeyboardNav :: KeyboardNavigation -> AccordionSemantics -> AccordionSemantics
setKeyboardNav k s = s { keyboardNav = k }

setFocusBehavior :: FocusBehavior -> AccordionSemantics -> AccordionSemantics
setFocusBehavior f s = s { focusBehavior = f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // item modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setItemLabel :: String -> AccordionItemSemantics -> AccordionItemSemantics
setItemLabel l i = i { label = l }

setItemDescription :: String -> AccordionItemSemantics -> AccordionItemSemantics
setItemDescription d i = i { description = Just d }

