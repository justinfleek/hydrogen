-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // text // richtext // block
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RichText.Block — Block element constructors and operations.
-- |
-- | This module provides:
-- | - Smart constructors for block elements (paragraph, heading, codeBlock, etc.)
-- | - Operations on block elements (isEmpty, prependInline, appendInline)
-- | - Block content extraction
-- |
-- | Block elements represent paragraph-level structure in documents.
-- | They contain inline elements for character-level formatting.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Text.RichText.Types (Block, Inline, HeadingLevel, ListType, ListItem, Language)
-- | - Data.Array
-- | - Data.Maybe
-- | - Data.String (null)

module Hydrogen.Schema.Text.RichText.Block
  ( -- * Block Constructors
    paragraph
  , heading
  , codeBlock
  , blockQuote
  , bulletList
  , numberedList
  , horizontalRule
  
  -- * Block Operations
  , blockToInlines
  , blockIsEmpty
  , prependInline
  , appendInline
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

import Hydrogen.Schema.Text.RichText.Types
  ( Block(Paragraph, Heading, CodeBlock, BlockQuote, List, HorizontalRule)
  , HeadingLevel
  , Inline
  , Language
  , ListItem
  , ListType(Bullet, Numbered)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // block // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a paragraph block.
paragraph :: Array Inline -> Block
paragraph = Paragraph

-- | Create a heading block.
heading :: HeadingLevel -> Array Inline -> Block
heading = Heading

-- | Create a code block.
codeBlock :: Language -> String -> Block
codeBlock = CodeBlock

-- | Create a block quote.
blockQuote :: Array Block -> Block
blockQuote = BlockQuote

-- | Create a bullet (unordered) list.
bulletList :: Array ListItem -> Block
bulletList = List Bullet

-- | Create a numbered (ordered) list.
numberedList :: Array ListItem -> Block
numberedList = List Numbered

-- | Create a horizontal rule.
horizontalRule :: Block
horizontalRule = HorizontalRule

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // block // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract inline content from a block (if applicable).
-- |
-- | CodeBlocks and HorizontalRules return Nothing.
blockToInlines :: Block -> Maybe (Array Inline)
blockToInlines = case _ of
  Paragraph inlines -> Just inlines
  Heading _ inlines -> Just inlines
  CodeBlock _ _ -> Nothing
  BlockQuote _ -> Nothing
  List _ _ -> Nothing
  HorizontalRule -> Nothing

-- | Check if a block is empty.
blockIsEmpty :: Block -> Boolean
blockIsEmpty = case _ of
  Paragraph inlines -> Array.null inlines
  Heading _ inlines -> Array.null inlines
  CodeBlock _ content -> String.null content
  BlockQuote blocks -> Array.null blocks
  List _ items -> Array.null items
  HorizontalRule -> false

-- | Prepend an inline to a block's content.
prependInline :: Inline -> Block -> Block
prependInline inline = case _ of
  Paragraph inlines -> Paragraph (Array.cons inline inlines)
  Heading level inlines -> Heading level (Array.cons inline inlines)
  other -> other

-- | Append an inline to a block's content.
appendInline :: Inline -> Block -> Block
appendInline inline = case _ of
  Paragraph inlines -> Paragraph (Array.snoc inlines inline)
  Heading level inlines -> Heading level (Array.snoc inlines inline)
  other -> other
