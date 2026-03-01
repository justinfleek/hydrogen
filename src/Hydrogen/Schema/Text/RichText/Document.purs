-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // text // richtext // document
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RichText.Document — Document-level operations and serialization.
-- |
-- | This module provides:
-- | - Document manipulation (prepend, append, insert, remove blocks)
-- | - Document traversal (mapBlocks, filterBlocks)
-- | - Document metrics (blockCount)
-- | - Serialization to plain text
-- |
-- | Documents are ordered sequences of blocks representing complete rich text
-- | content. All operations preserve document invariants.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Text.RichText.Types (RichTextDocument, Block, Inline, ListItem)
-- | - Hydrogen.Schema.Text.RichText.Inline (flattenInlinesToText)
-- | - Data.Array
-- | - Data.Maybe
-- | - Data.String (joinWith)

module Hydrogen.Schema.Text.RichText.Document
  ( -- * Document Metrics
    documentBlockCount
  
  -- * Document Traversal
  , mapBlocks
  , filterBlocks
  
  -- * Document Manipulation
  , prependBlock
  , appendBlock
  , insertBlockAt
  , removeBlockAt
  , getBlockAt
  
  -- * Serialization Helpers
  , documentToPlainText
  , blockToPlainText
  , inlineToPlainText
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (#)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

import Hydrogen.Schema.Text.RichText.Types
  ( Block(Paragraph, Heading, CodeBlock, BlockQuote, List, HorizontalRule)
  , Inline
  , ListItem
  , RichTextDocument(RichTextDocument)
  , documentBlocks
  )

import Hydrogen.Schema.Text.RichText.Inline
  ( flattenInlinesToText
  , inlineText
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // document // metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Count blocks in document.
documentBlockCount :: RichTextDocument -> Int
documentBlockCount doc = Array.length (documentBlocks doc)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // document // traversal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over all blocks.
mapBlocks :: (Block -> Block) -> RichTextDocument -> RichTextDocument
mapBlocks f doc = RichTextDocument (map f (documentBlocks doc))

-- | Filter blocks by predicate.
filterBlocks :: (Block -> Boolean) -> RichTextDocument -> RichTextDocument
filterBlocks p doc = RichTextDocument (Array.filter p (documentBlocks doc))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // document // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Prepend a block to the document.
prependBlock :: Block -> RichTextDocument -> RichTextDocument
prependBlock block doc =
  RichTextDocument (Array.cons block (documentBlocks doc))

-- | Append a block to the document.
appendBlock :: Block -> RichTextDocument -> RichTextDocument
appendBlock block doc =
  RichTextDocument (Array.snoc (documentBlocks doc) block)

-- | Insert a block at a specific index.
insertBlockAt :: Int -> Block -> RichTextDocument -> RichTextDocument
insertBlockAt idx block doc =
  let blocks = documentBlocks doc
  in RichTextDocument (Array.insertAt idx block blocks # orDefault blocks)
  where
    orDefault :: forall a. a -> Maybe a -> a
    orDefault def = case _ of
      Just v -> v
      Nothing -> def

-- | Remove a block at a specific index.
removeBlockAt :: Int -> RichTextDocument -> RichTextDocument
removeBlockAt idx doc =
  let blocks = documentBlocks doc
  in RichTextDocument (Array.deleteAt idx blocks # orDefault blocks)
  where
    orDefault :: forall a. a -> Maybe a -> a
    orDefault def = case _ of
      Just v -> v
      Nothing -> def

-- | Get a block at a specific index.
getBlockAt :: Int -> RichTextDocument -> Maybe Block
getBlockAt idx doc = Array.index (documentBlocks doc) idx

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // serialization // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a document to plain text (no formatting).
documentToPlainText :: RichTextDocument -> String
documentToPlainText doc =
  String.joinWith "\n\n" (map blockToPlainText (documentBlocks doc))

-- | Convert a block to plain text.
blockToPlainText :: Block -> String
blockToPlainText = case _ of
  Paragraph inlines -> flattenInlinesToText inlines
  Heading _ inlines -> flattenInlinesToText inlines
  CodeBlock _ content -> content
  BlockQuote blocks -> String.joinWith "\n" (map blockToPlainText blocks)
  List _ items -> String.joinWith "\n" (map listItemToPlainText items)
  HorizontalRule -> "---"
  where
    listItemToPlainText :: ListItem -> String
    listItemToPlainText item = flattenInlinesToText item.content

-- | Convert an inline to plain text.
inlineToPlainText :: Inline -> String
inlineToPlainText = inlineText
