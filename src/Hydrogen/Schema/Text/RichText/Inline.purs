-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // text // richtext // inline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RichText.Inline — Inline element constructors and operations.
-- |
-- | This module provides:
-- | - Smart constructors for inline elements (textNode, bold, italic, etc.)
-- | - Operations on inline elements (text extraction, length, flattening)
-- |
-- | Inline elements represent character-level formatting within blocks.
-- | They can be nested (e.g., bold containing italic) but the nesting is
-- | always well-formed, enforced by the ADT structure.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Text.RichText.Types (Inline, URL)
-- | - Data.Array
-- | - Data.Foldable (foldl)
-- | - Data.String (length, null)

module Hydrogen.Schema.Text.RichText.Inline
  ( -- * Inline Constructors
    textNode
  , bold
  , italic
  , code
  , link
  , strikethrough
  , underline
  , subscript
  , superscript
  
  -- * Inline Operations
  , inlineText
  , inlineLength
  , flattenInlines
  , flattenInlinesToText
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Foldable (foldl)
import Data.String as String
import Data.String (length) as String

import Hydrogen.Schema.Text.RichText.Types
  ( Inline(TextNode, Bold, Italic, Code, Link, Strikethrough, Underline, Subscript, Superscript)
  , URL
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // inline // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a plain text node.
textNode :: String -> Inline
textNode = TextNode

-- | Create bold text.
bold :: Array Inline -> Inline
bold = Bold

-- | Create italic text.
italic :: Array Inline -> Inline
italic = Italic

-- | Create inline code.
code :: String -> Inline
code = Code

-- | Create a link.
link :: URL -> Array Inline -> Inline
link = Link

-- | Create strikethrough text.
strikethrough :: Array Inline -> Inline
strikethrough = Strikethrough

-- | Create underlined text.
underline :: Array Inline -> Inline
underline = Underline

-- | Create subscript text.
subscript :: Array Inline -> Inline
subscript = Subscript

-- | Create superscript text.
superscript :: Array Inline -> Inline
superscript = Superscript

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // inline // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract plain text from an inline element.
inlineText :: Inline -> String
inlineText = case _ of
  TextNode s -> s
  Bold inlines -> flattenInlinesToText inlines
  Italic inlines -> flattenInlinesToText inlines
  Code s -> s
  Link _ inlines -> flattenInlinesToText inlines
  Strikethrough inlines -> flattenInlinesToText inlines
  Underline inlines -> flattenInlinesToText inlines
  Subscript inlines -> flattenInlinesToText inlines
  Superscript inlines -> flattenInlinesToText inlines

-- | Get the text length of an inline element.
inlineLength :: Inline -> Int
inlineLength inline = String.length (inlineText inline)

-- | Flatten nested inlines to plain text.
flattenInlinesToText :: Array Inline -> String
flattenInlinesToText = foldl (\acc i -> acc <> inlineText i) ""

-- | Flatten nested inlines to an array of TextNodes.
-- |
-- | All formatting is stripped, leaving only the text content.
flattenInlines :: Array Inline -> Array Inline
flattenInlines inlines =
  let text = flattenInlinesToText inlines
  in if String.null text then [] else [ TextNode text ]
