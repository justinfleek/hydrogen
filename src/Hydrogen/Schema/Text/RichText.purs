-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // text // richtext
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RichText — Pure document model for rich text editing.
-- |
-- | ## Design Philosophy
-- |
-- | Rich text documents are hierarchical data structures, NOT HTML strings.
-- | This module provides a complete, typed model for rich text that can be:
-- | - Rendered to any target (DOM, static HTML, canvas, terminal)
-- | - Serialized/deserialized without information loss
-- | - Transformed algebraically (fold, map, filter)
-- | - Validated at compile time for structural correctness
-- |
-- | ## Architecture
-- |
-- | Documents contain Blocks (paragraph-level elements).
-- | Blocks contain Inlines (character-level formatting).
-- | This two-level hierarchy matches most rich text editors (ProseMirror, Slate).
-- |
-- | ```
-- | RichTextDocument
-- |   └── Block (Paragraph, Heading, CodeBlock, etc.)
-- |         └── Inline (TextNode, Bold, Italic, Link, etc.)
-- | ```
-- |
-- | ## Why Not HTML?
-- |
-- | HTML strings are unbounded and ambiguous. Two different HTML strings can
-- | represent the same visual output. Our model is canonical: same content =
-- | same representation. This enables deterministic diffing and collaboration.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Types: Core type definitions (URL, Language, Inline, Block, etc.)
-- | - Inline: Inline constructors and operations
-- | - Block: Block constructors and operations
-- | - Document: Document operations and serialization

module Hydrogen.Schema.Text.RichText
  ( module Types
  , module Inline
  , module Block
  , module Document
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Text.RichText.Types
  ( Block(Paragraph, Heading, CodeBlock, BlockQuote, List, HorizontalRule)
  , HeadingLevel(H1, H2, H3, H4, H5, H6)
  , Inline(TextNode, Bold, Italic, Code, Link, Strikethrough, Underline, Subscript, Superscript)
  , Language(PlainText, JavaScript, TypeScript, PureScript, Haskell, Lean, Python, Rust, Go, C, Cpp, CSharp, Java, Kotlin, Swift, Ruby, PHP, Elixir, Erlang, Clojure, Scala, FSharp, OCaml, Lua, R, Julia, Zig, Nim, Crystal, Dart, HTML, CSS, SCSS, SASS, Less, JSON, YAML, TOML, XML, Markdown, LaTeX, Bash, Shell, PowerShell, SQL, GraphQL, Protobuf, Dockerfile, Makefile, Nix, Dhall)
  , ListItem
  , ListType(Bullet, Numbered, Checkbox)
  , RichTextDocument(RichTextDocument)
  , URL(URL)
  , documentBlocks
  , emptyDocument
  , languageFromString
  , languageToString
  , unwrapURL
  , url
  ) as Types

import Hydrogen.Schema.Text.RichText.Inline
  ( bold
  , code
  , flattenInlines
  , flattenInlinesToText
  , inlineLength
  , inlineText
  , italic
  , link
  , strikethrough
  , subscript
  , superscript
  , textNode
  , underline
  ) as Inline

import Hydrogen.Schema.Text.RichText.Block
  ( appendInline
  , blockIsEmpty
  , blockQuote
  , blockToInlines
  , bulletList
  , codeBlock
  , heading
  , horizontalRule
  , numberedList
  , paragraph
  , prependInline
  ) as Block

import Hydrogen.Schema.Text.RichText.Document
  ( appendBlock
  , blockToPlainText
  , documentBlockCount
  , documentToPlainText
  , filterBlocks
  , getBlockAt
  , inlineToPlainText
  , insertBlockAt
  , mapBlocks
  , prependBlock
  , removeBlockAt
  ) as Document
