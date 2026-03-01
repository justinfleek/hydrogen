-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // text // richtext // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RichText.Types — Core type definitions for rich text documents.
-- |
-- | This module defines the foundational types for the rich text system:
-- | - URL: Wrapped string for hyperlinks
-- | - Language: Bounded enumeration of programming languages
-- | - HeadingLevel: H1-H6 heading levels
-- | - ListType: Ordered, unordered, and checkbox lists
-- | - ListItem: Individual list entries with optional nesting
-- | - Inline: Character-level formatting (bold, italic, links, etc.)
-- | - Block: Paragraph-level structure (paragraphs, headings, code blocks)
-- | - RichTextDocument: Complete document container
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Generic)
-- | - Data.Array (for length in Show instances)
-- | - Data.Maybe (for optional fields)
-- | - Data.Generic.Rep (for deriving)
-- | - Data.String (for toLower, length, null)

module Hydrogen.Schema.Text.RichText.Types
  ( -- * URL Type
    URL(..)
  , url
  , unwrapURL
  
  -- * Language Type
  , Language(..)
  , languageFromString
  , languageToString
  
  -- * Heading Level
  , HeadingLevel(..)
  
  -- * List Types
  , ListType(..)
  , ListItem
  
  -- * Inline Type
  , Inline(..)
  
  -- * Block Type
  , Block(..)
  
  -- * Document Type
  , RichTextDocument(..)
  , emptyDocument
  , documentBlocks
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.String (length) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // url
-- ═════════════════════════════════════════════════════════════════════════════

-- | URL for links and external references.
-- |
-- | Wrapped String with semantic meaning. URLs are not validated at construction
-- | time — validation happens at the boundary (HTTP client, renderer).
newtype URL = URL String

derive instance eqURL :: Eq URL
derive instance ordURL :: Ord URL
derive instance genericURL :: Generic URL _

instance showURL :: Show URL where
  show (URL u) = "URL(" <> show u <> ")"

-- | Create a URL from a string.
url :: String -> URL
url = URL

-- | Extract the URL string.
unwrapURL :: URL -> String
unwrapURL (URL u) = u

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // language
-- ═════════════════════════════════════════════════════════════════════════════

-- | Programming language for code blocks.
-- |
-- | Bounded enumeration of supported languages. Adding new languages requires
-- | adding to this ADT — no stringly-typed escape hatches.
data Language
  = PlainText
  | JavaScript
  | TypeScript
  | PureScript
  | Haskell
  | Lean
  | Python
  | Rust
  | Go
  | C
  | Cpp
  | CSharp
  | Java
  | Kotlin
  | Swift
  | Ruby
  | PHP
  | Elixir
  | Erlang
  | Clojure
  | Scala
  | FSharp
  | OCaml
  | Lua
  | R
  | Julia
  | Zig
  | Nim
  | Crystal
  | Dart
  | HTML
  | CSS
  | SCSS
  | SASS
  | Less
  | JSON
  | YAML
  | TOML
  | XML
  | Markdown
  | LaTeX
  | Bash
  | Shell
  | PowerShell
  | SQL
  | GraphQL
  | Protobuf
  | Dockerfile
  | Makefile
  | Nix
  | Dhall

derive instance eqLanguage :: Eq Language
derive instance ordLanguage :: Ord Language
derive instance genericLanguage :: Generic Language _

instance showLanguage :: Show Language where
  show = genericShow

-- | Parse language from string (case-insensitive).
languageFromString :: String -> Maybe Language
languageFromString s = case String.toLower s of
  "plaintext" -> Just PlainText
  "text" -> Just PlainText
  "javascript" -> Just JavaScript
  "js" -> Just JavaScript
  "typescript" -> Just TypeScript
  "ts" -> Just TypeScript
  "purescript" -> Just PureScript
  "purs" -> Just PureScript
  "haskell" -> Just Haskell
  "hs" -> Just Haskell
  "lean" -> Just Lean
  "lean4" -> Just Lean
  "python" -> Just Python
  "py" -> Just Python
  "rust" -> Just Rust
  "rs" -> Just Rust
  "go" -> Just Go
  "golang" -> Just Go
  "c" -> Just C
  "cpp" -> Just Cpp
  "c++" -> Just Cpp
  "csharp" -> Just CSharp
  "cs" -> Just CSharp
  "c#" -> Just CSharp
  "java" -> Just Java
  "kotlin" -> Just Kotlin
  "kt" -> Just Kotlin
  "swift" -> Just Swift
  "ruby" -> Just Ruby
  "rb" -> Just Ruby
  "php" -> Just PHP
  "elixir" -> Just Elixir
  "ex" -> Just Elixir
  "erlang" -> Just Erlang
  "erl" -> Just Erlang
  "clojure" -> Just Clojure
  "clj" -> Just Clojure
  "scala" -> Just Scala
  "fsharp" -> Just FSharp
  "fs" -> Just FSharp
  "f#" -> Just FSharp
  "ocaml" -> Just OCaml
  "ml" -> Just OCaml
  "lua" -> Just Lua
  "r" -> Just R
  "julia" -> Just Julia
  "jl" -> Just Julia
  "zig" -> Just Zig
  "nim" -> Just Nim
  "crystal" -> Just Crystal
  "cr" -> Just Crystal
  "dart" -> Just Dart
  "html" -> Just HTML
  "css" -> Just CSS
  "scss" -> Just SCSS
  "sass" -> Just SASS
  "less" -> Just Less
  "json" -> Just JSON
  "yaml" -> Just YAML
  "yml" -> Just YAML
  "toml" -> Just TOML
  "xml" -> Just XML
  "markdown" -> Just Markdown
  "md" -> Just Markdown
  "latex" -> Just LaTeX
  "tex" -> Just LaTeX
  "bash" -> Just Bash
  "shell" -> Just Shell
  "sh" -> Just Shell
  "zsh" -> Just Shell
  "powershell" -> Just PowerShell
  "ps1" -> Just PowerShell
  "sql" -> Just SQL
  "graphql" -> Just GraphQL
  "gql" -> Just GraphQL
  "protobuf" -> Just Protobuf
  "proto" -> Just Protobuf
  "dockerfile" -> Just Dockerfile
  "docker" -> Just Dockerfile
  "makefile" -> Just Makefile
  "make" -> Just Makefile
  "nix" -> Just Nix
  "dhall" -> Just Dhall
  _ -> Nothing

-- | Convert language to canonical string representation.
languageToString :: Language -> String
languageToString = case _ of
  PlainText -> "plaintext"
  JavaScript -> "javascript"
  TypeScript -> "typescript"
  PureScript -> "purescript"
  Haskell -> "haskell"
  Lean -> "lean"
  Python -> "python"
  Rust -> "rust"
  Go -> "go"
  C -> "c"
  Cpp -> "cpp"
  CSharp -> "csharp"
  Java -> "java"
  Kotlin -> "kotlin"
  Swift -> "swift"
  Ruby -> "ruby"
  PHP -> "php"
  Elixir -> "elixir"
  Erlang -> "erlang"
  Clojure -> "clojure"
  Scala -> "scala"
  FSharp -> "fsharp"
  OCaml -> "ocaml"
  Lua -> "lua"
  R -> "r"
  Julia -> "julia"
  Zig -> "zig"
  Nim -> "nim"
  Crystal -> "crystal"
  Dart -> "dart"
  HTML -> "html"
  CSS -> "css"
  SCSS -> "scss"
  SASS -> "sass"
  Less -> "less"
  JSON -> "json"
  YAML -> "yaml"
  TOML -> "toml"
  XML -> "xml"
  Markdown -> "markdown"
  LaTeX -> "latex"
  Bash -> "bash"
  Shell -> "shell"
  PowerShell -> "powershell"
  SQL -> "sql"
  GraphQL -> "graphql"
  Protobuf -> "protobuf"
  Dockerfile -> "dockerfile"
  Makefile -> "makefile"
  Nix -> "nix"
  Dhall -> "dhall"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // heading level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Heading level (H1-H6).
-- |
-- | Bounded enumeration matching HTML heading levels.
data HeadingLevel
  = H1
  | H2
  | H3
  | H4
  | H5
  | H6

derive instance eqHeadingLevel :: Eq HeadingLevel
derive instance ordHeadingLevel :: Ord HeadingLevel
derive instance genericHeadingLevel :: Generic HeadingLevel _

instance showHeadingLevel :: Show HeadingLevel where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // list type
-- ═════════════════════════════════════════════════════════════════════════════

-- | List ordering type.
data ListType
  = Bullet      -- ^ Unordered list (ul)
  | Numbered    -- ^ Ordered list (ol)
  | Checkbox    -- ^ Task list with checkboxes

derive instance eqListType :: Eq ListType
derive instance ordListType :: Ord ListType
derive instance genericListType :: Generic ListType _

instance showListType :: Show ListType where
  show = genericShow

-- | A single list item.
-- |
-- | List items contain inline content and optionally nested lists.
-- | The checked field is only relevant for Checkbox lists.
type ListItem =
  { content :: Array Inline
  , checked :: Maybe Boolean    -- ^ For checkbox lists
  , children :: Array Block     -- ^ Nested blocks (for nested lists)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // inline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inline elements — character-level formatting within a block.
-- |
-- | Inlines can be nested (bold text containing italic text) but the nesting
-- | is always well-formed. This is enforced by the ADT structure.
data Inline
  = TextNode String                   -- ^ Plain text
  | Bold (Array Inline)               -- ^ Bold formatting
  | Italic (Array Inline)             -- ^ Italic formatting
  | Code String                       -- ^ Inline code (monospace)
  | Link URL (Array Inline)           -- ^ Hyperlink with visible text
  | Strikethrough (Array Inline)      -- ^ Strikethrough formatting
  | Underline (Array Inline)          -- ^ Underline formatting
  | Subscript (Array Inline)          -- ^ Subscript text
  | Superscript (Array Inline)        -- ^ Superscript text

derive instance eqInline :: Eq Inline

instance showInline :: Show Inline where
  show (TextNode s) = "TextNode " <> show s
  show (Bold inlines) = "Bold [" <> show (Array.length inlines) <> " items]"
  show (Italic inlines) = "Italic [" <> show (Array.length inlines) <> " items]"
  show (Code s) = "Code " <> show s
  show (Link u inlines) = "Link " <> show u <> " [" <> show (Array.length inlines) <> " items]"
  show (Strikethrough inlines) = "Strikethrough [" <> show (Array.length inlines) <> " items]"
  show (Underline inlines) = "Underline [" <> show (Array.length inlines) <> " items]"
  show (Subscript inlines) = "Subscript [" <> show (Array.length inlines) <> " items]"
  show (Superscript inlines) = "Superscript [" <> show (Array.length inlines) <> " items]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // block
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block elements — paragraph-level structure.
-- |
-- | Blocks are the top-level structural elements of a document.
data Block
  = Paragraph (Array Inline)              -- ^ Standard paragraph
  | Heading HeadingLevel (Array Inline)   -- ^ H1-H6 heading
  | CodeBlock Language String             -- ^ Fenced code block
  | BlockQuote (Array Block)              -- ^ Quoted content (can contain blocks)
  | List ListType (Array ListItem)        -- ^ Ordered or unordered list
  | HorizontalRule                        -- ^ Thematic break (hr)

derive instance eqBlock :: Eq Block

instance showBlock :: Show Block where
  show (Paragraph inlines) = "Paragraph [" <> show (Array.length inlines) <> " inlines]"
  show (Heading level inlines) = "Heading " <> show level <> " [" <> show (Array.length inlines) <> " inlines]"
  show (CodeBlock lang code') = "CodeBlock " <> show lang <> " [" <> show (String.length code') <> " chars]"
  show (BlockQuote blocks) = "BlockQuote [" <> show (Array.length blocks) <> " blocks]"
  show (List listType items) = "List " <> show listType <> " [" <> show (Array.length items) <> " items]"
  show HorizontalRule = "HorizontalRule"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // rich text // document
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete rich text document.
-- |
-- | Documents are ordered sequences of blocks. The structure is normalized:
-- | - No empty blocks (except empty paragraphs which may be intentional)
-- | - No adjacent TextNodes (they are merged)
-- | - No redundant nesting (bold inside bold)
newtype RichTextDocument = RichTextDocument (Array Block)

derive instance eqRichTextDocument :: Eq RichTextDocument
derive instance genericRichTextDocument :: Generic RichTextDocument _

instance showRichTextDocument :: Show RichTextDocument where
  show = genericShow

-- | Empty document with no blocks.
emptyDocument :: RichTextDocument
emptyDocument = RichTextDocument []

-- | Get all blocks from a document.
documentBlocks :: RichTextDocument -> Array Block
documentBlocks (RichTextDocument blocks) = blocks
