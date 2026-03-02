━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                   // 26 // text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Text Pillar

Rich text documents, code editing, text selection, and edit commands.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Text/`
- **Files**: 14 modules
- **Lines**: 3,366 total
- **Key features**: Rich text document model, code editor model, multi-cursor
  selection, syntax tokens, edit commands, undo/redo infrastructure

## Purpose

Text provides bounded, deterministic primitives for:
- Rich text documents (paragraphs, headings, lists, code blocks)
- Inline formatting (bold, italic, code, links, strikethrough)
- Code documents (line-oriented, syntax-aware)
- Syntax tokens (35 token types for highlighting)
- Text selection (anchor/focus model, multi-cursor support)
- Edit commands (pure data describing operations)
- Code folding, indentation, line endings, diagnostics

## Architecture

Two parallel document models serve different use cases:

**Rich Text** — Block/inline hierarchy for prose editing:
```
RichTextDocument
  └── Block (Paragraph, Heading, CodeBlock, List, etc.)
        └── Inline (TextNode, Bold, Italic, Link, etc.)
```

**Code** — Line-oriented model for code editing:
```
CodeDocument
  └── CodeLine (content, tokens, line number)
        └── Token (type, start, end, text)
```

Both share the same Selection system for cursor/selection management.

────────────────────────────────────────────────────────────────────────────────
                                                          // selection // atoms
────────────────────────────────────────────────────────────────────────────────

## Selection Atoms

Bounded indices for addressing positions in documents.

### BlockIndex

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| BlockIndex | Int | 0 | 65535 | clamps | Block position in rich text document |

```purescript
newtype BlockIndex = BlockIndex Int

blockIndex :: Int -> BlockIndex
unwrapBlockIndex :: BlockIndex -> Int
```

### CharOffset

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| CharOffset | Int | 0 | 16777215 | clamps | Character position within block (~16M) |

```purescript
newtype CharOffset = CharOffset Int

charOffset :: Int -> CharOffset
unwrapCharOffset :: CharOffset -> Int
```

### LineNumber

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| LineNumber | Int | 0 | 1048575 | clamps | Line position in code document (~1M) |

```purescript
newtype LineNumber = LineNumber Int

lineNumber :: Int -> LineNumber
unwrapLineNumber :: LineNumber -> Int
```

### Column

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Column | Int | 0 | 16383 | clamps | Character position within line (~16K) |

```purescript
newtype Column = Column Int

column :: Int -> Column
unwrapColumn :: Column -> Int
```

────────────────────────────────────────────────────────────────────────────────
                                                      // selection // molecules
────────────────────────────────────────────────────────────────────────────────

## Position Types

### Position (Rich Text)

Address within a rich text document.

```purescript
type Position =
  { blockIndex :: BlockIndex
  , offset :: CharOffset
  }

position :: Int -> Int -> Position
positionStart :: Position  -- block 0, offset 0
comparePositions :: Position -> Position -> Ordering
```

### CodePosition

Address within a code document.

```purescript
type CodePosition =
  { line :: LineNumber
  , column :: Column
  }

codePosition :: Int -> Int -> CodePosition
codePositionStart :: CodePosition  -- line 0, column 0
compareCodePositions :: CodePosition -> CodePosition -> Ordering
```

## Selection Types

### Selection (Rich Text)

Text selection with anchor and focus.

```purescript
type Selection =
  { anchor :: Position    -- where selection started
  , focus :: Position     -- where selection ends (cursor)
  }
```

**Key insight:** When anchor equals focus, the selection is collapsed (a cursor).
When they differ, text between them is selected.

**Operations:**
- `selection` — Create selection from anchor and focus
- `cursor` — Create collapsed selection at position
- `cursorAt` — Create cursor at block and offset
- `selectionIsCollapsed` — Check if no text selected
- `selectionIsForward` — Anchor before focus
- `selectionIsBackward` — Focus before anchor
- `normalizeSelection` — Ensure anchor <= focus
- `extendSelection` — Extend to new focus position
- `collapseToAnchor` — Collapse to anchor
- `collapseToFocus` — Collapse to focus

### CodeSelection

Selection for code documents.

```purescript
type CodeSelection =
  { anchor :: CodePosition
  , focus :: CodePosition
  }

codeSelection :: CodePosition -> CodePosition -> CodeSelection
codeCursor :: CodePosition -> CodeSelection
codeCursorAt :: Int -> Int -> CodeSelection
```

### MultiSelection

Multiple simultaneous selections for multi-cursor editing.

```purescript
newtype MultiSelection = MultiSelection (Array Selection)
```

**Invariant:** Array is never empty; first element is primary.

**Operations:**
- `singleSelection` — Create with one selection
- `addSelection` — Add selection (new selections at end)
- `removeSelection` — Remove by index (won't remove last)
- `primarySelection` — Get first selection
- `allSelections` — Get all selections
- `selectionsCount` — Count of active cursors

### SelectionRange

Normalized range (start always <= end).

```purescript
type SelectionRange =
  { start :: Position
  , end :: Position
  }

selectionRange :: Position -> Position -> SelectionRange  -- auto-normalizes
rangeStart :: SelectionRange -> Position
rangeEnd :: SelectionRange -> Position
rangeLength :: SelectionRange -> Int
positionsInRange :: Position -> SelectionRange -> Boolean
rangesOverlap :: SelectionRange -> SelectionRange -> Boolean
mergeRanges :: SelectionRange -> SelectionRange -> SelectionRange
```

────────────────────────────────────────────────────────────────────────────────
                                                         // richtext // types
────────────────────────────────────────────────────────────────────────────────

## URL Type

Wrapped string for hyperlinks.

```purescript
newtype URL = URL String

url :: String -> URL
unwrapURL :: URL -> String
```

**Note:** URLs are not validated at construction — validation happens at the
boundary (HTTP client, renderer).

────────────────────────────────────────────────────────────────────────────────
                                                            // heading // level
────────────────────────────────────────────────────────────────────────────────

## HeadingLevel Enum

Bounded enumeration matching HTML heading levels.

| Constructor | HTML | Description |
|-------------|------|-------------|
| `H1` | `<h1>` | Main heading |
| `H2` | `<h2>` | Section heading |
| `H3` | `<h3>` | Subsection |
| `H4` | `<h4>` | Sub-subsection |
| `H5` | `<h5>` | Minor heading |
| `H6` | `<h6>` | Smallest heading |

────────────────────────────────────────────────────────────────────────────────
                                                              // list // types
────────────────────────────────────────────────────────────────────────────────

## ListType Enum

| Constructor | HTML | Description |
|-------------|------|-------------|
| `Bullet` | `<ul>` | Unordered list |
| `Numbered` | `<ol>` | Ordered list |
| `Checkbox` | `<ul>` (task) | Task list with checkboxes |

## ListItem

Individual list entry with optional nesting.

```purescript
type ListItem =
  { content :: Array Inline
  , checked :: Maybe Boolean    -- for Checkbox lists only
  , children :: Array Block     -- nested blocks for nested lists
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                                    // inline
────────────────────────────────────────────────────────────────────────────────

## Inline Type

Character-level formatting within blocks.

| Constructor | Contains | Description |
|-------------|----------|-------------|
| `TextNode String` | Plain text | Unformatted text content |
| `Bold (Array Inline)` | Nested inlines | **Bold** formatting |
| `Italic (Array Inline)` | Nested inlines | *Italic* formatting |
| `Code String` | Plain text | `Inline code` (monospace) |
| `Link URL (Array Inline)` | URL + nested | Hyperlink with visible text |
| `Strikethrough (Array Inline)` | Nested inlines | ~~Strikethrough~~ |
| `Underline (Array Inline)` | Nested inlines | Underlined text |
| `Subscript (Array Inline)` | Nested inlines | Subscript text |
| `Superscript (Array Inline)` | Nested inlines | Superscript text |

**Nesting:** Inlines can nest (bold containing italic) but structure is always
well-formed, enforced by the ADT.

**Constructors:**
```purescript
textNode :: String -> Inline
bold :: Array Inline -> Inline
italic :: Array Inline -> Inline
code :: String -> Inline
link :: URL -> Array Inline -> Inline
strikethrough :: Array Inline -> Inline
underline :: Array Inline -> Inline
subscript :: Array Inline -> Inline
superscript :: Array Inline -> Inline
```

**Operations:**
```purescript
inlineText :: Inline -> String              -- extract plain text
inlineLength :: Inline -> Int               -- text length
flattenInlines :: Array Inline -> Array Inline  -- strip formatting
flattenInlinesToText :: Array Inline -> String  -- to plain text
```

────────────────────────────────────────────────────────────────────────────────
                                                                     // block
────────────────────────────────────────────────────────────────────────────────

## Block Type

Paragraph-level structure in documents.

| Constructor | Contains | Description |
|-------------|----------|-------------|
| `Paragraph (Array Inline)` | Inlines | Standard paragraph |
| `Heading HeadingLevel (Array Inline)` | Level + inlines | H1-H6 heading |
| `CodeBlock Language String` | Language + code | Fenced code block |
| `BlockQuote (Array Block)` | Nested blocks | Quoted content |
| `List ListType (Array ListItem)` | List type + items | Ordered/unordered list |
| `HorizontalRule` | Nothing | Thematic break (`<hr>`) |

**Constructors:**
```purescript
paragraph :: Array Inline -> Block
heading :: HeadingLevel -> Array Inline -> Block
codeBlock :: Language -> String -> Block
blockQuote :: Array Block -> Block
bulletList :: Array ListItem -> Block
numberedList :: Array ListItem -> Block
horizontalRule :: Block
```

**Operations:**
```purescript
blockToInlines :: Block -> Maybe (Array Inline)  -- Nothing for CodeBlock, HR
blockIsEmpty :: Block -> Boolean
prependInline :: Inline -> Block -> Block
appendInline :: Inline -> Block -> Block
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // document
────────────────────────────────────────────────────────────────────────────────

## RichTextDocument

Complete rich text document container.

```purescript
newtype RichTextDocument = RichTextDocument (Array Block)

emptyDocument :: RichTextDocument
documentBlocks :: RichTextDocument -> Array Block
```

**Invariants:**
- No empty blocks (except intentional empty paragraphs)
- No adjacent TextNodes (they are merged)
- No redundant nesting (bold inside bold)

**Operations:**
```purescript
documentBlockCount :: RichTextDocument -> Int
mapBlocks :: (Block -> Block) -> RichTextDocument -> RichTextDocument
filterBlocks :: (Block -> Boolean) -> RichTextDocument -> RichTextDocument
prependBlock :: Block -> RichTextDocument -> RichTextDocument
appendBlock :: Block -> RichTextDocument -> RichTextDocument
insertBlockAt :: Int -> Block -> RichTextDocument -> RichTextDocument
removeBlockAt :: Int -> RichTextDocument -> RichTextDocument
getBlockAt :: Int -> RichTextDocument -> Maybe Block
```

**Serialization:**
```purescript
documentToPlainText :: RichTextDocument -> String
blockToPlainText :: Block -> String
inlineToPlainText :: Inline -> String
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // language
────────────────────────────────────────────────────────────────────────────────

## Language Enum (51 Languages)

Bounded enumeration for code block syntax highlighting.

### General Purpose Languages

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `PlainText` | `"plaintext"`, `"text"` | No highlighting |
| `JavaScript` | `"javascript"`, `"js"` | JavaScript |
| `TypeScript` | `"typescript"`, `"ts"` | TypeScript |
| `PureScript` | `"purescript"`, `"purs"` | PureScript |
| `Haskell` | `"haskell"`, `"hs"` | Haskell |
| `Lean` | `"lean"`, `"lean4"` | Lean theorem prover |
| `Python` | `"python"`, `"py"` | Python |
| `Rust` | `"rust"`, `"rs"` | Rust |
| `Go` | `"go"`, `"golang"` | Go |
| `C` | `"c"` | C |
| `Cpp` | `"cpp"`, `"c++"` | C++ |
| `CSharp` | `"csharp"`, `"cs"`, `"c#"` | C# |
| `Java` | `"java"` | Java |
| `Kotlin` | `"kotlin"`, `"kt"` | Kotlin |
| `Swift` | `"swift"` | Swift |
| `Ruby` | `"ruby"`, `"rb"` | Ruby |
| `PHP` | `"php"` | PHP |

### Functional Languages

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `Elixir` | `"elixir"`, `"ex"` | Elixir |
| `Erlang` | `"erlang"`, `"erl"` | Erlang |
| `Clojure` | `"clojure"`, `"clj"` | Clojure |
| `Scala` | `"scala"` | Scala |
| `FSharp` | `"fsharp"`, `"fs"`, `"f#"` | F# |
| `OCaml` | `"ocaml"`, `"ml"` | OCaml |

### Systems & Emerging Languages

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `Lua` | `"lua"` | Lua |
| `R` | `"r"` | R statistical |
| `Julia` | `"julia"`, `"jl"` | Julia |
| `Zig` | `"zig"` | Zig |
| `Nim` | `"nim"` | Nim |
| `Crystal` | `"crystal"`, `"cr"` | Crystal |
| `Dart` | `"dart"` | Dart |

### Web Languages

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `HTML` | `"html"` | HTML |
| `CSS` | `"css"` | CSS |
| `SCSS` | `"scss"` | SCSS |
| `SASS` | `"sass"` | SASS |
| `Less` | `"less"` | Less CSS |

### Data Formats

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `JSON` | `"json"` | JSON |
| `YAML` | `"yaml"`, `"yml"` | YAML |
| `TOML` | `"toml"` | TOML |
| `XML` | `"xml"` | XML |

### Document & Markup

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `Markdown` | `"markdown"`, `"md"` | Markdown |
| `LaTeX` | `"latex"`, `"tex"` | LaTeX |

### Shell & Scripting

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `Bash` | `"bash"` | Bash |
| `Shell` | `"shell"`, `"sh"`, `"zsh"` | POSIX shell |
| `PowerShell` | `"powershell"`, `"ps1"` | PowerShell |

### Query & Schema Languages

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `SQL` | `"sql"` | SQL |
| `GraphQL` | `"graphql"`, `"gql"` | GraphQL |
| `Protobuf` | `"protobuf"`, `"proto"` | Protocol Buffers |

### Build & Config

| Constructor | String IDs | Description |
|-------------|------------|-------------|
| `Dockerfile` | `"dockerfile"`, `"docker"` | Dockerfile |
| `Makefile` | `"makefile"`, `"make"` | Makefile |
| `Nix` | `"nix"` | Nix expression |
| `Dhall` | `"dhall"` | Dhall |

**Parsing:**
```purescript
languageFromString :: String -> Maybe Language  -- case-insensitive
languageToString :: Language -> String          -- canonical form
```

────────────────────────────────────────────────────────────────────────────────
                                                              // token // types
────────────────────────────────────────────────────────────────────────────────

## TokenType Enum (35 Types)

Semantic categories for syntax highlighting.

### Keywords

| Constructor | Description |
|-------------|-------------|
| `TokKeyword` | Language keywords (`if`, `while`, `function`) |
| `TokKeywordControl` | Control flow (`return`, `break`, `continue`) |
| `TokKeywordOperator` | Operator keywords (`and`, `or`, `not`, `in`) |

### Identifiers

| Constructor | Description |
|-------------|-------------|
| `TokIdentifier` | Variable and function names |
| `TokFunction` | Function/method definitions |
| `TokFunctionCall` | Function/method calls |
| `TokVariable` | Local variables |
| `TokParameter` | Function parameters |
| `TokConstant` | Constants (`UPPER_CASE` by convention) |

### Types & Structures

| Constructor | Description |
|-------------|-------------|
| `TokType` | Type names and annotations |
| `TokTypeParameter` | Generic/template type parameters |
| `TokNamespace` | Namespace/module names |
| `TokClass` | Class/struct definitions |
| `TokInterface` | Interface/trait definitions |
| `TokEnum` | Enum definitions |
| `TokEnumMember` | Enum members/variants |
| `TokProperty` | Object properties/fields |

### Literals

| Constructor | Description |
|-------------|-------------|
| `TokString` | String literals |
| `TokStringEscape` | Escape sequences in strings |
| `TokStringInterp` | String interpolation expressions |
| `TokNumber` | Numeric literals |
| `TokBoolean` | Boolean literals (`true`, `false`) |
| `TokNull` | Null/nil/none literals |
| `TokRegexp` | Regular expression literals |

### Operators & Punctuation

| Constructor | Description |
|-------------|-------------|
| `TokOperator` | Operators (`+`, `-`, `*`, `/`, etc.) |
| `TokPunctuation` | Punctuation (braces, parens, commas) |
| `TokBracket` | Brackets specifically (for rainbow matching) |

### Comments

| Constructor | Description |
|-------------|-------------|
| `TokComment` | Single-line comments |
| `TokCommentBlock` | Multi-line/block comments |
| `TokCommentDoc` | Documentation comments |

### Other

| Constructor | Description |
|-------------|-------------|
| `TokTag` | HTML/XML tags |
| `TokTagAttribute` | HTML/XML attributes |
| `TokMacro` | Macros/preprocessor directives |
| `TokLabel` | Labels (for goto, case, etc.) |
| `TokInvalid` | Invalid/error tokens |
| `TokPlain` | Unhighlighted text |

**Predicates:**
```purescript
isKeyword :: TokenType -> Boolean      -- TokKeyword, TokKeywordControl, TokKeywordOperator
isString :: TokenType -> Boolean       -- TokString, TokStringEscape, TokStringInterp
isNumber :: TokenType -> Boolean       -- TokNumber
isComment :: TokenType -> Boolean      -- TokComment, TokCommentBlock, TokCommentDoc
isOperator :: TokenType -> Boolean     -- TokOperator
isPunctuation :: TokenType -> Boolean  -- TokPunctuation, TokBracket
```

────────────────────────────────────────────────────────────────────────────────
                                                                     // token
────────────────────────────────────────────────────────────────────────────────

## Token

A syntax token within a line.

```purescript
type Token =
  { tokenType :: TokenType
  , start :: Int              -- Start column (0-indexed)
  , end :: Int                -- End column (exclusive)
  , text :: String            -- Token text content
  }

token :: TokenType -> Int -> Int -> String -> Token
tokenType :: Token -> TokenType
tokenStart :: Token -> Int
tokenEnd :: Token -> Int
tokenText :: Token -> String
tokenLength :: Token -> Int
```

Tokens are computed by a tokenizer (external to this module); the renderer
styles them according to the current theme.

────────────────────────────────────────────────────────────────────────────────
                                                                  // code line
────────────────────────────────────────────────────────────────────────────────

## CodeLine

A single line in a code document.

```purescript
type CodeLine =
  { content :: String
  , tokens :: Array Token     -- Syntax tokens (may be empty if not tokenized)
  , lineNum :: Int            -- 0-indexed line number
  }

codeLine :: String -> Int -> CodeLine
lineContent :: CodeLine -> String
lineTokens :: CodeLine -> Array Token
lineNumber :: CodeLine -> Int
lineIndentation :: CodeLine -> Int   -- Leading whitespace count
isLineEmpty :: CodeLine -> Boolean
isLineWhitespace :: CodeLine -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                              // code document
────────────────────────────────────────────────────────────────────────────────

## CodeDocument

Complete code document with multi-cursor support.

```purescript
type CodeDocument =
  { lines :: Array CodeLine
  , language :: Language
  , cursors :: Array Cursor
  }

codeDocument :: String -> Language -> CodeDocument
emptyCodeDocument :: Language -> CodeDocument
documentContent :: CodeDocument -> String
documentLanguage :: CodeDocument -> Language
documentCursors :: CodeDocument -> Array Cursor
setContent :: String -> CodeDocument -> CodeDocument
setLanguage :: Language -> CodeDocument -> CodeDocument
setCursors :: Array Cursor -> CodeDocument -> CodeDocument
```

**Line Access:**
```purescript
documentLines :: CodeDocument -> Array CodeLine
documentLineCount :: CodeDocument -> Int
getLine :: Int -> CodeDocument -> Maybe CodeLine
setLine :: Int -> CodeLine -> CodeDocument -> CodeDocument
```

**Line Manipulation:**
```purescript
insertLine :: Int -> String -> CodeDocument -> CodeDocument
deleteLine :: Int -> CodeDocument -> CodeDocument
splitLine :: Int -> Int -> CodeDocument -> CodeDocument   -- line, column
joinLines :: Int -> CodeDocument -> CodeDocument
```

**Text Operations:**
```purescript
insertTextAt :: Int -> Int -> String -> CodeDocument -> CodeDocument
deleteTextAt :: Int -> Int -> Int -> CodeDocument -> CodeDocument
replaceTextAt :: Int -> Int -> Int -> String -> CodeDocument -> CodeDocument
getTextInRange :: Int -> Int -> Int -> Int -> CodeDocument -> String
```

────────────────────────────────────────────────────────────────────────────────
                                                                    // cursor
────────────────────────────────────────────────────────────────────────────────

## Cursor

Cursor position in code documents.

```purescript
type Cursor =
  { position :: CodePosition
  , selection :: Maybe CodeSelection
  }

cursor :: CodePosition -> Cursor
cursorPosition :: Cursor -> CodePosition
cursorSelection :: Cursor -> Maybe CodeSelection
cursorIsCollapsed :: Cursor -> Boolean
cursorLine :: Cursor -> Int
cursorColumn :: Cursor -> Int
```

────────────────────────────────────────────────────────────────────────────────
                                                               // indentation
────────────────────────────────────────────────────────────────────────────────

## IndentStyle Enum

| Constructor | Description |
|-------------|-------------|
| `IndentSpaces` | Use spaces for indentation |
| `IndentTabs` | Use tabs for indentation |

## IndentSize

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| IndentSize | Int | 1 | 8 | clamps | Spaces per indent level |

```purescript
newtype IndentSize = IndentSize Int

indentSize :: Int -> IndentSize
unwrapIndentSize :: IndentSize -> Int
```

**Operations:**
```purescript
detectIndentation :: CodeDocument -> { style :: IndentStyle, size :: IndentSize }
indentLine :: IndentStyle -> IndentSize -> Int -> CodeDocument -> CodeDocument
outdentLine :: IndentStyle -> IndentSize -> Int -> CodeDocument -> CodeDocument
normalizeIndentation :: IndentStyle -> IndentSize -> CodeDocument -> CodeDocument
```

────────────────────────────────────────────────────────────────────────────────
                                                              // line endings
────────────────────────────────────────────────────────────────────────────────

## LineEnding Enum

| Constructor | Escape | Platform | Description |
|-------------|--------|----------|-------------|
| `LineLF` | `\n` | Unix/Linux/macOS | Line feed |
| `LineCRLF` | `\r\n` | Windows | Carriage return + line feed |
| `LineCR` | `\r` | Classic Mac | Carriage return only |

**Operations:**
```purescript
detectLineEnding :: String -> LineEnding
normalizeLineEndings :: LineEnding -> String -> String
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // folding
────────────────────────────────────────────────────────────────────────────────

## FoldRegion

Collapsible code region.

```purescript
type FoldRegion =
  { startLine :: Int
  , endLine :: Int
  , folded :: Boolean
  }

foldRegion :: Int -> Int -> Boolean -> FoldRegion
foldStart :: FoldRegion -> Int
foldEnd :: FoldRegion -> Int
isFolded :: FoldRegion -> Boolean
toggleFold :: FoldRegion -> FoldRegion
```

────────────────────────────────────────────────────────────────────────────────
                                                               // diagnostics
────────────────────────────────────────────────────────────────────────────────

## DiagnosticSeverity Enum

| Constructor | Description | Visual |
|-------------|-------------|--------|
| `SeverityError` | Compilation/runtime error | Red squiggle |
| `SeverityWarning` | Code smell, deprecated | Yellow squiggle |
| `SeverityInfo` | Informational message | Blue indicator |
| `SeverityHint` | Suggestion for improvement | Subtle underline |

## Diagnostic

Error/warning message attached to code location.

```purescript
type Diagnostic =
  { line :: Int
  , column :: Int
  , endLine :: Int
  , endColumn :: Int
  , message :: String
  , severity :: DiagnosticSeverity
  , source :: Maybe String        -- Linter name, etc.
  , code :: Maybe String          -- Error code
  }

diagnostic :: Int -> Int -> String -> DiagnosticSeverity -> Diagnostic
diagnosticLine :: Diagnostic -> Int
diagnosticColumn :: Diagnostic -> Int
diagnosticMessage :: Diagnostic -> String
diagnosticSeverity :: Diagnostic -> DiagnosticSeverity
```

────────────────────────────────────────────────────────────────────────────────
                                                          // command // system
────────────────────────────────────────────────────────────────────────────────

## Edit Commands

All text editing operations as pure data. Commands are NOT imperative
procedures — they describe what to do, enabling:

- **Undo/redo** via command history
- **Collaborative editing** (OT/CRDT) via command transformation
- **Testing** via command application
- **Serialization** for persistence and sync

### InsertDirection Enum

| Constructor | Description |
|-------------|-------------|
| `InsertBefore` | Insert before cursor (normal typing) |
| `InsertAfter` | Insert after cursor (some paste modes) |

### DeleteDirection Enum

| Constructor | Description |
|-------------|-------------|
| `DeleteBackward` | Backspace: delete before cursor |
| `DeleteForward` | Delete: delete after cursor |

### DeleteScope Enum

| Constructor | Description |
|-------------|-------------|
| `DeleteChar` | Single character |
| `DeleteWord` | Whole word |
| `DeleteLine` | Entire line |
| `DeleteBlock` | Entire block (paragraph, etc.) |
| `DeleteSelection` | Whatever is selected |

────────────────────────────────────────────────────────────────────────────────
                                                        // format // commands
────────────────────────────────────────────────────────────────────────────────

## FormatCommand

Inline formatting operations (toggle semantics).

| Constructor | Description |
|-------------|-------------|
| `ToggleBold` | Toggle bold on selection |
| `ToggleItalic` | Toggle italic on selection |
| `ToggleCode` | Toggle inline code |
| `ToggleStrikethrough` | Toggle strikethrough |
| `ToggleUnderline` | Toggle underline |
| `ToggleSubscript` | Toggle subscript |
| `ToggleSuperscript` | Toggle superscript |
| `SetLink URL` | Set link URL (removes if empty) |
| `RemoveLink` | Remove link from selection |
| `ClearFormatting` | Remove all inline formatting |

**Convenience constructors:**
```purescript
formatBold :: FormatCommand        -- ToggleBold
formatItalic :: FormatCommand      -- ToggleItalic
formatCode :: FormatCommand        -- ToggleCode
formatStrikethrough :: FormatCommand
formatUnderline :: FormatCommand
formatLink :: URL -> FormatCommand
formatClear :: FormatCommand       -- ClearFormatting
```

────────────────────────────────────────────────────────────────────────────────
                                                          // block // commands
────────────────────────────────────────────────────────────────────────────────

## BlockCommand

Structural operations on blocks.

| Constructor | Description | Typical Trigger |
|-------------|-------------|-----------------|
| `SplitBlock` | Split current block at cursor | Enter |
| `MergeWithPrevious` | Merge with previous block | Backspace at start |
| `MergeWithNext` | Merge with next block | Delete at end |
| `SetHeading HeadingLevel` | Convert to heading | Markdown `#` |
| `SetParagraph` | Convert to paragraph | |
| `SetCodeBlock` | Convert to code block | ``` |
| `SetBlockQuote` | Convert to block quote | `>` |
| `SetBulletList` | Convert to bullet list | `-` or `*` |
| `SetNumberedList` | Convert to numbered list | `1.` |
| `SetCheckboxList` | Convert to checkbox list | `[ ]` |
| `ToggleCheckbox` | Toggle checkbox state | Click |
| `IndentBlock` | Increase indentation | Tab in list |
| `OutdentBlock` | Decrease indentation | Shift+Tab |
| `InsertBlockBefore Block` | Insert block before | |
| `InsertBlockAfter Block` | Insert block after | |
| `DeleteCurrentBlock` | Delete current block | |
| `InsertHorizontalRule` | Insert thematic break | `---` |

────────────────────────────────────────────────────────────────────────────────
                                                     // navigation // commands
────────────────────────────────────────────────────────────────────────────────

## MoveUnit Enum

| Constructor | Description |
|-------------|-------------|
| `MoveChar` | Single character |
| `MoveWord` | Word boundary |
| `MoveLine` | Line boundary |
| `MoveBlock` | Block boundary |
| `MoveDocument` | Document boundary (start/end) |

## SelectionMode Enum

| Constructor | Description |
|-------------|-------------|
| `MoveCursor` | Move cursor, collapse selection |
| `ExtendSelection` | Extend selection from anchor |

## NavigationCommand

Cursor and selection movement.

| Constructor | Description |
|-------------|-------------|
| `MoveLeft MoveUnit SelectionMode` | Move left by unit |
| `MoveRight MoveUnit SelectionMode` | Move right by unit |
| `MoveUp SelectionMode` | Move up one line |
| `MoveDown SelectionMode` | Move down one line |
| `MoveToLineStart SelectionMode` | Move to line start |
| `MoveToLineEnd SelectionMode` | Move to line end |
| `MoveToBlockStart SelectionMode` | Move to block start |
| `MoveToBlockEnd SelectionMode` | Move to block end |
| `MoveToDocumentStart SelectionMode` | Move to document start |
| `MoveToDocumentEnd SelectionMode` | Move to document end |
| `SelectAll` | Select entire document |
| `SelectWord` | Select current word |
| `SelectLine` | Select current line |
| `SelectBlock` | Select current block |
| `SetSelection Selection` | Set selection directly |
| `CollapseSelectionToStart` | Collapse to start |
| `CollapseSelectionToEnd` | Collapse to end |

────────────────────────────────────────────────────────────────────────────────
                                                        // history // commands
────────────────────────────────────────────────────────────────────────────────

## HistoryCommand

Undo/redo operations.

| Constructor | Description |
|-------------|-------------|
| `Undo` | Undo last command |
| `Redo` | Redo last undone command |
| `UndoAll` | Reset to initial state |
| `RedoAll` | Redo all undone commands |
| `ClearHistory` | Clear undo/redo history |

────────────────────────────────────────────────────────────────────────────────
                                                      // clipboard // commands
────────────────────────────────────────────────────────────────────────────────

## ClipboardCommand

Clipboard operations.

| Constructor | Description |
|-------------|-------------|
| `Cut` | Cut selection to clipboard |
| `Copy` | Copy selection to clipboard |
| `Paste` | Paste from clipboard |
| `PastePlain` | Paste as plain text (strip formatting) |

────────────────────────────────────────────────────────────────────────────────
                                                           // edit // command
────────────────────────────────────────────────────────────────────────────────

## EditCommand

Top-level edit command sum type.

```purescript
data EditCommand
  -- Text insertion
  = InsertText String                     -- Insert text at cursor
  | InsertNewline                         -- Insert newline (may split block)
  | InsertTab                             -- Insert tab (may indent)
  
  -- Text deletion
  | Delete DeleteDirection DeleteScope   -- Delete with direction and scope
  | DeleteRange Position Position         -- Delete between two positions
  
  -- Formatting
  | Format FormatCommand                  -- Apply formatting
  
  -- Block operations
  | BlockOp BlockCommand                  -- Apply block command
  
  -- Navigation
  | Navigate NavigationCommand            -- Apply navigation
  
  -- History
  | History HistoryCommand                -- Undo/redo
  
  -- Clipboard
  | Clipboard ClipboardCommand            -- Cut/copy/paste
  
  -- Composition
  | Compound CompoundCommand              -- Compound/atomic command
```

**Predicates:**
```purescript
isInsertCommand :: EditCommand -> Boolean
isDeleteCommand :: EditCommand -> Boolean
isFormatCommand :: EditCommand -> Boolean
isBlockCommand :: EditCommand -> Boolean
isNavigationCommand :: EditCommand -> Boolean
isHistoryCommand :: EditCommand -> Boolean
modifiesDocument :: EditCommand -> Boolean
modifiesSelection :: EditCommand -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                       // compound // commands
────────────────────────────────────────────────────────────────────────────────

## CompoundCommand

Multi-step operations with atomicity control.

| Constructor | Description |
|-------------|-------------|
| `Atomic (Array EditCommand)` | Execute as single undo step |
| `Sequence (Array EditCommand)` | Each is separate undo step |

**Key insight:** "Replace selection" is atomic: Delete + Insert as one unit.
Undo restores both the deleted text AND removes the inserted text.

```purescript
atomic :: Array EditCommand -> CompoundCommand
sequence :: Array EditCommand -> CompoundCommand
```

────────────────────────────────────────────────────────────────────────────────
                                                       // command // metadata
────────────────────────────────────────────────────────────────────────────────

## CommandMeta

Metadata for debugging and collaboration.

```purescript
type CommandMeta =
  { timestamp :: Maybe Number       -- Unix timestamp (ms)
  , userId :: Maybe String          -- User who issued command
  , source :: Maybe String          -- keyboard, menu, api
  , mergeId :: Maybe String         -- For merging adjacent commands
  }

commandMeta :: Maybe Number -> Maybe String -> Maybe String -> Maybe String -> CommandMeta
defaultMeta :: CommandMeta  -- all Nothing
```

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Text/
├── Code.purs                   # Leader module (re-exports Code.*)
├── Code/
│   ├── Cursor.purs             # Code cursor type
│   ├── Diagnostic.purs         # Error/warning messages
│   ├── Document.purs           # Code document operations
│   ├── Folding.purs            # Code folding regions
│   ├── Indentation.purs        # Indent style and operations
│   ├── Line.purs               # Single code line
│   ├── LineEnding.purs         # LF/CRLF/CR handling
│   └── Token.purs              # Syntax token types
├── Command.purs                # Edit commands (525 lines)
├── RichText.purs               # Leader module (re-exports RichText.*)
├── RichText/
│   ├── Block.purs              # Block constructors and operations
│   ├── Document.purs           # Document operations and serialization
│   ├── Inline.purs             # Inline constructors and operations
│   └── Types.purs              # Core types (440 lines)
└── Selection.purs              # Selection model (554 lines)
```

14 files, 3,366 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Rich Text as Data

Traditional rich text editors use HTML strings. This creates problems:

1. **Ambiguity** — Multiple HTML representations produce identical output
2. **Validation** — Invalid nesting is expressible (`<b><i></b></i>`)
3. **Diffing** — String comparison misses semantic equivalence
4. **Collaboration** — No algebraic structure for OT/CRDT

Hydrogen's model is **canonical**: same content = same representation. The ADT
structure makes invalid states unrepresentable.

## Why Commands as Data

Imperative editing procedures (`document.insertText(...)`) are opaque:

- Can't be serialized
- Can't be reversed without snapshots
- Can't be transformed for collaboration
- Can't be inspected for testing

Pure command data enables:

- **History** — Store commands, apply forward/backward
- **Collaboration** — Transform concurrent commands algebraically
- **Determinism** — Same command sequence = same result
- **Testing** — Commands are values, assert on them

## Why Two Document Models

Rich text and code have fundamentally different structure:

**Rich text:**
- Block/inline hierarchy
- Semantic formatting (bold, italic)
- Variable block sizes
- Focus: prose authoring

**Code:**
- Line-oriented
- Syntax tokens (semantically meaningful)
- Multi-cursor native
- Focus: precise character manipulation

Unifying them would lose important properties of each.

## Multi-Cursor Philosophy

Multi-cursor editing is first-class, not an afterthought:

- `MultiSelection` always contains at least one selection
- Primary selection (first) determines visible cursor
- Commands apply to all cursors simultaneously
- Overlapping selections are merged automatically

## Bounds Rationale

| Bound | Value | Rationale |
|-------|-------|-----------|
| BlockIndex max | 65,535 | 16-bit, covers any practical document |
| CharOffset max | 16,777,215 | 24-bit, ~16M chars per block |
| LineNumber max | 1,048,575 | 20-bit, ~1M lines per file |
| Column max | 16,383 | 14-bit, ~16K chars per line |
| IndentSize max | 8 | No sane codebase uses 9+ space indent |
| Languages | 51 | Common languages, extensible via ADT |
| TokenTypes | 35 | Universal semantic categories |

Every bound is chosen to handle real-world documents while remaining bounded
for deterministic agent reasoning.

────────────────────────────────────────────────────────────────────────────────
                                                     // integration // example
────────────────────────────────────────────────────────────────────────────────

## Building a Text Editor

```purescript
import Hydrogen.Schema.Text.Selection as Sel
import Hydrogen.Schema.Text.Command as Cmd
import Hydrogen.Schema.Text.RichText as RT

-- Initial document
initialDoc :: RT.RichTextDocument
initialDoc = RT.emptyDocument
  # RT.appendBlock (RT.paragraph [ RT.textNode "Hello, world!" ])

-- Initial selection (cursor at end)
initialSel :: Sel.Selection
initialSel = Sel.cursorAt 0 13

-- Handle user typing
handleKeypress :: String -> Cmd.EditCommand
handleKeypress char = Cmd.InsertText char

-- Handle formatting
handleBold :: Cmd.EditCommand
handleBold = Cmd.Format Cmd.formatBold

-- Handle undo
handleUndo :: Cmd.EditCommand
handleUndo = Cmd.History Cmd.Undo

-- Commands are data — store them for history
commandHistory :: Array Cmd.EditCommand
commandHistory = 
  [ Cmd.InsertText "H"
  , Cmd.InsertText "i"
  , Cmd.Format Cmd.formatBold
  ]
```

────────────────────────────────────────────────────────────────────────────────
