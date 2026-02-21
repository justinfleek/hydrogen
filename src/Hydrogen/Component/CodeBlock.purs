-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // codeblock
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CodeBlock component
-- |
-- | Display formatted code with optional line numbers and copy button.
-- | For read-only code display (not editing - see Editor.Code for that).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.CodeBlock as CodeBlock
-- |
-- | -- Basic code block
-- | CodeBlock.codeBlock
-- |   [ CodeBlock.code "const x = 42;"
-- |   , CodeBlock.language CodeBlock.JavaScript
-- |   ]
-- |
-- | -- With line numbers
-- | CodeBlock.codeBlock
-- |   [ CodeBlock.code multilineCode
-- |   , CodeBlock.language CodeBlock.PureScript
-- |   , CodeBlock.showLineNumbers true
-- |   ]
-- |
-- | -- With filename header
-- | CodeBlock.codeBlock
-- |   [ CodeBlock.code configCode
-- |   , CodeBlock.language CodeBlock.JSON
-- |   , CodeBlock.filename "package.json"
-- |   , CodeBlock.showCopy true
-- |   ]
-- |
-- | -- Inline code
-- | CodeBlock.inlineCode "npm install"
-- | ```
module Hydrogen.Component.CodeBlock
  ( -- * CodeBlock Components
    codeBlock
  , inlineCode
  , codeBlockWithHeader
    -- * Types
  , Language(..)
    -- * Props
  , CodeBlockProps
  , CodeBlockProp
  , defaultProps
    -- * Prop Builders
  , code
  , language
  , filename
  , showLineNumbers
  , showCopy
  , highlightLines
  , maxHeight
  , wrap
  , theme
  , className
  , onCopy
    -- * Theme
  , Theme(..)
  ) where

import Prelude

import Data.Array (foldl, mapWithIndex, elem)
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Supported languages
data Language
  = PlainText
  | JavaScript
  | TypeScript
  | PureScript
  | Haskell
  | Python
  | Rust
  | Go
  | HTML
  | CSS
  | JSON
  | YAML
  | Markdown
  | Bash
  | SQL

derive instance eqLanguage :: Eq Language

-- | Get language display name
languageName :: Language -> String
languageName = case _ of
  PlainText -> "text"
  JavaScript -> "javascript"
  TypeScript -> "typescript"
  PureScript -> "purescript"
  Haskell -> "haskell"
  Python -> "python"
  Rust -> "rust"
  Go -> "go"
  HTML -> "html"
  CSS -> "css"
  JSON -> "json"
  YAML -> "yaml"
  Markdown -> "markdown"
  Bash -> "bash"
  SQL -> "sql"

-- | Theme options
data Theme
  = Light
  | Dark
  | Auto

derive instance eqTheme :: Eq Theme

-- | Get theme classes
themeClasses :: Theme -> String
themeClasses = case _ of
  Light -> "bg-zinc-50 text-zinc-900"
  Dark -> "bg-zinc-900 text-zinc-100"
  Auto -> "bg-muted text-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CodeBlock properties
type CodeBlockProps i =
  { code :: String
  , language :: Language
  , filename :: Maybe String
  , showLineNumbers :: Boolean
  , showCopy :: Boolean
  , highlightLines :: Array Int
  , maxHeight :: Maybe String
  , wrap :: Boolean
  , theme :: Theme
  , className :: String
  , onCopy :: Maybe i
  }

-- | Property modifier
type CodeBlockProp i = CodeBlockProps i -> CodeBlockProps i

-- | Default properties
defaultProps :: forall i. CodeBlockProps i
defaultProps =
  { code: ""
  , language: PlainText
  , filename: Nothing
  , showLineNumbers: false
  , showCopy: true
  , highlightLines: []
  , maxHeight: Nothing
  , wrap: false
  , theme: Auto
  , className: ""
  , onCopy: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set code content
code :: forall i. String -> CodeBlockProp i
code c props = props { code = c }

-- | Set language
language :: forall i. Language -> CodeBlockProp i
language l props = props { language = l }

-- | Set filename for header
filename :: forall i. String -> CodeBlockProp i
filename f props = props { filename = Just f }

-- | Show line numbers
showLineNumbers :: forall i. Boolean -> CodeBlockProp i
showLineNumbers s props = props { showLineNumbers = s }

-- | Show copy button
showCopy :: forall i. Boolean -> CodeBlockProp i
showCopy s props = props { showCopy = s }

-- | Set lines to highlight
highlightLines :: forall i. Array Int -> CodeBlockProp i
highlightLines h props = props { highlightLines = h }

-- | Set max height (enables scrolling)
maxHeight :: forall i. String -> CodeBlockProp i
maxHeight m props = props { maxHeight = Just m }

-- | Enable word wrap
wrap :: forall i. Boolean -> CodeBlockProp i
wrap w props = props { wrap = w }

-- | Set theme
theme :: forall i. Theme -> CodeBlockProp i
theme t props = props { theme = t }

-- | Add custom class
className :: forall i. String -> CodeBlockProp i
className c props = props { className = props.className <> " " <> c }

-- | Set copy handler
onCopy :: forall i. i -> CodeBlockProp i
onCopy handler props = props { onCopy = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "relative rounded-lg border overflow-hidden"

-- | Header classes
headerClasses :: String
headerClasses =
  "flex items-center justify-between px-4 py-2 border-b bg-muted/50"

-- | Filename classes
filenameClasses :: String
filenameClasses =
  "text-sm font-mono text-muted-foreground"

-- | Language badge classes
languageBadgeClasses :: String
languageBadgeClasses =
  "text-xs font-mono text-muted-foreground bg-muted px-2 py-0.5 rounded"

-- | Code container classes
codeContainerClasses :: String
codeContainerClasses =
  "relative overflow-x-auto"

-- | Pre classes
preClasses :: String
preClasses =
  "p-4 font-mono text-sm leading-relaxed"

-- | Line number gutter classes
gutterClasses :: String
gutterClasses =
  "select-none text-right pr-4 text-muted-foreground/50"

-- | Highlighted line classes
highlightedLineClasses :: String
highlightedLineClasses =
  "bg-primary/10"

-- | Copy button classes
copyButtonClasses :: String
copyButtonClasses =
  "absolute top-2 right-2 p-2 rounded-md bg-background/80 hover:bg-background text-muted-foreground hover:text-foreground transition-colors opacity-0 group-hover:opacity-100"

-- | Inline code classes
inlineCodeClasses :: String
inlineCodeClasses =
  "font-mono text-sm bg-muted px-1.5 py-0.5 rounded"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Inline code element
inlineCode :: forall w i. String -> HH.HTML w i
inlineCode content =
  HH.code
    [ cls [ inlineCodeClasses ] ]
    [ HH.text content ]

-- | Code block with optional header
codeBlockWithHeader :: forall w i. 
  Array (CodeBlockProp i) -> 
  { header :: HH.HTML w i, content :: HH.HTML w i } -> 
  HH.HTML w i
codeBlockWithHeader propMods slots =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerCls = 
      containerClasses 
      <> " " <> themeClasses props.theme
      <> " " <> props.className
  in
    HH.div
      [ cls [ containerCls, "group" ] ]
      [ slots.header
      , slots.content
      ]

-- | Full code block component
codeBlock :: forall w i. Array (CodeBlockProp i) -> HH.HTML w i
codeBlock propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Split code into lines
    lines = String.split (String.Pattern "\n") props.code
    
    -- Container classes
    containerCls = 
      containerClasses 
      <> " " <> themeClasses props.theme
      <> " " <> props.className
    
    -- Code container style for max height
    containerStyle = case props.maxHeight of
      Just h -> [ HP.attr (HH.AttrName "style") ("max-height: " <> h <> "; overflow-y: auto;") ]
      Nothing -> []
    
    -- Render a single line
    renderLine :: Int -> String -> HH.HTML w i
    renderLine idx lineContent =
      let
        lineNum = idx + 1
        isHighlighted = elem lineNum props.highlightLines
        lineCls = if isHighlighted then highlightedLineClasses else ""
      in
        HH.div
          [ cls [ "flex", lineCls ] ]
          [ -- Line number (optional)
            if props.showLineNumbers
              then
                HH.span
                  [ cls [ gutterClasses, "w-8 flex-shrink-0" ] ]
                  [ HH.text (show lineNum) ]
              else HH.text ""
          -- Line content
          , HH.span
              [ cls [ if props.wrap then "whitespace-pre-wrap break-all" else "whitespace-pre" ] ]
              [ HH.text (if lineContent == "" then " " else lineContent) ]
          ]
    
    -- Copy button
    copyButton :: HH.HTML w i
    copyButton =
      let
        clickHandler = case props.onCopy of
          Just handler -> [ HE.onClick (\_ -> handler) ]
          Nothing -> []
      in
        HH.button
          ( [ cls [ copyButtonClasses ]
            , HP.type_ HP.ButtonButton
            , ARIA.label "Copy code"
            ] <> clickHandler
          )
          [ copyIcon ]
    
    -- Header (optional)
    header :: HH.HTML w i
    header =
      case props.filename of
        Just fname ->
          HH.div
            [ cls [ headerClasses ] ]
            [ HH.span [ cls [ filenameClasses ] ] [ HH.text fname ]
            , HH.span [ cls [ languageBadgeClasses ] ] [ HH.text (languageName props.language) ]
            ]
        Nothing -> HH.text ""
  in
    HH.div
      [ cls [ containerCls, "group" ] ]
      [ -- Header
        header
      -- Code content
      , HH.div
          ( [ cls [ codeContainerClasses ] ] <> containerStyle )
          [ HH.pre
              [ cls [ preClasses ] ]
              [ HH.code
                  [ HP.attr (HH.AttrName "data-language") (languageName props.language) ]
                  (mapWithIndex renderLine lines)
              ]
          ]
      -- Copy button
      , if props.showCopy
          then copyButton
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Copy icon
copyIcon :: forall w i. HH.HTML w i
copyIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "rect")
        [ HP.attr (HH.AttrName "x") "9"
        , HP.attr (HH.AttrName "y") "9"
        , HP.attr (HH.AttrName "width") "13"
        , HP.attr (HH.AttrName "height") "13"
        , HP.attr (HH.AttrName "rx") "2"
        , HP.attr (HH.AttrName "ry") "2"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1" ]
        []
    ]
