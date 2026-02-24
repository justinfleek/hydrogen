-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // code-editor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Full-featured code editor component
-- |
-- | A Monaco/CodeMirror-style code editor with syntax highlighting, line numbers,
-- | code folding, multiple cursors, find & replace, and comprehensive keyboard
-- | shortcuts.
-- |
-- | ## Features
-- |
-- | - Syntax highlighting for JS, TS, HTML, CSS, JSON, Markdown, PureScript
-- | - Line numbers with gutter
-- | - Current line highlighting
-- | - Code folding
-- | - Auto-indentation
-- | - Tab handling (tabs vs spaces, configurable)
-- | - Bracket matching
-- | - Auto-closing brackets/quotes
-- | - Multiple cursors (Ctrl+D)
-- | - Find & Replace (Ctrl+F, Ctrl+H)
-- | - Go to line (Ctrl+G)
-- | - Minimap (optional)
-- | - Word wrap toggle
-- | - Theme support (light/dark)
-- | - Read-only mode
-- | - Diff view (two-pane comparison)
-- | - Error/warning gutters (line markers)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Editor.Code as Code
-- |
-- | -- Basic editor
-- | Code.codeEditor
-- |   [ Code.value "console.log('Hello, world!')"
-- |   , Code.language Code.JavaScript
-- |   , Code.onChange HandleChange
-- |   ]
-- |
-- | -- With line numbers and theme
-- | Code.codeEditor
-- |   [ Code.value state.code
-- |   , Code.language Code.TypeScript
-- |   , Code.lineNumbers true
-- |   , Code.theme Code.Dark
-- |   , Code.onChange UpdateCode
-- |   ]
-- |
-- | -- Read-only with minimap
-- | Code.codeEditor
-- |   [ Code.value sourceCode
-- |   , Code.language Code.PureScript
-- |   , Code.readOnly true
-- |   , Code.minimap true
-- |   ]
-- |
-- | -- Diff view
-- | Code.diffEditor
-- |   [ Code.original originalCode
-- |   , Code.modified modifiedCode
-- |   , Code.language Code.JSON
-- |   ]
-- |
-- | -- With error markers
-- | Code.codeEditor
-- |   [ Code.value state.code
-- |   , Code.language Code.TypeScript
-- |   , Code.markers
-- |       [ Code.errorMarker 5 "Type error: ..."
-- |       , Code.warningMarker 10 "Unused variable"
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Keyboard Shortcuts
-- |
-- | | Shortcut | Action |
-- | |----------|--------|
-- | | Ctrl+F | Find |
-- | | Ctrl+H | Replace |
-- | | Ctrl+G | Go to line |
-- | | Ctrl+D | Add cursor at next occurrence |
-- | | Ctrl+/ | Toggle comment |
-- | | Ctrl+Z | Undo |
-- | | Ctrl+Shift+Z | Redo |
-- | | Alt+Up | Move line up |
-- | | Alt+Down | Move line down |
-- | | Alt+Shift+Up | Copy line up |
-- | | Alt+Shift+Down | Copy line down |
-- | | Tab | Indent |
-- | | Shift+Tab | Outdent |
-- | | Ctrl+] | Indent line |
-- | | Ctrl+[ | Outdent line |
module Hydrogen.Editor.Code
  ( -- * Editor Components
    codeEditor
  , diffEditor
    -- * Language Types
  , Language(JavaScript, TypeScript, HTML, CSS, JSON, Markdown, PureScript, PlainText)
  , detectLanguage
    -- * Theme Types
  , Theme(Light, Dark)
    -- * Marker Types
  , Marker
  , MarkerSeverity(Error, Warning, Info, Hint)
  , errorMarker
  , warningMarker
  , infoMarker
  , hintMarker
    -- * Editor Props
  , EditorProps
  , EditorProp
  , value
  , language
  , theme
  , lineNumbers
  , readOnly
  , minimap
  , wordWrap
  , tabSize
  , useTabs
  , autoCloseBrackets
  , autoCloseQuotes
  , bracketMatching
  , highlightActiveLine
  , codeFolding
  , markers
  , className
  , height
  , onInit
  , onChange
  , onCursorChange
  , onSelectionChange
  , onFocus
  , onBlur
  , onKeyDown
    -- * Diff Editor Props
  , DiffEditorProps
  , DiffEditorProp
  , original
  , modified
  , diffLanguage
  , diffTheme
  , renderSideBySide
  , diffClassName
  , diffHeight
    -- * Editor State
  , EditorState
  , CursorPosition
  , Selection
  , getEditorState
    -- * Imperative API (FFI)
  , EditorRef
  , createEditorRef
  , getValue
  , setValue
  , getSelection
  , setSelection
  , getCursorPosition
  , setCursorPosition
  , focus
  , blur
  , undo
  , redo
  , format
  , find
  , replace
  , replaceAll
  , goToLine
  , insertText
  , foldAll
  , unfoldAll
  ) where

import Prelude hiding (map)

import Data.Array (foldl, filter)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Supported programming languages
data Language
  = JavaScript
  | TypeScript
  | HTML
  | CSS
  | JSON
  | Markdown
  | PureScript
  | PlainText

derive instance eqLanguage :: Eq Language

instance showLanguage :: Show Language where
  show JavaScript = "javascript"
  show TypeScript = "typescript"
  show HTML = "html"
  show CSS = "css"
  show JSON = "json"
  show Markdown = "markdown"
  show PureScript = "purescript"
  show PlainText = "plaintext"

-- | Color theme
data Theme
  = Light
  | Dark

derive instance eqTheme :: Eq Theme

instance showTheme :: Show Theme where
  show Light = "light"
  show Dark = "dark"

-- | Marker severity levels
data MarkerSeverity
  = Error
  | Warning
  | Info
  | Hint

derive instance eqMarkerSeverity :: Eq MarkerSeverity

instance showMarkerSeverity :: Show MarkerSeverity where
  show Error = "error"
  show Warning = "warning"
  show Info = "info"
  show Hint = "hint"

-- | Line marker (error, warning, etc.)
type Marker =
  { line :: Int
  , column :: Int
  , endLine :: Int
  , endColumn :: Int
  , message :: String
  , severity :: MarkerSeverity
  }

-- | Cursor position
type CursorPosition =
  { line :: Int
  , column :: Int
  }

-- | Text selection
type Selection =
  { startLine :: Int
  , startColumn :: Int
  , endLine :: Int
  , endColumn :: Int
  }

-- | Editor internal state
type EditorState =
  { value :: String
  , cursorPosition :: CursorPosition
  , selections :: Array Selection
  , scrollTop :: Number
  , scrollLeft :: Number
  , isFocused :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Raw editor handle from JS
foreign import data EditorHandle :: Type

-- | Editor ref for imperative operations
newtype EditorRef = EditorRef (Ref (Maybe EditorHandle))

-- Editor lifecycle
foreign import createEditorImpl :: EffectFn2 String EditorConfig EditorHandle
foreign import destroyEditorImpl :: EffectFn1 EditorHandle Unit

-- Value operations
foreign import getValueImpl :: EffectFn1 EditorHandle String
foreign import setValueImpl :: EffectFn2 EditorHandle String Unit

-- Cursor/Selection
foreign import getCursorPositionImpl :: EffectFn1 EditorHandle { line :: Int, column :: Int }
foreign import setCursorPositionImpl :: EffectFn2 EditorHandle { line :: Int, column :: Int } Unit
foreign import getSelectionImpl :: EffectFn1 EditorHandle Selection
foreign import setSelectionImpl :: EffectFn2 EditorHandle Selection Unit
foreign import getSelectionsImpl :: EffectFn1 EditorHandle (Array Selection)
foreign import addSelectionImpl :: EffectFn2 EditorHandle Selection Unit

-- Focus management
foreign import focusEditorImpl :: EffectFn1 EditorHandle Unit
foreign import blurEditorImpl :: EffectFn1 EditorHandle Unit

-- Edit operations
foreign import undoImpl :: EffectFn1 EditorHandle Unit
foreign import redoImpl :: EffectFn1 EditorHandle Unit
foreign import formatImpl :: EffectFn1 EditorHandle Unit
foreign import insertTextImpl :: EffectFn2 EditorHandle String Unit

-- Find/Replace
foreign import findImpl :: EffectFn2 EditorHandle String Unit
foreign import replaceImpl :: EffectFn3 EditorHandle String String Unit
foreign import replaceAllImpl :: EffectFn3 EditorHandle String String Unit

-- Navigation
foreign import goToLineImpl :: EffectFn2 EditorHandle Int Unit

-- Folding
foreign import foldAllImpl :: EffectFn1 EditorHandle Unit
foreign import unfoldAllImpl :: EffectFn1 EditorHandle Unit

-- Editor config type (passed to JS)
type EditorConfig =
  { language :: String
  , theme :: String
  , lineNumbers :: Boolean
  , readOnly :: Boolean
  , minimap :: Boolean
  , wordWrap :: Boolean
  , tabSize :: Int
  , useTabs :: Boolean
  , autoCloseBrackets :: Boolean
  , autoCloseQuotes :: Boolean
  , bracketMatching :: Boolean
  , highlightActiveLine :: Boolean
  , codeFolding :: Boolean
  , height :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // marker utils
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an error marker
errorMarker :: Int -> String -> Marker
errorMarker line message =
  { line
  , column: 1
  , endLine: line
  , endColumn: 1000  -- End of line
  , message
  , severity: Error
  }

-- | Create a warning marker
warningMarker :: Int -> String -> Marker
warningMarker line message =
  { line
  , column: 1
  , endLine: line
  , endColumn: 1000
  , message
  , severity: Warning
  }

-- | Create an info marker
infoMarker :: Int -> String -> Marker
infoMarker line message =
  { line
  , column: 1
  , endLine: line
  , endColumn: 1000
  , message
  , severity: Info
  }

-- | Create a hint marker
hintMarker :: Int -> String -> Marker
hintMarker line message =
  { line
  , column: 1
  , endLine: line
  , endColumn: 1000
  , message
  , severity: Hint
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // language detection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detect language from filename
-- |
-- | ```purescript
-- | detectLanguage "app.js"      -- Just JavaScript
-- | detectLanguage "styles.css"  -- Just CSS
-- | detectLanguage "unknown.xyz" -- Nothing
-- | ```
detectLanguage :: String -> Maybe Language
detectLanguage filename =
  let
    ext = getExtension filename
  in case ext of
    "js" -> Just JavaScript
    "jsx" -> Just JavaScript
    "mjs" -> Just JavaScript
    "cjs" -> Just JavaScript
    "ts" -> Just TypeScript
    "tsx" -> Just TypeScript
    "mts" -> Just TypeScript
    "cts" -> Just TypeScript
    "html" -> Just HTML
    "htm" -> Just HTML
    "xhtml" -> Just HTML
    "css" -> Just CSS
    "scss" -> Just CSS
    "sass" -> Just CSS
    "less" -> Just CSS
    "json" -> Just JSON
    "jsonc" -> Just JSON
    "md" -> Just Markdown
    "markdown" -> Just Markdown
    "mdx" -> Just Markdown
    "purs" -> Just PureScript
    _ -> Nothing
  where
  getExtension :: String -> String
  getExtension fname =
    let parts = String.split (Pattern ".") fname
    in case parts of
      [] -> ""
      xs -> fromMaybe "" (lastElement xs)
  
  lastElement :: forall a. Array a -> Maybe a
  lastElement arr = case arr of
    [] -> Nothing
    _ -> Just (unsafeLast arr)
  
  -- Safe in context because we check for empty array
  unsafeLast :: forall a. Array a -> a
  unsafeLast arr = 
    let len = arrayLength arr
    in unsafeIndex arr (len - 1)

foreign import arrayLength :: forall a. Array a -> Int
foreign import unsafeIndex :: forall a. Array a -> Int -> a

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // editor props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Editor properties
type EditorProps i =
  { value :: String
  , language :: Language
  , theme :: Theme
  , lineNumbers :: Boolean
  , readOnly :: Boolean
  , minimap :: Boolean
  , wordWrap :: Boolean
  , tabSize :: Int
  , useTabs :: Boolean
  , autoCloseBrackets :: Boolean
  , autoCloseQuotes :: Boolean
  , bracketMatching :: Boolean
  , highlightActiveLine :: Boolean
  , codeFolding :: Boolean
  , markers :: Array Marker
  , className :: String
  , height :: String
  , onInit :: Maybe (EditorRef -> i)
  , onChange :: Maybe (String -> i)
  , onCursorChange :: Maybe (CursorPosition -> i)
  , onSelectionChange :: Maybe (Array Selection -> i)
  , onFocus :: Maybe i
  , onBlur :: Maybe i
  , onKeyDown :: Maybe (KeyboardEvent -> i)
  }

-- | Property modifier
type EditorProp i = EditorProps i -> EditorProps i

-- | Default editor properties
defaultProps :: forall i. EditorProps i
defaultProps =
  { value: ""
  , language: PlainText
  , theme: Light
  , lineNumbers: true
  , readOnly: false
  , minimap: false
  , wordWrap: false
  , tabSize: 2
  , useTabs: false
  , autoCloseBrackets: true
  , autoCloseQuotes: true
  , bracketMatching: true
  , highlightActiveLine: true
  , codeFolding: true
  , markers: []
  , className: ""
  , height: "400px"
  , onInit: Nothing
  , onChange: Nothing
  , onCursorChange: Nothing
  , onSelectionChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , onKeyDown: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set editor value
value :: forall i. String -> EditorProp i
value v props = props { value = v }

-- | Set language for syntax highlighting
language :: forall i. Language -> EditorProp i
language l props = props { language = l }

-- | Set color theme
theme :: forall i. Theme -> EditorProp i
theme t props = props { theme = t }

-- | Toggle line numbers
lineNumbers :: forall i. Boolean -> EditorProp i
lineNumbers ln props = props { lineNumbers = ln }

-- | Set read-only mode
readOnly :: forall i. Boolean -> EditorProp i
readOnly ro props = props { readOnly = ro }

-- | Toggle minimap
minimap :: forall i. Boolean -> EditorProp i
minimap m props = props { minimap = m }

-- | Toggle word wrap
wordWrap :: forall i. Boolean -> EditorProp i
wordWrap ww props = props { wordWrap = ww }

-- | Set tab size
tabSize :: forall i. Int -> EditorProp i
tabSize ts props = props { tabSize = ts }

-- | Use tabs instead of spaces
useTabs :: forall i. Boolean -> EditorProp i
useTabs ut props = props { useTabs = ut }

-- | Auto-close brackets
autoCloseBrackets :: forall i. Boolean -> EditorProp i
autoCloseBrackets acb props = props { autoCloseBrackets = acb }

-- | Auto-close quotes
autoCloseQuotes :: forall i. Boolean -> EditorProp i
autoCloseQuotes acq props = props { autoCloseQuotes = acq }

-- | Enable bracket matching
bracketMatching :: forall i. Boolean -> EditorProp i
bracketMatching bm props = props { bracketMatching = bm }

-- | Highlight active line
highlightActiveLine :: forall i. Boolean -> EditorProp i
highlightActiveLine hal props = props { highlightActiveLine = hal }

-- | Enable code folding
codeFolding :: forall i. Boolean -> EditorProp i
codeFolding cf props = props { codeFolding = cf }

-- | Set error/warning markers
markers :: forall i. Array Marker -> EditorProp i
markers m props = props { markers = m }

-- | Add custom class
className :: forall i. String -> EditorProp i
className c props = props { className = props.className <> " " <> c }

-- | Set editor height
height :: forall i. String -> EditorProp i
height h props = props { height = h }

-- | Callback when editor is initialized
onInit :: forall i. (EditorRef -> i) -> EditorProp i
onInit handler props = props { onInit = Just handler }

-- | Callback when content changes
onChange :: forall i. (String -> i) -> EditorProp i
onChange handler props = props { onChange = Just handler }

-- | Callback when cursor position changes
onCursorChange :: forall i. (CursorPosition -> i) -> EditorProp i
onCursorChange handler props = props { onCursorChange = Just handler }

-- | Callback when selection changes
onSelectionChange :: forall i. (Array Selection -> i) -> EditorProp i
onSelectionChange handler props = props { onSelectionChange = Just handler }

-- | Callback when editor gains focus
onFocus :: forall i. i -> EditorProp i
onFocus handler props = props { onFocus = Just handler }

-- | Callback when editor loses focus
onBlur :: forall i. i -> EditorProp i
onBlur handler props = props { onBlur = Just handler }

-- | Callback for keydown events
onKeyDown :: forall i. (KeyboardEvent -> i) -> EditorProp i
onKeyDown handler props = props { onKeyDown = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // diff editor props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Diff editor properties
type DiffEditorProps i =
  { original :: String
  , modified :: String
  , language :: Language
  , theme :: Theme
  , renderSideBySide :: Boolean
  , className :: String
  , height :: String
  }

-- | Diff editor property modifier
type DiffEditorProp i = DiffEditorProps i -> DiffEditorProps i

-- | Default diff editor properties
defaultDiffProps :: forall i. DiffEditorProps i
defaultDiffProps =
  { original: ""
  , modified: ""
  , language: PlainText
  , theme: Light
  , renderSideBySide: true
  , className: ""
  , height: "400px"
  }

-- | Set original (left) content
original :: forall i. String -> DiffEditorProp i
original o props = props { original = o }

-- | Set modified (right) content
modified :: forall i. String -> DiffEditorProp i
modified m props = props { modified = m }

-- | Set diff language
diffLanguage :: forall i. Language -> DiffEditorProp i
diffLanguage l props = props { language = l }

-- | Set diff theme
diffTheme :: forall i. Theme -> DiffEditorProp i
diffTheme t props = props { theme = t }

-- | Render side by side (true) or inline (false)
renderSideBySide :: forall i. Boolean -> DiffEditorProp i
renderSideBySide sbs props = props { renderSideBySide = sbs }

-- | Add custom class to diff editor
diffClassName :: forall i. String -> DiffEditorProp i
diffClassName c props = props { className = props.className <> " " <> c }

-- | Set diff editor height
diffHeight :: forall i. String -> DiffEditorProp i
diffHeight h props = props { height = h }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base editor container classes
editorContainerClasses :: String
editorContainerClasses =
  "relative rounded-md border border-border bg-background overflow-hidden font-mono text-sm"

-- | Gutter classes
gutterClasses :: String
gutterClasses =
  "select-none text-right pr-2 text-muted-foreground bg-muted/30"

-- | Active line highlight classes (used by JS for dynamic highlighting)
_activeLineClasses :: String
_activeLineClasses =
  "bg-muted/50"

-- | Error marker classes
errorMarkerClasses :: String
errorMarkerClasses =
  "bg-destructive/20 border-l-2 border-destructive"

-- | Warning marker classes
warningMarkerClasses :: String
warningMarkerClasses =
  "bg-yellow-500/20 border-l-2 border-yellow-500"

-- | Render the code editor
codeEditor :: forall w i. Array (EditorProp i) -> HH.HTML w i
codeEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    themeClass = case props.theme of
      Dark -> "code-editor-dark"
      Light -> "code-editor-light"
    editorId = "code-editor-" <> show (String.length props.value)
  in
    HH.div
      [ cls [ editorContainerClasses, themeClass, props.className ]
      , HP.style ("height: " <> props.height)
      , HP.id editorId
      , HP.attr (HH.AttrName "data-language") (show props.language)
      , HP.attr (HH.AttrName "data-theme") (show props.theme)
      , HP.attr (HH.AttrName "data-line-numbers") (if props.lineNumbers then "true" else "false")
      , HP.attr (HH.AttrName "data-read-only") (if props.readOnly then "true" else "false")
      , HP.attr (HH.AttrName "data-minimap") (if props.minimap then "true" else "false")
      , HP.attr (HH.AttrName "data-word-wrap") (if props.wordWrap then "true" else "false")
      , HP.attr (HH.AttrName "data-tab-size") (show props.tabSize)
      , HP.attr (HH.AttrName "data-use-tabs") (if props.useTabs then "true" else "false")
      , HP.attr (HH.AttrName "data-auto-close-brackets") (if props.autoCloseBrackets then "true" else "false")
      , HP.attr (HH.AttrName "data-bracket-matching") (if props.bracketMatching then "true" else "false")
      , HP.attr (HH.AttrName "data-highlight-active-line") (if props.highlightActiveLine then "true" else "false")
      , HP.attr (HH.AttrName "data-code-folding") (if props.codeFolding then "true" else "false")
      , ARIA.role "textbox"
      , ARIA.label "Code editor"
      , HP.attr (HH.AttrName "aria-multiline") "true"
      ]
      [ -- Toolbar (find/replace, settings)
        renderToolbar props
      , -- Main editor area
        HH.div
          [ cls [ "flex h-full" ] ]
          [ -- Line numbers gutter
            if props.lineNumbers
              then renderGutter props
              else HH.text ""
          , -- Code content area
            renderEditorContent props
          , -- Minimap
            if props.minimap
              then renderMinimap props
              else HH.text ""
          ]
      , -- Markers overlay
        renderMarkers props
      , -- Status bar
        renderStatusBar props
      ]

-- | Render editor toolbar
renderToolbar :: forall w i. EditorProps i -> HH.HTML w i
renderToolbar _props =
  HH.div
    [ cls [ "hidden absolute top-0 left-0 right-0 z-10 flex items-center gap-2 px-2 py-1 bg-muted/50 border-b border-border" ]
    , HP.attr (HH.AttrName "data-toolbar") "true"
    ]
    [ -- Find input (shown with Ctrl+F)
      HH.div
        [ cls [ "hidden flex-1 max-w-xs" ]
        , HP.attr (HH.AttrName "data-find-container") "true"
        ]
        [ HH.input
            [ cls [ "flex h-7 w-full rounded-md border border-input bg-transparent px-2 py-1 text-sm placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-ring" ]
            , HP.type_ HP.InputText
            , HP.placeholder "Find..."
            , HP.attr (HH.AttrName "data-find-input") "true"
            ]
        ]
    , -- Replace input (shown with Ctrl+H)
      HH.div
        [ cls [ "hidden flex-1 max-w-xs" ]
        , HP.attr (HH.AttrName "data-replace-container") "true"
        ]
        [ HH.input
            [ cls [ "flex h-7 w-full rounded-md border border-input bg-transparent px-2 py-1 text-sm placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-ring" ]
            , HP.type_ HP.InputText
            , HP.placeholder "Replace..."
            , HP.attr (HH.AttrName "data-replace-input") "true"
            ]
        ]
    ]

-- | Render line numbers gutter
renderGutter :: forall w i. EditorProps i -> HH.HTML w i
renderGutter props =
  let
    lineCount = countLines props.value
    errorLines = map _.line (filter (\m -> m.severity == Error) props.markers)
    warningLines = map _.line (filter (\m -> m.severity == Warning) props.markers)
  in
    HH.div
      [ cls [ gutterClasses, "flex-none w-12 py-1 overflow-hidden" ]
      , HP.attr (HH.AttrName "data-gutter") "true"
      , ARIA.hidden "true"
      ]
      (map (renderLineNumber errorLines warningLines) (range 1 lineCount))

-- | Render a single line number
renderLineNumber :: forall w i. Array Int -> Array Int -> Int -> HH.HTML w i
renderLineNumber errorLines warningLines line =
  let
    hasError = elem line errorLines
    hasWarning = elem line warningLines
    markerClass = 
      if hasError then "text-destructive font-bold"
      else if hasWarning then "text-yellow-500 font-bold"
      else ""
  in
    HH.div
      [ cls [ "h-5 leading-5 text-xs", markerClass ]
      , HP.attr (HH.AttrName "data-line-number") (show line)
      ]
      [ HH.text (show line) ]

-- | Render editor content area
renderEditorContent :: forall w i. EditorProps i -> HH.HTML w i
renderEditorContent props =
  HH.div
    [ cls [ "flex-1 overflow-auto" ]
    , HP.attr (HH.AttrName "data-editor-content") "true"
    ]
    [ -- Hidden textarea for actual input
      HH.textarea
        [ cls [ "absolute opacity-0 pointer-events-none" ]
        , HP.value props.value
        , HP.readOnly props.readOnly
        , HP.attr (HH.AttrName "data-editor-textarea") "true"
        , HP.attr (HH.AttrName "autocapitalize") "off"
        , HP.attr (HH.AttrName "autocomplete") "off"
        , HP.attr (HH.AttrName "autocorrect") "off"
        , HP.attr (HH.AttrName "spellcheck") "false"
        ]
    , -- Syntax highlighted content
      HH.div
        [ cls [ "py-1 px-2" ]
        , HP.attr (HH.AttrName "data-highlighted-content") "true"
        ]
        [ renderHighlightedCode props ]
    ]

-- | Render syntax-highlighted code
renderHighlightedCode :: forall w i. EditorProps i -> HH.HTML w i
renderHighlightedCode props =
  HH.pre
    [ cls [ "m-0 p-0 font-mono text-sm leading-5 whitespace-pre" <> wrapClass ]
    , HP.attr (HH.AttrName "data-language") (show props.language)
    ]
    [ HH.code_
        [ HH.text props.value ]
    ]
  where
  wrapClass = if props.wordWrap then " whitespace-pre-wrap break-words" else ""

-- | Render minimap
renderMinimap :: forall w i. EditorProps i -> HH.HTML w i
renderMinimap props =
  HH.div
    [ cls [ "flex-none w-24 bg-muted/20 border-l border-border overflow-hidden" ]
    , HP.attr (HH.AttrName "data-minimap") "true"
    , ARIA.hidden "true"
    ]
    [ HH.div
        [ cls [ "p-1 text-[2px] leading-[3px] font-mono whitespace-pre overflow-hidden" ]
        , HP.style "transform: scale(0.2); transform-origin: top left; width: 500%;"
        ]
        [ HH.text props.value ]
    ]

-- | Render error/warning markers
renderMarkers :: forall w i. EditorProps i -> HH.HTML w i
renderMarkers props =
  if null props.markers
    then HH.text ""
    else HH.div
      [ cls [ "absolute top-0 left-0 right-0 pointer-events-none" ]
      , HP.attr (HH.AttrName "data-markers") "true"
      ]
      (map renderMarker props.markers)

-- | Render a single marker
renderMarker :: forall w i. Marker -> HH.HTML w i
renderMarker marker =
  let
    markerClass = case marker.severity of
      Error -> errorMarkerClasses
      Warning -> warningMarkerClasses
      Info -> "bg-blue-500/20 border-l-2 border-blue-500"
      Hint -> "bg-green-500/20 border-l-2 border-green-500"
    topOffset = (marker.line - 1) * 20  -- 20px per line (h-5)
  in
    HH.div
      [ cls [ "absolute left-12 right-0 h-5", markerClass ]
      , HP.style ("top: " <> show topOffset <> "px")
      , HP.title marker.message
      , HP.attr (HH.AttrName "data-marker-line") (show marker.line)
      , HP.attr (HH.AttrName "data-marker-severity") (show marker.severity)
      ]
      []

-- | Render status bar
renderStatusBar :: forall w i. EditorProps i -> HH.HTML w i
renderStatusBar props =
  let
    lineCount = countLines props.value
    charCount = String.length props.value
    langDisplay = show props.language
    errorCount = countMarkers Error props.markers
    warningCount = countMarkers Warning props.markers
  in
    HH.div
      [ cls [ "absolute bottom-0 left-0 right-0 flex items-center justify-between px-2 py-0.5 text-xs text-muted-foreground bg-muted/30 border-t border-border" ]
      , HP.attr (HH.AttrName "data-status-bar") "true"
      ]
      [ -- Left side: position info
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ HH.span
              [ HP.attr (HH.AttrName "data-cursor-position") "true" ]
              [ HH.text "Ln 1, Col 1" ]
          , HH.span [] [ HH.text "|" ]
          , HH.span [] [ HH.text (show lineCount <> " lines") ]
          , HH.span [] [ HH.text "|" ]
          , HH.span [] [ HH.text (show charCount <> " chars") ]
          ]
      , -- Right side: language and markers
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ if errorCount > 0
              then HH.span 
                [ cls [ "text-destructive" ] ]
                [ HH.text (show errorCount <> " errors") ]
              else HH.text ""
          , if warningCount > 0
              then HH.span
                [ cls [ "text-yellow-500" ] ]
                [ HH.text (show warningCount <> " warnings") ]
              else HH.text ""
          , HH.span [] [ HH.text langDisplay ]
          , if props.readOnly
              then HH.span [ cls [ "text-muted-foreground" ] ] [ HH.text "[Read-only]" ]
              else HH.text ""
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // diff editor
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render diff editor (two-pane comparison)
diffEditor :: forall w i. Array (DiffEditorProp i) -> HH.HTML w i
diffEditor propMods =
  let
    props = foldl (\p f -> f p) defaultDiffProps propMods
    themeClass = case props.theme of
      Dark -> "code-editor-dark"
      Light -> "code-editor-light"
  in
    HH.div
      [ cls [ "relative rounded-md border border-border bg-background overflow-hidden", themeClass, props.className ]
      , HP.style ("height: " <> props.height)
      , HP.attr (HH.AttrName "data-diff-editor") "true"
      ]
      [ if props.renderSideBySide
          then renderSideBySideDiff props
          else renderInlineDiff props
      ]

-- | Render side-by-side diff view
renderSideBySideDiff :: forall w i. DiffEditorProps i -> HH.HTML w i
renderSideBySideDiff props =
  HH.div
    [ cls [ "flex h-full" ] ]
    [ -- Original (left) pane
      HH.div
        [ cls [ "flex-1 border-r border-border overflow-auto" ]
        , HP.attr (HH.AttrName "data-diff-original") "true"
        ]
        [ HH.div
            [ cls [ "px-2 py-1 text-xs font-medium bg-muted/50 border-b border-border" ] ]
            [ HH.text "Original" ]
        , HH.pre
            [ cls [ "m-0 p-2 font-mono text-sm leading-5 whitespace-pre" ] ]
            [ HH.code_ [ HH.text props.original ] ]
        ]
    , -- Modified (right) pane
      HH.div
        [ cls [ "flex-1 overflow-auto" ]
        , HP.attr (HH.AttrName "data-diff-modified") "true"
        ]
        [ HH.div
            [ cls [ "px-2 py-1 text-xs font-medium bg-muted/50 border-b border-border" ] ]
            [ HH.text "Modified" ]
        , HH.pre
            [ cls [ "m-0 p-2 font-mono text-sm leading-5 whitespace-pre" ] ]
            [ HH.code_ [ HH.text props.modified ] ]
        ]
    ]

-- | Render inline diff view
renderInlineDiff :: forall w i. DiffEditorProps i -> HH.HTML w i
renderInlineDiff props =
  HH.div
    [ cls [ "h-full overflow-auto" ]
    , HP.attr (HH.AttrName "data-diff-inline") "true"
    ]
    [ HH.div
        [ cls [ "px-2 py-1 text-xs font-medium bg-muted/50 border-b border-border" ] ]
        [ HH.text "Diff" ]
    , HH.pre
        [ cls [ "m-0 p-2 font-mono text-sm leading-5 whitespace-pre" ] ]
        [ HH.code_
            [ -- Simplified - in production would compute actual diff
              HH.text ("- " <> props.original <> "\n+ " <> props.modified)
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an editor ref for imperative operations
createEditorRef :: Effect EditorRef
createEditorRef = EditorRef <$> Ref.new Nothing

-- | Get editor state
getEditorState :: EditorRef -> Effect (Maybe EditorState)
getEditorState (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure Nothing
    Just handle -> do
      val <- runEffectFn1 getValueImpl handle
      pos <- runEffectFn1 getCursorPositionImpl handle
      sels <- runEffectFn1 getSelectionsImpl handle
      pure $ Just
        { value: val
        , cursorPosition: pos
        , selections: sels
        , scrollTop: 0.0
        , scrollLeft: 0.0
        , isFocused: false
        }

-- | Get editor value
getValue :: EditorRef -> Effect String
getValue (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure ""
    Just handle -> runEffectFn1 getValueImpl handle

-- | Set editor value
setValue :: EditorRef -> String -> Effect Unit
setValue (EditorRef ref) val = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn2 setValueImpl handle val

-- | Get current selection
getSelection :: EditorRef -> Effect (Maybe Selection)
getSelection (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure Nothing
    Just handle -> do
      sel <- runEffectFn1 getSelectionImpl handle
      pure (Just sel)

-- | Set selection
setSelection :: EditorRef -> Selection -> Effect Unit
setSelection (EditorRef ref) sel = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn2 setSelectionImpl handle sel

-- | Get cursor position
getCursorPosition :: EditorRef -> Effect (Maybe CursorPosition)
getCursorPosition (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure Nothing
    Just handle -> do
      pos <- runEffectFn1 getCursorPositionImpl handle
      pure (Just pos)

-- | Set cursor position
setCursorPosition :: EditorRef -> CursorPosition -> Effect Unit
setCursorPosition (EditorRef ref) pos = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn2 setCursorPositionImpl handle pos

-- | Focus the editor
focus :: EditorRef -> Effect Unit
focus (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 focusEditorImpl handle

-- | Blur the editor
blur :: EditorRef -> Effect Unit
blur (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 blurEditorImpl handle

-- | Undo last edit
undo :: EditorRef -> Effect Unit
undo (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 undoImpl handle

-- | Redo last undone edit
redo :: EditorRef -> Effect Unit
redo (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 redoImpl handle

-- | Format document
format :: EditorRef -> Effect Unit
format (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 formatImpl handle

-- | Open find dialog
find :: EditorRef -> String -> Effect Unit
find (EditorRef ref) query = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn2 findImpl handle query

-- | Replace current match
replace :: EditorRef -> String -> String -> Effect Unit
replace (EditorRef ref) searchText replaceText = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn3 replaceImpl handle searchText replaceText

-- | Replace all matches
replaceAll :: EditorRef -> String -> String -> Effect Unit
replaceAll (EditorRef ref) searchText replaceText = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn3 replaceAllImpl handle searchText replaceText

-- | Go to specific line
goToLine :: EditorRef -> Int -> Effect Unit
goToLine (EditorRef ref) line = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn2 goToLineImpl handle line

-- | Insert text at cursor
insertText :: EditorRef -> String -> Effect Unit
insertText (EditorRef ref) text = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn2 insertTextImpl handle text

-- | Fold all code blocks
foldAll :: EditorRef -> Effect Unit
foldAll (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 foldAllImpl handle

-- | Unfold all code blocks
unfoldAll :: EditorRef -> Effect Unit
unfoldAll (EditorRef ref) = do
  maybeHandle <- Ref.read ref
  case maybeHandle of
    Nothing -> pure unit
    Just handle -> runEffectFn1 unfoldAllImpl handle

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Count lines in text
countLines :: String -> Int
countLines text = 
  let lines = String.split (Pattern "\n") text
  in max 1 (arrayLength lines)

-- | Count markers of a specific severity
countMarkers :: MarkerSeverity -> Array Marker -> Int
countMarkers severity markers' = arrayLength (filter (\m -> m.severity == severity) markers')

-- | Check if array is empty
null :: forall a. Array a -> Boolean
null arr = arrayLength arr == 0

-- | Check if element is in array
elem :: forall a. Eq a => a -> Array a -> Boolean
elem x arr = arrayLength (filter (_ == x) arr) > 0

-- | Generate range of integers
range :: Int -> Int -> Array Int
range start end = rangeImpl start end

foreign import rangeImpl :: Int -> Int -> Array Int

-- | Map over array
map :: forall a b. (a -> b) -> Array a -> Array b
map = mapImpl

foreign import mapImpl :: forall a b. (a -> b) -> Array a -> Array b
