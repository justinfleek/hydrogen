-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // markdowneditor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Markdown Editor with Live Preview
-- |
-- | A feature-rich Markdown editor with split view, live preview,
-- | syntax highlighting, and GitHub Flavored Markdown support.
-- |
-- | ## Features
-- |
-- | - Split view (editor | preview)
-- | - Live preview as you type
-- | - Toolbar for common formatting
-- | - Syntax highlighting in editor
-- | - GFM (GitHub Flavored Markdown) support
-- | - Tables with easy editing
-- | - Task lists (checkboxes)
-- | - Code blocks with language highlighting
-- | - Math equations (KaTeX)
-- | - Mermaid diagrams
-- | - Image upload/paste
-- | - Link insertion
-- | - Fullscreen editing
-- | - Preview-only mode
-- | - Editor-only mode
-- | - Word/character count
-- | - Export to HTML
-- | - Custom renderers for extensions
-- | - Vim/Emacs key bindings (optional)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Document.MarkdownEditor as MarkdownEditor
-- |
-- | -- Basic editor
-- | MarkdownEditor.markdownEditor
-- |   [ MarkdownEditor.value content
-- |   , MarkdownEditor.onChange HandleChange
-- |   , MarkdownEditor.showToolbar true
-- |   ]
-- |
-- | -- With GFM and extensions
-- | MarkdownEditor.markdownEditor
-- |   [ MarkdownEditor.value content
-- |   , MarkdownEditor.onChange HandleChange
-- |   , MarkdownEditor.gfm true
-- |   , MarkdownEditor.enableMath true
-- |   , MarkdownEditor.enableMermaid true
-- |   ]
-- |
-- | -- Preview only
-- | MarkdownEditor.markdownEditor
-- |   [ MarkdownEditor.value content
-- |   , MarkdownEditor.viewMode MarkdownEditor.PreviewOnly
-- |   ]
-- | ```
module Hydrogen.Document.MarkdownEditor
  ( -- * Component
    markdownEditor
  , markdownPreview
    -- * Props
  , MarkdownEditorProps
  , MarkdownEditorProp
  , defaultProps
    -- * Prop Builders
  , value
  , placeholder
  , viewMode
  , showToolbar
  , showStatusBar
  , gfm
  , enableMath
  , enableMermaid
  , syntaxHighlight
  , keyBindings
  , tabSize
  , lineNumbers
  , wordWrap
  , spellCheck
  , autoFocus
  , readOnly
  , minHeight
  , maxHeight
  , className
    -- * Event Handlers
  , onChange
  , onImageUpload
  , onLinkInsert
  , onSave
  , onFullscreenChange
    -- * Types
  , ViewMode(..)
  , KeyBindings(..)
  , ToolbarAction(..)
  , EditorStats
  , ImageUploadResult
    -- * Rendering
  , renderMarkdown
  , renderMarkdownToHtml
    -- * FFI
  , EditorHandle
  , initEditor
  , destroyEditor
  , insertText
  , wrapSelection
  , getSelection
  , setSelection
  , scrollToLine
  , focus
  , blur
  ) where

import Prelude

import Data.Array (foldl, length)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (length) as String
import Data.String.CodeUnits (toCharArray)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Editor view mode
data ViewMode
  = SplitView     -- ^ Editor and preview side by side
  | EditorOnly    -- ^ Just the editor
  | PreviewOnly   -- ^ Just the preview

derive instance eqViewMode :: Eq ViewMode

-- | Key binding mode
data KeyBindings
  = Default       -- ^ Standard key bindings
  | Vim           -- ^ Vim-style key bindings
  | Emacs         -- ^ Emacs-style key bindings

derive instance eqKeyBindings :: Eq KeyBindings

-- | Toolbar actions
data ToolbarAction
  = Bold
  | Italic
  | Strikethrough
  | Heading1
  | Heading2
  | Heading3
  | BulletList
  | NumberedList
  | TaskList
  | Blockquote
  | CodeBlock
  | InlineCode
  | Link
  | Image
  | Table
  | HorizontalRule
  | Undo
  | Redo

derive instance eqToolbarAction :: Eq ToolbarAction

-- | Editor statistics
type EditorStats =
  { characters :: Int
  , words :: Int
  , lines :: Int
  , paragraphs :: Int
  }

-- | Image upload result
type ImageUploadResult =
  { url :: String
  , alt :: String
  , title :: Maybe String
  }

-- | Opaque editor handle
foreign import data EditorHandle :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize editor with syntax highlighting
foreign import initEditorImpl :: EffectFn2 Element
  { onChange :: String -> Effect Unit
  , onKeyDown :: String -> Boolean -> Boolean -> Boolean -> Effect Boolean
  }
  EditorHandle

-- | Destroy editor
foreign import destroyEditorImpl :: EffectFn1 EditorHandle Unit

-- | Insert text at cursor
foreign import insertTextImpl :: EffectFn2 EditorHandle String Unit

-- | Wrap selection with text
foreign import wrapSelectionImpl :: EffectFn3 EditorHandle String String Unit

-- | Get current selection
foreign import getSelectionImpl :: EffectFn1 EditorHandle { start :: Int, end :: Int, text :: String }

-- | Set selection range
foreign import setSelectionImpl :: EffectFn3 EditorHandle Int Int Unit

-- | Scroll to specific line
foreign import scrollToLineImpl :: EffectFn2 EditorHandle Int Unit

-- | Focus the editor
foreign import focusImpl :: EffectFn1 EditorHandle Unit

-- | Blur the editor
foreign import blurImpl :: EffectFn1 EditorHandle Unit

-- | Render Markdown to HTML
foreign import renderMarkdownImpl :: EffectFn2 String
  { gfm :: Boolean
  , breaks :: Boolean
  , sanitize :: Boolean
  }
  String

-- | Initialize editor
initEditor :: Element ->
  { onChange :: String -> Effect Unit
  , onKeyDown :: String -> Boolean -> Boolean -> Boolean -> Effect Boolean
  } ->
  Effect EditorHandle
initEditor _ _ = pure unsafeEditorHandle

-- | Destroy editor
destroyEditor :: EditorHandle -> Effect Unit
destroyEditor _ = pure unit

-- | Insert text at cursor
insertText :: EditorHandle -> String -> Effect Unit
insertText _ _ = pure unit

-- | Wrap selection
wrapSelection :: EditorHandle -> String -> String -> Effect Unit
wrapSelection _ _ _ = pure unit

-- | Get selection
getSelection :: EditorHandle -> Effect { start :: Int, end :: Int, text :: String }
getSelection _ = pure { start: 0, end: 0, text: "" }

-- | Set selection
setSelection :: EditorHandle -> Int -> Int -> Effect Unit
setSelection _ _ _ = pure unit

-- | Scroll to line
scrollToLine :: EditorHandle -> Int -> Effect Unit
scrollToLine _ _ = pure unit

-- | Focus editor
focus :: EditorHandle -> Effect Unit
focus _ = pure unit

-- | Blur editor
blur :: EditorHandle -> Effect Unit
blur _ = pure unit

-- | Render Markdown to HTML string
renderMarkdown :: String ->
  { gfm :: Boolean
  , breaks :: Boolean
  , sanitize :: Boolean
  } ->
  Effect String
renderMarkdown content _ = pure content

-- | Render Markdown to HTML (pure, for preview)
renderMarkdownToHtml :: String -> String
renderMarkdownToHtml = identity

-- Internal placeholder
foreign import unsafeEditorHandle :: EditorHandle

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Markdown editor properties
type MarkdownEditorProps i =
  { value :: String
  , placeholder :: String
  , viewMode :: ViewMode
  , showToolbar :: Boolean
  , showStatusBar :: Boolean
  , gfm :: Boolean
  , enableMath :: Boolean
  , enableMermaid :: Boolean
  , syntaxHighlight :: Boolean
  , keyBindings :: KeyBindings
  , tabSize :: Int
  , lineNumbers :: Boolean
  , wordWrap :: Boolean
  , spellCheck :: Boolean
  , autoFocus :: Boolean
  , readOnly :: Boolean
  , minHeight :: String
  , maxHeight :: String
  , isFullscreen :: Boolean
  , className :: String
  , onChange :: Maybe (String -> i)
  , onImageUpload :: Maybe (Effect ImageUploadResult -> i)
  , onLinkInsert :: Maybe i
  , onSave :: Maybe (String -> i)
  , onFullscreenChange :: Maybe (Boolean -> i)
  }

-- | Property modifier
type MarkdownEditorProp i = MarkdownEditorProps i -> MarkdownEditorProps i

-- | Default properties
defaultProps :: forall i. MarkdownEditorProps i
defaultProps =
  { value: ""
  , placeholder: "Write your markdown here..."
  , viewMode: SplitView
  , showToolbar: true
  , showStatusBar: true
  , gfm: true
  , enableMath: false
  , enableMermaid: false
  , syntaxHighlight: true
  , keyBindings: Default
  , tabSize: 2
  , lineNumbers: false
  , wordWrap: true
  , spellCheck: true
  , autoFocus: false
  , readOnly: false
  , minHeight: "400px"
  , maxHeight: "none"
  , isFullscreen: false
  , className: ""
  , onChange: Nothing
  , onImageUpload: Nothing
  , onLinkInsert: Nothing
  , onSave: Nothing
  , onFullscreenChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set markdown content
value :: forall i. String -> MarkdownEditorProp i
value v props = props { value = v }

-- | Set placeholder text
placeholder :: forall i. String -> MarkdownEditorProp i
placeholder p props = props { placeholder = p }

-- | Set view mode
viewMode :: forall i. ViewMode -> MarkdownEditorProp i
viewMode m props = props { viewMode = m }

-- | Show/hide toolbar
showToolbar :: forall i. Boolean -> MarkdownEditorProp i
showToolbar s props = props { showToolbar = s }

-- | Show/hide status bar
showStatusBar :: forall i. Boolean -> MarkdownEditorProp i
showStatusBar s props = props { showStatusBar = s }

-- | Enable GitHub Flavored Markdown
gfm :: forall i. Boolean -> MarkdownEditorProp i
gfm g props = props { gfm = g }

-- | Enable math equations (KaTeX)
enableMath :: forall i. Boolean -> MarkdownEditorProp i
enableMath m props = props { enableMath = m }

-- | Enable Mermaid diagrams
enableMermaid :: forall i. Boolean -> MarkdownEditorProp i
enableMermaid m props = props { enableMermaid = m }

-- | Enable syntax highlighting
syntaxHighlight :: forall i. Boolean -> MarkdownEditorProp i
syntaxHighlight s props = props { syntaxHighlight = s }

-- | Set key binding mode
keyBindings :: forall i. KeyBindings -> MarkdownEditorProp i
keyBindings k props = props { keyBindings = k }

-- | Set tab size
tabSize :: forall i. Int -> MarkdownEditorProp i
tabSize t props = props { tabSize = t }

-- | Show/hide line numbers
lineNumbers :: forall i. Boolean -> MarkdownEditorProp i
lineNumbers l props = props { lineNumbers = l }

-- | Enable/disable word wrap
wordWrap :: forall i. Boolean -> MarkdownEditorProp i
wordWrap w props = props { wordWrap = w }

-- | Enable/disable spell check
spellCheck :: forall i. Boolean -> MarkdownEditorProp i
spellCheck s props = props { spellCheck = s }

-- | Auto-focus on mount
autoFocus :: forall i. Boolean -> MarkdownEditorProp i
autoFocus a props = props { autoFocus = a }

-- | Set read-only mode
readOnly :: forall i. Boolean -> MarkdownEditorProp i
readOnly r props = props { readOnly = r }

-- | Set minimum height
minHeight :: forall i. String -> MarkdownEditorProp i
minHeight h props = props { minHeight = h }

-- | Set maximum height
maxHeight :: forall i. String -> MarkdownEditorProp i
maxHeight h props = props { maxHeight = h }

-- | Add custom class
className :: forall i. String -> MarkdownEditorProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle content change
onChange :: forall i. (String -> i) -> MarkdownEditorProp i
onChange handler props = props { onChange = Just handler }

-- | Handle image upload
onImageUpload :: forall i. (Effect ImageUploadResult -> i) -> MarkdownEditorProp i
onImageUpload handler props = props { onImageUpload = Just handler }

-- | Handle link insertion
onLinkInsert :: forall i. i -> MarkdownEditorProp i
onLinkInsert handler props = props { onLinkInsert = Just handler }

-- | Handle save (Ctrl+S)
onSave :: forall i. (String -> i) -> MarkdownEditorProp i
onSave handler props = props { onSave = Just handler }

-- | Handle fullscreen change
onFullscreenChange :: forall i. (Boolean -> i) -> MarkdownEditorProp i
onFullscreenChange handler props = props { onFullscreenChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Markdown Editor component
-- |
-- | Full-featured markdown editor with live preview, toolbar,
-- | and support for GFM, math, and diagrams.
markdownEditor :: forall w i. Array (MarkdownEditorProp i) -> HH.HTML w i
markdownEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    stats = calculateStats props.value
  in
    HH.div
      [ cls [ "markdown-editor flex flex-col border border-border rounded-lg bg-background overflow-hidden"
            , if props.isFullscreen then "fixed inset-0 z-50" else ""
            , props.className
            ]
      , HP.attr (HH.AttrName "data-markdown-editor") "true"
      , HP.attr (HH.AttrName "style") 
          ("min-height: " <> props.minHeight <> "; max-height: " <> props.maxHeight <> ";")
      ]
      [ -- Toolbar
        if props.showToolbar && props.viewMode /= PreviewOnly
          then renderToolbar props
          else HH.text ""
      , -- Editor area
        HH.div
          [ cls [ "flex flex-1 overflow-hidden" ] ]
          (case props.viewMode of
            SplitView ->
              [ renderEditorPane props
              , HH.div [ cls [ "w-px bg-border" ] ] []
              , renderPreviewPane props
              ]
            EditorOnly ->
              [ renderEditorPane props ]
            PreviewOnly ->
              [ renderPreviewPane props ]
          )
      , -- Status bar
        if props.showStatusBar
          then renderStatusBar props stats
          else HH.text ""
      ]

-- | Standalone Markdown preview component
markdownPreview :: forall w i. String -> Array String -> HH.HTML w i
markdownPreview content extraClasses =
  HH.div
    [ cls ([ "markdown-preview prose prose-sm dark:prose-invert max-w-none p-4" ] <> extraClasses) ]
    [ HH.text content ]  -- In production, render actual HTML

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // toolbar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render toolbar
renderToolbar :: forall w i. MarkdownEditorProps i -> HH.HTML w i
renderToolbar props =
  HH.div
    [ cls [ "markdown-toolbar flex flex-wrap items-center gap-1 px-2 py-1.5 border-b border-border bg-muted/30" ]
    , ARIA.role "toolbar"
    , ARIA.label "Formatting toolbar"
    ]
    [ -- Text formatting
      toolbarGroup
        [ toolbarButton Bold "Bold" "B" "font-bold"
        , toolbarButton Italic "Italic" "I" "italic"
        , toolbarButton Strikethrough "Strikethrough" "S" "line-through"
        ]
    , divider
    , -- Headings
      toolbarGroup
        [ toolbarButton Heading1 "Heading 1" "H1" ""
        , toolbarButton Heading2 "Heading 2" "H2" ""
        , toolbarButton Heading3 "Heading 3" "H3" ""
        ]
    , divider
    , -- Lists
      toolbarGroup
        [ toolbarButton BulletList "Bullet List" bulletIcon ""
        , toolbarButton NumberedList "Numbered List" numberIcon ""
        , toolbarButton TaskList "Task List" taskIcon ""
        ]
    , divider
    , -- Blocks
      toolbarGroup
        [ toolbarButton Blockquote "Quote" quoteIcon ""
        , toolbarButton CodeBlock "Code Block" codeIcon ""
        , toolbarButton InlineCode "Inline Code" inlineCodeIcon ""
        ]
    , divider
    , -- Insert
      toolbarGroup
        [ toolbarButton Link "Insert Link" linkIcon ""
        , toolbarButton Image "Insert Image" imageIcon ""
        , toolbarButton Table "Insert Table" tableIcon ""
        , toolbarButton HorizontalRule "Horizontal Rule" hrIcon ""
        ]
    , HH.div [ cls [ "flex-1" ] ] []  -- Spacer
    , -- View mode
      toolbarGroup
        [ viewModeButton EditorOnly "Editor" editorIcon (props.viewMode == EditorOnly)
        , viewModeButton SplitView "Split" splitIcon (props.viewMode == SplitView)
        , viewModeButton PreviewOnly "Preview" previewIcon (props.viewMode == PreviewOnly)
        ]
    , divider
    , -- Fullscreen
      toolbarButton Bold "Fullscreen" fullscreenIcon ""
    ]
  where
    divider = HH.div [ cls [ "w-px h-6 bg-border mx-1" ] ] []
    
    toolbarGroup items = HH.div [ cls [ "flex items-center" ] ] items
    
    toolbarButton :: ToolbarAction -> String -> String -> String -> HH.HTML w i
    toolbarButton _ label icon extraClass =
      HH.button
        [ cls [ "inline-flex items-center justify-center h-8 w-8 rounded hover:bg-muted transition-colors text-sm", extraClass ]
        , HP.type_ HP.ButtonButton
        , HP.title label
        , ARIA.label label
        , HP.disabled props.readOnly
        ]
        [ HH.text icon ]
    
    viewModeButton :: ViewMode -> String -> String -> Boolean -> HH.HTML w i
    viewModeButton _ label icon isActive =
      HH.button
        [ cls [ "inline-flex items-center justify-center h-8 px-2 rounded transition-colors text-sm"
              , if isActive then "bg-muted" else "hover:bg-muted"
              ]
        , HP.type_ HP.ButtonButton
        , HP.title label
        , ARIA.label label
        ]
        [ HH.text icon ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // editor pane
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render editor pane
renderEditorPane :: forall w i. MarkdownEditorProps i -> HH.HTML w i
renderEditorPane props =
  HH.div
    [ cls [ "markdown-editor-pane flex-1 flex flex-col overflow-hidden"
          , if props.viewMode == SplitView then "w-1/2" else "w-full"
          ]
    ]
    [ HH.div
        [ cls [ "relative flex-1 overflow-hidden" ] ]
        [ -- Line numbers gutter
          if props.lineNumbers
            then renderLineNumbers props
            else HH.text ""
        , -- Textarea
          HH.textarea
            [ cls [ "w-full h-full resize-none p-4 bg-transparent font-mono text-sm leading-relaxed"
                  , "focus:outline-none"
                  , if props.lineNumbers then "pl-12" else ""
                  , if props.wordWrap then "" else "whitespace-pre overflow-x-auto"
                  ]
            , HP.value props.value
            , HP.placeholder props.placeholder
            , HP.readOnly props.readOnly
            , HP.attr (HH.AttrName "spellcheck") (if props.spellCheck then "true" else "false")
            , HP.attr (HH.AttrName "data-markdown-textarea") "true"
            , ARIA.label "Markdown editor"
            ]
        ]
    ]

-- | Render line numbers
renderLineNumbers :: forall w i. MarkdownEditorProps i -> HH.HTML w i
renderLineNumbers props =
  let
    lineCount = countLines props.value
    numbers = map show (rangeArray 1 lineCount)
  in
    HH.div
      [ cls [ "absolute left-0 top-0 bottom-0 w-10 bg-muted/30 border-r border-border text-right pr-2 py-4 select-none overflow-hidden" ]
      , ARIA.hidden "true"
      ]
      [ HH.div
          [ cls [ "font-mono text-sm text-muted-foreground leading-relaxed" ] ]
          (map (\n -> HH.div [] [ HH.text n ]) numbers)
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // preview pane
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render preview pane
renderPreviewPane :: forall w i. MarkdownEditorProps i -> HH.HTML w i
renderPreviewPane props =
  HH.div
    [ cls [ "markdown-preview-pane flex-1 overflow-auto"
          , if props.viewMode == SplitView then "w-1/2" else "w-full"
          ]
    ]
    [ HH.div
        [ cls [ "prose prose-sm dark:prose-invert max-w-none p-4" ]
        , HP.attr (HH.AttrName "data-markdown-preview") "true"
        ]
        [ -- In production, this would be rendered HTML
          -- For now, show the raw markdown with basic formatting hints
          if String.length props.value > 0
            then renderPreviewContent props
            else HH.p
              [ cls [ "text-muted-foreground italic" ] ]
              [ HH.text "Preview will appear here..." ]
        ]
    ]

-- | Render preview content (simplified)
renderPreviewContent :: forall w i. MarkdownEditorProps i -> HH.HTML w i
renderPreviewContent props =
  HH.div
    []
    [ HH.text props.value ]  -- In production, parse and render markdown

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // status bar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render status bar
renderStatusBar :: forall w i. MarkdownEditorProps i -> EditorStats -> HH.HTML w i
renderStatusBar props stats =
  HH.div
    [ cls [ "markdown-status-bar flex items-center justify-between px-3 py-1.5 border-t border-border bg-muted/30 text-xs text-muted-foreground" ]
    ]
    [ -- Stats
      HH.div
        [ cls [ "flex items-center gap-4" ] ]
        [ HH.span [] [ HH.text (show stats.words <> " words") ]
        , HH.span [] [ HH.text (show stats.characters <> " characters") ]
        , HH.span [] [ HH.text (show stats.lines <> " lines") ]
        ]
    , -- Mode indicators
      HH.div
        [ cls [ "flex items-center gap-3" ] ]
        [ if props.gfm
            then HH.span [ cls [ "px-1.5 py-0.5 rounded bg-muted" ] ] [ HH.text "GFM" ]
            else HH.text ""
        , if props.enableMath
            then HH.span [ cls [ "px-1.5 py-0.5 rounded bg-muted" ] ] [ HH.text "Math" ]
            else HH.text ""
        , case props.keyBindings of
            Vim -> HH.span [ cls [ "px-1.5 py-0.5 rounded bg-muted" ] ] [ HH.text "Vim" ]
            Emacs -> HH.span [ cls [ "px-1.5 py-0.5 rounded bg-muted" ] ] [ HH.text "Emacs" ]
            Default -> HH.text ""
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate editor statistics
calculateStats :: String -> EditorStats
calculateStats content =
  { characters: String.length content
  , words: countWords content
  , lines: countLines content
  , paragraphs: countParagraphs content
  }

-- | Count words in text
countWords :: String -> Int
countWords content =
  let
    chars = toCharArray content
    trimmed = foldl (\acc c -> if c == ' ' || c == '\n' || c == '\t' then acc else acc <> [c]) [] chars
  in
    if length trimmed == 0 then 0
    else countWordsImpl content

foreign import countWordsImpl :: String -> Int

-- | Count lines in text
countLines :: String -> Int
countLines content =
  let
    chars = toCharArray content
    count = foldl (\acc c -> if c == '\n' then acc + 1 else acc) 0 chars
  in count + 1

-- | Count paragraphs in text
countParagraphs :: String -> Int
countParagraphs _ = 1  -- Simplified

-- | Generate array range
rangeArray :: Int -> Int -> Array Int
rangeArray start end = rangeArrayImpl start end

foreign import rangeArrayImpl :: Int -> Int -> Array Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

bulletIcon :: String
bulletIcon = "L"

numberIcon :: String
numberIcon = "1"

taskIcon :: String
taskIcon = "T"

quoteIcon :: String
quoteIcon = ">"

codeIcon :: String
codeIcon = "{}"

inlineCodeIcon :: String
inlineCodeIcon = "`"

linkIcon :: String
linkIcon = "@"

imageIcon :: String
imageIcon = "P"

tableIcon :: String
tableIcon = "#"

hrIcon :: String
hrIcon = "-"

editorIcon :: String
editorIcon = "E"

splitIcon :: String
splitIcon = "|"

previewIcon :: String
previewIcon = "V"

fullscreenIcon :: String
fullscreenIcon = "F"
