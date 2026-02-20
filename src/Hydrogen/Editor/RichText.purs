-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // richtext
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rich Text Editor component (TipTap/ProseMirror-style)
-- |
-- | A full-featured WYSIWYG editor with contenteditable, formatting toolbar,
-- | keyboard shortcuts, and structured content output.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Editor.RichText as RichText
-- |
-- | -- Basic editor
-- | RichText.editor
-- |   [ RichText.value state.content
-- |   , RichText.onChange HandleContentChange
-- |   , RichText.placeholder "Start writing..."
-- |   ]
-- |
-- | -- Full-featured editor with toolbar
-- | RichText.editorWithToolbar
-- |   [ RichText.value state.content
-- |   , RichText.onChange HandleContentChange
-- |   , RichText.showWordCount true
-- |   , RichText.characterLimit 5000
-- |   , RichText.mentions state.mentionSuggestions
-- |   ]
-- |
-- | -- Read-only mode
-- | RichText.editor
-- |   [ RichText.value state.content
-- |   , RichText.readOnly true
-- |   ]
-- | ```
-- |
-- | ## Keyboard Shortcuts
-- |
-- | - `Ctrl+B` / `Cmd+B` - Bold
-- | - `Ctrl+I` / `Cmd+I` - Italic
-- | - `Ctrl+U` / `Cmd+U` - Underline
-- | - `Ctrl+Shift+S` - Strikethrough
-- | - `Ctrl+E` / `Cmd+E` - Code (inline)
-- | - `Ctrl+Shift+1/2/3` - Heading 1/2/3
-- | - `Ctrl+Shift+7` - Numbered list
-- | - `Ctrl+Shift+8` - Bullet list
-- | - `Ctrl+Shift+9` - Task list
-- | - `Ctrl+Z` / `Cmd+Z` - Undo
-- | - `Ctrl+Shift+Z` / `Cmd+Shift+Z` - Redo
-- | - `Ctrl+K` / `Cmd+K` - Insert link
-- | - `/` - Slash commands
-- | - `@` - Mentions
-- |
-- | ## Toolbar Buttons
-- |
-- | The toolbar includes buttons for:
-- | - Text formatting (bold, italic, underline, strikethrough, code)
-- | - Headings (H1, H2, H3, paragraph)
-- | - Lists (bullet, numbered, task)
-- | - Alignment (left, center, right, justify)
-- | - Links and images
-- | - Tables (insert, add/remove rows/columns)
-- | - Code blocks and blockquotes
-- | - Horizontal rule
-- | - Undo/redo
-- |
-- | ## Bubble Menu
-- |
-- | A floating toolbar appears on text selection with quick formatting options.
-- |
-- | ## Slash Commands
-- |
-- | Type `/` at the start of a line or after whitespace to open the command palette:
-- | - `/heading1`, `/heading2`, `/heading3`
-- | - `/bullet`, `/numbered`, `/task`
-- | - `/quote`, `/code`, `/hr`
-- | - `/image`, `/table`
-- |
-- | ## Mentions
-- |
-- | Type `@` to trigger the mentions popup. Provide suggestions via the
-- | `mentions` prop.
-- |
-- | ## Output Formats
-- |
-- | - HTML: Standard HTML string output
-- | - JSON: Structured document representation
-- |
-- | ```purescript
-- | -- Get HTML output
-- | htmlContent <- RichText.getHtml editorRef
-- |
-- | -- Get JSON output
-- | jsonContent <- RichText.getJson editorRef
-- |
-- | -- Set content from HTML
-- | RichText.setHtml editorRef "<p>Hello world</p>"
-- |
-- | -- Set content from JSON
-- | RichText.setJson editorRef jsonDoc
-- | ```
module Hydrogen.Editor.RichText
  ( -- * Editor Components
    editor
  , editorWithToolbar
  , toolbar
  , bubbleMenu
  , slashCommandMenu
  , mentionMenu
    -- * Toolbar Components
  , toolbarGroup
  , toolbarButton
  , toolbarSeparator
  , toolbarSelect
    -- * Props
  , EditorProps
  , EditorProp
  , defaultProps
    -- * Prop Builders
  , value
  , onChange
  , onHtmlChange
  , onJsonChange
  , onSelectionChange
  , onFocus
  , onBlur
  , placeholder
  , readOnly
  , disabled
  , autofocus
  , characterLimit
  , showCharacterCount
  , showWordCount
  , className
  , editorClassName
  , toolbarClassName
  , mentions
  , onMentionSearch
  , onMentionSelect
  , slashCommands
  , enableBubbleMenu
  , enableSlashCommands
  , enableMentions
  , enableTables
  , enableImages
  , enableCodeBlocks
  , ariaLabel
  , ariaDescribedBy
    -- * Types
  , EditorContent(..)
  , ContentNode(..)
  , Mark(..)
  , TextAlign(..)
  , HeadingLevel(..)
  , ListType(..)
  , SlashCommand(..)
  , Mention(..)
  , Selection(..)
  , ToolbarState(..)
    -- * Commands
  , EditorCommand(..)
  , formatBold
  , formatItalic
  , formatUnderline
  , formatStrikethrough
  , formatCode
  , setHeading
  , setParagraph
  , toggleBulletList
  , toggleNumberedList
  , toggleTaskList
  , setAlignment
  , insertLink
  , insertImage
  , insertTable
  , insertCodeBlock
  , insertBlockquote
  , insertHorizontalRule
  , undo
  , redo
  , focus
  , blur
    -- * FFI
  , EditorElement
  , initEditor
  , destroyEditor
  , getHtml
  , setHtml
  , getJson
  , setJson
  , getSelection
  , executeCommand
  , getCharacterCount
  , getWordCount
  , registerShortcuts
  , unregisterShortcuts
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Foreign (Foreign)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.Event.Event (Event)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Editor content representation
data EditorContent
  = HtmlContent String
  | JsonContent (Array ContentNode)

-- | Document node types
data ContentNode
  = TextNode String (Array Mark)
  | ParagraphNode (Array ContentNode) TextAlign
  | HeadingNode HeadingLevel (Array ContentNode)
  | BulletListNode (Array ContentNode)
  | OrderedListNode (Array ContentNode)
  | TaskListNode (Array { checked :: Boolean, content :: Array ContentNode })
  | ListItemNode (Array ContentNode)
  | BlockquoteNode (Array ContentNode)
  | CodeBlockNode String (Maybe String) -- content, language
  | ImageNode { src :: String, alt :: String, title :: Maybe String }
  | LinkNode String (Array ContentNode) -- href, children
  | TableNode (Array (Array ContentNode)) -- rows of cells
  | HorizontalRuleNode
  | MentionNode Mention

-- | Text marks (formatting)
data Mark
  = Bold
  | Italic
  | Underline
  | Strikethrough
  | Code
  | Link String -- href

derive instance eqMark :: Eq Mark

-- | Text alignment options
data TextAlign
  = AlignLeft
  | AlignCenter
  | AlignRight
  | AlignJustify

derive instance eqTextAlign :: Eq TextAlign

-- | Heading levels
data HeadingLevel
  = H1
  | H2
  | H3

derive instance eqHeadingLevel :: Eq HeadingLevel

-- | List types
data ListType
  = BulletList
  | NumberedList
  | TaskList

derive instance eqListType :: Eq ListType

-- | Slash command definition
type SlashCommand =
  { id :: String
  , label :: String
  , description :: String
  , icon :: Maybe String
  , keywords :: Array String
  }

-- | Mention data
type Mention =
  { id :: String
  , label :: String
  , avatar :: Maybe String
  }

-- | Selection state
type Selection =
  { from :: Int
  , to :: Int
  , empty :: Boolean
  }

-- | Toolbar state (active formatting)
type ToolbarState =
  { bold :: Boolean
  , italic :: Boolean
  , underline :: Boolean
  , strikethrough :: Boolean
  , code :: Boolean
  , heading :: Maybe HeadingLevel
  , alignment :: TextAlign
  , bulletList :: Boolean
  , orderedList :: Boolean
  , taskList :: Boolean
  , link :: Maybe String
  , canUndo :: Boolean
  , canRedo :: Boolean
  }

-- | Editor commands
data EditorCommand
  = CmdBold
  | CmdItalic
  | CmdUnderline
  | CmdStrikethrough
  | CmdCode
  | CmdHeading HeadingLevel
  | CmdParagraph
  | CmdBulletList
  | CmdOrderedList
  | CmdTaskList
  | CmdAlign TextAlign
  | CmdLink String
  | CmdImage String String -- src, alt
  | CmdTable Int Int -- rows, cols
  | CmdCodeBlock (Maybe String) -- language
  | CmdBlockquote
  | CmdHorizontalRule
  | CmdUndo
  | CmdRedo
  | CmdFocus
  | CmdBlur

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Opaque editor element reference
foreign import data EditorElement :: Type

-- | Initialize the editor on a DOM element
foreign import initEditorImpl :: EffectFn3 Element Foreign (Foreign -> Effect Unit) EditorElement

-- | Destroy the editor and cleanup
foreign import destroyEditorImpl :: EffectFn1 EditorElement Unit

-- | Get HTML content
foreign import getHtmlImpl :: EffectFn1 EditorElement String

-- | Set HTML content
foreign import setHtmlImpl :: EffectFn2 EditorElement String Unit

-- | Get JSON content
foreign import getJsonImpl :: EffectFn1 EditorElement Foreign

-- | Set JSON content
foreign import setJsonImpl :: EffectFn2 EditorElement Foreign Unit

-- | Get current selection
foreign import getSelectionImpl :: EffectFn1 EditorElement Foreign

-- | Execute a command
foreign import executeCommandImpl :: EffectFn2 EditorElement Foreign Unit

-- | Get character count
foreign import getCharacterCountImpl :: EffectFn1 EditorElement Int

-- | Get word count
foreign import getWordCountImpl :: EffectFn1 EditorElement Int

-- | Register keyboard shortcuts
foreign import registerShortcutsImpl :: EffectFn2 EditorElement (Foreign -> Effect Unit) (Effect Unit)

-- | Unregister keyboard shortcuts
foreign import unregisterShortcutsImpl :: EffectFn1 (Effect Unit) Unit

-- | Focus the editor
foreign import focusEditorImpl :: EffectFn1 EditorElement Unit

-- | Blur the editor
foreign import blurEditorImpl :: EffectFn1 EditorElement Unit

-- | Get toolbar state
foreign import getToolbarStateImpl :: EffectFn1 EditorElement Foreign

-- | Show bubble menu at selection
foreign import showBubbleMenuImpl :: EffectFn2 EditorElement Element Unit

-- | Hide bubble menu
foreign import hideBubbleMenuImpl :: EffectFn1 EditorElement Unit

-- | Show slash command menu
foreign import showSlashMenuImpl :: EffectFn2 EditorElement Element Unit

-- | Hide slash command menu
foreign import hideSlashMenuImpl :: EffectFn1 EditorElement Unit

-- | Show mention menu
foreign import showMentionMenuImpl :: EffectFn2 EditorElement Element Unit

-- | Hide mention menu
foreign import hideMentionMenuImpl :: EffectFn1 EditorElement Unit

-- Wrapped FFI functions

-- | Initialize editor
initEditor :: Element -> Foreign -> (Foreign -> Effect Unit) -> Effect EditorElement
initEditor el opts cb = runEffectFn3 initEditorImpl el opts cb

-- | Destroy editor
destroyEditor :: EditorElement -> Effect Unit
destroyEditor = runEffectFn1 destroyEditorImpl

-- | Get HTML content from editor
getHtml :: EditorElement -> Effect String
getHtml = runEffectFn1 getHtmlImpl

-- | Set HTML content in editor
setHtml :: EditorElement -> String -> Effect Unit
setHtml = runEffectFn2 setHtmlImpl

-- | Get JSON content from editor
getJson :: EditorElement -> Effect Foreign
getJson = runEffectFn1 getJsonImpl

-- | Set JSON content in editor
setJson :: EditorElement -> Foreign -> Effect Unit
setJson = runEffectFn2 setJsonImpl

-- | Get current selection state
getSelection :: EditorElement -> Effect Foreign
getSelection = runEffectFn1 getSelectionImpl

-- | Execute editor command
executeCommand :: EditorElement -> Foreign -> Effect Unit
executeCommand = runEffectFn2 executeCommandImpl

-- | Get character count
getCharacterCount :: EditorElement -> Effect Int
getCharacterCount = runEffectFn1 getCharacterCountImpl

-- | Get word count
getWordCount :: EditorElement -> Effect Int
getWordCount = runEffectFn1 getWordCountImpl

-- | Register keyboard shortcuts with callback
registerShortcuts :: EditorElement -> (Foreign -> Effect Unit) -> Effect (Effect Unit)
registerShortcuts = runEffectFn2 registerShortcutsImpl

-- | Unregister keyboard shortcuts
unregisterShortcuts :: Effect Unit -> Effect Unit
unregisterShortcuts = runEffectFn1 unregisterShortcutsImpl

-- | Focus the editor
focus :: EditorElement -> Effect Unit
focus = runEffectFn1 focusEditorImpl

-- | Blur the editor
blur :: EditorElement -> Effect Unit
blur = runEffectFn1 blurEditorImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Editor properties
type EditorProps i =
  { value :: String
  , onChange :: Maybe (String -> i)
  , onHtmlChange :: Maybe (String -> i)
  , onJsonChange :: Maybe (Foreign -> i)
  , onSelectionChange :: Maybe (Selection -> i)
  , onFocus :: Maybe (Event -> i)
  , onBlur :: Maybe (Event -> i)
  , placeholder :: String
  , readOnly :: Boolean
  , disabled :: Boolean
  , autofocus :: Boolean
  , characterLimit :: Maybe Int
  , showCharacterCount :: Boolean
  , showWordCount :: Boolean
  , className :: String
  , editorClassName :: String
  , toolbarClassName :: String
  , mentions :: Array Mention
  , onMentionSearch :: Maybe (String -> i)
  , onMentionSelect :: Maybe (Mention -> i)
  , slashCommands :: Array SlashCommand
  , enableBubbleMenu :: Boolean
  , enableSlashCommands :: Boolean
  , enableMentions :: Boolean
  , enableTables :: Boolean
  , enableImages :: Boolean
  , enableCodeBlocks :: Boolean
  , ariaLabel :: String
  , ariaDescribedBy :: Maybe String
  }

type EditorProp i = EditorProps i -> EditorProps i

defaultProps :: forall i. EditorProps i
defaultProps =
  { value: ""
  , onChange: Nothing
  , onHtmlChange: Nothing
  , onJsonChange: Nothing
  , onSelectionChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , placeholder: "Start writing..."
  , readOnly: false
  , disabled: false
  , autofocus: false
  , characterLimit: Nothing
  , showCharacterCount: false
  , showWordCount: false
  , className: ""
  , editorClassName: ""
  , toolbarClassName: ""
  , mentions: []
  , onMentionSearch: Nothing
  , onMentionSelect: Nothing
  , slashCommands: defaultSlashCommands
  , enableBubbleMenu: true
  , enableSlashCommands: true
  , enableMentions: true
  , enableTables: true
  , enableImages: true
  , enableCodeBlocks: true
  , ariaLabel: "Rich text editor"
  , ariaDescribedBy: Nothing
  }

-- | Default slash commands
defaultSlashCommands :: Array SlashCommand
defaultSlashCommands =
  [ { id: "heading1", label: "Heading 1", description: "Large heading", icon: Just "h1", keywords: ["h1", "title", "heading"] }
  , { id: "heading2", label: "Heading 2", description: "Medium heading", icon: Just "h2", keywords: ["h2", "subtitle"] }
  , { id: "heading3", label: "Heading 3", description: "Small heading", icon: Just "h3", keywords: ["h3"] }
  , { id: "bullet", label: "Bullet List", description: "Unordered list", icon: Just "list", keywords: ["ul", "bullet", "list"] }
  , { id: "numbered", label: "Numbered List", description: "Ordered list", icon: Just "list-ordered", keywords: ["ol", "number", "list"] }
  , { id: "task", label: "Task List", description: "Checklist with checkboxes", icon: Just "check-square", keywords: ["todo", "task", "check"] }
  , { id: "quote", label: "Quote", description: "Block quotation", icon: Just "quote", keywords: ["blockquote", "quote"] }
  , { id: "code", label: "Code Block", description: "Code with syntax highlighting", icon: Just "code", keywords: ["code", "pre", "syntax"] }
  , { id: "hr", label: "Horizontal Rule", description: "Divider line", icon: Just "minus", keywords: ["hr", "divider", "line"] }
  , { id: "image", label: "Image", description: "Insert an image", icon: Just "image", keywords: ["img", "picture", "photo"] }
  , { id: "table", label: "Table", description: "Insert a table", icon: Just "table", keywords: ["table", "grid"] }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set editor content value (HTML string)
value :: forall i. String -> EditorProp i
value v props = props { value = v }

-- | Handle content changes (HTML)
onChange :: forall i. (String -> i) -> EditorProp i
onChange handler props = props { onChange = Just handler }

-- | Handle HTML content changes
onHtmlChange :: forall i. (String -> i) -> EditorProp i
onHtmlChange handler props = props { onHtmlChange = Just handler }

-- | Handle JSON content changes
onJsonChange :: forall i. (Foreign -> i) -> EditorProp i
onJsonChange handler props = props { onJsonChange = Just handler }

-- | Handle selection changes
onSelectionChange :: forall i. (Selection -> i) -> EditorProp i
onSelectionChange handler props = props { onSelectionChange = Just handler }

-- | Handle focus event
onFocus :: forall i. (Event -> i) -> EditorProp i
onFocus handler props = props { onFocus = Just handler }

-- | Handle blur event
onBlur :: forall i. (Event -> i) -> EditorProp i
onBlur handler props = props { onBlur = Just handler }

-- | Set placeholder text
placeholder :: forall i. String -> EditorProp i
placeholder p props = props { placeholder = p }

-- | Set read-only mode
readOnly :: forall i. Boolean -> EditorProp i
readOnly r props = props { readOnly = r }

-- | Set disabled state
disabled :: forall i. Boolean -> EditorProp i
disabled d props = props { disabled = d }

-- | Enable autofocus
autofocus :: forall i. Boolean -> EditorProp i
autofocus a props = props { autofocus = a }

-- | Set character limit
characterLimit :: forall i. Int -> EditorProp i
characterLimit limit props = props { characterLimit = Just limit }

-- | Show character count
showCharacterCount :: forall i. Boolean -> EditorProp i
showCharacterCount s props = props { showCharacterCount = s }

-- | Show word count
showWordCount :: forall i. Boolean -> EditorProp i
showWordCount s props = props { showWordCount = s }

-- | Add custom container class
className :: forall i. String -> EditorProp i
className c props = props { className = props.className <> " " <> c }

-- | Add custom editor class
editorClassName :: forall i. String -> EditorProp i
editorClassName c props = props { editorClassName = props.editorClassName <> " " <> c }

-- | Add custom toolbar class
toolbarClassName :: forall i. String -> EditorProp i
toolbarClassName c props = props { toolbarClassName = props.toolbarClassName <> " " <> c }

-- | Set mention suggestions
mentions :: forall i. Array Mention -> EditorProp i
mentions m props = props { mentions = m }

-- | Handle mention search
onMentionSearch :: forall i. (String -> i) -> EditorProp i
onMentionSearch handler props = props { onMentionSearch = Just handler }

-- | Handle mention selection
onMentionSelect :: forall i. (Mention -> i) -> EditorProp i
onMentionSelect handler props = props { onMentionSelect = Just handler }

-- | Set custom slash commands
slashCommands :: forall i. Array SlashCommand -> EditorProp i
slashCommands cmds props = props { slashCommands = cmds }

-- | Enable/disable bubble menu
enableBubbleMenu :: forall i. Boolean -> EditorProp i
enableBubbleMenu e props = props { enableBubbleMenu = e }

-- | Enable/disable slash commands
enableSlashCommands :: forall i. Boolean -> EditorProp i
enableSlashCommands e props = props { enableSlashCommands = e }

-- | Enable/disable mentions
enableMentions :: forall i. Boolean -> EditorProp i
enableMentions e props = props { enableMentions = e }

-- | Enable/disable tables
enableTables :: forall i. Boolean -> EditorProp i
enableTables e props = props { enableTables = e }

-- | Enable/disable images
enableImages :: forall i. Boolean -> EditorProp i
enableImages e props = props { enableImages = e }

-- | Enable/disable code blocks
enableCodeBlocks :: forall i. Boolean -> EditorProp i
enableCodeBlocks e props = props { enableCodeBlocks = e }

-- | Set ARIA label
ariaLabel :: forall i. String -> EditorProp i
ariaLabel l props = props { ariaLabel = l }

-- | Set ARIA described-by
ariaDescribedBy :: forall i. String -> EditorProp i
ariaDescribedBy id props = props { ariaDescribedBy = Just id }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // commands
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toggle bold formatting
formatBold :: EditorCommand
formatBold = CmdBold

-- | Toggle italic formatting
formatItalic :: EditorCommand
formatItalic = CmdItalic

-- | Toggle underline formatting
formatUnderline :: EditorCommand
formatUnderline = CmdUnderline

-- | Toggle strikethrough formatting
formatStrikethrough :: EditorCommand
formatStrikethrough = CmdStrikethrough

-- | Toggle inline code formatting
formatCode :: EditorCommand
formatCode = CmdCode

-- | Set heading level
setHeading :: HeadingLevel -> EditorCommand
setHeading = CmdHeading

-- | Set paragraph (remove heading)
setParagraph :: EditorCommand
setParagraph = CmdParagraph

-- | Toggle bullet list
toggleBulletList :: EditorCommand
toggleBulletList = CmdBulletList

-- | Toggle numbered list
toggleNumberedList :: EditorCommand
toggleNumberedList = CmdOrderedList

-- | Toggle task list
toggleTaskList :: EditorCommand
toggleTaskList = CmdTaskList

-- | Set text alignment
setAlignment :: TextAlign -> EditorCommand
setAlignment = CmdAlign

-- | Insert or edit link
insertLink :: String -> EditorCommand
insertLink = CmdLink

-- | Insert image
insertImage :: String -> String -> EditorCommand
insertImage = CmdImage

-- | Insert table with specified dimensions
insertTable :: Int -> Int -> EditorCommand
insertTable = CmdTable

-- | Insert code block with optional language
insertCodeBlock :: Maybe String -> EditorCommand
insertCodeBlock = CmdCodeBlock

-- | Insert blockquote
insertBlockquote :: EditorCommand
insertBlockquote = CmdBlockquote

-- | Insert horizontal rule
insertHorizontalRule :: EditorCommand
insertHorizontalRule = CmdHorizontalRule

-- | Undo last action
undo :: EditorCommand
undo = CmdUndo

-- | Redo last undone action
redo :: EditorCommand
redo = CmdRedo

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base editor container classes
editorContainerClasses :: String
editorContainerClasses =
  "relative w-full rounded-lg border border-input bg-background ring-offset-background focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2"

-- | Base editor content classes
editorContentClasses :: String
editorContentClasses =
  "prose prose-sm dark:prose-invert max-w-none min-h-[150px] px-4 py-3 focus:outline-none"

-- | Base toolbar classes
toolbarBaseClasses :: String
toolbarBaseClasses =
  "flex flex-wrap items-center gap-1 p-2 border-b border-input bg-muted/50"

-- | Basic editor without toolbar
-- |
-- | A minimal contenteditable editor with all features but no visible toolbar.
-- | Formatting is available via keyboard shortcuts and right-click context menu.
editor :: forall w i. Array (EditorProp i) -> HH.HTML w i
editor propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled then "opacity-50 cursor-not-allowed" else ""
    readOnlyClasses = if props.readOnly then "bg-muted" else ""
  in
    HH.div
      [ cls [ editorContainerClasses, disabledClasses, props.className ]
      , HP.attr (HH.AttrName "data-richtext-editor") ""
      ]
      [ -- Contenteditable area
        HH.div
          ( [ cls [ editorContentClasses, readOnlyClasses, props.editorClassName ]
            , HP.attr (HH.AttrName "contenteditable") (if props.readOnly || props.disabled then "false" else "true")
            , HP.attr (HH.AttrName "data-placeholder") props.placeholder
            , HP.attr (HH.AttrName "spellcheck") "true"
            , HP.tabIndex (if props.disabled then (-1) else 0)
            , ARIA.role "textbox"
            , ARIA.multiLine "true"
            , ARIA.label props.ariaLabel
            , ARIA.readOnly (show props.readOnly)
            , ARIA.disabled (show props.disabled)
            ] <> maybeAttr ARIA.describedBy props.ariaDescribedBy
          )
          [ -- Content will be managed by JS
          ]
      , -- Character/word count footer
        if props.showCharacterCount || props.showWordCount
          then editorFooter props
          else HH.text ""
      ]

-- | Editor with toolbar
-- |
-- | Full-featured editor with formatting toolbar at the top.
editorWithToolbar :: forall w i. Array (EditorProp i) -> HH.HTML w i
editorWithToolbar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled then "opacity-50 cursor-not-allowed" else ""
    readOnlyClasses = if props.readOnly then "bg-muted" else ""
  in
    HH.div
      [ cls [ editorContainerClasses, disabledClasses, props.className ]
      , HP.attr (HH.AttrName "data-richtext-editor") ""
      ]
      [ -- Toolbar
        toolbar propMods
      , -- Contenteditable area
        HH.div
          ( [ cls [ editorContentClasses, readOnlyClasses, props.editorClassName ]
            , HP.attr (HH.AttrName "contenteditable") (if props.readOnly || props.disabled then "false" else "true")
            , HP.attr (HH.AttrName "data-placeholder") props.placeholder
            , HP.attr (HH.AttrName "spellcheck") "true"
            , HP.tabIndex (if props.disabled then (-1) else 0)
            , ARIA.role "textbox"
            , ARIA.multiLine "true"
            , ARIA.label props.ariaLabel
            , ARIA.readOnly (show props.readOnly)
            , ARIA.disabled (show props.disabled)
            ] <> maybeAttr ARIA.describedBy props.ariaDescribedBy
          )
          []
      , -- Character/word count footer
        if props.showCharacterCount || props.showWordCount
          then editorFooter props
          else HH.text ""
      ]

-- | Toolbar component
-- |
-- | Standalone toolbar that can be positioned anywhere.
toolbar :: forall w i. Array (EditorProp i) -> HH.HTML w i
toolbar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ toolbarBaseClasses, props.toolbarClassName ]
      , ARIA.role "toolbar"
      , ARIA.label "Formatting options"
      ]
      [ -- Undo/Redo
        toolbarGroup
          [ toolbarButton "Undo (Ctrl+Z)" "undo" undoIcon
          , toolbarButton "Redo (Ctrl+Shift+Z)" "redo" redoIcon
          ]
      , toolbarSeparator
      , -- Text formatting
        toolbarGroup
          [ toolbarButton "Bold (Ctrl+B)" "bold" boldIcon
          , toolbarButton "Italic (Ctrl+I)" "italic" italicIcon
          , toolbarButton "Underline (Ctrl+U)" "underline" underlineIcon
          , toolbarButton "Strikethrough" "strikethrough" strikethroughIcon
          , toolbarButton "Code (Ctrl+E)" "code" codeIcon
          ]
      , toolbarSeparator
      , -- Headings
        toolbarGroup
          [ toolbarButton "Heading 1" "heading1" h1Icon
          , toolbarButton "Heading 2" "heading2" h2Icon
          , toolbarButton "Heading 3" "heading3" h3Icon
          , toolbarButton "Paragraph" "paragraph" paragraphIcon
          ]
      , toolbarSeparator
      , -- Lists
        toolbarGroup
          [ toolbarButton "Bullet List" "bulletList" bulletListIcon
          , toolbarButton "Numbered List" "orderedList" orderedListIcon
          , toolbarButton "Task List" "taskList" taskListIcon
          ]
      , toolbarSeparator
      , -- Alignment
        toolbarGroup
          [ toolbarButton "Align Left" "alignLeft" alignLeftIcon
          , toolbarButton "Align Center" "alignCenter" alignCenterIcon
          , toolbarButton "Align Right" "alignRight" alignRightIcon
          , toolbarButton "Justify" "alignJustify" alignJustifyIcon
          ]
      , toolbarSeparator
      , -- Insert
        toolbarGroup
          ( [ toolbarButton "Link (Ctrl+K)" "link" linkIcon ]
            <> (if props.enableImages
                  then [ toolbarButton "Image" "image" imageIcon ]
                  else [])
            <> (if props.enableTables
                  then [ toolbarButton "Table" "table" tableIcon ]
                  else [])
            <> (if props.enableCodeBlocks
                  then [ toolbarButton "Code Block" "codeBlock" codeBlockIcon ]
                  else [])
            <> [ toolbarButton "Quote" "blockquote" quoteIcon
               , toolbarButton "Horizontal Rule" "horizontalRule" hrIcon
               ]
          )
      ]

-- | Toolbar button group
toolbarGroup :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
toolbarGroup children =
  HH.div
    [ cls [ "flex items-center gap-0.5" ] ]
    children

-- | Toolbar button
-- |
-- | Creates a toolbar button with given title, data-command attribute, and icon.
toolbarButton :: forall w i. String -> String -> HH.HTML w i -> HH.HTML w i
toolbarButton title' command icon =
  HH.button
    [ cls [ "inline-flex items-center justify-center h-8 w-8 rounded-md text-sm font-medium ring-offset-background transition-colors hover:bg-accent hover:text-accent-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 data-[active=true]:bg-accent data-[active=true]:text-accent-foreground" ]
    , HP.type_ HP.ButtonButton
    , HP.tabIndex (-1)
    , HP.title title'
    , HP.attr (HH.AttrName "data-command") command
    ]
    [ icon ]

-- | Toolbar separator
toolbarSeparator :: forall w i. HH.HTML w i
toolbarSeparator =
  HH.div
    [ cls [ "w-px h-6 mx-1 bg-border" ] ]
    []

-- | Toolbar select dropdown
toolbarSelect :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
toolbarSelect children =
  HH.select
    [ cls [ "h-8 rounded-md border border-input bg-background px-2 text-sm ring-offset-background focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2" ]
    , HP.tabIndex (-1)
    ]
    children

-- | Bubble menu (floating toolbar on selection)
-- |
-- | Appears above selected text with quick formatting options.
bubbleMenu :: forall w i. Array (EditorProp i) -> HH.HTML w i
bubbleMenu propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "absolute hidden z-50 flex items-center gap-1 p-1 bg-popover border rounded-lg shadow-lg", props.className ]
      , HP.attr (HH.AttrName "data-bubble-menu") ""
      , ARIA.role "toolbar"
      , ARIA.label "Text formatting"
      ]
      [ toolbarButton "Bold" "bold" boldIcon
      , toolbarButton "Italic" "italic" italicIcon
      , toolbarButton "Underline" "underline" underlineIcon
      , toolbarButton "Strikethrough" "strikethrough" strikethroughIcon
      , toolbarButton "Code" "code" codeIcon
      , toolbarSeparator
      , toolbarButton "Link" "link" linkIcon
      ]

-- | Slash command menu
-- |
-- | Dropdown menu for slash commands (/).
slashCommandMenu :: forall w i. Array SlashCommand -> HH.HTML w i
slashCommandMenu commands =
  HH.div
    [ cls [ "absolute hidden z-50 w-64 max-h-80 overflow-y-auto bg-popover border rounded-lg shadow-lg" ]
    , HP.attr (HH.AttrName "data-slash-menu") ""
    , ARIA.role "listbox"
    , ARIA.label "Commands"
    ]
    (map renderSlashCommand commands)
  where
    renderSlashCommand :: SlashCommand -> HH.HTML w i
    renderSlashCommand cmd =
      HH.div
        [ cls [ "flex items-center gap-3 px-3 py-2 cursor-pointer hover:bg-accent hover:text-accent-foreground transition-colors" ]
        , HP.attr (HH.AttrName "data-command-id") cmd.id
        , ARIA.role "option"
        ]
        [ HH.div [ cls [ "flex-shrink-0 w-8 h-8 flex items-center justify-center rounded bg-muted" ] ]
            [ HH.text (fromMaybe "/" cmd.icon) ]
        , HH.div [ cls [ "flex-1 min-w-0" ] ]
            [ HH.div [ cls [ "text-sm font-medium truncate" ] ] [ HH.text cmd.label ]
            , HH.div [ cls [ "text-xs text-muted-foreground truncate" ] ] [ HH.text cmd.description ]
            ]
        ]

-- | Mention menu
-- |
-- | Dropdown menu for @-mentions.
mentionMenu :: forall w i. Array Mention -> HH.HTML w i
mentionMenu mentionList =
  HH.div
    [ cls [ "absolute hidden z-50 w-64 max-h-60 overflow-y-auto bg-popover border rounded-lg shadow-lg" ]
    , HP.attr (HH.AttrName "data-mention-menu") ""
    , ARIA.role "listbox"
    , ARIA.label "Mentions"
    ]
    (map renderMention mentionList)
  where
    renderMention :: Mention -> HH.HTML w i
    renderMention m =
      HH.div
        [ cls [ "flex items-center gap-3 px-3 py-2 cursor-pointer hover:bg-accent hover:text-accent-foreground transition-colors" ]
        , HP.attr (HH.AttrName "data-mention-id") m.id
        , ARIA.role "option"
        ]
        [ case m.avatar of
            Just url -> HH.img [ cls [ "w-8 h-8 rounded-full" ], HP.src url, HP.alt m.label ]
            Nothing -> HH.div [ cls [ "w-8 h-8 rounded-full bg-muted flex items-center justify-center text-sm font-medium" ] ]
                         [ HH.text (String.take 1 m.label) ]
        , HH.span [ cls [ "text-sm font-medium" ] ] [ HH.text m.label ]
        ]

-- | Editor footer with counts
editorFooter :: forall w i. EditorProps i -> HH.HTML w i
editorFooter props =
  HH.div
    [ cls [ "flex items-center justify-end gap-4 px-3 py-2 border-t border-input text-xs text-muted-foreground" ] ]
    [ if props.showWordCount
        then HH.span [ HP.attr (HH.AttrName "data-word-count") "" ] [ HH.text "0 words" ]
        else HH.text ""
    , if props.showCharacterCount
        then HH.span [ HP.attr (HH.AttrName "data-character-count") "" ]
          [ HH.text $ case props.characterLimit of
              Just limit -> "0 / " <> show limit
              Nothing -> "0 characters"
          ]
        else HH.text ""
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SVG icon helper
svgIcon :: forall w i. String -> HH.HTML w i
svgIcon path =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") path ]
        []
    ]

-- Bold icon
boldIcon :: forall w i. HH.HTML w i
boldIcon = svgIcon "M6 4h8a4 4 0 0 1 4 4 4 4 0 0 1-4 4H6zM6 12h9a4 4 0 0 1 4 4 4 4 0 0 1-4 4H6z"

-- Italic icon
italicIcon :: forall w i. HH.HTML w i
italicIcon = svgIcon "M19 4h-9M14 20H5M15 4 9 20"

-- Underline icon
underlineIcon :: forall w i. HH.HTML w i
underlineIcon = svgIcon "M6 4v6a6 6 0 0 0 12 0V4M4 20h16"

-- Strikethrough icon
strikethroughIcon :: forall w i. HH.HTML w i
strikethroughIcon = svgIcon "M16 4H9a3 3 0 0 0-2.83 4M14 12H4M8 20h7a3 3 0 0 0 2.83-4"

-- Code icon
codeIcon :: forall w i. HH.HTML w i
codeIcon = svgIcon "m16 18 6-6-6-6M8 6l-6 6 6 6"

-- H1 icon
h1Icon :: forall w i. HH.HTML w i
h1Icon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M4 12h8M4 6v12M12 6v12M17 12l3-2v10" ] []
    ]

-- H2 icon
h2Icon :: forall w i. HH.HTML w i
h2Icon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M4 12h8M4 6v12M12 6v12M21 18h-4c0-4 4-3 4-6 0-1.5-2-2.5-4-1" ] []
    ]

-- H3 icon
h3Icon :: forall w i. HH.HTML w i
h3Icon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M4 12h8M4 6v12M12 6v12M17.5 10.5c1.7-1 3.5 0 3.5 1.5a2 2 0 0 1-2 2M17 17.5c2 1.5 4 .3 4-1.5a2 2 0 0 0-2-2" ] []
    ]

-- Paragraph icon
paragraphIcon :: forall w i. HH.HTML w i
paragraphIcon = svgIcon "M13 4v16M19 4H9.5a4.5 4.5 0 1 0 0 9H13"

-- Bullet list icon
bulletListIcon :: forall w i. HH.HTML w i
bulletListIcon = svgIcon "M8 6h13M8 12h13M8 18h13M3 6h.01M3 12h.01M3 18h.01"

-- Ordered list icon
orderedListIcon :: forall w i. HH.HTML w i
orderedListIcon = svgIcon "M10 6h11M10 12h11M10 18h11M4 6h1v4M4 10h2M6 18H4c0-1 2-2 2-3s-1-1.5-2-1"

-- Task list icon
taskListIcon :: forall w i. HH.HTML w i
taskListIcon = svgIcon "M12 6h8M12 12h8M12 18h8M3 6h4v4H3zM4 13l1.5 1.5L9 11"

-- Align left icon
alignLeftIcon :: forall w i. HH.HTML w i
alignLeftIcon = svgIcon "M21 6H3M15 12H3M18 18H3"

-- Align center icon
alignCenterIcon :: forall w i. HH.HTML w i
alignCenterIcon = svgIcon "M21 6H3M17 12H7M19 18H5"

-- Align right icon
alignRightIcon :: forall w i. HH.HTML w i
alignRightIcon = svgIcon "M21 6H3M21 12H9M21 18H6"

-- Align justify icon
alignJustifyIcon :: forall w i. HH.HTML w i
alignJustifyIcon = svgIcon "M3 6h18M3 12h18M3 18h18"

-- Link icon
linkIcon :: forall w i. HH.HTML w i
linkIcon = svgIcon "M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"

-- Image icon
imageIcon :: forall w i. HH.HTML w i
imageIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "rect")
        [ HP.attr (HH.AttrName "width") "18"
        , HP.attr (HH.AttrName "height") "18"
        , HP.attr (HH.AttrName "x") "3"
        , HP.attr (HH.AttrName "y") "3"
        , HP.attr (HH.AttrName "rx") "2"
        , HP.attr (HH.AttrName "ry") "2"
        ] []
    , HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "9"
        , HP.attr (HH.AttrName "cy") "9"
        , HP.attr (HH.AttrName "r") "2"
        ] []
    , HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "m21 15-3.086-3.086a2 2 0 0 0-2.828 0L6 21" ] []
    ]

-- Table icon
tableIcon :: forall w i. HH.HTML w i
tableIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M12 3v18M3 9h18M3 15h18" ] []
    , HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "rect")
        [ HP.attr (HH.AttrName "width") "18"
        , HP.attr (HH.AttrName "height") "18"
        , HP.attr (HH.AttrName "x") "3"
        , HP.attr (HH.AttrName "y") "3"
        , HP.attr (HH.AttrName "rx") "2"
        ] []
    ]

-- Code block icon
codeBlockIcon :: forall w i. HH.HTML w i
codeBlockIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "m10 9-3 3 3 3M14 9l3 3-3 3" ] []
    , HH.elementNS (HH.Namespace "http://www.w3.org/2000/svg") (HH.ElemName "rect")
        [ HP.attr (HH.AttrName "width") "20"
        , HP.attr (HH.AttrName "height") "16"
        , HP.attr (HH.AttrName "x") "2"
        , HP.attr (HH.AttrName "y") "4"
        , HP.attr (HH.AttrName "rx") "2"
        ] []
    ]

-- Quote icon
quoteIcon :: forall w i. HH.HTML w i
quoteIcon = svgIcon "M3 21c3 0 7-1 7-8V5c0-1.25-.756-2.017-2-2H4c-1.25 0-2 .75-2 1.972V11c0 1.25.75 2 2 2 1 0 1 0 1 1v1c0 1-1 2-2 2s-1 .008-1 1.031V21M15 21c3 0 7-1 7-8V5c0-1.25-.757-2.017-2-2h-4c-1.25 0-2 .75-2 1.972V11c0 1.25.75 2 2 2h.75c0 2.25.25 4-2.75 4v3c0 1 0 1 1 1"

-- Horizontal rule icon
hrIcon :: forall w i. HH.HTML w i
hrIcon = svgIcon "M5 12h14"

-- Undo icon
undoIcon :: forall w i. HH.HTML w i
undoIcon = svgIcon "M3 7v6h6M3 13a9 9 0 1 0 2.083-5.753"

-- Redo icon
redoIcon :: forall w i. HH.HTML w i
redoIcon = svgIcon "M21 7v6h-6M21 13a9 9 0 1 1-2.083-5.753"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Helper for optional attributes
maybeAttr :: forall r i a. (a -> HH.IProp r i) -> Maybe a -> Array (HH.IProp r i)
maybeAttr _ Nothing = []
maybeAttr f (Just a) = [f a]

