-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // text // command
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Command — Edit commands for rich text and code editors.
-- |
-- | ## Design Philosophy
-- |
-- | Edit commands are pure data describing operations on text. They are NOT
-- | imperative procedures. This enables:
-- | - Undo/redo via command history
-- | - Collaborative editing (OT/CRDT) via command transformation
-- | - Testing via command application
-- | - Serialization for persistence and sync
-- |
-- | ## Command Categories
-- |
-- | 1. **Insertion**: Adding text, blocks, or formatting
-- | 2. **Deletion**: Removing text, blocks, or formatting
-- | 3. **Formatting**: Toggling or applying styles
-- | 4. **Navigation**: Moving cursor/selection (for history tracking)
-- | 5. **Structure**: Block-level operations (split, merge)
-- | 6. **History**: Undo/redo operations
-- |
-- | ## Composability
-- |
-- | Commands can be composed into compound commands for atomic operations.
-- | A "replace selection with text" is: Delete + Insert as one atomic unit.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show, Generic)
-- | - Schema.Text.RichText (Block, Inline, HeadingLevel, ListType, Language)
-- | - Schema.Text.Selection (Selection, Position)

module Hydrogen.Schema.Text.Command
  ( -- * Edit Commands
    EditCommand(..)
  
  -- * Text Commands
  , InsertDirection(..)
  , DeleteDirection(..)
  , DeleteScope(..)
  
  -- * Formatting Commands
  , FormatCommand(..)
  , formatBold
  , formatItalic
  , formatCode
  , formatStrikethrough
  , formatUnderline
  , formatLink
  , formatClear
  
  -- * Block Commands
  , BlockCommand(..)
  
  -- * Navigation Commands
  , NavigationCommand(..)
  , MoveUnit(..)
  , SelectionMode(..)
  
  -- * History Commands
  , HistoryCommand(..)
  
  -- * Clipboard Commands
  , ClipboardCommand(..)
  
  -- * Compound Commands
  , CompoundCommand(..)
  , atomic
  , sequence
  
  -- * Command Metadata
  , CommandMeta
  , commandMeta
  , defaultMeta
  
  -- * Command Predicates
  , isInsertCommand
  , isDeleteCommand
  , isFormatCommand
  , isBlockCommand
  , isNavigationCommand
  , isHistoryCommand
  , modifiesDocument
  , modifiesSelection
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (||)
  , ($)
  , (<>)
  )

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)

import Hydrogen.Schema.Text.RichText (Block, HeadingLevel, ListType, URL)
import Hydrogen.Schema.Text.Selection (Position, Selection)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // insert // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction for text insertion relative to cursor.
data InsertDirection
  = InsertBefore    -- ^ Insert before cursor (normal typing)
  | InsertAfter     -- ^ Insert after cursor (paste behavior in some modes)

derive instance eqInsertDirection :: Eq InsertDirection
derive instance genericInsertDirection :: Generic InsertDirection _

instance showInsertDirection :: Show InsertDirection where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // delete // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction for text deletion.
data DeleteDirection
  = DeleteBackward    -- ^ Backspace: delete before cursor
  | DeleteForward     -- ^ Delete: delete after cursor

derive instance eqDeleteDirection :: Eq DeleteDirection
derive instance genericDeleteDirection :: Generic DeleteDirection _

instance showDeleteDirection :: Show DeleteDirection where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // delete // scope
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scope of deletion operation.
data DeleteScope
  = DeleteChar        -- ^ Single character
  | DeleteWord        -- ^ Whole word
  | DeleteLine        -- ^ Entire line
  | DeleteBlock       -- ^ Entire block (paragraph, etc.)
  | DeleteSelection   -- ^ Whatever is selected

derive instance eqDeleteScope :: Eq DeleteScope
derive instance genericDeleteScope :: Generic DeleteScope _

instance showDeleteScope :: Show DeleteScope where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // format // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Formatting commands for inline styles.
-- |
-- | These are toggle operations: applying bold to bold text removes it.
data FormatCommand
  = ToggleBold
  | ToggleItalic
  | ToggleCode
  | ToggleStrikethrough
  | ToggleUnderline
  | ToggleSubscript
  | ToggleSuperscript
  | SetLink URL           -- ^ Set link URL (removes link if empty URL)
  | RemoveLink            -- ^ Remove link from selection
  | ClearFormatting       -- ^ Remove all inline formatting

derive instance eqFormatCommand :: Eq FormatCommand
derive instance genericFormatCommand :: Generic FormatCommand _

instance showFormatCommand :: Show FormatCommand where
  show = genericShow

-- | Convenience: toggle bold.
formatBold :: FormatCommand
formatBold = ToggleBold

-- | Convenience: toggle italic.
formatItalic :: FormatCommand
formatItalic = ToggleItalic

-- | Convenience: toggle code.
formatCode :: FormatCommand
formatCode = ToggleCode

-- | Convenience: toggle strikethrough.
formatStrikethrough :: FormatCommand
formatStrikethrough = ToggleStrikethrough

-- | Convenience: toggle underline.
formatUnderline :: FormatCommand
formatUnderline = ToggleUnderline

-- | Convenience: set link.
formatLink :: URL -> FormatCommand
formatLink = SetLink

-- | Convenience: clear all formatting.
formatClear :: FormatCommand
formatClear = ClearFormatting

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // block // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block-level structural commands.
data BlockCommand
  = SplitBlock                      -- ^ Split current block at cursor (Enter)
  | MergeWithPrevious               -- ^ Merge with previous block (Backspace at start)
  | MergeWithNext                   -- ^ Merge with next block (Delete at end)
  | SetHeading HeadingLevel         -- ^ Convert block to heading
  | SetParagraph                    -- ^ Convert block to paragraph
  | SetCodeBlock                    -- ^ Convert block to code block
  | SetBlockQuote                   -- ^ Convert block to block quote
  | SetBulletList                   -- ^ Convert to bullet list item
  | SetNumberedList                 -- ^ Convert to numbered list item
  | SetCheckboxList                 -- ^ Convert to checkbox list item
  | ToggleCheckbox                  -- ^ Toggle checkbox state
  | IndentBlock                     -- ^ Increase block indentation (Tab in list)
  | OutdentBlock                    -- ^ Decrease block indentation (Shift+Tab)
  | InsertBlockBefore Block         -- ^ Insert a block before current
  | InsertBlockAfter Block          -- ^ Insert a block after current
  | DeleteCurrentBlock              -- ^ Delete the current block
  | InsertHorizontalRule            -- ^ Insert a horizontal rule

derive instance eqBlockCommand :: Eq BlockCommand
derive instance genericBlockCommand :: Generic BlockCommand _

instance showBlockCommand :: Show BlockCommand where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // move // unit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unit of movement for navigation.
data MoveUnit
  = MoveChar        -- ^ Single character
  | MoveWord        -- ^ Word boundary
  | MoveLine        -- ^ Line boundary
  | MoveBlock       -- ^ Block boundary
  | MoveDocument    -- ^ Document boundary (start/end)

derive instance eqMoveUnit :: Eq MoveUnit
derive instance genericMoveUnit :: Generic MoveUnit _

instance showMoveUnit :: Show MoveUnit where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode for navigation: move cursor or extend selection.
data SelectionMode
  = MoveCursor      -- ^ Move cursor, collapse selection
  | ExtendSelection -- ^ Extend selection from anchor

derive instance eqSelectionMode :: Eq SelectionMode
derive instance genericSelectionMode :: Generic SelectionMode _

instance showSelectionMode :: Show SelectionMode where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // navigation // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigation commands for cursor/selection movement.
data NavigationCommand
  = MoveLeft MoveUnit SelectionMode       -- ^ Move left by unit
  | MoveRight MoveUnit SelectionMode      -- ^ Move right by unit
  | MoveUp SelectionMode                  -- ^ Move up one line
  | MoveDown SelectionMode                -- ^ Move down one line
  | MoveToLineStart SelectionMode         -- ^ Move to start of line
  | MoveToLineEnd SelectionMode           -- ^ Move to end of line
  | MoveToBlockStart SelectionMode        -- ^ Move to start of block
  | MoveToBlockEnd SelectionMode          -- ^ Move to end of block
  | MoveToDocumentStart SelectionMode     -- ^ Move to start of document
  | MoveToDocumentEnd SelectionMode       -- ^ Move to end of document
  | SelectAll                             -- ^ Select entire document
  | SelectWord                            -- ^ Select current word
  | SelectLine                            -- ^ Select current line
  | SelectBlock                           -- ^ Select current block
  | SetSelection Selection                -- ^ Set selection directly
  | CollapseSelectionToStart              -- ^ Collapse to selection start
  | CollapseSelectionToEnd                -- ^ Collapse to selection end

derive instance eqNavigationCommand :: Eq NavigationCommand
derive instance genericNavigationCommand :: Generic NavigationCommand _

instance showNavigationCommand :: Show NavigationCommand where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // history // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | History commands for undo/redo.
data HistoryCommand
  = Undo            -- ^ Undo last command
  | Redo            -- ^ Redo last undone command
  | UndoAll         -- ^ Undo all commands (reset to initial state)
  | RedoAll         -- ^ Redo all undone commands
  | ClearHistory    -- ^ Clear undo/redo history

derive instance eqHistoryCommand :: Eq HistoryCommand
derive instance genericHistoryCommand :: Generic HistoryCommand _

instance showHistoryCommand :: Show HistoryCommand where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // clipboard // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clipboard operations.
data ClipboardCommand
  = Cut             -- ^ Cut selection to clipboard
  | Copy            -- ^ Copy selection to clipboard
  | Paste           -- ^ Paste from clipboard
  | PastePlain      -- ^ Paste as plain text (strip formatting)

derive instance eqClipboardCommand :: Eq ClipboardCommand
derive instance genericClipboardCommand :: Generic ClipboardCommand _

instance showClipboardCommand :: Show ClipboardCommand where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // edit // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Top-level edit command.
-- |
-- | All text editing operations are represented as one of these commands.
-- | Commands are pure data — they describe what to do, not how.
data EditCommand
  -- Text insertion
  = InsertText String                     -- ^ Insert text at cursor
  | InsertNewline                         -- ^ Insert newline (may split block)
  | InsertTab                             -- ^ Insert tab (may indent)
  
  -- Text deletion
  | Delete DeleteDirection DeleteScope    -- ^ Delete with direction and scope
  | DeleteRange Position Position         -- ^ Delete between two positions
  
  -- Formatting
  | Format FormatCommand                  -- ^ Apply formatting command
  
  -- Block operations
  | BlockOp BlockCommand                  -- ^ Apply block command
  
  -- Navigation
  | Navigate NavigationCommand            -- ^ Apply navigation command
  
  -- History
  | History HistoryCommand                -- ^ Apply history command
  
  -- Clipboard
  | Clipboard ClipboardCommand            -- ^ Apply clipboard command
  
  -- Composition
  | Compound CompoundCommand              -- ^ Compound/atomic command

derive instance eqEditCommand :: Eq EditCommand

instance showEditCommand :: Show EditCommand where
  show (InsertText s) = "InsertText " <> show s
  show InsertNewline = "InsertNewline"
  show InsertTab = "InsertTab"
  show (Delete dir scope) = "Delete " <> show dir <> " " <> show scope
  show (DeleteRange p1 p2) = "DeleteRange " <> show p1 <> " " <> show p2
  show (Format cmd) = "Format " <> show cmd
  show (BlockOp cmd) = "BlockOp " <> show cmd
  show (Navigate cmd) = "Navigate " <> show cmd
  show (History cmd) = "History " <> show cmd
  show (Clipboard cmd) = "Clipboard " <> show cmd
  show (Compound cmd) = "Compound " <> show cmd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // compound // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compound commands for atomic multi-step operations.
-- |
-- | ## Atomicity
-- |
-- | Atomic commands are undone/redone as a single unit.
-- | A "replace selection" is atomic: undo restores both the deleted
-- | text AND removes the inserted text.
data CompoundCommand
  = Atomic (Array EditCommand)            -- ^ Execute as single atomic operation
  | Sequence (Array EditCommand)          -- ^ Execute in order, each is separate undo step

derive instance eqCompoundCommand :: Eq CompoundCommand

instance showCompoundCommand :: Show CompoundCommand where
  show (Atomic cmds) = "Atomic [" <> show (Array.length cmds) <> " commands]"
  show (Sequence cmds) = "Sequence [" <> show (Array.length cmds) <> " commands]"

-- | Create an atomic compound command.
atomic :: Array EditCommand -> CompoundCommand
atomic = Atomic

-- | Create a sequence compound command.
sequence :: Array EditCommand -> CompoundCommand
sequence = Sequence

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // command // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metadata attached to commands for debugging and collaboration.
type CommandMeta =
  { timestamp :: Maybe Number       -- ^ Unix timestamp in milliseconds
  , userId :: Maybe String          -- ^ User who issued command (for collab)
  , source :: Maybe String          -- ^ Source of command (keyboard, menu, api)
  , mergeId :: Maybe String         -- ^ ID for merging adjacent commands
  }

-- | Create command metadata.
commandMeta
  :: Maybe Number
  -> Maybe String
  -> Maybe String
  -> Maybe String
  -> CommandMeta
commandMeta ts uid src mid =
  { timestamp: ts
  , userId: uid
  , source: src
  , mergeId: mid
  }

-- | Default metadata (all Nothing).
defaultMeta :: CommandMeta
defaultMeta =
  { timestamp: Nothing
  , userId: Nothing
  , source: Nothing
  , mergeId: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // command // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if command is an insert operation.
isInsertCommand :: EditCommand -> Boolean
isInsertCommand = case _ of
  InsertText _ -> true
  InsertNewline -> true
  InsertTab -> true
  _ -> false

-- | Check if command is a delete operation.
isDeleteCommand :: EditCommand -> Boolean
isDeleteCommand = case _ of
  Delete _ _ -> true
  DeleteRange _ _ -> true
  _ -> false

-- | Check if command is a format operation.
isFormatCommand :: EditCommand -> Boolean
isFormatCommand = case _ of
  Format _ -> true
  _ -> false

-- | Check if command is a block operation.
isBlockCommand :: EditCommand -> Boolean
isBlockCommand = case _ of
  BlockOp _ -> true
  _ -> false

-- | Check if command is a navigation operation.
isNavigationCommand :: EditCommand -> Boolean
isNavigationCommand = case _ of
  Navigate _ -> true
  _ -> false

-- | Check if command is a history operation.
isHistoryCommand :: EditCommand -> Boolean
isHistoryCommand = case _ of
  History _ -> true
  _ -> false

-- | Check if command modifies document content.
-- |
-- | Returns true for insert, delete, format, and block commands.
-- | Returns false for navigation, history, and clipboard (reading).
modifiesDocument :: EditCommand -> Boolean
modifiesDocument cmd =
  isInsertCommand cmd ||
  isDeleteCommand cmd ||
  isFormatCommand cmd ||
  isBlockCommand cmd ||
  case cmd of
    Clipboard Cut -> true
    Clipboard Paste -> true
    Clipboard PastePlain -> true
    Compound (Atomic cmds) -> hasDocumentModifier cmds
    Compound (Sequence cmds) -> hasDocumentModifier cmds
    _ -> false
  where
    hasDocumentModifier cmds = case cmds of
      [] -> false
      _ -> true  -- If there are commands, assume some modify document

-- | Check if command modifies selection.
modifiesSelection :: EditCommand -> Boolean
modifiesSelection cmd =
  isNavigationCommand cmd ||
  isInsertCommand cmd ||
  isDeleteCommand cmd
