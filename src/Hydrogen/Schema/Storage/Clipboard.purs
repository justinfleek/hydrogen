-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // storage // clipboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Clipboard — ADT types for browser Clipboard API operations.
-- |
-- | ## Design Philosophy
-- |
-- | The Clipboard API is asynchronous and requires user permission.
-- | This module represents clipboard data and operations as pure data,
-- | enabling:
-- | - Type-safe clipboard content handling
-- | - Permission requirement tracking
-- | - Operation composition without side effects
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Clipboard operations are represented as intent. Agents can compose
-- | copy/paste workflows, validate content types, and handle errors
-- | declaratively without executing browser APIs.

module Hydrogen.Schema.Storage.Clipboard
  ( -- * MIME Type
    MimeType(TextPlain, TextHtml, TextRtf, ImagePng, ImageJpeg, ImageGif, ImageSvg, ImageWebp, ApplicationJson, CustomMimeType)
  , mimeTypeString
  , mimeTypeCategory
  , isTextMimeType
  , isImageMimeType
  
  -- * Clipboard Item
  , ClipboardItem(TextItem, HtmlItem, ImageItem, BinaryItem)
  , clipboardItemMimeType
  , textItem
  , htmlItem
  , imageItem
  , binaryItem
  , isTextItem
  , isImageItem
  , clipboardItemSize
  
  -- * Clipboard Contents
  , ClipboardContents
  , clipboardContents
  , emptyClipboard
  , clipboardItems
  , clipboardItemCount
  , hasTextContent
  , hasImageContent
  , firstTextItem
  , firstImageItem
  
  -- * Clipboard Operation
  , ClipboardOp(ReadClipboard, WriteClipboard, WriteTextOp, ReadTextOp)
  , readClipboard
  , writeClipboard
  , writeText
  , readText
  , opIsRead
  , opIsWrite
  , opRequiresPermission
  
  -- * Clipboard Error
  , ClipboardError(ClipboardNotSupported, PermissionDenied, ReadFailed, WriteFailed, InvalidData, FocusRequired)
  , clipboardErrorMessage
  , isPermissionError
  , isNotSupportedError
  
  -- * Clipboard Permission
  , ClipboardPermission(PermissionGranted, PermissionDeniedState, PermissionPrompt)
  , permissionLabel
  , isPermissionGranted
  , permissionForOperation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , show
  , not
  , (<>)
  )

import Data.Array (head, filter, length, null) as Array
import Data.Maybe (Maybe)
import Data.String (length) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // mime type
-- ═════════════════════════════════════════════════════════════════════════════

-- | MimeType — content type for clipboard data.
-- |
-- | The Clipboard API uses MIME types to identify content formats.
data MimeType
  = TextPlain           -- ^ text/plain
  | TextHtml            -- ^ text/html
  | TextRtf             -- ^ text/rtf
  | ImagePng            -- ^ image/png
  | ImageJpeg           -- ^ image/jpeg
  | ImageGif            -- ^ image/gif
  | ImageSvg            -- ^ image/svg+xml
  | ImageWebp           -- ^ image/webp
  | ApplicationJson     -- ^ application/json
  | CustomMimeType String  -- ^ Custom MIME type

derive instance eqMimeType :: Eq MimeType
derive instance ordMimeType :: Ord MimeType

instance showMimeType :: Show MimeType where
  show = mimeTypeString

-- | Convert MIME type to string.
mimeTypeString :: MimeType -> String
mimeTypeString TextPlain = "text/plain"
mimeTypeString TextHtml = "text/html"
mimeTypeString TextRtf = "text/rtf"
mimeTypeString ImagePng = "image/png"
mimeTypeString ImageJpeg = "image/jpeg"
mimeTypeString ImageGif = "image/gif"
mimeTypeString ImageSvg = "image/svg+xml"
mimeTypeString ImageWebp = "image/webp"
mimeTypeString ApplicationJson = "application/json"
mimeTypeString (CustomMimeType s) = s

-- | Get the category of a MIME type.
mimeTypeCategory :: MimeType -> String
mimeTypeCategory TextPlain = "text"
mimeTypeCategory TextHtml = "text"
mimeTypeCategory TextRtf = "text"
mimeTypeCategory ImagePng = "image"
mimeTypeCategory ImageJpeg = "image"
mimeTypeCategory ImageGif = "image"
mimeTypeCategory ImageSvg = "image"
mimeTypeCategory ImageWebp = "image"
mimeTypeCategory ApplicationJson = "application"
mimeTypeCategory (CustomMimeType _) = "custom"

-- | Check if MIME type is a text type.
isTextMimeType :: MimeType -> Boolean
isTextMimeType TextPlain = true
isTextMimeType TextHtml = true
isTextMimeType TextRtf = true
isTextMimeType ApplicationJson = true
isTextMimeType _ = false

-- | Check if MIME type is an image type.
isImageMimeType :: MimeType -> Boolean
isImageMimeType ImagePng = true
isImageMimeType ImageJpeg = true
isImageMimeType ImageGif = true
isImageMimeType ImageSvg = true
isImageMimeType ImageWebp = true
isImageMimeType _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // clipboard item
-- ═════════════════════════════════════════════════════════════════════════════

-- | ClipboardItem — a single item on the clipboard.
-- |
-- | The clipboard can hold multiple items with different MIME types.
-- | This type represents a single content item.
data ClipboardItem
  = TextItem String               -- ^ Plain text content
  | HtmlItem String               -- ^ HTML markup content
  | ImageItem Int                 -- ^ Image as bytes (size in bytes)
  | BinaryItem MimeType Int       -- ^ Binary data with MIME type and size

derive instance eqClipboardItem :: Eq ClipboardItem

instance showClipboardItem :: Show ClipboardItem where
  show (TextItem t) = "(TextItem " <> show (String.length t) <> " chars)"
  show (HtmlItem h) = "(HtmlItem " <> show (String.length h) <> " chars)"
  show (ImageItem size) = "(ImageItem " <> show size <> " bytes)"
  show (BinaryItem mime size) = "(BinaryItem " <> show mime <> " " <> show size <> " bytes)"

-- | Get the MIME type of a clipboard item.
clipboardItemMimeType :: ClipboardItem -> MimeType
clipboardItemMimeType (TextItem _) = TextPlain
clipboardItemMimeType (HtmlItem _) = TextHtml
clipboardItemMimeType (ImageItem _) = ImagePng
clipboardItemMimeType (BinaryItem mime _) = mime

-- | Create a plain text clipboard item.
textItem :: String -> ClipboardItem
textItem = TextItem

-- | Create an HTML clipboard item.
htmlItem :: String -> ClipboardItem
htmlItem = HtmlItem

-- | Create an image clipboard item (with byte size).
imageItem :: Int -> ClipboardItem
imageItem = ImageItem

-- | Create a binary clipboard item.
binaryItem :: MimeType -> Int -> ClipboardItem
binaryItem = BinaryItem

-- | Check if item is a text item.
isTextItem :: ClipboardItem -> Boolean
isTextItem (TextItem _) = true
isTextItem (HtmlItem _) = true
isTextItem _ = false

-- | Check if item is an image item.
isImageItem :: ClipboardItem -> Boolean
isImageItem (ImageItem _) = true
isImageItem (BinaryItem mime _) = isImageMimeType mime
isImageItem _ = false

-- | Get the size of a clipboard item in bytes/characters.
clipboardItemSize :: ClipboardItem -> Int
clipboardItemSize (TextItem t) = String.length t
clipboardItemSize (HtmlItem h) = String.length h
clipboardItemSize (ImageItem size) = size
clipboardItemSize (BinaryItem _ size) = size

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // clipboard contents
-- ═════════════════════════════════════════════════════════════════════════════

-- | ClipboardContents — the complete clipboard state.
-- |
-- | The clipboard can hold multiple items simultaneously.
-- | For example, copying from a web page might include both
-- | plain text and HTML representations.
type ClipboardContents =
  { items :: Array ClipboardItem
  }

-- | Construct clipboard contents from items.
clipboardContents :: Array ClipboardItem -> ClipboardContents
clipboardContents items = { items: items }

-- | Empty clipboard.
emptyClipboard :: ClipboardContents
emptyClipboard = { items: [] }

-- | Get all clipboard items.
clipboardItems :: ClipboardContents -> Array ClipboardItem
clipboardItems c = c.items

-- | Count items on clipboard.
clipboardItemCount :: ClipboardContents -> Int
clipboardItemCount c = Array.length c.items

-- | Check if clipboard has text content.
hasTextContent :: ClipboardContents -> Boolean
hasTextContent c = not (Array.null (Array.filter isTextItem c.items))

-- | Check if clipboard has image content.
hasImageContent :: ClipboardContents -> Boolean
hasImageContent c = not (Array.null (Array.filter isImageItem c.items))

-- | Get the first text item from clipboard.
firstTextItem :: ClipboardContents -> Maybe ClipboardItem
firstTextItem c = Array.head (Array.filter isTextItem c.items)

-- | Get the first image item from clipboard.
firstImageItem :: ClipboardContents -> Maybe ClipboardItem
firstImageItem c = Array.head (Array.filter isImageItem c.items)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // clipboard operation
-- ═════════════════════════════════════════════════════════════════════════════

-- | ClipboardOp — ADT representing clipboard operations.
-- |
-- | Operations are pure data describing intent. This is not parameterized
-- | because different operations have different result types; use the
-- | result type functions to determine expected results.
data ClipboardOp
  = ReadClipboard                 -- ^ Read all clipboard contents
  | WriteClipboard ClipboardContents  -- ^ Write contents to clipboard
  | WriteTextOp String            -- ^ Shorthand for writing plain text
  | ReadTextOp                    -- ^ Shorthand for reading plain text

derive instance eqClipboardOp :: Eq ClipboardOp

instance showClipboardOp :: Show ClipboardOp where
  show ReadClipboard = "ReadClipboard"
  show (WriteClipboard c) = "(WriteClipboard " <> show (clipboardItemCount c) <> " items)"
  show (WriteTextOp t) = "(WriteTextOp " <> show (String.length t) <> " chars)"
  show ReadTextOp = "ReadTextOp"

-- | Create a read clipboard operation.
readClipboard :: ClipboardOp
readClipboard = ReadClipboard

-- | Create a write clipboard operation.
writeClipboard :: ClipboardContents -> ClipboardOp
writeClipboard = WriteClipboard

-- | Create a write text operation.
writeText :: String -> ClipboardOp
writeText = WriteTextOp

-- | Create a read text operation.
readText :: ClipboardOp
readText = ReadTextOp

-- | Check if operation is a read.
opIsRead :: ClipboardOp -> Boolean
opIsRead ReadClipboard = true
opIsRead ReadTextOp = true
opIsRead _ = false

-- | Check if operation is a write.
opIsWrite :: ClipboardOp -> Boolean
opIsWrite (WriteClipboard _) = true
opIsWrite (WriteTextOp _) = true
opIsWrite _ = false

-- | Check if operation requires explicit permission.
-- |
-- | Read operations always require permission.
-- | Write operations may work without permission in some contexts
-- | (e.g., in response to user action).
opRequiresPermission :: ClipboardOp -> Boolean
opRequiresPermission ReadClipboard = true
opRequiresPermission ReadTextOp = true
opRequiresPermission (WriteClipboard _) = true
opRequiresPermission (WriteTextOp _) = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // clipboard error
-- ═════════════════════════════════════════════════════════════════════════════

-- | ClipboardError — errors that can occur during clipboard operations.
data ClipboardError
  = ClipboardNotSupported             -- ^ Clipboard API not available
  | PermissionDenied                  -- ^ User denied permission
  | ReadFailed String                 -- ^ Failed to read clipboard
  | WriteFailed String                -- ^ Failed to write to clipboard
  | InvalidData String                -- ^ Data format invalid
  | FocusRequired                     -- ^ Window must be focused

derive instance eqClipboardError :: Eq ClipboardError

instance showClipboardError :: Show ClipboardError where
  show ClipboardNotSupported = "ClipboardNotSupported"
  show PermissionDenied = "PermissionDenied"
  show (ReadFailed msg) = "(ReadFailed " <> show msg <> ")"
  show (WriteFailed msg) = "(WriteFailed " <> show msg <> ")"
  show (InvalidData msg) = "(InvalidData " <> show msg <> ")"
  show FocusRequired = "FocusRequired"

-- | Get human-readable error message.
clipboardErrorMessage :: ClipboardError -> String
clipboardErrorMessage ClipboardNotSupported = "Clipboard API is not supported in this browser"
clipboardErrorMessage PermissionDenied = "Permission to access clipboard was denied"
clipboardErrorMessage (ReadFailed msg) = "Failed to read clipboard: " <> msg
clipboardErrorMessage (WriteFailed msg) = "Failed to write to clipboard: " <> msg
clipboardErrorMessage (InvalidData msg) = "Invalid clipboard data: " <> msg
clipboardErrorMessage FocusRequired = "Window must be focused to access clipboard"

-- | Check if error is a permission error.
isPermissionError :: ClipboardError -> Boolean
isPermissionError PermissionDenied = true
isPermissionError _ = false

-- | Check if error is a not-supported error.
isNotSupportedError :: ClipboardError -> Boolean
isNotSupportedError ClipboardNotSupported = true
isNotSupportedError _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // clipboard permission
-- ═════════════════════════════════════════════════════════════════════════════

-- | ClipboardPermission — permission state for clipboard access.
data ClipboardPermission
  = PermissionGranted         -- ^ Permission granted
  | PermissionDeniedState     -- ^ Permission explicitly denied
  | PermissionPrompt          -- ^ Permission not yet requested

derive instance eqClipboardPermission :: Eq ClipboardPermission
derive instance ordClipboardPermission :: Ord ClipboardPermission

instance showClipboardPermission :: Show ClipboardPermission where
  show = permissionLabel

-- | Get display label for permission state.
permissionLabel :: ClipboardPermission -> String
permissionLabel PermissionGranted = "granted"
permissionLabel PermissionDeniedState = "denied"
permissionLabel PermissionPrompt = "prompt"

-- | Check if permission is granted.
isPermissionGranted :: ClipboardPermission -> Boolean
isPermissionGranted PermissionGranted = true
isPermissionGranted _ = false

-- | Determine required permission for an operation.
permissionForOperation :: ClipboardOp -> String
permissionForOperation ReadClipboard = "clipboard-read"
permissionForOperation ReadTextOp = "clipboard-read"
permissionForOperation (WriteClipboard _) = "clipboard-write"
permissionForOperation (WriteTextOp _) = "clipboard-write"
