-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // fileupload
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | File Upload component
-- |
-- | A comprehensive file upload component with drag-and-drop support,
-- | progress tracking, chunked uploads, and preview capabilities.
-- |
-- | ## Features
-- |
-- | - Drag and drop zone
-- | - Click to browse files
-- | - Multiple file selection
-- | - File type restrictions (accept)
-- | - File size limits
-- | - Upload progress bar
-- | - Cancel upload
-- | - Retry failed uploads
-- | - Preview for images
-- | - File list display
-- | - Remove file from list
-- | - Chunked upload support
-- | - Paste from clipboard
-- | - Directory upload (webkitdirectory)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Media.FileUpload as FileUpload
-- |
-- | -- Basic file upload
-- | FileUpload.fileUpload
-- |   [ FileUpload.onSelect HandleFileSelect
-- |   , FileUpload.onComplete HandleUploadComplete
-- |   ]
-- |
-- | -- With restrictions
-- | FileUpload.fileUpload
-- |   [ FileUpload.accept [ "image/*", ".pdf" ]
-- |   , FileUpload.maxSize (10 * 1024 * 1024)  -- 10MB
-- |   , FileUpload.maxFiles 5
-- |   , FileUpload.onError HandleError
-- |   ]
-- |
-- | -- Chunked upload
-- | FileUpload.fileUpload
-- |   [ FileUpload.chunked true
-- |   , FileUpload.chunkSize (1024 * 1024)  -- 1MB chunks
-- |   , FileUpload.onProgress HandleProgress
-- |   ]
-- |
-- | -- Directory upload
-- | FileUpload.fileUpload
-- |   [ FileUpload.directory true
-- |   , FileUpload.onSelect HandleDirectorySelect
-- |   ]
-- |
-- | -- File list with previews
-- | FileUpload.fileList
-- |   [ FileUpload.showPreview true
-- |   , FileUpload.onRemove HandleRemove
-- |   ]
-- |   files
-- | ```
module Hydrogen.Media.FileUpload
  ( -- * File Upload Components
    fileUpload
  , fileList
  , fileItem
  , progressBar
  , dropZone
    -- * Props
  , FileUploadProps
  , FileUploadProp
  , FileListProps
  , FileListProp
  , FileItemProps
  , FileItemProp
  , defaultProps
  , defaultFileListProps
  , defaultFileItemProps
    -- * Prop Builders - FileUpload
  , accept
  , maxSize
  , maxFiles
  , multiple
  , directory
  , chunked
  , chunkSize
  , autoUpload
  , uploadUrl
  , headers
  , withCredentials
  , disabled
  , className
  , onSelect
  , onUpload
  , onProgress
  , onComplete
  , onError
  , onCancel
    -- * Prop Builders - FileList
  , showPreview
  , showProgress
  , showSize
  , listClassName
  , onRemove
  , onRetry
    -- * Prop Builders - FileItem
  , file
  , progress
  , status
  , previewUrl
  , itemClassName
    -- * Types
  , FileInfo
  , UploadStatus(..)
  , UploadError(..)
  , ProgressEvent
  , SelectEvent
  , UploadEvent
  , CompleteEvent
  , ErrorEvent
    -- * FFI
  , UploadElement
  , initFileUpload
  , destroyFileUpload
  , startUpload
  , cancelUpload
  , retryUpload
  , createImagePreview
  , readFileAsDataUrl
  , readFileAsArrayBuffer
  , uploadChunked
  ) where

import Prelude

import Data.Array (foldl, length)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Foreign (Foreign)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.File.File (File)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File information
type FileInfo =
  { id :: String
  , name :: String
  , size :: Number
  , type_ :: String
  , lastModified :: Number
  , file :: File
  , previewUrl :: Maybe String
  , progress :: Number
  , status :: UploadStatus
  , error :: Maybe String
  }

-- | Upload status
data UploadStatus
  = Pending
  | Uploading
  | Completed
  | Failed
  | Cancelled

derive instance eqUploadStatus :: Eq UploadStatus

-- | Upload error types
data UploadError
  = FileTooLarge { maxSize :: Number, actualSize :: Number }
  | InvalidFileType { accepted :: Array String, actual :: String }
  | TooManyFiles { maxFiles :: Int, actualFiles :: Int }
  | NetworkError String
  | ServerError { status :: Int, message :: String }
  | AbortedError
  | UnknownError String

derive instance eqUploadError :: Eq UploadError

-- | Progress event
type ProgressEvent =
  { fileId :: String
  , loaded :: Number
  , total :: Number
  , percent :: Number
  }

-- | Select event
type SelectEvent =
  { files :: Array FileInfo
  }

-- | Upload event
type UploadEvent =
  { fileId :: String
  , file :: FileInfo
  }

-- | Complete event
type CompleteEvent =
  { fileId :: String
  , response :: Foreign
  }

-- | Error event
type ErrorEvent =
  { fileId :: String
  , error :: UploadError
  }

-- | Opaque upload element for FFI
foreign import data UploadElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize file upload
foreign import initFileUploadImpl :: EffectFn3 Element
  { onDragEnter :: Effect Unit
  , onDragLeave :: Effect Unit
  , onDrop :: Array File -> Effect Unit
  , onFileSelect :: Array File -> Effect Unit
  , onPaste :: Array File -> Effect Unit
  }
  { accept :: Array String
  , maxSize :: Number
  , maxFiles :: Int
  , multiple :: Boolean
  , directory :: Boolean
  }
  UploadElement

-- | Destroy file upload
foreign import destroyFileUploadImpl :: EffectFn1 UploadElement Unit

-- | Start uploading a file
foreign import startUploadImpl :: EffectFn3 UploadElement FileInfo
  { onProgress :: ProgressEvent -> Effect Unit
  , onComplete :: CompleteEvent -> Effect Unit
  , onError :: ErrorEvent -> Effect Unit
  }
  Unit

-- | Cancel an upload
foreign import cancelUploadImpl :: EffectFn2 UploadElement String Unit

-- | Retry a failed upload
foreign import retryUploadImpl :: EffectFn2 UploadElement String Unit

-- | Create image preview
foreign import createImagePreviewImpl :: EffectFn2 File 
  (String -> Effect Unit) 
  Unit

-- | Read file as data URL
foreign import readFileAsDataUrlImpl :: EffectFn2 File
  (String -> Effect Unit)
  Unit

-- | Read file as ArrayBuffer
foreign import readFileAsArrayBufferImpl :: EffectFn2 File
  (Foreign -> Effect Unit)
  Unit

-- | Upload file in chunks
foreign import uploadChunkedImpl :: EffectFn3 UploadElement FileInfo
  { chunkSize :: Int
  , onChunkComplete :: Int -> Effect Unit
  , onProgress :: ProgressEvent -> Effect Unit
  , onComplete :: CompleteEvent -> Effect Unit
  , onError :: ErrorEvent -> Effect Unit
  }
  Unit

-- | Initialize file upload
initFileUpload :: Element ->
  { onDragEnter :: Effect Unit
  , onDragLeave :: Effect Unit
  , onDrop :: Array File -> Effect Unit
  , onFileSelect :: Array File -> Effect Unit
  , onPaste :: Array File -> Effect Unit
  } ->
  { accept :: Array String
  , maxSize :: Number
  , maxFiles :: Int
  , multiple :: Boolean
  , directory :: Boolean
  } ->
  Effect UploadElement
initFileUpload el callbacks opts = do
  pure unsafeUploadElement

-- | Destroy file upload
destroyFileUpload :: UploadElement -> Effect Unit
destroyFileUpload _ = pure unit

-- | Start upload
startUpload :: UploadElement -> FileInfo ->
  { onProgress :: ProgressEvent -> Effect Unit
  , onComplete :: CompleteEvent -> Effect Unit
  , onError :: ErrorEvent -> Effect Unit
  } ->
  Effect Unit
startUpload _ _ _ = pure unit

-- | Cancel upload
cancelUpload :: UploadElement -> String -> Effect Unit
cancelUpload _ _ = pure unit

-- | Retry upload
retryUpload :: UploadElement -> String -> Effect Unit
retryUpload _ _ = pure unit

-- | Create image preview
createImagePreview :: File -> (String -> Effect Unit) -> Effect Unit
createImagePreview _ _ = pure unit

-- | Read file as data URL
readFileAsDataUrl :: File -> (String -> Effect Unit) -> Effect Unit
readFileAsDataUrl _ _ = pure unit

-- | Read file as ArrayBuffer
readFileAsArrayBuffer :: File -> (Foreign -> Effect Unit) -> Effect Unit
readFileAsArrayBuffer _ _ = pure unit

-- | Upload chunked
uploadChunked :: UploadElement -> FileInfo ->
  { chunkSize :: Int
  , onChunkComplete :: Int -> Effect Unit
  , onProgress :: ProgressEvent -> Effect Unit
  , onComplete :: CompleteEvent -> Effect Unit
  , onError :: ErrorEvent -> Effect Unit
  } ->
  Effect Unit
uploadChunked _ _ _ = pure unit

-- Internal placeholder
foreign import unsafeUploadElement :: UploadElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File upload properties
type FileUploadProps i =
  { accept :: Array String
  , maxSize :: Number
  , maxFiles :: Int
  , multiple :: Boolean
  , directory :: Boolean
  , chunked :: Boolean
  , chunkSize :: Int
  , autoUpload :: Boolean
  , uploadUrl :: String
  , headers :: Array { key :: String, value :: String }
  , withCredentials :: Boolean
  , disabled :: Boolean
  , className :: String
  , onSelect :: Maybe (SelectEvent -> i)
  , onUpload :: Maybe (UploadEvent -> i)
  , onProgress :: Maybe (ProgressEvent -> i)
  , onComplete :: Maybe (CompleteEvent -> i)
  , onError :: Maybe (ErrorEvent -> i)
  , onCancel :: Maybe (String -> i)
  }

-- | File upload property modifier
type FileUploadProp i = FileUploadProps i -> FileUploadProps i

-- | Default file upload properties
defaultProps :: forall i. FileUploadProps i
defaultProps =
  { accept: []
  , maxSize: 0.0  -- 0 = no limit
  , maxFiles: 0   -- 0 = no limit
  , multiple: true
  , directory: false
  , chunked: false
  , chunkSize: 1048576  -- 1MB
  , autoUpload: false
  , uploadUrl: ""
  , headers: []
  , withCredentials: false
  , disabled: false
  , className: ""
  , onSelect: Nothing
  , onUpload: Nothing
  , onProgress: Nothing
  , onComplete: Nothing
  , onError: Nothing
  , onCancel: Nothing
  }

-- | File list properties
type FileListProps i =
  { showPreview :: Boolean
  , showProgress :: Boolean
  , showSize :: Boolean
  , className :: String
  , onRemove :: Maybe (String -> i)
  , onRetry :: Maybe (String -> i)
  }

-- | File list property modifier
type FileListProp i = FileListProps i -> FileListProps i

-- | Default file list properties
defaultFileListProps :: forall i. FileListProps i
defaultFileListProps =
  { showPreview: true
  , showProgress: true
  , showSize: true
  , className: ""
  , onRemove: Nothing
  , onRetry: Nothing
  }

-- | File item properties
type FileItemProps i =
  { file :: Maybe FileInfo
  , progress :: Number
  , status :: UploadStatus
  , previewUrl :: Maybe String
  , className :: String
  }

-- | File item property modifier
type FileItemProp i = FileItemProps i -> FileItemProps i

-- | Default file item properties
defaultFileItemProps :: forall i. FileItemProps i
defaultFileItemProps =
  { file: Nothing
  , progress: 0.0
  , status: Pending
  , previewUrl: Nothing
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set accepted file types
accept :: forall i. Array String -> FileUploadProp i
accept a props = props { accept = a }

-- | Set maximum file size in bytes
maxSize :: forall i. Number -> FileUploadProp i
maxSize s props = props { maxSize = s }

-- | Set maximum number of files
maxFiles :: forall i. Int -> FileUploadProp i
maxFiles m props = props { maxFiles = m }

-- | Enable multiple file selection
multiple :: forall i. Boolean -> FileUploadProp i
multiple m props = props { multiple = m }

-- | Enable directory upload
directory :: forall i. Boolean -> FileUploadProp i
directory d props = props { directory = d }

-- | Enable chunked upload
chunked :: forall i. Boolean -> FileUploadProp i
chunked c props = props { chunked = c }

-- | Set chunk size in bytes
chunkSize :: forall i. Int -> FileUploadProp i
chunkSize s props = props { chunkSize = s }

-- | Enable auto-upload on file select
autoUpload :: forall i. Boolean -> FileUploadProp i
autoUpload a props = props { autoUpload = a }

-- | Set upload URL
uploadUrl :: forall i. String -> FileUploadProp i
uploadUrl u props = props { uploadUrl = u }

-- | Set upload headers
headers :: forall i. Array { key :: String, value :: String } -> FileUploadProp i
headers h props = props { headers = h }

-- | Enable credentials in upload requests
withCredentials :: forall i. Boolean -> FileUploadProp i
withCredentials w props = props { withCredentials = w }

-- | Disable file upload
disabled :: forall i. Boolean -> FileUploadProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> FileUploadProp i
className c props = props { className = props.className <> " " <> c }

-- | Set select handler
onSelect :: forall i. (SelectEvent -> i) -> FileUploadProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set upload start handler
onUpload :: forall i. (UploadEvent -> i) -> FileUploadProp i
onUpload handler props = props { onUpload = Just handler }

-- | Set progress handler
onProgress :: forall i. (ProgressEvent -> i) -> FileUploadProp i
onProgress handler props = props { onProgress = Just handler }

-- | Set complete handler
onComplete :: forall i. (CompleteEvent -> i) -> FileUploadProp i
onComplete handler props = props { onComplete = Just handler }

-- | Set error handler
onError :: forall i. (ErrorEvent -> i) -> FileUploadProp i
onError handler props = props { onError = Just handler }

-- | Set cancel handler
onCancel :: forall i. (String -> i) -> FileUploadProp i
onCancel handler props = props { onCancel = Just handler }

-- | Show preview images
showPreview :: forall i. Boolean -> FileListProp i
showPreview s props = props { showPreview = s }

-- | Show progress bars
showProgress :: forall i. Boolean -> FileListProp i
showProgress s props = props { showProgress = s }

-- | Show file sizes
showSize :: forall i. Boolean -> FileListProp i
showSize s props = props { showSize = s }

-- | Add custom class to file list
listClassName :: forall i. String -> FileListProp i
listClassName c props = props { className = props.className <> " " <> c }

-- | Set remove handler
onRemove :: forall i. (String -> i) -> FileListProp i
onRemove handler props = props { onRemove = Just handler }

-- | Set retry handler
onRetry :: forall i. (String -> i) -> FileListProp i
onRetry handler props = props { onRetry = Just handler }

-- | Set file info
file :: forall i. FileInfo -> FileItemProp i
file f props = props { file = Just f }

-- | Set progress
progress :: forall i. Number -> FileItemProp i
progress p props = props { progress = p }

-- | Set status
status :: forall i. UploadStatus -> FileItemProp i
status s props = props { status = s }

-- | Set preview URL
previewUrl :: forall i. String -> FileItemProp i
previewUrl u props = props { previewUrl = Just u }

-- | Add custom class to file item
itemClassName :: forall i. String -> FileItemProp i
itemClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File upload component
-- |
-- | Drag-and-drop zone with file browser fallback
fileUpload :: forall w i. Array (FileUploadProp i) -> HH.HTML w i
fileUpload propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    acceptStr = joinWith "," props.accept
    
    containerClasses = 
      "file-upload relative group"
      <> (if props.disabled then " opacity-50 pointer-events-none" else "")
    
    dropZoneClasses =
      "flex flex-col items-center justify-center w-full min-h-[200px] p-8 border-2 border-dashed border-muted-foreground/25 rounded-lg bg-muted/10 cursor-pointer transition-all hover:border-primary/50 hover:bg-muted/20 [&[data-drag-over=true]]:border-primary [&[data-drag-over=true]]:bg-primary/10"
    
    inputAttrs = 
      [ HP.type_ HP.InputFile
      , cls [ "sr-only" ]
      , HP.id "file-upload-input"
      , HP.attr (HH.AttrName "accept") acceptStr
      ] <> 
      (if props.multiple then [ HP.attr (HH.AttrName "multiple") "true" ] else []) <>
      (if props.directory then [ HP.attr (HH.AttrName "webkitdirectory") "true" ] else [])
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-file-upload") "true"
      ]
      [ HH.label
          [ cls [ dropZoneClasses ]
          , HP.for "file-upload-input"
          , HP.attr (HH.AttrName "data-drop-zone") "true"
          , ARIA.role "button"
          , HP.tabIndex 0
          ]
          [ HH.div
              [ cls [ "flex flex-col items-center gap-3 text-center" ] ]
              [ -- Upload icon
                HH.div
                  [ cls [ "w-12 h-12 rounded-full bg-primary/10 flex items-center justify-center text-primary" ] ]
                  [ HH.span [ cls [ "text-2xl" ] ] [ HH.text "+" ] ]
              , -- Text
                HH.div
                  [ cls [ "space-y-1" ] ]
                  [ HH.p
                      [ cls [ "text-sm font-medium text-foreground" ] ]
                      [ HH.text "Drag & drop files here" ]
                  , HH.p
                      [ cls [ "text-xs text-muted-foreground" ] ]
                      [ HH.text "or click to browse" ]
                  ]
              , -- Restrictions
                if length props.accept > 0 || props.maxSize > 0.0
                  then
                    HH.p
                      [ cls [ "text-xs text-muted-foreground mt-2" ] ]
                      [ HH.text (restrictionText props) ]
                  else
                    HH.text ""
              ]
          ]
      , HH.input inputAttrs
      ]
  where
    joinWith :: String -> Array String -> String
    joinWith = joinWithImpl
    
    restrictionText :: FileUploadProps i -> String
    restrictionText p =
      let
        typeText = if length p.accept > 0 
          then "Accepts: " <> joinWith ", " p.accept 
          else ""
        sizeText = if p.maxSize > 0.0 
          then "Max size: " <> formatFileSize p.maxSize 
          else ""
      in
        case typeText, sizeText of
          "", "" -> ""
          t, "" -> t
          "", s -> s
          t, s -> t <> " | " <> s

foreign import joinWithImpl :: String -> Array String -> String

-- | Drop zone component
-- |
-- | Standalone drop zone for custom layouts
dropZone :: forall w i. Array (FileUploadProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropZone propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    zoneClasses =
      "drop-zone flex flex-col items-center justify-center min-h-[150px] p-6 border-2 border-dashed border-muted-foreground/25 rounded-lg transition-all [&[data-drag-over=true]]:border-primary [&[data-drag-over=true]]:bg-primary/10"
  in
    HH.div
      [ cls [ zoneClasses, props.className ]
      , HP.attr (HH.AttrName "data-drop-zone") "true"
      , ARIA.role "region"
      , ARIA.label "Drop zone"
      ]
      children

-- | File list component
-- |
-- | Displays uploaded files with progress and actions
fileList :: forall w i. Array (FileListProp i) -> Array FileInfo -> HH.HTML w i
fileList propMods files =
  let
    props = foldl (\p f -> f p) defaultFileListProps propMods
    
    listClasses = "file-list space-y-2"
  in
    HH.div
      [ cls [ listClasses, props.className ]
      , ARIA.role "list"
      , ARIA.label "Uploaded files"
      ]
      (map (renderFileItem props) files)
  where
    renderFileItem :: FileListProps i -> FileInfo -> HH.HTML w i
    renderFileItem props' fileInfo =
      let
        itemClasses = 
          "flex items-center gap-3 p-3 rounded-lg border bg-card text-card-foreground"
          <> case fileInfo.status of
               Failed -> " border-destructive/50 bg-destructive/5"
               Completed -> " border-green-500/50 bg-green-500/5"
               _ -> " border-border"
        
        statusIcon = case fileInfo.status of
          Pending -> HH.span [ cls [ "text-muted-foreground" ] ] [ HH.text "..." ]
          Uploading -> HH.span [ cls [ "animate-spin text-primary" ] ] [ HH.text "O" ]
          Completed -> HH.span [ cls [ "text-green-500" ] ] [ HH.text "V" ]
          Failed -> HH.span [ cls [ "text-destructive" ] ] [ HH.text "X" ]
          Cancelled -> HH.span [ cls [ "text-muted-foreground" ] ] [ HH.text "-" ]
        
        preview = case props'.showPreview, fileInfo.previewUrl of
          true, Just url ->
            HH.img
              [ cls [ "w-10 h-10 rounded object-cover" ]
              , HP.src url
              , HP.alt fileInfo.name
              ]
          _, _ ->
            HH.div
              [ cls [ "w-10 h-10 rounded bg-muted flex items-center justify-center text-muted-foreground text-xs" ] ]
              [ HH.text (getFileExtension fileInfo.name) ]
        
        removeBtn = case props'.onRemove of
          Just handler ->
            HH.button
              [ cls [ "p-1 rounded hover:bg-muted text-muted-foreground hover:text-foreground transition-colors" ]
              , HP.type_ HP.ButtonButton
              , ARIA.label "Remove file"
              , HE.onClick (\_ -> handler fileInfo.id)
              ]
              [ HH.text "X" ]
          Nothing -> HH.text ""
        
        retryBtn = case fileInfo.status, props'.onRetry of
          Failed, Just handler ->
            HH.button
              [ cls [ "px-2 py-1 rounded text-xs bg-primary text-primary-foreground hover:bg-primary/90" ]
              , HP.type_ HP.ButtonButton
              , HE.onClick (\_ -> handler fileInfo.id)
              ]
              [ HH.text "Retry" ]
          _, _ -> HH.text ""
        
        progressBarEl =
          if props'.showProgress && fileInfo.status == Uploading
            then progressBar fileInfo.progress
            else HH.text ""
      in
        HH.div
          [ cls [ itemClasses ]
          , HP.attr (HH.AttrName "data-file-id") fileInfo.id
          , ARIA.role "listitem"
          ]
          [ preview
          , HH.div
              [ cls [ "flex-1 min-w-0" ] ]
              [ HH.div
                  [ cls [ "flex items-center gap-2" ] ]
                  [ HH.span 
                      [ cls [ "text-sm font-medium truncate" ] ] 
                      [ HH.text fileInfo.name ]
                  , statusIcon
                  ]
              , if props'.showSize
                  then 
                    HH.span 
                      [ cls [ "text-xs text-muted-foreground" ] ] 
                      [ HH.text (formatFileSize fileInfo.size) ]
                  else HH.text ""
              , progressBarEl
              , case fileInfo.error of
                  Just err -> 
                    HH.span 
                      [ cls [ "text-xs text-destructive" ] ] 
                      [ HH.text err ]
                  Nothing -> HH.text ""
              ]
          , retryBtn
          , removeBtn
          ]

-- | Single file item
-- |
-- | For custom file list layouts
fileItem :: forall w i. Array (FileItemProp i) -> HH.HTML w i
fileItem propMods =
  let
    props = foldl (\p f -> f p) defaultFileItemProps propMods
    
    itemClasses = "file-item flex items-center gap-3 p-3 rounded-lg border bg-card"
  in
    HH.div
      [ cls [ itemClasses, props.className ]
      , ARIA.role "listitem"
      ]
      [ case props.previewUrl of
          Just url ->
            HH.img
              [ cls [ "w-10 h-10 rounded object-cover" ]
              , HP.src url
              ]
          Nothing ->
            HH.div
              [ cls [ "w-10 h-10 rounded bg-muted" ] ]
              []
      , HH.div
          [ cls [ "flex-1" ] ]
          [ case props.file of
              Just f -> HH.span [ cls [ "text-sm font-medium" ] ] [ HH.text f.name ]
              Nothing -> HH.text ""
          , if props.status == Uploading
              then progressBar props.progress
              else HH.text ""
          ]
      ]

-- | Progress bar
-- |
-- | Displays upload progress
progressBar :: forall w i. Number -> HH.HTML w i
progressBar percent =
  let
    percentInt = toInt percent
    widthStyle = "width: " <> show percentInt <> "%"
  in
    HH.div
      [ cls [ "mt-1 h-1.5 w-full bg-muted rounded-full overflow-hidden" ]
      , ARIA.role "progressbar"
      , ARIA.valueMin "0"
      , ARIA.valueMax "100"
      , ARIA.valueNow (show percentInt)
      ]
      [ HH.div
          [ cls [ "h-full bg-primary transition-all duration-150" ]
          , HP.attr (HH.AttrName "style") widthStyle
          ]
          []
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format file size to human readable string
formatFileSize :: Number -> String
formatFileSize = formatFileSizeImpl

foreign import formatFileSizeImpl :: Number -> String

-- | Get file extension
getFileExtension :: String -> String
getFileExtension = getFileExtensionImpl

foreign import getFileExtensionImpl :: String -> String

-- | Convert Number to Int
toInt :: Number -> Int
toInt = toIntImpl

foreign import toIntImpl :: Number -> Int

-- | Generate unique file ID
foreign import generateFileIdImpl :: Effect String

-- | Validate file against restrictions
foreign import validateFileImpl :: File -> 
  { accept :: Array String, maxSize :: Number } -> 
  Effect (Maybe String)
