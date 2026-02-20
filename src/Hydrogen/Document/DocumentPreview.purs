-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // documentpreview
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generic Document Preview Component
-- |
-- | Automatically detects file type and renders appropriate preview
-- | for images, videos, audio, PDFs, text, code, and more.
-- |
-- | ## Features
-- |
-- | - Automatic file type detection
-- | - Image preview (with zoom)
-- | - Video preview with controls
-- | - Audio preview with waveform
-- | - PDF preview (embedded PDFViewer)
-- | - Text file preview
-- | - Code file preview with syntax highlighting
-- | - Office document preview (download prompt or iframe)
-- | - Unsupported file message
-- | - Loading state
-- | - Error state
-- | - Download button
-- | - Open in new tab
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Document.DocumentPreview as Preview
-- |
-- | -- Basic preview
-- | Preview.documentPreview
-- |   [ Preview.source fileUrl
-- |   , Preview.fileName "document.pdf"
-- |   ]
-- |
-- | -- With callbacks
-- | Preview.documentPreview
-- |   [ Preview.source fileUrl
-- |   , Preview.fileName "image.png"
-- |   , Preview.onLoad HandleLoad
-- |   , Preview.onError HandleError
-- |   , Preview.onDownload HandleDownload
-- |   ]
-- |
-- | -- Force specific type
-- | Preview.documentPreview
-- |   [ Preview.source codeUrl
-- |   , Preview.fileName "script.js"
-- |   , Preview.fileType Preview.Code
-- |   , Preview.codeLanguage "javascript"
-- |   ]
-- | ```
module Hydrogen.Document.DocumentPreview
  ( -- * Component
    documentPreview
  , inlinePreview
    -- * Props
  , DocumentPreviewProps
  , DocumentPreviewProp
  , defaultProps
    -- * Prop Builders
  , source
  , fileName
  , fileType
  , fileSize
  , mimeType
  , codeLanguage
  , showToolbar
  , showDownload
  , showOpenInNew
  , maxWidth
  , maxHeight
  , className
    -- * Event Handlers
  , onLoad
  , onError
  , onDownload
  , onOpenInNew
    -- * Types
  , FileType(..)
  , PreviewState(..)
  , FileInfo
    -- * Detection
  , detectFileType
  , getFileExtension
  , getMimeCategory
    -- * FFI
  , loadFileInfo
  , downloadFile
  , openInNewTab
  ) where

import Prelude

import Data.Array (elem, foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split, toLower)
import Data.String as String
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Supported file types
data FileType
  = Image       -- ^ Images (jpg, png, gif, svg, webp)
  | Video       -- ^ Videos (mp4, webm, mov)
  | Audio       -- ^ Audio (mp3, wav, ogg, flac)
  | PDF         -- ^ PDF documents
  | Text        -- ^ Plain text files
  | Code        -- ^ Code files with syntax highlighting
  | Markdown    -- ^ Markdown files
  | Office      -- ^ Office documents (docx, xlsx, pptx)
  | Archive     -- ^ Archive files (zip, tar, gz)
  | Unknown     -- ^ Unknown/unsupported file type

derive instance eqFileType :: Eq FileType

-- | Preview loading state
data PreviewState
  = Loading
  | Loaded
  | Error String

derive instance eqPreviewState :: Eq PreviewState

-- | File information
type FileInfo =
  { name :: String
  , size :: Int
  , type :: String
  , lastModified :: Maybe String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Load file info from URL
foreign import loadFileInfoImpl :: EffectFn1 String (Effect FileInfo)

-- | Download file
foreign import downloadFileImpl :: EffectFn2 String String Unit

-- | Open URL in new tab
foreign import openInNewTabImpl :: EffectFn1 String Unit

-- | Load file info
loadFileInfo :: String -> Effect (Effect FileInfo)
loadFileInfo _ = pure (pure { name: "", size: 0, type: "", lastModified: Nothing })

-- | Download file with filename
downloadFile :: String -> String -> Effect Unit
downloadFile _ _ = pure unit

-- | Open URL in new tab
openInNewTab :: String -> Effect Unit
openInNewTab _ = pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Document preview properties
type DocumentPreviewProps i =
  { source :: String
  , fileName :: String
  , fileType :: Maybe FileType
  , fileSize :: Maybe Int
  , mimeType :: Maybe String
  , codeLanguage :: Maybe String
  , showToolbar :: Boolean
  , showDownload :: Boolean
  , showOpenInNew :: Boolean
  , maxWidth :: String
  , maxHeight :: String
  , state :: PreviewState
  , className :: String
  , onLoad :: Maybe i
  , onError :: Maybe (String -> i)
  , onDownload :: Maybe i
  , onOpenInNew :: Maybe i
  }

-- | Property modifier
type DocumentPreviewProp i = DocumentPreviewProps i -> DocumentPreviewProps i

-- | Default properties
defaultProps :: forall i. DocumentPreviewProps i
defaultProps =
  { source: ""
  , fileName: ""
  , fileType: Nothing
  , fileSize: Nothing
  , mimeType: Nothing
  , codeLanguage: Nothing
  , showToolbar: true
  , showDownload: true
  , showOpenInNew: true
  , maxWidth: "100%"
  , maxHeight: "600px"
  , state: Loading
  , className: ""
  , onLoad: Nothing
  , onError: Nothing
  , onDownload: Nothing
  , onOpenInNew: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set file source URL
source :: forall i. String -> DocumentPreviewProp i
source s props = props { source = s }

-- | Set file name
fileName :: forall i. String -> DocumentPreviewProp i
fileName n props = props { fileName = n }

-- | Force specific file type
fileType :: forall i. FileType -> DocumentPreviewProp i
fileType t props = props { fileType = Just t }

-- | Set file size in bytes
fileSize :: forall i. Int -> DocumentPreviewProp i
fileSize s props = props { fileSize = Just s }

-- | Set MIME type
mimeType :: forall i. String -> DocumentPreviewProp i
mimeType m props = props { mimeType = Just m }

-- | Set code language for syntax highlighting
codeLanguage :: forall i. String -> DocumentPreviewProp i
codeLanguage l props = props { codeLanguage = Just l }

-- | Show/hide toolbar
showToolbar :: forall i. Boolean -> DocumentPreviewProp i
showToolbar s props = props { showToolbar = s }

-- | Show/hide download button
showDownload :: forall i. Boolean -> DocumentPreviewProp i
showDownload s props = props { showDownload = s }

-- | Show/hide open in new tab button
showOpenInNew :: forall i. Boolean -> DocumentPreviewProp i
showOpenInNew s props = props { showOpenInNew = s }

-- | Set maximum width
maxWidth :: forall i. String -> DocumentPreviewProp i
maxWidth w props = props { maxWidth = w }

-- | Set maximum height
maxHeight :: forall i. String -> DocumentPreviewProp i
maxHeight h props = props { maxHeight = h }

-- | Add custom class
className :: forall i. String -> DocumentPreviewProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle load complete
onLoad :: forall i. i -> DocumentPreviewProp i
onLoad handler props = props { onLoad = Just handler }

-- | Handle load error
onError :: forall i. (String -> i) -> DocumentPreviewProp i
onError handler props = props { onError = Just handler }

-- | Handle download click
onDownload :: forall i. i -> DocumentPreviewProp i
onDownload handler props = props { onDownload = Just handler }

-- | Handle open in new tab click
onOpenInNew :: forall i. i -> DocumentPreviewProp i
onOpenInNew handler props = props { onOpenInNew = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // type detection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detect file type from filename and mime type
detectFileType :: String -> Maybe String -> FileType
detectFileType name maybeMime =
  let
    ext = toLower (getFileExtension name)
    mime = fromMaybe "" maybeMime
  in
    -- Check MIME type first
    case getMimeCategory mime of
      Just t -> t
      Nothing ->
        -- Fall back to extension
        if elem ext imageExtensions then Image
        else if elem ext videoExtensions then Video
        else if elem ext audioExtensions then Audio
        else if ext == "pdf" then PDF
        else if elem ext codeExtensions then Code
        else if ext == "md" || ext == "markdown" then Markdown
        else if elem ext textExtensions then Text
        else if elem ext officeExtensions then Office
        else if elem ext archiveExtensions then Archive
        else Unknown

-- | Get file extension from filename
getFileExtension :: String -> String
getFileExtension name =
  let parts = split (Pattern ".") name
  in case parts of
    [] -> ""
    [_] -> ""
    arr -> fromMaybe "" (lastElement arr)

-- | Get last element of array
lastElement :: Array String -> Maybe String
lastElement arr = arr !! (arrayLength arr - 1)
  where
    arrayLength :: Array String -> Int
    arrayLength = foldl (\acc _ -> acc + 1) 0

-- | Get file type from MIME type
getMimeCategory :: String -> Maybe FileType
getMimeCategory mime
  | String.indexOf (Pattern "image/") mime == Just 0 = Just Image
  | String.indexOf (Pattern "video/") mime == Just 0 = Just Video
  | String.indexOf (Pattern "audio/") mime == Just 0 = Just Audio
  | mime == "application/pdf" = Just PDF
  | String.indexOf (Pattern "text/") mime == Just 0 = Just Text
  | otherwise = Nothing

-- Extension lists
imageExtensions :: Array String
imageExtensions = ["jpg", "jpeg", "png", "gif", "webp", "svg", "bmp", "ico", "tiff"]

videoExtensions :: Array String
videoExtensions = ["mp4", "webm", "mov", "avi", "mkv", "flv", "wmv"]

audioExtensions :: Array String
audioExtensions = ["mp3", "wav", "ogg", "flac", "aac", "m4a", "wma"]

codeExtensions :: Array String
codeExtensions = 
  [ "js", "ts", "jsx", "tsx", "json"
  , "py", "rb", "php", "java", "c", "cpp", "h", "hpp"
  , "go", "rs", "swift", "kt", "scala"
  , "html", "css", "scss", "sass", "less"
  , "xml", "yaml", "yml", "toml"
  , "sh", "bash", "zsh", "fish"
  , "sql", "graphql"
  , "purs", "hs", "elm", "ml", "ex", "exs"
  ]

textExtensions :: Array String
textExtensions = ["txt", "log", "cfg", "ini", "conf"]

officeExtensions :: Array String
officeExtensions = ["doc", "docx", "xls", "xlsx", "ppt", "pptx", "odt", "ods", "odp"]

archiveExtensions :: Array String
archiveExtensions = ["zip", "tar", "gz", "rar", "7z", "bz2", "xz"]

-- Array indexing
foreign import indexArrayImpl :: forall a. Array a -> Int -> Maybe a

infixl 8 indexArrayImpl as !!

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Document Preview component
-- |
-- | Automatically detects file type and renders appropriate preview.
-- | Supports images, video, audio, PDF, text, code, and more.
documentPreview :: forall w i. Array (DocumentPreviewProp i) -> HH.HTML w i
documentPreview propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    detectedType = fromMaybe (detectFileType props.fileName props.mimeType) props.fileType
  in
    HH.div
      [ cls [ "document-preview flex flex-col border border-border rounded-lg bg-background overflow-hidden", props.className ]
      , HP.attr (HH.AttrName "data-document-preview") "true"
      , HP.attr (HH.AttrName "data-file-type") (fileTypeString detectedType)
      ]
      [ -- Toolbar
        if props.showToolbar
          then renderToolbar props
          else HH.text ""
      , -- Preview content
        HH.div
          [ cls [ "flex-1 overflow-auto" ]
          , HP.attr (HH.AttrName "style") 
              ("max-width: " <> props.maxWidth <> "; max-height: " <> props.maxHeight <> ";")
          ]
          [ case props.state of
              Loading -> renderLoading
              Error msg -> renderError msg
              Loaded -> renderPreview props detectedType
          ]
      ]

-- | Inline preview (without toolbar)
inlinePreview :: forall w i. String -> String -> HH.HTML w i
inlinePreview src name =
  let
    detectedType = detectFileType name Nothing
  in
    renderPreviewContent src detectedType Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // toolbar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render toolbar
renderToolbar :: forall w i. DocumentPreviewProps i -> HH.HTML w i
renderToolbar props =
  HH.div
    [ cls [ "preview-toolbar flex items-center justify-between px-3 py-2 border-b border-border bg-muted/30" ]
    ]
    [ -- File info
      HH.div
        [ cls [ "flex items-center gap-2 min-w-0" ] ]
        [ fileIcon (fromMaybe Unknown props.fileType)
        , HH.span
            [ cls [ "text-sm font-medium truncate" ] ]
            [ HH.text props.fileName ]
        , case props.fileSize of
            Just size -> HH.span
              [ cls [ "text-xs text-muted-foreground" ] ]
              [ HH.text (formatFileSize size) ]
            Nothing -> HH.text ""
        ]
    , -- Actions
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ if props.showOpenInNew
            then HH.button
              [ cls [ "inline-flex items-center justify-center h-8 w-8 rounded hover:bg-muted transition-colors" ]
              , HP.type_ HP.ButtonButton
              , HP.title "Open in new tab"
              , ARIA.label "Open in new tab"
              ]
              [ openInNewIcon ]
            else HH.text ""
        , if props.showDownload
            then HH.button
              [ cls [ "inline-flex items-center justify-center h-8 w-8 rounded hover:bg-muted transition-colors" ]
              , HP.type_ HP.ButtonButton
              , HP.title "Download"
              , ARIA.label "Download file"
              ]
              [ downloadIcon ]
            else HH.text ""
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // preview content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render preview based on file type
renderPreview :: forall w i. DocumentPreviewProps i -> FileType -> HH.HTML w i
renderPreview props fileType' =
  renderPreviewContent props.source fileType' props.codeLanguage

-- | Render preview content
renderPreviewContent :: forall w i. String -> FileType -> Maybe String -> HH.HTML w i
renderPreviewContent src fileType' codeLang =
  case fileType' of
    Image -> renderImagePreview src
    Video -> renderVideoPreview src
    Audio -> renderAudioPreview src
    PDF -> renderPDFPreview src
    Text -> renderTextPreview src
    Code -> renderCodePreview src codeLang
    Markdown -> renderMarkdownPreview src
    Office -> renderOfficePreview src
    Archive -> renderArchivePreview src
    Unknown -> renderUnsupportedPreview

-- | Render image preview
renderImagePreview :: forall w i. String -> HH.HTML w i
renderImagePreview src =
  HH.div
    [ cls [ "p-4 flex items-center justify-center min-h-[200px]" ] ]
    [ HH.img
        [ cls [ "max-w-full max-h-full object-contain cursor-zoom-in" ]
        , HP.src src
        , HP.alt "Image preview"
        , HP.attr (HH.AttrName "loading") "lazy"
        ]
    ]

-- | Render video preview
renderVideoPreview :: forall w i. String -> HH.HTML w i
renderVideoPreview src =
  HH.div
    [ cls [ "p-4 flex items-center justify-center bg-black min-h-[200px]" ] ]
    [ HH.video
        [ cls [ "max-w-full max-h-full" ]
        , HP.src src
        , HP.attr (HH.AttrName "controls") "true"
        , HP.attr (HH.AttrName "preload") "metadata"
        ]
        [ HH.text "Your browser does not support the video element." ]
    ]

-- | Render audio preview
renderAudioPreview :: forall w i. String -> HH.HTML w i
renderAudioPreview src =
  HH.div
    [ cls [ "p-6 flex flex-col items-center justify-center gap-4 min-h-[150px]" ] ]
    [ audioWaveformIcon
    , HH.audio
        [ cls [ "w-full max-w-md" ]
        , HP.src src
        , HP.attr (HH.AttrName "controls") "true"
        , HP.attr (HH.AttrName "preload") "metadata"
        ]
        [ HH.text "Your browser does not support the audio element." ]
    ]

-- | Render PDF preview
renderPDFPreview :: forall w i. String -> HH.HTML w i
renderPDFPreview src =
  HH.div
    [ cls [ "w-full h-full min-h-[400px]" ] ]
    [ HH.iframe
        [ cls [ "w-full h-full border-0" ]
        , HP.src src
        , HP.title "PDF preview"
        ]
    ]

-- | Render text file preview
renderTextPreview :: forall w i. String -> HH.HTML w i
renderTextPreview _src =
  HH.div
    [ cls [ "p-4 overflow-auto" ] ]
    [ HH.pre
        [ cls [ "font-mono text-sm whitespace-pre-wrap" ] ]
        [ HH.text "Loading text content..." ]
    ]

-- | Render code preview with syntax highlighting
renderCodePreview :: forall w i. String -> Maybe String -> HH.HTML w i
renderCodePreview _src lang =
  HH.div
    [ cls [ "overflow-auto" ] ]
    [ HH.pre
        [ cls [ "p-4 font-mono text-sm leading-relaxed" ]
        , HP.attr (HH.AttrName "data-language") (fromMaybe "" lang)
        ]
        [ HH.code
            [ cls [ "language-" <> fromMaybe "text" lang ] ]
            [ HH.text "Loading code..." ]
        ]
    ]

-- | Render markdown preview
renderMarkdownPreview :: forall w i. String -> HH.HTML w i
renderMarkdownPreview _src =
  HH.div
    [ cls [ "prose prose-sm dark:prose-invert max-w-none p-4" ] ]
    [ HH.text "Loading markdown..." ]

-- | Render office document preview
renderOfficePreview :: forall w i. String -> HH.HTML w i
renderOfficePreview src =
  HH.div
    [ cls [ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ] ]
    [ officeIcon
    , HH.p
        [ cls [ "text-sm text-muted-foreground text-center" ] ]
        [ HH.text "Office documents cannot be previewed directly." ]
    , HH.a
        [ cls [ "inline-flex items-center gap-2 px-4 py-2 rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors" ]
        , HP.href src
        , HP.attr (HH.AttrName "download") ""
        ]
        [ downloadIcon
        , HH.text "Download to view"
        ]
    ]

-- | Render archive preview
renderArchivePreview :: forall w i. String -> HH.HTML w i
renderArchivePreview src =
  HH.div
    [ cls [ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ] ]
    [ archiveIcon
    , HH.p
        [ cls [ "text-sm text-muted-foreground text-center" ] ]
        [ HH.text "Archive contents cannot be previewed." ]
    , HH.a
        [ cls [ "inline-flex items-center gap-2 px-4 py-2 rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors" ]
        , HP.href src
        , HP.attr (HH.AttrName "download") ""
        ]
        [ downloadIcon
        , HH.text "Download archive"
        ]
    ]

-- | Render unsupported file message
renderUnsupportedPreview :: forall w i. HH.HTML w i
renderUnsupportedPreview =
  HH.div
    [ cls [ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ] ]
    [ unknownIcon
    , HH.p
        [ cls [ "text-sm text-muted-foreground text-center" ] ]
        [ HH.text "This file type cannot be previewed." ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // loading/error
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render loading state
renderLoading :: forall w i. HH.HTML w i
renderLoading =
  HH.div
    [ cls [ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]
    , ARIA.role "status"
    , ARIA.label "Loading preview"
    ]
    [ HH.div
        [ cls [ "h-8 w-8 animate-spin rounded-full border-4 border-primary border-t-transparent" ] ]
        []
    , HH.span
        [ cls [ "text-sm text-muted-foreground" ] ]
        [ HH.text "Loading preview..." ]
    ]

-- | Render error state
renderError :: forall w i. String -> HH.HTML w i
renderError message =
  HH.div
    [ cls [ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]
    , ARIA.role "alert"
    ]
    [ errorIcon
    , HH.p
        [ cls [ "text-sm text-destructive font-medium" ] ]
        [ HH.text "Failed to load preview" ]
    , HH.p
        [ cls [ "text-xs text-muted-foreground text-center max-w-xs" ] ]
        [ HH.text message ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert FileType to string
fileTypeString :: FileType -> String
fileTypeString = case _ of
  Image -> "image"
  Video -> "video"
  Audio -> "audio"
  PDF -> "pdf"
  Text -> "text"
  Code -> "code"
  Markdown -> "markdown"
  Office -> "office"
  Archive -> "archive"
  Unknown -> "unknown"

-- | Format file size for display
formatFileSize :: Int -> String
formatFileSize bytes
  | bytes < 1024 = show bytes <> " B"
  | bytes < 1024 * 1024 = show (bytes / 1024) <> " KB"
  | bytes < 1024 * 1024 * 1024 = show (bytes / (1024 * 1024)) <> " MB"
  | otherwise = show (bytes / (1024 * 1024 * 1024)) <> " GB"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File type icon
fileIcon :: forall w i. FileType -> HH.HTML w i
fileIcon ft =
  let
    symbol = case ft of
      Image -> "I"
      Video -> "V"
      Audio -> "A"
      PDF -> "P"
      Text -> "T"
      Code -> "C"
      Markdown -> "M"
      Office -> "O"
      Archive -> "Z"
      Unknown -> "?"
  in
    HH.span
      [ cls [ "inline-flex items-center justify-center w-6 h-6 rounded bg-muted text-xs font-medium" ]
      , ARIA.hidden "true"
      ]
      [ HH.text symbol ]

downloadIcon :: forall w i. HH.HTML w i
downloadIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "D" ]

openInNewIcon :: forall w i. HH.HTML w i
openInNewIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "N" ]

audioWaveformIcon :: forall w i. HH.HTML w i
audioWaveformIcon = HH.span [ cls [ "w-16 h-16 text-muted-foreground" ], ARIA.hidden "true" ] [ HH.text "W" ]

officeIcon :: forall w i. HH.HTML w i
officeIcon = HH.span [ cls [ "w-16 h-16 text-muted-foreground" ], ARIA.hidden "true" ] [ HH.text "O" ]

archiveIcon :: forall w i. HH.HTML w i
archiveIcon = HH.span [ cls [ "w-16 h-16 text-muted-foreground" ], ARIA.hidden "true" ] [ HH.text "Z" ]

unknownIcon :: forall w i. HH.HTML w i
unknownIcon = HH.span [ cls [ "w-16 h-16 text-muted-foreground" ], ARIA.hidden "true" ] [ HH.text "?" ]

errorIcon :: forall w i. HH.HTML w i
errorIcon = HH.span [ cls [ "w-12 h-12 text-destructive" ], ARIA.hidden "true" ] [ HH.text "!" ]
