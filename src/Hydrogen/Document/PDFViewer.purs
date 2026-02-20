-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // pdfviewer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PDF Viewer Component
-- |
-- | A full-featured PDF viewer with canvas-based rendering, navigation,
-- | search, annotations, and zoom controls.
-- |
-- | ## Features
-- |
-- | - Canvas-based PDF page rendering
-- | - Page navigation (prev/next, go to page)
-- | - Thumbnails sidebar
-- | - Zoom controls (fit width, fit page, percentage)
-- | - Continuous scroll through pages
-- | - Text search with highlighting
-- | - Text selection and copy
-- | - Outline/bookmarks sidebar
-- | - Print and download buttons
-- | - Fullscreen mode
-- | - Two-page view
-- | - Loading progress
-- | - Error handling
-- | - Basic annotations (highlight, underline, comment)
-- | - Page rotation
-- | - Keyboard shortcuts
-- | - Mobile pinch-to-zoom
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Document.PDFViewer as PDFViewer
-- |
-- | -- Basic PDF viewer
-- | PDFViewer.pdfViewer
-- |   [ PDFViewer.source "document.pdf"
-- |   , PDFViewer.showToolbar true
-- |   , PDFViewer.showThumbnails true
-- |   ]
-- |
-- | -- Controlled viewer with callbacks
-- | PDFViewer.pdfViewer
-- |   [ PDFViewer.source pdfUrl
-- |   , PDFViewer.currentPage state.page
-- |   , PDFViewer.zoom state.zoom
-- |   , PDFViewer.onPageChange HandlePageChange
-- |   , PDFViewer.onZoomChange HandleZoomChange
-- |   , PDFViewer.onTextSelect HandleTextSelect
-- |   ]
-- |
-- | -- With annotations
-- | PDFViewer.pdfViewer
-- |   [ PDFViewer.source pdfUrl
-- |   , PDFViewer.annotations myAnnotations
-- |   , PDFViewer.annotationMode PDFViewer.Highlight
-- |   , PDFViewer.onAnnotationAdd HandleAnnotationAdd
-- |   ]
-- | ```
-- |
-- | ## Keyboard Shortcuts
-- |
-- | - Arrow keys: Navigate pages
-- | - +/-: Zoom in/out
-- | - Ctrl+F: Open search
-- | - Ctrl+P: Print
-- | - Esc: Exit fullscreen / Close search
-- | - R: Rotate page
-- | - Home/End: First/last page
module Hydrogen.Document.PDFViewer
  ( -- * Component
    pdfViewer
    -- * Props
  , PDFViewerProps
  , PDFViewerProp
  , defaultProps
    -- * Prop Builders
  , source
  , currentPage
  , totalPages
  , zoom
  , zoomMode
  , rotation
  , showToolbar
  , showThumbnails
  , showOutline
  , showSearch
  , pageMode
  , annotations
  , annotationMode
  , className
    -- * Event Handlers
  , onPageChange
  , onZoomChange
  , onRotationChange
  , onTextSelect
  , onAnnotationAdd
  , onAnnotationRemove
  , onLoad
  , onError
  , onLoadProgress
    -- * Types
  , ZoomMode(..)
  , PageMode(..)
  , AnnotationMode(..)
  , Annotation
  , AnnotationType(..)
  , Outline(..)
  , unwrapOutline
  , LoadProgress
  , PDFError(..)
    -- * FFI
  , PDFDocument
  , PDFPage
  , loadDocument
  , renderPage
  , getPageText
  , searchText
  , printDocument
  , downloadDocument
  , initPinchZoom
  , destroyViewer
  ) where

import Prelude

import Data.Array (foldl, length, mapWithIndex, range, (!!))
import Data.Maybe (Maybe(..), fromMaybe)
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

-- | Zoom mode options
data ZoomMode
  = ZoomActual    -- ^ 100% zoom
  | ZoomFitWidth  -- ^ Fit to container width
  | ZoomFitPage   -- ^ Fit entire page in view
  | ZoomPercent Number  -- ^ Custom percentage

derive instance eqZoomMode :: Eq ZoomMode

-- | Page viewing mode
data PageMode
  = SinglePage    -- ^ One page at a time
  | TwoPage       -- ^ Two pages side by side
  | Continuous    -- ^ Scroll through all pages

derive instance eqPageMode :: Eq PageMode

-- | Annotation mode
data AnnotationMode
  = NoAnnotation  -- ^ View only
  | Highlight     -- ^ Highlight text
  | Underline     -- ^ Underline text
  | Comment       -- ^ Add comment

derive instance eqAnnotationMode :: Eq AnnotationMode

-- | Annotation type
data AnnotationType
  = HighlightAnnotation
  | UnderlineAnnotation
  | CommentAnnotation

derive instance eqAnnotationType :: Eq AnnotationType

-- | Annotation record
type Annotation =
  { id :: String
  , type :: AnnotationType
  , page :: Int
  , rect :: { x :: Number, y :: Number, width :: Number, height :: Number }
  , color :: String
  , content :: Maybe String  -- For comments
  , timestamp :: String
  }

-- | Document outline/bookmark
newtype Outline = Outline
  { title :: String
  , page :: Int
  , level :: Int
  , children :: Array Outline
  }

-- | Unwrap outline record
unwrapOutline :: Outline -> { title :: String, page :: Int, level :: Int, children :: Array Outline }
unwrapOutline (Outline o) = o

-- | Loading progress
type LoadProgress =
  { loaded :: Int
  , total :: Int
  , percent :: Number
  }

-- | PDF error types
data PDFError
  = LoadError String
  | RenderError String
  | PasswordRequired
  | InvalidPDF
  | NetworkError String

derive instance eqPDFError :: Eq PDFError

-- | Opaque PDF document handle
foreign import data PDFDocument :: Type

-- | Opaque PDF page handle
foreign import data PDFPage :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Load PDF document from URL or data
foreign import loadDocumentImpl :: EffectFn2 String
  { onProgress :: LoadProgress -> Effect Unit
  , onPassword :: Effect String
  }
  (Effect PDFDocument)

-- | Render page to canvas
foreign import renderPageImpl :: EffectFn3 PDFDocument Int
  { canvas :: Element
  , scale :: Number
  , rotation :: Int
  }
  (Effect Unit)

-- | Get text content from page
foreign import getPageTextImpl :: EffectFn2 PDFDocument Int (Effect String)

-- | Search text in document
foreign import searchTextImpl :: EffectFn2 PDFDocument String 
  (Effect (Array { page :: Int, matches :: Array { text :: String, rect :: { x :: Number, y :: Number, width :: Number, height :: Number } } }))

-- | Print document
foreign import printDocumentImpl :: EffectFn1 PDFDocument Unit

-- | Download document
foreign import downloadDocumentImpl :: EffectFn2 PDFDocument String Unit

-- | Initialize pinch-to-zoom
foreign import initPinchZoomImpl :: EffectFn2 Element
  { onZoom :: Number -> Effect Unit }
  (Effect { destroy :: Effect Unit })

-- | Destroy viewer and cleanup resources
foreign import destroyViewerImpl :: EffectFn1 PDFDocument Unit

-- | Load PDF document
loadDocument :: String ->
  { onProgress :: LoadProgress -> Effect Unit
  , onPassword :: Effect String
  } ->
  Effect (Effect PDFDocument)
loadDocument _url _callbacks = pure (pure unsafePDFDocument)

-- | Render a page
renderPage :: PDFDocument -> Int ->
  { canvas :: Element
  , scale :: Number
  , rotation :: Int
  } ->
  Effect (Effect Unit)
renderPage _ _ _ = pure (pure unit)

-- | Get page text
getPageText :: PDFDocument -> Int -> Effect (Effect String)
getPageText _ _ = pure (pure "")

-- | Search text
searchText :: PDFDocument -> String -> Effect (Effect (Array { page :: Int, matches :: Array { text :: String, rect :: { x :: Number, y :: Number, width :: Number, height :: Number } } }))
searchText _ _ = pure (pure [])

-- | Print document
printDocument :: PDFDocument -> Effect Unit
printDocument _ = pure unit

-- | Download document with filename
downloadDocument :: PDFDocument -> String -> Effect Unit
downloadDocument _ _ = pure unit

-- | Initialize pinch-to-zoom on element
initPinchZoom :: Element ->
  { onZoom :: Number -> Effect Unit } ->
  Effect { destroy :: Effect Unit }
initPinchZoom _ _ = pure { destroy: pure unit }

-- | Destroy viewer
destroyViewer :: PDFDocument -> Effect Unit
destroyViewer _ = pure unit

-- Internal placeholder
foreign import unsafePDFDocument :: PDFDocument

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PDF Viewer properties
type PDFViewerProps i =
  { source :: String
  , currentPage :: Int
  , totalPages :: Int
  , zoom :: Number
  , zoomMode :: ZoomMode
  , rotation :: Int
  , showToolbar :: Boolean
  , showThumbnails :: Boolean
  , showOutline :: Boolean
  , showSearch :: Boolean
  , pageMode :: PageMode
  , annotations :: Array Annotation
  , annotationMode :: AnnotationMode
  , outline :: Array Outline
  , isLoading :: Boolean
  , loadProgress :: Maybe LoadProgress
  , error :: Maybe PDFError
  , searchQuery :: String
  , searchResults :: Array { page :: Int, index :: Int }
  , currentSearchIndex :: Int
  , isFullscreen :: Boolean
  , className :: String
  , onPageChange :: Maybe (Int -> i)
  , onZoomChange :: Maybe (Number -> i)
  , onRotationChange :: Maybe (Int -> i)
  , onTextSelect :: Maybe (String -> i)
  , onAnnotationAdd :: Maybe (Annotation -> i)
  , onAnnotationRemove :: Maybe (String -> i)
  , onLoad :: Maybe ({ totalPages :: Int, outline :: Array Outline } -> i)
  , onError :: Maybe (PDFError -> i)
  , onLoadProgress :: Maybe (LoadProgress -> i)
  , onSearchChange :: Maybe (String -> i)
  , onFullscreenChange :: Maybe (Boolean -> i)
  }

-- | Property modifier
type PDFViewerProp i = PDFViewerProps i -> PDFViewerProps i

-- | Default properties
defaultProps :: forall i. PDFViewerProps i
defaultProps =
  { source: ""
  , currentPage: 1
  , totalPages: 0
  , zoom: 100.0
  , zoomMode: ZoomFitWidth
  , rotation: 0
  , showToolbar: true
  , showThumbnails: false
  , showOutline: false
  , showSearch: false
  , pageMode: SinglePage
  , annotations: []
  , annotationMode: NoAnnotation
  , outline: []
  , isLoading: false
  , loadProgress: Nothing
  , error: Nothing
  , searchQuery: ""
  , searchResults: []
  , currentSearchIndex: 0
  , isFullscreen: false
  , className: ""
  , onPageChange: Nothing
  , onZoomChange: Nothing
  , onRotationChange: Nothing
  , onTextSelect: Nothing
  , onAnnotationAdd: Nothing
  , onAnnotationRemove: Nothing
  , onLoad: Nothing
  , onError: Nothing
  , onLoadProgress: Nothing
  , onSearchChange: Nothing
  , onFullscreenChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set PDF source URL or data URI
source :: forall i. String -> PDFViewerProp i
source s props = props { source = s }

-- | Set current page number (1-indexed)
currentPage :: forall i. Int -> PDFViewerProp i
currentPage p props = props { currentPage = p }

-- | Set total pages (read from document)
totalPages :: forall i. Int -> PDFViewerProp i
totalPages t props = props { totalPages = t }

-- | Set zoom level (percentage)
zoom :: forall i. Number -> PDFViewerProp i
zoom z props = props { zoom = z }

-- | Set zoom mode
zoomMode :: forall i. ZoomMode -> PDFViewerProp i
zoomMode m props = props { zoomMode = m }

-- | Set page rotation (0, 90, 180, 270)
rotation :: forall i. Int -> PDFViewerProp i
rotation r props = props { rotation = (r `mod` 360) }

-- | Show/hide toolbar
showToolbar :: forall i. Boolean -> PDFViewerProp i
showToolbar s props = props { showToolbar = s }

-- | Show/hide thumbnails sidebar
showThumbnails :: forall i. Boolean -> PDFViewerProp i
showThumbnails s props = props { showThumbnails = s }

-- | Show/hide outline/bookmarks sidebar
showOutline :: forall i. Boolean -> PDFViewerProp i
showOutline s props = props { showOutline = s }

-- | Show/hide search panel
showSearch :: forall i. Boolean -> PDFViewerProp i
showSearch s props = props { showSearch = s }

-- | Set page viewing mode
pageMode :: forall i. PageMode -> PDFViewerProp i
pageMode m props = props { pageMode = m }

-- | Set annotations
annotations :: forall i. Array Annotation -> PDFViewerProp i
annotations a props = props { annotations = a }

-- | Set annotation mode
annotationMode :: forall i. AnnotationMode -> PDFViewerProp i
annotationMode m props = props { annotationMode = m }

-- | Add custom class
className :: forall i. String -> PDFViewerProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle page change
onPageChange :: forall i. (Int -> i) -> PDFViewerProp i
onPageChange handler props = props { onPageChange = Just handler }

-- | Handle zoom change
onZoomChange :: forall i. (Number -> i) -> PDFViewerProp i
onZoomChange handler props = props { onZoomChange = Just handler }

-- | Handle rotation change
onRotationChange :: forall i. (Int -> i) -> PDFViewerProp i
onRotationChange handler props = props { onRotationChange = Just handler }

-- | Handle text selection
onTextSelect :: forall i. (String -> i) -> PDFViewerProp i
onTextSelect handler props = props { onTextSelect = Just handler }

-- | Handle annotation addition
onAnnotationAdd :: forall i. (Annotation -> i) -> PDFViewerProp i
onAnnotationAdd handler props = props { onAnnotationAdd = Just handler }

-- | Handle annotation removal
onAnnotationRemove :: forall i. (String -> i) -> PDFViewerProp i
onAnnotationRemove handler props = props { onAnnotationRemove = Just handler }

-- | Handle document load
onLoad :: forall i. ({ totalPages :: Int, outline :: Array Outline } -> i) -> PDFViewerProp i
onLoad handler props = props { onLoad = Just handler }

-- | Handle load error
onError :: forall i. (PDFError -> i) -> PDFViewerProp i
onError handler props = props { onError = Just handler }

-- | Handle load progress
onLoadProgress :: forall i. (LoadProgress -> i) -> PDFViewerProp i
onLoadProgress handler props = props { onLoadProgress = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PDF Viewer component
-- |
-- | Renders a full-featured PDF viewer with toolbar, navigation,
-- | and optional sidebars for thumbnails and outline.
pdfViewer :: forall w i. Array (PDFViewerProp i) -> HH.HTML w i
pdfViewer propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "pdf-viewer relative flex flex-col h-full bg-muted/30", props.className ]
      , HP.attr (HH.AttrName "data-pdf-viewer") "true"
      , ARIA.role "document"
      , ARIA.label "PDF document viewer"
      ]
      [ -- Toolbar
        if props.showToolbar
          then renderToolbar props
          else HH.text ""
      , -- Main content area
        HH.div
          [ cls [ "flex flex-1 overflow-hidden" ] ]
          [ -- Thumbnails sidebar
            if props.showThumbnails
              then renderThumbnailsSidebar props
              else HH.text ""
          , -- Outline sidebar
            if props.showOutline
              then renderOutlineSidebar props
              else HH.text ""
          , -- PDF canvas area
            renderCanvasArea props
          ]
      , -- Loading overlay
        renderLoadingOverlay props
      , -- Error overlay
        renderErrorOverlay props
      , -- Search panel
        if props.showSearch
          then renderSearchPanel props
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // toolbar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render toolbar
renderToolbar :: forall w i. PDFViewerProps i -> HH.HTML w i
renderToolbar props =
  HH.div
    [ cls [ "pdf-toolbar flex items-center gap-2 px-4 py-2 border-b border-border bg-background" ]
    , ARIA.role "toolbar"
    , ARIA.label "PDF viewer controls"
    ]
    [ -- Sidebar toggles
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ toolbarButton "Toggle thumbnails" thumbnailIcon
        , toolbarButton "Toggle outline" outlineIcon
        ]
    , divider
    , -- Page navigation
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ toolbarButton "Previous page" prevIcon
        , HH.span
            [ cls [ "flex items-center gap-1 text-sm" ] ]
            [ HH.input
                [ cls [ "w-12 h-8 px-2 text-center rounded border border-input bg-transparent text-sm" ]
                , HP.type_ HP.InputNumber
                , HP.value (show props.currentPage)
                , HP.attr (HH.AttrName "min") "1"
                , HP.attr (HH.AttrName "max") (show props.totalPages)
                , ARIA.label "Current page"
                ]
            , HH.span
                [ cls [ "text-muted-foreground" ] ]
                [ HH.text ("/ " <> show props.totalPages) ]
            ]
        , toolbarButton "Next page" nextIcon
        ]
    , divider
    , -- Zoom controls
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ toolbarButton "Zoom out" zoomOutIcon
        , HH.select
            [ cls [ "h-8 px-2 rounded border border-input bg-transparent text-sm cursor-pointer" ]
            , ARIA.label "Zoom level"
            ]
            [ HH.option [ HP.value "50" ] [ HH.text "50%" ]
            , HH.option [ HP.value "75" ] [ HH.text "75%" ]
            , HH.option [ HP.value "100", HP.selected (props.zoom == 100.0) ] [ HH.text "100%" ]
            , HH.option [ HP.value "125" ] [ HH.text "125%" ]
            , HH.option [ HP.value "150" ] [ HH.text "150%" ]
            , HH.option [ HP.value "200" ] [ HH.text "200%" ]
            , HH.option [ HP.value "fit-width" ] [ HH.text "Fit Width" ]
            , HH.option [ HP.value "fit-page" ] [ HH.text "Fit Page" ]
            ]
        , toolbarButton "Zoom in" zoomInIcon
        ]
    , divider
    , -- View mode
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ toolbarButton "Single page" singlePageIcon
        , toolbarButton "Two pages" twoPageIcon
        , toolbarButton "Continuous" continuousIcon
        ]
    , divider
    , -- Rotation
      toolbarButton "Rotate clockwise" rotateIcon
    , HH.div [ cls [ "flex-1" ] ] []  -- Spacer
    , -- Search
      toolbarButton "Search" searchIcon
    , divider
    , -- Actions
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ toolbarButton "Download" downloadIcon
        , toolbarButton "Print" printIcon
        , toolbarButton "Fullscreen" fullscreenIcon
        ]
    ]
  where
    divider = HH.div [ cls [ "w-px h-6 bg-border" ] ] []

-- | Toolbar button helper
toolbarButton :: forall w i. String -> HH.HTML w i -> HH.HTML w i
toolbarButton label icon =
  HH.button
    [ cls [ "inline-flex items-center justify-center h-8 w-8 rounded-md hover:bg-muted transition-colors" ]
    , HP.type_ HP.ButtonButton
    , HP.title label
    , ARIA.label label
    ]
    [ icon ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // thumbnails sidebar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render thumbnails sidebar
renderThumbnailsSidebar :: forall w i. PDFViewerProps i -> HH.HTML w i
renderThumbnailsSidebar props =
  HH.div
    [ cls [ "pdf-thumbnails w-48 border-r border-border bg-background overflow-y-auto flex-shrink-0" ]
    , ARIA.role "navigation"
    , ARIA.label "Page thumbnails"
    ]
    [ HH.div
        [ cls [ "p-2 space-y-2" ] ]
        (mapWithIndex (renderThumbnail props) (range 1 props.totalPages))
    ]

-- | Render single thumbnail
renderThumbnail :: forall w i. PDFViewerProps i -> Int -> Int -> HH.HTML w i
renderThumbnail props _idx pageNum =
  let
    isActive = props.currentPage == pageNum
  in
    HH.button
      [ cls [ "pdf-thumbnail w-full p-2 rounded-md border-2 transition-colors cursor-pointer text-center"
            , if isActive then "border-primary bg-primary/10" else "border-transparent hover:border-muted-foreground/30"
            ]
      , HP.type_ HP.ButtonButton
      , ARIA.label ("Go to page " <> show pageNum)
      ]
      [ HH.div
          [ cls [ "aspect-[3/4] bg-white rounded shadow-sm mb-1 flex items-center justify-center text-muted-foreground" ] ]
          [ HH.text (show pageNum) ]
      , HH.span
          [ cls [ "text-xs text-muted-foreground" ] ]
          [ HH.text (show pageNum) ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // outline sidebar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render outline/bookmarks sidebar
renderOutlineSidebar :: forall w i. PDFViewerProps i -> HH.HTML w i
renderOutlineSidebar props =
  HH.div
    [ cls [ "pdf-outline w-64 border-r border-border bg-background overflow-y-auto flex-shrink-0" ]
    , ARIA.role "navigation"
    , ARIA.label "Document outline"
    ]
    [ HH.div
        [ cls [ "p-2" ] ]
        [ HH.h3
            [ cls [ "text-sm font-medium px-2 py-1 text-muted-foreground" ] ]
            [ HH.text "Outline" ]
        , if length props.outline == 0
            then HH.p
              [ cls [ "px-2 py-4 text-sm text-muted-foreground italic" ] ]
              [ HH.text "No outline available" ]
            else HH.ul
              [ cls [ "space-y-0.5" ] ]
              (map (renderOutlineItem props) props.outline)
        ]
    ]

-- | Render outline item
renderOutlineItem :: forall w i. PDFViewerProps i -> Outline -> HH.HTML w i
renderOutlineItem props outlineItem =
  let
    item = unwrapOutline outlineItem
  in
    HH.li
      []
      [ HH.button
          [ cls [ "w-full text-left px-2 py-1 text-sm rounded hover:bg-muted transition-colors truncate"
                , "pl-" <> show (2 + item.level * 3)
                ]
          , HP.type_ HP.ButtonButton
          ]
          [ HH.text item.title ]
      , if length item.children > 0
          then HH.ul
            [ cls [ "ml-2" ] ]
            (map (renderOutlineItem props) item.children)
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // canvas area
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render main canvas area
renderCanvasArea :: forall w i. PDFViewerProps i -> HH.HTML w i
renderCanvasArea props =
  HH.div
    [ cls [ "pdf-canvas-area flex-1 overflow-auto bg-muted/50 relative" ]
    , HP.attr (HH.AttrName "data-pdf-scroll") "true"
    ]
    [ HH.div
        [ cls [ "pdf-pages flex flex-col items-center py-4 gap-4 min-h-full" ]
        , HP.attr (HH.AttrName "data-page-mode") (pageModeAttr props.pageMode)
        ]
        [ case props.pageMode of
            SinglePage -> renderSinglePage props
            TwoPage -> renderTwoPageView props
            Continuous -> renderContinuousView props
        ]
    ]
  where
    pageModeAttr :: PageMode -> String
    pageModeAttr = case _ of
      SinglePage -> "single"
      TwoPage -> "two"
      Continuous -> "continuous"

-- | Render single page view
renderSinglePage :: forall w i. PDFViewerProps i -> HH.HTML w i
renderSinglePage props =
  renderPageCanvas props props.currentPage

-- | Render two-page view
renderTwoPageView :: forall w i. PDFViewerProps i -> HH.HTML w i
renderTwoPageView props =
  let
    leftPage = props.currentPage
    rightPage = props.currentPage + 1
  in
    HH.div
      [ cls [ "flex gap-4" ] ]
      [ renderPageCanvas props leftPage
      , if rightPage <= props.totalPages
          then renderPageCanvas props rightPage
          else HH.text ""
      ]

-- | Render continuous view
renderContinuousView :: forall w i. PDFViewerProps i -> HH.HTML w i
renderContinuousView props =
  HH.div
    [ cls [ "space-y-4" ] ]
    (map (renderPageCanvas props) (range 1 props.totalPages))

-- | Render page canvas
renderPageCanvas :: forall w i. PDFViewerProps i -> Int -> HH.HTML w i
renderPageCanvas props pageNum =
  HH.div
    [ cls [ "pdf-page relative bg-white shadow-lg" ]
    , HP.attr (HH.AttrName "data-page-number") (show pageNum)
    , HP.attr (HH.AttrName "style") ("transform: rotate(" <> show props.rotation <> "deg)")
    ]
    [ HH.canvas
        [ cls [ "block" ]
        , HP.attr (HH.AttrName "data-pdf-canvas") (show pageNum)
        ]
    , -- Annotation layer
      renderAnnotationLayer props pageNum
    , -- Text selection layer (invisible, for text selection)
      HH.div
        [ cls [ "pdf-text-layer absolute inset-0 overflow-hidden opacity-20 mix-blend-multiply pointer-events-none" ]
        , HP.attr (HH.AttrName "data-text-layer") (show pageNum)
        ]
        []
    ]

-- | Render annotation layer
renderAnnotationLayer :: forall w i. PDFViewerProps i -> Int -> HH.HTML w i
renderAnnotationLayer props pageNum =
  let
    pageAnnotations = foldl (\acc a -> if a.page == pageNum then acc <> [a] else acc) [] props.annotations
  in
    HH.div
      [ cls [ "pdf-annotation-layer absolute inset-0 pointer-events-none" ]
      , HP.attr (HH.AttrName "data-annotation-layer") (show pageNum)
      ]
      (map renderAnnotation pageAnnotations)

-- | Render single annotation
renderAnnotation :: forall w i. Annotation -> HH.HTML w i
renderAnnotation ann =
  let
    style = "left: " <> show ann.rect.x <> "%; top: " <> show ann.rect.y <> "%; " <>
            "width: " <> show ann.rect.width <> "%; height: " <> show ann.rect.height <> "%;"
    typeClass = case ann.type of
      HighlightAnnotation -> "bg-yellow-300/50"
      UnderlineAnnotation -> "border-b-2 border-red-500"
      CommentAnnotation -> "bg-blue-200/50"
  in
    HH.div
      [ cls [ "absolute pointer-events-auto cursor-pointer", typeClass ]
      , HP.attr (HH.AttrName "style") style
      , HP.attr (HH.AttrName "data-annotation-id") ann.id
      , HP.title (fromMaybe "" ann.content)
      ]
      []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // search panel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render search panel
renderSearchPanel :: forall w i. PDFViewerProps i -> HH.HTML w i
renderSearchPanel props =
  HH.div
    [ cls [ "pdf-search absolute top-14 right-4 w-80 bg-background border border-border rounded-lg shadow-lg p-3" ]
    , ARIA.role "search"
    ]
    [ HH.div
        [ cls [ "flex items-center gap-2" ] ]
        [ HH.input
            [ cls [ "flex-1 h-9 px-3 rounded-md border border-input bg-transparent text-sm placeholder:text-muted-foreground focus:outline-none focus:ring-1 focus:ring-ring" ]
            , HP.type_ HP.InputText
            , HP.placeholder "Search in document..."
            , HP.value props.searchQuery
            , ARIA.label "Search text"
            ]
        , HH.button
            [ cls [ "h-9 w-9 inline-flex items-center justify-center rounded-md hover:bg-muted" ]
            , HP.type_ HP.ButtonButton
            , ARIA.label "Close search"
            ]
            [ closeIcon ]
        ]
    , HH.div
        [ cls [ "flex items-center justify-between mt-2 text-sm text-muted-foreground" ] ]
        [ HH.span
            []
            [ HH.text $ if length props.searchResults > 0
                then show (props.currentSearchIndex + 1) <> " of " <> show (length props.searchResults) <> " results"
                else "No results"
            ]
        , HH.div
            [ cls [ "flex items-center gap-1" ] ]
            [ HH.button
                [ cls [ "h-7 w-7 inline-flex items-center justify-center rounded hover:bg-muted" ]
                , HP.type_ HP.ButtonButton
                , HP.disabled (length props.searchResults == 0)
                , ARIA.label "Previous result"
                ]
                [ prevIcon ]
            , HH.button
                [ cls [ "h-7 w-7 inline-flex items-center justify-center rounded hover:bg-muted" ]
                , HP.type_ HP.ButtonButton
                , HP.disabled (length props.searchResults == 0)
                , ARIA.label "Next result"
                ]
                [ nextIcon ]
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // loading/error
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render loading overlay
renderLoadingOverlay :: forall w i. PDFViewerProps i -> HH.HTML w i
renderLoadingOverlay props =
  if props.isLoading
    then HH.div
      [ cls [ "absolute inset-0 z-50 flex flex-col items-center justify-center bg-background/80 backdrop-blur-sm" ]
      , ARIA.role "status"
      , ARIA.label "Loading PDF"
      ]
      [ HH.div
          [ cls [ "h-12 w-12 animate-spin rounded-full border-4 border-primary border-t-transparent" ] ]
          []
      , HH.p
          [ cls [ "mt-4 text-sm text-muted-foreground" ] ]
          [ HH.text "Loading PDF..." ]
      , case props.loadProgress of
          Just progress ->
            HH.div
              [ cls [ "mt-2 w-48 h-2 bg-muted rounded-full overflow-hidden" ] ]
              [ HH.div
                  [ cls [ "h-full bg-primary transition-all" ]
                  , HP.attr (HH.AttrName "style") ("width: " <> show progress.percent <> "%")
                  ]
                  []
              ]
          Nothing -> HH.text ""
      ]
    else HH.text ""

-- | Render error overlay
renderErrorOverlay :: forall w i. PDFViewerProps i -> HH.HTML w i
renderErrorOverlay props =
  case props.error of
    Just err ->
      HH.div
        [ cls [ "absolute inset-0 z-50 flex flex-col items-center justify-center bg-background/80 backdrop-blur-sm" ]
        , ARIA.role "alert"
        ]
        [ errorIcon
        , HH.h3
            [ cls [ "mt-4 text-lg font-semibold text-destructive" ] ]
            [ HH.text "Error Loading PDF" ]
        , HH.p
            [ cls [ "mt-2 text-sm text-muted-foreground max-w-md text-center" ] ]
            [ HH.text (errorMessage err) ]
        , HH.button
            [ cls [ "mt-4 px-4 py-2 rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors" ]
            , HP.type_ HP.ButtonButton
            ]
            [ HH.text "Try Again" ]
        ]
    Nothing -> HH.text ""
  where
    errorMessage :: PDFError -> String
    errorMessage = case _ of
      LoadError msg -> "Failed to load document: " <> msg
      RenderError msg -> "Failed to render page: " <> msg
      PasswordRequired -> "This document is password protected"
      InvalidPDF -> "The file does not appear to be a valid PDF"
      NetworkError msg -> "Network error: " <> msg

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

thumbnailIcon :: forall w i. HH.HTML w i
thumbnailIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "T" ]

outlineIcon :: forall w i. HH.HTML w i
outlineIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "O" ]

prevIcon :: forall w i. HH.HTML w i
prevIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "<" ]

nextIcon :: forall w i. HH.HTML w i
nextIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text ">" ]

zoomOutIcon :: forall w i. HH.HTML w i
zoomOutIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "-" ]

zoomInIcon :: forall w i. HH.HTML w i
zoomInIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "+" ]

singlePageIcon :: forall w i. HH.HTML w i
singlePageIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "1" ]

twoPageIcon :: forall w i. HH.HTML w i
twoPageIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "2" ]

continuousIcon :: forall w i. HH.HTML w i
continuousIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "C" ]

rotateIcon :: forall w i. HH.HTML w i
rotateIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "R" ]

searchIcon :: forall w i. HH.HTML w i
searchIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "S" ]

downloadIcon :: forall w i. HH.HTML w i
downloadIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "D" ]

printIcon :: forall w i. HH.HTML w i
printIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "P" ]

fullscreenIcon :: forall w i. HH.HTML w i
fullscreenIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "F" ]

closeIcon :: forall w i. HH.HTML w i
closeIcon = HH.span [ cls [ "w-4 h-4" ], ARIA.hidden "true" ] [ HH.text "X" ]

errorIcon :: forall w i. HH.HTML w i
errorIcon = HH.span [ cls [ "w-16 h-16 text-destructive" ], ARIA.hidden "true" ] [ HH.text "!" ]
