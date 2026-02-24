-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // gallery
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Image gallery with lightbox
-- |
-- | Responsive image gallery with thumbnail grid, lightbox viewer,
-- | zoom/pan support, and touch gestures.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Media.Gallery as G
-- |
-- | -- Basic gallery
-- | G.gallery
-- |   [ G.images
-- |       [ { src: "img1.jpg", thumb: "thumb1.jpg", alt: "Image 1" }
-- |       , { src: "img2.jpg", thumb: "thumb2.jpg", alt: "Image 2" }
-- |       ]
-- |   ]
-- |
-- | -- Masonry layout with columns
-- | G.gallery
-- |   [ G.images myImages
-- |   , G.layout G.Masonry
-- |   , G.columns 4
-- |   , G.gap G.G4
-- |   ]
-- |
-- | -- With lightbox features
-- | G.gallery
-- |   [ G.images myImages
-- |   , G.enableZoom true
-- |   , G.enableSlideshow true
-- |   , G.slideshowInterval 3000.0
-- |   , G.showDownload true
-- |   , G.showShare true
-- |   ]
-- |
-- | -- Responsive columns
-- | G.gallery
-- |   [ G.images myImages
-- |   , G.columnsSm 2
-- |   , G.columnsMd 3
-- |   , G.columnsLg 4
-- |   ]
-- | ```
module Hydrogen.Media.Gallery
  ( -- * Component
    gallery
  , lightbox
    -- * Props
  , GalleryProps
  , GalleryProp
  , defaultProps
    -- * Prop Builders
  , images
  , layout
  , columns
  , columnsSm
  , columnsMd
  , columnsLg
  , columnsXl
  , gap
  , aspectRatio
  , objectFit
  , enableLightbox
  , enableZoom
  , enableSlideshow
  , slideshowInterval
  , showDownload
  , showShare
  , showInfo
  , lazyLoad
  , placeholderColor
  , className
    -- * Event Handlers
  , onImageClick
  , onLightboxOpen
  , onLightboxClose
  , onImageChange
  , onDownload
  , onShare
    -- * Types
  , GalleryImage
  , GalleryState
  , GalleryLayout(..)
  , Gap(..)
  , AspectRatio(..)
  , ObjectFit(..)
    -- * State Helpers
  , defaultState
    -- * FFI
  , GalleryRef
  , createGalleryRef
  , openLightbox
  , closeLightbox
  , nextImage
  , previousImage
  , goToImage
  , startSlideshow
  , stopSlideshow
  , toggleSlideshow
  , zoomIn
  , zoomOut
  , resetZoom
  ) where

import Prelude

import Data.Array (foldl, length, mapWithIndex, (!!))
import Data.Int (round)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Gallery image
type GalleryImage =
  { src :: String
  , thumb :: Maybe String
  , alt :: String
  , title :: Maybe String
  , description :: Maybe String
  , width :: Maybe Int
  , height :: Maybe Int
  }

-- | Gallery layout options
data GalleryLayout
  = Grid       -- ^ Regular grid
  | Masonry    -- ^ Masonry (Pinterest-style)
  | Justified  -- ^ Justified (Flickr-style)

derive instance eqGalleryLayout :: Eq GalleryLayout

-- | Gap sizes
data Gap
  = G0 | G1 | G2 | G3 | G4 | G5 | G6 | G8

derive instance eqGap :: Eq Gap

gapClass :: Gap -> String
gapClass = case _ of
  G0 -> "gap-0"
  G1 -> "gap-1"
  G2 -> "gap-2"
  G3 -> "gap-3"
  G4 -> "gap-4"
  G5 -> "gap-5"
  G6 -> "gap-6"
  G8 -> "gap-8"

-- | Aspect ratio options
data AspectRatio
  = Square      -- ^ 1:1
  | Video       -- ^ 16:9
  | Photo       -- ^ 4:3
  | Portrait    -- ^ 3:4
  | Auto        -- ^ Natural aspect ratio

derive instance eqAspectRatio :: Eq AspectRatio

aspectRatioClass :: AspectRatio -> String
aspectRatioClass = case _ of
  Square -> "aspect-square"
  Video -> "aspect-video"
  Photo -> "aspect-[4/3]"
  Portrait -> "aspect-[3/4]"
  Auto -> ""

-- | Object fit options
data ObjectFit
  = Cover
  | Contain
  | Fill

derive instance eqObjectFit :: Eq ObjectFit

objectFitClass :: ObjectFit -> String
objectFitClass = case _ of
  Cover -> "object-cover"
  Contain -> "object-contain"
  Fill -> "object-fill"

-- | Gallery state
type GalleryState =
  { lightboxOpen :: Boolean
  , currentIndex :: Int
  , zoom :: Number
  , panX :: Number
  , panY :: Number
  , slideshowActive :: Boolean
  , loading :: Boolean
  }

-- | Default gallery state
defaultState :: GalleryState
defaultState =
  { lightboxOpen: false
  , currentIndex: 0
  , zoom: 1.0
  , panX: 0.0
  , panY: 0.0
  , slideshowActive: false
  , loading: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Opaque gallery element
foreign import data GalleryElement :: Type

-- | Gallery ref for imperative control
newtype GalleryRef = GalleryRef
  { elementRef :: Ref (Maybe GalleryElement)
  , state :: Ref GalleryState
  }

-- | FFI: Initialize gallery
foreign import initGalleryImpl :: EffectFn2 String GalleryConfig GalleryElement

-- | FFI: Setup touch gestures
foreign import setupGesturesImpl :: EffectFn1 GalleryElement Unit

-- | FFI: Set zoom level
foreign import setZoomImpl :: EffectFn2 GalleryElement Number Unit

-- | FFI: Set pan position
foreign import setPanImpl :: EffectFn2 GalleryElement { x :: Number, y :: Number } Unit

-- | FFI: Download image
foreign import downloadImageImpl :: EffectFn1 String Unit

-- | FFI: Share image
foreign import shareImageImpl :: EffectFn1 ShareData Unit

-- | FFI: Destroy gallery
foreign import destroyGalleryImpl :: EffectFn1 GalleryElement Unit

-- | Initialize gallery element
initGallery :: String -> GalleryConfig -> Effect GalleryElement
initGallery selector config = runEffectFn2 initGalleryImpl selector config

-- | Setup touch/mouse gestures on gallery element
setupGestures :: GalleryElement -> Effect Unit
setupGestures el = runEffectFn1 setupGesturesImpl el

-- | Set zoom level on gallery element
setZoom :: GalleryElement -> Number -> Effect Unit
setZoom el level = runEffectFn2 setZoomImpl el level

-- | Set pan position on gallery element
setPan :: GalleryElement -> { x :: Number, y :: Number } -> Effect Unit
setPan el pos = runEffectFn2 setPanImpl el pos

-- | Download image from URL
downloadImage :: String -> Effect Unit
downloadImage url = runEffectFn1 downloadImageImpl url

-- | Share image via Web Share API
shareImage :: ShareData -> Effect Unit
shareImage shareData = runEffectFn1 shareImageImpl shareData

-- | Destroy gallery and clean up resources
destroyGallery :: GalleryElement -> Effect Unit
destroyGallery el = runEffectFn1 destroyGalleryImpl el

-- Internal config types for FFI
type GalleryConfig =
  { onImageClick :: Int -> Effect Unit
  , onLightboxOpen :: Effect Unit
  , onLightboxClose :: Effect Unit
  , onImageChange :: Int -> Effect Unit
  , enableKeyboard :: Boolean
  , enableZoom :: Boolean
  }

type ShareData =
  { url :: String
  , title :: String
  , text :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type GalleryProps i =
  { images :: Array GalleryImage
  , layout :: GalleryLayout
  , columns :: Int
  , columnsSm :: Maybe Int
  , columnsMd :: Maybe Int
  , columnsLg :: Maybe Int
  , columnsXl :: Maybe Int
  , gap :: Gap
  , aspectRatio :: AspectRatio
  , objectFit :: ObjectFit
  , enableLightbox :: Boolean
  , enableZoom :: Boolean
  , enableSlideshow :: Boolean
  , slideshowInterval :: Number
  , showDownload :: Boolean
  , showShare :: Boolean
  , showInfo :: Boolean
  , lazyLoad :: Boolean
  , placeholderColor :: String
  , className :: String
  -- Event handlers
  , onImageClick :: Maybe (Int -> i)
  , onLightboxOpen :: Maybe (Unit -> i)
  , onLightboxClose :: Maybe (Unit -> i)
  , onImageChange :: Maybe (Int -> i)
  , onDownload :: Maybe (GalleryImage -> i)
  , onShare :: Maybe (GalleryImage -> i)
  }

type GalleryProp i = GalleryProps i -> GalleryProps i

defaultProps :: forall i. GalleryProps i
defaultProps =
  { images: []
  , layout: Grid
  , columns: 3
  , columnsSm: Nothing
  , columnsMd: Nothing
  , columnsLg: Nothing
  , columnsXl: Nothing
  , gap: G4
  , aspectRatio: Square
  , objectFit: Cover
  , enableLightbox: true
  , enableZoom: true
  , enableSlideshow: true
  , slideshowInterval: 3000.0
  , showDownload: true
  , showShare: true
  , showInfo: true
  , lazyLoad: true
  , placeholderColor: "#e2e8f0"
  , className: ""
  , onImageClick: Nothing
  , onLightboxOpen: Nothing
  , onLightboxClose: Nothing
  , onImageChange: Nothing
  , onDownload: Nothing
  , onShare: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set gallery images
images :: forall i. Array GalleryImage -> GalleryProp i
images imgs props = props { images = imgs }

-- | Set layout mode
layout :: forall i. GalleryLayout -> GalleryProp i
layout l props = props { layout = l }

-- | Set number of columns
columns :: forall i. Int -> GalleryProp i
columns c props = props { columns = c }

-- | Columns at small breakpoint
columnsSm :: forall i. Int -> GalleryProp i
columnsSm c props = props { columnsSm = Just c }

-- | Columns at medium breakpoint
columnsMd :: forall i. Int -> GalleryProp i
columnsMd c props = props { columnsMd = Just c }

-- | Columns at large breakpoint
columnsLg :: forall i. Int -> GalleryProp i
columnsLg c props = props { columnsLg = Just c }

-- | Columns at extra-large breakpoint
columnsXl :: forall i. Int -> GalleryProp i
columnsXl c props = props { columnsXl = Just c }

-- | Set gap between items
gap :: forall i. Gap -> GalleryProp i
gap g props = props { gap = g }

-- | Set aspect ratio
aspectRatio :: forall i. AspectRatio -> GalleryProp i
aspectRatio a props = props { aspectRatio = a }

-- | Set object fit
objectFit :: forall i. ObjectFit -> GalleryProp i
objectFit o props = props { objectFit = o }

-- | Enable lightbox
enableLightbox :: forall i. Boolean -> GalleryProp i
enableLightbox e props = props { enableLightbox = e }

-- | Enable zoom in lightbox
enableZoom :: forall i. Boolean -> GalleryProp i
enableZoom e props = props { enableZoom = e }

-- | Enable slideshow mode
enableSlideshow :: forall i. Boolean -> GalleryProp i
enableSlideshow e props = props { enableSlideshow = e }

-- | Set slideshow interval (ms)
slideshowInterval :: forall i. Number -> GalleryProp i
slideshowInterval s props = props { slideshowInterval = s }

-- | Show download button
showDownload :: forall i. Boolean -> GalleryProp i
showDownload s props = props { showDownload = s }

-- | Show share button
showShare :: forall i. Boolean -> GalleryProp i
showShare s props = props { showShare = s }

-- | Show image info panel
showInfo :: forall i. Boolean -> GalleryProp i
showInfo s props = props { showInfo = s }

-- | Enable lazy loading
lazyLoad :: forall i. Boolean -> GalleryProp i
lazyLoad l props = props { lazyLoad = l }

-- | Set placeholder color
placeholderColor :: forall i. String -> GalleryProp i
placeholderColor c props = props { placeholderColor = c }

-- | Add custom class
className :: forall i. String -> GalleryProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle image click
onImageClick :: forall i. (Int -> i) -> GalleryProp i
onImageClick h props = props { onImageClick = Just h }

-- | Handle lightbox open
onLightboxOpen :: forall i. (Unit -> i) -> GalleryProp i
onLightboxOpen h props = props { onLightboxOpen = Just h }

-- | Handle lightbox close
onLightboxClose :: forall i. (Unit -> i) -> GalleryProp i
onLightboxClose h props = props { onLightboxClose = Just h }

-- | Handle image change
onImageChange :: forall i. (Int -> i) -> GalleryProp i
onImageChange h props = props { onImageChange = Just h }

-- | Handle download
onDownload :: forall i. (GalleryImage -> i) -> GalleryProp i
onDownload h props = props { onDownload = Just h }

-- | Handle share
onShare :: forall i. (GalleryImage -> i) -> GalleryProp i
onShare h props = props { onShare = Just h }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create gallery ref
createGalleryRef :: Effect GalleryRef
createGalleryRef = do
  elementRef <- Ref.new Nothing
  state <- Ref.new defaultState
  pure $ GalleryRef { elementRef, state }

-- | Open lightbox at index
openLightbox :: GalleryRef -> Int -> Effect Unit
openLightbox (GalleryRef ref) index = do
  Ref.modify_ (\s -> s { lightboxOpen = true, currentIndex = index }) ref.state

-- | Close lightbox
closeLightbox :: GalleryRef -> Effect Unit
closeLightbox (GalleryRef ref) = do
  Ref.modify_ (\s -> s { lightboxOpen = false, zoom = 1.0, panX = 0.0, panY = 0.0 }) ref.state

-- | Go to next image
nextImage :: GalleryRef -> Int -> Effect Unit
nextImage (GalleryRef ref) total = do
  Ref.modify_ (\s -> s { currentIndex = (s.currentIndex + 1) `mod` total, zoom = 1.0, panX = 0.0, panY = 0.0 }) ref.state

-- | Go to previous image
previousImage :: GalleryRef -> Int -> Effect Unit
previousImage (GalleryRef ref) total = do
  Ref.modify_ (\s -> s { currentIndex = (s.currentIndex - 1 + total) `mod` total, zoom = 1.0, panX = 0.0, panY = 0.0 }) ref.state

-- | Go to specific image
goToImage :: GalleryRef -> Int -> Effect Unit
goToImage (GalleryRef ref) index = do
  Ref.modify_ (\s -> s { currentIndex = index, zoom = 1.0, panX = 0.0, panY = 0.0 }) ref.state

-- | Start slideshow
startSlideshow :: GalleryRef -> Effect Unit
startSlideshow (GalleryRef ref) = do
  Ref.modify_ (\s -> s { slideshowActive = true }) ref.state

-- | Stop slideshow
stopSlideshow :: GalleryRef -> Effect Unit
stopSlideshow (GalleryRef ref) = do
  Ref.modify_ (\s -> s { slideshowActive = false }) ref.state

-- | Toggle slideshow
toggleSlideshow :: GalleryRef -> Effect Unit
toggleSlideshow (GalleryRef ref) = do
  Ref.modify_ (\s -> s { slideshowActive = not s.slideshowActive }) ref.state

-- | Zoom in
zoomIn :: GalleryRef -> Effect Unit
zoomIn (GalleryRef ref) = do
  Ref.modify_ (\s -> s { zoom = min 4.0 (s.zoom * 1.5) }) ref.state

-- | Zoom out
zoomOut :: GalleryRef -> Effect Unit
zoomOut (GalleryRef ref) = do
  Ref.modify_ (\s -> s { zoom = max 1.0 (s.zoom / 1.5) }) ref.state

-- | Reset zoom
resetZoom :: GalleryRef -> Effect Unit
resetZoom (GalleryRef ref) = do
  Ref.modify_ (\s -> s { zoom = 1.0, panX = 0.0, panY = 0.0 }) ref.state

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Gallery component
gallery
  :: forall w i
   . Array (GalleryProp i)
  -> GalleryState
  -> HH.HTML w i
gallery propMods state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "gallery", props.className ] ]
      [ -- Thumbnail grid
        renderGrid props
      
      -- Lightbox
      , if state.lightboxOpen && props.enableLightbox
          then lightbox props state
          else HH.text ""
      ]

-- | Render thumbnail grid
renderGrid :: forall w i. GalleryProps i -> HH.HTML w i
renderGrid props =
  case props.layout of
    Grid -> renderRegularGrid props
    Masonry -> renderMasonryGrid props
    Justified -> renderJustifiedGrid props

-- | Regular grid layout
renderRegularGrid :: forall w i. GalleryProps i -> HH.HTML w i
renderRegularGrid props =
  let
    columnClasses = buildColumnClasses props
  in
    HH.div
      [ cls [ "grid", columnClasses, gapClass props.gap ] ]
      (mapWithIndex (renderThumbnail props) props.images)

-- | Masonry layout
renderMasonryGrid :: forall w i. GalleryProps i -> HH.HTML w i
renderMasonryGrid props =
  let
    columnClasses = buildMasonryClasses props
  in
    HH.div
      [ cls [ columnClasses, gapClass props.gap ] ]
      (mapWithIndex (renderMasonryItem props) props.images)

-- | Justified layout (simplified)
renderJustifiedGrid :: forall w i. GalleryProps i -> HH.HTML w i
renderJustifiedGrid props =
  HH.div
    [ cls [ "flex flex-wrap", gapClass props.gap ] ]
    (mapWithIndex (renderJustifiedItem props) props.images)

-- | Build grid column classes
buildColumnClasses :: forall i. GalleryProps i -> String
buildColumnClasses props =
  let
    base = "grid-cols-" <> show props.columns
    sm = case props.columnsSm of
      Just n -> "sm:grid-cols-" <> show n
      Nothing -> ""
    md = case props.columnsMd of
      Just n -> "md:grid-cols-" <> show n
      Nothing -> ""
    lg = case props.columnsLg of
      Just n -> "lg:grid-cols-" <> show n
      Nothing -> ""
    xl = case props.columnsXl of
      Just n -> "xl:grid-cols-" <> show n
      Nothing -> ""
  in
    base <> " " <> sm <> " " <> md <> " " <> lg <> " " <> xl

-- | Build masonry column classes
buildMasonryClasses :: forall i. GalleryProps i -> String
buildMasonryClasses props =
  let
    base = "columns-" <> show props.columns
    sm = case props.columnsSm of
      Just n -> "sm:columns-" <> show n
      Nothing -> ""
    md = case props.columnsMd of
      Just n -> "md:columns-" <> show n
      Nothing -> ""
    lg = case props.columnsLg of
      Just n -> "lg:columns-" <> show n
      Nothing -> ""
    xl = case props.columnsXl of
      Just n -> "xl:columns-" <> show n
      Nothing -> ""
  in
    base <> " " <> sm <> " " <> md <> " " <> lg <> " " <> xl

-- | Render thumbnail
renderThumbnail :: forall w i. GalleryProps i -> Int -> GalleryImage -> HH.HTML w i
renderThumbnail props index img =
  HH.div
    [ cls 
        [ "gallery-item group relative overflow-hidden rounded-lg cursor-pointer"
        , "transition-transform hover:scale-[1.02]"
        , aspectRatioClass props.aspectRatio
        ]
    , HP.attr (HH.AttrName "data-index") (show index)
    ]
    [ HH.img
        [ cls [ "w-full h-full", objectFitClass props.objectFit ]
        , HP.src (fromMaybe img.src img.thumb)
        , HP.alt img.alt
        , if props.lazyLoad
            then HP.attr (HH.AttrName "loading") "lazy"
            else HP.attr (HH.AttrName "loading") "eager"
        ]
    
    -- Hover overlay
    , HH.div
        [ cls [ "absolute inset-0 bg-black/0 group-hover:bg-black/20 transition-colors" ] ]
        []
    ]

-- | Render masonry item
renderMasonryItem :: forall w i. GalleryProps i -> Int -> GalleryImage -> HH.HTML w i
renderMasonryItem props index img =
  HH.div
    [ cls [ "gallery-item break-inside-avoid mb-4 overflow-hidden rounded-lg cursor-pointer group" ]
    , HP.attr (HH.AttrName "data-index") (show index)
    ]
    [ HH.img
        [ cls [ "w-full", objectFitClass props.objectFit ]
        , HP.src (fromMaybe img.src img.thumb)
        , HP.alt img.alt
        , if props.lazyLoad
            then HP.attr (HH.AttrName "loading") "lazy"
            else HP.attr (HH.AttrName "loading") "eager"
        ]
    ]

-- | Render justified item
renderJustifiedItem :: forall w i. GalleryProps i -> Int -> GalleryImage -> HH.HTML w i
renderJustifiedItem props index img =
  HH.div
    [ cls [ "gallery-item flex-grow overflow-hidden rounded-lg cursor-pointer group" ]
    , HP.style "flex-basis: 200px; height: 200px;"
    , HP.attr (HH.AttrName "data-index") (show index)
    ]
    [ HH.img
        [ cls [ "w-full h-full object-cover" ]
        , HP.src (fromMaybe img.src img.thumb)
        , HP.alt img.alt
        , if props.lazyLoad
            then HP.attr (HH.AttrName "loading") "lazy"
            else HP.attr (HH.AttrName "loading") "eager"
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // lightbox
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lightbox component
lightbox
  :: forall w i
   . GalleryProps i
  -> GalleryState
  -> HH.HTML w i
lightbox props state =
  let
    currentImage = props.images !! state.currentIndex
    total = length props.images
    
    -- Transform for zoom/pan
    transformStyle = 
      "transform: scale(" <> show state.zoom <> ") " <>
      "translate(" <> show state.panX <> "px, " <> show state.panY <> "px);"
  in
    HH.div
      [ cls [ "lightbox fixed inset-0 z-50 bg-black/95 flex items-center justify-center" ]
      , ARIA.role "dialog"
      , ARIA.label "Image lightbox"
      ]
      [ -- Close button
        HH.button
          [ cls [ "absolute top-4 right-4 p-2 text-white/80 hover:text-white transition-colors z-10" ]
          , ARIA.label "Close lightbox"
          ]
          [ closeIcon ]
      
      -- Header with counter and actions
      , HH.div
          [ cls [ "absolute top-4 left-4 flex items-center gap-4 z-10" ] ]
          [ -- Image counter
            HH.div
              [ cls [ "text-white/80 text-sm" ] ]
              [ HH.text (show (state.currentIndex + 1) <> " / " <> show total) ]
          
          -- Slideshow toggle
          , if props.enableSlideshow
              then HH.button
                [ cls 
                    [ "p-2 transition-colors"
                    , if state.slideshowActive
                        then "text-primary"
                        else "text-white/80 hover:text-white"
                    ]
                , ARIA.label (if state.slideshowActive then "Stop slideshow" else "Start slideshow")
                ]
                [ if state.slideshowActive then pauseIcon else playIcon ]
              else HH.text ""
          
          -- Zoom controls
          , if props.enableZoom
              then HH.div
                [ cls [ "flex items-center gap-1" ] ]
                [ HH.button
                    [ cls [ "p-2 text-white/80 hover:text-white transition-colors" ]
                    , ARIA.label "Zoom out"
                    ]
                    [ zoomOutIcon ]
                , HH.span
                    [ cls [ "text-white/80 text-xs min-w-[3rem] text-center" ] ]
                    [ HH.text (show (round (state.zoom * 100.0)) <> "%") ]
                , HH.button
                    [ cls [ "p-2 text-white/80 hover:text-white transition-colors" ]
                    , ARIA.label "Zoom in"
                    ]
                    [ zoomInIcon ]
                ]
              else HH.text ""
          ]
      
      -- Navigation: Previous
      , if total > 1
          then HH.button
            [ cls 
                [ "absolute left-4 top-1/2 -translate-y-1/2 p-3 rounded-full"
                , "bg-black/50 text-white hover:bg-black/70 transition-colors"
                ]
            , ARIA.label "Previous image"
            ]
            [ chevronLeftIcon ]
          else HH.text ""
      
      -- Main image
      , case currentImage of
          Just img ->
            HH.div
              [ cls [ "relative max-w-[90vw] max-h-[80vh] select-none" ]
              , HP.style (if state.zoom > 1.0 then "cursor: grab;" else "")
              ]
              [ HH.img
                  [ cls [ "max-w-full max-h-[80vh] object-contain transition-transform duration-200" ]
                  , HP.src img.src
                  , HP.alt img.alt
                  , HP.style transformStyle
                  , HP.attr (HH.AttrName "draggable") "false"
                  ]
              ]
          Nothing -> HH.text ""
      
      -- Navigation: Next
      , if total > 1
          then HH.button
            [ cls 
                [ "absolute right-4 top-1/2 -translate-y-1/2 p-3 rounded-full"
                , "bg-black/50 text-white hover:bg-black/70 transition-colors"
                ]
            , ARIA.label "Next image"
            ]
            [ chevronRightIcon ]
          else HH.text ""
      
      -- Bottom bar with info and actions
      , HH.div
          [ cls [ "absolute bottom-0 left-0 right-0 p-4 bg-gradient-to-t from-black/60 to-transparent" ] ]
          [ HH.div
              [ cls [ "flex items-end justify-between" ] ]
              [ -- Image info
                if props.showInfo
                  then case currentImage of
                    Just img -> HH.div_
                      [ case img.title of
                          Just t -> HH.div
                            [ cls [ "text-white font-medium" ] ]
                            [ HH.text t ]
                          Nothing -> HH.text ""
                      , case img.description of
                          Just d -> HH.div
                            [ cls [ "text-white/70 text-sm" ] ]
                            [ HH.text d ]
                          Nothing -> HH.text ""
                      ]
                    Nothing -> HH.text ""
                  else HH.text ""
              
              -- Action buttons
              , HH.div
                  [ cls [ "flex items-center gap-2" ] ]
                  [ -- Download
                    if props.showDownload
                      then HH.button
                        [ cls [ "p-2 text-white/80 hover:text-white transition-colors" ]
                        , ARIA.label "Download"
                        ]
                        [ downloadIcon ]
                      else HH.text ""
                  
                  -- Share
                  , if props.showShare
                      then HH.button
                        [ cls [ "p-2 text-white/80 hover:text-white transition-colors" ]
                        , ARIA.label "Share"
                        ]
                        [ shareIcon ]
                      else HH.text ""
                  ]
              ]
          
          -- Thumbnail strip
          , if total > 1
              then HH.div
                [ cls [ "flex gap-2 mt-4 justify-center overflow-x-auto py-2" ] ]
                (mapWithIndex (renderLightboxThumb state.currentIndex) props.images)
              else HH.text ""
          ]
      ]

-- | Render lightbox thumbnail
renderLightboxThumb :: forall w i. Int -> Int -> GalleryImage -> HH.HTML w i
renderLightboxThumb currentIndex index img =
  HH.div
    [ cls 
        [ "w-16 h-16 flex-shrink-0 rounded overflow-hidden cursor-pointer transition-all"
        , if index == currentIndex
            then "ring-2 ring-white opacity-100"
            else "opacity-50 hover:opacity-75"
        ]
    , HP.attr (HH.AttrName "data-index") (show index)
    ]
    [ HH.img
        [ cls [ "w-full h-full object-cover" ]
        , HP.src (fromMaybe img.src img.thumb)
        , HP.alt ""
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-6 h-6" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 18L18 6M6 6l12 12" ]
        []
    ]

chevronLeftIcon :: forall w i. HH.HTML w i
chevronLeftIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-6 h-6" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M15 19l-7-7 7-7" ]
        []
    ]

chevronRightIcon :: forall w i. HH.HTML w i
chevronRightIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-6 h-6" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M9 5l7 7-7 7" ]
        []
    ]

zoomInIcon :: forall w i. HH.HTML w i
zoomInIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "11"
        , HP.attr (HH.AttrName "cy") "11"
        , HP.attr (HH.AttrName "r") "8"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 21l-4.35-4.35M11 8v6M8 11h6" ]
        []
    ]

zoomOutIcon :: forall w i. HH.HTML w i
zoomOutIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "11"
        , HP.attr (HH.AttrName "cy") "11"
        , HP.attr (HH.AttrName "r") "8"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 21l-4.35-4.35M8 11h6" ]
        []
    ]

playIcon :: forall w i. HH.HTML w i
playIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M8 5v14l11-7z" ]
        []
    ]

pauseIcon :: forall w i. HH.HTML w i
pauseIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 4h4v16H6V4zm8 0h4v16h-4V4z" ]
        []
    ]

downloadIcon :: forall w i. HH.HTML w i
downloadIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 15v4a2 2 0 01-2 2H5a2 2 0 01-2-2v-4M7 10l5 5 5-5M12 15V3" ]
        []
    ]

shareIcon :: forall w i. HH.HTML w i
shareIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "18"
        , HP.attr (HH.AttrName "cy") "5"
        , HP.attr (HH.AttrName "r") "3"
        ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "6"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "3"
        ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "18"
        , HP.attr (HH.AttrName "cy") "19"
        , HP.attr (HH.AttrName "r") "3"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M8.59 13.51l6.83 3.98M15.41 6.51l-6.82 3.98" ]
        []
    ]
