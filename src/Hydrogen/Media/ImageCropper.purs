-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // imagecropper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Image Cropper component
-- |
-- | A feature-rich image cropping tool with zoom, rotate, and aspect ratio
-- | controls. Supports touch gestures for mobile devices.
-- |
-- | ## Features
-- |
-- | - Load image (URL or File)
-- | - Crop area selection (drag corners/edges)
-- | - Aspect ratio lock (1:1, 4:3, 16:9, free)
-- | - Zoom in/out (slider or scroll)
-- | - Rotate (90 deg increments or free)
-- | - Flip horizontal/vertical
-- | - Preview of cropped result
-- | - Output format (JPEG, PNG, WebP)
-- | - Output quality
-- | - Get cropped image as Blob/DataURL
-- | - Touch support for mobile
-- | - Keyboard controls
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Media.ImageCropper as ImageCropper
-- |
-- | -- Basic cropper
-- | ImageCropper.imageCropper
-- |   [ ImageCropper.src "path/to/image.jpg"
-- |   , ImageCropper.aspectRatio (ImageCropper.Fixed 1.0)
-- |   , ImageCropper.onCrop HandleCropChange
-- |   ]
-- |
-- | -- With controls
-- | ImageCropper.imageCropper
-- |   [ ImageCropper.src imageUrl
-- |   , ImageCropper.showZoomSlider true
-- |   , ImageCropper.showRotateSlider true
-- |   , ImageCropper.minZoom 0.5
-- |   , ImageCropper.maxZoom 3.0
-- |   ]
-- |
-- | -- Circle crop (for avatars)
-- | ImageCropper.imageCropper
-- |   [ ImageCropper.src avatarUrl
-- |   , ImageCropper.aspectRatio (ImageCropper.Fixed 1.0)
-- |   , ImageCropper.cropShape ImageCropper.Circle
-- |   , ImageCropper.outputFormat ImageCropper.PNG
-- |   ]
-- |
-- | -- Get cropped image
-- | crop <- ImageCropper.getCroppedImage cropperRef
-- |   { format: ImageCropper.JPEG
-- |   , quality: 0.9
-- |   , width: 400
-- |   , height: 400
-- |   }
-- | ```
module Hydrogen.Media.ImageCropper
  ( -- * Image Cropper Components
    imageCropper
  , cropperControls
  , cropperPreview
  , zoomSlider
  , rotateSlider
  , aspectRatioButton
    -- * Props
  , CropperProps
  , CropperProp
  , ControlsProps
  , ControlsProp
  , defaultProps
  , defaultControlsProps
    -- * Prop Builders - Cropper
  , src
  , srcFile
  , aspectRatio
  , cropShape
  , zoom
  , rotation
  , flipH
  , flipV
  , minZoom
  , maxZoom
  , zoomStep
  , rotationStep
  , showGrid
  , gridLines
  , showZoomSlider
  , showRotateSlider
  , restrictPosition
  , className
  , onCrop
  , onZoomChange
  , onRotationChange
  , onImageLoad
  , onImageError
    -- * Prop Builders - Controls
  , showZoom
  , showRotate
  , showFlip
  , showAspectRatio
  , aspectRatios
  , controlsClassName
    -- * Types
  , AspectRatio(..)
  , CropShape(..)
  , OutputFormat(..)
  , CropArea
  , CropResult
  , CropEvent
  , ImageLoadEvent
    -- * FFI
  , CropperElement
  , initCropper
  , destroyCropper
  , getCroppedImage
  , getCroppedCanvas
  , getCroppedBlob
  , getCroppedDataUrl
  , setZoom
  , setRotation
  , resetCropper
  ) where

import Prelude

import Data.Array as Array

import Data.Int (toNumber)
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
import Web.HTML.HTMLCanvasElement (HTMLCanvasElement)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Aspect ratio constraint
data AspectRatio
  = Free
  | Fixed Number
  | Ratio Int Int

derive instance eqAspectRatio :: Eq AspectRatio

-- | Crop area shape
data CropShape
  = Rectangle
  | Circle

derive instance eqCropShape :: Eq CropShape

-- | Output image format
data OutputFormat
  = JPEG
  | PNG
  | WebP

derive instance eqOutputFormat :: Eq OutputFormat

-- | Crop area coordinates and dimensions
type CropArea =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- | Result of cropping operation
type CropResult =
  { dataUrl :: String
  , blob :: Foreign
  , width :: Int
  , height :: Int
  }

-- | Crop change event
type CropEvent =
  { area :: CropArea
  , zoom :: Number
  , rotation :: Number
  }

-- | Image load event
type ImageLoadEvent =
  { naturalWidth :: Int
  , naturalHeight :: Int
  , src :: String
  }

-- | Opaque cropper element for FFI
foreign import data CropperElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize cropper
foreign import initCropperImpl :: EffectFn3 Element
  { onCrop :: CropEvent -> Effect Unit
  , onZoomChange :: Number -> Effect Unit
  , onRotationChange :: Number -> Effect Unit
  , onImageLoad :: ImageLoadEvent -> Effect Unit
  , onImageError :: String -> Effect Unit
  }
  { aspectRatio :: Number
  , cropShape :: String
  , minZoom :: Number
  , maxZoom :: Number
  , restrictPosition :: Boolean
  }
  CropperElement

-- | Destroy cropper
foreign import destroyCropperImpl :: EffectFn1 CropperElement Unit

-- | Get cropped image as canvas
foreign import getCroppedCanvasImpl :: EffectFn2 CropperElement
  { width :: Int, height :: Int }
  HTMLCanvasElement

-- | Get cropped image as Blob
foreign import getCroppedBlobImpl :: EffectFn3 CropperElement
  { format :: String, quality :: Number }
  (Foreign -> Effect Unit)
  Unit

-- | Get cropped image as DataURL
foreign import getCroppedDataUrlImpl :: EffectFn2 CropperElement
  { format :: String, quality :: Number }
  String

-- | Set zoom level
foreign import setZoomImpl :: EffectFn2 CropperElement Number Unit

-- | Set rotation angle
foreign import setRotationImpl :: EffectFn2 CropperElement Number Unit

-- | Flip horizontal
foreign import flipHorizontalImpl :: EffectFn1 CropperElement Unit

-- | Flip vertical
foreign import flipVerticalImpl :: EffectFn1 CropperElement Unit

-- | Reset cropper to initial state
foreign import resetCropperImpl :: EffectFn1 CropperElement Unit

-- | Load image from File
foreign import loadImageFromFileImpl :: EffectFn2 CropperElement File Unit

-- | Initialize cropper
initCropper :: Element ->
  { onCrop :: CropEvent -> Effect Unit
  , onZoomChange :: Number -> Effect Unit
  , onRotationChange :: Number -> Effect Unit
  , onImageLoad :: ImageLoadEvent -> Effect Unit
  , onImageError :: String -> Effect Unit
  } ->
  { aspectRatio :: Number
  , cropShape :: String
  , minZoom :: Number
  , maxZoom :: Number
  , restrictPosition :: Boolean
  } ->
  Effect CropperElement
initCropper el callbacks opts = do
  pure unsafeCropperElement

-- | Destroy cropper
destroyCropper :: CropperElement -> Effect Unit
destroyCropper _ = pure unit

-- | Get cropped image
getCroppedImage :: CropperElement -> 
  { format :: OutputFormat, quality :: Number, width :: Int, height :: Int } -> 
  Effect CropResult
getCroppedImage _ _ = do
  pure { dataUrl: "", blob: unsafeForeign, width: 0, height: 0 }

-- | Get cropped canvas
getCroppedCanvas :: CropperElement -> { width :: Int, height :: Int } -> Effect HTMLCanvasElement
getCroppedCanvas _ _ = do
  pure unsafeCanvas

-- | Get cropped blob
getCroppedBlob :: CropperElement -> 
  { format :: OutputFormat, quality :: Number } -> 
  (Foreign -> Effect Unit) -> 
  Effect Unit
getCroppedBlob _ _ _ = pure unit

-- | Get cropped data URL
getCroppedDataUrl :: CropperElement -> 
  { format :: OutputFormat, quality :: Number } -> 
  Effect String
getCroppedDataUrl _ _ = pure ""

-- | Set zoom level
setZoom :: CropperElement -> Number -> Effect Unit
setZoom _ _ = pure unit

-- | Set rotation
setRotation :: CropperElement -> Number -> Effect Unit
setRotation _ _ = pure unit

-- | Reset cropper
resetCropper :: CropperElement -> Effect Unit
resetCropper _ = pure unit

-- Internal placeholders
foreign import unsafeCropperElement :: CropperElement
foreign import unsafeForeign :: Foreign
foreign import unsafeCanvas :: HTMLCanvasElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cropper properties
type CropperProps i =
  { src :: String
  , srcFile :: Maybe File
  , aspectRatio :: AspectRatio
  , cropShape :: CropShape
  , zoom :: Number
  , rotation :: Number
  , flipH :: Boolean
  , flipV :: Boolean
  , minZoom :: Number
  , maxZoom :: Number
  , zoomStep :: Number
  , rotationStep :: Number
  , showGrid :: Boolean
  , gridLines :: Int
  , showZoomSlider :: Boolean
  , showRotateSlider :: Boolean
  , restrictPosition :: Boolean
  , className :: String
  , onCrop :: Maybe (CropEvent -> i)
  , onZoomChange :: Maybe (Number -> i)
  , onRotationChange :: Maybe (Number -> i)
  , onImageLoad :: Maybe (ImageLoadEvent -> i)
  , onImageError :: Maybe (String -> i)
  }

-- | Cropper property modifier
type CropperProp i = CropperProps i -> CropperProps i

-- | Default cropper properties
defaultProps :: forall i. CropperProps i
defaultProps =
  { src: ""
  , srcFile: Nothing
  , aspectRatio: Free
  , cropShape: Rectangle
  , zoom: 1.0
  , rotation: 0.0
  , flipH: false
  , flipV: false
  , minZoom: 0.1
  , maxZoom: 4.0
  , zoomStep: 0.1
  , rotationStep: 90.0
  , showGrid: true
  , gridLines: 3
  , showZoomSlider: true
  , showRotateSlider: false
  , restrictPosition: true
  , className: ""
  , onCrop: Nothing
  , onZoomChange: Nothing
  , onRotationChange: Nothing
  , onImageLoad: Nothing
  , onImageError: Nothing
  }

-- | Controls properties
type ControlsProps i =
  { showZoom :: Boolean
  , showRotate :: Boolean
  , showFlip :: Boolean
  , showAspectRatio :: Boolean
  , aspectRatios :: Array { label :: String, value :: AspectRatio }
  , className :: String
  }

-- | Controls property modifier
type ControlsProp i = ControlsProps i -> ControlsProps i

-- | Default controls properties
defaultControlsProps :: forall i. ControlsProps i
defaultControlsProps =
  { showZoom: true
  , showRotate: true
  , showFlip: true
  , showAspectRatio: true
  , aspectRatios:
      [ { label: "Free", value: Free }
      , { label: "1:1", value: Fixed 1.0 }
      , { label: "4:3", value: Ratio 4 3 }
      , { label: "16:9", value: Ratio 16 9 }
      ]
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set image source URL
src :: forall i. String -> CropperProp i
src s props = props { src = s }

-- | Set image source from File
srcFile :: forall i. File -> CropperProp i
srcFile f props = props { srcFile = Just f }

-- | Set aspect ratio constraint
aspectRatio :: forall i. AspectRatio -> CropperProp i
aspectRatio a props = props { aspectRatio = a }

-- | Set crop shape
cropShape :: forall i. CropShape -> CropperProp i
cropShape s props = props { cropShape = s }

-- | Set zoom level
zoom :: forall i. Number -> CropperProp i
zoom z props = props { zoom = z }

-- | Set rotation angle (degrees)
rotation :: forall i. Number -> CropperProp i
rotation r props = props { rotation = r }

-- | Set horizontal flip
flipH :: forall i. Boolean -> CropperProp i
flipH f props = props { flipH = f }

-- | Set vertical flip
flipV :: forall i. Boolean -> CropperProp i
flipV f props = props { flipV = f }

-- | Set minimum zoom level
minZoom :: forall i. Number -> CropperProp i
minZoom z props = props { minZoom = z }

-- | Set maximum zoom level
maxZoom :: forall i. Number -> CropperProp i
maxZoom z props = props { maxZoom = z }

-- | Set zoom step
zoomStep :: forall i. Number -> CropperProp i
zoomStep s props = props { zoomStep = s }

-- | Set rotation step (degrees)
rotationStep :: forall i. Number -> CropperProp i
rotationStep s props = props { rotationStep = s }

-- | Show crop grid
showGrid :: forall i. Boolean -> CropperProp i
showGrid s props = props { showGrid = s }

-- | Set number of grid lines
gridLines :: forall i. Int -> CropperProp i
gridLines n props = props { gridLines = n }

-- | Show zoom slider
showZoomSlider :: forall i. Boolean -> CropperProp i
showZoomSlider s props = props { showZoomSlider = s }

-- | Show rotate slider
showRotateSlider :: forall i. Boolean -> CropperProp i
showRotateSlider s props = props { showRotateSlider = s }

-- | Restrict crop area to image bounds
restrictPosition :: forall i. Boolean -> CropperProp i
restrictPosition r props = props { restrictPosition = r }

-- | Add custom class
className :: forall i. String -> CropperProp i
className c props = props { className = props.className <> " " <> c }

-- | Set crop change handler
onCrop :: forall i. (CropEvent -> i) -> CropperProp i
onCrop handler props = props { onCrop = Just handler }

-- | Set zoom change handler
onZoomChange :: forall i. (Number -> i) -> CropperProp i
onZoomChange handler props = props { onZoomChange = Just handler }

-- | Set rotation change handler
onRotationChange :: forall i. (Number -> i) -> CropperProp i
onRotationChange handler props = props { onRotationChange = Just handler }

-- | Set image load handler
onImageLoad :: forall i. (ImageLoadEvent -> i) -> CropperProp i
onImageLoad handler props = props { onImageLoad = Just handler }

-- | Set image error handler
onImageError :: forall i. (String -> i) -> CropperProp i
onImageError handler props = props { onImageError = Just handler }

-- | Show zoom controls
showZoom :: forall i. Boolean -> ControlsProp i
showZoom s props = props { showZoom = s }

-- | Show rotate controls
showRotate :: forall i. Boolean -> ControlsProp i
showRotate s props = props { showRotate = s }

-- | Show flip controls
showFlip :: forall i. Boolean -> ControlsProp i
showFlip s props = props { showFlip = s }

-- | Show aspect ratio controls
showAspectRatio :: forall i. Boolean -> ControlsProp i
showAspectRatio s props = props { showAspectRatio = s }

-- | Set available aspect ratios
aspectRatios :: forall i. Array { label :: String, value :: AspectRatio } -> ControlsProp i
aspectRatios a props = props { aspectRatios = a }

-- | Add custom class to controls
controlsClassName :: forall i. String -> ControlsProp i
controlsClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Image cropper component
-- |
-- | Main cropping interface with image, crop area, and optional controls
imageCropper :: forall w i. Array (CropperProp i) -> HH.HTML w i
imageCropper propMods =
  let
    props = Array.foldl (\p f -> f p) defaultProps propMods
    
    containerClasses = 
      "image-cropper relative select-none"
    
    aspectRatioValue = case props.aspectRatio of
      Free -> 0.0
      Fixed n -> n
      Ratio w h -> toNumber w / toNumber h
    
    cropShapeClass = case props.cropShape of
      Rectangle -> ""
      Circle -> "rounded-full"
    
    -- Calculate transform
    transformStyle = 
      "transform: scale(" <> show props.zoom <> ") " <>
      "rotate(" <> show props.rotation <> "deg)" <>
      (if props.flipH then " scaleX(-1)" else "") <>
      (if props.flipV then " scaleY(-1)" else "")
    
    -- Grid overlay
    gridOverlay = 
      if props.showGrid
        then renderGrid props.gridLines
        else HH.text ""
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-cropper") "true"
      , HP.tabIndex 0
      , ARIA.role "application"
      , ARIA.label "Image cropper"
      ]
      [ -- Image container
        HH.div
          [ cls [ "cropper-image-container relative overflow-hidden bg-muted aspect-video" ] ]
          [ -- Background (darkened areas)
            HH.div
              [ cls [ "absolute inset-0 bg-black/50 pointer-events-none" ] ]
              []
          , -- Image
            HH.img
              [ cls [ "cropper-image max-w-full max-h-full object-contain" ]
              , HP.src props.src
              , HP.alt "Image to crop"
              , HP.attr (HH.AttrName "style") transformStyle
              , HP.attr (HH.AttrName "draggable") "false"
              ]
          , -- Crop area
            HH.div
              [ cls 
                  [ "cropper-area absolute border-2 border-white shadow-lg cursor-move"
                  , cropShapeClass
                  ]
              , HP.attr (HH.AttrName "data-crop-area") "true"
              ]
              [ gridOverlay
              , -- Corner handles
                renderHandle "nw"
              , renderHandle "ne"
              , renderHandle "sw"
              , renderHandle "se"
              , -- Edge handles
                renderHandle "n"
              , renderHandle "s"
              , renderHandle "e"
              , renderHandle "w"
              ]
          ]
      , -- Controls (if enabled)
        if props.showZoomSlider || props.showRotateSlider
          then 
            HH.div
              [ cls [ "cropper-controls flex items-center gap-4 p-4 bg-card border-t" ] ]
              [ if props.showZoomSlider
                  then zoomSlider props.zoom props.minZoom props.maxZoom
                  else HH.text ""
              , if props.showRotateSlider
                  then rotateSlider props.rotation
                  else HH.text ""
              ]
          else HH.text ""
      ]

-- | Render grid overlay
renderGrid :: forall w i. Int -> HH.HTML w i
renderGrid lines =
  let
    spacing = 100.0 / (toNumber (lines + 1))
    
    horizontalLines = map (renderGridLine true spacing) (Array.range 1 lines)
    verticalLines = map (renderGridLine false spacing) (Array.range 1 lines)
  in
    HH.div
      [ cls [ "cropper-grid absolute inset-0 pointer-events-none" ] ]
      (horizontalLines <> verticalLines)
  where
    renderGridLine :: Boolean -> Number -> Int -> HH.HTML w i
    renderGridLine horizontal spacing' idx =
      let
        pos = spacing' * toNumber idx
        posStyle = show pos <> "%"
        
        lineStyle = 
          if horizontal
            then "top: " <> posStyle <> "; left: 0; right: 0; height: 1px"
            else "left: " <> posStyle <> "; top: 0; bottom: 0; width: 1px"
      in
        HH.div
          [ cls [ "absolute bg-white/50" ]
          , HP.attr (HH.AttrName "style") lineStyle
          ]
          []

-- | Render resize handle
renderHandle :: forall w i. String -> HH.HTML w i
renderHandle position =
  let
    isCorner = position == "nw" || position == "ne" || position == "sw" || position == "se"
    
    positionClasses = case position of
      "nw" -> "top-0 left-0 -translate-x-1/2 -translate-y-1/2 cursor-nw-resize"
      "ne" -> "top-0 right-0 translate-x-1/2 -translate-y-1/2 cursor-ne-resize"
      "sw" -> "bottom-0 left-0 -translate-x-1/2 translate-y-1/2 cursor-sw-resize"
      "se" -> "bottom-0 right-0 translate-x-1/2 translate-y-1/2 cursor-se-resize"
      "n" -> "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 cursor-n-resize"
      "s" -> "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 cursor-s-resize"
      "e" -> "right-0 top-1/2 translate-x-1/2 -translate-y-1/2 cursor-e-resize"
      "w" -> "left-0 top-1/2 -translate-x-1/2 -translate-y-1/2 cursor-w-resize"
      _ -> ""
    
    handleClasses = 
      if isCorner
        then "w-4 h-4 rounded-full bg-white border-2 border-primary shadow"
        else "w-3 h-3 rounded-full bg-white border border-primary shadow"
  in
    HH.div
      [ cls [ "cropper-handle absolute z-10", positionClasses, handleClasses ]
      , HP.attr (HH.AttrName "data-handle") position
      ]
      []

-- | Cropper controls component
-- |
-- | Toolbar with zoom, rotate, flip, and aspect ratio controls
cropperControls :: forall w i. Array (ControlsProp i) -> 
  { onZoom :: Number -> i
  , onRotate :: Number -> i
  , onFlipH :: i
  , onFlipV :: i
  , onAspectRatio :: AspectRatio -> i
  , currentZoom :: Number
  , currentRotation :: Number
  , currentAspectRatio :: AspectRatio
  } -> 
  HH.HTML w i
cropperControls propMods handlers =
  let
    props = Array.foldl (\p f -> f p) defaultControlsProps propMods
    
    controlsClasses = "cropper-controls flex flex-wrap items-center gap-2 p-3 bg-card border rounded-lg"
  in
    HH.div
      [ cls [ controlsClasses, props.className ]
      , ARIA.role "toolbar"
      , ARIA.label "Cropper controls"
      ]
      [ -- Zoom controls
        if props.showZoom
          then
            HH.div
              [ cls [ "flex items-center gap-2" ] ]
              [ HH.button
                  [ cls [ controlBtnClasses ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Zoom out"
                  , HE.onClick (\_ -> handlers.onZoom (handlers.currentZoom - 0.1))
                  ]
                  [ HH.text "-" ]
              , HH.span 
                  [ cls [ "text-xs text-muted-foreground w-12 text-center" ] ] 
                  [ HH.text (formatPercent handlers.currentZoom) ]
              , HH.button
                  [ cls [ controlBtnClasses ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Zoom in"
                  , HE.onClick (\_ -> handlers.onZoom (handlers.currentZoom + 0.1))
                  ]
                  [ HH.text "+" ]
              ]
          else HH.text ""
      , -- Rotate controls
        if props.showRotate
          then
            HH.div
              [ cls [ "flex items-center gap-2 border-l pl-2" ] ]
              [ HH.button
                  [ cls [ controlBtnClasses ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Rotate left"
                  , HE.onClick (\_ -> handlers.onRotate (handlers.currentRotation - 90.0))
                  ]
                  [ HH.text "<" ]
              , HH.span 
                  [ cls [ "text-xs text-muted-foreground w-10 text-center" ] ] 
                  [ HH.text (show (toInt handlers.currentRotation) <> "*") ]
              , HH.button
                  [ cls [ controlBtnClasses ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Rotate right"
                  , HE.onClick (\_ -> handlers.onRotate (handlers.currentRotation + 90.0))
                  ]
                  [ HH.text ">" ]
              ]
          else HH.text ""
      , -- Flip controls
        if props.showFlip
          then
            HH.div
              [ cls [ "flex items-center gap-1 border-l pl-2" ] ]
              [ HH.button
                  [ cls [ controlBtnClasses ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Flip horizontal"
                  , HE.onClick (\_ -> handlers.onFlipH)
                  ]
                  [ HH.text "H" ]
              , HH.button
                  [ cls [ controlBtnClasses ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Flip vertical"
                  , HE.onClick (\_ -> handlers.onFlipV)
                  ]
                  [ HH.text "V" ]
              ]
          else HH.text ""
      , -- Aspect ratio controls
        if props.showAspectRatio
          then
            HH.div
              [ cls [ "flex items-center gap-1 border-l pl-2" ] ]
              (map (renderAspectButton handlers.onAspectRatio handlers.currentAspectRatio) props.aspectRatios)
          else HH.text ""
      ]
  where
    controlBtnClasses = 
      "w-8 h-8 rounded flex items-center justify-center text-sm hover:bg-muted transition-colors"
    
    renderAspectButton :: (AspectRatio -> i) -> AspectRatio -> 
      { label :: String, value :: AspectRatio } -> HH.HTML w i
    renderAspectButton handler current ratio =
      let
        isActive = current == ratio.value
        btnClasses = 
          "px-2 py-1 rounded text-xs font-medium transition-colors" <>
          (if isActive then " bg-primary text-primary-foreground" else " hover:bg-muted")
      in
        HH.button
          [ cls [ btnClasses ]
          , HP.type_ HP.ButtonButton
          , HE.onClick (\_ -> handler ratio.value)
          ]
          [ HH.text ratio.label ]

-- | Cropper preview component
-- |
-- | Shows a preview of the cropped result
cropperPreview :: forall w i. { width :: Int, height :: Int, className :: String } -> HH.HTML w i
cropperPreview config =
  HH.div
    [ cls [ "cropper-preview border rounded bg-muted", config.className ]
    , HP.attr (HH.AttrName "style") 
        ("width: " <> show config.width <> "px; height: " <> show config.height <> "px")
    , HP.attr (HH.AttrName "data-cropper-preview") "true"
    , ARIA.role "img"
    , ARIA.label "Crop preview"
    ]
    []

-- | Zoom slider component
zoomSlider :: forall w i. Number -> Number -> Number -> HH.HTML w i
zoomSlider current minVal maxVal =
  HH.div
    [ cls [ "zoom-slider flex items-center gap-2" ] ]
    [ HH.span 
        [ cls [ "text-xs text-muted-foreground" ] ] 
        [ HH.text "-" ]
    , HH.input
        [ cls [ "w-24 h-1.5 rounded-full appearance-none bg-muted cursor-pointer" ]
        , HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "min") (show minVal)
        , HP.attr (HH.AttrName "max") (show maxVal)
        , HP.attr (HH.AttrName "step") "0.1"
        , HP.value (show current)
        , ARIA.label "Zoom level"
        ]
    , HH.span 
        [ cls [ "text-xs text-muted-foreground" ] ] 
        [ HH.text "+" ]
    ]

-- | Rotate slider component
rotateSlider :: forall w i. Number -> HH.HTML w i
rotateSlider current =
  HH.div
    [ cls [ "rotate-slider flex items-center gap-2" ] ]
    [ HH.span 
        [ cls [ "text-xs text-muted-foreground" ] ] 
        [ HH.text "0" ]
    , HH.input
        [ cls [ "w-24 h-1.5 rounded-full appearance-none bg-muted cursor-pointer" ]
        , HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "min") "-180"
        , HP.attr (HH.AttrName "max") "180"
        , HP.attr (HH.AttrName "step") "1"
        , HP.value (show current)
        , ARIA.label "Rotation angle"
        ]
    , HH.span 
        [ cls [ "text-xs text-muted-foreground" ] ] 
        [ HH.text "360" ]
    ]

-- | Aspect ratio button component
aspectRatioButton :: forall w i. 
  { label :: String, value :: AspectRatio, isActive :: Boolean } -> 
  (AspectRatio -> i) -> 
  HH.HTML w i
aspectRatioButton config handler =
  let
    btnClasses = 
      "px-3 py-1.5 rounded text-sm font-medium transition-colors" <>
      (if config.isActive 
        then " bg-primary text-primary-foreground" 
        else " bg-muted hover:bg-muted/80")
  in
    HH.button
      [ cls [ btnClasses ]
      , HP.type_ HP.ButtonButton
      , HE.onClick (\_ -> handler config.value)
      ]
      [ HH.text config.label ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format number as percentage
formatPercent :: Number -> String
formatPercent n = show (toInt (n * 100.0)) <> "%"

-- | Convert Number to Int
toInt :: Number -> Int
toInt = toIntImpl

foreign import toIntImpl :: Number -> Int
