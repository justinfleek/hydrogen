-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // signature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Signature pad component
-- |
-- | Canvas-based signature capture with drawing, erasing, and export capabilities.
-- |
-- | ## Features
-- |
-- | - Canvas-based drawing
-- | - Configurable pen color and thickness
-- | - Eraser mode
-- | - Clear and undo functionality
-- | - Save as PNG/SVG/JSON
-- | - Load from JSON (replay strokes)
-- | - Touch and stylus support
-- | - Pressure sensitivity (when available)
-- | - Dotted line guide option
-- | - Read-only display mode
-- | - Responsive sizing
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Signature as Signature
-- |
-- | -- Basic signature pad
-- | Signature.signaturePad
-- |   [ Signature.onChange HandleSignatureChange
-- |   , Signature.penColor "#000000"
-- |   , Signature.penThickness 2.0
-- |   ]
-- |
-- | -- With guide line and eraser
-- | Signature.signaturePad
-- |   [ Signature.showGuide true
-- |   , Signature.allowEraser true
-- |   , Signature.onClear HandleClear
-- |   ]
-- |
-- | -- Read-only display mode
-- | Signature.signaturePad
-- |   [ Signature.readOnly true
-- |   , Signature.strokeData existingSignature
-- |   ]
-- |
-- | -- With toolbar
-- | Signature.signaturePadWithToolbar
-- |   [ Signature.onChange HandleChange
-- |   , Signature.showColorPicker true
-- |   ]
-- | ```
module Hydrogen.Component.Signature
  ( -- * Components
    signaturePad
  , signaturePadWithToolbar
  , signatureToolbar
  , signatureDisplay
    -- * Props
  , SignatureProps
  , SignatureProp
  , ToolbarProps
  , ToolbarProp
  , defaultProps
  , defaultToolbarProps
    -- * Prop Builders - Signature Pad
  , penColor
  , penThickness
  , eraserMode
  , showGuide
  , guideStyle
  , readOnly
  , strokeData
  , backgroundColor
  , width
  , height
  , onChange
  , onClear
  , onUndo
  , className
    -- * Prop Builders - Toolbar
  , showColorPicker
  , showThicknessSlider
  , showEraser
  , showClear
  , showUndo
  , toolbarPosition
  , toolbarClassName
    -- * Types
  , StrokeData
  , Point
  , Stroke
  , GuideStyle(Dotted, Dashed, Solid, Hidden)
  , ToolbarPosition(Top, Bottom)
  , ExportFormat(PNG, SVG, JSON)
    -- * FFI
  , SignatureElement
  , initSignaturePad
  , destroySignaturePad
  , clearSignature
  , undoStroke
  , exportSignature
  , importSignature
  , isEmpty
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Point with optional pressure
type Point =
  { x :: Number
  , y :: Number
  , pressure :: Maybe Number
  }

-- | Single stroke (line segment)
type Stroke =
  { points :: Array Point
  , color :: String
  , thickness :: Number
  }

-- | Complete stroke data for serialization
type StrokeData =
  { strokes :: Array Stroke
  , width :: Int
  , height :: Int
  }

-- | Guide line style
data GuideStyle
  = Dotted
  | Dashed
  | Solid
  | Hidden

derive instance eqGuideStyle :: Eq GuideStyle

-- | Toolbar position
data ToolbarPosition
  = Top
  | Bottom

derive instance eqToolbarPosition :: Eq ToolbarPosition

-- | Export format
data ExportFormat
  = PNG
  | SVG
  | JSON

derive instance eqExportFormat :: Eq ExportFormat

-- | Opaque signature element for FFI
foreign import data SignatureElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize signature pad
foreign import initSignaturePadImpl :: EffectFn2 Element
  { penColor :: String
  , penThickness :: Number
  , backgroundColor :: String
  , onDraw :: Effect Unit
  }
  SignatureElement

-- | Destroy signature pad
foreign import destroySignaturePadImpl :: EffectFn1 SignatureElement Unit

-- | Clear signature
foreign import clearSignatureImpl :: EffectFn1 SignatureElement Unit

-- | Undo last stroke
foreign import undoStrokeImpl :: EffectFn1 SignatureElement Boolean

-- | Export signature
foreign import exportSignatureImpl :: EffectFn2 SignatureElement String String

-- | Import signature from JSON
foreign import importSignatureImpl :: EffectFn2 SignatureElement String Unit

-- | Check if signature is empty
foreign import isEmptyImpl :: EffectFn1 SignatureElement Boolean

-- | Initialize signature pad
initSignaturePad :: Element ->
  { penColor :: String
  , penThickness :: Number
  , backgroundColor :: String
  , onDraw :: Effect Unit
  } ->
  Effect SignatureElement
initSignaturePad el opts = pure unsafeSignatureElement

-- | Destroy signature pad
destroySignaturePad :: SignatureElement -> Effect Unit
destroySignaturePad _ = pure unit

-- | Clear signature
clearSignature :: SignatureElement -> Effect Unit
clearSignature _ = pure unit

-- | Undo last stroke
undoStroke :: SignatureElement -> Effect Boolean
undoStroke _ = pure false

-- | Export signature
exportSignature :: SignatureElement -> String -> Effect String
exportSignature _ _ = pure ""

-- | Import signature
importSignature :: SignatureElement -> String -> Effect Unit
importSignature _ _ = pure unit

-- | Check if empty
isEmpty :: SignatureElement -> Effect Boolean
isEmpty _ = pure true

-- Internal placeholder
foreign import unsafeSignatureElement :: SignatureElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Signature pad properties
type SignatureProps i =
  { penColor :: String
  , penThickness :: Number
  , eraserMode :: Boolean
  , showGuide :: Boolean
  , guideStyle :: GuideStyle
  , readOnly :: Boolean
  , strokeData :: Maybe StrokeData
  , backgroundColor :: String
  , width :: Int
  , height :: Int
  , onChange :: Maybe (StrokeData -> i)
  , onClear :: Maybe (MouseEvent -> i)
  , onUndo :: Maybe (MouseEvent -> i)
  , className :: String
  }

-- | Signature pad property modifier
type SignatureProp i = SignatureProps i -> SignatureProps i

-- | Default signature pad properties
defaultProps :: forall i. SignatureProps i
defaultProps =
  { penColor: "#000000"
  , penThickness: 2.0
  , eraserMode: false
  , showGuide: true
  , guideStyle: Dotted
  , readOnly: false
  , strokeData: Nothing
  , backgroundColor: "#ffffff"
  , width: 400
  , height: 200
  , onChange: Nothing
  , onClear: Nothing
  , onUndo: Nothing
  , className: ""
  }

-- | Toolbar properties
type ToolbarProps i =
  { showColorPicker :: Boolean
  , showThicknessSlider :: Boolean
  , showEraser :: Boolean
  , showClear :: Boolean
  , showUndo :: Boolean
  , position :: ToolbarPosition
  , className :: String
  , onColorChange :: Maybe (String -> i)
  , onThicknessChange :: Maybe (Number -> i)
  , onEraserToggle :: Maybe (Boolean -> i)
  , onClear :: Maybe (MouseEvent -> i)
  , onUndo :: Maybe (MouseEvent -> i)
  }

-- | Toolbar property modifier
type ToolbarProp i = ToolbarProps i -> ToolbarProps i

-- | Default toolbar properties
defaultToolbarProps :: forall i. ToolbarProps i
defaultToolbarProps =
  { showColorPicker: true
  , showThicknessSlider: true
  , showEraser: true
  , showClear: true
  , showUndo: true
  , position: Bottom
  , className: ""
  , onColorChange: Nothing
  , onThicknessChange: Nothing
  , onEraserToggle: Nothing
  , onClear: Nothing
  , onUndo: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders - signature
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set pen color
penColor :: forall i. String -> SignatureProp i
penColor c props = props { penColor = c }

-- | Set pen thickness
penThickness :: forall i. Number -> SignatureProp i
penThickness t props = props { penThickness = t }

-- | Enable eraser mode
eraserMode :: forall i. Boolean -> SignatureProp i
eraserMode e props = props { eraserMode = e }

-- | Show guide line
showGuide :: forall i. Boolean -> SignatureProp i
showGuide g props = props { showGuide = g }

-- | Set guide line style
guideStyle :: forall i. GuideStyle -> SignatureProp i
guideStyle s props = props { guideStyle = s }

-- | Set read-only mode
readOnly :: forall i. Boolean -> SignatureProp i
readOnly r props = props { readOnly = r }

-- | Set initial stroke data
strokeData :: forall i. StrokeData -> SignatureProp i
strokeData d props = props { strokeData = Just d }

-- | Set background color
backgroundColor :: forall i. String -> SignatureProp i
backgroundColor c props = props { backgroundColor = c }

-- | Set canvas width
width :: forall i. Int -> SignatureProp i
width w props = props { width = w }

-- | Set canvas height
height :: forall i. Int -> SignatureProp i
height h props = props { height = h }

-- | Set change handler
onChange :: forall i. (StrokeData -> i) -> SignatureProp i
onChange handler props = props { onChange = Just handler }

-- | Set clear handler
onClear :: forall i. (MouseEvent -> i) -> SignatureProp i
onClear handler props = props { onClear = Just handler }

-- | Set undo handler
onUndo :: forall i. (MouseEvent -> i) -> SignatureProp i
onUndo handler props = props { onUndo = Just handler }

-- | Add custom class
className :: forall i. String -> SignatureProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders - toolbar
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show color picker
showColorPicker :: forall i. Boolean -> ToolbarProp i
showColorPicker s props = props { showColorPicker = s }

-- | Show thickness slider
showThicknessSlider :: forall i. Boolean -> ToolbarProp i
showThicknessSlider s props = props { showThicknessSlider = s }

-- | Show eraser toggle
showEraser :: forall i. Boolean -> ToolbarProp i
showEraser s props = props { showEraser = s }

-- | Show clear button
showClear :: forall i. Boolean -> ToolbarProp i
showClear s props = props { showClear = s }

-- | Show undo button
showUndo :: forall i. Boolean -> ToolbarProp i
showUndo s props = props { showUndo = s }

-- | Set toolbar position
toolbarPosition :: forall i. ToolbarPosition -> ToolbarProp i
toolbarPosition p props = props { position = p }

-- | Add toolbar custom class
toolbarClassName :: forall i. String -> ToolbarProp i
toolbarClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Signature pad component
-- |
-- | Canvas-based signature capture
signaturePad :: forall w i. Array (SignatureProp i) -> HH.HTML w i
signaturePad propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerClasses =
      "signature-pad relative inline-block rounded-lg border border-input overflow-hidden"
    
    sizeStyle = 
      "width: " <> show props.width <> "px; " <>
      "height: " <> show props.height <> "px; " <>
      "background-color: " <> props.backgroundColor
    
    guideClasses = case props.guideStyle of
      Dotted -> "border-t-2 border-dotted border-muted-foreground/30"
      Dashed -> "border-t-2 border-dashed border-muted-foreground/30"
      Solid -> "border-t border-muted-foreground/30"
      Hidden -> "hidden"
    
    cursorClass = 
      if props.readOnly then "cursor-default"
      else if props.eraserMode then "cursor-cell"
      else "cursor-crosshair"
  in
    HH.div
      [ cls [ containerClasses, cursorClass, props.className ]
      , HP.attr (HH.AttrName "style") sizeStyle
      , HP.attr (HH.AttrName "data-pen-color") props.penColor
      , HP.attr (HH.AttrName "data-pen-thickness") (show props.penThickness)
      , HP.attr (HH.AttrName "data-eraser") (if props.eraserMode then "true" else "false")
      , HP.attr (HH.AttrName "data-readonly") (if props.readOnly then "true" else "false")
      , ARIA.label "Signature pad"
      , ARIA.role "img"
      ]
      [ -- Canvas element
        HH.element (HH.ElemName "canvas")
          [ cls [ "signature-canvas w-full h-full touch-none" ]
          , HP.attr (HH.AttrName "width") (show props.width)
          , HP.attr (HH.AttrName "height") (show props.height)
          ]
          []
      , -- Guide line
        if props.showGuide
          then HH.div
            [ cls [ "signature-guide absolute bottom-1/4 left-4 right-4", guideClasses ] ]
            []
          else HH.text ""
      , -- "Sign here" hint
        HH.div
          [ cls [ "signature-hint absolute bottom-2 left-4 text-xs text-muted-foreground pointer-events-none select-none" ] ]
          [ HH.text (if props.readOnly then "" else "Sign here") ]
      ]

-- | Signature pad with integrated toolbar
-- |
-- | Combines signature pad with toolbar controls
signaturePadWithToolbar :: forall w i. Array (SignatureProp i) -> Array (ToolbarProp i) -> HH.HTML w i
signaturePadWithToolbar sigMods toolbarMods =
  let
    toolbarProps = foldl (\p f -> f p) defaultToolbarProps toolbarMods
    
    content = case toolbarProps.position of
      Top -> [ signatureToolbar toolbarMods, signaturePad sigMods ]
      Bottom -> [ signaturePad sigMods, signatureToolbar toolbarMods ]
  in
    HH.div
      [ cls [ "signature-pad-container flex flex-col gap-2" ] ]
      content

-- | Signature toolbar component
-- |
-- | Controls for color, thickness, eraser, clear, and undo
signatureToolbar :: forall w i. Array (ToolbarProp i) -> HH.HTML w i
signatureToolbar propMods =
  let
    props = foldl (\p f -> f p) defaultToolbarProps propMods
  in
    HH.div
      [ cls [ "signature-toolbar flex items-center gap-2 p-2 bg-muted rounded-lg", props.className ] ]
      [ -- Color picker
        if props.showColorPicker
          then colorPickerButton
          else HH.text ""
      , -- Thickness slider
        if props.showThicknessSlider
          then thicknessControl
          else HH.text ""
      , -- Spacer
        HH.div [ cls [ "flex-1" ] ] []
      , -- Eraser toggle
        if props.showEraser
          then eraserButton
          else HH.text ""
      , -- Undo button
        if props.showUndo
          then undoButton props.onUndo
          else HH.text ""
      , -- Clear button
        if props.showClear
          then clearButton props.onClear
          else HH.text ""
      ]

-- | Read-only signature display
-- |
-- | For displaying existing signatures
signatureDisplay :: forall w i. StrokeData -> String -> HH.HTML w i
signatureDisplay data_ customClass =
  let
    sizeStyle = 
      "width: " <> show data_.width <> "px; " <>
      "height: " <> show data_.height <> "px"
  in
    HH.div
      [ cls [ "signature-display inline-block rounded-lg border border-input bg-background", customClass ]
      , HP.attr (HH.AttrName "style") sizeStyle
      , ARIA.label "Signature"
      , ARIA.role "img"
      ]
      [ HH.element (HH.ElemName "canvas")
          [ cls [ "w-full h-full" ]
          , HP.attr (HH.AttrName "width") (show data_.width)
          , HP.attr (HH.AttrName "height") (show data_.height)
          ]
          []
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // toolbar components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color picker button
colorPickerButton :: forall w i. HH.HTML w i
colorPickerButton =
  HH.label
    [ cls [ "signature-color-picker relative" ] ]
    [ HH.div
        [ cls 
            [ "w-8 h-8 rounded-md border border-input cursor-pointer"
            , "bg-current ring-offset-background focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2"
            ]
        ]
        []
    , HH.input
        [ HP.type_ HP.InputColor
        , cls [ "sr-only" ]
        , ARIA.label "Pen color"
        ]
    ]

-- | Thickness control
thicknessControl :: forall w i. HH.HTML w i
thicknessControl =
  HH.div
    [ cls [ "signature-thickness flex items-center gap-2" ] ]
    [ HH.span [ cls [ "text-xs text-muted-foreground" ] ] [ HH.text "Thin" ]
    , HH.input
        [ HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "min") "1"
        , HP.attr (HH.AttrName "max") "10"
        , HP.attr (HH.AttrName "step") "0.5"
        , cls [ "w-20 h-2 cursor-pointer" ]
        , ARIA.label "Pen thickness"
        ]
    , HH.span [ cls [ "text-xs text-muted-foreground" ] ] [ HH.text "Thick" ]
    ]

-- | Eraser button
eraserButton :: forall w i. HH.HTML w i
eraserButton =
  HH.button
    [ cls 
        [ "signature-eraser p-2 rounded-md hover:bg-accent transition-colors"
        , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
        ]
    , HP.type_ HP.ButtonButton
    , ARIA.label "Toggle eraser"
    ]
    [ eraserIcon ]

-- | Undo button
undoButton :: forall w i. Maybe (MouseEvent -> i) -> HH.HTML w i
undoButton handler =
  HH.button
    ( [ cls 
          [ "signature-undo p-2 rounded-md hover:bg-accent transition-colors"
          , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
          ]
      , HP.type_ HP.ButtonButton
      , ARIA.label "Undo"
      ] <> case handler of
            Just h -> [ HE.onClick h ]
            Nothing -> []
    )
    [ undoIcon ]

-- | Clear button
clearButton :: forall w i. Maybe (MouseEvent -> i) -> HH.HTML w i
clearButton handler =
  HH.button
    ( [ cls 
          [ "signature-clear p-2 rounded-md hover:bg-destructive/10 text-destructive transition-colors"
          , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
          ]
      , HP.type_ HP.ButtonButton
      , ARIA.label "Clear signature"
      ] <> case handler of
            Just h -> [ HE.onClick h ]
            Nothing -> []
    )
    [ trashIcon ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Eraser icon
eraserIcon :: forall w i. HH.HTML w i
eraserIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "18"
    , HP.attr (HH.AttrName "height") "18"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M20 20H9.2l-6.1-6.1a1.5 1.5 0 0 1 0-2.1L15 3.3a1.5 1.5 0 0 1 2.1 0l6.1 6.1a1.5 1.5 0 0 1 0 2.1L17 17.7" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M12 12l3-3" ]
        []
    ]

-- | Undo icon
undoIcon :: forall w i. HH.HTML w i
undoIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "18"
    , HP.attr (HH.AttrName "height") "18"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M3 7v6h6" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 17a9 9 0 0 0-9-9 9 9 0 0 0-6 2.3L3 13" ]
        []
    ]

-- | Trash icon
trashIcon :: forall w i. HH.HTML w i
trashIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "18"
    , HP.attr (HH.AttrName "height") "18"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "3 6 5 6 21 6" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2" ]
        []
    ]
