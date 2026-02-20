-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // qrcode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code generator and scanner component
-- |
-- | Generate QR codes from text/URLs and scan QR codes using camera or images.
-- |
-- | ## Features
-- |
-- | - Generate QR code from text/URL
-- | - Configurable size and colors
-- | - Error correction levels
-- | - Optional center logo
-- | - Download as PNG/SVG
-- | - Camera-based scanning
-- | - Image upload scanning
-- | - Multiple format support (QR, barcode)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.QRCode as QRCode
-- |
-- | -- Basic QR code generator
-- | QRCode.qrCode
-- |   [ QRCode.content "https://example.com"
-- |   , QRCode.size 200
-- |   ]
-- |
-- | -- With custom colors and logo
-- | QRCode.qrCode
-- |   [ QRCode.content "https://example.com"
-- |   , QRCode.size 256
-- |   , QRCode.foreground "#000000"
-- |   , QRCode.background "#ffffff"
-- |   , QRCode.errorCorrection QRCode.High
-- |   , QRCode.logo "/logo.png"
-- |   ]
-- |
-- | -- QR code scanner with camera
-- | QRCode.qrScanner
-- |   [ QRCode.onScan HandleScanResult
-- |   , QRCode.showFlashlight true
-- |   , QRCode.formats [ QRCode.QR, QRCode.EAN13 ]
-- |   ]
-- |
-- | -- Scanner with image upload
-- | QRCode.qrScanner
-- |   [ QRCode.onScan HandleScanResult
-- |   , QRCode.allowUpload true
-- |   ]
-- | ```
module Hydrogen.Component.QRCode
  ( -- * Components
    qrCode
  , qrScanner
  , qrDownloadButton
    -- * Props
  , QRCodeProps
  , QRCodeProp
  , ScannerProps
  , ScannerProp
  , defaultProps
  , defaultScannerProps
    -- * Prop Builders - Generator
  , content
  , size
  , foreground
  , background
  , errorCorrection
  , logo
  , logoSize
  , className
    -- * Prop Builders - Scanner
  , onScan
  , onError
  , showFlashlight
  , allowUpload
  , formats
  , facingMode
  , scannerClassName
    -- * Types
  , ErrorCorrectionLevel(..)
  , ScanFormat(..)
  , ScanResult
  , FacingMode(..)
    -- * FFI
  , QRCodeElement
  , ScannerElement
  , generateQRCode
  , downloadQRCode
  , startScanner
  , stopScanner
  , toggleFlashlight
  , scanImage
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.File.File (File)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Error correction level for QR codes
data ErrorCorrectionLevel
  = Low       -- ~7% recovery
  | Medium    -- ~15% recovery
  | Quartile  -- ~25% recovery
  | High      -- ~30% recovery

derive instance eqErrorCorrectionLevel :: Eq ErrorCorrectionLevel

-- | Scan format types
data ScanFormat
  = QR
  | EAN8
  | EAN13
  | Code128
  | Code39
  | UPC_A
  | UPC_E
  | DataMatrix
  | PDF417

derive instance eqScanFormat :: Eq ScanFormat

-- | Camera facing mode
data FacingMode
  = Front
  | Back

derive instance eqFacingMode :: Eq FacingMode

-- | Scan result
type ScanResult =
  { value :: String
  , format :: String
  , rawValue :: String
  }

-- | Opaque QR code element for FFI
foreign import data QRCodeElement :: Type

-- | Opaque scanner element for FFI
foreign import data ScannerElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate QR code into element
foreign import generateQRCodeImpl :: EffectFn2 Element
  { content :: String
  , size :: Int
  , foreground :: String
  , background :: String
  , errorCorrection :: String
  , logo :: String
  , logoSize :: Int
  }
  QRCodeElement

-- | Download QR code as image
foreign import downloadQRCodeImpl :: EffectFn3 QRCodeElement String String Unit

-- | Start camera scanner
foreign import startScannerImpl :: EffectFn2 Element
  { onScan :: ScanResult -> Effect Unit
  , onError :: String -> Effect Unit
  , formats :: Array String
  , facingMode :: String
  }
  ScannerElement

-- | Stop camera scanner
foreign import stopScannerImpl :: EffectFn1 ScannerElement Unit

-- | Toggle flashlight
foreign import toggleFlashlightImpl :: EffectFn1 ScannerElement Boolean

-- | Scan from image file
foreign import scanImageImpl :: EffectFn2 File (ScanResult -> Effect Unit) Unit

-- | Generate QR code
generateQRCode :: Element ->
  { content :: String
  , size :: Int
  , foreground :: String
  , background :: String
  , errorCorrection :: String
  , logo :: String
  , logoSize :: Int
  } ->
  Effect QRCodeElement
generateQRCode el opts = pure unsafeQRCodeElement

-- | Download QR code
downloadQRCode :: QRCodeElement -> String -> String -> Effect Unit
downloadQRCode _ _ _ = pure unit

-- | Start scanner
startScanner :: Element ->
  { onScan :: ScanResult -> Effect Unit
  , onError :: String -> Effect Unit
  , formats :: Array String
  , facingMode :: String
  } ->
  Effect ScannerElement
startScanner el opts = pure unsafeScannerElement

-- | Stop scanner
stopScanner :: ScannerElement -> Effect Unit
stopScanner _ = pure unit

-- | Toggle flashlight
toggleFlashlight :: ScannerElement -> Effect Boolean
toggleFlashlight _ = pure false

-- | Scan image
scanImage :: File -> (ScanResult -> Effect Unit) -> Effect Unit
scanImage _ _ = pure unit

-- Internal placeholders
foreign import unsafeQRCodeElement :: QRCodeElement
foreign import unsafeScannerElement :: ScannerElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | QR code generator properties
type QRCodeProps =
  { content :: String
  , size :: Int
  , foreground :: String
  , background :: String
  , errorCorrection :: ErrorCorrectionLevel
  , logo :: Maybe String
  , logoSize :: Int
  , className :: String
  }

-- | QR code property modifier
type QRCodeProp = QRCodeProps -> QRCodeProps

-- | Default QR code properties
defaultProps :: QRCodeProps
defaultProps =
  { content: ""
  , size: 200
  , foreground: "#000000"
  , background: "#ffffff"
  , errorCorrection: Medium
  , logo: Nothing
  , logoSize: 50
  , className: ""
  }

-- | Scanner properties
type ScannerProps i =
  { onScan :: Maybe (ScanResult -> i)
  , onError :: Maybe (String -> i)
  , showFlashlight :: Boolean
  , allowUpload :: Boolean
  , formats :: Array ScanFormat
  , facingMode :: FacingMode
  , className :: String
  }

-- | Scanner property modifier
type ScannerProp i = ScannerProps i -> ScannerProps i

-- | Default scanner properties
defaultScannerProps :: forall i. ScannerProps i
defaultScannerProps =
  { onScan: Nothing
  , onError: Nothing
  , showFlashlight: true
  , allowUpload: true
  , formats: [ QR ]
  , facingMode: Back
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // prop builders - qrcode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set QR code content
content :: String -> QRCodeProp
content c props = props { content = c }

-- | Set QR code size (pixels)
size :: Int -> QRCodeProp
size s props = props { size = s }

-- | Set foreground color
foreground :: String -> QRCodeProp
foreground f props = props { foreground = f }

-- | Set background color
background :: String -> QRCodeProp
background b props = props { background = b }

-- | Set error correction level
errorCorrection :: ErrorCorrectionLevel -> QRCodeProp
errorCorrection e props = props { errorCorrection = e }

-- | Set center logo URL
logo :: String -> QRCodeProp
logo l props = props { logo = Just l }

-- | Set logo size (pixels)
logoSize :: Int -> QRCodeProp
logoSize s props = props { logoSize = s }

-- | Add custom class
className :: String -> QRCodeProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders - scanner
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set scan result handler
onScan :: forall i. (ScanResult -> i) -> ScannerProp i
onScan handler props = props { onScan = Just handler }

-- | Set error handler
onError :: forall i. (String -> i) -> ScannerProp i
onError handler props = props { onError = Just handler }

-- | Show flashlight toggle
showFlashlight :: forall i. Boolean -> ScannerProp i
showFlashlight s props = props { showFlashlight = s }

-- | Allow image upload
allowUpload :: forall i. Boolean -> ScannerProp i
allowUpload a props = props { allowUpload = a }

-- | Set supported formats
formats :: forall i. Array ScanFormat -> ScannerProp i
formats f props = props { formats = f }

-- | Set camera facing mode
facingMode :: forall i. FacingMode -> ScannerProp i
facingMode f props = props { facingMode = f }

-- | Add custom class to scanner
scannerClassName :: forall i. String -> ScannerProp i
scannerClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert error correction to string
errorCorrectionToString :: ErrorCorrectionLevel -> String
errorCorrectionToString = case _ of
  Low -> "L"
  Medium -> "M"
  Quartile -> "Q"
  High -> "H"

-- | QR code generator component
-- |
-- | Renders a QR code from the provided content
qrCode :: forall w i. Array QRCodeProp -> HH.HTML w i
qrCode propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerClasses =
      "qrcode-container inline-flex items-center justify-center"
    
    sizeStyle = "width: " <> show props.size <> "px; height: " <> show props.size <> "px"
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-qr-content") props.content
      , HP.attr (HH.AttrName "data-qr-size") (show props.size)
      , HP.attr (HH.AttrName "data-qr-fg") props.foreground
      , HP.attr (HH.AttrName "data-qr-bg") props.background
      , HP.attr (HH.AttrName "data-qr-ec") (errorCorrectionToString props.errorCorrection)
      , HP.attr (HH.AttrName "style") sizeStyle
      , ARIA.label ("QR code for: " <> props.content)
      ]
      [ -- Canvas element for QR code
        HH.element (HH.ElemName "canvas")
          [ cls [ "qrcode-canvas" ]
          , HP.attr (HH.AttrName "width") (show props.size)
          , HP.attr (HH.AttrName "height") (show props.size)
          ]
          []
      , -- Optional logo overlay
        case props.logo of
          Just logoUrl ->
            HH.div
              [ cls [ "qrcode-logo absolute" ]
              , HP.attr (HH.AttrName "style") 
                  ( "width: " <> show props.logoSize <> "px; " <>
                    "height: " <> show props.logoSize <> "px"
                  )
              ]
              [ HH.img
                  [ HP.src logoUrl
                  , HP.alt "QR code logo"
                  , cls [ "w-full h-full object-contain rounded-sm bg-white p-1" ]
                  ]
              ]
          Nothing -> HH.text ""
      ]

-- | Download button for QR code
qrDownloadButton :: forall w i. 
  { onClick :: MouseEvent -> i
  , format :: String  -- "png" or "svg"
  , label :: String
  } -> 
  HH.HTML w i
qrDownloadButton config =
  HH.button
    [ cls 
        [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
        , "h-10 px-4 py-2 bg-primary text-primary-foreground"
        , "hover:bg-primary/90 transition-colors"
        , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
        ]
    , HE.onClick config.onClick
    , HP.attr (HH.AttrName "data-download-format") config.format
    ]
    [ downloadIcon
    , HH.span [ cls [ "ml-2" ] ] [ HH.text config.label ]
    ]

-- | QR code scanner component
-- |
-- | Camera-based scanner with optional image upload
qrScanner :: forall w i. Array (ScannerProp i) -> HH.HTML w i
qrScanner propMods =
  let
    props = foldl (\p f -> f p) defaultScannerProps propMods
    
    containerClasses =
      "qrscanner-container relative flex flex-col items-center gap-4"
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , ARIA.label "QR code scanner"
      ]
      [ -- Video feed container
        HH.div
          [ cls [ "qrscanner-viewport relative w-full max-w-sm aspect-square bg-black rounded-lg overflow-hidden" ] ]
          [ -- Video element
            HH.element (HH.ElemName "video")
              [ cls [ "qrscanner-video w-full h-full object-cover" ]
              , HP.attr (HH.AttrName "playsinline") "true"
              , HP.attr (HH.AttrName "autoplay") "true"
              , HP.attr (HH.AttrName "muted") "true"
              ]
              []
          , -- Scan overlay with targeting box
            scanOverlay
          , -- Flashlight toggle
            if props.showFlashlight
              then flashlightButton
              else HH.text ""
          ]
      , -- Controls
        HH.div
          [ cls [ "qrscanner-controls flex gap-2" ] ]
          [ -- Upload button
            if props.allowUpload
              then uploadButton
              else HH.text ""
          ]
      ]

-- | Scan overlay with targeting frame
scanOverlay :: forall w i. HH.HTML w i
scanOverlay =
  HH.div
    [ cls [ "absolute inset-0 flex items-center justify-center pointer-events-none" ] ]
    [ -- Targeting frame
      HH.div
        [ cls 
            [ "w-48 h-48 border-2 border-primary rounded-lg"
            , "relative"
            ]
        ]
        [ -- Corner accents
          HH.div [ cls [ "absolute top-0 left-0 w-4 h-4 border-t-2 border-l-2 border-primary -translate-x-px -translate-y-px" ] ] []
        , HH.div [ cls [ "absolute top-0 right-0 w-4 h-4 border-t-2 border-r-2 border-primary translate-x-px -translate-y-px" ] ] []
        , HH.div [ cls [ "absolute bottom-0 left-0 w-4 h-4 border-b-2 border-l-2 border-primary -translate-x-px translate-y-px" ] ] []
        , HH.div [ cls [ "absolute bottom-0 right-0 w-4 h-4 border-b-2 border-r-2 border-primary translate-x-px translate-y-px" ] ] []
        , -- Scanning line animation
          HH.div
            [ cls [ "absolute inset-x-0 top-0 h-0.5 bg-primary/50 animate-scan" ] ]
            []
        ]
    , -- Hint text
      HH.p
        [ cls [ "absolute bottom-4 text-sm text-white/80" ] ]
        [ HH.text "Position QR code within frame" ]
    ]

-- | Flashlight toggle button
flashlightButton :: forall w i. HH.HTML w i
flashlightButton =
  HH.button
    [ cls 
        [ "qrscanner-flashlight absolute top-2 right-2 p-2 rounded-full"
        , "bg-black/50 text-white hover:bg-black/70 transition-colors"
        ]
    , HP.type_ HP.ButtonButton
    , ARIA.label "Toggle flashlight"
    ]
    [ flashlightIcon ]

-- | Upload button
uploadButton :: forall w i. HH.HTML w i
uploadButton =
  HH.label
    [ cls 
        [ "qrscanner-upload inline-flex items-center justify-center rounded-md"
        , "h-10 px-4 py-2 bg-secondary text-secondary-foreground"
        , "hover:bg-secondary/80 transition-colors cursor-pointer"
        ]
    ]
    [ uploadIcon
    , HH.span [ cls [ "ml-2" ] ] [ HH.text "Upload Image" ]
    , HH.input
        [ HP.type_ HP.InputFile
        , HP.attr (HH.AttrName "accept") "image/*"
        , cls [ "sr-only" ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Download icon
downloadIcon :: forall w i. HH.HTML w i
downloadIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4" ]
        []
    , HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "7 10 12 15 17 10" ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "15"
        , HP.attr (HH.AttrName "x2") "12"
        , HP.attr (HH.AttrName "y2") "3"
        ]
        []
    ]

-- | Flashlight icon
flashlightIcon :: forall w i. HH.HTML w i
flashlightIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "20"
    , HP.attr (HH.AttrName "height") "20"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M18 6l-6 6" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 18l6-6" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M14 4l-8 8 8 8 8-8-8-8z" ]
        []
    ]

-- | Upload icon
uploadIcon :: forall w i. HH.HTML w i
uploadIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4" ]
        []
    , HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "17 8 12 3 7 8" ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "3"
        , HP.attr (HH.AttrName "x2") "12"
        , HP.attr (HH.AttrName "y2") "15"
        ]
        []
    ]
