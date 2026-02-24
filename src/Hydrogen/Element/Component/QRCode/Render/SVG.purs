-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // qrcode // render // svg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code SVG Renderer — Pure Element output from QRMatrix.
-- |
-- | ## Design Philosophy
-- |
-- | This module converts a QRMatrix into an SVG Element. The rendering is
-- | completely pure — no FFI, no DOM manipulation, just data transformation.
-- |
-- | Supports multiple visual styles:
-- | - Classic: Sharp square modules
-- | - Rounded: Rounded corner squares
-- | - Dots: Circular modules
-- | - Custom: Any Schema shape as module
-- |
-- | ## Architecture
-- |
-- | ```
-- | QRMatrix → RenderConfig → Element msg
-- | ```
-- |
-- | The matrix provides the data (which modules are dark/light).
-- | The config provides the visual style (colors, shapes, sizes).
-- | The output is a pure SVG Element ready for any target.
-- |
-- | ## Dependencies
-- |
-- | - Matrix (QRMatrix, Module, getModule, matrixSize)
-- | - Element (SVG primitives)

module Hydrogen.Element.Component.QRCode.Render.SVG
  ( -- * Rendering
    renderQRCode
  , renderMatrix
  
  -- * Configuration
  , RenderConfig
  , defaultRenderConfig
  
  -- * Module Styles
  , ModuleStyle(Classic, Rounded, Dots)
  
  -- * Colors
  , QRColors
  , defaultColors
  , invertedColors
  
  -- * Position Utilities
  , ModulePosition
  , getDarkModulePositions
  , mapDarkModules
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl, (..))
import Data.Int (toNumber)

import Hydrogen.Render.Element as E
import Hydrogen.Element.Component.QRCode.Types
  ( QRMatrix
  , Module(Dark, Light, Reserved)
  , matrixSize
  , getModule
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // module styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visual style for QR code modules.
data ModuleStyle
  = Classic   -- ^ Sharp square modules (standard QR)
  | Rounded   -- ^ Rounded corner squares
  | Dots      -- ^ Circular modules

derive instance eqModuleStyle :: Eq ModuleStyle
derive instance ordModuleStyle :: Ord ModuleStyle

instance showModuleStyle :: Show ModuleStyle where
  show Classic = "Classic"
  show Rounded = "Rounded"
  show Dots = "Dots"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // colors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color configuration for QR code rendering.
type QRColors =
  { dark :: String       -- ^ Color for dark modules (usually black)
  , light :: String      -- ^ Color for light modules (usually white)
  , background :: String -- ^ Background color (quiet zone)
  }

-- | Default black-on-white colors.
defaultColors :: QRColors
defaultColors =
  { dark: "#000000"
  , light: "#ffffff"
  , background: "#ffffff"
  }

-- | Inverted white-on-black colors.
invertedColors :: QRColors
invertedColors =
  { dark: "#ffffff"
  , light: "#000000"
  , background: "#000000"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // render config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for QR code rendering.
type RenderConfig =
  { moduleSize :: Number    -- ^ Size of each module in pixels
  , quietZone :: Int        -- ^ Quiet zone width in modules (spec: 4)
  , style :: ModuleStyle    -- ^ Visual style
  , colors :: QRColors      -- ^ Color scheme
  , cornerRadius :: Number  -- ^ Corner radius for Rounded style (0-0.5)
  }

-- | Default render configuration.
-- |
-- | - 10px modules
-- | - 4-module quiet zone (QR spec minimum)
-- | - Classic square style
-- | - Black on white
defaultRenderConfig :: RenderConfig
defaultRenderConfig =
  { moduleSize: 10.0
  , quietZone: 4
  , style: Classic
  , colors: defaultColors
  , cornerRadius: 0.3
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a QRMatrix to an SVG Element.
-- |
-- | This is the main rendering function. It produces a complete SVG
-- | with proper viewBox, quiet zone, and all modules rendered.
renderQRCode :: forall msg. RenderConfig -> QRMatrix -> E.Element msg
renderQRCode cfg matrix =
  let
    size = matrixSize matrix
    totalSize = size + cfg.quietZone * 2
    viewBoxSize = toNumber totalSize * cfg.moduleSize
    viewBox = "0 0 " <> show viewBoxSize <> " " <> show viewBoxSize
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.attr "xmlns" "http://www.w3.org/2000/svg"
      , E.class_ "qr-code"
      ]
      [ -- Background (quiet zone)
        renderBackground cfg totalSize
      -- QR modules
      , renderMatrix cfg matrix
      ]

-- | Render just the matrix modules (without background/quiet zone).
-- |
-- | Useful for composing with custom backgrounds or overlays.
renderMatrix :: forall msg. RenderConfig -> QRMatrix -> E.Element msg
renderMatrix cfg matrix =
  let
    size = matrixSize matrix
    offset = toNumber cfg.quietZone * cfg.moduleSize
  in
    E.g_
      [ E.attr "transform" ("translate(" <> show offset <> "," <> show offset <> ")") ]
      (renderAllModules cfg matrix size)

-- | Render background rectangle for quiet zone.
renderBackground :: forall msg. RenderConfig -> Int -> E.Element msg
renderBackground cfg totalSize =
  let
    pixelSize = toNumber totalSize * cfg.moduleSize
  in
    E.rect_
      [ E.attr "x" "0"
      , E.attr "y" "0"
      , E.attr "width" (show pixelSize)
      , E.attr "height" (show pixelSize)
      , E.attr "fill" cfg.colors.background
      ]

-- | Render all modules in the matrix.
renderAllModules :: forall msg. RenderConfig -> QRMatrix -> Int -> Array (E.Element msg)
renderAllModules cfg matrix size =
  foldl (renderRow cfg matrix size) [] (0 .. (size - 1))

-- | Render a single row of modules.
renderRow :: forall msg. RenderConfig -> QRMatrix -> Int -> Array (E.Element msg) -> Int -> Array (E.Element msg)
renderRow cfg matrix size acc row =
  foldl (renderCell cfg matrix row) acc (0 .. (size - 1))

-- | Render a single module cell.
renderCell :: forall msg. RenderConfig -> QRMatrix -> Int -> Array (E.Element msg) -> Int -> Array (E.Element msg)
renderCell cfg matrix row acc col =
  let
    mod = getModule row col matrix
  in
    case mod of
      Dark _ -> acc <> [renderDarkModule cfg row col]
      Light _ -> acc  -- Light modules are background, no need to render
      Reserved -> acc -- Reserved shouldn't appear in final matrix

-- | Render a dark module based on style.
renderDarkModule :: forall msg. RenderConfig -> Int -> Int -> E.Element msg
renderDarkModule cfg row col =
  case cfg.style of
    Classic -> renderSquare cfg row col
    Rounded -> renderRounded cfg row col
    Dots -> renderDot cfg row col

-- | Render a classic square module.
renderSquare :: forall msg. RenderConfig -> Int -> Int -> E.Element msg
renderSquare cfg row col =
  let
    x = toNumber col * cfg.moduleSize
    y = toNumber row * cfg.moduleSize
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show y)
      , E.attr "width" (show cfg.moduleSize)
      , E.attr "height" (show cfg.moduleSize)
      , E.attr "fill" cfg.colors.dark
      ]

-- | Render a rounded corner module.
renderRounded :: forall msg. RenderConfig -> Int -> Int -> E.Element msg
renderRounded cfg row col =
  let
    x = toNumber col * cfg.moduleSize
    y = toNumber row * cfg.moduleSize
    r = cfg.moduleSize * cfg.cornerRadius
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show y)
      , E.attr "width" (show cfg.moduleSize)
      , E.attr "height" (show cfg.moduleSize)
      , E.attr "rx" (show r)
      , E.attr "ry" (show r)
      , E.attr "fill" cfg.colors.dark
      ]

-- | Render a circular dot module.
renderDot :: forall msg. RenderConfig -> Int -> Int -> E.Element msg
renderDot cfg row col =
  let
    cx = toNumber col * cfg.moduleSize + cfg.moduleSize / 2.0
    cy = toNumber row * cfg.moduleSize + cfg.moduleSize / 2.0
    r = cfg.moduleSize / 2.0 * 0.85  -- Slightly smaller for spacing
  in
    E.circle_
      [ E.attr "cx" (show cx)
      , E.attr "cy" (show cy)
      , E.attr "r" (show r)
      , E.attr "fill" cfg.colors.dark
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // position utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Module position with pixel coordinates.
type ModulePosition =
  { row :: Int
  , col :: Int
  , x :: Number
  , y :: Number
  , isDark :: Boolean
  }

-- | Get all dark module positions with pixel coordinates.
-- |
-- | Useful for custom rendering pipelines that need position data.
getDarkModulePositions :: RenderConfig -> QRMatrix -> Array ModulePosition
getDarkModulePositions cfg matrix =
  let
    size = matrixSize matrix
    rows = 0 .. (size - 1)
    allPositions = foldl (collectRowPositions cfg matrix size) [] rows
  in
    allPositions
  where
    collectRowPositions :: RenderConfig -> QRMatrix -> Int -> Array ModulePosition -> Int -> Array ModulePosition
    collectRowPositions config m size acc row =
      let
        cols = 0 .. (size - 1)
        rowPositions = map (makePosition config m row) cols
        darkOnly = foldl (\a p -> if p.isDark then a <> [p] else a) [] rowPositions
      in
        acc <> darkOnly
    
    makePosition :: RenderConfig -> QRMatrix -> Int -> Int -> ModulePosition
    makePosition config m row col =
      let
        mod = getModule row col m
        dark = case mod of
          Dark _ -> true
          _ -> false
      in
        { row
        , col
        , x: toNumber col * config.moduleSize
        , y: toNumber row * config.moduleSize
        , isDark: dark
        }

-- | Map a rendering function over all dark modules.
-- |
-- | This allows custom module renderers to be applied uniformly.
mapDarkModules :: forall a. (Int -> Int -> Number -> Number -> a) -> RenderConfig -> QRMatrix -> Array a
mapDarkModules f cfg matrix =
  let
    positions = getDarkModulePositions cfg matrix
  in
    map (\p -> f p.row p.col p.x p.y) positions
