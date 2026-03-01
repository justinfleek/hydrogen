-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // render // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Types — Messages and configuration for canvas rendering.
-- |
-- | ## Purpose
-- |
-- | Defines the foundational types for canvas rendering:
-- | - CanvasMsg: Messages emitted by canvas interactions
-- | - RenderConfig: Configuration for rendering appearance
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasTool, CanvasObjectId)

module Hydrogen.Element.Compound.Canvas.Render.Types
  ( -- * Canvas Messages
    CanvasMsg(..)
  
  -- * Render Config
  , RenderConfig
  , defaultRenderConfig
  , withHandleSize
  , withGridOpacity
  , withSelectionColor
  , withGuideColor
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , max
  , min
  )

import Hydrogen.Element.Compound.Canvas.Types as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // canvas messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages the canvas can emit.
data CanvasMsg
  = CanvasMouseDown { x :: Number, y :: Number, button :: Int }
  | CanvasMouseMove { x :: Number, y :: Number }
  | CanvasMouseUp { x :: Number, y :: Number, button :: Int }
  | CanvasWheel { deltaX :: Number, deltaY :: Number, ctrlKey :: Boolean }
  | CanvasKeyDown { key :: String, ctrlKey :: Boolean, shiftKey :: Boolean, altKey :: Boolean }
  | CanvasKeyUp { key :: String }
  | CanvasTouchStart { touches :: Array { x :: Number, y :: Number } }
  | CanvasTouchMove { touches :: Array { x :: Number, y :: Number } }
  | CanvasTouchEnd { touches :: Array { x :: Number, y :: Number } }
  | CanvasToolChange Types.CanvasTool
  | CanvasObjectSelect Types.CanvasObjectId
  | CanvasObjectDeselect Types.CanvasObjectId
  | CanvasZoomIn
  | CanvasZoomOut
  | CanvasZoomFit
  | CanvasPanStart { x :: Number, y :: Number }
  | CanvasPanEnd
  | CanvasUndo
  | CanvasRedo

derive instance eqCanvasMsg :: Eq CanvasMsg

instance showCanvasMsg :: Show CanvasMsg where
  show (CanvasMouseDown p) = "MouseDown(" <> show p.x <> "," <> show p.y <> ")"
  show (CanvasMouseMove p) = "MouseMove(" <> show p.x <> "," <> show p.y <> ")"
  show (CanvasMouseUp p) = "MouseUp(" <> show p.x <> "," <> show p.y <> ")"
  show (CanvasWheel w) = "Wheel(" <> show w.deltaY <> ")"
  show (CanvasKeyDown k) = "KeyDown(" <> k.key <> ")"
  show (CanvasKeyUp k) = "KeyUp(" <> k.key <> ")"
  show (CanvasTouchStart _) = "TouchStart"
  show (CanvasTouchMove _) = "TouchMove"
  show (CanvasTouchEnd _) = "TouchEnd"
  show (CanvasToolChange t) = "ToolChange(" <> show t <> ")"
  show (CanvasObjectSelect id) = "ObjectSelect(" <> show id <> ")"
  show (CanvasObjectDeselect id) = "ObjectDeselect(" <> show id <> ")"
  show CanvasZoomIn = "ZoomIn"
  show CanvasZoomOut = "ZoomOut"
  show CanvasZoomFit = "ZoomFit"
  show (CanvasPanStart p) = "PanStart(" <> show p.x <> "," <> show p.y <> ")"
  show CanvasPanEnd = "PanEnd"
  show CanvasUndo = "Undo"
  show CanvasRedo = "Redo"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // render config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for rendering.
type RenderConfig =
  { handleSize :: Number           -- Size of selection handles in pixels
  , gridOpacity :: Number          -- Opacity of grid lines (0.0-1.0)
  , selectionColor :: String       -- Color of selection outline (hex)
  , selectionWidth :: Number       -- Width of selection outline
  , guideColor :: String           -- Color of guides (hex)
  , marqueeColor :: String         -- Color of marquee rectangle
  , marqueeOpacity :: Number       -- Opacity of marquee fill
  , showRulers :: Boolean          -- Whether to render rulers
  , rulerSize :: Number            -- Size of rulers in pixels
  , antialiased :: Boolean         -- Whether to use antialiasing
  }

-- | Default render configuration.
defaultRenderConfig :: RenderConfig
defaultRenderConfig =
  { handleSize: 8.0
  , gridOpacity: 0.3
  , selectionColor: "#3b82f6"      -- Blue-500
  , selectionWidth: 1.0
  , guideColor: "#06b6d4"          -- Cyan-500
  , marqueeColor: "#3b82f6"        -- Blue-500
  , marqueeOpacity: 0.1
  , showRulers: true
  , rulerSize: 20.0
  , antialiased: true
  }

-- | Set handle size.
withHandleSize :: Number -> RenderConfig -> RenderConfig
withHandleSize size config = config { handleSize = size }

-- | Set grid opacity.
withGridOpacity :: Number -> RenderConfig -> RenderConfig
withGridOpacity opacity config = config { gridOpacity = clamp01 opacity }

-- | Set selection color.
withSelectionColor :: String -> RenderConfig -> RenderConfig
withSelectionColor color config = config { selectionColor = color }

-- | Set guide color.
withGuideColor :: String -> RenderConfig -> RenderConfig
withGuideColor color config = config { guideColor = color }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to 0.0-1.0 range.
clamp01 :: Number -> Number
clamp01 n = max 0.0 (min 1.0 n)
