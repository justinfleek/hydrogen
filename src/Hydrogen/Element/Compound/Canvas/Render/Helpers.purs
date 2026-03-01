-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // element // compound // canvas // render // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Helpers — Utility functions for canvas rendering.
-- |
-- | ## Purpose
-- |
-- | Provides helper functions used across rendering submodules:
-- | - Sorting and comparison utilities
-- | - CSS conversion functions
-- | - Path generation
-- | - Array utilities
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject, CanvasObjectId)
-- | - Schema.Color.Blend (BlendMode)
-- | - Schema.Graph.Viewport (ViewportState)

module Hydrogen.Element.Compound.Canvas.Render.Helpers
  ( -- * Sorting
    sortByZIndex
  
  -- * CSS Conversion
  , blendModeToCSS
  , viewportTransform
  , handleCursor
  
  -- * Object Utilities
  , showObjectId
  
  -- * Path Generation
  , lassoToPath
  
  -- * Array Utilities
  , arrayIndex
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (+)
  , ($)
  , (||)
  )

import Data.Array (length, sortBy, foldl, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering(GT, LT, EQ))

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.Selection as Selection
import Hydrogen.Schema.Color.Blend as Blend
import Hydrogen.Schema.Graph.Viewport as VP

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // sorting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort objects by zIndex ascending.
sortByZIndex :: Array Types.CanvasObject -> Array Types.CanvasObject
sortByZIndex = sortBy compareZIndex
  where
    compareZIndex a b =
      let za = Types.objectZIndex a
          zb = Types.objectZIndex b
      in if za < zb then LT
         else if za > zb then GT
         else EQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert blend mode to CSS mix-blend-mode value.
blendModeToCSS :: Blend.BlendMode -> String
blendModeToCSS Blend.Normal = "normal"
blendModeToCSS Blend.Multiply = "multiply"
blendModeToCSS Blend.Screen = "screen"
blendModeToCSS Blend.Overlay = "overlay"
blendModeToCSS Blend.Darken = "darken"
blendModeToCSS Blend.Lighten = "lighten"
blendModeToCSS Blend.ColorDodge = "color-dodge"
blendModeToCSS Blend.ColorBurn = "color-burn"
blendModeToCSS Blend.HardLight = "hard-light"
blendModeToCSS Blend.SoftLight = "soft-light"
blendModeToCSS Blend.Difference = "difference"
blendModeToCSS Blend.Exclusion = "exclusion"
blendModeToCSS _ = "normal"  -- Fallback for non-CSS blend modes

-- | Generate viewport transform CSS.
viewportTransform :: VP.ViewportState -> String
viewportTransform vp = 
  let 
    zoom = VP.zoomLevel (VP.viewportZoomLevel vp)
    pan = VP.viewportPan vp
  in "translate(" <> show (VP.panX pan) <> "px, " <> show (VP.panY pan) <> "px) " <>
     "scale(" <> show zoom <> ")"

-- | Get cursor for handle type.
handleCursor :: Selection.HandleType -> String
handleCursor Selection.HandleTopLeft = "nwse-resize"
handleCursor Selection.HandleTopCenter = "ns-resize"
handleCursor Selection.HandleTopRight = "nesw-resize"
handleCursor Selection.HandleMiddleLeft = "ew-resize"
handleCursor Selection.HandleMiddleRight = "ew-resize"
handleCursor Selection.HandleBottomLeft = "nesw-resize"
handleCursor Selection.HandleBottomCenter = "ns-resize"
handleCursor Selection.HandleBottomRight = "nwse-resize"
handleCursor Selection.HandleRotation = "grab"
handleCursor Selection.HandleCenter = "move"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // object utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show object ID as string.
showObjectId :: Types.CanvasObjectId -> String
showObjectId (Types.CanvasObjectId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert lasso points to SVG path.
lassoToPath :: Array { x :: Number, y :: Number } -> String
lassoToPath points =
  foldl buildPath "" (indexPoints points)
  where
    buildPath acc item =
      if item.idx == 0
        then "M " <> show item.point.x <> " " <> show item.point.y
        else acc <> " L " <> show item.point.x <> " " <> show item.point.y
    
    indexPoints pts = indexHelper pts 0 []
    
    indexHelper pts idx acc =
      case arrayIndex pts idx of
        Nothing -> acc
        Just p -> indexHelper pts (idx + 1) (snoc acc { idx, point: p })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe array index.
arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex arr idx =
  if idx < 0 || idx >= length arr
    then Nothing
    else arrayIndexUnsafe arr idx

-- | Array index (using foldl for safety).
arrayIndexUnsafe :: forall a. Array a -> Int -> Maybe a
arrayIndexUnsafe arr idx =
  let result = foldl (\acc item ->
        case acc of
          { found: Just _, i: _ } -> acc
          { found: Nothing, i } ->
            if i == idx 
              then { found: Just item, i: i + 1 }
              else { found: Nothing, i: i + 1 }
      ) { found: Nothing, i: 0 } arr
  in result.found
