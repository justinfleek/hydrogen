-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // canvas // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Bounds — The finite region where everything exists.
-- |
-- | ## Design Philosophy
-- |
-- | The canvas is bounded. Nothing exists outside it.
-- | All coordinates are relative to canvas origin (top-left or center).
-- |
-- | ## Coordinate Systems
-- |
-- | - **Screen**: Origin at top-left, Y increases downward
-- | - **Cartesian**: Origin at center, Y increases upward
-- | - **Normalized**: 0-1 range, origin at top-left
-- |
-- | ## Dependencies
-- | - Prelude

module Hydrogen.Schema.Canvas.Bounds
  ( -- * CanvasBounds
    CanvasBounds
  , mkCanvasBounds
  , boundsWidth
  , boundsHeight
  , boundsArea
  , boundsAspectRatio
  , boundsCenter
  
  -- * Coordinate Systems
  , CoordinateSystem(..)
  , allCoordinateSystems
  
  -- * Point Queries
  , isInBounds
  , clampToBounds
  , normalizePoint
  , denormalizePoint
  
  -- * Common Sizes
  , bounds1080p
  , bounds4K
  , boundsSquare1K
  , boundsA4Portrait
  , boundsA4Landscape
  
  -- * Grid Subdivision
  , subdivideIntoCells
  , cellAtPoint
  , cellCenter
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , max
  , min
  )

import Data.Int (floor, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // canvas bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | The finite region of the canvas.
-- |
-- | All content exists within these bounds.
-- | Origin is at top-left (screen coordinates).
type CanvasBounds =
  { width :: Number       -- ^ Width in pixels
  , height :: Number      -- ^ Height in pixels
  , originX :: Number     -- ^ X offset (usually 0)
  , originY :: Number     -- ^ Y offset (usually 0)
  }

-- | Create canvas bounds with validation.
mkCanvasBounds :: Number -> Number -> CanvasBounds
mkCanvasBounds w h =
  { width: max 1.0 w
  , height: max 1.0 h
  , originX: 0.0
  , originY: 0.0
  }

-- | Get canvas width.
boundsWidth :: CanvasBounds -> Number
boundsWidth b = b.width

-- | Get canvas height.
boundsHeight :: CanvasBounds -> Number
boundsHeight b = b.height

-- | Get canvas area in square pixels.
boundsArea :: CanvasBounds -> Number
boundsArea b = b.width * b.height

-- | Get aspect ratio (width / height).
boundsAspectRatio :: CanvasBounds -> Number
boundsAspectRatio b = b.width / b.height

-- | Get center point of canvas.
boundsCenter :: CanvasBounds -> { x :: Number, y :: Number }
boundsCenter b =
  { x: b.originX + b.width / 2.0
  , y: b.originY + b.height / 2.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // coordinate systems
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coordinate system for the canvas.
data CoordinateSystem
  = ScreenCoords      -- ^ Origin top-left, Y down (default)
  | CartesianCoords   -- ^ Origin center, Y up
  | NormalizedCoords  -- ^ 0-1 range, origin top-left

derive instance eqCoordinateSystem :: Eq CoordinateSystem
derive instance ordCoordinateSystem :: Ord CoordinateSystem

instance showCoordinateSystem :: Show CoordinateSystem where
  show ScreenCoords = "screen"
  show CartesianCoords = "cartesian"
  show NormalizedCoords = "normalized"

-- | All coordinate system variants.
allCoordinateSystems :: Array CoordinateSystem
allCoordinateSystems = [ScreenCoords, CartesianCoords, NormalizedCoords]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // point queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is within canvas bounds.
isInBounds :: CanvasBounds -> Number -> Number -> Boolean
isInBounds b x y =
  x >= b.originX && x < (b.originX + b.width) &&
  y >= b.originY && y < (b.originY + b.height)

-- | Clamp a point to stay within bounds.
clampToBounds :: CanvasBounds -> Number -> Number -> { x :: Number, y :: Number }
clampToBounds b x y =
  { x: max b.originX (min (b.originX + b.width - 1.0) x)
  , y: max b.originY (min (b.originY + b.height - 1.0) y)
  }

-- | Convert screen coordinates to normalized (0-1).
normalizePoint :: CanvasBounds -> Number -> Number -> { x :: Number, y :: Number }
normalizePoint b x y =
  { x: (x - b.originX) / b.width
  , y: (y - b.originY) / b.height
  }

-- | Convert normalized coordinates to screen pixels.
denormalizePoint :: CanvasBounds -> Number -> Number -> { x :: Number, y :: Number }
denormalizePoint b nx ny =
  { x: b.originX + nx * b.width
  , y: b.originY + ny * b.height
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // common sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1080p HD (1920×1080)
bounds1080p :: CanvasBounds
bounds1080p = mkCanvasBounds 1920.0 1080.0

-- | 4K UHD (3840×2160)
bounds4K :: CanvasBounds
bounds4K = mkCanvasBounds 3840.0 2160.0

-- | Square 1K (1024×1024)
boundsSquare1K :: CanvasBounds
boundsSquare1K = mkCanvasBounds 1024.0 1024.0

-- | A4 portrait at 300 DPI (2480×3508)
boundsA4Portrait :: CanvasBounds
boundsA4Portrait = mkCanvasBounds 2480.0 3508.0

-- | A4 landscape at 300 DPI (3508×2480)
boundsA4Landscape :: CanvasBounds
boundsA4Landscape = mkCanvasBounds 3508.0 2480.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // grid subdivision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subdivide canvas into a grid of cells.
-- |
-- | Returns cell dimensions and counts.
subdivideIntoCells 
  :: CanvasBounds 
  -> Int              -- ^ Cells in X direction
  -> Int              -- ^ Cells in Y direction
  -> { cellWidth :: Number
     , cellHeight :: Number
     , cellsX :: Int
     , cellsY :: Int
     , totalCells :: Int
     }
subdivideIntoCells b cellsX cellsY =
  let
    cx = max 1 cellsX
    cy = max 1 cellsY
  in
    { cellWidth: b.width / Int.toNumber cx
    , cellHeight: b.height / Int.toNumber cy
    , cellsX: cx
    , cellsY: cy
    , totalCells: cx * cy
    }

-- | Get cell index at a point.
-- |
-- | Returns (cellX, cellY) indices.
cellAtPoint 
  :: CanvasBounds 
  -> Int              -- ^ Cells in X
  -> Int              -- ^ Cells in Y
  -> Number           -- ^ Point X
  -> Number           -- ^ Point Y
  -> { cellX :: Int, cellY :: Int }
cellAtPoint b cellsX cellsY px py =
  let
    cellW = b.width / Int.toNumber (max 1 cellsX)
    cellH = b.height / Int.toNumber (max 1 cellsY)
    cx = Int.floor ((px - b.originX) / cellW)
    cy = Int.floor ((py - b.originY) / cellH)
  in
    { cellX: max 0 (min (cellsX - 1) cx)
    , cellY: max 0 (min (cellsY - 1) cy)
    }

-- | Get center point of a cell.
cellCenter 
  :: CanvasBounds 
  -> Int              -- ^ Cells in X
  -> Int              -- ^ Cells in Y
  -> Int              -- ^ Cell X index
  -> Int              -- ^ Cell Y index
  -> { x :: Number, y :: Number }
cellCenter b cellsX cellsY cx cy =
  let
    cellW = b.width / Int.toNumber (max 1 cellsX)
    cellH = b.height / Int.toNumber (max 1 cellsY)
  in
    { x: b.originX + (Int.toNumber cx + 0.5) * cellW
    , y: b.originY + (Int.toNumber cy + 0.5) * cellH
    }
