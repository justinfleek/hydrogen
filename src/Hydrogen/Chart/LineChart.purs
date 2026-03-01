-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // chart // linechart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Line Chart Module
-- |
-- | Provides pure geometric calculations for line charts and minimal FFI
-- | for browser-only operations (animations, crosshairs, tooltips).
-- |
-- | ## Pure Functions (No FFI)
-- |
-- | - `findNearestPoint` — Euclidean distance to find closest data point
-- | - `findNearestPointX` — X-axis only distance for vertical hover
-- | - `NearestPointResult` — Result type with index, distance, and point
-- |
-- | ## Browser Boundaries (FFI Required)
-- |
-- | - Line animation (stroke-dasharray manipulation)
-- | - Crosshair initialization (event listeners)
-- | - Tooltip display (DOM creation/positioning)
-- | - Dot highlighting (style manipulation)
-- | - Path length queries (SVG getTotalLength API)

module Hydrogen.Chart.LineChart
  ( -- * Types
    Point2D
  , NearestPointResult
  , ChartPadding
  , CrosshairPosition
  
  -- * Pure Geometry (No FFI)
  , findNearestPoint
  , findNearestPointX
  , distanceEuclidean
  , distanceX
  
  -- * Browser Boundaries (FFI)
  , animateLine
  , resetLine
  , initCrosshair
  , showTooltip
  , hideTooltip
  , highlightDot
  , clearDotHighlights
  , getPathLength
  , getPointAtLength
  ) where

import Prelude
  ( Unit
  , bind
  , compare
  , discard
  , identity
  , map
  , negate
  , otherwise
  , pure
  , unit
  , ($)
  , (*)
  , (+)
  , (-)
  , (<)
  , (==)
  )

import Data.Array (foldl, head, length, mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Ordering (Ordering(LT))
import Effect (Effect)

import Hydrogen.Math.Core.Arithmetic (sqrt, abs)
import Hydrogen.Math.Core.Constants (infinity)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A point in 2D SVG coordinate space
type Point2D =
  { x :: Number
  , y :: Number
  }

-- | Result of finding the nearest point
-- |
-- | - `index`: Array index of the nearest point (-1 if empty)
-- | - `distance`: Euclidean distance to the cursor
-- | - `point`: The actual point coordinates
type NearestPointResult =
  { index :: Int
  , distance :: Number
  , point :: Point2D
  }

-- | Chart padding configuration
type ChartPadding =
  { top :: Number
  , right :: Number
  , bottom :: Number
  , left :: Number
  }

-- | Crosshair cursor position with visibility flag
type CrosshairPosition =
  { x :: Number
  , y :: Number
  , visible :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // pure // geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Euclidean distance between two points
-- |
-- | √((x₂ - x₁)² + (y₂ - y₁)²)
distanceEuclidean :: Point2D -> Point2D -> Number
distanceEuclidean p1 p2 =
  let dx = p2.x - p1.x
      dy = p2.y - p1.y
  in sqrt (dx * dx + dy * dy)

-- | Horizontal distance between two points (X-axis only)
-- |
-- | |x₂ - x₁|
distanceX :: Point2D -> Point2D -> Number
distanceX p1 p2 = abs (p2.x - p1.x)

-- | Find the nearest data point to a cursor position using Euclidean distance
-- |
-- | This is a pure function — no DOM access, no FFI.
-- | Returns index -1 with infinite distance if the array is empty.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let points = [{ x: 10.0, y: 20.0 }, { x: 50.0, y: 30.0 }]
-- |     cursor = { x: 45.0, y: 25.0 }
-- |     result = findNearestPoint points cursor
-- | -- result.index == 1 (second point is closer)
-- | ```
findNearestPoint :: Array Point2D -> Point2D -> NearestPointResult
findNearestPoint points cursor =
  case head points of
    Nothing -> emptyResult
    Just firstPoint ->
      let initial = 
            { index: 0
            , distance: distanceEuclidean firstPoint cursor
            , point: firstPoint
            }
          indexed = mapWithIndex (\i p -> { idx: i, pt: p }) points
      in foldl (findCloser cursor) initial indexed

-- | Find the nearest data point using X-axis distance only
-- |
-- | Useful for vertical line hover behavior where Y position doesn't matter.
-- | This creates a "snap to column" effect common in line charts.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let points = [{ x: 10.0, y: 100.0 }, { x: 50.0, y: 200.0 }]
-- |     cursor = { x: 45.0, y: 0.0 }  -- Y doesn't matter
-- |     result = findNearestPointX points cursor
-- | -- result.index == 1 (x=50 is closer to x=45 than x=10)
-- | ```
findNearestPointX :: Array Point2D -> Point2D -> NearestPointResult
findNearestPointX points cursor =
  case head points of
    Nothing -> emptyResult
    Just firstPoint ->
      let initial = 
            { index: 0
            , distance: distanceX firstPoint cursor
            , point: firstPoint
            }
          indexed = mapWithIndex (\i p -> { idx: i, pt: p }) points
      in foldl (findCloserX cursor) initial indexed

-- | Helper: empty result for empty point arrays
emptyResult :: NearestPointResult
emptyResult =
  { index: -1
  , distance: infinity
  , point: { x: 0.0, y: 0.0 }
  }

-- | Helper: compare using Euclidean distance
findCloser 
  :: Point2D 
  -> NearestPointResult 
  -> { idx :: Int, pt :: Point2D } 
  -> NearestPointResult
findCloser cursor acc indexed =
  let dist = distanceEuclidean indexed.pt cursor
  in case compare dist acc.distance of
       LT -> { index: indexed.idx, distance: dist, point: indexed.pt }
       _  -> acc

-- | Helper: compare using X-axis distance
findCloserX
  :: Point2D 
  -> NearestPointResult 
  -> { idx :: Int, pt :: Point2D } 
  -> NearestPointResult
findCloserX cursor acc indexed =
  let dist = distanceX indexed.pt cursor
  in case compare dist acc.distance of
       LT -> { index: indexed.idx, distance: dist, point: indexed.pt }
       _  -> acc

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // browser // boundaries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animate line drawing from start to end
-- |
-- | BROWSER BOUNDARY: Requires DOM access for stroke-dasharray manipulation.
-- |
-- | @param containerId Container element ID
-- | @param duration Animation duration in milliseconds
foreign import animateLineImpl :: String -> Number -> Effect Unit

-- | Type-safe wrapper for line animation
animateLine :: String -> Number -> Effect Unit
animateLine = animateLineImpl

-- | Reset line animation state
-- |
-- | BROWSER BOUNDARY: Requires DOM access.
foreign import resetLineImpl :: String -> Effect Unit

-- | Type-safe wrapper for reset
resetLine :: String -> Effect Unit
resetLine = resetLineImpl

-- | Initialize crosshair tracking
-- |
-- | BROWSER BOUNDARY: Requires DOM event listeners and SVG manipulation.
-- |
-- | Returns a cleanup function to remove listeners.
foreign import initCrosshairImpl 
  :: String 
  -> ChartPadding 
  -> (CrosshairPosition -> Effect Unit) 
  -> Effect (Effect Unit)

-- | Type-safe wrapper for crosshair initialization
initCrosshair 
  :: String 
  -> ChartPadding 
  -> (CrosshairPosition -> Effect Unit) 
  -> Effect (Effect Unit)
initCrosshair = initCrosshairImpl

-- | Show tooltip at position
-- |
-- | BROWSER BOUNDARY: Creates/positions DOM elements.
foreign import showTooltipImpl :: String -> Number -> Number -> String -> Effect Unit

-- | Type-safe wrapper for showing tooltip
showTooltip :: String -> Number -> Number -> String -> Effect Unit
showTooltip = showTooltipImpl

-- | Hide tooltip
-- |
-- | BROWSER BOUNDARY: Manipulates DOM element visibility.
foreign import hideTooltipImpl :: String -> Effect Unit

-- | Type-safe wrapper for hiding tooltip
hideTooltip :: String -> Effect Unit
hideTooltip = hideTooltipImpl

-- | Highlight a data point dot
-- |
-- | BROWSER BOUNDARY: Manipulates SVG element attributes.
foreign import highlightDotImpl :: String -> Int -> Effect Unit

-- | Type-safe wrapper for dot highlighting
highlightDot :: String -> Int -> Effect Unit
highlightDot = highlightDotImpl

-- | Clear all dot highlights
-- |
-- | BROWSER BOUNDARY: Resets SVG element attributes.
foreign import clearDotHighlightsImpl :: String -> Number -> Effect Unit

-- | Type-safe wrapper for clearing highlights
clearDotHighlights :: String -> Number -> Effect Unit
clearDotHighlights = clearDotHighlightsImpl

-- | Get total length of an SVG path
-- |
-- | BROWSER BOUNDARY: Requires SVG getTotalLength() API.
foreign import getPathLengthImpl :: String -> Effect Number

-- | Type-safe wrapper for path length
getPathLength :: String -> Effect Number
getPathLength = getPathLengthImpl

-- | Get point at length along path
-- |
-- | BROWSER BOUNDARY: Requires SVG getPointAtLength() API.
foreign import getPointAtLengthImpl :: String -> Number -> Effect Point2D

-- | Type-safe wrapper for point at length
getPointAtLength :: String -> Number -> Effect Point2D
getPointAtLength = getPointAtLengthImpl
