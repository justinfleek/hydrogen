-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // chart // linechart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Line Chart Geometry Module
-- |
-- | Pure geometric calculations for line charts. NO FFI, NO DOM.
-- |
-- | ## Pure Functions
-- |
-- | - `findNearestPoint` — Euclidean distance to find closest data point
-- | - `findNearestPointX` — X-axis only distance for vertical hover
-- | - `distanceEuclidean` — Distance between two points
-- | - `distanceX` — Horizontal distance only
-- |
-- | ## Architecture Note
-- |
-- | Visual operations (tooltips, highlights, animations) are handled by:
-- | 1. App state machine (update function)
-- | 2. Different Element values based on state
-- | 3. GPU kernel rendering (Hydrogen.GPU.Kernel.Chart.LinePlot)
-- |
-- | There is no DOM. Charts are DrawCommands rendered via WebGPU.

module Hydrogen.Chart.LineChart
  ( -- * Types (all use bounded coordinates)
    Point2D
  , NearestPointResult
  , ChartPadding
  , CrosshairPosition
  
  -- * Smart Constructors
  , mkPoint2D
  , mkChartPadding
  
  -- * Path Geometry Types
  , PathSegment
  , PathLength(PathLength)
  , PolylinePath(PolylinePath)
  
  -- * Path Length Functions
  , mkPathLength
  , pathLengthToNumber
  , pathLengthZero
  , addPathLength
  
  -- * Animation State Types
  , LineAnimationState(LineAnimationState)
  , LineDrawProgress(LineDrawProgress)
  , CrosshairState
  , HoverState
  , TooltipState
  , DataPointHighlight
  
  -- * Animation Progress Functions
  , mkLineDrawProgress
  , unwrapLineDrawProgress
  , progressStart
  , progressEnd
  , isProgressComplete
  
  -- * Pure Geometry (bounded inputs/outputs)
  , findNearestPoint
  , findNearestPointX
  , distanceEuclidean
  , distanceX
  , emptyResult
  
  -- * Path Geometry Functions
  , segmentLength
  , computePathLength
  , pointAtLength
  , tessellatePoints
  , lerpPoint2D
  
  -- * Animation Functions
  , mkLineAnimationState
  , advanceAnimation
  , lineAnimationProgress
  , visiblePathLength
  , visiblePathPoints
  
  -- * Crosshair State Functions
  , initialCrosshairState
  , updateCrosshair
  
  -- * Hover State Functions
  , mkHoverState
  , clearHover
  
  -- * Tooltip State Functions
  , mkTooltipState
  , hideTooltip
  
  -- * Highlight Functions
  , mkHighlight
  , noHighlight
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , show
  , otherwise
  , negate
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (<>)
  , (&&)
  )

import Data.Array (foldl, head, mapWithIndex, zip, drop, length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering(LT))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Math.Core.Arithmetic (sqrt, abs)

import Hydrogen.GPU.Coordinates 
  ( ScreenX
  , ScreenY
  , PixelWidth
  , PixelHeight
  , screenX
  , screenY
  , pixelWidth
  , pixelHeight
  , unwrapScreenX
  , unwrapScreenY
  , unwrapPixelWidth
  , unwrapPixelHeight
  )

import Hydrogen.Schema.Bounded 
  ( UnitInterval
  , clampUnit
  , unwrapUnit
  , unitZero
  , unitOne
  , clampNumber
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A point in 2D screen coordinate space.
-- |
-- | Uses bounded ScreenX/ScreenY types from Hydrogen.GPU.Coordinates:
-- | - Coordinates clamped to [-32768, 32768] (GPU texture limits)
-- | - NaN and Infinity are rejected at construction
-- |
-- | This replaces raw Number coordinates.
type Point2D =
  { x :: ScreenX
  , y :: ScreenY
  }

-- | Smart constructor for Point2D from raw Numbers.
-- | Clamps coordinates to valid GPU bounds.
mkPoint2D :: Number -> Number -> Point2D
mkPoint2D x' y' = { x: screenX x', y: screenY y' }

-- | Result of finding the nearest point
-- |
-- | - `index`: Array index of the nearest point (-1 if empty)
-- | - `distance`: Non-negative Euclidean distance to the cursor (clamped)
-- | - `point`: The actual point coordinates (bounded)
type NearestPointResult =
  { index :: Int
  , distance :: PixelWidth  -- Distance is always non-negative, like width
  , point :: Point2D
  }

-- | Chart padding configuration using bounded pixel dimensions.
-- |
-- | All padding values are non-negative (clamped to [0, 32768]).
type ChartPadding =
  { top :: PixelHeight
  , right :: PixelWidth
  , bottom :: PixelHeight
  , left :: PixelWidth
  }

-- | Smart constructor for ChartPadding from raw Numbers.
mkChartPadding :: Number -> Number -> Number -> Number -> ChartPadding
mkChartPadding t r b l =
  { top: pixelHeight t
  , right: pixelWidth r
  , bottom: pixelHeight b
  , left: pixelWidth l
  }

-- | Crosshair cursor position with visibility flag.
-- |
-- | Uses bounded coordinates — no raw Numbers.
type CrosshairPosition =
  { x :: ScreenX
  , y :: ScreenY
  , visible :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // path // geometry // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A segment of a polyline path between two consecutive points.
-- |
-- | Stores the start/end points and the segment's length.
-- | This is precomputed during tessellation for efficient pointAtLength queries.
-- |
-- | All lengths use PixelWidth (non-negative, bounded).
type PathSegment =
  { start :: Point2D
  , end :: Point2D
  , segmentLength :: PixelWidth      -- This segment's length (non-negative)
  , cumulativeLength :: PixelWidth   -- Length from path start to end of this segment
  }

-- | Path length — non-negative total length of a polyline.
-- |
-- | This is a bounded type: length is always in [0.0, 32768.0].
-- | Computed purely from point coordinates, no DOM needed.
-- | Uses PixelWidth internally for bounded non-negative semantics.
newtype PathLength = PathLength PixelWidth

derive instance eqPathLength :: Eq PathLength
derive instance ordPathLength :: Ord PathLength

instance showPathLength :: Show PathLength where
  show (PathLength len) = "(PathLength " <> show len <> ")"

-- | Smart constructor for PathLength from raw Number.
-- | Clamps to non-negative range [0.0, 32768.0].
mkPathLength :: Number -> PathLength
mkPathLength n = PathLength (pixelWidth n)

-- | Extract raw Number from PathLength (for calculations).
-- | The returned value is guaranteed to be in [0.0, 32768.0].
pathLengthToNumber :: PathLength -> Number
pathLengthToNumber (PathLength len) = unwrapPixelWidth len

-- | Zero path length.
pathLengthZero :: PathLength
pathLengthZero = PathLength (pixelWidth 0.0)

-- | Add two path lengths.
addPathLength :: PathLength -> PathLength -> PathLength
addPathLength (PathLength a) (PathLength b) = 
  mkPathLength (unwrapPixelWidth a + unwrapPixelWidth b)

-- | A tessellated polyline path — array of segments with precomputed lengths.
-- |
-- | Created from an array of Point2D via `tessellatePoints`.
-- | Enables efficient path-length queries without DOM access.
newtype PolylinePath = PolylinePath
  { segments :: Array PathSegment
  , totalLength :: PathLength
  }

derive instance eqPolylinePath :: Eq PolylinePath

instance showPolylinePath :: Show PolylinePath where
  show (PolylinePath p) = 
    "(PolylinePath segments:" <> show (length p.segments) <> 
    " length:" <> show p.totalLength <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // animation // state // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Line draw progress — bounded [0.0, 1.0] representing how much of the line is drawn.
-- |
-- | This is the pure replacement for strokeDashoffset animation:
-- | - 0.0 = line not drawn (invisible)
-- | - 1.0 = line fully drawn (complete)
-- | - 0.5 = half the line is drawn
-- |
-- | Wraps UnitInterval from Hydrogen.Schema.Bounded for guaranteed bounds.
-- | NaN and Infinity are rejected at construction.
newtype LineDrawProgress = LineDrawProgress UnitInterval

derive instance eqLineDrawProgress :: Eq LineDrawProgress
derive instance ordLineDrawProgress :: Ord LineDrawProgress

instance showLineDrawProgress :: Show LineDrawProgress where
  show (LineDrawProgress p) = "(LineDrawProgress " <> show p <> ")"

-- | Create LineDrawProgress from raw Number, clamping to [0.0, 1.0].
-- | NaN/Infinity are clamped to 0.0 (safe fallback via clampUnit).
mkLineDrawProgress :: Number -> LineDrawProgress
mkLineDrawProgress n = LineDrawProgress (clampUnit n)

-- | Extract raw Number from LineDrawProgress.
-- | Result is guaranteed to be in [0.0, 1.0].
unwrapLineDrawProgress :: LineDrawProgress -> Number
unwrapLineDrawProgress (LineDrawProgress p) = unwrapUnit p

-- | Animation not started (0.0).
progressStart :: LineDrawProgress
progressStart = LineDrawProgress unitZero

-- | Animation complete (1.0).
progressEnd :: LineDrawProgress
progressEnd = LineDrawProgress unitOne

-- | Check if animation is complete (progress >= 1.0).
isProgressComplete :: LineDrawProgress -> Boolean
isProgressComplete (LineDrawProgress p) = unwrapUnit p >= 1.0

-- | Complete state for line drawing animation.
-- |
-- | This replaces the JS animation state machine:
-- | - `path`: The tessellated polyline with precomputed lengths
-- | - `progress`: Current draw progress [0.0, 1.0]
-- | - `isAnimating`: Whether animation is in progress
-- |
-- | The animation is pure: given progress, compute visible path length.
-- | The runtime handles timing — PureScript handles geometry.
newtype LineAnimationState = LineAnimationState
  { path :: PolylinePath
  , progress :: LineDrawProgress
  , isAnimating :: Boolean
  }

derive instance eqLineAnimationState :: Eq LineAnimationState

instance showLineAnimationState :: Show LineAnimationState where
  show (LineAnimationState s) = 
    "(LineAnimationState progress:" <> show s.progress <> 
    " animating:" <> show s.isAnimating <> ")"

-- | Crosshair state — pure cursor tracking.
-- |
-- | This replaces DOM event listeners and SVG line manipulation:
-- | - Position is tracked as bounded Point2D values
-- | - Visibility is a boolean, not style.display
-- | - The view function renders based on this state
-- |
-- | All dimensions use bounded PixelWidth/PixelHeight.
type CrosshairState =
  { position :: Maybe Point2D  -- Nothing = not visible
  , padding :: ChartPadding    -- Chart bounds for clipping (bounded)
  , chartWidth :: PixelWidth   -- Total chart width (bounded, non-negative)
  , chartHeight :: PixelHeight -- Total chart height (bounded, non-negative)
  }

-- | Hover state — tracks which data point is being hovered.
-- |
-- | This replaces DOM querySelector + attribute manipulation:
-- | - hoveredIndex: Which point (if any) is under cursor
-- | - nearestResult: Full result from findNearestPoint (bounded)
type HoverState =
  { hoveredIndex :: Maybe Int
  , nearestResult :: NearestPointResult
  }

-- | Tooltip state — pure position and content tracking.
-- |
-- | This replaces DOM tooltip element manipulation:
-- | - position: Where to render (bounded screen coordinates)
-- | - visible: Whether to show (not style.visibility)
-- | - dataPointIndex: Which data point this tooltip describes
type TooltipState =
  { position :: Point2D       -- Bounded screen coordinates
  , visible :: Boolean
  , dataPointIndex :: Int     -- Which data point this tooltip describes
  }

-- | Data point highlight parameters.
-- |
-- | This replaces DOM radius/filter manipulation:
-- | - radiusMultiplier: Scale factor for highlighted point (bounded UnitInterval scaled)
-- | - glowIntensity: Glow effect strength [0.0, 1.0] (bounded UnitInterval)
-- |
-- | Using bounded types prevents invalid visual states.
type DataPointHighlight =
  { radiusMultiplier :: UnitInterval  -- 0.0 = invisible, 1.0 = normal (scaled by view)
  , glowIntensity :: UnitInterval     -- 0.0 = no glow, 1.0 = full glow
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // pure // geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Euclidean distance between two bounded points.
-- |
-- | Returns a bounded PixelWidth (non-negative).
-- | √((x₂ - x₁)² + (y₂ - y₁)²)
distanceEuclidean :: Point2D -> Point2D -> PixelWidth
distanceEuclidean p1 p2 =
  let dx = unwrapScreenX p2.x - unwrapScreenX p1.x
      dy = unwrapScreenY p2.y - unwrapScreenY p1.y
  in pixelWidth (sqrt (dx * dx + dy * dy))

-- | Horizontal distance between two points (X-axis only).
-- |
-- | Returns a bounded PixelWidth (non-negative).
-- | |x₂ - x₁|
distanceX :: Point2D -> Point2D -> PixelWidth
distanceX p1 p2 = pixelWidth (abs (unwrapScreenX p2.x - unwrapScreenX p1.x))

-- | Find the nearest data point to a cursor position using Euclidean distance.
-- |
-- | This is a pure function — no DOM access, no FFI.
-- | All coordinates and distances are bounded types.
-- | Returns index -1 with max distance if the array is empty.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let points = [mkPoint2D 10.0 20.0, mkPoint2D 50.0 30.0]
-- |     cursor = mkPoint2D 45.0 25.0
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

-- | Find the nearest data point using X-axis distance only.
-- |
-- | Useful for vertical line hover behavior where Y position doesn't matter.
-- | This creates a "snap to column" effect common in line charts.
-- | All coordinates and distances are bounded types.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let points = [mkPoint2D 10.0 100.0, mkPoint2D 50.0 200.0]
-- |     cursor = mkPoint2D 45.0 0.0  -- Y doesn't matter
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

-- | Helper: empty result for empty point arrays.
-- |
-- | Uses maximum bounded distance (32768 pixels) instead of raw infinity.
-- | Point is origin (0,0) with bounded coordinates.
emptyResult :: NearestPointResult
emptyResult =
  { index: -1
  , distance: pixelWidth 32768.0  -- Max bounded distance (GPU limit)
  , point: mkPoint2D 0.0 0.0
  }

-- | Helper: compare using Euclidean distance (bounded).
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

-- | Helper: compare using X-axis distance (bounded).
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
--                                                    // path // geometry // functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute length of a single segment (Euclidean distance).
-- |
-- | This is the fundamental building block for path length calculation.
-- | Returns bounded PixelWidth (non-negative, clamped to [0, 32768]).
segmentLength :: Point2D -> Point2D -> PixelWidth
segmentLength = distanceEuclidean

-- | Tessellate an array of points into a PolylinePath with precomputed lengths.
-- |
-- | This is the pure replacement for SVG getTotalLength():
-- | - Converts Array Point2D → PolylinePath
-- | - Precomputes each segment's length (bounded PixelWidth)
-- | - Tracks cumulative length at each segment
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let points = [mkPoint2D 0.0 0.0, mkPoint2D 3.0 4.0, mkPoint2D 6.0 4.0]
-- |     path = tessellatePoints points
-- | -- path.totalLength == PathLength (PixelWidth 8.0) (5.0 + 3.0)
-- | ```
-- |
-- | For empty or single-point arrays, returns zero-length path.
tessellatePoints :: Array Point2D -> PolylinePath
tessellatePoints points =
  let pairs = zip points (drop 1 points)
      -- Use PixelWidth internally (bounded non-negative)
      buildSegments :: PixelWidth -> Array PathSegment -> Array (Tuple Point2D Point2D) -> { segs :: Array PathSegment, total :: PixelWidth }
      buildSegments cumLen segs remaining =
        case head remaining of
          Nothing -> { segs, total: cumLen }
          Just (Tuple p1 p2) ->
            let len = segmentLength p1 p2
                newCumLen = pixelWidth (unwrapPixelWidth cumLen + unwrapPixelWidth len)
                seg = { start: p1, end: p2, segmentLength: len, cumulativeLength: newCumLen }
            in buildSegments newCumLen (appendSegment segs seg) (drop 1 remaining)
      result = buildSegments (pixelWidth 0.0) [] pairs
  in PolylinePath
       { segments: result.segs
       , totalLength: PathLength result.total
       }

-- | Helper: append segment to array (avoiding snoc for efficiency clarity)
appendSegment :: Array PathSegment -> PathSegment -> Array PathSegment
appendSegment arr seg = arr <> [seg]

-- | Compute total length of a point array.
-- |
-- | Shorthand for: (tessellatePoints points).totalLength
-- |
-- | This is the pure replacement for SVG path.getTotalLength().
-- | Returns PathLength with bounded PixelWidth (0.0 for empty arrays).
-- |
-- | ## Example
-- |
-- | ```purescript
-- | computePathLength [mkPoint2D 0.0 0.0, mkPoint2D 3.0 4.0]
-- | -- Returns PathLength (PixelWidth 5.0) (3-4-5 triangle hypotenuse)
-- | ```
computePathLength :: Array Point2D -> PathLength
computePathLength points =
  let (PolylinePath p) = tessellatePoints points
  in p.totalLength

-- | Find the point at a given distance along the path.
-- |
-- | This is the pure replacement for SVG path.getPointAtLength(distance).
-- | Takes bounded PixelWidth distance, returns bounded Point2D.
-- |
-- | - If distance <= 0, returns the first point
-- | - If distance >= totalLength, returns the last point
-- | - Otherwise, interpolates linearly within the appropriate segment
-- |
-- | Returns Nothing for empty paths.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let path = tessellatePoints [mkPoint2D 0.0 0.0, mkPoint2D 10.0 0.0]
-- | pointAtLength path (pixelWidth 5.0)
-- | -- Just (mkPoint2D 5.0 0.0)
-- | ```
pointAtLength :: PolylinePath -> PixelWidth -> Maybe Point2D
pointAtLength (PolylinePath p) distance
  | length p.segments < 1 = Nothing  -- Empty path
  | unwrapPixelWidth distance <= 0.0 = 
      case head p.segments of
        Nothing -> Nothing
        Just seg -> Just seg.start
  | otherwise =
      let (PathLength total) = p.totalLength
          distNum = unwrapPixelWidth distance
          totalNum = unwrapPixelWidth total
      in if distNum >= totalNum
           then lastPoint p.segments
           else findSegmentAtLength p.segments distNum

-- | Helper: get last point of segment array
lastPoint :: Array PathSegment -> Maybe Point2D
lastPoint segments = 
  foldl (\_ seg -> Just seg.end) Nothing segments

-- | Helper: find segment containing the target length and interpolate.
-- | Uses raw Number internally but all inputs/outputs are bounded.
findSegmentAtLength :: Array PathSegment -> Number -> Maybe Point2D
findSegmentAtLength segments targetLen =
  foldl (checkSegment targetLen) Nothing segments

-- | Helper: check if target length falls within this segment.
-- | Computes interpolation parameter as UnitInterval for bounded lerp.
checkSegment :: Number -> Maybe Point2D -> PathSegment -> Maybe Point2D
checkSegment targetLen acc seg =
  case acc of
    Just pt -> Just pt  -- Already found
    Nothing ->
      let prevCumLen = unwrapPixelWidth seg.cumulativeLength - unwrapPixelWidth seg.segmentLength
          segCumLen = unwrapPixelWidth seg.cumulativeLength
          segLen = unwrapPixelWidth seg.segmentLength
      in if targetLen <= segCumLen
           then 
             -- Target is in this segment — interpolate
             let t = if segLen <= 0.0 
                       then 0.0 
                       else clampNumber 0.0 1.0 ((targetLen - prevCumLen) / segLen)
             in Just (lerpPoint2D seg.start seg.end (clampUnit t))
           else Nothing

-- | Linear interpolation between two bounded points.
-- |
-- | Uses UnitInterval for interpolation parameter — guaranteed [0.0, 1.0].
-- | Returns bounded Point2D.
-- |
-- | lerpPoint2D a b t:
-- | - t = 0.0 → returns a
-- | - t = 1.0 → returns b
-- | - t = 0.5 → returns midpoint
lerpPoint2D :: Point2D -> Point2D -> UnitInterval -> Point2D
lerpPoint2D p1 p2 t =
  let tVal = unwrapUnit t
      x1 = unwrapScreenX p1.x
      y1 = unwrapScreenY p1.y
      x2 = unwrapScreenX p2.x
      y2 = unwrapScreenY p2.y
  in mkPoint2D 
       (x1 + (x2 - x1) * tVal)
       (y1 + (y2 - y1) * tVal)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // animation // functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create initial line animation state from point array.
-- |
-- | This is the pure replacement for the JS animateLineImpl setup:
-- | - Tessellates points into path with precomputed lengths (bounded)
-- | - Initializes progress to 0.0 (line not visible)
-- | - Sets isAnimating to true to indicate animation should run
-- |
-- | The runtime handles actual timing — this is pure state initialization.
mkLineAnimationState :: Array Point2D -> LineAnimationState
mkLineAnimationState points =
  LineAnimationState
    { path: tessellatePoints points
    , progress: progressStart
    , isAnimating: true
    }

-- | Advance animation by a progress delta.
-- |
-- | Takes a UnitInterval delta (bounded [0.0, 1.0]).
-- | Progress is clamped to [0.0, 1.0] via mkLineDrawProgress.
-- | When progress reaches 1.0, isAnimating becomes false.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let state = mkLineAnimationState points
-- |     delta = clampUnit 0.016  -- ~60fps frame time as fraction of duration
-- |     newState = advanceAnimation delta state
-- | ```
advanceAnimation :: UnitInterval -> LineAnimationState -> LineAnimationState
advanceAnimation delta (LineAnimationState s) =
  let currentProgress = unwrapLineDrawProgress s.progress
      deltaVal = unwrapUnit delta
      newProgress = currentProgress + deltaVal
      clampedProgress = mkLineDrawProgress newProgress
      done = isProgressComplete clampedProgress
  in LineAnimationState
       { path: s.path
       , progress: clampedProgress
       , isAnimating: if done then false else s.isAnimating
       }

-- | Get current progress as UnitInterval (bounded [0.0, 1.0]).
lineAnimationProgress :: LineAnimationState -> UnitInterval
lineAnimationProgress (LineAnimationState s) =
  let (LineDrawProgress p) = s.progress
  in p

-- | Compute the visible path length at current animation progress.
-- |
-- | Returns bounded PixelWidth. This is what the GPU renderer needs:
-- | - progress 0.0 → visible length 0.0
-- | - progress 1.0 → visible length = totalLength
-- | - progress 0.5 → visible length = totalLength * 0.5
-- |
-- | This replaces strokeDashoffset calculation.
visiblePathLength :: LineAnimationState -> PixelWidth
visiblePathLength (LineAnimationState s) =
  let (PolylinePath path) = s.path
      (PathLength total) = path.totalLength
      prog = unwrapLineDrawProgress s.progress
      totalNum = unwrapPixelWidth total
  in pixelWidth (totalNum * prog)

-- | Get all visible points at current animation progress.
-- |
-- | Returns the subset of path segments that should be drawn,
-- | with the final segment potentially truncated at the visible length.
-- | All points are bounded Point2D.
-- |
-- | This is used to render partial line during animation.
visiblePathPoints :: LineAnimationState -> Array Point2D
visiblePathPoints (LineAnimationState s) =
  let (PolylinePath path) = s.path
      prog = unwrapLineDrawProgress s.progress
      (PathLength total) = path.totalLength
      visLen = unwrapPixelWidth total * prog
  in extractVisiblePoints path.segments visLen

-- | Helper: extract points up to visible length.
-- | Uses raw Number internally for calculations.
extractVisiblePoints :: Array PathSegment -> Number -> Array Point2D
extractVisiblePoints segments visLen =
  let result = foldl (collectPoints visLen) { points: [], done: false } segments
  in result.points

-- | Helper: collect points up to visible length.
-- | All output points are bounded Point2D.
collectPoints 
  :: Number 
  -> { points :: Array Point2D, done :: Boolean } 
  -> PathSegment 
  -> { points :: Array Point2D, done :: Boolean }
collectPoints visLen acc seg
  | acc.done = acc  -- Already collected all visible points
  | otherwise =
      let prevCumLen = unwrapPixelWidth seg.cumulativeLength - unwrapPixelWidth seg.segmentLength
          segCumLen = unwrapPixelWidth seg.cumulativeLength
          segLen = unwrapPixelWidth seg.segmentLength
      in if visLen <= prevCumLen
           then acc  -- This segment is beyond visible range
           else if visLen >= segCumLen
             then 
               -- Full segment is visible — add start and end
               let newPoints = case length acc.points of
                     0 -> [seg.start, seg.end]
                     _ -> acc.points <> [seg.end]  -- Start already added
               in { points: newPoints, done: false }
             else
               -- Partial segment — interpolate end point
               let t = if segLen <= 0.0 
                         then 1.0 
                         else clampNumber 0.0 1.0 ((visLen - prevCumLen) / segLen)
                   partialEnd = lerpPoint2D seg.start seg.end (clampUnit t)
                   newPoints = case length acc.points of
                     0 -> [seg.start, partialEnd]
                     _ -> acc.points <> [partialEnd]
               in { points: newPoints, done: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // crosshair // state // functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create initial crosshair state (not visible).
-- |
-- | All dimensions use bounded types:
-- | - ChartPadding with PixelWidth/PixelHeight
-- | - Chart dimensions as PixelWidth/PixelHeight
-- |
-- | This replaces DOM event listener setup — pure state.
initialCrosshairState :: ChartPadding -> PixelWidth -> PixelHeight -> CrosshairState
initialCrosshairState padding chartWidth chartHeight =
  { position: Nothing
  , padding
  , chartWidth
  , chartHeight
  }

-- | Update crosshair position based on cursor coordinates.
-- |
-- | Takes bounded Point2D, returns updated CrosshairState.
-- | If cursor is within chart bounds (respecting padding), crosshair is visible.
-- | Otherwise, crosshair is hidden.
-- |
-- | All comparisons use bounded types.
-- | This replaces the JS handleMouseMove logic.
updateCrosshair :: Point2D -> CrosshairState -> CrosshairState
updateCrosshair cursor state =
  let cursorX = unwrapScreenX cursor.x
      cursorY = unwrapScreenY cursor.y
      padLeft = unwrapPixelWidth state.padding.left
      padRight = unwrapPixelWidth state.padding.right
      padTop = unwrapPixelHeight state.padding.top
      padBottom = unwrapPixelHeight state.padding.bottom
      width = unwrapPixelWidth state.chartWidth
      height = unwrapPixelHeight state.chartHeight
      inBounds = 
        cursorX >= padLeft &&
        cursorX <= width - padRight &&
        cursorY >= padTop &&
        cursorY <= height - padBottom
  in if inBounds
       then state { position = Just cursor }
       else state { position = Nothing }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // hover // state // functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create hover state from nearest point result.
-- |
-- | This replaces JS highlightDotImpl:
-- | - No DOM querySelector
-- | - No setAttribute manipulation
-- | - Just pure state that view function renders
mkHoverState :: NearestPointResult -> HoverState
mkHoverState result =
  { hoveredIndex: if result.index >= 0 then Just result.index else Nothing
  , nearestResult: result
  }

-- | Clear hover state (no point hovered).
clearHover :: HoverState
clearHover =
  { hoveredIndex: Nothing
  , nearestResult: emptyResult
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // tooltip // state // functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create visible tooltip state at position.
-- |
-- | This replaces JS showTooltipImpl:
-- | - No DOM createElement
-- | - No innerHTML
-- | - No style manipulation
-- | - Just pure state
mkTooltipState :: Point2D -> Int -> TooltipState
mkTooltipState position dataPointIndex =
  { position
  , visible: true
  , dataPointIndex
  }

-- | Hide tooltip.
-- |
-- | This replaces JS hideTooltipImpl:
-- | - No style.opacity manipulation
-- | - Just set visible = false
hideTooltip :: TooltipState -> TooltipState
hideTooltip state = state { visible = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // highlight // state // functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create highlight parameters for data point.
-- |
-- | This replaces JS highlightDotImpl radius/filter manipulation.
-- | Uses bounded UnitInterval values:
-- | - radiusMultiplier: Scaled by view layer (0.0 = invisible, 1.0 = max)
-- |   Default 1.0 means "use highlight scale" (view interprets as 1.5x)
-- | - glowIntensity: 1.0 = full glow (matches JS drop-shadow filter)
-- |
-- | Both values are bounded [0.0, 1.0] via UnitInterval.
mkHighlight :: DataPointHighlight
mkHighlight =
  { radiusMultiplier: unitOne   -- Full highlight scale
  , glowIntensity: unitOne      -- Full glow
  }

-- | No highlight (normal appearance).
-- |
-- | This replaces JS clearDotHighlightsImpl.
-- | Uses bounded UnitInterval values:
-- | - radiusMultiplier: 0.5 scaled by view to 1.0x (normal)
-- | - glowIntensity: 0.0 = no glow
noHighlight :: DataPointHighlight
noHighlight =
  { radiusMultiplier: clampUnit 0.5  -- View scales 0.5 → 1.0x (normal size)
  , glowIntensity: unitZero          -- No glow
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // architecture note
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ## Visual Operations
-- |
-- | Visual operations (tooltips, highlights, animations) are NOT functions.
-- | They are expressed as:
-- |
-- | 1. **State** — App state tracks hover index, animation phase, tooltip visibility
-- | 2. **Element** — View function produces Element based on state
-- | 3. **DrawCommand** — Element flattens to GPU commands
-- | 4. **Rust/WebGPU** — Runtime renders DrawCommands
-- |
-- | Example: To show a tooltip at data point 3:
-- |
-- | ```purescript
-- | type ChartState = { hoveredIndex :: Maybe Int, ... }
-- |
-- | update :: Msg -> ChartState -> ChartState
-- | update (MouseMoved pos) state =
-- |   let nearest = findNearestPoint points pos
-- |   in state { hoveredIndex = Just nearest.index }
-- |
-- | view :: ChartState -> Element Msg
-- | view state =
-- |   Group
-- |     [ renderLinePath points
-- |     , case state.hoveredIndex of
-- |         Just idx -> renderTooltip (points !! idx)
-- |         Nothing -> Empty
-- |     ]
-- | ```
-- |
-- | The tooltip IS an Element. It renders as DrawCommands. No FFI needed.
-- |
-- | ## Path Length / Point At Length
-- |
-- | For SVG path queries, use the pure geometry functions in
-- | `Hydrogen.GPU.Kernel.Chart.LinePlot` or compute from the data points directly.
-- | The Rust runtime handles path tessellation — PureScript works with data.
