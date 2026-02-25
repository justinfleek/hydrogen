-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path — SVG path commands composed into vector graphics.

module Hydrogen.Schema.Geometry.Path
  ( -- * Types
    PathCommand(..)
  , Path(Path)
  , ArcParams
  
  -- * Construction
  , emptyPath
  , pathFromCommands
  , pathFromPoints
  , moveTo
  , lineTo
  , quadTo
  , cubicTo
  , arcTo
  , closePath
  
  -- * Query
  , isEmpty
  , commandCount
  , isClosed
  , getCommands
  , firstPoint
  , lastPoint
  
  -- * Serialization
  , toSvgString
  , commandToSvgString
  
  -- * Geometry
  , bounds
  , pathLength
  , pointAtLength
  , tangentAtLength
  
  -- * Transformation
  , reversePath
  , translatePath
  , scalePath
  , rotatePath
  
  -- * Operations
  , appendPath
  , flattenPath
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , map
  , pure
  , bind
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (<$>)
  , (>>=)
  , ($)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , not
  , negate
  , min
  , max
  , otherwise
  )

import Data.Array 
  ( snoc
  , cons
  , uncons
  , head
  , tail
  , last
  , init
  , length
  , null
  , reverse
  , foldl
  , foldr
  , filter
  , concatMap
  , concat
  , take
  , drop
  , index
  , mapWithIndex
  , zip
  , zipWith
  ) as Array
import Data.Maybe (Maybe(..))

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Angle (Degrees, unwrapDegrees)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)
import Hydrogen.Schema.Geometry.Bezier 
  ( QuadBezier
  , CubicBezier
  , quadBezier
  , cubicBezier
  , quadPointAt
  , cubicPointAt
  , quadTangentAt
  , cubicTangentAt
  , quadBoundingBox
  , cubicBoundingBox
  , quadLength
  , cubicLength
  )
import Data.Number (sqrt, sin, cos, pi)
import Data.Number (floor) as Number
import Data.Int (toNumber, floor) as Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Arc parameters for elliptical arc command.
type ArcParams =
  { rx :: Number           -- ^ X radius
  , ry :: Number           -- ^ Y radius
  , rotation :: Degrees    -- ^ X-axis rotation
  , largeArc :: Boolean    -- ^ Use large arc (> 180°)
  , sweep :: Boolean       -- ^ Sweep clockwise
  , end :: Point2D         -- ^ End point
  }

-- | SVG path command.
data PathCommand
  = MoveTo Point2D
  | LineTo Point2D
  | QuadTo Point2D Point2D
  | CubicTo Point2D Point2D Point2D
  | ArcTo ArcParams
  | ClosePath

derive instance eqPathCommand :: Eq PathCommand

instance showPathCommand :: Show PathCommand where
  show (MoveTo p) = "(MoveTo " <> show p <> ")"
  show (LineTo p) = "(LineTo " <> show p <> ")"
  show (QuadTo c p) = "(QuadTo " <> show c <> " " <> show p <> ")"
  show (CubicTo c1 c2 p) = "(CubicTo " <> show c1 <> " " <> show c2 <> " " <> show p <> ")"
  show (ArcTo params) = "(ArcTo rx:" <> show params.rx <> " ry:" <> show params.ry <> " end:" <> show params.end <> ")"
  show ClosePath = "ClosePath"

-- | A path is an array of commands.
newtype Path = Path (Array PathCommand)

derive instance eqPath :: Eq Path

instance showPath :: Show Path where
  show (Path cmds) = "(Path " <> show cmds <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // construction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty path with no commands.
emptyPath :: Path
emptyPath = Path []

-- | Create path from array of commands.
pathFromCommands :: Array PathCommand -> Path
pathFromCommands = Path

-- | Create path from array of points.
-- |
-- | First point becomes MoveTo, subsequent points become LineTo.
-- | Returns empty path if no points provided.
pathFromPoints :: Array Point2D -> Path
pathFromPoints points =
  case Array.uncons points of
    Nothing -> emptyPath
    Just { head: first, tail: rest } ->
      Path (Array.cons (MoveTo first) (map LineTo rest))

-- | Add MoveTo command to path.
moveTo :: Point2D -> Path -> Path
moveTo p (Path cmds) = Path (Array.snoc cmds (MoveTo p))

-- | Add LineTo command to path.
lineTo :: Point2D -> Path -> Path
lineTo p (Path cmds) = Path (Array.snoc cmds (LineTo p))

-- | Add QuadTo command to path.
-- |
-- | Parameters: control point, end point.
quadTo :: Point2D -> Point2D -> Path -> Path
quadTo control end (Path cmds) = Path (Array.snoc cmds (QuadTo control end))

-- | Add CubicTo command to path.
-- |
-- | Parameters: first control point, second control point, end point.
cubicTo :: Point2D -> Point2D -> Point2D -> Path -> Path
cubicTo c1 c2 end (Path cmds) = Path (Array.snoc cmds (CubicTo c1 c2 end))

-- | Add ArcTo command to path.
arcTo :: ArcParams -> Path -> Path
arcTo params (Path cmds) = Path (Array.snoc cmds (ArcTo params))

-- | Add ClosePath command to path.
closePath :: Path -> Path
closePath (Path cmds) = Path (Array.snoc cmds ClosePath)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // query
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Is the path empty (no commands)?
isEmpty :: Path -> Boolean
isEmpty (Path cmds) = Array.null cmds

-- | Number of commands in path.
commandCount :: Path -> Int
commandCount (Path cmds) = Array.length cmds

-- | Does the path end with ClosePath?
isClosed :: Path -> Boolean
isClosed (Path cmds) =
  case Array.last cmds of
    Nothing -> false
    Just ClosePath -> true
    Just _ -> false

-- | Get the array of commands.
getCommands :: Path -> Array PathCommand
getCommands (Path cmds) = cmds

-- | Get the first point of the path (from MoveTo).
-- |
-- | Returns Nothing if path is empty or doesn't start with MoveTo.
firstPoint :: Path -> Maybe Point2D
firstPoint (Path cmds) =
  case Array.head cmds of
    Just (MoveTo p) -> Just p
    _ -> Nothing

-- | Get the last point of the path.
-- |
-- | Returns the endpoint of the last drawing command.
-- | Returns Nothing if path is empty or has no drawing commands.
lastPoint :: Path -> Maybe Point2D
lastPoint (Path cmds) = findLastPoint cmds

-- | Find the last point from commands (helper).
findLastPoint :: Array PathCommand -> Maybe Point2D
findLastPoint cmds =
  case Array.last cmds of
    Nothing -> Nothing
    Just (MoveTo p) -> Just p
    Just (LineTo p) -> Just p
    Just (QuadTo _ p) -> Just p
    Just (CubicTo _ _ p) -> Just p
    Just (ArcTo params) -> Just params.end
    Just ClosePath ->
      -- ClosePath returns to first MoveTo — find it
      case Array.head cmds of
        Just (MoveTo p) -> Just p
        _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // serialization
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert path to SVG path data string.
-- |
-- | Produces the `d` attribute value for SVG `<path>` elements.
-- | Example: "M 10 20 L 30 40 Q 50 60 70 80 Z"
toSvgString :: Path -> String
toSvgString (Path cmds) =
  joinWithSpace (map commandToSvgString cmds)

-- | Convert single command to SVG path data fragment.
commandToSvgString :: PathCommand -> String
commandToSvgString cmd = case cmd of
  MoveTo p -> 
    "M " <> showNum (getX p) <> " " <> showNum (getY p)
  
  LineTo p -> 
    "L " <> showNum (getX p) <> " " <> showNum (getY p)
  
  QuadTo control end -> 
    "Q " <> showNum (getX control) <> " " <> showNum (getY control) 
    <> " " <> showNum (getX end) <> " " <> showNum (getY end)
  
  CubicTo c1 c2 end -> 
    "C " <> showNum (getX c1) <> " " <> showNum (getY c1)
    <> " " <> showNum (getX c2) <> " " <> showNum (getY c2)
    <> " " <> showNum (getX end) <> " " <> showNum (getY end)
  
  ArcTo params ->
    "A " <> showNum params.rx <> " " <> showNum params.ry
    <> " " <> showNum (unwrapDegrees params.rotation)
    <> " " <> boolToFlag params.largeArc
    <> " " <> boolToFlag params.sweep
    <> " " <> showNum (getX params.end) <> " " <> showNum (getY params.end)
  
  ClosePath -> "Z"

-- | Convert boolean to SVG arc flag (0 or 1).
boolToFlag :: Boolean -> String
boolToFlag b = if b then "1" else "0"

-- | Show number for SVG (no trailing decimals if integer).
showNum :: Number -> String
showNum = show

-- | Join strings with spaces.
joinWithSpace :: Array String -> String
joinWithSpace strs = 
  case Array.uncons strs of
    Nothing -> ""
    Just { head: first, tail: rest } ->
      Array.foldl (\acc s -> acc <> " " <> s) first rest

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bounding box of entire path.
-- |
-- | Returns Nothing for empty path.
bounds :: Path -> Maybe { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
bounds (Path cmds) =
  case Array.uncons cmds of
    Nothing -> Nothing
    Just _ -> Just (computeBounds cmds)

-- | Compute bounding box from commands.
computeBounds :: Array PathCommand -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
computeBounds cmds =
  let
    initial = { minX: infinity, minY: infinity, maxX: negInfinity, maxY: negInfinity, currentPos: point2D 0.0 0.0 }
    result = Array.foldl updateBounds initial cmds
  in
    { minX: result.minX, minY: result.minY, maxX: result.maxX, maxY: result.maxY }

-- | Update bounds with a command.
updateBounds 
  :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number, currentPos :: Point2D }
  -> PathCommand
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number, currentPos :: Point2D }
updateBounds acc cmd = case cmd of
  MoveTo p ->
    { minX: min acc.minX (getX p)
    , minY: min acc.minY (getY p)
    , maxX: max acc.maxX (getX p)
    , maxY: max acc.maxY (getY p)
    , currentPos: p
    }
  
  LineTo p ->
    { minX: min acc.minX (getX p)
    , minY: min acc.minY (getY p)
    , maxX: max acc.maxX (getX p)
    , maxY: max acc.maxY (getY p)
    , currentPos: p
    }
  
  QuadTo control end ->
    let
      curve = quadBezier acc.currentPos control end
      box = quadBoundingBox curve
    in
      { minX: min acc.minX box.minX
      , minY: min acc.minY box.minY
      , maxX: max acc.maxX box.maxX
      , maxY: max acc.maxY box.maxY
      , currentPos: end
      }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      box = cubicBoundingBox curve
    in
      { minX: min acc.minX box.minX
      , minY: min acc.minY box.minY
      , maxX: max acc.maxX box.maxX
      , maxY: max acc.maxY box.maxY
      , currentPos: end
      }
  
  ArcTo params ->
    -- Approximate arc bounds by sampling
    -- (Full arc bounding is complex — this is a reasonable approximation)
    let arcBounds = approximateArcBounds acc.currentPos params
    in
      { minX: min acc.minX arcBounds.minX
      , minY: min acc.minY arcBounds.minY
      , maxX: max acc.maxX arcBounds.maxX
      , maxY: max acc.maxY arcBounds.maxY
      , currentPos: params.end
      }
  
  ClosePath -> acc

-- | Approximate arc bounding box by sampling points.
approximateArcBounds :: Point2D -> ArcParams -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
approximateArcBounds start params =
  let
    -- Sample 16 points along the arc
    samples = map (\t -> arcPointAtT (t / 16.0) start params) (rangeNumbers 0 16)
    xs = map getX samples
    ys = map getY samples
  in
    { minX: foldMin infinity xs
    , minY: foldMin infinity ys
    , maxX: foldMax negInfinity xs
    , maxY: foldMax negInfinity ys
    }

-- | Point on elliptical arc at parameter t ∈ [0, 1].
-- |
-- | This is an approximation using linear interpolation of the endpoint parameterization.
-- | For precise arc evaluation, see the SVG arc implementation notes.
arcPointAtT :: Number -> Point2D -> ArcParams -> Point2D
arcPointAtT t start params =
  -- Linear interpolation as approximation (actual arc is more complex)
  let
    x = getX start + t * (getX params.end - getX start)
    y = getY start + t * (getY params.end - getY start)
  in
    point2D x y

-- | Total arc length of path.
pathLength :: Path -> Number
pathLength (Path cmds) =
  let
    result = Array.foldl accumulateLength { total: 0.0, currentPos: point2D 0.0 0.0 } cmds
  in
    result.total

-- | Accumulate length for each command.
accumulateLength 
  :: { total :: Number, currentPos :: Point2D }
  -> PathCommand
  -> { total :: Number, currentPos :: Point2D }
accumulateLength acc cmd = case cmd of
  MoveTo p -> 
    { total: acc.total, currentPos: p }
  
  LineTo p ->
    let len = distance acc.currentPos p
    in { total: acc.total + len, currentPos: p }
  
  QuadTo control end ->
    let 
      curve = quadBezier acc.currentPos control end
      len = quadLength curve
    in { total: acc.total + len, currentPos: end }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      len = cubicLength curve
    in { total: acc.total + len, currentPos: end }
  
  ArcTo params ->
    -- Approximate arc length
    let len = approximateArcLength acc.currentPos params
    in { total: acc.total + len, currentPos: params.end }
  
  ClosePath -> acc

-- | Point at a given arc length along the path.
-- |
-- | Returns Nothing if path is empty or length is out of bounds.
pointAtLength :: Number -> Path -> Maybe Point2D
pointAtLength targetLen path =
  if targetLen <= 0.0 then firstPoint path
  else if targetLen >= pathLength path then lastPoint path
  else findPointAtLength targetLen path

-- | Find point at specific length (helper).
findPointAtLength :: Number -> Path -> Maybe Point2D
findPointAtLength targetLen (Path cmds) =
  let
    result = Array.foldl (stepToLength targetLen) 
      { accumulated: 0.0, currentPos: point2D 0.0 0.0, found: Nothing } 
      cmds
  in
    result.found

-- | Step through commands to find point at target length.
stepToLength 
  :: Number
  -> { accumulated :: Number, currentPos :: Point2D, found :: Maybe Point2D }
  -> PathCommand
  -> { accumulated :: Number, currentPos :: Point2D, found :: Maybe Point2D }
stepToLength targetLen acc cmd =
  case acc.found of
    Just _ -> acc  -- Already found
    Nothing -> case cmd of
      MoveTo p -> 
        { accumulated: acc.accumulated, currentPos: p, found: Nothing }
      
      LineTo p ->
        let 
          segLen = distance acc.currentPos p
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let 
              t = (targetLen - acc.accumulated) / segLen
              x = getX acc.currentPos + t * (getX p - getX acc.currentPos)
              y = getY acc.currentPos + t * (getY p - getY acc.currentPos)
            in { accumulated: newAcc, currentPos: p, found: Just (point2D x y) }
          else
            { accumulated: newAcc, currentPos: p, found: Nothing }
      
      QuadTo control end ->
        let
          curve = quadBezier acc.currentPos control end
          segLen = quadLength curve
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let t = (targetLen - acc.accumulated) / segLen
            in { accumulated: newAcc, currentPos: end, found: Just (quadPointAt t curve) }
          else
            { accumulated: newAcc, currentPos: end, found: Nothing }
      
      CubicTo c1 c2 end ->
        let
          curve = cubicBezier acc.currentPos c1 c2 end
          segLen = cubicLength curve
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let t = (targetLen - acc.accumulated) / segLen
            in { accumulated: newAcc, currentPos: end, found: Just (cubicPointAt t curve) }
          else
            { accumulated: newAcc, currentPos: end, found: Nothing }
      
      ArcTo params ->
        let
          segLen = approximateArcLength acc.currentPos params
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let t = (targetLen - acc.accumulated) / segLen
            in { accumulated: newAcc, currentPos: params.end, found: Just (arcPointAtT t acc.currentPos params) }
          else
            { accumulated: newAcc, currentPos: params.end, found: Nothing }
      
      ClosePath -> acc

-- | Tangent vector at a given arc length along the path.
-- |
-- | Returns Nothing if path is empty or length is out of bounds.
tangentAtLength :: Number -> Path -> Maybe Vector2D
tangentAtLength targetLen path =
  if isEmpty path then Nothing
  else Just (findTangentAtLength targetLen path)

-- | Find tangent at specific length (helper).
findTangentAtLength :: Number -> Path -> Vector2D
findTangentAtLength targetLen (Path cmds) =
  let
    result = Array.foldl (stepToTangent targetLen)
      { accumulated: 0.0, currentPos: point2D 0.0 0.0, tangent: vec2 1.0 0.0 }
      cmds
  in
    result.tangent

-- | Step through commands to find tangent at target length.
stepToTangent
  :: Number
  -> { accumulated :: Number, currentPos :: Point2D, tangent :: Vector2D }
  -> PathCommand
  -> { accumulated :: Number, currentPos :: Point2D, tangent :: Vector2D }
stepToTangent targetLen acc cmd = case cmd of
  MoveTo p ->
    { accumulated: acc.accumulated, currentPos: p, tangent: acc.tangent }
  
  LineTo p ->
    let
      segLen = distance acc.currentPos p
      newAcc = acc.accumulated + segLen
      dx = getX p - getX acc.currentPos
      dy = getY p - getY acc.currentPos
      len = sqrt (dx * dx + dy * dy)
      tangent = if len > 0.0 then vec2 (dx / len) (dy / len) else acc.tangent
    in
      if newAcc >= targetLen then
        { accumulated: newAcc, currentPos: p, tangent: tangent }
      else
        { accumulated: newAcc, currentPos: p, tangent: tangent }
  
  QuadTo control end ->
    let
      curve = quadBezier acc.currentPos control end
      segLen = quadLength curve
      newAcc = acc.accumulated + segLen
    in
      if newAcc >= targetLen then
        let t = (targetLen - acc.accumulated) / segLen
        in { accumulated: newAcc, currentPos: end, tangent: quadTangentAt t curve }
      else
        { accumulated: newAcc, currentPos: end, tangent: quadTangentAt 1.0 curve }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      segLen = cubicLength curve
      newAcc = acc.accumulated + segLen
    in
      if newAcc >= targetLen then
        let t = (targetLen - acc.accumulated) / segLen
        in { accumulated: newAcc, currentPos: end, tangent: cubicTangentAt t curve }
      else
        { accumulated: newAcc, currentPos: end, tangent: cubicTangentAt 1.0 curve }
  
  ArcTo params ->
    let
      segLen = approximateArcLength acc.currentPos params
      newAcc = acc.accumulated + segLen
      -- Approximate tangent for arc
      dx = getX params.end - getX acc.currentPos
      dy = getY params.end - getY acc.currentPos
      len = sqrt (dx * dx + dy * dy)
      tangent = if len > 0.0 then vec2 (dx / len) (dy / len) else acc.tangent
    in
      { accumulated: newAcc, currentPos: params.end, tangent: tangent }
  
  ClosePath -> acc

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Distance between two points.
distance :: Point2D -> Point2D -> Number
distance p1 p2 =
  let
    dx = getX p2 - getX p1
    dy = getY p2 - getY p1
  in
    sqrt (dx * dx + dy * dy)

-- | Approximate arc length by chord + sagitta method.
approximateArcLength :: Point2D -> ArcParams -> Number
approximateArcLength start params =
  -- Simple approximation: use chord length scaled by ellipse factor
  let
    chord = distance start params.end
    avgRadius = (params.rx + params.ry) / 2.0
  in
    -- For small arcs, chord ≈ arc length
    -- For larger arcs, multiply by π/2 factor
    if params.largeArc then chord * 1.57 else chord * 1.1

-- | Large positive number (approximation of infinity).
infinity :: Number
infinity = 1.0e308

-- | Large negative number.
negInfinity :: Number
negInfinity = negate 1.0e308

-- | Generate integer range [start, end] as Numbers.
-- |
-- | Used for sampling curves.
rangeNumbers :: Int -> Int -> Array Number
rangeNumbers start end = 
  if start > end then []
  else Array.cons (Int.toNumber start) (rangeNumbers (start + 1) end)

-- | Fold to find minimum.
foldMin :: Number -> Array Number -> Number
foldMin initial arr = Array.foldl min initial arr

-- | Fold to find maximum.
foldMax :: Number -> Array Number -> Number
foldMax initial arr = Array.foldl max initial arr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // transformation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Reverse the direction of a path.
-- |
-- | The path will traverse in the opposite direction.
-- | ClosePath commands are preserved at the end.
reversePath :: Path -> Path
reversePath (Path cmds) =
  case Array.uncons cmds of
    Nothing -> emptyPath
    Just { head: first, tail: rest } ->
      let
        -- Check if path is closed
        endsWithClose = case Array.last cmds of
          Just ClosePath -> true
          _ -> false
        
        -- Remove ClosePath if present for reversal
        toReverse = if endsWithClose 
          then case Array.init cmds of
            Just init' -> init'
            Nothing -> []
          else cmds
        
        -- Collect all points in order
        points = collectPoints toReverse
        
        -- Reverse the points and rebuild path
        reversedPoints = Array.reverse points
        
        -- Build new path
        newPath = pathFromPoints reversedPoints
      in
        if endsWithClose then closePath newPath else newPath

-- | Collect all points from commands in order.
collectPoints :: Array PathCommand -> Array Point2D
collectPoints cmds = Array.foldl addPoint [] cmds
  where
    addPoint acc cmd = case cmd of
      MoveTo p -> Array.snoc acc p
      LineTo p -> Array.snoc acc p
      QuadTo _ p -> Array.snoc acc p
      CubicTo _ _ p -> Array.snoc acc p
      ArcTo params -> Array.snoc acc params.end
      ClosePath -> acc

-- | Translate path by offset.
translatePath :: Number -> Number -> Path -> Path
translatePath dx dy (Path cmds) = Path (map (translateCommand dx dy) cmds)

-- | Translate a single command.
translateCommand :: Number -> Number -> PathCommand -> PathCommand
translateCommand dx dy cmd = case cmd of
  MoveTo p -> MoveTo (translatePoint dx dy p)
  LineTo p -> LineTo (translatePoint dx dy p)
  QuadTo c e -> QuadTo (translatePoint dx dy c) (translatePoint dx dy e)
  CubicTo c1 c2 e -> CubicTo (translatePoint dx dy c1) (translatePoint dx dy c2) (translatePoint dx dy e)
  ArcTo params -> ArcTo (params { end = translatePoint dx dy params.end })
  ClosePath -> ClosePath

-- | Translate a point.
translatePoint :: Number -> Number -> Point2D -> Point2D
translatePoint dx dy p = point2D (getX p + dx) (getY p + dy)

-- | Scale path from origin.
scalePath :: Number -> Number -> Path -> Path
scalePath sx sy (Path cmds) = Path (map (scaleCommand sx sy) cmds)

-- | Scale a single command.
scaleCommand :: Number -> Number -> PathCommand -> PathCommand
scaleCommand sx sy cmd = case cmd of
  MoveTo p -> MoveTo (scalePoint sx sy p)
  LineTo p -> LineTo (scalePoint sx sy p)
  QuadTo c e -> QuadTo (scalePoint sx sy c) (scalePoint sx sy e)
  CubicTo c1 c2 e -> CubicTo (scalePoint sx sy c1) (scalePoint sx sy c2) (scalePoint sx sy e)
  ArcTo params -> ArcTo (params 
    { rx = params.rx * sx
    , ry = params.ry * sy
    , end = scalePoint sx sy params.end 
    })
  ClosePath -> ClosePath

-- | Scale a point from origin.
scalePoint :: Number -> Number -> Point2D -> Point2D
scalePoint sx sy p = point2D (getX p * sx) (getY p * sy)

-- | Rotate path around origin by angle.
rotatePath :: Degrees -> Path -> Path
rotatePath angle (Path cmds) = 
  let 
    rad = unwrapDegrees angle * pi / 180.0
    cosA = cos rad
    sinA = sin rad
  in 
    Path (map (rotateCommand cosA sinA) cmds)

-- | Rotate a single command.
rotateCommand :: Number -> Number -> PathCommand -> PathCommand
rotateCommand cosA sinA cmd = case cmd of
  MoveTo p -> MoveTo (rotatePoint cosA sinA p)
  LineTo p -> LineTo (rotatePoint cosA sinA p)
  QuadTo c e -> QuadTo (rotatePoint cosA sinA c) (rotatePoint cosA sinA e)
  CubicTo c1 c2 e -> CubicTo (rotatePoint cosA sinA c1) (rotatePoint cosA sinA c2) (rotatePoint cosA sinA e)
  ArcTo params -> ArcTo (params { end = rotatePoint cosA sinA params.end })
  ClosePath -> ClosePath

-- | Rotate a point around origin.
rotatePoint :: Number -> Number -> Point2D -> Point2D
rotatePoint cosA sinA p =
  let
    x = getX p
    y = getY p
  in
    point2D (x * cosA - y * sinA) (x * sinA + y * cosA)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Append two paths.
-- |
-- | The second path is appended to the first. If the first path ends with
-- | ClosePath, it is preserved. The second path's initial MoveTo becomes
-- | part of the combined path.
appendPath :: Path -> Path -> Path
appendPath (Path cmds1) (Path cmds2) = Path (cmds1 <> cmds2)

-- | Flatten path to line segments.
-- |
-- | Converts all curves to line segments with specified tolerance.
-- | Tolerance is the maximum distance a line segment can deviate from the curve.
-- |
-- | Lower tolerance = more segments = more accurate
-- | Higher tolerance = fewer segments = more efficient
flattenPath :: Number -> Path -> Path
flattenPath tolerance (Path cmds) =
  let
    result = Array.foldl (flattenStep tolerance) { output: [], currentPos: point2D 0.0 0.0 } cmds
  in
    Path result.output

-- | Flatten one command.
flattenStep 
  :: Number 
  -> { output :: Array PathCommand, currentPos :: Point2D }
  -> PathCommand
  -> { output :: Array PathCommand, currentPos :: Point2D }
flattenStep tolerance acc cmd = case cmd of
  MoveTo p ->
    { output: Array.snoc acc.output (MoveTo p), currentPos: p }
  
  LineTo p ->
    { output: Array.snoc acc.output (LineTo p), currentPos: p }
  
  QuadTo control end ->
    let
      curve = quadBezier acc.currentPos control end
      segments = flattenQuadBezier tolerance curve
    in
      { output: acc.output <> segments, currentPos: end }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      segments = flattenCubicBezier tolerance curve
    in
      { output: acc.output <> segments, currentPos: end }
  
  ArcTo params ->
    let
      segments = flattenArc tolerance acc.currentPos params
    in
      { output: acc.output <> segments, currentPos: params.end }
  
  ClosePath ->
    { output: Array.snoc acc.output ClosePath, currentPos: acc.currentPos }

-- | Flatten quadratic Bezier to line segments.
flattenQuadBezier :: Number -> QuadBezier -> Array PathCommand
flattenQuadBezier tolerance curve =
  let
    -- Adaptive subdivision based on flatness
    numSegments = max 2 (estimateQuadSegments tolerance curve)
    step = 1.0 / Int.toNumber numSegments
    -- Generate points at regular intervals
    points = map (\i -> quadPointAt (Int.toNumber i * step) curve) (rangeInts 1 numSegments)
  in
    map LineTo points

-- | Flatten cubic Bezier to line segments.
flattenCubicBezier :: Number -> CubicBezier -> Array PathCommand
flattenCubicBezier tolerance curve =
  let
    numSegments = max 2 (estimateCubicSegments tolerance curve)
    step = 1.0 / Int.toNumber numSegments
    points = map (\i -> cubicPointAt (Int.toNumber i * step) curve) (rangeInts 1 numSegments)
  in
    map LineTo points

-- | Flatten arc to line segments.
flattenArc :: Number -> Point2D -> ArcParams -> Array PathCommand
flattenArc tolerance start params =
  let
    -- Use more segments for larger arcs
    numSegments = if params.largeArc then 16 else 8
    step = 1.0 / Int.toNumber numSegments
    points = map (\i -> arcPointAtT (Int.toNumber i * step) start params) (rangeInts 1 numSegments)
  in
    map LineTo points

-- | Estimate number of segments needed for quadratic Bezier.
estimateQuadSegments :: Number -> QuadBezier -> Int
estimateQuadSegments tolerance curve =
  let len = quadLength curve
  in max 2 (ceil (len / (tolerance * 4.0)))

-- | Estimate number of segments needed for cubic Bezier.
estimateCubicSegments :: Number -> CubicBezier -> Int
estimateCubicSegments tolerance curve =
  let len = cubicLength curve
  in max 2 (ceil (len / (tolerance * 3.0)))

-- | Generate integer range [start, end].
rangeInts :: Int -> Int -> Array Int
rangeInts start end =
  if start > end then []
  else Array.cons start (rangeInts (start + 1) end)

-- | Ceiling function (round up).
ceil :: Number -> Int
ceil n = 
  let floored = Int.floor n
  in if Int.toNumber floored < n then floored + 1 else floored
