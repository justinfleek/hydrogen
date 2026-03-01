-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions for canvas selection.
-- |
-- | ## Functions
-- |
-- | - Testability checks (isTestable)
-- | - Sorting utilities (sortByZIndexDesc)
-- | - Bounds computation (computeBounds)
-- | - Handle generation (generateHandles)
-- | - Point-in-polygon algorithms (raycast, shoelace)
-- | - Array utilities (arrayHead, arrayIndex)
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject)
-- | - Selection.Types (HandleType, SelectionHandle)

module Hydrogen.Element.Compound.Canvas.Selection.Internal
  ( -- * Testability
    isTestable
    
  -- * Sorting
  , sortByZIndexDesc
  
  -- * First Hit
  , findFirstHit
  
  -- * Bounds
  , computeBounds
  
  -- * Handle Generation
  , generateHandles
  , selectionHandle
  
  -- * Point-in-Polygon
  , pointInPolygon
  
  -- * Lasso Helpers
  , anyPoint
  
  -- * Shoelace
  , shoelaceArea
  
  -- * Math Helpers
  , abs'
  , mod'
  
  -- * Array Utilities
  , arrayHead
  , arrayIndex
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , max
  , min
  , negate
  , not
  )

import Data.Array (length, filter, foldl, sortBy)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering(GT, LT, EQ))

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.Selection.Types
  ( HandleType
      ( HandleTopLeft
      , HandleTopCenter
      , HandleTopRight
      , HandleMiddleLeft
      , HandleMiddleRight
      , HandleBottomLeft
      , HandleBottomCenter
      , HandleBottomRight
      , HandleRotation
      , HandleCenter
      )
  , SelectionHandle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // testability
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if object is testable based on options.
isTestable :: { testLocked :: Boolean, testInvisible :: Boolean } 
           -> Types.CanvasObject 
           -> Boolean
isTestable opts obj =
  let visibleOk = Types.objectVisible obj || opts.testInvisible
      lockedOk = not (Types.objectLocked obj) || opts.testLocked
  in visibleOk && lockedOk

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sorting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort objects by zIndex descending.
sortByZIndexDesc :: Array Types.CanvasObject -> Array Types.CanvasObject
sortByZIndexDesc = sortBy compareZIndexDesc
  where
    compareZIndexDesc a b =
      let za = Types.objectZIndex a
          zb = Types.objectZIndex b
      in if za > zb then LT
         else if za < zb then GT
         else EQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // first hit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find first object that contains point.
findFirstHit :: { x :: Number, y :: Number } 
             -> Array Types.CanvasObject 
             -> Maybe Types.CanvasObjectId
findFirstHit point objects =
  case filter (objectContainsPoint' point) objects of
    [] -> Nothing
    hits -> case arrayHead hits of
      Nothing -> Nothing
      Just obj -> Just (Types.objectId obj)

-- | Check if object contains a point (internal helper).
objectContainsPoint' :: { x :: Number, y :: Number } -> Types.CanvasObject -> Boolean
objectContainsPoint' point obj =
  let bounds = Types.objectBounds obj
  in point.x >= bounds.x && point.x <= bounds.x + bounds.width
     && point.y >= bounds.y && point.y <= bounds.y + bounds.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute combined bounds of objects.
computeBounds :: Array Types.CanvasObject 
              -> { x :: Number, y :: Number, width :: Number, height :: Number }
computeBounds objects =
  let
    initial = { minX: infinity, minY: infinity, maxX: negInfinity, maxY: negInfinity }
    result = foldl accumulateBounds initial objects
  in
    { x: result.minX
    , y: result.minY
    , width: result.maxX - result.minX
    , height: result.maxY - result.minY
    }
  where
    accumulateBounds acc obj =
      let bounds = Types.objectBounds obj
      in
        { minX: min acc.minX bounds.x
        , minY: min acc.minY bounds.y
        , maxX: max acc.maxX (bounds.x + bounds.width)
        , maxY: max acc.maxY (bounds.y + bounds.height)
        }
    
    infinity :: Number
    infinity = 1.0e308
    
    negInfinity :: Number
    negInfinity = negate 1.0e308

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // handle generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a selection handle.
selectionHandle :: HandleType -> Number -> Number -> Number -> SelectionHandle
selectionHandle ht x y size = { handleType: ht, x, y, size }

-- | Generate handles for a bounding box.
generateHandles :: { x :: Number, y :: Number, width :: Number, height :: Number }
                -> Number
                -> Array SelectionHandle
generateHandles bounds size =
  let
    x = bounds.x
    y = bounds.y
    w = bounds.width
    h = bounds.height
    cx = x + w / 2.0
    cy = y + h / 2.0
    rotationOffset = 20.0  -- Pixels above top center
  in
    [ selectionHandle HandleTopLeft x y size
    , selectionHandle HandleTopCenter cx y size
    , selectionHandle HandleTopRight (x + w) y size
    , selectionHandle HandleMiddleLeft x cy size
    , selectionHandle HandleMiddleRight (x + w) cy size
    , selectionHandle HandleBottomLeft x (y + h) size
    , selectionHandle HandleBottomCenter cx (y + h) size
    , selectionHandle HandleBottomRight (x + w) (y + h) size
    , selectionHandle HandleRotation cx (y - rotationOffset) size
    , selectionHandle HandleCenter cx cy size
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // point-in-polygon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point-in-polygon test using ray casting.
pointInPolygon :: { x :: Number, y :: Number } 
               -> Array { x :: Number, y :: Number } 
               -> Boolean
pointInPolygon point pts =
  let n = length pts
  in if n < 3 then notYes
     else raycastCount point pts 0 0
  where
    yes = 1 < 2
    notYes = not yes

raycastCount :: { x :: Number, y :: Number }
             -> Array { x :: Number, y :: Number }
             -> Int
             -> Int
             -> Boolean
raycastCount point pts idx count =
  let n = length pts
  in if idx >= n then (count `mod'` 2) /= 0
     else
       case arrayIndex pts idx of
         Nothing -> (count `mod'` 2) /= 0
         Just p1 ->
           let nextIdx = if idx + 1 >= n then 0 else idx + 1
           in case arrayIndex pts nextIdx of
             Nothing -> (count `mod'` 2) /= 0
             Just p2 ->
               let newCount = if rayIntersects point p1 p2 
                              then count + 1 
                              else count
               in raycastCount point pts (idx + 1) newCount

-- | Check if horizontal ray from point intersects line segment.
rayIntersects :: { x :: Number, y :: Number }
              -> { x :: Number, y :: Number }
              -> { x :: Number, y :: Number }
              -> Boolean
rayIntersects point p1 p2 =
  let
    minY = min p1.y p2.y
    maxY = max p1.y p2.y
  in
    if point.y < minY || point.y > maxY then notYes
    else if point.y == p1.y && point.y == p2.y then notYes  -- Horizontal edge
    else
      let 
        -- X coordinate where ray intersects the line
        t = (point.y - p1.y) / (p2.y - p1.y)
        xIntersect = p1.x + t * (p2.x - p1.x)
      in xIntersect > point.x
  where
    yes = 1 < 2
    notYes = not yes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lasso helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if any point satisfies predicate.
anyPoint :: ({ x :: Number, y :: Number } -> Boolean) 
         -> Array { x :: Number, y :: Number } 
         -> Boolean
anyPoint f pts = length (filter f pts) > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // shoelace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shoelace formula for polygon area.
shoelaceArea :: Array { x :: Number, y :: Number } -> Number
shoelaceArea pts = shoelaceHelper pts 0 0.0

shoelaceHelper :: Array { x :: Number, y :: Number } -> Int -> Number -> Number
shoelaceHelper pts idx acc =
  let n = length pts
  in if idx >= n then acc
     else
       case arrayIndex pts idx of
         Nothing -> acc
         Just p1 ->
           let nextIdx = if idx + 1 >= n then 0 else idx + 1
           in case arrayIndex pts nextIdx of
             Nothing -> acc
             Just p2 ->
               let term = (p1.x * p2.y) - (p2.x * p1.y)
               in shoelaceHelper pts (idx + 1) (acc + term)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value.
abs' :: Number -> Number
abs' n = if n < 0.0 then negate n else n

-- | Integer modulo.
mod' :: Int -> Int -> Int
mod' a b = a - ((a / b) * b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe array head.
arrayHead :: forall a. Array a -> Maybe a
arrayHead arr = arrayIndex arr 0

-- | Safe array index.
arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex arr idx =
  if idx < 0 || idx >= length arr
    then Nothing
    else unsafeArrayIndex arr idx

-- | Unsafe array index (bounds already checked).
unsafeArrayIndex :: forall a. Array a -> Int -> Maybe a
unsafeArrayIndex arr idx = 
  -- Use foldl to find element at index
  let result = foldl (\acc item -> 
        case acc of
          { found: Just _, idx: _ } -> acc
          { found: Nothing, idx: i } ->
            if i == idx 
              then { found: Just item, idx: i + 1 }
              else { found: Nothing, idx: i + 1 }
      ) { found: Nothing, idx: 0 } arr
  in result.found
