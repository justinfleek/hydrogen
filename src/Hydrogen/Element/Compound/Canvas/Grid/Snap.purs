-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // canvas // grid // snap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Snap Operations — Functions for snapping to grid points.
-- |
-- | ## Operations
-- |
-- | - **nearestSnapPoint**: Find closest snap point within threshold
-- | - **snapPointsInBounds**: Get all snap points in a region
-- | - **snapToGrid**: Snap a position to grid intersections
-- |
-- | ## Dependencies
-- |
-- | - Grid.Types (SnapPoint, SnapPointType, GridSpacing, Subdivisions)
-- | - Data.Array (filter, head, index, concat)
-- | - Data.Foldable (foldl)
-- | - Data.Maybe (Maybe)
-- | - Data.Int (toNumber, floor)

module Hydrogen.Element.Compound.Canvas.Grid.Snap
  ( -- * Snap Operations
    nearestSnapPoint
  , snapPointsInBounds
  , snapToGrid
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , (<)
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , (&&)
  , negate
  )

import Data.Array (filter, snoc, head, index, concat)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Element.Compound.Canvas.Grid.Types
  ( SnapPoint(SnapPoint)
  , snapPointPosition
  , GridSpacing(GridSpacing)
  , Subdivisions(Subdivisions)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // snap operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find the nearest snap point to a position.
-- |
-- | Returns Nothing if no snap points are within the threshold distance.
nearestSnapPoint :: Number -> { x :: Number, y :: Number } -> Array SnapPoint -> Maybe SnapPoint
nearestSnapPoint threshold pos points =
  case points of
    [] -> Nothing
    _ -> 
      let 
        withDist = map (\sp -> { point: sp, dist: distanceTo pos sp }) points
        sorted = sortByDistance withDist
      in case head sorted of
        Nothing -> Nothing
        Just closest -> 
          if closest.dist <= threshold 
            then Just closest.point 
            else Nothing

-- | Get all snap points within given bounds.
snapPointsInBounds :: { x :: Number, y :: Number, width :: Number, height :: Number } 
                   -> Array SnapPoint 
                   -> Array SnapPoint
snapPointsInBounds bounds points =
  filter (\sp -> 
    let p = snapPointPosition sp
    in p.x >= bounds.x && p.x <= bounds.x + bounds.width &&
       p.y >= bounds.y && p.y <= bounds.y + bounds.height
  ) points

-- | Snap a position to the grid.
-- |
-- | Given spacing and subdivisions, find the nearest grid intersection.
snapToGrid :: GridSpacing -> Subdivisions -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
snapToGrid (GridSpacing spacing) (Subdivisions subs) pos =
  let 
    step = spacing / Int.toNumber subs
    snapValue v = Int.toNumber (Int.floor ((v / step) + 0.5)) * step
  in { x: snapValue pos.x, y: snapValue pos.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance from a position to a snap point.
distanceTo :: { x :: Number, y :: Number } -> SnapPoint -> Number
distanceTo pos sp =
  let 
    p = snapPointPosition sp
    dx = pos.x - p.x
    dy = pos.y - p.y
  in sqrt (dx * dx + dy * dy)

-- | Approximate square root using Newton's method.
sqrt :: Number -> Number
sqrt n =
  if n <= 0.0 then 0.0
  else newtonSqrt n (n / 2.0) 0

-- | Newton's method for square root (max 10 iterations).
newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt n guess iterations =
  if iterations >= 10 then guess
  else 
    let nextGuess = (guess + n / guess) / 2.0
    in if abs (nextGuess - guess) < 0.0001 
       then nextGuess 
       else newtonSqrt n nextGuess (iterations + 1)

-- | Absolute value.
abs :: Number -> Number
abs n = if n < 0.0 then negate n else n

-- | Sort by distance (simple insertion sort for small arrays).
sortByDistance :: Array { point :: SnapPoint, dist :: Number } -> Array { point :: SnapPoint, dist :: Number }
sortByDistance arr = foldl insertSorted [] arr

-- | Insert into sorted array.
insertSorted :: Array { point :: SnapPoint, dist :: Number } 
             -> { point :: SnapPoint, dist :: Number } 
             -> Array { point :: SnapPoint, dist :: Number }
insertSorted sorted item =
  let 
    smaller = filter (\x -> x.dist < item.dist) sorted
    larger = filter (\x -> x.dist >= item.dist) sorted
  in concat [smaller, [item], larger]

-- | Map over array.
map :: forall a b. (a -> b) -> Array a -> Array b
map f arr = mapHelper f arr 0 []

mapHelper :: forall a b. (a -> b) -> Array a -> Int -> Array b -> Array b
mapHelper f arr idx acc =
  case index arr idx of
    Nothing -> acc
    Just x -> mapHelper f arr (idx + 1) (snoc acc (f x))
