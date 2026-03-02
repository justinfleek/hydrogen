-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // grid3d // snap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D snap points for precision editing.
-- |
-- | ## Snap Point Types
-- |
-- | - Origin: World origin (0,0,0)
-- | - AxisPoint: Point on an axis
-- | - MajorIntersection: Major grid line intersection
-- | - MinorIntersection: Minor grid line intersection
-- | - PlaneCenter: Center of a grid plane

module Hydrogen.Element.Compound.Canvas.Grid3D.Snap
  ( -- * Snap Point Type
    SnapPoint3DType(Snap3DOrigin, Snap3DAxisPoint, Snap3DMajorIntersection, Snap3DMinorIntersection, Snap3DPlaneCenter)
  
  -- * Snap Point
  , SnapPoint3D
  , snapPoint3D
  , snap3DPosition
  , snap3DType
  
  -- * Snap Operations
  , nearestSnapPoint3D
  , snapToGrid3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (<)
  , (<=)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (snoc, filter, index)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Element.Compound.Canvas.Grid 
  ( GridSpacing
  , spacingValue
  , Subdivisions
  , subdivisionsValue
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( WorldPlane(PlaneXY, PlaneXZ, PlaneYZ)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // snap point types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of 3D snap point.
data SnapPoint3DType
  = Snap3DOrigin             -- ^ World origin (0,0,0)
  | Snap3DAxisPoint          -- ^ Point on an axis
  | Snap3DMajorIntersection  -- ^ Major grid line intersection
  | Snap3DMinorIntersection  -- ^ Minor grid line intersection
  | Snap3DPlaneCenter        -- ^ Center of a grid plane

derive instance eqSnapPoint3DType :: Eq SnapPoint3DType
derive instance ordSnapPoint3DType :: Ord SnapPoint3DType

instance showSnapPoint3DType :: Show SnapPoint3DType where
  show Snap3DOrigin = "origin"
  show Snap3DAxisPoint = "axis"
  show Snap3DMajorIntersection = "major"
  show Snap3DMinorIntersection = "minor"
  show Snap3DPlaneCenter = "plane-center"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // snap point
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 3D snap point.
newtype SnapPoint3D = SnapPoint3D
  { x :: Number
  , y :: Number
  , z :: Number
  , pointType :: SnapPoint3DType
  , plane :: Maybe WorldPlane  -- Which plane this point is on (if any)
  }

derive instance eqSnapPoint3D :: Eq SnapPoint3D

instance showSnapPoint3D :: Show SnapPoint3D where
  show (SnapPoint3D sp) = 
    "Snap3D(" <> show sp.x <> "," <> show sp.y <> "," <> show sp.z <> ")"

-- | Create a 3D snap point.
snapPoint3D :: Number -> Number -> Number -> SnapPoint3DType -> Maybe WorldPlane -> SnapPoint3D
snapPoint3D x y z pointType plane = SnapPoint3D { x, y, z, pointType, plane }

-- | Get snap point position.
snap3DPosition :: SnapPoint3D -> { x :: Number, y :: Number, z :: Number }
snap3DPosition (SnapPoint3D sp) = { x: sp.x, y: sp.y, z: sp.z }

-- | Get snap point type.
snap3DType :: SnapPoint3D -> SnapPoint3DType
snap3DType (SnapPoint3D sp) = sp.pointType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // snap operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find nearest 3D snap point.
nearestSnapPoint3D :: Number 
                   -> { x :: Number, y :: Number, z :: Number } 
                   -> Array SnapPoint3D 
                   -> Maybe SnapPoint3D
nearestSnapPoint3D threshold pos points =
  case points of
    [] -> Nothing
    _ ->
      let 
        withDist = mapSnap (\sp -> { point: sp, dist: distance3D pos sp }) points
        sorted = sortByDistanceSnap withDist
      in case headSnap sorted of
        Nothing -> Nothing
        Just closest ->
          if closest.dist <= threshold
            then Just closest.point
            else Nothing

-- | Snap a 3D position to the grid on a specific plane.
snapToGrid3D :: GridSpacing 
             -> Subdivisions 
             -> WorldPlane
             -> { x :: Number, y :: Number, z :: Number } 
             -> { x :: Number, y :: Number, z :: Number }
snapToGrid3D gridSpace subs plane pos =
  let 
    spacing = spacingValue gridSpace
    subsCount = subdivisionsValue subs
    step = spacing / Int.toNumber subsCount
    snapValue v = Int.toNumber (Int.floor ((v / step) + 0.5)) * step
  in case plane of
    PlaneXY -> { x: snapValue pos.x, y: snapValue pos.y, z: pos.z }
    PlaneXZ -> { x: snapValue pos.x, y: pos.y, z: snapValue pos.z }
    PlaneYZ -> { x: pos.x, y: snapValue pos.y, z: snapValue pos.z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance from position to 3D snap point.
distance3D :: { x :: Number, y :: Number, z :: Number } -> SnapPoint3D -> Number
distance3D pos (SnapPoint3D sp) =
  let
    dx = pos.x - sp.x
    dy = pos.y - sp.y
    dz = pos.z - sp.z
  in sqrtSnap (dx * dx + dy * dy + dz * dz)

-- | Square root using Newton's method.
sqrtSnap :: Number -> Number
sqrtSnap n =
  if n <= 0.0 then 0.0
  else newtonSnap n (n / 2.0) 0

newtonSnap :: Number -> Number -> Int -> Number
newtonSnap n guess iterations =
  if iterations >= 10 then guess
  else
    let nextGuess = (guess + n / guess) / 2.0
    in if absSnap (nextGuess - guess) < 0.0001
       then nextGuess
       else newtonSnap n nextGuess (iterations + 1)

absSnap :: Number -> Number
absSnap n = if n < 0.0 then negate n else n
  where
  negate :: Number -> Number
  negate x = 0.0 - x

-- | Sort by distance.
sortByDistanceSnap :: Array { point :: SnapPoint3D, dist :: Number } 
                   -> Array { point :: SnapPoint3D, dist :: Number }
sortByDistanceSnap arr = foldl insertSortedSnap [] arr

insertSortedSnap :: Array { point :: SnapPoint3D, dist :: Number }
                 -> { point :: SnapPoint3D, dist :: Number }
                 -> Array { point :: SnapPoint3D, dist :: Number }
insertSortedSnap sorted item =
  let
    smaller = filter (\x -> x.dist < item.dist) sorted
    larger = filter (\x -> x.dist >= item.dist) sorted
  in concatSnap [smaller, [item], larger]
  where
  concatSnap :: Array (Array { point :: SnapPoint3D, dist :: Number }) 
             -> Array { point :: SnapPoint3D, dist :: Number }
  concatSnap arrs = foldl appendSnap [] arrs
  
  appendSnap :: Array { point :: SnapPoint3D, dist :: Number }
             -> Array { point :: SnapPoint3D, dist :: Number }
             -> Array { point :: SnapPoint3D, dist :: Number }
  appendSnap acc arr = foldl snoc acc arr

-- | Map for snap arrays.
mapSnap :: forall a b. (a -> b) -> Array a -> Array b
mapSnap f arr = mapSnapHelper f arr 0 []

mapSnapHelper :: forall a b. (a -> b) -> Array a -> Int -> Array b -> Array b
mapSnapHelper f arr idx acc =
  case index arr idx of
    Nothing -> acc
    Just x -> mapSnapHelper f arr (idx + 1) (snoc acc (f x))

-- | Head of array.
headSnap :: forall a. Array a -> Maybe a
headSnap arr = index arr 0
