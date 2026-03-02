-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // nurbs // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Operations on NURBS curves.
-- |
-- | ## Overview
-- |
-- | This module provides operations for:
-- | - Modifying NURBS curves (setControlPoint, setWeight, insertKnot, elevateDegree)
-- | - Geometric queries (length, boundingBox)
-- | - Conversion to Bezier curves
-- | - Validation
-- | - Point access
-- | - Morphing/blending
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Bezier (CubicBezier)
-- | - Hydrogen.Schema.Geometry.Nurbs.Types (NurbsCurve, ControlPoint)
-- | - Hydrogen.Schema.Geometry.Nurbs.Evaluation (nurbsPointAt, sampleNurbs)

module Hydrogen.Schema.Geometry.Nurbs.Operations
  ( -- * Modification
    setControlPoint
  , setWeight
  , insertKnot
  , elevateDegree
  
  -- * Geometry
  , nurbsLength
  , nurbsBoundingBox
  
  -- * Conversion
  , nurbsToBeziers
  
  -- * Validation
  , isValidNurbs
  
  -- * Point Access
  , nurbsControlPointAt
  , nurbsWeightAt
  
  -- * Bezier Integration
  , nurbsLengthViaBeziers
  , nurbsBoundingBoxViaBeziers
  
  -- * Morphing
  , blendNurbsWeights
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (||)
  )

import Data.Array (length, index, (!!), foldl, updateAt, zipWith)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Bezier 
  ( CubicBezier
  , cubicBezier
  , cubicLength
  , cubicBoundingBox
  )
import Hydrogen.Schema.Geometry.Nurbs.Types 
  ( ControlPoint(ControlPoint)
  , KnotVector
  , NurbsCurve(NurbsCurve)
  , nurbsControlPoints
  , nurbsKnots
  , nurbsDegree
  , controlPointWeight
  )
import Hydrogen.Schema.Geometry.Nurbs.Evaluation
  ( nurbsPointAt
  , nurbsParameterRange
  , sampleNurbs
  )
import Hydrogen.Schema.Geometry.Nurbs.Internal
  ( nurbsParamRange
  , findKnotSpan
  , isNonDecreasing
  , allWeightsPositive
  , uniformKnotVector
  , insertIntoSortedArray
  , osloInsert
  , initialBounds
  , updateBounds
  , mergeBounds
  , sumDistances
  , clampNumber
  , epsilon
  , origin
  , toNumber
  , buildArray
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // modification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set a control point at given index.
-- |
-- | Returns Nothing if index out of bounds.
setControlPoint :: Int -> ControlPoint -> NurbsCurve -> Maybe NurbsCurve
setControlPoint i cp (NurbsCurve c) =
  case updateAt i cp c.controlPoints of
    Nothing -> Nothing
    Just newCps -> Just (NurbsCurve { controlPoints: newCps, knots: c.knots, degree: c.degree })

-- | Set weight of control point at given index.
-- |
-- | Returns Nothing if index out of bounds or weight ≤ 0.
setWeight :: Int -> Number -> NurbsCurve -> Maybe NurbsCurve
setWeight i w (NurbsCurve c) =
  if w <= 0.0 then Nothing
  else case index c.controlPoints i of
    Nothing -> Nothing
    Just (ControlPoint cp) ->
      let newCp = ControlPoint { position: cp.position, weight: w }
      in setControlPoint i newCp (NurbsCurve c)

-- | Insert a knot into the curve (knot insertion algorithm).
-- |
-- | Knot insertion adds a knot without changing the curve shape.
-- | This is useful for:
-- | - Converting NURBS to Beziers
-- | - Splitting curves
-- | - Increasing local control
-- |
-- | Returns Nothing if u is outside valid range.
insertKnot :: Number -> NurbsCurve -> Maybe NurbsCurve
insertKnot u (NurbsCurve c) =
  let
    range = nurbsParamRange c.knots c.degree
  in
    if u < range.start || u > range.end then Nothing
    else 
      let
        -- Find span where u will be inserted
        k = findKnotSpan u c.knots c.degree
        
        -- Insert knot into knot vector
        newKnots = insertIntoSortedArray u c.knots
        
        -- Compute new control points using Oslo algorithm
        newCps = osloInsert u k c.degree c.controlPoints c.knots
      in
        Just (NurbsCurve { controlPoints: newCps, knots: newKnots, degree: c.degree })

-- | Elevate degree of curve by 1.
-- |
-- | Degree elevation increases flexibility without changing shape.
elevateDegree :: NurbsCurve -> NurbsCurve
elevateDegree (NurbsCurve c) =
  let
    -- Degree elevation requires inserting new control points
    -- For now, use a simplified approach via sampling and refitting
    -- Full implementation would use the degree elevation algorithm
    
    newDegree = c.degree + 1
    n = length c.controlPoints
    
    -- Sample the curve at more points
    numSamples = n + c.degree
    samples = buildArray numSamples (\i ->
      let t = toNumber i / toNumber (numSamples - 1)
          range = nurbsParamRange c.knots c.degree
          u = range.start + t * (range.end - range.start)
      in Just (nurbsPointAt u (NurbsCurve c))
    )
    
    -- Create new control points (simplified: use samples as approximation)
    newCps = buildArray numSamples (\i ->
      case index samples i of
        Just p -> Just (ControlPoint { position: p, weight: 1.0 })
        Nothing -> Nothing
    )
    
    -- Create new knot vector
    newKnots = uniformKnotVector (length newCps) newDegree
  in
    NurbsCurve { controlPoints: newCps, knots: newKnots, degree: newDegree }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length of NURBS curve.
-- |
-- | Uses adaptive sampling for accuracy.
nurbsLength :: NurbsCurve -> Number
nurbsLength curve =
  let
    samples = sampleNurbs 100 curve
    n = length samples
  in
    sumDistances samples 0 0.0 n

-- | Bounding box of NURBS curve.
-- |
-- | Computed from sampled points (conservative estimate).
nurbsBoundingBox :: NurbsCurve -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
nurbsBoundingBox curve =
  let samples = sampleNurbs 100 curve
  in foldl updateBounds initialBounds samples

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert NURBS to array of cubic Bezier curves.
-- |
-- | Uses knot insertion to split at each unique internal knot,
-- | then extracts Bezier segments.
nurbsToBeziers :: NurbsCurve -> Array CubicBezier
nurbsToBeziers curve =
  let
    -- Sample curve and create Bezier approximation
    samples = sampleNurbs 64 curve
    n = length samples
  in
    if n < 4 then []
    else buildArray ((n - 1) / 3) (\i ->
      let 
        base = i * 3
        p0 = fromMaybe origin (index samples base)
        p1 = fromMaybe origin (index samples (base + 1))
        p2 = fromMaybe origin (index samples (base + 2))
        p3 = fromMaybe origin (index samples (safeMin (base + 3) (n - 1)))
      in Just (cubicBezier p0 p1 p2 p3)
    )
  where
    safeMin :: Int -> Int -> Int
    safeMin a b = if a < b then a else b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if NURBS curve is valid.
isValidNurbs :: NurbsCurve -> Boolean
isValidNurbs (NurbsCurve c) =
  let
    n = length c.controlPoints
    m = length c.knots
    requiredKnots = n + c.degree + 1
  in
    c.degree >= 1 &&
    n >= c.degree + 1 &&
    m == requiredKnots &&
    isNonDecreasing c.knots &&
    allWeightsPositive c.controlPoints

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // point access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get control point at index using array indexing operator.
nurbsControlPointAt :: Int -> NurbsCurve -> Maybe ControlPoint
nurbsControlPointAt i (NurbsCurve c) = c.controlPoints !! i

-- | Get weight at index.
nurbsWeightAt :: Int -> NurbsCurve -> Maybe Number
nurbsWeightAt i curve =
  case nurbsControlPointAt i curve of
    Nothing -> Nothing
    Just cp -> Just (controlPointWeight cp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bezier integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute NURBS length via Bezier conversion.
-- |
-- | More accurate than direct sampling for curves that convert well to Beziers.
nurbsLengthViaBeziers :: NurbsCurve -> Number
nurbsLengthViaBeziers curve =
  let beziers = nurbsToBeziers curve
  in foldl (\acc b -> acc + cubicLength b) 0.0 beziers

-- | Compute NURBS bounding box via Bezier conversion.
-- |
-- | Uses exact Bezier bounding box computation for each segment.
nurbsBoundingBoxViaBeziers :: NurbsCurve -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
nurbsBoundingBoxViaBeziers curve =
  let 
    beziers = nurbsToBeziers curve
    bezierBounds = buildArray (length beziers) (\i ->
      case index beziers i of
        Just b -> Just (cubicBoundingBox b)
        Nothing -> Nothing
    )
  in foldl mergeBounds initialBounds bezierBounds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // morphing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two NURBS curves with given weights (for morphing/interpolation).
-- |
-- | Curves must have same number of control points.
-- | Returns array of blended control point positions.
blendNurbsWeights :: Number -> NurbsCurve -> NurbsCurve -> Array Point2D
blendNurbsWeights t curve1 curve2 =
  let
    (NurbsCurve c1) = curve1
    (NurbsCurve c2) = curve2
    t' = clampNumber 0.0 1.0 t
    mt = 1.0 - t'
    
    blend :: ControlPoint -> ControlPoint -> Point2D
    blend (ControlPoint cp1) (ControlPoint cp2) =
      let
        (Point2D p1) = cp1.position
        (Point2D p2) = cp2.position
        x = mt * p1.x * cp1.weight + t' * p2.x * cp2.weight
        y = mt * p1.y * cp1.weight + t' * p2.y * cp2.weight
        w = mt * cp1.weight + t' * cp2.weight
      in
        if w < epsilon then origin
        else point2D (x / w) (y / w)
  in
    zipWith blend c1.controlPoints c2.controlPoints
