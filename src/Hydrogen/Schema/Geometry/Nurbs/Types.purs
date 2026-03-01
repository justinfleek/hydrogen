-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // nurbs // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for NURBS (Non-Uniform Rational B-Splines).
-- |
-- | ## Overview
-- |
-- | This module defines the fundamental types for NURBS curve representation:
-- | - ControlPoint: Weighted control point with position and weight
-- | - KnotVector: Non-decreasing sequence of parameter values
-- | - NurbsCurve: Complete NURBS curve with control points, knots, and degree
-- |
-- | ## Mathematical Foundation
-- |
-- | A NURBS curve of degree p is defined as:
-- |
-- | ```
-- | C(u) = Σᵢ (Nᵢ,ₚ(u) · wᵢ · Pᵢ) / Σᵢ (Nᵢ,ₚ(u) · wᵢ)
-- | ```
-- |
-- | Where:
-- | - Pᵢ are control points
-- | - wᵢ are weights (positive numbers)
-- | - Nᵢ,ₚ(u) are B-spline basis functions of degree p
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D for positions)

module Hydrogen.Schema.Geometry.Nurbs.Types
  ( -- * Control Point
    ControlPoint(ControlPoint)
  , controlPointPosition
  , controlPointWeight
  
  -- * Knot Vector
  , KnotVector
  
  -- * NURBS Curve
  , NurbsCurve(NurbsCurve)
  , nurbsControlPoints
  , nurbsKnots
  , nurbsDegree
  , nurbsOrder
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (<>)
  )

import Data.Array (length)

import Hydrogen.Schema.Geometry.Point (Point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // control point
-- ═════════════════════════════════════════════════════════════════════════════

-- | A weighted control point for NURBS curves.
-- |
-- | Weight > 0 always. Higher weight pulls the curve closer to the point.
-- | Weight = 1 gives standard B-spline behavior.
newtype ControlPoint = ControlPoint
  { position :: Point2D
  , weight :: Number
  }

derive instance eqControlPoint :: Eq ControlPoint

instance showControlPoint :: Show ControlPoint where
  show (ControlPoint cp) = "(ControlPoint pos:" <> show cp.position 
    <> " w:" <> show cp.weight <> ")"

-- | Get position from control point.
controlPointPosition :: ControlPoint -> Point2D
controlPointPosition (ControlPoint cp) = cp.position

-- | Get weight from control point.
controlPointWeight :: ControlPoint -> Number
controlPointWeight (ControlPoint cp) = cp.weight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // knot vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Knot vector for NURBS.
-- |
-- | A non-decreasing sequence of parameter values.
-- | For a curve of degree p with n control points:
-- | - Knot vector has m = n + p + 1 values
-- | - First p+1 knots are often clamped (equal to first value)
-- | - Last p+1 knots are often clamped (equal to last value)
type KnotVector = Array Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // nurbs curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | NURBS (Non-Uniform Rational B-Spline) curve.
-- |
-- | Degree p curve with n control points requires n + p + 1 knots.
newtype NurbsCurve = NurbsCurve
  { controlPoints :: Array ControlPoint
  , knots :: KnotVector
  , degree :: Int
  }

derive instance eqNurbsCurve :: Eq NurbsCurve

instance showNurbsCurve :: Show NurbsCurve where
  show (NurbsCurve c) = "(NurbsCurve degree:" <> show c.degree 
    <> " points:" <> show (length c.controlPoints)
    <> " knots:" <> show (length c.knots) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get control points of NURBS curve.
nurbsControlPoints :: NurbsCurve -> Array ControlPoint
nurbsControlPoints (NurbsCurve c) = c.controlPoints

-- | Get knot vector of NURBS curve.
nurbsKnots :: NurbsCurve -> KnotVector
nurbsKnots (NurbsCurve c) = c.knots

-- | Get degree of NURBS curve.
nurbsDegree :: NurbsCurve -> Int
nurbsDegree (NurbsCurve c) = c.degree

-- | Get order of NURBS curve (degree + 1).
nurbsOrder :: NurbsCurve -> Int
nurbsOrder (NurbsCurve c) = c.degree + 1
