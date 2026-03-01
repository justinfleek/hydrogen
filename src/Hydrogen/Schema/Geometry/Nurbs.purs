-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // nurbs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Nurbs — Non-Uniform Rational B-Splines for professional curve modeling.
-- |
-- | ## Design Philosophy
-- |
-- | NURBS are the gold standard for precise curve and surface representation
-- | in CAD, professional animation, and industrial design. They extend B-splines
-- | with two key features:
-- |
-- | - **Weights**: Each control point has a weight that affects how strongly
-- |   it "pulls" the curve. Weights enable exact representation of conic
-- |   sections (circles, ellipses, hyperbolas).
-- |
-- | - **Non-uniform knots**: The knot vector can have non-uniform spacing,
-- |   allowing finer control over where the curve "responds" to control points.
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
-- | - The knot vector determines the basis functions
-- |
-- | ## Key Properties
-- |
-- | - **Exact conics**: Circles, ellipses, and arcs can be represented exactly
-- | - **Local control**: Moving one point affects only nearby curve segments
-- | - **Affine invariance**: Transformations apply to control points only
-- | - **Variation diminishing**: The curve is "smoother" than control polygon
-- |
-- | ## Use Cases
-- |
-- | - CAD/CAM systems (Solidworks, AutoCAD, Rhino)
-- | - Typography and font design
-- | - Aircraft and automotive body design
-- | - Professional 3D modeling (Maya, Blender)
-- | - CNC machining tool paths
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Nurbs.Types` — Core type definitions
-- | - `Nurbs.Construction` — Curve constructors
-- | - `Nurbs.Evaluation` — Point and derivative evaluation
-- | - `Nurbs.Operations` — Modification, geometry, conversion

module Hydrogen.Schema.Geometry.Nurbs
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Geometry.Nurbs.Types
  
  -- * Re-exports from Construction
  , module Hydrogen.Schema.Geometry.Nurbs.Construction
  
  -- * Re-exports from Evaluation
  , module Hydrogen.Schema.Geometry.Nurbs.Evaluation
  
  -- * Re-exports from Operations
  , module Hydrogen.Schema.Geometry.Nurbs.Operations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Geometry.Nurbs.Types 
  ( ControlPoint(ControlPoint)
  , KnotVector
  , NurbsCurve(NurbsCurve)
  , controlPointPosition
  , controlPointWeight
  , nurbsControlPoints
  , nurbsKnots
  , nurbsDegree
  , nurbsOrder
  )

import Hydrogen.Schema.Geometry.Nurbs.Construction
  ( nurbsCurve
  , nurbsFromPoints
  , nurbsCircle
  , nurbsArc
  , nurbsEllipse
  )

import Hydrogen.Schema.Geometry.Nurbs.Evaluation
  ( nurbsPointAt
  , nurbsTangentAt
  , nurbsNormalAt
  , nurbsCurvatureAt
  , nurbsParameterRange
  , sampleNurbs
  )

import Hydrogen.Schema.Geometry.Nurbs.Operations
  ( setControlPoint
  , setWeight
  , insertKnot
  , elevateDegree
  , nurbsLength
  , nurbsBoundingBox
  , nurbsToBeziers
  , isValidNurbs
  , nurbsControlPointAt
  , nurbsWeightAt
  , nurbsLengthViaBeziers
  , nurbsBoundingBoxViaBeziers
  , blendNurbsWeights
  )
