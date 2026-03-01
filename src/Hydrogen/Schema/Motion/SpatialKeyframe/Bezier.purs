-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // spatial-keyframe // bezier
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cubic Bezier Mathematics — Core bezier evaluation and arc length calculation.
-- |
-- | ## Cubic Bezier Formula
-- |
-- | B(t) = (1-t)^3 * P0 + 3(1-t)^2 * t * P1 + 3(1-t) * t^2 * P2 + t^3 * P3
-- |
-- | Where:
-- | - P0 = start point
-- | - P1 = start point + outgoing tangent (control point 1)
-- | - P2 = end point + incoming tangent (control point 2)
-- | - P3 = end point
-- |
-- | ## Arc Length Integration
-- |
-- | Arc length = integral from 0 to 1 of |B'(t)| dt
-- |
-- | Computed via 5-point Gaussian quadrature for accuracy.

module Hydrogen.Schema.Motion.SpatialKeyframe.Bezier
  ( -- * Cubic Bezier Evaluation
    cubicBezier
  , cubicBezierDerivative
  , evalBezier2D
  , evalBezier3D
  
  -- * Temporal Easing
  , applyTemporalEasing
  , solveForT
  
  -- * Arc Length Calculation
  , bezierArcLength2D
  , bezierArcLength3D
  , bezierSpeed2D
  , bezierSpeed3D
  ) where

import Prelude
  ( ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>=)
  , (<)
  , negate
  , otherwise
  )

import Hydrogen.Schema.Motion.SpatialKeyframe.Handle
  ( SpatialHandle2D
  , SpatialHandle3D
  , TemporalHandle
  , unwrapSpatialHandle2D
  , unwrapSpatialHandle3D
  , unwrapTemporalHandle
  )
import Hydrogen.Schema.Motion.SpatialKeyframe.Keyframe
  ( SpatialKeyframe2D
  , SpatialKeyframe3D
  )
import Hydrogen.Math.Core as Math
import Data.Array (index, length, drop) as Array
import Data.Tuple (Tuple(Tuple))
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // cubic // bezier // math
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic bezier evaluation for a single component.
-- |
-- | B(t) = (1-t)^3 * P0 + 3(1-t)^2 * t * P1 + 3(1-t) * t^2 * P2 + t^3 * P3
-- |
-- | Where:
-- | - P0 = start point
-- | - P1 = start point + outgoing tangent
-- | - P2 = end point + incoming tangent  
-- | - P3 = end point
cubicBezier :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezier p0 p1 p2 p3 t =
  let t2 = t * t
      t3 = t2 * t
      mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
  in mt3 * p0 + 3.0 * mt2 * t * p1 + 3.0 * mt * t2 * p2 + t3 * p3

-- | Derivative of cubic bezier (velocity).
-- |
-- | B'(t) = 3(1-t)^2 * (P1-P0) + 6(1-t) * t * (P2-P1) + 3t^2 * (P3-P2)
cubicBezierDerivative :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezierDerivative p0 p1 p2 p3 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      t2 = t * t
  in 3.0 * mt2 * (p1 - p0) + 6.0 * mt * t * (p2 - p1) + 3.0 * t2 * (p3 - p2)

-- | Evaluate 2D cubic bezier at parameter t.
-- |
-- | Given two keyframes KF1 and KF2, construct the bezier:
-- | - P0 = KF1.position
-- | - P1 = KF1.position + KF1.spatialOut
-- | - P2 = KF2.position + KF2.spatialIn
-- | - P3 = KF2.position
evalBezier2D 
  :: SpatialKeyframe2D 
  -> SpatialKeyframe2D 
  -> Number 
  -> { x :: Number, y :: Number }
evalBezier2D kf1 kf2 t =
  let -- Extract positions
      p0x = kf1.position.x
      p0y = kf1.position.y
      p3x = kf2.position.x
      p3y = kf2.position.y
      -- Extract tangent handles (relative to their keyframes)
      out1 = unwrapSpatialHandle2D kf1.spatialOut
      in2 = unwrapSpatialHandle2D kf2.spatialIn
      -- Control points (absolute positions)
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
  in { x: cubicBezier p0x p1x p2x p3x t
     , y: cubicBezier p0y p1y p2y p3y t
     }

-- | Evaluate 3D cubic bezier at parameter t.
evalBezier3D 
  :: SpatialKeyframe3D 
  -> SpatialKeyframe3D 
  -> Number 
  -> { x :: Number, y :: Number, z :: Number }
evalBezier3D kf1 kf2 t =
  let p0x = kf1.position.x
      p0y = kf1.position.y
      p0z = kf1.position.z
      p3x = kf2.position.x
      p3y = kf2.position.y
      p3z = kf2.position.z
      out1 = unwrapSpatialHandle3D kf1.spatialOut
      in2 = unwrapSpatialHandle3D kf2.spatialIn
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p1z = p0z + out1.dz
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
      p2z = p3z + in2.dz
  in { x: cubicBezier p0x p1x p2x p3x t
     , y: cubicBezier p0y p1y p2y p3y t
     , z: cubicBezier p0z p1z p2z p3z t
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // temporal // easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply temporal easing to convert normalized time to bezier parameter.
-- |
-- | Temporal handles define a 1D bezier curve that maps linear time to
-- | eased time. This creates ease-in, ease-out effects.
-- |
-- | The temporal bezier goes from (0,0) to (1,1) with control points
-- | derived from the influence values.
applyTemporalEasing :: TemporalHandle -> TemporalHandle -> Number -> Number
applyTemporalEasing outHandle inHandle t =
  let out = unwrapTemporalHandle outHandle
      inp = unwrapTemporalHandle inHandle
      -- Convert influence (0-100%) to bezier control points
      -- For ease-out: control point moves right (x increases)
      -- For ease-in: control point moves left from end (x decreases from 1)
      p1x = out.influence / 100.0
      p1y = 0.0  -- Start at 0 value
      p2x = 1.0 - (inp.influence / 100.0)
      p2y = 1.0  -- End at 1 value
  in cubicBezier 0.0 p1y p2y 1.0 (solveForT p1x p2x t)

-- | Newton-Raphson solver to find t for a given x on the temporal bezier.
-- |
-- | Given x, find t such that cubicBezier(0, p1x, p2x, 1, t) = x
solveForT :: Number -> Number -> Number -> Number
solveForT p1x p2x targetX = newtonSolve p1x p2x targetX targetX 0

newtonSolve :: Number -> Number -> Number -> Number -> Int -> Number
newtonSolve p1x p2x targetX guess iter
  | iter >= 10 = guess  -- Max iterations
  | otherwise =
      let currentX = cubicBezier 0.0 p1x p2x 1.0 guess
          deriv = cubicBezierDerivative 0.0 p1x p2x 1.0 guess
          errorVal = currentX - targetX
      in if Math.abs errorVal < 1.0e-10 then guess
         else if Math.abs deriv < 1.0e-10 then guess  -- Avoid division by near-zero
         else newtonSolve p1x p2x targetX (guess - errorVal / deriv) (iter + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // arc // length // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate arc length of a single 2D bezier segment using Gaussian quadrature.
-- |
-- | Arc length = integral from 0 to 1 of |B'(t)| dt
-- |
-- | Using 5-point Gaussian quadrature for good accuracy.
bezierArcLength2D :: SpatialKeyframe2D -> SpatialKeyframe2D -> Number
bezierArcLength2D kf1 kf2 =
  let -- Gaussian quadrature nodes and weights for [-1, 1] interval
      -- 5-point Legendre-Gauss
      nodes = [ -0.9061798459386640, -0.5384693101056831, 0.0, 0.5384693101056831, 0.9061798459386640 ]
      weights = [ 0.2369268850561891, 0.4786286704993665, 0.5688888888888889, 0.4786286704993665, 0.2369268850561891 ]
      -- Transform from [-1,1] to [0,1]: t = (x + 1) / 2, dt = dx / 2
      -- So integral becomes (1/2) * sum(w_i * f((x_i + 1)/2))
  in 0.5 * gaussSum2D kf1 kf2 nodes weights 0.0

gaussSum2D :: SpatialKeyframe2D -> SpatialKeyframe2D -> Array Number -> Array Number -> Number -> Number
gaussSum2D kf1 kf2 nodes weights acc =
  case Tuple (Array.index nodes 0) (Array.index weights 0) of
    Tuple (Just node) (Just weight) ->
      let t = (node + 1.0) / 2.0  -- Transform to [0,1]
          speed = bezierSpeed2D kf1 kf2 t
          newAcc = acc + weight * speed
          remainingNodes = Array.drop 1 nodes
          remainingWeights = Array.drop 1 weights
      in if Array.length remainingNodes == 0
           then newAcc
           else gaussSum2D kf1 kf2 remainingNodes remainingWeights newAcc
    _ -> acc

-- | Calculate instantaneous speed (magnitude of velocity) on a 2D bezier.
bezierSpeed2D :: SpatialKeyframe2D -> SpatialKeyframe2D -> Number -> Number
bezierSpeed2D kf1 kf2 t =
  let p0x = kf1.position.x
      p0y = kf1.position.y
      p3x = kf2.position.x
      p3y = kf2.position.y
      out1 = unwrapSpatialHandle2D kf1.spatialOut
      in2 = unwrapSpatialHandle2D kf2.spatialIn
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
      -- Velocity components
      vx = cubicBezierDerivative p0x p1x p2x p3x t
      vy = cubicBezierDerivative p0y p1y p2y p3y t
  in Math.hypot vx vy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // arc // length // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate arc length of a single 3D bezier segment using Gaussian quadrature.
bezierArcLength3D :: SpatialKeyframe3D -> SpatialKeyframe3D -> Number
bezierArcLength3D kf1 kf2 =
  let nodes = [ -0.9061798459386640, -0.5384693101056831, 0.0, 0.5384693101056831, 0.9061798459386640 ]
      weights = [ 0.2369268850561891, 0.4786286704993665, 0.5688888888888889, 0.4786286704993665, 0.2369268850561891 ]
  in 0.5 * gaussSum3D kf1 kf2 nodes weights 0.0

gaussSum3D :: SpatialKeyframe3D -> SpatialKeyframe3D -> Array Number -> Array Number -> Number -> Number
gaussSum3D kf1 kf2 nodes weights acc =
  case Tuple (Array.index nodes 0) (Array.index weights 0) of
    Tuple (Just node) (Just weight) ->
      let t = (node + 1.0) / 2.0
          speed = bezierSpeed3D kf1 kf2 t
          newAcc = acc + weight * speed
          remainingNodes = Array.drop 1 nodes
          remainingWeights = Array.drop 1 weights
      in if Array.length remainingNodes == 0
           then newAcc
           else gaussSum3D kf1 kf2 remainingNodes remainingWeights newAcc
    _ -> acc

-- | Calculate instantaneous speed (magnitude of velocity) on a 3D bezier.
bezierSpeed3D :: SpatialKeyframe3D -> SpatialKeyframe3D -> Number -> Number
bezierSpeed3D kf1 kf2 t =
  let p0x = kf1.position.x
      p0y = kf1.position.y
      p0z = kf1.position.z
      p3x = kf2.position.x
      p3y = kf2.position.y
      p3z = kf2.position.z
      out1 = unwrapSpatialHandle3D kf1.spatialOut
      in2 = unwrapSpatialHandle3D kf2.spatialIn
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p1z = p0z + out1.dz
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
      p2z = p3z + in2.dz
      vx = cubicBezierDerivative p0x p1x p2x p3x t
      vy = cubicBezierDerivative p0y p1y p2y p3y t
      vz = cubicBezierDerivative p0z p1z p2z p3z t
  in Math.hypot3 vx vy vz
