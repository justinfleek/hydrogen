-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // spatial-keyframe // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Motion Paths — Sequences of spatial keyframes defining paths through space.
-- |
-- | ## Motion Path Architecture
-- |
-- | A motion path is a sequence of spatial keyframes connected by bezier curves.
-- | Each segment between keyframes forms a cubic bezier defined by:
-- |
-- | - Start position + outgoing spatial handle
-- | - End position + incoming spatial handle
-- |
-- | ## Speed Graph
-- |
-- | The speed graph visualizes velocity over time, showing how fast an object
-- | moves along the motion path at each frame.

module Hydrogen.Schema.Motion.SpatialKeyframe.Path
  ( -- * Motion Path 2D
    MotionPath2D
  , motionPath2D
  , motionPath2DFromKeyframes
  , evaluateMotionPath2D
  , motionPathLength2D
  
  -- * Motion Path 3D
  , MotionPath3D
  , motionPath3D
  , motionPath3DFromKeyframes
  , evaluateMotionPath3D
  , motionPathLength3D
  
  -- * Speed Graph
  , SpeedGraph
  , speedGraph
  , speedAt
  , averageSpeed
  , maxSpeed
  , minSpeed
  ) where

import Prelude
  ( ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<=)
  , (<)
  , (>=)
  , (&&)
  , otherwise
  , map
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (index, length, foldl) as Array
import Data.Int (toNumber) as Int
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Schema.Dimension.Temporal (Frames, unwrapFrames)
import Hydrogen.Schema.Motion.SpatialKeyframe.Keyframe
  ( SpatialKeyframe2D
  , SpatialKeyframe3D
  )
import Hydrogen.Schema.Motion.SpatialKeyframe.Types
  ( DimensionMode(DMUnified)
  , SpatialInterpolation(SILinear, SIBezier, SIAuto)
  , TemporalInterpolation(TILinear, TIHold, TIBezier, TIAuto)
  )
import Hydrogen.Schema.Motion.SpatialKeyframe.Bezier
  ( evalBezier2D
  , evalBezier3D
  , applyTemporalEasing
  , bezierArcLength2D
  , bezierArcLength3D
  )
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // motion // path 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D motion path — sequence of spatial keyframes defining a path through space.
type MotionPath2D =
  { keyframes :: Array SpatialKeyframe2D
  , closed :: Boolean           -- ^ Does path loop?
  , dimensionMode :: DimensionMode
  }

-- | Create an empty motion path.
motionPath2D :: MotionPath2D
motionPath2D =
  { keyframes: []
  , closed: pathNotClosed
  , dimensionMode: DMUnified
  }

-- | Create motion path from keyframes.
motionPath2DFromKeyframes :: Array SpatialKeyframe2D -> MotionPath2D
motionPath2DFromKeyframes kfs =
  { keyframes: kfs
  , closed: pathNotClosed
  , dimensionMode: DMUnified
  }

-- | Evaluate position on motion path at a given frame.
-- |
-- | Returns the interpolated position considering both spatial
-- | and temporal curves.
-- |
-- | ## Algorithm
-- |
-- | 1. Find the two keyframes surrounding the target frame
-- | 2. Calculate the normalized time t between them
-- | 3. Apply temporal easing to get the eased parameter u
-- | 4. Evaluate the cubic bezier curve at parameter u
evaluateMotionPath2D :: Frames -> MotionPath2D -> Maybe { x :: Number, y :: Number }
evaluateMotionPath2D targetFrame path =
  case Array.length path.keyframes of
    0 -> Nothing
    1 -> case Array.index path.keyframes 0 of
      Just kf -> Just kf.position
      Nothing -> Nothing
    _ -> findAndInterpolate2D targetFrame path.keyframes

-- | Calculate total arc length of motion path.
-- |
-- | Uses Gaussian quadrature to numerically integrate the arc length
-- | of each bezier segment, then sums them.
motionPathLength2D :: MotionPath2D -> Number
motionPathLength2D path =
  case Array.length path.keyframes of
    0 -> 0.0
    1 -> 0.0
    _ -> sumSegmentLengths2D path.keyframes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // motion // path 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D motion path — sequence of spatial keyframes in 3D space.
type MotionPath3D =
  { keyframes :: Array SpatialKeyframe3D
  , closed :: Boolean
  , dimensionMode :: DimensionMode
  }

-- | Create an empty 3D motion path.
motionPath3D :: MotionPath3D
motionPath3D =
  { keyframes: []
  , closed: pathNotClosed
  , dimensionMode: DMUnified
  }

-- | Create 3D motion path from keyframes.
motionPath3DFromKeyframes :: Array SpatialKeyframe3D -> MotionPath3D
motionPath3DFromKeyframes kfs =
  { keyframes: kfs
  , closed: pathNotClosed
  , dimensionMode: DMUnified
  }

-- | Evaluate position on 3D motion path at a given frame.
-- |
-- | Returns the interpolated position considering both spatial
-- | and temporal curves in 3D space.
evaluateMotionPath3D :: Frames -> MotionPath3D -> Maybe { x :: Number, y :: Number, z :: Number }
evaluateMotionPath3D targetFrame path =
  case Array.length path.keyframes of
    0 -> Nothing
    1 -> case Array.index path.keyframes 0 of
      Just kf -> Just kf.position
      Nothing -> Nothing
    _ -> findAndInterpolate3D targetFrame path.keyframes

-- | Calculate total arc length of 3D motion path.
-- |
-- | Uses Gaussian quadrature to numerically integrate the arc length
-- | of each bezier segment in 3D space.
motionPathLength3D :: MotionPath3D -> Number
motionPathLength3D path =
  case Array.length path.keyframes of
    0 -> 0.0
    1 -> 0.0
    _ -> sumSegmentLengths3D path.keyframes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // speed // graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | Speed graph — represents velocity over time for a property.
-- |
-- | The speed graph shows how fast a property is changing at any point.
-- | For position, this is the actual velocity (distance/time).
type SpeedGraph =
  { samples :: Array { frame :: Number, speed :: Number }
  , minSpeed :: Number
  , maxSpeed :: Number
  , averageSpeed :: Number
  }

-- | Create a speed graph from sample points.
speedGraph :: Array { frame :: Number, speed :: Number } -> SpeedGraph
speedGraph samples =
  let speeds = map (\s -> s.speed) samples
      minS = Array.foldl min 0.0 speeds
      maxS = Array.foldl max 0.0 speeds
      avgS = case Array.length speeds of
        0 -> 0.0
        n -> Array.foldl (+) 0.0 speeds / toNumber n
  in { samples, minSpeed: minS, maxSpeed: maxS, averageSpeed: avgS }

-- | Get speed at a specific frame.
-- |
-- | Finds the two samples surrounding the target frame and linearly
-- | interpolates between them to get the instantaneous speed.
speedAt :: Number -> SpeedGraph -> Number
speedAt fr graph = speedAtImpl fr graph.samples

-- | Get average speed.
averageSpeed :: SpeedGraph -> Number
averageSpeed graph = graph.averageSpeed

-- | Get maximum speed.
maxSpeed :: SpeedGraph -> Number
maxSpeed graph = graph.maxSpeed

-- | Get minimum speed.
minSpeed :: SpeedGraph -> Number
minSpeed graph = graph.minSpeed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Helper for min fold.
min :: Number -> Number -> Number
min a b = if a < b then a else b

-- | Helper for max fold.
max :: Number -> Number -> Number
max a b = if a < b then b else a

-- | Boolean constant for closed path (default is not closed).
pathNotClosed :: Boolean
pathNotClosed = 1 == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // interpolation // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find the two keyframes surrounding a target frame and interpolate.
findAndInterpolate2D 
  :: Frames 
  -> Array SpatialKeyframe2D 
  -> Maybe { x :: Number, y :: Number }
findAndInterpolate2D targetFrame keyframes =
  findSurroundingPair2D targetFrame keyframes 0

-- | Search through keyframes to find the surrounding pair.
findSurroundingPair2D 
  :: Frames 
  -> Array SpatialKeyframe2D 
  -> Int 
  -> Maybe { x :: Number, y :: Number }
findSurroundingPair2D targetFrame keyframes idx =
  let targetFrameNum = unwrapFrames targetFrame
      len = Array.length keyframes
  in if idx >= len - 1
       then 
         -- Past the last keyframe, return last position
         case Array.index keyframes (len - 1) of
           Just lastKeyframe -> Just lastKeyframe.position
           Nothing -> Nothing
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just keyframe1) (Just keyframe2) ->
             let frameTime1 = unwrapFrames keyframe1.frame
                 frameTime2 = unwrapFrames keyframe2.frame
             in if targetFrameNum < frameTime1
                  then Just keyframe1.position  -- Before first keyframe
                  else if targetFrameNum >= frameTime1 && targetFrameNum <= frameTime2
                    then interpolateBetween2D keyframe1 keyframe2 targetFrameNum
                    else findSurroundingPair2D targetFrame keyframes (idx + 1)
           _ -> Nothing

-- | Interpolate between two 2D keyframes at a specific frame.
interpolateBetween2D 
  :: SpatialKeyframe2D 
  -> SpatialKeyframe2D 
  -> Number 
  -> Maybe { x :: Number, y :: Number }
interpolateBetween2D keyframe1 keyframe2 targetFrameNum =
  let frameTime1 = unwrapFrames keyframe1.frame
      frameTime2 = unwrapFrames keyframe2.frame
      duration = frameTime2 - frameTime1
  in if duration <= 0.0
       then Just keyframe1.position
       else
         let -- Normalized linear time (0 to 1)
             linearT = (targetFrameNum - frameTime1) / duration
             -- Apply temporal easing based on interpolation type
             easedT = case keyframe1.temporalInterp of
               TILinear -> linearT
               TIHold -> 0.0  -- Hold stays at start value
               TIBezier -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
               TIAuto -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
             -- Evaluate spatial bezier based on interpolation type
             position = case keyframe1.spatialInterp of
               SILinear -> 
                 { x: Math.lerp keyframe1.position.x keyframe2.position.x easedT
                 , y: Math.lerp keyframe1.position.y keyframe2.position.y easedT
                 }
               SIBezier -> evalBezier2D keyframe1 keyframe2 easedT
               SIAuto -> evalBezier2D keyframe1 keyframe2 easedT
         in Just position

-- | Sum arc lengths of all bezier segments in a 2D path.
sumSegmentLengths2D :: Array SpatialKeyframe2D -> Number
sumSegmentLengths2D keyframes =
  sumPairs2D keyframes 0 0.0

sumPairs2D :: Array SpatialKeyframe2D -> Int -> Number -> Number
sumPairs2D keyframes idx acc =
  let len = Array.length keyframes
  in if idx >= len - 1
       then acc
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just kf1) (Just kf2) ->
             let segmentLen = bezierArcLength2D kf1 kf2
             in sumPairs2D keyframes (idx + 1) (acc + segmentLen)
           _ -> acc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // interpolation // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find surrounding keyframes and interpolate for 3D path.
findAndInterpolate3D 
  :: Frames 
  -> Array SpatialKeyframe3D 
  -> Maybe { x :: Number, y :: Number, z :: Number }
findAndInterpolate3D targetFrame keyframes =
  findSurroundingPair3D targetFrame keyframes 0

findSurroundingPair3D 
  :: Frames 
  -> Array SpatialKeyframe3D 
  -> Int 
  -> Maybe { x :: Number, y :: Number, z :: Number }
findSurroundingPair3D targetFrame keyframes idx =
  let targetFrameNum = unwrapFrames targetFrame
      len = Array.length keyframes
  in if idx >= len - 1
       then 
         case Array.index keyframes (len - 1) of
           Just lastKeyframe -> Just lastKeyframe.position
           Nothing -> Nothing
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just keyframe1) (Just keyframe2) ->
             let frameTime1 = unwrapFrames keyframe1.frame
                 frameTime2 = unwrapFrames keyframe2.frame
             in if targetFrameNum < frameTime1
                  then Just keyframe1.position
                  else if targetFrameNum >= frameTime1 && targetFrameNum <= frameTime2
                    then interpolateBetween3D keyframe1 keyframe2 targetFrameNum
                    else findSurroundingPair3D targetFrame keyframes (idx + 1)
           _ -> Nothing

interpolateBetween3D 
  :: SpatialKeyframe3D 
  -> SpatialKeyframe3D 
  -> Number 
  -> Maybe { x :: Number, y :: Number, z :: Number }
interpolateBetween3D keyframe1 keyframe2 targetFrameNum =
  let frameTime1 = unwrapFrames keyframe1.frame
      frameTime2 = unwrapFrames keyframe2.frame
      duration = frameTime2 - frameTime1
  in if duration <= 0.0
       then Just keyframe1.position
       else
         let linearT = (targetFrameNum - frameTime1) / duration
             easedT = case keyframe1.temporalInterp of
               TILinear -> linearT
               TIHold -> 0.0
               TIBezier -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
               TIAuto -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
             position = case keyframe1.spatialInterp of
               SILinear -> 
                 { x: Math.lerp keyframe1.position.x keyframe2.position.x easedT
                 , y: Math.lerp keyframe1.position.y keyframe2.position.y easedT
                 , z: Math.lerp keyframe1.position.z keyframe2.position.z easedT
                 }
               SIBezier -> evalBezier3D keyframe1 keyframe2 easedT
               SIAuto -> evalBezier3D keyframe1 keyframe2 easedT
         in Just position

-- | Sum arc lengths of all bezier segments in a 3D path.
sumSegmentLengths3D :: Array SpatialKeyframe3D -> Number
sumSegmentLengths3D keyframes =
  sumPairs3D keyframes 0 0.0

sumPairs3D :: Array SpatialKeyframe3D -> Int -> Number -> Number
sumPairs3D keyframes idx acc =
  let len = Array.length keyframes
  in if idx >= len - 1
       then acc
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just kf1) (Just kf2) ->
             let segmentLen = bezierArcLength3D kf1 kf2
             in sumPairs3D keyframes (idx + 1) (acc + segmentLen)
           _ -> acc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // speed // graph // impl
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find speed at a specific frame by interpolating between samples.
speedAtImpl :: Number -> Array { frame :: Number, speed :: Number } -> Number
speedAtImpl targetFr samples =
  findSpeedSample targetFr samples 0

findSpeedSample :: Number -> Array { frame :: Number, speed :: Number } -> Int -> Number
findSpeedSample targetFr samples idx =
  let len = Array.length samples
  in if len == 0
       then 0.0
       else if idx >= len - 1
         then 
           case Array.index samples (len - 1) of
             Just s -> s.speed
             Nothing -> 0.0
         else
           case Tuple (Array.index samples idx) (Array.index samples (idx + 1)) of
             Tuple (Just s1) (Just s2) ->
               if targetFr < s1.frame
                 then s1.speed
                 else if targetFr >= s1.frame && targetFr <= s2.frame
                   then 
                     let t = if s2.frame == s1.frame 
                               then 0.0 
                               else (targetFr - s1.frame) / (s2.frame - s1.frame)
                     in Math.lerp s1.speed s2.speed t
                   else findSpeedSample targetFr samples (idx + 1)
             _ -> 0.0
