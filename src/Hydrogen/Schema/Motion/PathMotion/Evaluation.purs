-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // motion // pathmotion // evaluation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMotion Evaluation — Position, tangent, rotation, and sampling functions.
-- |
-- | ## Exports
-- |
-- | - Position evaluation: `positionAtFrame`, `positionAtTime`, `positionAtProgress`
-- | - Tangent evaluation: `tangentAtFrame`, `tangentAtProgress`
-- | - Rotation evaluation: `rotationAtFrame`
-- | - Full sampling: `sampleAtFrame`, `sampleAtProgress`
-- | - Path length: `pathLength`, `progressToArcLength`, `arcLengthToProgress`
-- | - Frame utilities: `frameToProgress`, `progressToFrame`, `isActiveAtFrame`
-- | - Batch sampling: `sampleFrameRange`, `samplePoints`
-- | - Path filtering: `filterActiveFrames`, `mapSampledPositions`
-- |
-- | ## Dependencies
-- |
-- | - PathMotion.Types (MotionPath, MotionSample, OrientMode)
-- | - PathMotion.Internal (path evaluation helpers)
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D)
-- | - Schema.Geometry.Angle (Degrees)
-- | - Schema.Motion.Easing (Easing evaluation)

module Hydrogen.Schema.Motion.PathMotion.Evaluation
  ( -- * Position Evaluation
    positionAtFrame
  , positionAtTime
  , positionAtProgress
  
  -- * Tangent Evaluation
  , tangentAtFrame
  , tangentAtProgress
  
  -- * Rotation Evaluation
  , rotationAtFrame
  
  -- * Full Sampling
  , sampleAtFrame
  , sampleAtProgress
  
  -- * Path Length
  , pathLength
  , progressToArcLength
  , arcLengthToProgress
  
  -- * Frame Utilities
  , frameToProgress
  , progressToFrame
  , isActiveAtFrame
  
  -- * Batch Sampling
  , sampleFrameRange
  , samplePoints
  
  -- * Path Filtering
  , filterActiveFrames
  , mapSampledPositions
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
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , otherwise
  , map
  )

import Data.Array (snoc, foldl)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, magnitude2)
import Hydrogen.Schema.Geometry.Angle (Degrees(Degrees))
import Hydrogen.Schema.Motion.Easing (evaluate)
import Hydrogen.Schema.Motion.PathMotion.Types 
  ( MotionPath(MotionPath)
  , MotionSample(MotionSample)
  , OrientMode(NoOrient, OrientToPath, OrientToPathFlipped, OrientPerpendicular, OrientCustomOffset)
  )
import Hydrogen.Schema.Motion.PathMotion.Internal 
  ( evaluatePathPosition
  , evaluatePathTangent
  , evaluatePathLength
  , vectorToAngle
  , addDegrees
  , calculateBank
  , clamp01
  , epsilon
  , floorInt
  , floorNum
  , buildArray
  )
import Hydrogen.Schema.Motion.PathMotion.Core (isLooping)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // position evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get position at a specific frame number.
positionAtFrame :: Number -> MotionPath -> Point2D
positionAtFrame frame mp =
  let progress = frameToProgress frame mp
  in positionAtProgress progress mp

-- | Get position at normalized time (0-1).
positionAtTime :: Number -> MotionPath -> Point2D
positionAtTime t mp =
  let progress = clamp01 t
  in positionAtProgress progress mp

-- | Get position at progress value (0-1), applying easing.
positionAtProgress :: Number -> MotionPath -> Point2D
positionAtProgress progress (MotionPath mp) =
  let
    -- Apply easing to progress
    easedProgress = evaluate mp.easing (clamp01 progress)
    
    -- Map to path range
    pathT = mp.startOffset + easedProgress * (mp.endOffset - mp.startOffset)
    
    -- Handle ping-pong
    actualT = if mp.pingPong && pathT > 0.5
              then 1.0 - (pathT - 0.5) * 2.0
              else if mp.pingPong then pathT * 2.0
              else pathT
  in
    evaluatePathPosition mp.source (clamp01 actualT)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // tangent evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get tangent vector at frame.
tangentAtFrame :: Number -> MotionPath -> Vector2D
tangentAtFrame frame mp =
  let progress = frameToProgress frame mp
  in tangentAtProgress progress mp

-- | Tangent at progress value (0-1).
tangentAtProgress :: Number -> MotionPath -> Vector2D
tangentAtProgress progress (MotionPath mp) =
  let
    easedProgress = evaluate mp.easing (clamp01 progress)
    pathT = mp.startOffset + easedProgress * (mp.endOffset - mp.startOffset)
  in
    evaluatePathTangent mp.source (clamp01 pathT)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rotation evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get rotation at frame (based on orient mode).
rotationAtFrame :: Number -> MotionPath -> Degrees
rotationAtFrame frame mp =
  let sample = sampleAtFrame frame mp
      (MotionSample s) = sample
  in s.rotation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // full sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get complete motion sample at frame.
sampleAtFrame :: Number -> MotionPath -> MotionSample
sampleAtFrame frame mp =
  let progress = frameToProgress frame mp
  in sampleAtProgress progress mp

-- | Get complete motion sample at progress (0-1).
sampleAtProgress :: Number -> MotionPath -> MotionSample
sampleAtProgress progress (MotionPath mp) =
  let
    -- Apply easing
    easedProgress = evaluate mp.easing (clamp01 progress)
    pathT = mp.startOffset + easedProgress * (mp.endOffset - mp.startOffset)
    
    -- Handle ping-pong
    actualT = if mp.pingPong && pathT > 0.5
              then 1.0 - (pathT - 0.5) * 2.0
              else if mp.pingPong then pathT * 2.0
              else pathT
    
    clampedT = clamp01 actualT
    
    -- Get position and tangent
    pos = evaluatePathPosition mp.source clampedT
    tan = evaluatePathTangent mp.source clampedT
    
    -- Calculate rotation from tangent
    baseRotation = vectorToAngle tan
    
    -- Apply orient mode
    rotation = case mp.orientMode of
      NoOrient -> Degrees 0.0
      OrientToPath -> baseRotation
      OrientToPathFlipped -> addDegrees baseRotation (Degrees 180.0)
      OrientPerpendicular -> addDegrees baseRotation (Degrees 90.0)
      OrientCustomOffset offset -> addDegrees baseRotation offset
    
    -- Calculate banking (based on curvature/rate of rotation change)
    bank = calculateBank clampedT mp.source mp.bankAngle mp.bankSmoothing
    
    -- Arc length and speed
    totalLength = evaluatePathLength mp.source
    arcLen = clampedT * totalLength  -- Approximation
    speed = magnitude2 tan
  in
    MotionSample
      { position: pos
      , rotation: rotation
      , tangent: tan
      , progress: easedProgress
      , arcLength: arcLen
      , speed: speed
      , bank: bank
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // path length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get total path length.
pathLength :: MotionPath -> Number
pathLength (MotionPath mp) = evaluatePathLength mp.source

-- | Convert normalized progress to arc length.
progressToArcLength :: Number -> MotionPath -> Number
progressToArcLength progress mp =
  clamp01 progress * pathLength mp

-- | Convert arc length to normalized progress.
arcLengthToProgress :: Number -> MotionPath -> Number
arcLengthToProgress arcLen mp =
  let total = pathLength mp
  in if total < epsilon then 0.0 else clamp01 (arcLen / total)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // frame utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert frame number to progress (0-1).
frameToProgress :: Number -> MotionPath -> Number
frameToProgress frame (MotionPath mp) =
  let
    relativeFrame = frame - mp.startFrame
    rawProgress = if mp.durationFrames < epsilon 
                  then 0.0 
                  else relativeFrame / mp.durationFrames
  in
    if mp.loop then
      -- Loop: wrap progress
      let wrapped = rawProgress - floorNum rawProgress
      in if wrapped < 0.0 then wrapped + 1.0 else wrapped
    else
      clamp01 rawProgress

-- | Convert progress to frame number.
progressToFrame :: Number -> MotionPath -> Number
progressToFrame progress (MotionPath mp) =
  mp.startFrame + clamp01 progress * mp.durationFrames

-- | Check if animation is active at frame.
isActiveAtFrame :: Number -> MotionPath -> Boolean
isActiveAtFrame frame (MotionPath mp) =
  let relativeFrame = frame - mp.startFrame
  in if mp.loop then true
     else relativeFrame >= 0.0 && relativeFrame <= mp.durationFrames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // batch sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample motion at every frame in range.
sampleFrameRange :: Number -> Number -> MotionPath -> Array MotionSample
sampleFrameRange startFrame endFrame mp =
  let
    numFrames = Int.toNumber (floorInt (endFrame - startFrame)) + 1.0
  in
    buildArray (floorInt numFrames) (\i ->
      let frame = startFrame + Int.toNumber i
      in Just (sampleAtFrame frame mp)
    )

-- | Sample n evenly-spaced points along path.
samplePoints :: Int -> MotionPath -> Array Point2D
samplePoints n mp =
  if n <= 0 then []
  else buildArray (n + 1) (\i ->
    let progress = Int.toNumber i / Int.toNumber n
    in Just (positionAtProgress progress mp)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // path filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter frame numbers to only those where path is active.
filterActiveFrames :: Array Number -> MotionPath -> Array Number
filterActiveFrames frames mp =
  foldl (\acc frame ->
    if isActiveAtFrame frame mp || isLooping mp
    then snoc acc frame
    else acc
  ) [] frames

-- | Map a function over sampled positions.
mapSampledPositions :: (Point2D -> Point2D) -> Int -> MotionPath -> Array Point2D
mapSampledPositions f n mp =
  map f (samplePoints n mp)
