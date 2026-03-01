-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // animated-transform // keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe — Management operations for keyframes.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides CRUD operations for keyframes:
-- |
-- | - Add keyframes at specific frames
-- | - Remove keyframes
-- | - Move keyframes to new positions
-- | - Update keyframe values and interpolation
-- |
-- | ## Dependencies
-- |
-- | - AnimatedTransform.Core (AnimatableValue, PropertyKeyframe)
-- | - Schema.Dimension.Temporal (Frames)
-- | - Schema.Motion.Interpolation (FullInterpolationType)

module Hydrogen.Schema.Motion.AnimatedTransform.Keyframe
  ( -- * Keyframe Management
    addKeyframe
  , removeKeyframe
  , moveKeyframe
  , updateKeyframeValue
  , updateKeyframeInterpolation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , compare
  , (==)
  , (/=)
  , map
  , ($)
  )

import Data.Array (snoc, filter, sortBy)

import Hydrogen.Schema.Dimension.Temporal (Frames)
import Hydrogen.Schema.Motion.Interpolation (FullInterpolationType)

import Hydrogen.Schema.Motion.AnimatedTransform.Core
  ( AnimatableValue(AnimatableValue)
  , PropertyKeyframe(PropertyKeyframe)
  , mkPropertyKeyframe
  , keyframeFrame
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // keyframe management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a keyframe to an animatable value.
addKeyframe :: Frames -> Number -> AnimatableValue -> AnimatableValue
addKeyframe frame value (AnimatableValue av) = AnimatableValue av
  { keyframes = sortBy compare $ snoc av.keyframes (mkPropertyKeyframe frame value)
  }

-- | Remove a keyframe at frame.
removeKeyframe :: Frames -> AnimatableValue -> AnimatableValue
removeKeyframe frame (AnimatableValue av) = AnimatableValue av
  { keyframes = filter (\kf -> keyframeFrame kf /= frame) av.keyframes
  }

-- | Move a keyframe to a new frame position.
moveKeyframe :: Frames -> Frames -> AnimatableValue -> AnimatableValue
moveKeyframe oldFrame newFrame (AnimatableValue av) = AnimatableValue av
  { keyframes = sortBy compare $ map (\kf -> 
      if keyframeFrame kf == oldFrame
      then updateKeyframeFrameInternal newFrame kf
      else kf
    ) av.keyframes
  }

-- | Update the value of a keyframe at frame.
updateKeyframeValue :: Frames -> Number -> AnimatableValue -> AnimatableValue
updateKeyframeValue frame newValue (AnimatableValue av) = AnimatableValue av
  { keyframes = map (\kf -> 
      if keyframeFrame kf == frame
      then updateKeyframeValueInternal newValue kf
      else kf
    ) av.keyframes
  }

-- | Update interpolation type of keyframe at frame.
updateKeyframeInterpolation :: Frames -> FullInterpolationType -> AnimatableValue -> AnimatableValue
updateKeyframeInterpolation frame newInterp (AnimatableValue av) = AnimatableValue av
  { keyframes = map (\kf -> 
      if keyframeFrame kf == frame
      then updateKeyframeInterpolationInternal newInterp kf
      else kf
    ) av.keyframes
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update keyframe frame internally.
updateKeyframeFrameInternal :: Frames -> PropertyKeyframe -> PropertyKeyframe
updateKeyframeFrameInternal newFrame (PropertyKeyframe kf) = 
  PropertyKeyframe kf { frame = newFrame }

-- | Update keyframe value internally.
updateKeyframeValueInternal :: Number -> PropertyKeyframe -> PropertyKeyframe
updateKeyframeValueInternal newValue (PropertyKeyframe kf) = 
  PropertyKeyframe kf { value = newValue }

-- | Update keyframe interpolation internally.
updateKeyframeInterpolationInternal :: FullInterpolationType -> PropertyKeyframe -> PropertyKeyframe
updateKeyframeInterpolationInternal newInterp (PropertyKeyframe kf) = 
  PropertyKeyframe kf { interpolation = newInterp }
