-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // animated-transform // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core — PropertyKeyframe, AnimatableValue, and SpeedGraph.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides the foundational types for animation:
-- |
-- | - **PropertyKeyframe** — A single keyframe with value and timing
-- | - **AnimatableValue** — Container for static or animated values
-- | - **SpeedGraph** — Temporal remapping for non-linear time
-- |
-- | These types are the building blocks for all animated properties.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Temporal (Frames)
-- | - Schema.Motion.Interpolation (BezierHandle, SpatialTangent)

module Hydrogen.Schema.Motion.AnimatedTransform.Core
  ( -- * Property Keyframe
    PropertyKeyframe(..)
  , mkPropertyKeyframe
  , keyframeFrame
  , keyframeValue
  , keyframeInterpolation
  , keyframeInHandle
  , keyframeOutHandle
  , keyframeSpatialIn
  , keyframeSpatialOut
  
  -- * Animatable Value Container
  , AnimatableValue(..)
  , mkAnimatableValue
  , mkAnimatableValueStatic
  , isAnimated
  , hasExpression
  , getStaticValue
  , getKeyframes
  
  -- * Speed Graph
  , SpeedGraphPoint(..)
  , SpeedGraph(..)
  , defaultSpeedGraph
  , addSpeedGraphPoint
  , evaluateSpeedGraph
  
  -- * Motion Path Mode
  , MotionPathMode(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , not
  , otherwise
  )

import Data.Array (length, snoc, filter, sortBy, head, index)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Temporal (Frames, unwrapFrames)
import Hydrogen.Schema.Motion.Interpolation 
  ( FullInterpolationType
  , BezierHandle
  , SpatialTangent
  , defaultInHandle
  , defaultOutHandle
  , fitLinear
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // property // keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | A keyframe for a single numeric property.
-- |
-- | Contains the frame position, value, and all interpolation settings.
-- | This is the After Effects keyframe model with full bezier control.
newtype PropertyKeyframe = PropertyKeyframe
  { frame :: Frames                      -- Frame position
  , value :: Number                      -- Property value at this frame
  , interpolation :: FullInterpolationType  -- How to interpolate to next keyframe
  , inHandle :: BezierHandle             -- Incoming bezier handle
  , outHandle :: BezierHandle            -- Outgoing bezier handle
  , spatialIn :: Maybe SpatialTangent    -- Spatial tangent (position props only)
  , spatialOut :: Maybe SpatialTangent   -- Spatial tangent (position props only)
  , roving :: Boolean                    -- Roving keyframe (recalculates timing)
  , selected :: Boolean                  -- UI selection state
  }

derive instance eqPropertyKeyframe :: Eq PropertyKeyframe

instance showPropertyKeyframe :: Show PropertyKeyframe where
  show (PropertyKeyframe kf) = 
    "Keyframe@" <> show kf.frame <> " = " <> show kf.value

instance ordPropertyKeyframe :: Ord PropertyKeyframe where
  compare (PropertyKeyframe a) (PropertyKeyframe b) = 
    compare (unwrapFrames a.frame) (unwrapFrames b.frame)

-- | Create a property keyframe with default interpolation.
mkPropertyKeyframe :: Frames -> Number -> PropertyKeyframe
mkPropertyKeyframe frame value = PropertyKeyframe
  { frame: frame
  , value: value
  , interpolation: fitLinear
  , inHandle: defaultInHandle
  , outHandle: defaultOutHandle
  , spatialIn: Nothing
  , spatialOut: Nothing
  , roving: false
  , selected: false
  }

-- | Get keyframe frame position.
keyframeFrame :: PropertyKeyframe -> Frames
keyframeFrame (PropertyKeyframe kf) = kf.frame

-- | Get keyframe value.
keyframeValue :: PropertyKeyframe -> Number
keyframeValue (PropertyKeyframe kf) = kf.value

-- | Get keyframe interpolation type.
keyframeInterpolation :: PropertyKeyframe -> FullInterpolationType
keyframeInterpolation (PropertyKeyframe kf) = kf.interpolation

-- | Get keyframe incoming bezier handle.
keyframeInHandle :: PropertyKeyframe -> BezierHandle
keyframeInHandle (PropertyKeyframe kf) = kf.inHandle

-- | Get keyframe outgoing bezier handle.
keyframeOutHandle :: PropertyKeyframe -> BezierHandle
keyframeOutHandle (PropertyKeyframe kf) = kf.outHandle

-- | Get keyframe spatial incoming tangent.
keyframeSpatialIn :: PropertyKeyframe -> Maybe SpatialTangent
keyframeSpatialIn (PropertyKeyframe kf) = kf.spatialIn

-- | Get keyframe spatial outgoing tangent.
keyframeSpatialOut :: PropertyKeyframe -> Maybe SpatialTangent
keyframeSpatialOut (PropertyKeyframe kf) = kf.spatialOut

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animatable // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for an animatable property value.
-- |
-- | Can be either static (single value) or animated (multiple keyframes).
-- | Optionally includes expression for procedural animation.
newtype AnimatableValue = AnimatableValue
  { staticValue :: Number                -- Value when not animated
  , keyframes :: Array PropertyKeyframe  -- Keyframes (empty = static)
  , expression :: Maybe String           -- Expression code (overrides keyframes)
  , speedGraph :: Maybe SpeedGraph       -- Speed graph override
  , name :: String                       -- Property name (e.g., "Position X")
  }

derive instance eqAnimatableValue :: Eq AnimatableValue

instance showAnimatableValue :: Show AnimatableValue where
  show (AnimatableValue av) = 
    av.name <> ": " <> 
    (if length av.keyframes > 0 
     then show (length av.keyframes) <> " keyframes"
     else show av.staticValue)

-- | Create an animatable value with initial static value.
mkAnimatableValue :: String -> Number -> AnimatableValue
mkAnimatableValue name value = AnimatableValue
  { staticValue: value
  , keyframes: []
  , expression: Nothing
  , speedGraph: Nothing
  , name: name
  }

-- | Create a static (non-animated) value.
mkAnimatableValueStatic :: String -> Number -> AnimatableValue
mkAnimatableValueStatic = mkAnimatableValue

-- | Check if value is animated (has keyframes).
isAnimated :: AnimatableValue -> Boolean
isAnimated (AnimatableValue av) = length av.keyframes > 0

-- | Check if value has an expression.
hasExpression :: AnimatableValue -> Boolean
hasExpression (AnimatableValue av) = case av.expression of
  Just _ -> true
  Nothing -> false

-- | Get static value (ignoring keyframes).
getStaticValue :: AnimatableValue -> Number
getStaticValue (AnimatableValue av) = av.staticValue

-- | Get keyframes array.
getKeyframes :: AnimatableValue -> Array PropertyKeyframe
getKeyframes (AnimatableValue av) = av.keyframes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // speed // graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | A point on the speed graph.
-- |
-- | Maps input time to output time with bezier control.
newtype SpeedGraphPoint = SpeedGraphPoint
  { frame :: Number           -- Input frame
  , mappedFrame :: Number     -- Output frame (where value is sampled)
  , inHandle :: BezierHandle  -- Incoming bezier handle
  , outHandle :: BezierHandle -- Outgoing bezier handle
  }

derive instance eqSpeedGraphPoint :: Eq SpeedGraphPoint

instance showSpeedGraphPoint :: Show SpeedGraphPoint where
  show (SpeedGraphPoint p) = 
    "SpeedPoint(" <> show p.frame <> " -> " <> show p.mappedFrame <> ")"

-- | Speed graph for temporal remapping.
-- |
-- | Allows non-linear time mapping for a property's animation.
-- | The speed graph overrides normal keyframe interpolation timing.
newtype SpeedGraph = SpeedGraph
  { points :: Array SpeedGraphPoint
  , enabled :: Boolean
  }

derive instance eqSpeedGraph :: Eq SpeedGraph

instance showSpeedGraph :: Show SpeedGraph where
  show (SpeedGraph sg) = 
    "SpeedGraph(" <> show (length sg.points) <> " points)"

-- | Default speed graph (linear 1:1 mapping).
defaultSpeedGraph :: SpeedGraph
defaultSpeedGraph = SpeedGraph
  { points: []
  , enabled: false
  }

-- | Add a point to the speed graph.
addSpeedGraphPoint :: Number -> Number -> SpeedGraph -> SpeedGraph
addSpeedGraphPoint frame mappedFrame (SpeedGraph sg) = SpeedGraph sg
  { points = sortBy comparePoints $ snoc sg.points newPoint
  }
  where
    newPoint = SpeedGraphPoint
      { frame: frame
      , mappedFrame: mappedFrame
      , inHandle: defaultInHandle
      , outHandle: defaultOutHandle
      }
    comparePoints (SpeedGraphPoint a) (SpeedGraphPoint b) = compare a.frame b.frame

-- | Evaluate speed graph at frame to get mapped frame.
evaluateSpeedGraph :: Number -> SpeedGraph -> Number
evaluateSpeedGraph frame (SpeedGraph sg)
  | not sg.enabled = frame  -- Disabled = identity mapping
  | length sg.points < 2 = frame  -- Need at least 2 points
  | otherwise = interpolateSpeedGraph frame sg.points

-- | Interpolate speed graph points.
interpolateSpeedGraph :: Number -> Array SpeedGraphPoint -> Number
interpolateSpeedGraph frame points =
  case findBracketingPoints frame points of
    Nothing -> frame
    Just { before: SpeedGraphPoint p1, after: SpeedGraphPoint p2 } ->
      let
        t = if p2.frame == p1.frame 
            then 0.0
            else (frame - p1.frame) / (p2.frame - p1.frame)
        -- Linear interpolation for now; could use bezier handles
      in p1.mappedFrame + t * (p2.mappedFrame - p1.mappedFrame)

-- | Find bracketing points for interpolation.
findBracketingPoints :: Number -> Array SpeedGraphPoint -> Maybe { before :: SpeedGraphPoint, after :: SpeedGraphPoint }
findBracketingPoints frame points =
  let
    before = filter (\(SpeedGraphPoint p) -> p.frame <= frame) points
    after = filter (\(SpeedGraphPoint p) -> p.frame > frame) points
  in case { b: lastPoint before, a: head after } of
    { b: Just b, a: Just a } -> Just { before: b, after: a }
    _ -> Nothing

-- | Get last point in array.
lastPoint :: forall a. Array a -> Maybe a
lastPoint arr = index arr (length arr - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // motion // path // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion path mode for position properties.
data MotionPathMode
  = MotionPathOff        -- No motion path, linear interpolation
  | MotionPathLinear     -- Linear path between keyframes
  | MotionPathBezier     -- Bezier curve path (uses spatial tangents)
  | MotionPathAutoOrient -- Bezier path + auto-orient rotation

derive instance eqMotionPathMode :: Eq MotionPathMode

instance showMotionPathMode :: Show MotionPathMode where
  show MotionPathOff = "off"
  show MotionPathLinear = "linear"
  show MotionPathBezier = "bezier"
  show MotionPathAutoOrient = "auto-orient"
