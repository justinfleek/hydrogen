# Motion Pillar: Transform System

> Part of the Motion pillar documentation. See [05-motion.md](./05-motion.md) for index.

## Overview

The Transform system provides complete layer transformation infrastructure for 
motion graphics, matching the professional motion graphics transform model:

- **Static transforms** — Snapshot values for position, scale, rotation, anchor, opacity
- **Animated transforms** — Keyframe-driven animation with full bezier control
- **2D and 3D variants** — Separate types for 2D composition and 3D rendering
- **Layer parenting** — Pick-whip style parent-child relationships
- **Rotation order** — Configurable Euler angle order for 3D (avoid gimbal lock)
- **Null objects** — Invisible transform-only layers for rigging

All values use bounded primitives — no Infinity, no NaN, deterministic at scale.

## Source Files

```
src/Hydrogen/Schema/Motion/
├── Transform.purs                      # Static transform types (482 lines)
└── AnimatedTransform/
    ├── Core.purs                       # PropertyKeyframe, AnimatableValue, SpeedGraph (328 lines)
    ├── Properties.purs                 # Animated position, scale, rotation, etc. (347 lines)
    ├── Keyframe.purs                   # Keyframe CRUD operations (120 lines)
    ├── Transform.purs                  # AnimatedTransform2D/3D (137 lines)
    ├── Evaluation.purs                 # Value evaluation at frames (203 lines)
    └── Layer.purs                      # 3D system, parenting, null objects (441 lines)
```

**Total: ~2,058 lines across 7 files**

## Static Transform Types

**Source**: `Transform.purs` (482 lines)

Static transforms represent snapshot values — the concrete position, scale, 
rotation at a specific moment. These are the building blocks that animated 
transforms interpolate between.

## Position

```purescript
-- 2D position relative to composition origin (typically top-left)
newtype Position2D = Position2D { x :: Number, y :: Number }

-- 3D position (Z extends "into" the screen, positive = further away)
newtype Position3D = Position3D { x :: Number, y :: Number, z :: Number }

mkPosition2D  :: Number -> Number -> Position2D
mkPosition3D  :: Number -> Number -> Number -> Position3D
positionZero2D :: Position2D  -- Origin (0, 0)
positionZero3D :: Position3D  -- Origin (0, 0, 0)
```

## Scale

Percentage-based scaling. 100.0 = normal size. Negative values create 
flip/mirror effects. Clamped to ±10000.0.

```purescript
newtype Scale2D = Scale2D { x :: Number, y :: Number }
newtype Scale3D = Scale3D { x :: Number, y :: Number, z :: Number }

mkScale2D       :: Number -> Number -> Scale2D
mkScale3D       :: Number -> Number -> Number -> Scale3D
scaleIdentity2D :: Scale2D  -- 100%, 100%
scaleIdentity3D :: Scale3D  -- 100%, 100%, 100%
scaleUniform2D  :: Number -> Scale2D  -- Same value for X and Y
scaleUniform3D  :: Number -> Scale3D  -- Same value for X, Y, Z
```

## Rotation

Single-axis rotation in degrees. Values are NOT clamped — can exceed 360 
for multiple rotations (common in motion graphics).

```purescript
-- Single-axis rotation (2D or Z-axis for 3D)
newtype Rotation = Rotation { degrees :: Number }

-- 3D rotation (Euler angles, order: X then Y then Z)
newtype Rotation3D = Rotation3D { x :: Number, y :: Number, z :: Number }

-- Orientation (separate from rotation, for cameras/3D layers)
newtype Orientation = Orientation { x :: Number, y :: Number, z :: Number }

mkRotation      :: Number -> Rotation
mkRotation3D    :: Number -> Number -> Number -> Rotation3D
mkOrientation   :: Number -> Number -> Number -> Orientation
rotationZero    :: Rotation      -- 0°
rotation3DZero  :: Rotation3D    -- 0°, 0°, 0°
orientationZero :: Orientation   -- 0°, 0°, 0°
```

## Anchor Point

Transform origin — the point within the layer where transforms are applied from.
(0, 0) = top-left corner of layer bounds.

```purescript
newtype AnchorPoint2D = AnchorPoint2D { x :: Number, y :: Number }
newtype AnchorPoint3D = AnchorPoint3D { x :: Number, y :: Number, z :: Number }

mkAnchorPoint2D :: Number -> Number -> AnchorPoint2D
mkAnchorPoint3D :: Number -> Number -> Number -> AnchorPoint3D
anchorCenter2D  :: Number -> Number -> AnchorPoint2D  -- Centered (width/2, height/2)
anchorCenter3D  :: Number -> Number -> Number -> AnchorPoint3D
anchorTopLeft2D :: AnchorPoint2D  -- (0, 0)
```

## Opacity

Layer visibility from 0.0 (invisible) to 1.0 (fully visible). Clamped.

```purescript
newtype Opacity = Opacity Number

mkOpacity    :: Number -> Opacity  -- Clamped to 0.0-1.0
opacityFull  :: Opacity  -- 1.0 (100%)
opacityHalf  :: Opacity  -- 0.5 (50%)
opacityZero  :: Opacity  -- 0.0 (invisible)
getOpacityValue :: Opacity -> Number
```

## Complete Transforms

Combines all transform properties into a single coherent structure.

```purescript
-- 2D transform (motion graphics standard)
newtype LayerTransform2D = LayerTransform2D
  { position :: Position2D
  , rotation :: Rotation
  , scale    :: Scale2D
  , anchor   :: AnchorPoint2D
  , opacity  :: Opacity
  }

-- 3D transform (cameras, lights, 3D layers)
newtype LayerTransform3D = LayerTransform3D
  { position    :: Position3D
  , rotation    :: Rotation3D
  , orientation :: Orientation
  , scale       :: Scale3D
  , anchor      :: AnchorPoint3D
  , opacity     :: Opacity
  }

defaultTransform2D  :: LayerTransform2D
defaultTransform3D  :: LayerTransform3D
identityTransform2D :: LayerTransform2D  -- No transformation
identityTransform3D :: LayerTransform3D
```

## Animated Transform System

**Source**: `AnimatedTransform/` (6 files, ~1,576 lines)

The animated transform system extends static transforms with keyframe-driven 
animation. Each property (Position X, Rotation, etc.) can be independently 
animated with full bezier control, expressions, and speed graph overrides.

Key concepts:
- **AnimatableValue** — Container wrapping static value + keyframe array
- **PropertyKeyframe** — Single keyframe with value, timing, bezier handles
- **SpeedGraph** — Non-linear time remapping for property animation
- **MotionPathMode** — Linear, bezier, or auto-orient paths for position

## Property Keyframes

**Source**: `AnimatedTransform/Core.purs` (lines 95-161)

A PropertyKeyframe represents a single point on an animation curve, matching 
professional motion graphics keyframe model with full bezier control.

```purescript
newtype PropertyKeyframe = PropertyKeyframe
  { frame :: Frames                      -- Frame position on timeline
  , value :: Number                      -- Property value at this frame
  , interpolation :: FullInterpolationType  -- How to interpolate to next
  , inHandle :: BezierHandle             -- Incoming bezier handle (value graph)
  , outHandle :: BezierHandle            -- Outgoing bezier handle (value graph)
  , spatialIn :: Maybe SpatialTangent    -- Spatial tangent (position only)
  , spatialOut :: Maybe SpatialTangent   -- Spatial tangent (position only)
  , roving :: Boolean                    -- Roving keyframe (auto-calculates timing)
  , selected :: Boolean                  -- UI selection state
  }

-- Construction
mkPropertyKeyframe :: Frames -> Number -> PropertyKeyframe  -- Default interpolation

-- Accessors
keyframeFrame         :: PropertyKeyframe -> Frames
keyframeValue         :: PropertyKeyframe -> Number
keyframeInterpolation :: PropertyKeyframe -> FullInterpolationType
keyframeInHandle      :: PropertyKeyframe -> BezierHandle
keyframeOutHandle     :: PropertyKeyframe -> BezierHandle
keyframeSpatialIn     :: PropertyKeyframe -> Maybe SpatialTangent
keyframeSpatialOut    :: PropertyKeyframe -> Maybe SpatialTangent
```

**Roving keyframes**: When `roving = true`, the keyframe's timing is automatically
recalculated to maintain consistent speed along the motion path. Useful for 
smooth camera moves.

## Animatable Values

**Source**: `AnimatedTransform/Core.purs` (lines 163-218)

AnimatableValue is the container for any animated property. It holds either
a static value (no animation) or an array of keyframes with optional expression.

```purescript
newtype AnimatableValue = AnimatableValue
  { staticValue :: Number                -- Value when not animated
  , keyframes :: Array PropertyKeyframe  -- Keyframes (empty = static)
  , expression :: Maybe String           -- Expression code (overrides keyframes)
  , speedGraph :: Maybe SpeedGraph       -- Speed graph override
  , name :: String                       -- Property name (e.g., "Position X")
  }

-- Construction
mkAnimatableValue       :: String -> Number -> AnimatableValue
mkAnimatableValueStatic :: String -> Number -> AnimatableValue  -- Alias

-- Queries
isAnimated     :: AnimatableValue -> Boolean  -- Has keyframes?
hasExpression  :: AnimatableValue -> Boolean  -- Has expression?
getStaticValue :: AnimatableValue -> Number
getKeyframes   :: AnimatableValue -> Array PropertyKeyframe
```

**Precedence**: Expression > Keyframes > Static Value. If an expression exists,
it overrides keyframes. This matches professional motion graphics behavior.

## Speed Graph

**Source**: `AnimatedTransform/Core.purs` (lines 220-308)

The speed graph allows non-linear time remapping for a property's animation.
Input frames are mapped to different output frames, changing the effective
playback speed.

```purescript
-- Point on speed graph
newtype SpeedGraphPoint = SpeedGraphPoint
  { frame :: Number           -- Input frame (playback time)
  , mappedFrame :: Number     -- Output frame (where value is sampled)
  , inHandle :: BezierHandle  -- Incoming bezier handle
  , outHandle :: BezierHandle -- Outgoing bezier handle
  }

-- Speed graph container
newtype SpeedGraph = SpeedGraph
  { points :: Array SpeedGraphPoint
  , enabled :: Boolean
  }

-- Operations
defaultSpeedGraph   :: SpeedGraph                              -- Linear 1:1 (disabled)
addSpeedGraphPoint  :: Number -> Number -> SpeedGraph -> SpeedGraph
evaluateSpeedGraph  :: Number -> SpeedGraph -> Number          -- Get mapped frame
```

**Use case**: Create slow-motion segments, time freezes, or reverse playback
within an animation without duplicating keyframes.

## Motion Path Mode

**Source**: `AnimatedTransform/Core.purs` (lines 310-328)

Controls how position properties interpolate spatially between keyframes.

```purescript
data MotionPathMode
  = MotionPathOff        -- No motion path, linear interpolation
  | MotionPathLinear     -- Linear path between keyframes
  | MotionPathBezier     -- Bezier curve path (uses spatial tangents)
  | MotionPathAutoOrient -- Bezier path + auto-orient rotation
```

**Auto-orient**: When enabled, the layer's rotation automatically follows the
motion path tangent. Essential for vehicles, arrows, or anything "facing forward".

## Animated Properties

**Source**: `AnimatedTransform/Properties.purs` (347 lines)

Each transform property has both 2D and 3D animated variants. Properties wrap
AnimatableValue for each dimension, enabling independent per-axis animation.

### Animated Position

```purescript
-- 2D position with X/Y as separate animatable values
newtype AnimatedPosition2D = AnimatedPosition2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , separated :: Boolean       -- Are X/Y edited separately in UI?
  , motionPathMode :: MotionPathMode
  }

-- 3D position adds Z axis
newtype AnimatedPosition3D = AnimatedPosition3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  , separated :: Boolean
  , motionPathMode :: MotionPathMode
  }

-- Operations
defaultAnimatedPosition2D    :: AnimatedPosition2D  -- Origin (0, 0)
defaultAnimatedPosition3D    :: AnimatedPosition3D  -- Origin (0, 0, 0)
separatePositionDimensions   :: AnimatedPosition2D -> AnimatedPosition2D
combinePositionDimensions    :: AnimatedPosition2D -> AnimatedPosition2D
getMotionPathMode            :: AnimatedPosition2D -> MotionPathMode
setMotionPathMode            :: MotionPathMode -> AnimatedPosition2D -> AnimatedPosition2D
enableAutoOrient             :: AnimatedPosition2D -> AnimatedPosition2D
```

### Animated Scale

```purescript
-- 2D scale (percentage, 100.0 = 100%)
newtype AnimatedScale2D = AnimatedScale2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , linked :: Boolean  -- Are X/Y linked (uniform scale)?
  }

-- 3D scale adds Z axis
newtype AnimatedScale3D = AnimatedScale3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  , linked :: Boolean
  }

-- Operations
defaultAnimatedScale2D   :: AnimatedScale2D  -- 100%, 100%
defaultAnimatedScale3D   :: AnimatedScale3D  -- 100%, 100%, 100%
linkScaleDimensions      :: AnimatedScale2D -> AnimatedScale2D
unlinkScaleDimensions    :: AnimatedScale2D -> AnimatedScale2D
```

### Animated Rotation

```purescript
-- Single-axis rotation (2D or Z-axis for 3D layers)
newtype AnimatedRotation = AnimatedRotation
  { rotation :: AnimatableValue
  , revolutions :: Int  -- Additional full revolutions (for UI display)
  }

-- 3D rotation with separate X, Y, Z axes plus Orientation
newtype AnimatedRotation3D = AnimatedRotation3D
  { x :: AnimatableValue           -- Pitch
  , y :: AnimatableValue           -- Yaw
  , z :: AnimatableValue           -- Roll
  , orientationX :: AnimatableValue  -- Orientation (for cameras/lights)
  , orientationY :: AnimatableValue
  , orientationZ :: AnimatableValue
  }

-- Operations
defaultAnimatedRotation   :: AnimatedRotation    -- 0°
defaultAnimatedRotation3D :: AnimatedRotation3D  -- 0°, 0°, 0°
```

### Animated Anchor Point

```purescript
-- 2D anchor (transform origin within layer bounds)
newtype AnimatedAnchor2D = AnimatedAnchor2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  }

-- 3D anchor
newtype AnimatedAnchor3D = AnimatedAnchor3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  }

-- Operations
defaultAnimatedAnchor2D :: AnimatedAnchor2D  -- (0, 0)
defaultAnimatedAnchor3D :: AnimatedAnchor3D  -- (0, 0, 0)
```

### Animated Opacity

```purescript
-- Opacity (0-100 percentage)
newtype AnimatedOpacity = AnimatedOpacity
  { opacity :: AnimatableValue
  }

defaultAnimatedOpacity :: AnimatedOpacity  -- 100%
```

## Complete Animated Transforms

**Source**: `AnimatedTransform/Transform.purs` (137 lines)

Complete animated transforms combine all properties into a single structure,
matching professional motion graphics Layer Transform group.

```purescript
-- 2D animated transform (standard motion graphics layer)
newtype AnimatedTransform2D = AnimatedTransform2D
  { position :: AnimatedPosition2D
  , scale :: AnimatedScale2D
  , rotation :: AnimatedRotation
  , anchor :: AnimatedAnchor2D
  , opacity :: AnimatedOpacity
  }

-- 3D animated transform (3D layers, cameras, lights)
newtype AnimatedTransform3D = AnimatedTransform3D
  { position :: AnimatedPosition3D
  , scale :: AnimatedScale3D
  , rotation :: AnimatedRotation3D
  , anchor :: AnimatedAnchor3D
  , opacity :: AnimatedOpacity
  }

-- Construction
defaultAnimatedTransform2D  :: AnimatedTransform2D
defaultAnimatedTransform3D  :: AnimatedTransform3D
identityAnimatedTransform2D :: AnimatedTransform2D  -- Alias for default
identityAnimatedTransform3D :: AnimatedTransform3D  -- Alias for default
```

## Transform Evaluation

**Source**: `AnimatedTransform/Evaluation.purs` (203 lines)

Evaluation computes concrete values from animated properties at a specific frame.
This is the core rendering operation — given a frame number, produce the actual
transform values to apply.

```purescript
-- Evaluate single animatable value at frame
evaluateAt :: Frames -> AnimatableValue -> Number

-- Evaluate keyframes with optional speed graph
evaluateKeyframes :: Frames -> Array PropertyKeyframe -> Maybe SpeedGraph -> Number

-- Apply interpolation curve to t (0-1) value
applyInterpolation :: Number -> FullInterpolationType -> Number

-- Evaluate complete 2D transform, returning all values
evaluateTransform2DAt :: Frames -> AnimatedTransform2D 
  -> { posX :: Number, posY :: Number
     , scaleX :: Number, scaleY :: Number
     , rotation :: Number
     , anchorX :: Number, anchorY :: Number
     , opacity :: Number }

-- Evaluate complete 3D transform
evaluateTransform3DAt :: Frames -> AnimatedTransform3D
  -> { posX :: Number, posY :: Number, posZ :: Number
     , scaleX :: Number, scaleY :: Number, scaleZ :: Number
     , rotX :: Number, rotY :: Number, rotZ :: Number
     , orientX :: Number, orientY :: Number, orientZ :: Number
     , anchorX :: Number, anchorY :: Number, anchorZ :: Number
     , opacity :: Number }
```

**Evaluation process**:
1. If not animated (no keyframes), return static value
2. Apply speed graph if present (remap input frame)
3. Find bracketing keyframes (before and after current frame)
4. If before all keyframes, use first keyframe value
5. If after all keyframes, use last keyframe value
6. Otherwise, interpolate between bracketing keyframes using easing

## Keyframe Management

**Source**: `AnimatedTransform/Keyframe.purs` (120 lines)

CRUD operations for manipulating keyframes on animatable values.

```purescript
-- Add keyframe at frame with value
addKeyframe :: Frames -> Number -> AnimatableValue -> AnimatableValue

-- Remove keyframe at frame
removeKeyframe :: Frames -> AnimatableValue -> AnimatableValue

-- Move keyframe from old frame to new frame
moveKeyframe :: Frames -> Frames -> AnimatableValue -> AnimatableValue

-- Update value of keyframe at frame
updateKeyframeValue :: Frames -> Number -> AnimatableValue -> AnimatableValue

-- Update interpolation type of keyframe at frame
updateKeyframeInterpolation :: Frames -> FullInterpolationType -> AnimatableValue -> AnimatableValue
```

Keyframes are automatically sorted by frame after modification.

## Layer Transform Features

**Source**: `AnimatedTransform/Layer.purs` (441 lines)

Layer-level transform features including 2D/3D switching, rotation order,
parenting, and null objects.

### Layer Dimensionality

```purescript
data LayerDimensionality
  = Layer2D    -- Standard 2D layer
  | Layer3D    -- 3D layer with Z-axis properties

-- Operations
is3DLayer      :: LayerDimensionality -> Boolean
enable3DLayer  :: LayerDimensionality -> LayerDimensionality
disable3DLayer :: LayerDimensionality -> LayerDimensionality
```

**3D mode enables**: Position Z, Scale Z, Rotation X/Y (plus existing Z), 
Orientation X/Y/Z, and material options for lights/cameras.

## Rotation Order

**Source**: `AnimatedTransform/Layer.purs` (lines 129-179)

Euler angle rotation order determines the sequence rotations are applied.
Different orders are optimal for different use cases, and choosing the right
order can help avoid gimbal lock.

```purescript
data RotationOrder
  = RotationXYZ   -- X then Y then Z (motion graphics default)
  | RotationXZY   -- X then Z then Y
  | RotationYXZ   -- Y then X then Z (common in games)
  | RotationYZX   -- Y then Z then X
  | RotationZXY   -- Z then X then Y
  | RotationZYX   -- Z then Y then X (aerospace: heading-pitch-roll)

-- Operations
allRotationOrders     :: Array RotationOrder  -- For UI enumeration
rotationOrderToString :: RotationOrder -> String
defaultRotationOrder  :: RotationOrder  -- XYZ
```

**Why this matters**: When two rotation axes align (gimbal lock), one degree
of freedom is lost. By choosing an appropriate rotation order based on expected
motion, you can push gimbal lock to orientations that won't occur in your animation.

## Layer Parenting

**Source**: `AnimatedTransform/Layer.purs` (lines 181-272)

Layer parenting (pick-whip) creates parent-child relationships where child 
layers inherit transforms from parents. This is fundamental for rigging,
character animation, and hierarchical motion.

```purescript
-- Parent reference
data LayerParent
  = NoParent                    -- Not parented
  | ParentLayer String          -- Parented to layer with this ID
  | ParentNull String           -- Parented to null object with this ID

-- Parent link with selective inheritance
newtype ParentLink = ParentLink
  { parent :: LayerParent
  , inheritPosition :: Boolean   -- Inherit parent position
  , inheritScale :: Boolean      -- Inherit parent scale
  , inheritRotation :: Boolean   -- Inherit parent rotation
  , inheritOpacity :: Boolean    -- Inherit parent opacity (multiply)
  , linkAnchor :: Boolean        -- Link to parent's anchor point
  , jumpToParent :: Boolean      -- Position relative to parent anchor
  }

-- Construction
mkParentLink   :: LayerParent -> ParentLink  -- Default: inherit all
parentToLayer  :: String -> ParentLink       -- Parent to layer ID
parentToNull   :: String -> ParentLink       -- Parent to null ID
clearParent    :: ParentLink                 -- No parent

-- Queries
isParented   :: ParentLink -> Boolean
getParentId  :: ParentLink -> Maybe String

-- Modify inheritance
inheritPosition :: Boolean -> ParentLink -> ParentLink
inheritScale    :: Boolean -> ParentLink -> ParentLink
inheritRotation :: Boolean -> ParentLink -> ParentLink
```

### Selective Inheritance

The ParentLink allows selectively inheriting only some transforms:
- Position only: Move with parent, but maintain independent scale/rotation
- Rotation only: Rotate with parent, but stay in place
- Custom combinations for complex rigs

### Transform State

```purescript
-- Complete layer transform with all features
newtype LayerTransformState = LayerTransformState
  { dimensionality :: LayerDimensionality
  , transform2D :: AnimatedTransform2D
  , transform3D :: AnimatedTransform3D    -- Used when 3D enabled
  , rotationOrder :: RotationOrder
  , parentLink :: ParentLink
  , autoOrient :: Boolean                 -- Auto-orient to motion path
  , collapseTransforms :: Boolean         -- Collapse into parent (precomps)
  }

defaultLayerTransformState :: LayerTransformState  -- 2D, no parent

-- Parent management
setLayerParent :: ParentLink -> LayerTransformState -> LayerTransformState

-- Get effective transform (incorporates parent)
getEffectiveTransform2D :: Frames 
  -> Maybe { posX :: Number, posY :: Number, ... }  -- Parent transform
  -> LayerTransformState 
  -> { posX :: Number, posY :: Number, ... }        -- Effective transform

getEffectiveTransform3D :: Frames 
  -> Maybe { posX :: Number, posY :: Number, posZ :: Number, ... }
  -> LayerTransformState 
  -> { posX :: Number, posY :: Number, posZ :: Number, ... }
```

**Effective transform calculation**: The caller resolves the parent chain and
passes parent transforms. Child position is offset by parent position, child
scale is multiplied by parent scale (as percentage), child rotation is added
to parent rotation.

## Null Objects

**Source**: `AnimatedTransform/Layer.purs` (lines 404-441)

Null objects are invisible layers used only for their transform. They serve
as control rigs for parenting multiple layers.

```purescript
newtype NullObject = NullObject
  { id :: String
  , name :: String
  , transform :: LayerTransformState
  , visible :: Boolean           -- Show in viewport (debugging)
  , locked :: Boolean            -- Prevent editing
  }

-- Construction
mkNullObject :: String -> String -> NullObject  -- id, name

-- Access transform
nullObjectTransform :: NullObject -> LayerTransformState
```

**Common uses**:
- **Group control**: Parent multiple layers to a null, animate the null
- **Pivot point**: Create off-center rotation pivot for a layer
- **Character rig**: Hierarchical nulls for body parts (shoulder → elbow → wrist)
- **Camera rig**: Null for camera orbit, camera as child for look-at
- **Expression targets**: Null position drives expression values on other layers
