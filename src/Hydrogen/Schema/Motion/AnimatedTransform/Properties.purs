-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // animated-transform // properties
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Properties — Animated property types for Position, Scale, Rotation, etc.
-- |
-- | ## Design Philosophy
-- |
-- | Each transform property (Position, Scale, Rotation, Anchor, Opacity) has
-- | both 2D and 3D variants. All properties wrap AnimatableValue for each
-- | component, enabling independent animation of each dimension.
-- |
-- | ## Dependencies
-- |
-- | - AnimatedTransform.Core (AnimatableValue, MotionPathMode, mkAnimatableValue)

module Hydrogen.Schema.Motion.AnimatedTransform.Properties
  ( -- * Position Properties
    AnimatedPosition2D(AnimatedPosition2D)
  , AnimatedPosition3D(AnimatedPosition3D)
  , defaultAnimatedPosition2D
  , defaultAnimatedPosition3D
  , separatePositionDimensions
  , combinePositionDimensions
  , getMotionPathMode
  , setMotionPathMode
  , enableAutoOrient
  
  -- * Scale Properties
  , AnimatedScale2D(AnimatedScale2D)
  , AnimatedScale3D(AnimatedScale3D)
  , defaultAnimatedScale2D
  , defaultAnimatedScale3D
  , linkScaleDimensions
  , unlinkScaleDimensions
  
  -- * Rotation Properties
  , AnimatedRotation(AnimatedRotation)
  , AnimatedRotation3D(AnimatedRotation3D)
  , defaultAnimatedRotation
  , defaultAnimatedRotation3D
  
  -- * Anchor Point Properties
  , AnimatedAnchor2D(AnimatedAnchor2D)
  , AnimatedAnchor3D(AnimatedAnchor3D)
  , defaultAnimatedAnchor2D
  , defaultAnimatedAnchor3D
  
  -- * Opacity Property
  , AnimatedOpacity(AnimatedOpacity)
  , defaultAnimatedOpacity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.AnimatedTransform.Core
  ( AnimatableValue
  , MotionPathMode
    ( MotionPathOff
    , MotionPathLinear
    , MotionPathBezier
    , MotionPathAutoOrient
    )
  , mkAnimatableValue
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // animated // position 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 2D position with X and Y as separate properties.
-- |
-- | Allows independent animation of each dimension.
newtype AnimatedPosition2D = AnimatedPosition2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , separated :: Boolean       -- Are X/Y edited separately?
  , motionPathMode :: MotionPathMode
  }

derive instance eqAnimatedPosition2D :: Eq AnimatedPosition2D

instance showAnimatedPosition2D :: Show AnimatedPosition2D where
  show (AnimatedPosition2D p) = 
    "Position2D(" <> show p.x <> ", " <> show p.y <> ")"

-- | Default animated position at origin.
defaultAnimatedPosition2D :: AnimatedPosition2D
defaultAnimatedPosition2D = AnimatedPosition2D
  { x: mkAnimatableValue "Position X" 0.0
  , y: mkAnimatableValue "Position Y" 0.0
  , separated: false
  , motionPathMode: MotionPathBezier
  }

-- | Separate position into independent X/Y dimensions.
separatePositionDimensions :: AnimatedPosition2D -> AnimatedPosition2D
separatePositionDimensions (AnimatedPosition2D p) = 
  AnimatedPosition2D p { separated = true }

-- | Combine position dimensions (edit together).
combinePositionDimensions :: AnimatedPosition2D -> AnimatedPosition2D
combinePositionDimensions (AnimatedPosition2D p) = 
  AnimatedPosition2D p { separated = false }

-- | Get motion path mode from animated position.
getMotionPathMode :: AnimatedPosition2D -> MotionPathMode
getMotionPathMode (AnimatedPosition2D pos) = pos.motionPathMode

-- | Set motion path mode on animated position.
setMotionPathMode :: MotionPathMode -> AnimatedPosition2D -> AnimatedPosition2D
setMotionPathMode mode (AnimatedPosition2D pos) = 
  AnimatedPosition2D pos { motionPathMode = mode }

-- | Enable auto-orient rotation to path.
enableAutoOrient :: AnimatedPosition2D -> AnimatedPosition2D
enableAutoOrient = setMotionPathMode MotionPathAutoOrient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // animated // position 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D position with X, Y, Z as separate properties.
newtype AnimatedPosition3D = AnimatedPosition3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  , separated :: Boolean
  , motionPathMode :: MotionPathMode
  }

derive instance eqAnimatedPosition3D :: Eq AnimatedPosition3D

instance showAnimatedPosition3D :: Show AnimatedPosition3D where
  show (AnimatedPosition3D p) = 
    "Position3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Default animated 3D position at origin.
defaultAnimatedPosition3D :: AnimatedPosition3D
defaultAnimatedPosition3D = AnimatedPosition3D
  { x: mkAnimatableValue "Position X" 0.0
  , y: mkAnimatableValue "Position Y" 0.0
  , z: mkAnimatableValue "Position Z" 0.0
  , separated: false
  , motionPathMode: MotionPathBezier
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animated // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 2D scale with X and Y as separate properties.
-- |
-- | Values are percentages (100.0 = 100% = no change).
newtype AnimatedScale2D = AnimatedScale2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , linked :: Boolean  -- Are X/Y linked (uniform scale)?
  }

derive instance eqAnimatedScale2D :: Eq AnimatedScale2D

instance showAnimatedScale2D :: Show AnimatedScale2D where
  show (AnimatedScale2D s) = 
    "Scale2D(" <> show s.x <> ", " <> show s.y <> 
    (if s.linked then " [linked]" else "") <> ")"

-- | Default animated scale at 100%.
defaultAnimatedScale2D :: AnimatedScale2D
defaultAnimatedScale2D = AnimatedScale2D
  { x: mkAnimatableValue "Scale X" 100.0
  , y: mkAnimatableValue "Scale Y" 100.0
  , linked: true
  }

-- | Link scale dimensions (uniform scaling).
linkScaleDimensions :: AnimatedScale2D -> AnimatedScale2D
linkScaleDimensions (AnimatedScale2D s) = AnimatedScale2D s { linked = true }

-- | Unlink scale dimensions (independent X/Y).
unlinkScaleDimensions :: AnimatedScale2D -> AnimatedScale2D
unlinkScaleDimensions (AnimatedScale2D s) = AnimatedScale2D s { linked = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animated // scale 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D scale.
newtype AnimatedScale3D = AnimatedScale3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  , linked :: Boolean
  }

derive instance eqAnimatedScale3D :: Eq AnimatedScale3D

instance showAnimatedScale3D :: Show AnimatedScale3D where
  show (AnimatedScale3D s) = 
    "Scale3D(" <> show s.x <> ", " <> show s.y <> ", " <> show s.z <> ")"

-- | Default animated 3D scale at 100%.
defaultAnimatedScale3D :: AnimatedScale3D
defaultAnimatedScale3D = AnimatedScale3D
  { x: mkAnimatableValue "Scale X" 100.0
  , y: mkAnimatableValue "Scale Y" 100.0
  , z: mkAnimatableValue "Scale Z" 100.0
  , linked: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animated // rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated single-axis rotation (2D or Z-axis for 3D).
-- |
-- | Value is in degrees. Can exceed 360 for multiple rotations.
newtype AnimatedRotation = AnimatedRotation
  { rotation :: AnimatableValue
  , revolutions :: Int  -- Additional full revolutions (for UI)
  }

derive instance eqAnimatedRotation :: Eq AnimatedRotation

instance showAnimatedRotation :: Show AnimatedRotation where
  show (AnimatedRotation r) = "Rotation(" <> show r.rotation <> ")"

-- | Default animated rotation at 0 degrees.
defaultAnimatedRotation :: AnimatedRotation
defaultAnimatedRotation = AnimatedRotation
  { rotation: mkAnimatableValue "Rotation" 0.0
  , revolutions: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // animated // rotation 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D rotation with separate X, Y, Z axes.
-- |
-- | Also includes Orientation for cameras/3D layers.
newtype AnimatedRotation3D = AnimatedRotation3D
  { x :: AnimatableValue           -- Rotation X (pitch)
  , y :: AnimatableValue           -- Rotation Y (yaw)
  , z :: AnimatableValue           -- Rotation Z (roll)
  , orientationX :: AnimatableValue  -- Orientation X
  , orientationY :: AnimatableValue  -- Orientation Y
  , orientationZ :: AnimatableValue  -- Orientation Z
  }

derive instance eqAnimatedRotation3D :: Eq AnimatedRotation3D

instance showAnimatedRotation3D :: Show AnimatedRotation3D where
  show (AnimatedRotation3D r) = 
    "Rotation3D(X:" <> show r.x <> ", Y:" <> show r.y <> ", Z:" <> show r.z <> ")"

-- | Default animated 3D rotation at 0 degrees.
defaultAnimatedRotation3D :: AnimatedRotation3D
defaultAnimatedRotation3D = AnimatedRotation3D
  { x: mkAnimatableValue "X Rotation" 0.0
  , y: mkAnimatableValue "Y Rotation" 0.0
  , z: mkAnimatableValue "Z Rotation" 0.0
  , orientationX: mkAnimatableValue "Orientation X" 0.0
  , orientationY: mkAnimatableValue "Orientation Y" 0.0
  , orientationZ: mkAnimatableValue "Orientation Z" 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animated // anchor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 2D anchor point.
-- |
-- | Position within the layer where transforms are applied.
newtype AnimatedAnchor2D = AnimatedAnchor2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  }

derive instance eqAnimatedAnchor2D :: Eq AnimatedAnchor2D

instance showAnimatedAnchor2D :: Show AnimatedAnchor2D where
  show (AnimatedAnchor2D a) = "Anchor2D(" <> show a.x <> ", " <> show a.y <> ")"

-- | Default animated anchor at origin.
defaultAnimatedAnchor2D :: AnimatedAnchor2D
defaultAnimatedAnchor2D = AnimatedAnchor2D
  { x: mkAnimatableValue "Anchor Point X" 0.0
  , y: mkAnimatableValue "Anchor Point Y" 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animated // anchor 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D anchor point.
newtype AnimatedAnchor3D = AnimatedAnchor3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  }

derive instance eqAnimatedAnchor3D :: Eq AnimatedAnchor3D

instance showAnimatedAnchor3D :: Show AnimatedAnchor3D where
  show (AnimatedAnchor3D a) = 
    "Anchor3D(" <> show a.x <> ", " <> show a.y <> ", " <> show a.z <> ")"

-- | Default animated 3D anchor at origin.
defaultAnimatedAnchor3D :: AnimatedAnchor3D
defaultAnimatedAnchor3D = AnimatedAnchor3D
  { x: mkAnimatableValue "Anchor Point X" 0.0
  , y: mkAnimatableValue "Anchor Point Y" 0.0
  , z: mkAnimatableValue "Anchor Point Z" 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animated // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated opacity.
-- |
-- | Value is 0-100 (percentage).
newtype AnimatedOpacity = AnimatedOpacity
  { opacity :: AnimatableValue
  }

derive instance eqAnimatedOpacity :: Eq AnimatedOpacity

instance showAnimatedOpacity :: Show AnimatedOpacity where
  show (AnimatedOpacity o) = "Opacity(" <> show o.opacity <> ")"

-- | Default animated opacity at 100%.
defaultAnimatedOpacity :: AnimatedOpacity
defaultAnimatedOpacity = AnimatedOpacity
  { opacity: mkAnimatableValue "Opacity" 100.0
  }
