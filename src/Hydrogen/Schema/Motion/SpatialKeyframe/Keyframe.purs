-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // spatial-keyframe // keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spatial Keyframes — Complete 2D/3D keyframes with spatial and temporal handles.
-- |
-- | ## Industry Standard
-- |
-- | Each spatial keyframe contains:
-- |
-- | - **Position**: The point in 2D/3D space
-- | - **Spatial In/Out**: Handles controlling motion path SHAPE
-- | - **Temporal In/Out**: Handles controlling motion SPEED
-- | - **Interpolation Types**: How to interpolate spatially and temporally
-- | - **Flags**: Roving, locked, continuous bezier, auto bezier

module Hydrogen.Schema.Motion.SpatialKeyframe.Keyframe
  ( -- * Spatial Keyframe 2D
    SpatialKeyframe2D
  , spatialKeyframe2D
  , spatialKeyframe2DLinear
  , spatialKeyframe2DWithHandles
  
  -- * Spatial Keyframe 3D
  , SpatialKeyframe3D
  , spatialKeyframe3D
  , spatialKeyframe3DLinear
  , spatialKeyframe3DWithHandles
  
  -- * Accessors
  , keyframePosition2D
  , keyframePosition3D
  , keyframeFrame
  , keyframeSpatialIn2D
  , keyframeSpatialOut2D
  , keyframeSpatialIn3D
  , keyframeSpatialOut3D
  , keyframeTemporalIn
  , keyframeTemporalOut
  , keyframeFlags
  
  -- * Operations
  , setPosition2D
  , setPosition3D
  , setSpatialHandles2D
  , setSpatialHandles3D
  , setTemporalHandles
  , convertToRoving
  , convertToLinear
  , convertToBezier
  , convertToHold
  , convertToAuto
  ) where

import Hydrogen.Schema.Dimension.Temporal (Frames)
import Hydrogen.Schema.Motion.SpatialKeyframe.Handle
  ( SpatialHandle2D
  , SpatialHandle3D
  , TemporalHandle
  , spatialHandle2DZero
  , spatialHandle3DZero
  , temporalHandleLinear
  )
import Hydrogen.Schema.Motion.SpatialKeyframe.Types
  ( KeyframeFlags
  , SpatialInterpolation(SIAuto, SILinear, SIBezier)
  , TemporalInterpolation(TIAuto, TILinear, TIBezier, TIHold)
  , defaultKeyframeFlags
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // spatial // keyframe 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 2D spatial keyframe with all handles.
type SpatialKeyframe2D =
  { frame :: Frames                         -- ^ Time position
  , position :: { x :: Number, y :: Number } -- ^ Spatial position
  , spatialIn :: SpatialHandle2D            -- ^ Incoming spatial tangent
  , spatialOut :: SpatialHandle2D           -- ^ Outgoing spatial tangent
  , temporalIn :: TemporalHandle            -- ^ Incoming temporal tangent
  , temporalOut :: TemporalHandle           -- ^ Outgoing temporal tangent
  , spatialInterp :: SpatialInterpolation   -- ^ Spatial interpolation type
  , temporalInterp :: TemporalInterpolation -- ^ Temporal interpolation type
  , flags :: KeyframeFlags                  -- ^ Behavior flags
  }

-- | Create a basic 2D spatial keyframe.
spatialKeyframe2D :: Frames -> Number -> Number -> SpatialKeyframe2D
spatialKeyframe2D frameTime x y =
  { frame: frameTime
  , position: { x, y }
  , spatialIn: spatialHandle2DZero
  , spatialOut: spatialHandle2DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SIAuto
  , temporalInterp: TIAuto
  , flags: defaultKeyframeFlags
  }

-- | Create a linear 2D keyframe (no curves).
spatialKeyframe2DLinear :: Frames -> Number -> Number -> SpatialKeyframe2D
spatialKeyframe2DLinear frameTime x y =
  { frame: frameTime
  , position: { x, y }
  , spatialIn: spatialHandle2DZero
  , spatialOut: spatialHandle2DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SILinear
  , temporalInterp: TILinear
  , flags: defaultKeyframeFlags
  }

-- | Create a 2D keyframe with explicit handles.
spatialKeyframe2DWithHandles 
  :: Frames 
  -> Number -> Number 
  -> SpatialHandle2D -> SpatialHandle2D
  -> TemporalHandle -> TemporalHandle
  -> SpatialKeyframe2D
spatialKeyframe2DWithHandles frameTime x y spatialIn spatialOut temporalIn temporalOut =
  { frame: frameTime
  , position: { x, y }
  , spatialIn: spatialIn
  , spatialOut: spatialOut
  , temporalIn: temporalIn
  , temporalOut: temporalOut
  , spatialInterp: SIBezier
  , temporalInterp: TIBezier
  , flags: defaultKeyframeFlags
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // spatial // keyframe 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D spatial keyframe with all handles.
type SpatialKeyframe3D =
  { frame :: Frames
  , position :: { x :: Number, y :: Number, z :: Number }
  , spatialIn :: SpatialHandle3D
  , spatialOut :: SpatialHandle3D
  , temporalIn :: TemporalHandle
  , temporalOut :: TemporalHandle
  , spatialInterp :: SpatialInterpolation
  , temporalInterp :: TemporalInterpolation
  , flags :: KeyframeFlags
  }

-- | Create a basic 3D spatial keyframe.
spatialKeyframe3D :: Frames -> Number -> Number -> Number -> SpatialKeyframe3D
spatialKeyframe3D frameTime x y z =
  { frame: frameTime
  , position: { x, y, z }
  , spatialIn: spatialHandle3DZero
  , spatialOut: spatialHandle3DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SIAuto
  , temporalInterp: TIAuto
  , flags: defaultKeyframeFlags
  }

-- | Create a linear 3D keyframe (no curves).
spatialKeyframe3DLinear :: Frames -> Number -> Number -> Number -> SpatialKeyframe3D
spatialKeyframe3DLinear frameTime x y z =
  { frame: frameTime
  , position: { x, y, z }
  , spatialIn: spatialHandle3DZero
  , spatialOut: spatialHandle3DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SILinear
  , temporalInterp: TILinear
  , flags: defaultKeyframeFlags
  }

-- | Create a 3D keyframe with explicit handles.
spatialKeyframe3DWithHandles 
  :: Frames 
  -> Number -> Number -> Number
  -> SpatialHandle3D -> SpatialHandle3D
  -> TemporalHandle -> TemporalHandle
  -> SpatialKeyframe3D
spatialKeyframe3DWithHandles frameTime x y z spatialIn spatialOut temporalIn temporalOut =
  { frame: frameTime
  , position: { x, y, z }
  , spatialIn: spatialIn
  , spatialOut: spatialOut
  , temporalIn: temporalIn
  , temporalOut: temporalOut
  , spatialInterp: SIBezier
  , temporalInterp: TIBezier
  , flags: defaultKeyframeFlags
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get position from 2D keyframe.
keyframePosition2D :: SpatialKeyframe2D -> { x :: Number, y :: Number }
keyframePosition2D kf = kf.position

-- | Get position from 3D keyframe.
keyframePosition3D :: SpatialKeyframe3D -> { x :: Number, y :: Number, z :: Number }
keyframePosition3D kf = kf.position

-- | Get frame from 2D keyframe.
keyframeFrame :: forall r. { frame :: Frames | r } -> Frames
keyframeFrame kf = kf.frame

-- | Get incoming spatial handle from 2D keyframe.
keyframeSpatialIn2D :: SpatialKeyframe2D -> SpatialHandle2D
keyframeSpatialIn2D kf = kf.spatialIn

-- | Get outgoing spatial handle from 2D keyframe.
keyframeSpatialOut2D :: SpatialKeyframe2D -> SpatialHandle2D
keyframeSpatialOut2D kf = kf.spatialOut

-- | Get incoming spatial handle from 3D keyframe.
keyframeSpatialIn3D :: SpatialKeyframe3D -> SpatialHandle3D
keyframeSpatialIn3D kf = kf.spatialIn

-- | Get outgoing spatial handle from 3D keyframe.
keyframeSpatialOut3D :: SpatialKeyframe3D -> SpatialHandle3D
keyframeSpatialOut3D kf = kf.spatialOut

-- | Get incoming temporal handle.
keyframeTemporalIn :: forall r. { temporalIn :: TemporalHandle | r } -> TemporalHandle
keyframeTemporalIn kf = kf.temporalIn

-- | Get outgoing temporal handle.
keyframeTemporalOut :: forall r. { temporalOut :: TemporalHandle | r } -> TemporalHandle
keyframeTemporalOut kf = kf.temporalOut

-- | Get keyframe flags.
keyframeFlags :: forall r. { flags :: KeyframeFlags | r } -> KeyframeFlags
keyframeFlags kf = kf.flags

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set position on 2D keyframe.
setPosition2D :: Number -> Number -> SpatialKeyframe2D -> SpatialKeyframe2D
setPosition2D x y kf = kf { position = { x, y } }

-- | Set position on 3D keyframe.
setPosition3D :: Number -> Number -> Number -> SpatialKeyframe3D -> SpatialKeyframe3D
setPosition3D x y z kf = kf { position = { x, y, z } }

-- | Set spatial handles on 2D keyframe.
setSpatialHandles2D :: SpatialHandle2D -> SpatialHandle2D -> SpatialKeyframe2D -> SpatialKeyframe2D
setSpatialHandles2D spIn spOut kf = kf { spatialIn = spIn, spatialOut = spOut }

-- | Set spatial handles on 3D keyframe.
setSpatialHandles3D :: SpatialHandle3D -> SpatialHandle3D -> SpatialKeyframe3D -> SpatialKeyframe3D
setSpatialHandles3D spIn spOut kf = kf { spatialIn = spIn, spatialOut = spOut }

-- | Set temporal handles.
setTemporalHandles 
  :: forall r
   . TemporalHandle 
  -> TemporalHandle 
  -> { temporalIn :: TemporalHandle, temporalOut :: TemporalHandle | r } 
  -> { temporalIn :: TemporalHandle, temporalOut :: TemporalHandle | r }
setTemporalHandles tmpIn tmpOut kf = kf { temporalIn = tmpIn, temporalOut = tmpOut }

-- | Convert keyframe to roving (auto-time adjustment).
convertToRoving :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToRoving kf = kf { flags = kf.flags { roving = true } }

-- | Convert keyframe to linear interpolation.
convertToLinear :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToLinear kf = kf 
  { spatialInterp = SILinear
  , temporalInterp = TILinear
  , spatialIn = spatialHandle2DZero
  , spatialOut = spatialHandle2DZero
  }

-- | Convert keyframe to bezier interpolation.
convertToBezier :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToBezier kf = kf 
  { spatialInterp = SIBezier
  , temporalInterp = TIBezier
  }

-- | Convert keyframe to hold (no interpolation).
convertToHold :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToHold kf = kf { temporalInterp = TIHold }

-- | Convert keyframe to auto (system-calculated tangents).
convertToAuto :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToAuto kf = kf 
  { spatialInterp = SIAuto
  , temporalInterp = TIAuto
  , flags = kf.flags { autoBezier = true }
  }
