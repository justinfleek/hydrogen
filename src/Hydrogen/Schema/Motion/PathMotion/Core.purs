-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // pathmotion // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMotion Core — Construction, configuration, and accessors.
-- |
-- | ## Exports
-- |
-- | - Construction: `motionPath`, `motionPathSimple`, `motionPathWithBank`
-- | - Configuration: setters for duration, easing, orient mode, etc.
-- | - Accessors: getters for path properties
-- | - Presets: `defaultEasing`
-- | - Frame conversion: `framesToDuration`, `durationToFrames`
-- |
-- | ## Dependencies
-- |
-- | - PathMotion.Types (MotionPath, PathSource, OrientMode)
-- | - Schema.Geometry.Angle (Degrees)
-- | - Schema.Motion.Easing (Easing)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.PathMotion.Core
  ( -- * Construction
    motionPath
  , motionPathSimple
  , motionPathWithBank
  
  -- * Configuration
  , setDuration
  , setEasing
  , setOrientMode
  , setAutoOrient
  , setBankAngle
  , setLoop
  , setPingPong
  , setOffset
  
  -- * Accessors
  , pathSource
  , duration
  , easing
  , orientMode
  , isLooping
  , isPingPong
  
  -- * Presets
  , defaultEasing
  
  -- * Frame Conversion
  , framesToDuration
  , durationToFrames
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<)
  , (>)
  , otherwise
  )

import Hydrogen.Schema.Geometry.Angle (Degrees(Degrees))
import Hydrogen.Schema.Motion.Easing (Easing, linear, easeInOut)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames), unwrapFrames)
import Hydrogen.Schema.Motion.PathMotion.Types 
  ( MotionPath(MotionPath)
  , PathSource
  , OrientMode(NoOrient, OrientToPath)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a motion path with full configuration.
motionPath :: PathSource -> Number -> Easing -> MotionPath
motionPath source dur eas = MotionPath
  { source: source
  , durationFrames: dur
  , easing: eas
  , orientMode: NoOrient
  , bankAngle: Degrees 0.0
  , bankSmoothing: 0.5
  , loop: false
  , pingPong: false
  , startOffset: 0.0
  , endOffset: 1.0
  , startFrame: 0.0
  }

-- | Create a simple motion path with linear easing.
motionPathSimple :: PathSource -> Number -> MotionPath
motionPathSimple source dur = motionPath source dur linear

-- | Create a motion path with auto-orient and banking.
motionPathWithBank :: PathSource -> Number -> Easing -> Degrees -> MotionPath
motionPathWithBank source dur eas bankMax =
  let base = motionPath source dur eas
      (MotionPath mp) = base
  in MotionPath (mp { orientMode = OrientToPath, bankAngle = bankMax })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set duration in frames.
setDuration :: Number -> MotionPath -> MotionPath
setDuration dur (MotionPath mp) = MotionPath (mp { durationFrames = dur })

-- | Set easing curve.
setEasing :: Easing -> MotionPath -> MotionPath
setEasing eas (MotionPath mp) = MotionPath (mp { easing = eas })

-- | Set orientation mode.
setOrientMode :: OrientMode -> MotionPath -> MotionPath
setOrientMode mode (MotionPath mp) = MotionPath (mp { orientMode = mode })

-- | Enable auto-orient to path.
setAutoOrient :: MotionPath -> MotionPath
setAutoOrient = setOrientMode OrientToPath

-- | Set maximum banking angle.
setBankAngle :: Degrees -> MotionPath -> MotionPath
setBankAngle angle (MotionPath mp) = MotionPath (mp { bankAngle = angle })

-- | Enable looping.
setLoop :: Boolean -> MotionPath -> MotionPath
setLoop loop (MotionPath mp) = MotionPath (mp { loop = loop })

-- | Enable ping-pong (reverse at end).
setPingPong :: Boolean -> MotionPath -> MotionPath
setPingPong pp (MotionPath mp) = MotionPath (mp { pingPong = pp })

-- | Set path offset (start and end points on path).
setOffset :: Number -> Number -> MotionPath -> MotionPath
setOffset start end (MotionPath mp) = 
  MotionPath (mp { startOffset = clamp01 start, endOffset = clamp01 end })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get path source.
pathSource :: MotionPath -> PathSource
pathSource (MotionPath mp) = mp.source

-- | Get duration in frames.
duration :: MotionPath -> Number
duration (MotionPath mp) = mp.durationFrames

-- | Get easing curve.
easing :: MotionPath -> Easing
easing (MotionPath mp) = mp.easing

-- | Get orientation mode.
orientMode :: MotionPath -> OrientMode
orientMode (MotionPath mp) = mp.orientMode

-- | Check if looping.
isLooping :: MotionPath -> Boolean
isLooping (MotionPath mp) = mp.loop

-- | Check if ping-pong enabled.
isPingPong :: MotionPath -> Boolean
isPingPong (MotionPath mp) = mp.pingPong

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default easing (ease in-out).
defaultEasing :: Easing
defaultEasing = easeInOut

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // frame conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Frames to duration number.
framesToDuration :: Frames -> Number
framesToDuration f = unwrapFrames f

-- | Convert duration to Frames.
durationToFrames :: Number -> Frames
durationToFrames n = Frames n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n
