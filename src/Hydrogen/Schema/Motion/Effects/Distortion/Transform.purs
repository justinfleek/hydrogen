-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--         // hydrogen // schema // motion // effects // distortion // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform Effects — Spatial transformation distortion effects.
-- |
-- | ## Effects Included
-- |
-- | - **Corner Pin**: 4-corner perspective distortion
-- | - **Mirror**: Reflection/mirror effects
-- | - **Offset**: Tile/offset image
-- | - **Optics Compensation**: Lens distortion correction
-- | - **Polar Coordinates**: Rectangular to polar conversion
-- | - **Transform**: Basic spatial transform

module Hydrogen.Schema.Motion.Effects.Distortion.Transform
  ( -- * Corner Pin Effect
    CornerPinEffect
  , defaultCornerPin
  
  -- * Mirror Effect
  , MirrorEffect
  , defaultMirror
  , mirrorWithAngle
  
  -- * Offset Effect
  , OffsetEffect
  , defaultOffset
  , offsetWithShift
  
  -- * Optics Compensation Effect
  , OpticsCompensationEffect
  , defaultOpticsCompensation
  
  -- * Polar Coordinates Effect
  , PolarCoordinatesEffect
  , PolarType(PTRectToPolar, PTPolarToRect)
  , defaultPolarCoordinates
  
  -- * Transform Effect
  , TransformEffect
  , defaultTransform
  , transformWithPosition
  
  -- * Serialization
  , polarTypeToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // corner // pin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corner Pin Effect — 4-corner perspective distortion.
-- |
-- | ## AE Properties
-- |
-- | Move each corner independently for perspective transform.
type CornerPinEffect =
  { upperLeft :: Point2D                 -- ^ Upper-left corner
  , upperRight :: Point2D                -- ^ Upper-right corner
  , lowerLeft :: Point2D                 -- ^ Lower-left corner
  , lowerRight :: Point2D                -- ^ Lower-right corner
  }

-- | Default corner pin (no distortion).
defaultCornerPin :: CornerPinEffect
defaultCornerPin =
  { upperLeft: point2D 0.0 0.0
  , upperRight: point2D 100.0 0.0
  , lowerLeft: point2D 0.0 100.0
  , lowerRight: point2D 100.0 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // mirror // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mirror Effect — Reflection/mirror effects.
-- |
-- | ## AE Properties
-- |
-- | - Reflection Center: Center of reflection axis
-- | - Reflection Angle: Angle of reflection axis (0-360)
type MirrorEffect =
  { reflectionCenter :: Point2D          -- ^ Center point
  , reflectionAngle :: Number            -- ^ Axis angle (0-360)
  }

-- | Default mirror (vertical reflection at center).
defaultMirror :: MirrorEffect
defaultMirror =
  { reflectionCenter: point2D 50.0 50.0
  , reflectionAngle: 0.0
  }

-- | Create mirror with specific angle.
mirrorWithAngle :: Number -> MirrorEffect
mirrorWithAngle angle =
  { reflectionCenter: point2D 50.0 50.0
  , reflectionAngle: clampNumber 0.0 360.0 angle
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // offset // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Offset Effect — Tile/offset image.
-- |
-- | ## AE Properties
-- |
-- | - Shift Center To: New center point
-- | - Blend With Original: Original blend (0-100%)
type OffsetEffect =
  { shiftCenterTo :: Point2D             -- ^ Offset position
  , blendWithOriginal :: Number          -- ^ Original blend (0-100)
  }

-- | Default offset (no shift).
defaultOffset :: OffsetEffect
defaultOffset =
  { shiftCenterTo: point2D 0.0 0.0
  , blendWithOriginal: 0.0
  }

-- | Create offset with specific shift.
offsetWithShift :: Number -> Number -> OffsetEffect
offsetWithShift x y =
  { shiftCenterTo: point2D x y
  , blendWithOriginal: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // optics // compensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Optics Compensation Effect — Lens distortion correction.
-- |
-- | ## AE Properties
-- |
-- | - Field of View: FOV angle (0-180)
-- | - Reverse Lens Distortion: Invert correction
-- | - FOV Orientation: Horizontal or vertical FOV
-- | - View Center: Center of distortion
type OpticsCompensationEffect =
  { fieldOfView :: Number                -- ^ FOV angle (0-180)
  , reverseLensDistortion :: Boolean     -- ^ Invert correction
  , fovOrientationHorizontal :: Boolean  -- ^ true = horizontal FOV
  , viewCenter :: Point2D                -- ^ Center point
  , optimizePixels :: Boolean            -- ^ Pixel optimization
  }

-- | Default optics compensation.
defaultOpticsCompensation :: OpticsCompensationEffect
defaultOpticsCompensation =
  { fieldOfView: 45.0
  , reverseLensDistortion: false
  , fovOrientationHorizontal: true
  , viewCenter: point2D 50.0 50.0
  , optimizePixels: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // polar // coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Polar conversion type.
data PolarType
  = PTRectToPolar      -- ^ Rectangular to polar
  | PTPolarToRect      -- ^ Polar to rectangular

derive instance eqPolarType :: Eq PolarType
derive instance ordPolarType :: Ord PolarType

instance showPolarType :: Show PolarType where
  show PTRectToPolar = "rect-to-polar"
  show PTPolarToRect = "polar-to-rect"

-- | Polar Coordinates Effect — Rectangular to polar conversion.
-- |
-- | ## AE Properties
-- |
-- | - Type of Conversion: Rect to polar or polar to rect
-- | - Interpolation: Quality setting (0-100%)
type PolarCoordinatesEffect =
  { typeOfConversion :: PolarType        -- ^ Conversion direction
  , interpolation :: Number              -- ^ Quality (0-100)
  }

-- | Default polar coordinates.
defaultPolarCoordinates :: PolarCoordinatesEffect
defaultPolarCoordinates =
  { typeOfConversion: PTRectToPolar
  , interpolation: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // transform // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform Effect — Basic spatial transform.
-- |
-- | ## AE Properties
-- |
-- | Independent transform that doesn't affect layer transform.
type TransformEffect =
  { anchorPoint :: Point2D               -- ^ Transform anchor
  , position :: Point2D                  -- ^ Position
  , uniformScale :: Boolean              -- ^ Lock aspect ratio
  , scaleHeight :: Number                -- ^ Height scale (0-1000%)
  , scaleWidth :: Number                 -- ^ Width scale (0-1000%)
  , skew :: Number                       -- ^ Skew amount (-90 to 90)
  , skewAxis :: Number                   -- ^ Skew axis angle (0-360)
  , rotation :: Number                   -- ^ Rotation (degrees)
  , opacity :: Number                    -- ^ Opacity (0-100)
  , shuttleAngle :: Number               -- ^ Motion blur shutter (0-720)
  , useCompositionShutter :: Boolean     -- ^ Use comp shutter angle
  }

-- | Default transform (no change).
defaultTransform :: TransformEffect
defaultTransform =
  { anchorPoint: point2D 50.0 50.0
  , position: point2D 50.0 50.0
  , uniformScale: true
  , scaleHeight: 100.0
  , scaleWidth: 100.0
  , skew: 0.0
  , skewAxis: 0.0
  , rotation: 0.0
  , opacity: 100.0
  , shuttleAngle: 0.0
  , useCompositionShutter: true
  }

-- | Create transform with specific position.
transformWithPosition :: Number -> Number -> TransformEffect
transformWithPosition x y =
  { anchorPoint: point2D 50.0 50.0
  , position: point2D x y
  , uniformScale: true
  , scaleHeight: 100.0
  , scaleWidth: 100.0
  , skew: 0.0
  , skewAxis: 0.0
  , rotation: 0.0
  , opacity: 100.0
  , shuttleAngle: 0.0
  , useCompositionShutter: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // serialization
-- ═════════════════════════════════════════════════════════════════════════════

polarTypeToString :: PolarType -> String
polarTypeToString = show
