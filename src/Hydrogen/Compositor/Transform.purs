-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // compositor // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform — Scale, Rotation, Translation with Layer Behavior
-- |
-- | ## Design Philosophy
-- |
-- | Transforms behave differently per layer type:
-- | - **MaterialLayer**: Snaps to 8px grid on scale
-- | - **ShapeLayer**: Pure math, pixel-perfect at any scale

module Hydrogen.Compositor.Transform
  ( -- * Transform Type
    Transform(Transform)
  , identityTransform
  
  -- * Transform Components
  , Translation(Translation)
  , Scale(Scale)
  , Rotation(Rotation)
  
  -- * Transform Operations
  , translate
  , scale
  , rotate
  , compose
  
  -- * Component Accessors
  , getTranslation
  , getScale
  , getRotation
  , setTranslation
  , setScale
  , setRotation
  
  -- * Uniform Scale
  , uniformScale
  , scaleBy
  
  -- * Point Operations
  , applyToPoint
  , applyInverseToPoint
  
  -- * Transform Inversion
  , invert
  
  -- * Interpolation
  , lerp
  
  -- * Bounded Operations (for swarm scale safety)
  , clampScale
  , clampTranslation
  
  -- * Identity Check
  , isIdentity
  
  -- * Matrix Representation
  , Matrix3x3(Matrix3x3)
  , toMatrix
  , fromMatrix
  , multiplyMatrices
  , determinant
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude 
  ( class Eq
  , class Show
  , show
  , negate
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (&&)
  , (<)
  , (>)
  )

import Data.Number (cos, sin, sqrt, atan2)

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // transform components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translation — offset in x and y
newtype Translation = Translation { x :: Number, y :: Number }

derive instance eqTranslation :: Eq Translation

instance showTranslation :: Show Translation where
  show (Translation t) = "translate(" <> show t.x <> ", " <> show t.y <> ")"

-- | Scale — scaling factors for x and y
newtype Scale = Scale { x :: Number, y :: Number }

derive instance eqScale :: Eq Scale

instance showScale :: Show Scale where
  show (Scale s) = "scale(" <> show s.x <> ", " <> show s.y <> ")"

-- | Rotation — angle in radians
newtype Rotation = Rotation { angle :: Number }

derive instance eqRotation :: Eq Rotation

instance showRotation :: Show Rotation where
  show (Rotation r) = "rotate(" <> show r.angle <> "rad)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete 2D transform combining translation, scale, and rotation.
-- |
-- | Transforms are applied in order: scale → rotate → translate.
newtype Transform = Transform
  { translation :: Translation
  , scale :: Scale
  , rotation :: Rotation
  }

derive instance eqTransform :: Eq Transform

instance showTransform :: Show Transform where
  show (Transform t) = 
    "Transform { " <> show t.translation 
      <> " " <> show t.scale
      <> " " <> show t.rotation <> " }"

-- | Identity transform — no transformation
identityTransform :: Transform
identityTransform = Transform
  { translation: Translation { x: 0.0, y: 0.0 }
  , scale: Scale { x: 1.0, y: 1.0 }
  , rotation: Rotation { angle: 0.0 }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // transform operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a translation transform
translate :: Number -> Number -> Transform
translate x y = Transform
  { translation: Translation { x: x, y: y }
  , scale: Scale { x: 1.0, y: 1.0 }
  , rotation: Rotation { angle: 0.0 }
  }

-- | Create a scale transform
scale :: Number -> Number -> Transform
scale sx sy = Transform
  { translation: Translation { x: 0.0, y: 0.0 }
  , scale: Scale { x: sx, y: sy }
  , rotation: Rotation { angle: 0.0 }
  }

-- | Create a rotation transform (angle in radians)
rotate :: Number -> Transform
rotate angle = Transform
  { translation: Translation { x: 0.0, y: 0.0 }
  , scale: Scale { x: 1.0, y: 1.0 }
  , rotation: Rotation { angle: angle }
  }

-- | Compose two transforms (apply second after first)
compose :: Transform -> Transform -> Transform
compose (Transform a) (Transform b) =
  let
    Translation ta = a.translation
    Translation tb = b.translation
    Scale sa = a.scale
    Scale sb = b.scale
    Rotation ra = a.rotation
    Rotation rb = b.rotation
  in
    Transform
      { translation: Translation { x: ta.x + tb.x, y: ta.y + tb.y }
      , scale: Scale { x: sa.x * sb.x, y: sa.y * sb.y }
      , rotation: Rotation { angle: ra.angle + rb.angle }
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // component accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get translation component
getTranslation :: Transform -> Translation
getTranslation (Transform t) = t.translation

-- | Get scale component
getScale :: Transform -> Scale
getScale (Transform t) = t.scale

-- | Get rotation component
getRotation :: Transform -> Rotation
getRotation (Transform t) = t.rotation

-- | Set translation component
setTranslation :: Translation -> Transform -> Transform
setTranslation tr (Transform t) = Transform (t { translation = tr })

-- | Set scale component
setScale :: Scale -> Transform -> Transform
setScale s (Transform t) = Transform (t { scale = s })

-- | Set rotation component
setRotation :: Rotation -> Transform -> Transform
setRotation r (Transform t) = Transform (t { rotation = r })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // uniform scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a uniform scale transform (same factor for x and y)
uniformScale :: Number -> Transform
uniformScale s = scale s s

-- | Scale an existing transform uniformly
scaleBy :: Number -> Transform -> Transform
scaleBy factor (Transform t) =
  let
    Scale s = t.scale
  in
    Transform (t { scale = Scale { x: s.x * factor, y: s.y * factor } })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply transform to a point.
-- |
-- | Order: scale → rotate → translate
-- |
-- | This is essential for hit testing and animation path calculations.
applyToPoint :: Transform -> Point2D -> Point2D
applyToPoint (Transform t) pt =
  let
    -- Extract components
    Translation tr = t.translation
    Scale s = t.scale
    Rotation r = t.rotation
    
    -- Get point coordinates
    px = getX pt
    py = getY pt
    
    -- Step 1: Scale
    scaledX = px * s.x
    scaledY = py * s.y
    
    -- Step 2: Rotate (around origin)
    cosA = cos r.angle
    sinA = sin r.angle
    rotatedX = scaledX * cosA - scaledY * sinA
    rotatedY = scaledX * sinA + scaledY * cosA
    
    -- Step 3: Translate
    finalX = rotatedX + tr.x
    finalY = rotatedY + tr.y
  in
    point2D finalX finalY

-- | Apply inverse transform to a point.
-- |
-- | Order: inverse translate → inverse rotate → inverse scale
-- |
-- | Useful for converting screen coordinates to local coordinates.
applyInverseToPoint :: Transform -> Point2D -> Point2D
applyInverseToPoint t pt =
  let
    invT = invert t
  in
    applyToPoint invT pt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // transform inversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Invert a transform.
-- |
-- | The inverse undoes the original transform:
-- | `applyToPoint (invert t) (applyToPoint t p) == p`
-- |
-- | Scale inversion avoids division by zero by clamping near-zero values.
invert :: Transform -> Transform
invert (Transform t) =
  let
    Translation tr = t.translation
    Scale s = t.scale
    Rotation r = t.rotation
    
    -- Invert scale (avoid division by zero)
    invSx = if s.x > epsilon then 1.0 / s.x 
            else if s.x < negate epsilon then 1.0 / s.x
            else 1.0
    invSy = if s.y > epsilon then 1.0 / s.y 
            else if s.y < negate epsilon then 1.0 / s.y
            else 1.0
    
    -- Invert rotation
    invAngle = negate r.angle
    cosA = cos invAngle
    sinA = sin invAngle
    
    -- Invert translation (must account for rotation and scale)
    -- First negate, then apply inverse rotation and scale
    negTx = negate tr.x
    negTy = negate tr.y
    rotTx = negTx * cosA - negTy * sinA
    rotTy = negTx * sinA + negTy * cosA
    invTx = rotTx * invSx
    invTy = rotTy * invSy
  in
    Transform
      { translation: Translation { x: invTx, y: invTy }
      , scale: Scale { x: invSx, y: invSy }
      , rotation: Rotation { angle: invAngle }
      }

-- | Small value for floating point comparisons
epsilon :: Number
epsilon = 0.0000001

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two transforms.
-- |
-- | `t` in [0, 1]: t=0 returns `from`, t=1 returns `to`
-- |
-- | Essential for smooth animations between keyframes.
lerp :: Number -> Transform -> Transform -> Transform
lerp t (Transform from) (Transform to) =
  let
    Translation fTr = from.translation
    Translation tTr = to.translation
    Scale fS = from.scale
    Scale tS = to.scale
    Rotation fR = from.rotation
    Rotation tR = to.rotation
    
    -- Interpolate each component
    lerpVal :: Number -> Number -> Number
    lerpVal a b = a + (b - a) * t
  in
    Transform
      { translation: Translation 
          { x: lerpVal fTr.x tTr.x
          , y: lerpVal fTr.y tTr.y 
          }
      , scale: Scale 
          { x: lerpVal fS.x tS.x
          , y: lerpVal fS.y tS.y 
          }
      , rotation: Rotation 
          { angle: lerpVal fR.angle tR.angle 
          }
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // bounded operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp scale values to prevent exponential blowup at swarm scale.
-- |
-- | **Critical for billion-agent systems**: Unbounded scale multiplication
-- | can cause exponential growth. This clamps scale factors to [minScale, maxScale].
-- |
-- | Default reasonable bounds: [0.001, 1000.0]
clampScale :: Number -> Number -> Transform -> Transform
clampScale minScale maxScale (Transform t) =
  let
    Scale s = t.scale
    clamp :: Number -> Number
    clamp v = max minScale (min maxScale v)
  in
    Transform (t { scale = Scale { x: clamp s.x, y: clamp s.y } })

-- | Clamp translation to prevent infinite drift.
-- |
-- | Useful for keeping transforms within reasonable bounds.
clampTranslation :: Number -> Number -> Transform -> Transform
clampTranslation minVal maxVal (Transform t) =
  let
    Translation tr = t.translation
    clamp :: Number -> Number
    clamp v = max minVal (min maxVal v)
  in
    Transform (t { translation = Translation { x: clamp tr.x, y: clamp tr.y } })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // identity check
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a transform is the identity (no transformation).
-- |
-- | Useful for optimization — skip transform application if identity.
isIdentity :: Transform -> Boolean
isIdentity (Transform t) =
  let
    Translation tr = t.translation
    Scale s = t.scale
    Rotation r = t.rotation
  in
    tr.x == 0.0 && tr.y == 0.0 &&
    s.x == 1.0 && s.y == 1.0 &&
    r.angle == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // matrix representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3x3 affine transformation matrix.
-- |
-- | ```
-- | | m00 m01 m02 |   | a c tx |
-- | | m10 m11 m12 | = | b d ty |
-- | | m20 m21 m22 |   | 0 0 1  |
-- | ```
-- |
-- | Used for GPU/WebGL rendering where transforms must be passed as matrices.
newtype Matrix3x3 = Matrix3x3
  { m00 :: Number, m01 :: Number, m02 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number
  }

derive instance eqMatrix3x3 :: Eq Matrix3x3

instance showMatrix3x3 :: Show Matrix3x3 where
  show (Matrix3x3 m) = 
    "Matrix3x3 [" <> show m.m00 <> " " <> show m.m01 <> " " <> show m.m02 <> "; "
                  <> show m.m10 <> " " <> show m.m11 <> " " <> show m.m12 <> "; "
                  <> show m.m20 <> " " <> show m.m21 <> " " <> show m.m22 <> "]"

-- | Convert Transform to 3x3 affine matrix.
-- |
-- | Encodes: scale → rotate → translate
toMatrix :: Transform -> Matrix3x3
toMatrix (Transform t) =
  let
    Translation tr = t.translation
    Scale s = t.scale
    Rotation r = t.rotation
    
    cosA = cos r.angle
    sinA = sin r.angle
    
    -- Combined matrix: T * R * S
    -- | sx*cos  -sy*sin  tx |
    -- | sx*sin   sy*cos  ty |
    -- |   0        0      1 |
  in
    Matrix3x3
      { m00: s.x * cosA,  m01: negate (s.y * sinA), m02: tr.x
      , m10: s.x * sinA,  m11: s.y * cosA,          m12: tr.y
      , m20: 0.0,         m21: 0.0,                 m22: 1.0
      }

-- | Convert 3x3 affine matrix back to Transform.
-- |
-- | Extracts scale, rotation, and translation from the matrix.
-- | Assumes standard affine form (bottom row is [0, 0, 1]).
fromMatrix :: Matrix3x3 -> Transform
fromMatrix (Matrix3x3 m) =
  let
    -- Translation is directly in m02, m12
    tx = m.m02
    ty = m.m12
    
    -- Scale is length of column vectors
    sx = sqrt (m.m00 * m.m00 + m.m10 * m.m10)
    sy = sqrt (m.m01 * m.m01 + m.m11 * m.m11)
    
    -- Rotation from atan2 of first column (normalized)
    angle = atan2 m.m10 m.m00
  in
    Transform
      { translation: Translation { x: tx, y: ty }
      , scale: Scale { x: sx, y: sy }
      , rotation: Rotation { angle: angle }
      }

-- | Multiply two matrices.
-- |
-- | Used for composing transforms at the matrix level.
multiplyMatrices :: Matrix3x3 -> Matrix3x3 -> Matrix3x3
multiplyMatrices (Matrix3x3 a) (Matrix3x3 b) =
  Matrix3x3
    { m00: a.m00 * b.m00 + a.m01 * b.m10 + a.m02 * b.m20
    , m01: a.m00 * b.m01 + a.m01 * b.m11 + a.m02 * b.m21
    , m02: a.m00 * b.m02 + a.m01 * b.m12 + a.m02 * b.m22
    , m10: a.m10 * b.m00 + a.m11 * b.m10 + a.m12 * b.m20
    , m11: a.m10 * b.m01 + a.m11 * b.m11 + a.m12 * b.m21
    , m12: a.m10 * b.m02 + a.m11 * b.m12 + a.m12 * b.m22
    , m20: a.m20 * b.m00 + a.m21 * b.m10 + a.m22 * b.m20
    , m21: a.m20 * b.m01 + a.m21 * b.m11 + a.m22 * b.m21
    , m22: a.m20 * b.m02 + a.m21 * b.m12 + a.m22 * b.m22
    }

-- | Calculate matrix determinant.
-- |
-- | Useful for checking if a transform is invertible (det != 0).
determinant :: Matrix3x3 -> Number
determinant (Matrix3x3 m) =
  m.m00 * (m.m11 * m.m22 - m.m12 * m.m21) -
  m.m01 * (m.m10 * m.m22 - m.m12 * m.m20) +
  m.m02 * (m.m10 * m.m21 - m.m11 * m.m20)
