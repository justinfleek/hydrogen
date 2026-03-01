-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // kernel // text // vector
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Vector Types and Operations
-- |
-- | Provides vector types (Vec2, Vec3, Vec4, IVec2, IVec3) and tensor shapes
-- | used throughout GPU compute operations for text rendering.

module Hydrogen.GPU.Kernel.Text.Vector
  ( -- * Vector Types
    Vec2
  , Vec3
  , Vec4
  , IVec2
  , IVec3
  
  -- * Tensor Types
  , TensorShape
  
  -- * Vector Constructors
  , vec2
  , vec3
  , vec4
  , ivec2
  , ivec3
  
  -- * Vec2 Operations
  , addVec2
  , subVec2
  , scaleVec2
  , mulVec2
  , dotVec2
  , swapVec2
  , zeroVec2
  , oneVec2
  
  -- * Vec3 Operations
  , addVec3
  , subVec3
  , scaleVec3
  , dotVec3
  , zeroVec3
  , oneVec3
  
  -- * Vec4 Operations
  , vec4FromRGBA
  , vec4ToTuple
  , tupleToVec4
  , zeroVec4
  , oneVec4
  
  -- * Tensor Operations
  , textureShape
  , tensorElements
  , tensorByteSize
  , isTensorShapeValid
  , tensorShapeEq
  
  -- * Algebraic Utilities
  , addVecSemiring
  , negateVecRing
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Semiring
  , class Ring
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (==)
  , (&&)
  , negate
  , zero
  , one
  )

import Data.Int as Int
import Data.Tuple (Tuple(Tuple), fst, snd)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // vector types
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D vector type for GPU coordinates
type Vec2 = { x :: Number, y :: Number }

-- | 3D vector type for colors/positions
type Vec3 = { x :: Number, y :: Number, z :: Number }

-- | 4D vector type for RGBA colors
type Vec4 = { x :: Number, y :: Number, z :: Number, w :: Number }

-- | Integer 2D vector for pixel coordinates
type IVec2 = { x :: Int, y :: Int }

-- | Integer 3D vector for voxels/workgroups
type IVec3 = { x :: Int, y :: Int, z :: Int }

-- | Tensor shape for GPU buffers
type TensorShape = 
  { width :: Int
  , height :: Int
  , channels :: Int
  , batch :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // vector constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a vec2
vec2 :: Number -> Number -> Vec2
vec2 x y = { x, y }

-- | Create a vec3
vec3 :: Number -> Number -> Number -> Vec3
vec3 x y z = { x, y, z }

-- | Create a vec4
vec4 :: Number -> Number -> Number -> Number -> Vec4
vec4 x y z w = { x, y, z, w }

-- | Create an ivec2
ivec2 :: Int -> Int -> IVec2
ivec2 x y = { x, y }

-- | Create an ivec3
ivec3 :: Int -> Int -> Int -> IVec3
ivec3 x y z = { x, y, z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vec2 operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vec2 addition
addVec2 :: Vec2 -> Vec2 -> Vec2
addVec2 a b = { x: a.x + b.x, y: a.y + b.y }

-- | Vec2 subtraction
subVec2 :: Vec2 -> Vec2 -> Vec2
subVec2 a b = { x: a.x - b.x, y: a.y - b.y }

-- | Vec2 scalar multiply
scaleVec2 :: Number -> Vec2 -> Vec2
scaleVec2 s v = { x: v.x * s, y: v.y * s }

-- | Vec2 component-wise multiply
mulVec2 :: Vec2 -> Vec2 -> Vec2
mulVec2 a b = { x: a.x * b.x, y: a.y * b.y }

-- | Vec2 dot product
dotVec2 :: Vec2 -> Vec2 -> Number
dotVec2 a b = a.x * b.x + a.y * b.y

-- | Swap vec2 components
swapVec2 :: Vec2 -> Vec2
swapVec2 v = { x: v.y, y: v.x }

-- | Zero vector constants
zeroVec2 :: Vec2
zeroVec2 = { x: zero, y: zero }

-- | One vector constants
oneVec2 :: Vec2
oneVec2 = { x: one, y: one }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vec3 operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vec3 addition
addVec3 :: Vec3 -> Vec3 -> Vec3
addVec3 a b = { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

-- | Vec3 subtraction
subVec3 :: Vec3 -> Vec3 -> Vec3
subVec3 a b = { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }

-- | Vec3 scalar multiply
scaleVec3 :: Number -> Vec3 -> Vec3
scaleVec3 s v = { x: v.x * s, y: v.y * s, z: v.z * s }

-- | Vec3 dot product
dotVec3 :: Vec3 -> Vec3 -> Number
dotVec3 a b = a.x * b.x + a.y * b.y + a.z * b.z

zeroVec3 :: Vec3
zeroVec3 = { x: zero, y: zero, z: zero }

oneVec3 :: Vec3
oneVec3 = { x: one, y: one, z: one }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vec4 operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vec4 from RGBA (0-255 to 0-1)
vec4FromRGBA :: Int -> Int -> Int -> Int -> Vec4
vec4FromRGBA r g b a =
  { x: Int.toNumber r / 255.0
  , y: Int.toNumber g / 255.0
  , z: Int.toNumber b / 255.0
  , w: Int.toNumber a / 255.0
  }

-- | Convert Vec4 to tuple for interop
vec4ToTuple :: Vec4 -> Tuple (Tuple Number Number) (Tuple Number Number)
vec4ToTuple v = Tuple (Tuple v.x v.y) (Tuple v.z v.w)

-- | Convert tuple to Vec4
tupleToVec4 :: Tuple (Tuple Number Number) (Tuple Number Number) -> Vec4
tupleToVec4 t = 
  let xy = fst t
      zw = snd t
  in { x: fst xy, y: snd xy, z: fst zw, w: snd zw }

zeroVec4 :: Vec4
zeroVec4 = { x: zero, y: zero, z: zero, w: zero }

oneVec4 :: Vec4
oneVec4 = { x: one, y: one, z: one, w: one }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // tensor operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tensor shape for a 2D texture
textureShape :: Int -> Int -> Int -> TensorShape
textureShape w h channels = { width: w, height: h, channels, batch: 1 }

-- | Total elements in tensor
tensorElements :: TensorShape -> Int
tensorElements s = s.width * s.height * s.channels * s.batch

-- | Tensor byte size (assuming float32)
tensorByteSize :: TensorShape -> Int
tensorByteSize s = tensorElements s * 4

-- | Check if tensor shape is valid
isTensorShapeValid :: TensorShape -> Boolean
isTensorShapeValid s =
  s.width > 0 && s.height > 0 && s.channels > 0 && s.batch > 0

-- | Compare tensor shapes
tensorShapeEq :: TensorShape -> TensorShape -> Boolean
tensorShapeEq a b =
  a.width == b.width && a.height == b.height && 
  a.channels == b.channels && a.batch == b.batch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // algebraic utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add vectors using Semiring
addVecSemiring :: forall a. Semiring a => { x :: a, y :: a } -> { x :: a, y :: a } -> { x :: a, y :: a }
addVecSemiring v1 v2 = { x: v1.x + v2.x, y: v1.y + v2.y }

-- | Negate vector using Ring
negateVecRing :: forall a. Ring a => { x :: a, y :: a } -> { x :: a, y :: a }
negateVecRing v = { x: negate v.x, y: negate v.y }
