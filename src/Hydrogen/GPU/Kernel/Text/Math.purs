-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // kernel // text // math
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Math Utilities
-- |
-- | Mathematical functions commonly used in GPU compute shaders:
-- | interpolation, clamping, color packing, SDF evaluation, etc.

module Hydrogen.GPU.Kernel.Text.Math
  ( -- * Clamping
    saturate
  , clampInt
  , clampNumber
  
  -- * Interpolation
  , lerp
  , invLerp
  , remap
  , step
  , smoothstep
  
  -- * Color Packing
  , packRGB
  , unpackRGB
  , packRGBA
  , unpackRGBA
  
  -- * SDF Utilities
  , evalSDF
  , sdfEdge
  , sdfOutline
  
  -- * Workgroup Utilities
  , boundedWorkgroupDim
  , isPowerOfTwo
  , nextPowerOfTwo
  , optimalWorkgroupSize
  
  -- * Array Utilities
  , productArray
  , sumArray
  , containsInt
  
  -- * Bounded Utilities
  , boundedRange
  , isNumberFinite
  , isWorkgroupInBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (&&)
  , min
  , max
  , top
  , bottom
  )

import Data.Int as Int
import Data.Int.Bits as Bits
import Data.Tuple (Tuple(Tuple))
import Data.Foldable (sum, product, elem)
import Data.Number as Number

import Hydrogen.GPU.Kernel.Text.Vector (Vec4)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to [0, 1]
saturate :: Number -> Number
saturate x = min 1.0 (max 0.0 x)

-- | Clamp int to range
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x = min hi (max lo x)

-- | Clamp number to range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = min hi (max lo x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Inverse lerp (find t given value)
invLerp :: Number -> Number -> Number -> Number
invLerp a b v = (v - a) / (b - a)

-- | Remap value from one range to another
remap :: Number -> Number -> Number -> Number -> Number -> Number
remap inMin inMax outMin outMax v =
  lerp outMin outMax (invLerp inMin inMax v)

-- | Step function (0 if x < edge, 1 otherwise)
step :: Number -> Number -> Number
step edge x = if x < edge then 0.0 else 1.0

-- | Smooth step (cubic interpolation between edges)
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x =
  let t = saturate (invLerp edge0 edge1 x)
  in t * t * (3.0 - 2.0 * t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // color packing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pack RGB to 24-bit int
packRGB :: Int -> Int -> Int -> Int
packRGB r g b = 
  Bits.shl (clampInt 0 255 r) 16 `Bits.or`
  Bits.shl (clampInt 0 255 g) 8 `Bits.or`
  clampInt 0 255 b

-- | Unpack 24-bit int to RGB tuple
unpackRGB :: Int -> Tuple Int (Tuple Int Int)
unpackRGB packed =
  let r = Bits.and (Bits.shr packed 16) 255
      g = Bits.and (Bits.shr packed 8) 255
      b = Bits.and packed 255
  in Tuple r (Tuple g b)

-- | Pack RGBA to 32-bit int
packRGBA :: Int -> Int -> Int -> Int -> Int
packRGBA r g b a =
  Bits.shl (clampInt 0 255 a) 24 `Bits.or`
  Bits.shl (clampInt 0 255 r) 16 `Bits.or`
  Bits.shl (clampInt 0 255 g) 8 `Bits.or`
  clampInt 0 255 b

-- | Unpack 32-bit int to RGBA
unpackRGBA :: Int -> Vec4
unpackRGBA packed =
  { x: Int.toNumber (Bits.and (Bits.shr packed 16) 255) / 255.0
  , y: Int.toNumber (Bits.and (Bits.shr packed 8) 255) / 255.0
  , z: Int.toNumber (Bits.and packed 255) / 255.0
  , w: Int.toNumber (Bits.and (Bits.shr packed 24) 255) / 255.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sdf utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | SDF evaluation: negative inside, positive outside
-- | This is the core primitive for text rendering
evalSDF :: Number -> Number -> Number
evalSDF distance threshold = distance - threshold

-- | Anti-aliased edge from SDF
sdfEdge :: Number -> Number -> Number
sdfEdge distance edgeWidth =
  saturate (0.5 - distance / edgeWidth)

-- | Outline from SDF
sdfOutline :: Number -> Number -> Number -> Number
sdfOutline distance outlineWidth edgeWidth =
  let inner = sdfEdge distance edgeWidth
      outer = sdfEdge (distance - outlineWidth) edgeWidth
  in outer - inner

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // workgroup utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get bounded workgroup dimension
boundedWorkgroupDim :: Int -> Int
boundedWorkgroupDim d = clampInt (bottom :: Int) (top :: Int) d

-- | Check if workgroup is power of two (optimal for GPU)
isPowerOfTwo :: Int -> Boolean
isPowerOfTwo n = n > 0 && Bits.and n (n - 1) == 0

-- | Round up to next power of two
nextPowerOfTwo :: Int -> Int
nextPowerOfTwo n =
  if isPowerOfTwo n then n
  else 
    let n1 = Bits.or n (Bits.shr n 1)
        n2 = Bits.or n1 (Bits.shr n1 2)
        n3 = Bits.or n2 (Bits.shr n2 4)
        n4 = Bits.or n3 (Bits.shr n3 8)
        n5 = Bits.or n4 (Bits.shr n4 16)
    in n5 + 1

-- | Optimal workgroup size (power of two, max 256)
optimalWorkgroupSize :: Int -> Int
optimalWorkgroupSize requested =
  clampInt 1 256 (nextPowerOfTwo requested)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Product of array elements
productArray :: Array Int -> Int
productArray = product

-- | Sum of array elements
sumArray :: Array Number -> Number
sumArray = sum

-- | Check if value is in array
containsInt :: Int -> Array Int -> Boolean
containsInt = elem

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bounded utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get bounded range for a type
boundedRange :: forall a. Bounded a => { min :: a, max :: a }
boundedRange = { min: bottom, max: top }

-- | Check if a number is finite using Data.Number
isNumberFinite :: Number -> Boolean
isNumberFinite n = Number.isFinite n

-- | Bounded workgroup check using top/bottom
isWorkgroupInBounds :: Int -> Boolean
isWorkgroupInBounds x = x >= (bottom :: Int) && x <= (top :: Int)
