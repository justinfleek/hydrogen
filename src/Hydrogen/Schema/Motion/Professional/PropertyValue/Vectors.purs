-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--       // hydrogen // schema // motion // professional // propertyvalue // vectors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vector Property Values — 2D and 3D vector types for motion graphics properties.
-- |
-- | This module defines spatial and non-spatial 2D/3D vector types. The
-- | distinction between spatial and non-spatial matters for keyframe
-- | interpolation: spatial values have motion path tangents.

module Hydrogen.Schema.Motion.Professional.PropertyValue.Vectors
  ( -- * Spatial 3D Value
    Spatial3D
  , spatial3D
  , spatial3DFromArray
  , spatial3DX
  , spatial3DY
  , spatial3DZ
  , spatial3DToArray
  
  -- * Non-Spatial 3D Value  
  , ThreeD
  , threeD
  , threeDFromArray
  , threeDX
  , threeDY
  , threeDZ
  , threeDToArray
  
  -- * Spatial 2D Value
  , Spatial2D
  , spatial2D
  , spatial2DFromArray
  , spatial2DX
  , spatial2DY
  , spatial2DToArray
  
  -- * Non-Spatial 2D Value
  , TwoD
  , twoD
  , twoDFromArray
  , twoDX
  , twoDY
  , twoDToArray
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , bind
  , (<>)
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (index, length) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spatial // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D spatial value - position in 3D space WITH motion path tangents.
-- |
-- | In AE, 3D Position is Spatial3D because the keyframes form a bezier
-- | motion path in 3D space. The tangent handles control the curve shape.
newtype Spatial3D = Spatial3D { x :: Number, y :: Number, z :: Number }

derive instance eqSpatial3D :: Eq Spatial3D
derive instance ordSpatial3D :: Ord Spatial3D

instance showSpatial3D :: Show Spatial3D where
  show (Spatial3D v) = "[" <> show v.x <> ", " <> show v.y <> ", " <> show v.z <> "]"

spatial3D :: Number -> Number -> Number -> Spatial3D
spatial3D x y z = Spatial3D { x, y, z }

spatial3DFromArray :: Array Number -> Maybe Spatial3D
spatial3DFromArray arr = 
  case Array.length arr of
    3 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      z <- Array.index arr 2
      Just (Spatial3D { x, y, z })
    _ -> Nothing

spatial3DX :: Spatial3D -> Number
spatial3DX (Spatial3D v) = v.x

spatial3DY :: Spatial3D -> Number
spatial3DY (Spatial3D v) = v.y

spatial3DZ :: Spatial3D -> Number
spatial3DZ (Spatial3D v) = v.z

spatial3DToArray :: Spatial3D -> Array Number
spatial3DToArray (Spatial3D v) = [v.x, v.y, v.z]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // three // d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D non-spatial value - 3 numbers WITHOUT motion path tangents.
-- |
-- | Used for: Scale, Orientation, 3D Point Control, etc.
-- | These animate in value space, not spatial space.
newtype ThreeD = ThreeD { x :: Number, y :: Number, z :: Number }

derive instance eqThreeD :: Eq ThreeD
derive instance ordThreeD :: Ord ThreeD

instance showThreeD :: Show ThreeD where
  show (ThreeD v) = "[" <> show v.x <> ", " <> show v.y <> ", " <> show v.z <> "]"

threeD :: Number -> Number -> Number -> ThreeD
threeD x y z = ThreeD { x, y, z }

threeDFromArray :: Array Number -> Maybe ThreeD
threeDFromArray arr = 
  case Array.length arr of
    3 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      z <- Array.index arr 2
      Just (ThreeD { x, y, z })
    _ -> Nothing

threeDX :: ThreeD -> Number
threeDX (ThreeD v) = v.x

threeDY :: ThreeD -> Number
threeDY (ThreeD v) = v.y

threeDZ :: ThreeD -> Number
threeDZ (ThreeD v) = v.z

threeDToArray :: ThreeD -> Array Number
threeDToArray (ThreeD v) = [v.x, v.y, v.z]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spatial // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D spatial value - position in 2D space WITH motion path tangents.
-- |
-- | In AE, 2D Position is Spatial2D because keyframes form a bezier
-- | motion path. When "Separate Dimensions" is disabled.
newtype Spatial2D = Spatial2D { x :: Number, y :: Number }

derive instance eqSpatial2D :: Eq Spatial2D
derive instance ordSpatial2D :: Ord Spatial2D

instance showSpatial2D :: Show Spatial2D where
  show (Spatial2D v) = "[" <> show v.x <> ", " <> show v.y <> "]"

spatial2D :: Number -> Number -> Spatial2D
spatial2D x y = Spatial2D { x, y }

spatial2DFromArray :: Array Number -> Maybe Spatial2D
spatial2DFromArray arr = 
  case Array.length arr of
    2 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      Just (Spatial2D { x, y })
    _ -> Nothing

spatial2DX :: Spatial2D -> Number
spatial2DX (Spatial2D v) = v.x

spatial2DY :: Spatial2D -> Number
spatial2DY (Spatial2D v) = v.y

spatial2DToArray :: Spatial2D -> Array Number
spatial2DToArray (Spatial2D v) = [v.x, v.y]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // two // d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D non-spatial value - 2 numbers WITHOUT motion path tangents.
-- |
-- | Used for: Anchor Point, Scale (2D), 2D Point Control, etc.
newtype TwoD = TwoD { x :: Number, y :: Number }

derive instance eqTwoD :: Eq TwoD
derive instance ordTwoD :: Ord TwoD

instance showTwoD :: Show TwoD where
  show (TwoD v) = "[" <> show v.x <> ", " <> show v.y <> "]"

twoD :: Number -> Number -> TwoD
twoD x y = TwoD { x, y }

twoDFromArray :: Array Number -> Maybe TwoD
twoDFromArray arr = 
  case Array.length arr of
    2 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      Just (TwoD { x, y })
    _ -> Nothing

twoDX :: TwoD -> Number
twoDX (TwoD v) = v.x

twoDY :: TwoD -> Number
twoDY (TwoD v) = v.y

twoDToArray :: TwoD -> Array Number
twoDToArray (TwoD v) = [v.x, v.y]
