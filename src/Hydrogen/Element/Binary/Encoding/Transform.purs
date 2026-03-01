-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // binary // encoding // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform Serialization
-- |
-- | Binary encoding for Transform2D.
-- | Note: GroupSpec and TransformSpec serialization live in the main module
-- | due to the circular dependency with serializeElement.

module Hydrogen.Element.Binary.Encoding.Transform
  ( serializeTransform2D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Element.Binary.Types
  ( Bytes
  )

import Hydrogen.Element.Binary.Primitives
  ( concatBytes
  , writeF32
  )

import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Schema.Geometry.Transform as Transform

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // transform serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Transform2D
-- | Layout: translateX (4) + translateY (4) + scaleX (4) + scaleY (4) +
-- |         rotation (4) + skewX (4) + skewY (4) + originX (4) + originY (4) = 36 bytes
serializeTransform2D :: Transform.Transform2D -> Bytes
serializeTransform2D (Transform.Transform2D t) =
  let
    -- Extract translate values (default to 0)
    Tuple tx ty = case t.translate of
      Nothing -> Tuple 0.0 0.0
      Just (Transform.Translate tr) -> Tuple tr.x tr.y
    
    -- Extract scale values (default to 1)
    Tuple sx sy = case t.scale of
      Nothing -> Tuple 1.0 1.0
      Just (Transform.Scale sc) -> Tuple sc.x sc.y
    
    -- Extract rotation (default to 0)
    rot = case t.rotate of
      Nothing -> 0.0
      Just (Transform.Rotate r) -> unwrapDegrees r.angle
    
    -- Extract skew values (default to 0)
    Tuple skx sky = case t.skew of
      Nothing -> Tuple 0.0 0.0
      Just (Transform.Skew sk) -> Tuple sk.x sk.y
    
    -- Extract origin (percentages 0-100)
    Transform.Origin orig = t.origin
  in
    concatBytes (writeF32 tx) $
    concatBytes (writeF32 ty) $
    concatBytes (writeF32 sx) $
    concatBytes (writeF32 sy) $
    concatBytes (writeF32 rot) $
    concatBytes (writeF32 skx) $
    concatBytes (writeF32 sky) $
    concatBytes (writeF32 orig.x) $
    writeF32 orig.y
