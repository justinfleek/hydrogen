-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // scraper // types // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform extraction types for 1:1 visual parity.
-- |
-- | Captures all CSS transform-related properties:
-- | - 2D transforms (translate, rotate, scale, skew)
-- | - 3D transforms (perspective, rotateX/Y/Z)
-- | - Transform origin
-- | - Computed matrix representation

module Hydrogen.Scraper.Types.Transform
  ( -- * Types
    ExtractedTransform
  , TransformOrigin
  
  -- * Constructors
  , identityTransform
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Device (px) as Dev
import Hydrogen.Schema.Geometry.Transform (Scale, Translate, Rotate, Skew)
import Hydrogen.Schema.Geometry.Transform as T

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // transform origin
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS transform-origin
-- |
-- | The point around which transforms are applied.
type TransformOrigin =
  { x :: Pixel
  , y :: Pixel
  , z :: Pixel
  }

-- ═���═════════════════════════════════════════════════════════════════════════════
--                                                      // extracted transform
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete transform extraction for 1:1 parity
-- |
-- | Stores both the decomposed values and the computed matrix.
type ExtractedTransform =
  { -- Decomposed 2D transforms
    scale :: Scale
  , translate :: Translate
  , rotate :: Rotate
  , skew :: Skew
  
  -- 3D components
  , perspective :: Pixel
  , rotateX :: Number  -- ^ degrees
  , rotateY :: Number  -- ^ degrees
  , rotateZ :: Number  -- ^ degrees
  
  -- Origin
  , origin :: TransformOrigin
  
  -- Computed 4x4 matrix (row-major)
  -- Used for verification and complex transforms
  , matrix :: Array Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Identity transform (no transformation)
identityTransform :: ExtractedTransform
identityTransform =
  { scale: T.scaleIdentity
  , translate: T.translateNone
  , rotate: T.rotateNone
  , skew: T.skewNone
  , perspective: Dev.px 0.0
  , rotateX: 0.0
  , rotateY: 0.0
  , rotateZ: 0.0
  , origin:
      { x: Dev.px 0.0
      , y: Dev.px 0.0
      , z: Dev.px 0.0
      }
  , matrix: identityMatrix
  }

-- | 4x4 identity matrix (row-major)
identityMatrix :: Array Number
identityMatrix =
  [ 1.0, 0.0, 0.0, 0.0
  , 0.0, 1.0, 0.0, 0.0
  , 0.0, 0.0, 1.0, 0.0
  , 0.0, 0.0, 0.0, 1.0
  ]
