-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // effects // perspective // bevel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bevel Effects — functions for bevel alpha and bevel edges effects.
-- |
-- | Implements motion graphics Bevel Alpha and Bevel Edges effects with
-- | bounded properties for deterministic rendering across agents.

module Hydrogen.Schema.Motion.Effects.Perspective.Bevel
  ( -- * Bevel Alpha Constructors
    defaultBevelAlpha
  , bevelAlphaWithDepth
  
  -- * Bevel Edges Constructors
  , defaultBevelEdges
  , bevelEdgesWithDepth
  
  -- * Effect Names
  , bevelAlphaEffectName
  , bevelEdgesEffectName
  
  -- * Descriptions
  , describeBevelAlpha
  
  -- * Queries
  , hasBevelLight
  , isBevelThick
  , hasBevelFullLighting
  
  -- * Value Clamping
  , clampBevelAlphaValues
  
  -- * Serialization
  , bevelEdgeStyleToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  , (>)
  , (>=)
  , (&&)
  , (||)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (rgb)
import Hydrogen.Schema.Motion.Effects.Perspective.Types
  ( BevelAlphaEffect
  , BevelEdgeStyle
    ( BESSmooth
    )
  , BevelEdgesEffect
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // bevel // alpha // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default bevel alpha.
defaultBevelAlpha :: BevelAlphaEffect
defaultBevelAlpha =
  { edgeThickness: 5.0
  , lightAngle: 135.0
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  , edgeStyle: BESSmooth
  }

-- | Create bevel alpha with specific depth.
bevelAlphaWithDepth :: Number -> Number -> BevelAlphaEffect
bevelAlphaWithDepth thickness angle =
  { edgeThickness: clampNumber 0.0 100.0 thickness
  , lightAngle: clampNumber 0.0 360.0 angle
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  , edgeStyle: BESSmooth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // bevel // edges // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default bevel edges.
defaultBevelEdges :: BevelEdgesEffect
defaultBevelEdges =
  { edgeThickness: 5.0
  , lightAngle: 135.0
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  }

-- | Create bevel edges with specific depth.
bevelEdgesWithDepth :: Number -> Number -> BevelEdgesEffect
bevelEdgesWithDepth thickness angle =
  { edgeThickness: clampNumber 0.0 100.0 thickness
  , lightAngle: clampNumber 0.0 360.0 angle
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Bevel Alpha.
bevelAlphaEffectName :: BevelAlphaEffect -> String
bevelAlphaEffectName _ = "Bevel Alpha"

-- | Effect name for Bevel Edges.
bevelEdgesEffectName :: BevelEdgesEffect -> String
bevelEdgesEffectName _ = "Bevel Edges"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe bevel alpha effect.
describeBevelAlpha :: BevelAlphaEffect -> String
describeBevelAlpha e =
  "BevelAlpha(" <> show e.edgeStyle <> ", depth: " <> show e.edgeThickness <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if bevel has lighting enabled.
hasBevelLight :: BevelAlphaEffect -> Boolean
hasBevelLight e = e.lightIntensity > 0.0 || e.shadowIntensity > 0.0

-- | Check if bevel edge is thick (>= 10).
isBevelThick :: BevelAlphaEffect -> Boolean
isBevelThick e = e.edgeThickness >= 10.0

-- | Check if bevel has full lighting (both highlight and shadow).
hasBevelFullLighting :: BevelAlphaEffect -> Boolean
hasBevelFullLighting e = e.lightIntensity > 0.0 && e.shadowIntensity > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // value // clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp bevel values to valid ranges.
clampBevelAlphaValues :: BevelAlphaEffect -> BevelAlphaEffect
clampBevelAlphaValues e =
  { edgeThickness: clampNumber 0.0 100.0 e.edgeThickness
  , lightAngle: clampNumber 0.0 360.0 e.lightAngle
  , lightColor: e.lightColor
  , lightIntensity: clampNumber 0.0 200.0 e.lightIntensity
  , shadowColor: e.shadowColor
  , shadowIntensity: clampNumber 0.0 200.0 e.shadowIntensity
  , edgeStyle: e.edgeStyle
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert BevelEdgeStyle to string.
bevelEdgeStyleToString :: BevelEdgeStyle -> String
bevelEdgeStyleToString s = show (s :: BevelEdgeStyle)
