-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // effects // perspective // shadow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Drop Shadow Effect — functions for creating and querying drop shadows.
-- |
-- | Implements After Effects' Drop Shadow effect with bounded properties
-- | for deterministic rendering across agents.

module Hydrogen.Schema.Motion.Effects.Perspective.Shadow
  ( -- * Constructors
    defaultDropShadow
  , dropShadowWithOffset
  , dropShadowWithColor
  
  -- * Effect Name
  , dropShadowEffectName
  
  -- * Descriptions
  , describeDropShadow
  , describeDropShadowFull
  , shadowDirectionToString
  
  -- * Queries
  , isShadowVisible
  , isShadowSoft
  , isShadowHard
  , isDropShadowEffective
  
  -- * Value Clamping
  , clampDropShadowValues
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (<>)
  , (<)
  , (>)
  , (&&)
  , otherwise
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Motion.Effects.Perspective.Types (DropShadowEffect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default drop shadow: black, 75% opacity, 135 degrees.
defaultDropShadow :: DropShadowEffect
defaultDropShadow =
  { shadowColor: rgb 0 0 0
  , opacity: 75.0
  , direction: 135.0
  , distance: 5.0
  , softness: 5.0
  , shadowOnly: false
  }

-- | Create drop shadow with specific offset.
dropShadowWithOffset :: Number -> Number -> Number -> DropShadowEffect
dropShadowWithOffset dir dist soft =
  { shadowColor: rgb 0 0 0
  , opacity: 75.0
  , direction: clampNumber 0.0 360.0 dir
  , distance: clampNumber 0.0 1000.0 dist
  , softness: clampNumber 0.0 1000.0 soft
  , shadowOnly: false
  }

-- | Create drop shadow with specific color.
dropShadowWithColor :: RGB -> Number -> DropShadowEffect
dropShadowWithColor col opac =
  { shadowColor: col
  , opacity: clampNumber 0.0 100.0 opac
  , direction: 135.0
  , distance: 5.0
  , softness: 5.0
  , shadowOnly: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // effect // name
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Drop Shadow.
dropShadowEffectName :: DropShadowEffect -> String
dropShadowEffectName _ = "Drop Shadow"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe drop shadow effect.
describeDropShadow :: DropShadowEffect -> String
describeDropShadow e =
  "DropShadow(opacity: " <> show e.opacity <> "%, distance: " <> show e.distance <> "px)"

-- | Get shadow direction as readable string.
shadowDirectionToString :: DropShadowEffect -> String
shadowDirectionToString e
  | e.direction < 45.0 = "bottom-right"
  | e.direction < 90.0 = "bottom"
  | e.direction < 135.0 = "bottom-left"
  | e.direction < 180.0 = "left"
  | e.direction < 225.0 = "top-left"
  | e.direction < 270.0 = "top"
  | e.direction < 315.0 = "top-right"
  | otherwise = "right"

-- | Create a complete description of a drop shadow effect.
-- | Uses $ for clean function application in complex compositions.
describeDropShadowFull :: DropShadowEffect -> String
describeDropShadowFull e =
  let
    effectiveStr = show $ isDropShadowEffective e
    softStr = show $ isShadowSoft e
  in
    "DropShadow(" 
      <> "color: " <> show e.shadowColor
      <> ", opacity: " <> show e.opacity <> "%"
      <> ", direction: " <> shadowDirectionToString e
      <> " (" <> show e.direction <> ")"
      <> ", distance: " <> show e.distance <> "px"
      <> ", softness: " <> show e.softness <> "px"
      <> ", shadowOnly: " <> show e.shadowOnly
      <> ", effective: " <> effectiveStr
      <> ", soft: " <> softStr
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if shadow is visible (opacity > 0).
isShadowVisible :: DropShadowEffect -> Boolean
isShadowVisible e = e.opacity > 0.0

-- | Check if shadow is soft (softness > distance).
isShadowSoft :: DropShadowEffect -> Boolean
isShadowSoft e = e.softness > e.distance

-- | Check if shadow is hard (no softness).
isShadowHard :: DropShadowEffect -> Boolean
isShadowHard e = e.softness < 1.0

-- | Check if drop shadow has both visible shadow and non-zero distance.
isDropShadowEffective :: DropShadowEffect -> Boolean
isDropShadowEffective e = e.opacity > 0.0 && e.distance > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // value // clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp shadow values to valid ranges.
clampDropShadowValues :: DropShadowEffect -> DropShadowEffect
clampDropShadowValues e =
  { shadowColor: e.shadowColor
  , opacity: clampNumber 0.0 100.0 e.opacity
  , direction: clampNumber 0.0 360.0 e.direction
  , distance: clampNumber 0.0 1000.0 e.distance
  , softness: clampNumber 0.0 1000.0 e.softness
  , shadowOnly: e.shadowOnly
  }
