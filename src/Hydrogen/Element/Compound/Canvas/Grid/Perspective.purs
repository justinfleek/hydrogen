-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // element // compound // canvas // grid // perspective
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Perspective Grid — 1/2/3-point perspective grid generation.
-- |
-- | ## Perspective Types
-- |
-- | - **1-point**: Single vanishing point (frontal view)
-- | - **2-point**: Two vanishing points on horizon (corner view)
-- | - **3-point**: Three vanishing points (aerial/worm's eye view)
-- |
-- | ## Dependencies
-- |
-- | - Grid.Types (GridLine, gridLine)
-- | - Grid.Style (VanishingPoint)
-- | - Data.Array (concat, snoc, length)
-- | - Data.Int (toNumber)

module Hydrogen.Element.Compound.Canvas.Grid.Perspective
  ( -- * Perspective Grid
    PerspectiveGrid
  , perspectiveGrid1Point
  , perspectiveGrid2Point
  , perspectiveGrid3Point
  , perspectiveRays
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (==)
  , (<>)
  , max
  , min
  )

import Data.Array (concat, snoc, length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.Canvas.Grid.Types
  ( GridLine
  , gridLine
  )

import Hydrogen.Element.Compound.Canvas.Grid.Style
  ( VanishingPoint(VanishingPoint)
  , vanishingPoint
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // perspective grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective grid configuration.
newtype PerspectiveGrid = PerspectiveGrid
  { vanishingPoints :: Array VanishingPoint
  , rayCount :: Int  -- Rays per vanishing point (bounded 4-64)
  }

instance showPerspectiveGrid :: Show PerspectiveGrid where
  show (PerspectiveGrid p) = 
    "PerspectiveGrid(" <> show (length p.vanishingPoints) <> "-point)"

-- | Create 1-point perspective grid.
perspectiveGrid1Point :: VanishingPoint -> Int -> PerspectiveGrid
perspectiveGrid1Point vp rays = PerspectiveGrid 
  { vanishingPoints: [vp]
  , rayCount: max 4 (min 64 rays)
  }

-- | Create 2-point perspective grid.
perspectiveGrid2Point :: VanishingPoint -> VanishingPoint -> Int -> PerspectiveGrid
perspectiveGrid2Point vp1 vp2 rays = PerspectiveGrid 
  { vanishingPoints: [vp1, vp2]
  , rayCount: max 4 (min 64 rays)
  }

-- | Create 3-point perspective grid.
perspectiveGrid3Point :: VanishingPoint -> VanishingPoint -> VanishingPoint -> Int -> PerspectiveGrid
perspectiveGrid3Point vp1 vp2 vp3 rays = PerspectiveGrid 
  { vanishingPoints: [vp1, vp2, vp3]
  , rayCount: max 4 (min 64 rays)
  }

-- | Generate perspective rays from all vanishing points.
perspectiveRays :: PerspectiveGrid 
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> Array GridLine
perspectiveRays (PerspectiveGrid pg) bounds =
  generateAllRays pg.vanishingPoints pg.rayCount bounds 0 []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

generateAllRays :: Array VanishingPoint -> Int -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Int -> Array GridLine -> Array GridLine
generateAllRays vps rayCount bounds idx acc =
  case indexVP vps idx of
    Nothing -> acc
    Just vp -> 
      let rays = generateRaysFromVP vp rayCount bounds
          newAcc = concat [acc, rays]
      in generateAllRays vps rayCount bounds (idx + 1) newAcc

indexVP :: Array VanishingPoint -> Int -> Maybe VanishingPoint
indexVP vps idx = indexVPHelper vps idx 0

indexVPHelper :: Array VanishingPoint -> Int -> Int -> Maybe VanishingPoint
indexVPHelper vps targetIdx currentIdx =
  if currentIdx >= length vps then Nothing
  else if currentIdx == targetIdx then getVPAt vps currentIdx
  else indexVPHelper vps targetIdx (currentIdx + 1)

getVPAt :: Array VanishingPoint -> Int -> Maybe VanishingPoint
getVPAt vps idx =
  -- Use length check and rely on the array being short (max 3 elements)
  if idx >= length vps then Nothing
  else 
    case vps of
      [] -> Nothing
      _ -> Just (indexVPBounded vps idx)

-- | Index into perspective grid vanishing points (max 3 elements).
-- |
-- | This function is total — it handles all array sizes via pattern matching
-- | and provides a fallback for invalid cases. The name "bounded" reflects
-- | that perspective grids have a bounded number of vanishing points (1-3).
indexVPBounded :: Array VanishingPoint -> Int -> VanishingPoint
indexVPBounded vps idx =
  case vps of
    [a] -> a
    [a, b] -> if idx == 0 then a else b
    [a, b, c] -> if idx == 0 then a else if idx == 1 then b else c
    _ -> 
      -- Fallback for unexpected array sizes (>3 or empty)
      -- Perspective grids are constructed with exactly 1-3 VPs
      getFirstVPOrDefault vps

-- | Get first element, or return default vanishing point at origin.
-- |
-- | Total function — handles empty arrays with a sensible default.
getFirstVPOrDefault :: Array VanishingPoint -> VanishingPoint
getFirstVPOrDefault vps = 
  case vps of
    [a] -> a
    [a, _] -> a
    [a, _, _] -> a
    _ -> vanishingPoint 0.0 0.0 0.0  -- Origin fallback for empty

generateRaysFromVP :: VanishingPoint -> Int -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateRaysFromVP (VanishingPoint vp) rayCount bounds =
  generateVPRaysHelper vp rayCount bounds 0 []

generateVPRaysHelper :: { x :: Number, y :: Number, horizonY :: Number } -> Int -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Int -> Array GridLine -> Array GridLine
generateVPRaysHelper vp rayCount bounds current acc =
  if current >= rayCount then acc
  else
    let 
      targetX = bounds.x + bounds.width * Int.toNumber current / Int.toNumber (rayCount - 1)
      targetY = bounds.y + bounds.height
      line = gridLine vp.x vp.y targetX targetY true
      newAcc = snoc acc line
    in generateVPRaysHelper vp rayCount bounds (current + 1) newAcc


