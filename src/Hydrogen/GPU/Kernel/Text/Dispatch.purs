-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // kernel // text // dispatch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Dispatch Utilities
-- |
-- | Functions for computing dispatch sizes, workgroup dimensions, and
-- | coordinate transforms for GPU compute operations.

module Hydrogen.GPU.Kernel.Text.Dispatch
  ( -- * Dispatch Calculation
    computeDispatchGroups
  , totalInvocations
  , isDispatchValid
  
  -- * Coordinate Transforms
  , pixelToUV
  , uvToPixel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (<=)
  , (&&)
  , min
  , max
  )

import Data.Int as Int

import Hydrogen.GPU.Kernel.Text.Vector (Vec2, IVec2, IVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dispatch calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute dispatch groups for a given work size
computeDispatchGroups :: IVec3 -> IVec3 -> IVec3
computeDispatchGroups workSize groupSize =
  { x: divCeil workSize.x groupSize.x
  , y: divCeil workSize.y groupSize.y
  , z: divCeil workSize.z groupSize.z
  }
  where
    divCeil a b = (a + b - 1) / b

-- | Total invocations for dispatch
totalInvocations :: IVec3 -> IVec3 -> Int
totalInvocations groups groupSize =
  groups.x * groupSize.x * groups.y * groupSize.y * groups.z * groupSize.z

-- | Check if dispatch size is within GPU limits
isDispatchValid :: IVec3 -> Boolean
isDispatchValid d =
  d.x > 0 && d.x <= 65535 &&
  d.y > 0 && d.y <= 65535 &&
  d.z > 0 && d.z <= 65535

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // coordinate transforms
-- ═════════════════════════════════════════════════════════════════════════════

-- | UV coordinates from pixel position
pixelToUV :: IVec2 -> IVec2 -> Vec2
pixelToUV pixel size =
  { x: (Int.toNumber pixel.x + 0.5) / Int.toNumber size.x
  , y: (Int.toNumber pixel.y + 0.5) / Int.toNumber size.y
  }

-- | Pixel position from UV coordinates
uvToPixel :: Vec2 -> IVec2 -> IVec2
uvToPixel uv size =
  { x: min (size.x - 1) (max 0 (Int.floor (uv.x * Int.toNumber size.x)))
  , y: min (size.y - 1) (max 0 (Int.floor (uv.y * Int.toNumber size.y)))
  }
