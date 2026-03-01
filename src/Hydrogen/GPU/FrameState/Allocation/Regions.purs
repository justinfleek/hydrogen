-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // allocation // regions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Allocation.Regions — Region generation and spatial queries.
-- |
-- | ## Purpose
-- |
-- | Converts viewport state to regions for allocation:
-- | - Grid level selection based on viewport dimensions
-- | - Region generation with tier assignment
-- | - Spatial queries (adjacency, tier filtering)
-- |
-- | ## Design Notes
-- |
-- | Regions are generated deterministically based on viewport dimensions.
-- | Each region gets a tier (Foveal/Peripheral/Background) based on
-- | distance from center. This enables prioritization during allocation.

module Hydrogen.GPU.FrameState.Allocation.Regions
  ( -- * Grid Level Selection
    selectGridLevel
  
  -- * Region Generation
  , viewportToRegions
  , viewportToGroundSet
  , generateGridCoords
  , coordToRegion
  , assignTier
  , mkRegionId
  
  -- * Region Queries
  , regionCoord
  , adjacentRegions
  , regionsInTier
  
  -- * Allocation State Construction
  , mkAllocationState
  
  -- * Utilities
  , intToNum
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , map
  , min
  , show
  , ($)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (&&)
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set as Set

-- FrameState types
import Hydrogen.GPU.FrameState
  ( ViewportState
  , viewportLatentWidth
  , viewportLatentHeight
  )

-- Render.Online types
import Hydrogen.Render.Online.Core
  ( GridLevel(Coarse, Medium, Fine)
  , GridCoord(GridCoord)
  , mkGridCoord
  , gridLevelSize
  , RenderTier(Foveal, Peripheral, Background)
  , RegionId(RegionId)
  , Region(Region)
  , EpochId(EpochId)
  )

-- Types module (for AllocationState)
import Hydrogen.GPU.FrameState.Allocation.Types
  ( AllocationState
  , mkAllocationStateRaw
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // grid // level // select
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select appropriate grid level based on viewport latent dimensions.
-- |
-- | Heuristic:
-- | - Fine (32×32) for large viewports (latent >= 64 in both dimensions)
-- | - Medium (16×16) for standard viewports (latent >= 32)
-- | - Coarse (8×8) for small viewports or constrained rendering
-- |
-- | This ensures reasonable region sizes: ~4-8 latent pixels per region.
selectGridLevel :: Int -> Int -> GridLevel
selectGridLevel latentWidth latentHeight =
  let
    minDim = min latentWidth latentHeight
  in
    if minDim >= 64 then Fine
    else if minDim >= 32 then Medium
    else Coarse

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // region // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate all regions for a viewport at given grid level.
-- |
-- | Returns Array Region with deterministic RegionIds.
-- | Regions are assigned tiers based on distance from center:
-- | - Foveal: inner 25% of grid
-- | - Peripheral: middle 50% of grid
-- | - Background: outer 25% of grid
viewportToRegions :: ViewportState -> Array Region
viewportToRegions vs =
  let
    lw = viewportLatentWidth vs
    lh = viewportLatentHeight vs
    level = selectGridLevel lw lh
    size = gridLevelSize level
    
    -- Generate all coordinates
    coords = generateGridCoords level size
    
    -- Convert to regions with tier assignment
    regions = Array.mapMaybe (coordToRegion level size) coords
  in
    regions

-- | Generate all grid coordinates for a level.
generateGridCoords :: GridLevel -> Int -> Array { x :: Int, y :: Int }
generateGridCoords _level size =
  Array.concat $ map (\y -> map (\x -> { x, y }) (Array.range 0 (size - 1)))
                     (Array.range 0 (size - 1))

-- | Convert a coordinate to a Region with tier assignment.
coordToRegion :: GridLevel -> Int -> { x :: Int, y :: Int } -> Maybe Region
coordToRegion level size coord =
  case mkGridCoord level coord.x coord.y of
    Nothing -> Nothing
    Just gridCoord ->
      let
        tier = assignTier size coord.x coord.y
        regionId = mkRegionId level coord.x coord.y
      in
        Just (Region { id: regionId, coord: gridCoord, tier })

-- | Assign render tier based on distance from center.
-- |
-- | Uses Manhattan distance normalized by grid size:
-- | - Foveal: center 25% (distance < 0.25 * size)
-- | - Peripheral: middle ring (distance < 0.5 * size)
-- | - Background: outer ring
assignTier :: Int -> Int -> Int -> RenderTier
assignTier size x y =
  let
    -- Center of grid
    centerX = (size - 1) / 2
    centerY = (size - 1) / 2
    
    -- Manhattan distance from center (normalized)
    dx = if x > centerX then x - centerX else centerX - x
    dy = if y > centerY then y - centerY else centerY - y
    distNorm = (intToNum (dx + dy)) / (intToNum size)
  in
    if distNorm < 0.25 then Foveal
    else if distNorm < 0.5 then Peripheral
    else Background

-- | Create deterministic region ID from grid position.
-- |
-- | Format: "region-{level}-{x}-{y}"
-- | This is deterministic but not UUID5 (UUID5 would require crypto).
mkRegionId :: GridLevel -> Int -> Int -> RegionId
mkRegionId level x y =
  let
    levelStr = case level of
      Coarse -> "c"
      Medium -> "m"
      Fine -> "f"
  in
    RegionId (levelStr <> "-" <> show x <> "-" <> show y)

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum = Int.toNumber

-- | Convert viewport to a ground set for submodular optimization.
-- |
-- | Returns the regions as a Set for use with optimization algorithms.
viewportToGroundSet :: ViewportState -> Set.Set Region
viewportToGroundSet vs = Set.fromFoldable (viewportToRegions vs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // region // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the grid coordinate from a region.
regionCoord :: Region -> GridCoord
regionCoord (Region r) = r.coord

-- | Find all regions adjacent to a given region (4-connected).
-- |
-- | Returns regions sharing an edge (not diagonal).
-- | Useful for spatial smoothing or quality propagation.
adjacentRegions :: Region -> Array Region -> Array Region
adjacentRegions (Region target) allRegions =
  let
    (GridCoord tc) = target.coord
    targetLevel = tc.level
    targetX = tc.x
    targetY = tc.y
    
    -- Check if a region is adjacent (Manhattan distance = 1)
    isAdjacent :: Region -> Boolean
    isAdjacent (Region r) =
      let
        (GridCoord rc) = r.coord
        dx = if rc.x > targetX then rc.x - targetX else targetX - rc.x
        dy = if rc.y > targetY then rc.y - targetY else targetY - rc.y
      in
        rc.level == targetLevel && (dx + dy) == 1
  in
    Array.filter isAdjacent allRegions

-- | Filter regions by render tier.
-- |
-- | Returns all regions in the specified tier.
regionsInTier :: RenderTier -> Array Region -> Array Region
regionsInTier tier = Array.filter (\(Region r) -> r.tier == tier)

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // allocation // state // creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create initial allocation state for a viewport.
-- |
-- | Generates regions based on viewport dimensions and selects the
-- | appropriate grid level automatically.
mkAllocationState :: ViewportState -> AllocationState
mkAllocationState vs =
  let
    lw = viewportLatentWidth vs
    lh = viewportLatentHeight vs
    level = selectGridLevel lw lh
    regions = viewportToRegions vs
  in
    mkAllocationStateRaw (EpochId 0) regions level
