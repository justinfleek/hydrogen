-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // physics // fluid // neighborhood
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Neighborhood Search — Octree spatial lookup for SPH.
-- |
-- | ## Research Foundation
-- |
-- | Based on SIGGRAPH Asia 2022 paper "Neighborhood Search for SPH":
-- | - Adaptive octree clusters particles
-- | - 1.9x speedup over uniform grid
-- | - Essential for pigment particle simulation at scale
-- |
-- | ## Design Philosophy
-- |
-- | Neighbor search is the bottleneck for SPH. For each particle we need
-- | all neighbors within smoothing radius h. Naive O(n²) is intractable.
-- |
-- | ## Data Structures
-- |
-- | - **Uniform Grid**: Simple, good for uniform distributions
-- | - **Octree**: Adaptive, handles variable density
-- | - **Hash Grid**: Memory efficient, good cache locality
-- |
-- | ## Complexity
-- |
-- | - Build: O(n log n) for octree, O(n) for hash grid
-- | - Query: O(k) where k = average neighbors (typically 30-50)
-- |
-- | ## UUID5 Identity
-- |
-- | Spatial structures have deterministic identity for caching.
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.Physics.Fluid.Neighborhood
  ( -- * UUID5 Namespace
    nsNeighborhood
  
  -- * Spatial Bounds
  , SpatialBounds
  , mkSpatialBounds
  , boundsMinX
  , boundsMaxX
  , boundsMinY
  , boundsMaxY
  , boundsWidth
  , boundsHeight
  , boundsContains
  , expandBounds
  , pointDistance
  , pointDistanceSq
  , boundsDistanceToPoint
  
  -- * Grid Cell
  , GridCell
  , mkGridCell
  , cellX
  , cellY
  , cellParticles
  , cellAddParticle
  
  -- * Uniform Grid
  , UniformGrid
  , mkUniformGrid
  , gridResolutionX
  , gridResolutionY
  , gridCellSize
  , insertParticle
  , queryNeighbors
  , clearGrid
  , rebuildGrid
  
  -- * Octree Node
  , OctreeNode(OctreeLeaf, OctreeBranch)
  , OctreeConfig
  , mkOctreeConfig
  , maxParticlesPerNode
  , maxDepth
  
  -- * Octree Operations
  , Octree
  , mkOctree
  , octreeInsert
  , octreeQuery
  , octreeRebuild
  , octreeDepth
  , octreeNodeCount
  
  -- * Hash Grid
  , HashGrid
  , mkHashGrid
  , hashGridInsert
  , hashGridQuery
  , hashGridClear
  , spatialHash
  
  -- * Neighbor Iterator
  , NeighborIterator
  , mkNeighborIterator
  , iteratorNext
  , iteratorHasMore
  , collectNeighbors
  
  -- * Performance Metrics
  , SearchMetrics
  , mkSearchMetrics
  , totalQueries
  , totalNeighborsFound
  , averageNeighbors
  , cacheHitRate
  
  -- * Search Strategy
  , SearchStrategy(StrategyUniformGrid, StrategyOctree, StrategyHashGrid, StrategyBruteForce)
  , allSearchStrategies
  , chooseStrategy
  , strategyComplexity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , max
  , min
  , map
  , mod
  , not
  )

import Data.Array (length, filter, foldl, snoc, concat, index) as Array
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Int (floor, toNumber) as Int
import Data.Number (sqrt, abs) as Num

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for neighborhood search structures.
nsNeighborhood :: UUID5.UUID5
nsNeighborhood = UUID5.uuid5 UUID5.nsElement "hydrogen.physics.fluid.neighborhood"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // spatial bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned bounding box for spatial queries.
type SpatialBounds =
  { minX :: Number
  , maxX :: Number
  , minY :: Number
  , maxY :: Number
  }

-- | Create spatial bounds with validation.
mkSpatialBounds :: Number -> Number -> Number -> Number -> SpatialBounds
mkSpatialBounds x1 x2 y1 y2 =
  { minX: min x1 x2
  , maxX: max x1 x2
  , minY: min y1 y2
  , maxY: max y1 y2
  }

-- | Get minimum X.
boundsMinX :: SpatialBounds -> Number
boundsMinX b = b.minX

-- | Get maximum X.
boundsMaxX :: SpatialBounds -> Number
boundsMaxX b = b.maxX

-- | Get minimum Y.
boundsMinY :: SpatialBounds -> Number
boundsMinY b = b.minY

-- | Get maximum Y.
boundsMaxY :: SpatialBounds -> Number
boundsMaxY b = b.maxY

-- | Get bounds width.
boundsWidth :: SpatialBounds -> Number
boundsWidth b = b.maxX - b.minX

-- | Get bounds height.
boundsHeight :: SpatialBounds -> Number
boundsHeight b = b.maxY - b.minY

-- | Check if point is within bounds.
boundsContains :: SpatialBounds -> Number -> Number -> Boolean
boundsContains b x y =
  x >= b.minX && x <= b.maxX && y >= b.minY && y <= b.maxY

-- | Expand bounds by margin.
expandBounds :: SpatialBounds -> Number -> SpatialBounds
expandBounds b margin =
  { minX: b.minX - margin
  , maxX: b.maxX + margin
  , minY: b.minY - margin
  , maxY: b.maxY + margin
  }

-- | Calculate Euclidean distance between two points.
pointDistance :: Number -> Number -> Number -> Number -> Number
pointDistance x1 y1 x2 y2 =
  let
    dx = x2 - x1
    dy = y2 - y1
  in
    Num.sqrt (dx * dx + dy * dy)

-- | Calculate squared distance (avoids sqrt for comparisons).
pointDistanceSq :: Number -> Number -> Number -> Number -> Number
pointDistanceSq x1 y1 x2 y2 =
  let
    dx = x2 - x1
    dy = y2 - y1
  in
    dx * dx + dy * dy

-- | Calculate distance from point to nearest point on bounds.
boundsDistanceToPoint :: SpatialBounds -> Number -> Number -> Number
boundsDistanceToPoint b px py =
  let
    closestX = max b.minX (min b.maxX px)
    closestY = max b.minY (min b.maxY py)
    dx = Num.abs (px - closestX)
    dy = Num.abs (py - closestY)
  in
    Num.sqrt (dx * dx + dy * dy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // grid cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | A cell in the spatial grid containing particle indices.
type GridCell =
  { x :: Int
  , y :: Int
  , particles :: Array Int   -- Particle indices
  }

-- | Create an empty grid cell.
mkGridCell :: Int -> Int -> GridCell
mkGridCell cx cy = { x: cx, y: cy, particles: [] }

-- | Get cell X coordinate.
cellX :: GridCell -> Int
cellX c = c.x

-- | Get cell Y coordinate.
cellY :: GridCell -> Int
cellY c = c.y

-- | Get particles in cell.
cellParticles :: GridCell -> Array Int
cellParticles c = c.particles

-- | Add particle to cell.
cellAddParticle :: GridCell -> Int -> GridCell
cellAddParticle c pid = c { particles = Array.snoc c.particles pid }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // uniform grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Uniform spatial grid for neighbor search.
-- |
-- | Cell size should be >= smoothing radius for efficient queries.
type UniformGrid =
  { bounds :: SpatialBounds
  , cellSize :: Number
  , resolutionX :: Int
  , resolutionY :: Int
  , cells :: Array GridCell
  }

-- | Create uniform grid covering bounds.
mkUniformGrid :: SpatialBounds -> Number -> UniformGrid
mkUniformGrid bounds cellSz =
  let
    cs = max 0.01 cellSz
    w = boundsWidth bounds
    h = boundsHeight bounds
    resX = max 1 (Int.floor (w / cs) + 1)
    resY = max 1 (Int.floor (h / cs) + 1)
    -- totalCells computed implicitly in buildCells
    emptyCells = buildCells resX resY 0 []
  in
    { bounds: bounds
    , cellSize: cs
    , resolutionX: resX
    , resolutionY: resY
    , cells: emptyCells
    }

-- | Build empty cell array.
buildCells :: Int -> Int -> Int -> Array GridCell -> Array GridCell
buildCells resX resY idx acc =
  if idx >= resX * resY
    then acc
    else
      let
        cx = idx `mod` resX
        cy = idx / resX
      in
        buildCells resX resY (idx + 1) (Array.snoc acc (mkGridCell cx cy))

-- | Get grid X resolution.
gridResolutionX :: UniformGrid -> Int
gridResolutionX g = g.resolutionX

-- | Get grid Y resolution.
gridResolutionY :: UniformGrid -> Int
gridResolutionY g = g.resolutionY

-- | Get cell size.
gridCellSize :: UniformGrid -> Number
gridCellSize g = g.cellSize

-- | Insert particle into grid.
insertParticle :: UniformGrid -> Int -> Number -> Number -> UniformGrid
insertParticle grid pid px py =
  let
    cx = Int.floor ((px - grid.bounds.minX) / grid.cellSize)
    cy = Int.floor ((py - grid.bounds.minY) / grid.cellSize)
    idx = cy * grid.resolutionX + cx
  in
    if cx >= 0 && cx < grid.resolutionX && cy >= 0 && cy < grid.resolutionY
      then updateCellAt grid idx pid
      else grid

-- | Update cell at index.
updateCellAt :: UniformGrid -> Int -> Int -> UniformGrid
updateCellAt grid idx pid =
  case Array.index grid.cells idx of
    Nothing -> grid
    Just cell ->
      let
        newCell = cellAddParticle cell pid
        newCells = updateArrayAt grid.cells idx newCell
      in
        grid { cells = newCells }

-- | Update array at index.
updateArrayAt :: forall a. Array a -> Int -> a -> Array a
updateArrayAt arr idx val =
  Array.foldl (\acc i ->
    let v = if i == idx then val else fromMaybe val (Array.index arr i)
    in Array.snoc acc v
  ) [] (buildIndices (Array.length arr))

-- | Build indices 0 to n-1.
buildIndices :: Int -> Array Int
buildIndices n = buildIndicesRec n 0 []

buildIndicesRec :: Int -> Int -> Array Int -> Array Int
buildIndicesRec n i acc =
  if i >= n then acc
  else buildIndicesRec n (i + 1) (Array.snoc acc i)

-- | Query neighbors within radius.
queryNeighbors :: UniformGrid -> Number -> Number -> Number -> Array Int
queryNeighbors grid px py radius =
  let
    -- Find cell range to check
    minCx = max 0 (Int.floor ((px - radius - grid.bounds.minX) / grid.cellSize))
    maxCx = min (grid.resolutionX - 1) (Int.floor ((px + radius - grid.bounds.minX) / grid.cellSize))
    minCy = max 0 (Int.floor ((py - radius - grid.bounds.minY) / grid.cellSize))
    maxCy = min (grid.resolutionY - 1) (Int.floor ((py + radius - grid.bounds.minY) / grid.cellSize))
    
    -- Collect particles from cells in range
    cellsInRange = collectCellsInRange grid minCx maxCx minCy maxCy
    allParticles = Array.concat (map cellParticles cellsInRange)
  in
    allParticles

-- | Collect cells in range.
collectCellsInRange :: UniformGrid -> Int -> Int -> Int -> Int -> Array GridCell
collectCellsInRange grid minCx maxCx minCy maxCy =
  Array.filter (\c -> 
    c.x >= minCx && c.x <= maxCx && c.y >= minCy && c.y <= maxCy
  ) grid.cells

-- | Clear all particles from grid.
clearGrid :: UniformGrid -> UniformGrid
clearGrid grid =
  grid { cells = map (\c -> c { particles = [] }) grid.cells }

-- | Rebuild grid with new particle positions.
rebuildGrid :: UniformGrid -> Array { id :: Int, x :: Number, y :: Number } -> UniformGrid
rebuildGrid grid particles =
  let
    cleared = clearGrid grid
  in
    Array.foldl (\g p -> insertParticle g p.id p.x p.y) cleared particles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // octree node
-- ═════════════════════════════════════════════════════════════════════════════

-- | Octree configuration.
type OctreeConfig =
  { maxParticles :: Int    -- ^ Max particles before split
  , maxDepth :: Int        -- ^ Maximum tree depth
  }

-- | Create octree configuration.
mkOctreeConfig :: Int -> Int -> OctreeConfig
mkOctreeConfig maxP maxD =
  { maxParticles: max 1 maxP
  , maxDepth: max 1 maxD
  }

-- | Get max particles per node.
maxParticlesPerNode :: OctreeConfig -> Int
maxParticlesPerNode c = c.maxParticles

-- | Get max depth.
maxDepth :: OctreeConfig -> Int
maxDepth c = c.maxDepth

-- | Octree node (quadtree for 2D).
data OctreeNode
  = OctreeLeaf
      { bounds :: SpatialBounds
      , particles :: Array Int
      , depth :: Int
      }
  | OctreeBranch
      { bounds :: SpatialBounds
      , children :: Array OctreeNode  -- 4 children for quadtree
      , depth :: Int
      }

derive instance eqOctreeNode :: Eq OctreeNode

instance showOctreeNode :: Show OctreeNode where
  show (OctreeLeaf l) = "Leaf(" <> show (Array.length l.particles) <> " particles)"
  show (OctreeBranch b) = "Branch(depth=" <> show b.depth <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // octree operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete octree structure.
type Octree =
  { root :: OctreeNode
  , config :: OctreeConfig
  , totalParticles :: Int
  }

-- | Create empty octree.
mkOctree :: SpatialBounds -> OctreeConfig -> Octree
mkOctree bounds config =
  { root: OctreeLeaf { bounds: bounds, particles: [], depth: 0 }
  , config: config
  , totalParticles: 0
  }

-- | Insert particle into octree.
octreeInsert :: Octree -> Int -> Number -> Number -> Octree
octreeInsert tree pid px py =
  let
    newRoot = insertIntoNode tree.config tree.root pid px py
  in
    tree { root = newRoot, totalParticles = tree.totalParticles + 1 }

-- | Insert into node recursively.
insertIntoNode :: OctreeConfig -> OctreeNode -> Int -> Number -> Number -> OctreeNode
insertIntoNode config node pid px py =
  case node of
    OctreeLeaf leaf ->
      if not (boundsContains leaf.bounds px py)
        then node  -- Outside bounds
        else if Array.length leaf.particles < config.maxParticles || leaf.depth >= config.maxDepth
          then OctreeLeaf (leaf { particles = Array.snoc leaf.particles pid })
          else
            -- Split and reinsert
            let
              branch = splitLeaf config leaf
            in
              insertIntoNode config branch pid px py
    
    OctreeBranch branch ->
      let
        newChildren = map (\child -> 
          case child of
            OctreeLeaf l -> 
              if boundsContains l.bounds px py
                then insertIntoNode config child pid px py
                else child
            OctreeBranch b ->
              if boundsContains b.bounds px py
                then insertIntoNode config child pid px py
                else child
        ) branch.children
      in
        OctreeBranch (branch { children = newChildren })

-- | Split a leaf node into 4 children.
splitLeaf :: OctreeConfig -> { bounds :: SpatialBounds, particles :: Array Int, depth :: Int } -> OctreeNode
splitLeaf _config leaf =
  let
    b = leaf.bounds
    midX = (b.minX + b.maxX) / 2.0
    midY = (b.minY + b.maxY) / 2.0
    newDepth = leaf.depth + 1
    
    -- Create 4 quadrants
    q0 = mkSpatialBounds b.minX midX b.minY midY      -- Bottom-left
    q1 = mkSpatialBounds midX b.maxX b.minY midY      -- Bottom-right
    q2 = mkSpatialBounds b.minX midX midY b.maxY      -- Top-left
    q3 = mkSpatialBounds midX b.maxX midY b.maxY      -- Top-right
    
    children =
      [ OctreeLeaf { bounds: q0, particles: [], depth: newDepth }
      , OctreeLeaf { bounds: q1, particles: [], depth: newDepth }
      , OctreeLeaf { bounds: q2, particles: [], depth: newDepth }
      , OctreeLeaf { bounds: q3, particles: [], depth: newDepth }
      ]
  in
    OctreeBranch { bounds: b, children: children, depth: leaf.depth }

-- | Query neighbors in octree.
octreeQuery :: Octree -> Number -> Number -> Number -> Array Int
octreeQuery tree px py radius =
  queryNode tree.root px py radius

-- | Query node recursively.
queryNode :: OctreeNode -> Number -> Number -> Number -> Array Int
queryNode node px py radius =
  case node of
    OctreeLeaf leaf ->
      if boundsIntersectsCircle leaf.bounds px py radius
        then leaf.particles
        else []
    
    OctreeBranch branch ->
      if boundsIntersectsCircle branch.bounds px py radius
        then Array.concat (map (\child -> queryNode child px py radius) branch.children)
        else []

-- | Check if bounds intersects circle.
boundsIntersectsCircle :: SpatialBounds -> Number -> Number -> Number -> Boolean
boundsIntersectsCircle b cx cy r =
  let
    -- Find closest point on box to circle center
    closestX = max b.minX (min b.maxX cx)
    closestY = max b.minY (min b.maxY cy)
    dx = cx - closestX
    dy = cy - closestY
  in
    (dx * dx + dy * dy) <= (r * r)

-- | Rebuild octree with new particles.
octreeRebuild :: Octree -> Array { id :: Int, x :: Number, y :: Number } -> Octree
octreeRebuild tree particles =
  let
    bounds = case tree.root of
      OctreeLeaf l -> l.bounds
      OctreeBranch b -> b.bounds
    empty = mkOctree bounds tree.config
  in
    Array.foldl (\t p -> octreeInsert t p.id p.x p.y) empty particles

-- | Get maximum depth of octree.
octreeDepth :: Octree -> Int
octreeDepth tree = nodeDepth tree.root

nodeDepth :: OctreeNode -> Int
nodeDepth (OctreeLeaf l) = l.depth
nodeDepth (OctreeBranch b) = 
  Array.foldl (\maxD child -> max maxD (nodeDepth child)) b.depth b.children

-- | Count total nodes in octree.
octreeNodeCount :: Octree -> Int
octreeNodeCount tree = countNodes tree.root

countNodes :: OctreeNode -> Int
countNodes (OctreeLeaf _) = 1
countNodes (OctreeBranch b) = 
  1 + Array.foldl (\acc child -> acc + countNodes child) 0 b.children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // hash grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hash-based spatial grid.
-- |
-- | More memory-efficient than uniform grid for sparse distributions.
type HashGrid =
  { cellSize :: Number
  , tableSize :: Int
  , buckets :: Array (Array Int)  -- Hash buckets containing particle IDs
  }

-- | Create hash grid.
mkHashGrid :: Number -> Int -> HashGrid
mkHashGrid cellSz tblSize =
  { cellSize: max 0.01 cellSz
  , tableSize: max 16 tblSize
  , buckets: map (\_ -> []) (buildIndices (max 16 tblSize))
  }

-- | Spatial hash function.
-- |
-- | Maps (x, y) cell coordinates to hash bucket.
spatialHash :: Int -> Int -> Int -> Int
spatialHash cx cy tableSize =
  let
    -- Large primes for hashing
    p1 = 73856093
    p2 = 19349663
    h = ((cx * p1) + (cy * p2)) `mod` tableSize
  in
    if h < 0 then h + tableSize else h

-- | Insert particle into hash grid.
hashGridInsert :: HashGrid -> Int -> Number -> Number -> HashGrid
hashGridInsert grid pid px py =
  let
    cx = Int.floor (px / grid.cellSize)
    cy = Int.floor (py / grid.cellSize)
    h = spatialHash cx cy grid.tableSize
    bucket = fromMaybe [] (Array.index grid.buckets h)
    newBucket = Array.snoc bucket pid
    newBuckets = updateArrayAt grid.buckets h newBucket
  in
    grid { buckets = newBuckets }

-- | Query neighbors in hash grid.
hashGridQuery :: HashGrid -> Number -> Number -> Number -> Array Int
hashGridQuery grid px py radius =
  let
    cellsToCheck = Int.floor (radius / grid.cellSize) + 1
    centerCx = Int.floor (px / grid.cellSize)
    centerCy = Int.floor (py / grid.cellSize)
    
    -- Collect from all nearby buckets
    
    allBuckets = collectNearbyBuckets grid centerCx centerCy cellsToCheck
  in
    Array.concat allBuckets

-- | Collect particles from nearby hash buckets.
collectNearbyBuckets :: HashGrid -> Int -> Int -> Int -> Array (Array Int)
collectNearbyBuckets grid cx cy range =
  let
    offsets = buildOffsets range
  in
    map (\off ->
      let
        ncx = cx + off.dx
        ncy = cy + off.dy
        h = spatialHash ncx ncy grid.tableSize
      in
        fromMaybe [] (Array.index grid.buckets h)
    ) offsets

-- | Build offset pairs for range.
buildOffsets :: Int -> Array { dx :: Int, dy :: Int }
buildOffsets range =
  buildOffsetsRec (0 - range) (0 - range) range []

buildOffsetsRec :: Int -> Int -> Int -> Array { dx :: Int, dy :: Int } -> Array { dx :: Int, dy :: Int }
buildOffsetsRec dx dy range acc =
  if dy > range then acc
  else if dx > range then buildOffsetsRec (0 - range) (dy + 1) range acc
  else buildOffsetsRec (dx + 1) dy range (Array.snoc acc { dx: dx, dy: dy })

-- | Clear hash grid.
hashGridClear :: HashGrid -> HashGrid
hashGridClear grid =
  grid { buckets = map (\_ -> []) grid.buckets }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // neighbor iterator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Iterator for lazy neighbor enumeration.
type NeighborIterator =
  { candidates :: Array Int
  , currentIndex :: Int
  , centerX :: Number
  , centerY :: Number
  , radius :: Number
  }

-- | Create neighbor iterator.
mkNeighborIterator :: Array Int -> Number -> Number -> Number -> NeighborIterator
mkNeighborIterator candidates cx cy r =
  { candidates: candidates
  , currentIndex: 0
  , centerX: cx
  , centerY: cy
  , radius: r
  }

-- | Get next neighbor (if any).
iteratorNext :: NeighborIterator -> { neighbor :: Maybe Int, iterator :: NeighborIterator }
iteratorNext iter =
  if iter.currentIndex >= Array.length iter.candidates
    then { neighbor: Nothing, iterator: iter }
    else
      let
        pid = Array.index iter.candidates iter.currentIndex
        newIter = iter { currentIndex = iter.currentIndex + 1 }
      in
        { neighbor: pid, iterator: newIter }

-- | Check if iterator has more neighbors.
iteratorHasMore :: NeighborIterator -> Boolean
iteratorHasMore iter = iter.currentIndex < Array.length iter.candidates

-- | Collect all neighbors from iterator.
collectNeighbors :: NeighborIterator -> Array Int
collectNeighbors iter = iter.candidates

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // performance metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Performance metrics for neighbor search.
type SearchMetrics =
  { queries :: Int
  , neighborsFound :: Int
  , cacheHits :: Int
  , cacheMisses :: Int
  }

-- | Create empty metrics.
mkSearchMetrics :: SearchMetrics
mkSearchMetrics =
  { queries: 0
  , neighborsFound: 0
  , cacheHits: 0
  , cacheMisses: 0
  }

-- | Get total queries.
totalQueries :: SearchMetrics -> Int
totalQueries m = m.queries

-- | Get total neighbors found.
totalNeighborsFound :: SearchMetrics -> Int
totalNeighborsFound m = m.neighborsFound

-- | Get average neighbors per query.
averageNeighbors :: SearchMetrics -> Number
averageNeighbors m =
  if m.queries > 0
    then Int.toNumber m.neighborsFound / Int.toNumber m.queries
    else 0.0

-- | Get cache hit rate.
cacheHitRate :: SearchMetrics -> Number
cacheHitRate m =
  let total = m.cacheHits + m.cacheMisses
  in if total > 0
    then Int.toNumber m.cacheHits / Int.toNumber total
    else 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // search strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strategy for neighbor search.
data SearchStrategy
  = StrategyUniformGrid   -- ^ Best for uniform distributions
  | StrategyOctree        -- ^ Best for variable density
  | StrategyHashGrid      -- ^ Best for memory efficiency
  | StrategyBruteForce    -- ^ For very small particle counts

derive instance eqSearchStrategy :: Eq SearchStrategy
derive instance ordSearchStrategy :: Ord SearchStrategy

instance showSearchStrategy :: Show SearchStrategy where
  show StrategyUniformGrid = "uniform-grid"
  show StrategyOctree = "octree"
  show StrategyHashGrid = "hash-grid"
  show StrategyBruteForce = "brute-force"

-- | All search strategies.
allSearchStrategies :: Array SearchStrategy
allSearchStrategies =
  [ StrategyUniformGrid, StrategyOctree, StrategyHashGrid, StrategyBruteForce ]

-- | Choose optimal strategy based on particle count and distribution.
chooseStrategy :: Int -> Number -> SearchStrategy
chooseStrategy particleCount densityVariance
  | particleCount < 100 = StrategyBruteForce
  | densityVariance > 0.5 = StrategyOctree
  | particleCount > 100000 = StrategyHashGrid
  | true = StrategyUniformGrid

-- | Get complexity class of strategy.
strategyComplexity :: SearchStrategy -> String
strategyComplexity StrategyUniformGrid = "O(n + k)"
strategyComplexity StrategyOctree = "O(n log n + k)"
strategyComplexity StrategyHashGrid = "O(n + k)"
strategyComplexity StrategyBruteForce = "O(n²)"
