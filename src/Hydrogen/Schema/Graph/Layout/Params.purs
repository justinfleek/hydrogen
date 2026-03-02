-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // graph // layout // params
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layout Parameters — Algorithm-specific configuration.
-- |
-- | ## Contents
-- |
-- | - TreemapParams: Treemap algorithm configuration
-- | - RadialParams: Radial/sunburst layout configuration  
-- | - ForceParams: Force-directed simulation parameters
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Graph.Layout.Params
  ( -- * Treemap Specific
    TreemapAlgorithm(Squarify, Binary, Slice, Dice, SliceDice)
  , TreemapParams
  , treemapParams
  , defaultTreemapParams
  , treemapAlgorithm
  , treemapPaddingInner
  , treemapPaddingOuter
  , treemapPaddingTop
  , treemapRatio
  
  -- * Radial Specific
  , RadialParams
  , radialParams
  , defaultRadialParams
  , startAngle
  , endAngle
  , innerRadius
  , outerRadius
  , isClockwise
  
  -- * Force Specific
  , ForceParams
  , forceParams
  , defaultForceParams
  , repulsion
  , attraction
  , gravity
  , damping
  , iterations
  , linkDistance
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (*)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // treemap specific
-- ═════════════════════════════════════════════════════════════════════════════

-- | Treemap tiling algorithm
data TreemapAlgorithm
  = Squarify       -- ^ Optimal squareness (Bruls et al.)
  | Binary         -- ^ Binary split
  | Slice          -- ^ Horizontal slices
  | Dice           -- ^ Vertical slices
  | SliceDice      -- ^ Alternating slice/dice per level

derive instance eqTreemapAlgorithm :: Eq TreemapAlgorithm

instance showTreemapAlgorithm :: Show TreemapAlgorithm where
  show Squarify = "squarify"
  show Binary = "binary"
  show Slice = "slice"
  show Dice = "dice"
  show SliceDice = "slice-dice"

-- | Treemap-specific parameters
type TreemapParams =
  { algorithm :: TreemapAlgorithm
  , paddingInner :: Number    -- ^ Padding between siblings
  , paddingOuter :: Number    -- ^ Padding around groups
  , paddingTop :: Number      -- ^ Extra top padding (for labels)
  , ratio :: Number           -- ^ Target aspect ratio for squarify
  }

-- | Create treemap params
treemapParams :: TreemapAlgorithm -> TreemapParams
treemapParams alg =
  { algorithm: alg
  , paddingInner: 2.0
  , paddingOuter: 4.0
  , paddingTop: 20.0
  , ratio: 1.618  -- Golden ratio
  }

-- | Default treemap params (squarify)
defaultTreemapParams :: TreemapParams
defaultTreemapParams = treemapParams Squarify

-- | Get treemap algorithm
treemapAlgorithm :: TreemapParams -> TreemapAlgorithm
treemapAlgorithm p = p.algorithm

-- | Get inner padding
treemapPaddingInner :: TreemapParams -> Number
treemapPaddingInner p = p.paddingInner

-- | Get outer padding
treemapPaddingOuter :: TreemapParams -> Number
treemapPaddingOuter p = p.paddingOuter

-- | Get top padding
treemapPaddingTop :: TreemapParams -> Number
treemapPaddingTop p = p.paddingTop

-- | Get target ratio
treemapRatio :: TreemapParams -> Number
treemapRatio p = p.ratio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radial specific
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radial layout parameters
type RadialParams =
  { startAngle :: Number      -- ^ Start angle in radians (0 = right)
  , endAngle :: Number        -- ^ End angle in radians
  , innerRadius :: Number     -- ^ Inner radius (root position)
  , outerRadius :: Number     -- ^ Outer radius (leaf positions)
  , clockwise :: Boolean      -- ^ Direction of layout
  }

-- | Create radial params
radialParams :: Number -> Number -> Number -> Number -> RadialParams
radialParams start end inner outer =
  { startAngle: start
  , endAngle: end
  , innerRadius: inner
  , outerRadius: outer
  , clockwise: true
  }

-- | Default radial params (full circle)
defaultRadialParams :: RadialParams
defaultRadialParams = radialParams 0.0 (2.0 * pi) 50.0 300.0
  where
    pi = 3.14159265359

-- | Get start angle
startAngle :: RadialParams -> Number
startAngle p = p.startAngle

-- | Get end angle
endAngle :: RadialParams -> Number
endAngle p = p.endAngle

-- | Get inner radius
innerRadius :: RadialParams -> Number
innerRadius p = p.innerRadius

-- | Get outer radius
outerRadius :: RadialParams -> Number
outerRadius p = p.outerRadius

-- | Check if clockwise
isClockwise :: RadialParams -> Boolean
isClockwise p = p.clockwise

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // force specific
-- ═════════════════════════════════════════════════════════════════════════════

-- | Force-directed layout parameters
type ForceParams =
  { repulsion :: Number       -- ^ Node repulsion strength
  , attraction :: Number      -- ^ Edge attraction strength
  , gravity :: Number         -- ^ Center gravity
  , damping :: Number         -- ^ Velocity damping (0-1)
  , iterations :: Int         -- ^ Simulation iterations
  , linkDistance :: Number    -- ^ Ideal edge length
  }

-- | Create force params
forceParams :: Number -> Number -> Number -> ForceParams
forceParams rep att grav =
  { repulsion: rep
  , attraction: att
  , gravity: grav
  , damping: 0.9
  , iterations: 300
  , linkDistance: 100.0
  }

-- | Default force params
defaultForceParams :: ForceParams
defaultForceParams = forceParams 100.0 0.1 0.05

-- | Get repulsion strength
repulsion :: ForceParams -> Number
repulsion p = p.repulsion

-- | Get attraction strength
attraction :: ForceParams -> Number
attraction p = p.attraction

-- | Get gravity strength
gravity :: ForceParams -> Number
gravity p = p.gravity

-- | Get damping factor
damping :: ForceParams -> Number
damping p = p.damping

-- | Get iteration count
iterations :: ForceParams -> Int
iterations p = p.iterations

-- | Get link distance
linkDistance :: ForceParams -> Number
linkDistance p = p.linkDistance
