-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // graph // layout // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layout Config — Complete layout configuration compound.
-- |
-- | ## Contents
-- |
-- | - LayoutConfig: Full configuration record
-- | - Preset layouts: indentedListLayout, radialLayout, treemapLayout, etc.
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe
-- | - Layout.Types
-- | - Layout.Spacing
-- | - Layout.Constraints
-- | - Layout.Params

module Hydrogen.Schema.Graph.Layout.Config
  ( -- * Layout Configuration
    LayoutConfig
  , layoutConfig
  
  -- * Preset Layouts
  , indentedListLayout
  , radialLayout
  , sunburstLayout
  , treemapLayout
  , dendrogramLayout
  , orgChartLayout
  , mindMapLayout
  , circlePackLayout
  , forceLayout
  , tidyLayout
  
  -- * Accessors
  , configAlgorithm
  , configOrientation
  , configSpacing
  , configSizing
  , configConstraints
  , configTreemapParams
  , configRadialParams
  , configForceParams
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Graph.Layout.Types
  ( LayoutAlgorithm
      ( IndentedList
      , Radial
      , Sunburst
      , Treemap
      , Dendrogram
      , OrgChart
      , MindMap
      , CirclePack
      , Force
      , Tidy
      )
  , LayoutOrientation(TopDown, LeftRight)
  , NodeSizing(FitContent, Proportional, FixedSize)
  )

import Hydrogen.Schema.Graph.Layout.Spacing
  ( LayoutSpacing
  , defaultSpacing
  , spaciousSpacing
  )

import Hydrogen.Schema.Graph.Layout.Constraints
  ( LayoutConstraints
  , defaultConstraints
  )

import Hydrogen.Schema.Graph.Layout.Params
  ( TreemapParams
  , RadialParams
  , ForceParams
  , defaultTreemapParams
  , defaultRadialParams
  , defaultForceParams
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // layout config compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete layout configuration
type LayoutConfig =
  { algorithm :: LayoutAlgorithm
  , orientation :: LayoutOrientation
  , spacing :: LayoutSpacing
  , sizing :: NodeSizing
  , constraints :: LayoutConstraints
  
  -- Algorithm-specific params (only one applies per algorithm)
  , treemapParams :: Maybe TreemapParams
  , radialParams :: Maybe RadialParams
  , forceParams :: Maybe ForceParams
  }

-- | Create base layout config
layoutConfig :: LayoutAlgorithm -> LayoutOrientation -> LayoutConfig
layoutConfig alg orient =
  { algorithm: alg
  , orientation: orient
  , spacing: defaultSpacing
  , sizing: FitContent 100.0 32.0
  , constraints: defaultConstraints
  , treemapParams: Nothing
  , radialParams: Nothing
  , forceParams: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // preset layouts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Indented list layout (file explorer)
indentedListLayout :: LayoutConfig
indentedListLayout = layoutConfig IndentedList TopDown

-- | Radial tree layout
radialLayout :: LayoutConfig
radialLayout = (layoutConfig Radial TopDown)
  { radialParams = Just defaultRadialParams }

-- | Sunburst layout
sunburstLayout :: LayoutConfig
sunburstLayout = (layoutConfig Sunburst TopDown)
  { radialParams = Just defaultRadialParams
  , sizing = Proportional
  }

-- | Treemap layout
treemapLayout :: LayoutConfig
treemapLayout = (layoutConfig Treemap TopDown)
  { treemapParams = Just defaultTreemapParams
  , sizing = Proportional
  }

-- | Dendrogram layout (biological tree)
dendrogramLayout :: LayoutConfig
dendrogramLayout = (layoutConfig Dendrogram LeftRight)
  { spacing = spaciousSpacing }

-- | Org chart layout
orgChartLayout :: LayoutConfig
orgChartLayout = (layoutConfig OrgChart TopDown)
  { spacing = spaciousSpacing
  , sizing = FixedSize 180.0 80.0
  }

-- | Mind map layout
mindMapLayout :: LayoutConfig
mindMapLayout = layoutConfig MindMap LeftRight

-- | Circle pack layout
circlePackLayout :: LayoutConfig
circlePackLayout = (layoutConfig CirclePack TopDown)
  { sizing = Proportional }

-- | Force-directed layout
forceLayout :: LayoutConfig
forceLayout = (layoutConfig Force TopDown)
  { forceParams = Just defaultForceParams }

-- | Tidy tree layout (Reingold-Tilford)
tidyLayout :: LayoutConfig
tidyLayout = layoutConfig Tidy TopDown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get algorithm
configAlgorithm :: LayoutConfig -> LayoutAlgorithm
configAlgorithm c = c.algorithm

-- | Get orientation
configOrientation :: LayoutConfig -> LayoutOrientation
configOrientation c = c.orientation

-- | Get spacing
configSpacing :: LayoutConfig -> LayoutSpacing
configSpacing c = c.spacing

-- | Get sizing
configSizing :: LayoutConfig -> NodeSizing
configSizing c = c.sizing

-- | Get constraints
configConstraints :: LayoutConfig -> LayoutConstraints
configConstraints c = c.constraints

-- | Get treemap params if present
configTreemapParams :: LayoutConfig -> Maybe TreemapParams
configTreemapParams c = c.treemapParams

-- | Get radial params if present
configRadialParams :: LayoutConfig -> Maybe RadialParams
configRadialParams c = c.radialParams

-- | Get force params if present
configForceParams :: LayoutConfig -> Maybe ForceParams
configForceParams c = c.forceParams
