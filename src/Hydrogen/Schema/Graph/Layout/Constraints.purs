-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // graph // layout // constraints
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layout Constraints — Bounds and constraints for layout algorithms.
-- |
-- | ## Contents
-- |
-- | - LayoutBounds: Optional width/height constraints
-- | - LayoutConstraints: Full constraint specification
-- | - NodePosition: Computed position result for a node
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe

module Hydrogen.Schema.Graph.Layout.Constraints
  ( -- * Layout Bounds
    LayoutBounds
  , layoutBounds
  , unbounded
  , boundsWidth
  , boundsHeight
  , hasBounds
  
  -- * Layout Constraints
  , LayoutConstraints
  , layoutConstraints
  , defaultConstraints
  , withBounds
  , withMinNodeSize
  , withMaxNodeSize
  , withAspectRatio
  
  -- * Node Position (Layout Result)
  , NodePosition
  , nodePosition
  , positionX
  , positionY
  , positionWidth
  , positionHeight
  , positionRotation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (||)
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding box for layout
type LayoutBounds =
  { width :: Maybe Number
  , height :: Maybe Number
  }

-- | Create bounded layout
layoutBounds :: Number -> Number -> LayoutBounds
layoutBounds w h = { width: Just w, height: Just h }

-- | Unbounded layout (grow to fit)
unbounded :: LayoutBounds
unbounded = { width: Nothing, height: Nothing }

-- | Get width if bounded
boundsWidth :: LayoutBounds -> Maybe Number
boundsWidth b = b.width

-- | Get height if bounded
boundsHeight :: LayoutBounds -> Maybe Number
boundsHeight b = b.height

-- | Check if bounds are specified
hasBounds :: LayoutBounds -> Boolean
hasBounds b = isJust b.width || isJust b.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layout constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints for layout algorithm
type LayoutConstraints =
  { bounds :: LayoutBounds
  , minNodeWidth :: Number
  , minNodeHeight :: Number
  , maxNodeWidth :: Maybe Number
  , maxNodeHeight :: Maybe Number
  , aspectRatio :: Maybe Number
  }

-- | Create layout constraints
layoutConstraints :: LayoutBounds -> Number -> Number -> LayoutConstraints
layoutConstraints bounds minW minH =
  { bounds
  , minNodeWidth: minW
  , minNodeHeight: minH
  , maxNodeWidth: Nothing
  , maxNodeHeight: Nothing
  , aspectRatio: Nothing
  }

-- | Default constraints
defaultConstraints :: LayoutConstraints
defaultConstraints = layoutConstraints unbounded 50.0 24.0

-- | Set bounds
withBounds :: LayoutBounds -> LayoutConstraints -> LayoutConstraints
withBounds b c = c { bounds = b }

-- | Set minimum node size
withMinNodeSize :: Number -> Number -> LayoutConstraints -> LayoutConstraints
withMinNodeSize w h c = c { minNodeWidth = w, minNodeHeight = h }

-- | Set maximum node size
withMaxNodeSize :: Number -> Number -> LayoutConstraints -> LayoutConstraints
withMaxNodeSize w h c = c { maxNodeWidth = Just w, maxNodeHeight = Just h }

-- | Set aspect ratio constraint
withAspectRatio :: Number -> LayoutConstraints -> LayoutConstraints
withAspectRatio r c = c { aspectRatio = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // node position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Computed position and size for a node
type NodePosition =
  { x :: Number       -- ^ X coordinate (center or left, depends on layout)
  , y :: Number       -- ^ Y coordinate (center or top)
  , width :: Number   -- ^ Computed width
  , height :: Number  -- ^ Computed height
  , rotation :: Number  -- ^ Rotation in degrees (for radial)
  }

-- | Create node position
nodePosition :: Number -> Number -> Number -> Number -> NodePosition
nodePosition x y w h =
  { x, y, width: w, height: h, rotation: 0.0 }

-- | Get X coordinate
positionX :: NodePosition -> Number
positionX p = p.x

-- | Get Y coordinate
positionY :: NodePosition -> Number
positionY p = p.y

-- | Get computed width
positionWidth :: NodePosition -> Number
positionWidth p = p.width

-- | Get computed height
positionHeight :: NodePosition -> Number
positionHeight p = p.height

-- | Get rotation
positionRotation :: NodePosition -> Number
positionRotation p = p.rotation
