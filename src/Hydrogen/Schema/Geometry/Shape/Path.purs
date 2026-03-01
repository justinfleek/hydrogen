-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // shape // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path — Generic path shape constructed from path commands.
-- |
-- | Paths are the most flexible shape primitive, capable of representing
-- | any arbitrary 2D shape through a sequence of drawing commands.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (comparison)
-- | - Data.Array (length)
-- | - Shape.Types (PathCommand, WindingRule)

module Hydrogen.Schema.Geometry.Shape.Path
  ( -- * Path
    PathShape
  , pathShape
  , closedPath
  , openPath
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (>)
  )

import Data.Array (length) as Array

import Hydrogen.Schema.Geometry.Shape.Types (PathCommand, WindingRule(WindingNonZero))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic path shape defined by commands
type PathShape =
  { commands :: Array PathCommand
  , windingRule :: WindingRule
  , closed :: Boolean
  }

-- | Create a path shape from commands
pathShape :: Array PathCommand -> WindingRule -> PathShape
pathShape commands windingRule =
  { commands
  , windingRule
  , closed: Array.length commands > 0
  }

-- | Create a closed path
closedPath :: Array PathCommand -> PathShape
closedPath commands =
  { commands
  , windingRule: WindingNonZero
  , closed: true
  }

-- | Create an open path
openPath :: Array PathCommand -> PathShape
openPath commands =
  { commands
  , windingRule: WindingNonZero
  , closed: false
  }
