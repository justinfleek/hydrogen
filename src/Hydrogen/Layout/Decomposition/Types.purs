-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // layout // decomposition // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for layout decomposition.
-- |
-- | This module provides the fundamental identifiers and constraint types
-- | used throughout the decomposition system.
-- |
-- | ## Lean Correspondence
-- |
-- | These types correspond to the core definitions in:
-- | `proofs/Hydrogen/Layout/Decomposition.lean`

module Hydrogen.Layout.Decomposition.Types
  ( -- * Identifiers
    ElementId
  , ViewportId
  
  -- * Constraint Types
  , ConstraintType(..)
  , constraintPriority
  
  -- * Constraint Edge
  , ConstraintEdge
  , mkConstraintEdge
  , edgeSource
  , edgeTarget
  , edgeType
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // identifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for layout elements.
type ElementId = String

-- | Unique identifier for viewports.
type ViewportId = String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // constraint types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of constraints between layout elements.
-- |
-- | Each constraint type corresponds to a linear constraint in the ILP.
-- |
-- | ## Lean Correspondence
-- |
-- | These constraint types generate edges in the `ConstraintGraph` structure
-- | defined in `proofs/Hydrogen/Layout/Decomposition.lean`.
data ConstraintType
  = GapConstraint Int              -- ^ x_j >= x_i + w_i + gap
  | AlignStart                     -- ^ x_i = x_j
  | AlignCenter                    -- ^ x_i + w_i/2 = x_j + w_j/2
  | AlignEnd                       -- ^ x_i + w_i = x_j + w_j
  | RelativeSize Number            -- ^ w_i = alpha * w_j
  | MinSpacing Int                 -- ^ x_j - (x_i + w_i) >= delta
  | MaxSpacing Int                 -- ^ x_j - (x_i + w_i) <= delta
  | EqualWidth                     -- ^ w_i = w_j
  | AspectRatio Number             -- ^ w_i = ratio * h_i

derive instance eqConstraintType :: Eq ConstraintType

instance showConstraintType :: Show ConstraintType where
  show (GapConstraint g) = "Gap(" <> show g <> ")"
  show AlignStart = "AlignStart"
  show AlignCenter = "AlignCenter"
  show AlignEnd = "AlignEnd"
  show (RelativeSize r) = "RelativeSize(" <> show r <> ")"
  show (MinSpacing s) = "MinSpacing(" <> show s <> ")"
  show (MaxSpacing s) = "MaxSpacing(" <> show s <> ")"
  show EqualWidth = "EqualWidth"
  show (AspectRatio r) = "AspectRatio(" <> show r <> ")"

-- | Priority of a constraint (higher = more important to satisfy first).
constraintPriority :: ConstraintType -> Int
constraintPriority (GapConstraint _) = 1
constraintPriority AlignStart = 2
constraintPriority AlignCenter = 2
constraintPriority AlignEnd = 2
constraintPriority (RelativeSize _) = 1
constraintPriority (MinSpacing _) = 1
constraintPriority (MaxSpacing _) = 1
constraintPriority EqualWidth = 1
constraintPriority (AspectRatio _) = 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constraint edge
-- ═════════════════════════════════════════════════════════════════════════════

-- | An edge in the constraint graph.
-- |
-- | Represents a constraint between two elements.
-- |
-- | ## Lean Correspondence
-- |
-- | This corresponds to an element of the `edges` field in `ConstraintGraph`.
type ConstraintEdge =
  { source :: ElementId
  , target :: ElementId
  , constraint :: ConstraintType
  , priority :: Int
  }

-- | Create a constraint edge.
mkConstraintEdge :: ElementId -> ElementId -> ConstraintType -> ConstraintEdge
mkConstraintEdge src tgt ctype =
  { source: src
  , target: tgt
  , constraint: ctype
  , priority: constraintPriority ctype
  }

-- | Get the source element of an edge.
edgeSource :: ConstraintEdge -> ElementId
edgeSource e = e.source

-- | Get the target element of an edge.
edgeTarget :: ConstraintEdge -> ElementId
edgeTarget e = e.target

-- | Get the constraint type of an edge.
edgeType :: ConstraintEdge -> ConstraintType
edgeType e = e.constraint
