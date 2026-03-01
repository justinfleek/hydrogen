-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // flatten // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for the Element → DrawCommand flattening process.
-- |
-- | ## Purpose
-- |
-- | Defines the state and result types used during flattening.
-- | Separated to avoid circular dependencies between flattening modules.
-- |
-- | ## Types
-- |
-- | - `FlattenState`: Accumulator threaded through flattening
-- | - `FlattenResult`: Output of flattening a single element

module Hydrogen.Element.Flatten.Types
  ( FlattenState
  , FlattenResult
  , initialState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.DrawCommand (DrawCommand)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of flattening an Element tree.
-- |
-- | Contains the array of GPU commands and the updated state (for chaining).
type FlattenResult msg =
  { commands :: Array (DrawCommand msg)
  , state :: FlattenState
  }

-- | State maintained during flattening.
-- |
-- | ## Fields
-- |
-- | - `nextPickId`: Counter for generating unique pick IDs for hit testing.
-- |   Each interactive element gets a unique ID, enabling pixel → agent mapping.
-- |
-- | - `depth`: Current depth for z-ordering. Incremented for each element
-- |   to ensure proper layering without explicit z-index management.
type FlattenState =
  { nextPickId :: Int
  , depth :: Number
  }

-- | Initial flattening state.
-- |
-- | Start with pickId 1 (0 is reserved for "no element") and depth 0.
initialState :: FlattenState
initialState =
  { nextPickId: 1
  , depth: 0.0
  }
