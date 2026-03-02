-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // types // objectid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas ObjectId — Unique identifier for canvas objects.
-- |
-- | ## Design Note
-- |
-- | This type is split into its own module to break circular dependencies.
-- | Both Core (for SelectionState) and Object (for CanvasObject) need this type.

module Hydrogen.Element.Compound.Canvas.Types.ObjectId
  ( CanvasObjectId(CanvasObjectId)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // object id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for canvas objects.
newtype CanvasObjectId = CanvasObjectId String

derive instance eqCanvasObjectId :: Eq CanvasObjectId
derive instance ordCanvasObjectId :: Ord CanvasObjectId

instance showCanvasObjectId :: Show CanvasObjectId where
  show (CanvasObjectId id) = "ObjectId(" <> id <> ")"
