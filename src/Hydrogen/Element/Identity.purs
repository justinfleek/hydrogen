-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deterministic Element Identity via UUID5.
-- |
-- | This is the critical integration layer that makes Elements content-addressed:
-- |
-- | Same Element content → Same binary serialization → Same UUID5
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, agents need to reference Elements deterministically:
-- | - Agent A creates a button with certain visual properties
-- | - Agent B creates the same button independently
-- | - Both get the SAME UUID5 — enabling coordination without communication
-- |
-- | ## Implementation
-- |
-- | Element → Binary Serialization → SHA-256 → UUID5
-- |
-- | The serialization is deterministic (same Element → same bytes).
-- | UUID5 uses SHA-256 under the hood (stronger than RFC 4122's SHA-1).
-- | Namespace is `nsElement` from Hydrogen.Schema.Attestation.UUID5.

module Hydrogen.Element.Identity
  ( -- * UUID5 Generation
    elementUUID5
  , elementUUID5String
  
  -- * Identified Elements
  , IdentifiedElement
  , identifyElement
  , identifyElementWithGen
  
  -- * Accessors
  , elementId
  , elementGeneration
  , unwrapIdentified
  
  -- * Comparison
  , sameElement
  , sameContent
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , ($)
  , (==)
  , (<>)
  )

import Hydrogen.Element.Core (Element)
import Hydrogen.Element.Binary.Encoding (serialize)
import Hydrogen.Element.Binary.Primitives (toByteArray)
import Hydrogen.Schema.Attestation.UUID5 (UUID5, uuid5Bytes, toString, nsElement)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 from Element content.
-- |
-- | This is THE function for content-addressed element identity.
-- | Same visual properties → same bytes → same UUID5.
-- |
-- | ```purescript
-- | rect1 = Rectangle { ... }
-- | rect2 = Rectangle { ... }  -- identical properties
-- | 
-- | elementUUID5 rect1 == elementUUID5 rect2  -- Always true
-- | ```
elementUUID5 :: Element -> UUID5
elementUUID5 elem =
  let
    -- Serialize to deterministic binary
    bytes = serialize elem
    -- Convert to Int array for UUID5
    intArray = toByteArray bytes
  in
    -- Generate UUID5 using element namespace
    uuid5Bytes nsElement intArray

-- | Generate UUID5 as string (36-char format with dashes)
-- |
-- | Example: "550e8400-e29b-51d4-a716-446655440000"
elementUUID5String :: Element -> String
elementUUID5String elem = toString (elementUUID5 elem)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // identified element
-- ═════════════════════════════════════════════════════════════════════════════

-- | An Element wrapped with its deterministic identity and generation counter.
-- |
-- | The generation counter enables cache invalidation:
-- | - Same UUID5 = same visual content
-- | - Different generation = newer version (even if content unchanged)
type IdentifiedElement =
  { uuid :: UUID5
  , generation :: Int
  , element :: Element
  }

-- | Wrap an Element with its deterministic identity.
-- |
-- | Generation defaults to 0 (first version).
identifyElement :: Element -> IdentifiedElement
identifyElement elem =
  { uuid: elementUUID5 elem
  , generation: 0
  , element: elem
  }

-- | Wrap an Element with identity and explicit generation counter.
-- |
-- | Use this when updating an existing element to increment generation.
identifyElementWithGen :: Int -> Element -> IdentifiedElement
identifyElementWithGen gen elem =
  { uuid: elementUUID5 elem
  , generation: gen
  , element: elem
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the UUID5 identifier
elementId :: IdentifiedElement -> UUID5
elementId ie = ie.uuid

-- | Get the generation counter
elementGeneration :: IdentifiedElement -> Int
elementGeneration ie = ie.generation

-- | Unwrap to get the raw Element
unwrapIdentified :: IdentifiedElement -> Element
unwrapIdentified ie = ie.element

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two identified elements have the same identity (UUID5).
-- |
-- | Same UUID5 means same visual content (deterministic).
sameElement :: IdentifiedElement -> IdentifiedElement -> Boolean
sameElement a b = a.uuid == b.uuid

-- | Check if two identified elements have the same content.
-- |
-- | Same as sameElement — both check UUID5 equality.
sameContent :: IdentifiedElement -> IdentifiedElement -> Boolean
sameContent = sameElement
