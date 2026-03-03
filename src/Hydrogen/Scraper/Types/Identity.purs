-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // scraper // types // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Identity types for deterministic element identification.
-- |
-- | Every extracted element gets a UUID5 derived from its content.
-- | This enables:
-- | - Deterministic identity across scrapes
-- | - Content-addressable caching
-- | - Change detection
-- | - AI training data deduplication
-- |
-- | ## UUID5 Namespace
-- |
-- | All element UUIDs use namespace: "hydrogen.scraper.element"
-- | uuid5(namespace, serialize(element)) → deterministic UUID

module Hydrogen.Scraper.Types.Identity
  ( -- * Types
    ElementId
  , ContentHash
  , ElementIdentity
  
  -- * Constructors
  , elementId
  , contentHash
  , emptyIdentity
  
  -- * Accessors
  , unwrapElementId
  , unwrapContentHash
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // element id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Deterministic element identifier (UUID5)
-- |
-- | Generated from element content, not random.
-- | Same element content → same UUID5 → same identity.
newtype ElementId = ElementId String

derive instance eqElementId :: Eq ElementId
derive instance ordElementId :: Ord ElementId

instance showElementId :: Show ElementId where
  show (ElementId id) = "ElementId(" <> id <> ")"

-- | Create an element ID
elementId :: String -> ElementId
elementId = ElementId

-- | Extract raw string
unwrapElementId :: ElementId -> String
unwrapElementId (ElementId id) = id

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // content hash
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SHA256 hash of visual content
-- |
-- | Used for image/SVG content deduplication.
newtype ContentHash = ContentHash String

derive instance eqContentHash :: Eq ContentHash
derive instance ordContentHash :: Ord ContentHash

instance showContentHash :: Show ContentHash where
  show (ContentHash h) = "ContentHash(" <> h <> ")"

-- | Create a content hash
contentHash :: String -> ContentHash
contentHash = ContentHash

-- | Extract raw string
unwrapContentHash :: ContentHash -> String
unwrapContentHash (ContentHash h) = h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // element identity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete identity for an extracted element
type ElementIdentity =
  { -- Deterministic UUID5
    uuid :: ElementId
  
  -- DOM path for debugging (not part of identity)
  , domPath :: String  -- ^ e.g., "html > body > div.container > button.primary"
  
  -- Content hashes for assets
  , imageHash :: Maybe ContentHash
  , svgHash :: Maybe ContentHash
  
  -- Semantic role (from ARIA or implicit)
  , role :: Maybe String
  
  -- Accessible name
  , accessibleName :: Maybe String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty identity (placeholder)
emptyIdentity :: ElementIdentity
emptyIdentity =
  { uuid: ElementId ""
  , domPath: ""
  , imageHash: Nothing
  , svgHash: Nothing
  , role: Nothing
  , accessibleName: Nothing
  }
