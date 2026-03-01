-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // tag-input // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput Types — Core type definitions for tag input component.
-- |
-- | This module contains the Tag type and constructors.

module Hydrogen.Element.Compound.TagInput.Types
  ( -- * Tag Types
    Tag
  , mkTag
  , tagWithLabel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tag types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A tag with value, label, and removable flag
type Tag =
  { value :: String
  , label :: String
  , removable :: Boolean
  }

-- | Create a simple tag from a string
mkTag :: String -> Tag
mkTag s = { value: s, label: s, removable: true }

-- | Create a tag with custom label
tagWithLabel :: String -> String -> Tag
tagWithLabel val lbl = { value: val, label: lbl, removable: true }
