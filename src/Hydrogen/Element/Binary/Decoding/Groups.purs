-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // binary // decoding // groups
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Group/Transform Decoding
-- |
-- | Deserialize Group and Transform elements from binary format.
-- | Note: This module imports the main Decoding module for recursive
-- | element deserialization.

module Hydrogen.Element.Binary.Decoding.Groups
  ( -- * Group
    deserializeGroup
  , deserializeElements
  
  -- * Transform
  , deserializeTransformElem
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , pure
  , ($)
  , (+)
  , (-)
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Binary.Types (DeserializeResult)
import Hydrogen.Element.Binary.Primitives (readU32)

import Hydrogen.Element.Binary.Decoding.Common (deserializeOpacity)
import Hydrogen.Element.Binary.Decoding.Text (deserializeTransform2D)

import Hydrogen.Element.Core
  ( Element(Group, Transform)
  , GroupSpec
  , TransformSpec
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // group deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Group at offset
-- | Note: This function needs the element deserializer passed in to avoid
-- | circular dependencies.
deserializeGroup 
  :: (Array Int -> Int -> Maybe (DeserializeResult Element))
  -> Array Int 
  -> Int 
  -> Maybe (DeserializeResult Element)
deserializeGroup deserializeElementAt arr offset = do
  -- Child count (4 bytes)
  count <- readU32 arr offset
  
  -- Children (variable)
  childrenResult <- deserializeElements deserializeElementAt arr (offset + 4) count
  let childrenEnd = offset + 4 + childrenResult.bytesRead
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr childrenEnd
  
  let spec :: GroupSpec
      spec = 
        { children: childrenResult.value
        , opacity: opacity
        }
  
  Just { value: Group spec, bytesRead: childrenEnd + 4 - offset }

-- | Deserialize array of Elements
deserializeElements 
  :: (Array Int -> Int -> Maybe (DeserializeResult Element))
  -> Array Int 
  -> Int 
  -> Int 
  -> Maybe (DeserializeResult (Array Element))
deserializeElements deserializeElementAt arr offset count =
  deserializeElementsLoop deserializeElementAt arr offset count []

-- | Helper for deserializing elements
deserializeElementsLoop 
  :: (Array Int -> Int -> Maybe (DeserializeResult Element))
  -> Array Int 
  -> Int 
  -> Int 
  -> Array Element 
  -> Maybe (DeserializeResult (Array Element))
deserializeElementsLoop deserializeElementAt arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      elemResult <- deserializeElementAt arr offset
      restResult <- deserializeElementsLoop deserializeElementAt arr (offset + elemResult.bytesRead) (remaining - 1) (acc <> [elemResult.value])
      Just { value: restResult.value, bytesRead: elemResult.bytesRead + restResult.bytesRead }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // transform deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Transform at offset
deserializeTransformElem 
  :: (Array Int -> Int -> Maybe (DeserializeResult Element))
  -> Array Int 
  -> Int 
  -> Maybe (DeserializeResult Element)
deserializeTransformElem deserializeElementAt arr offset = do
  -- Transform2D (36 bytes)
  transform <- deserializeTransform2D arr offset
  
  -- Child element (variable)
  childResult <- deserializeElementAt arr (offset + 36)
  
  let spec :: TransformSpec
      spec = 
        { transform: transform
        , child: childResult.value
        }
  
  Just { value: Transform spec, bytesRead: 36 + childResult.bytesRead }
