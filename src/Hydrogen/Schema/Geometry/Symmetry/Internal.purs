-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // symmetry // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helpers for Symmetry module.
-- |
-- | This module contains shared utility functions used across the Symmetry
-- | submodules. Not intended for direct use by consumers.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Maybe (Maybe)

module Hydrogen.Schema.Geometry.Symmetry.Internal
  ( intToNumber
  , absNumber
  , showMaybe
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , negate
  , (<>)
  , (+)
  , (-)
  , (<)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Helper: convert Int to Number
intToNumber :: Int -> Number
intToNumber n = toNumber n
  where
    -- This is a workaround since we don't have direct Int -> Number
    toNumber :: Int -> Number
    toNumber i = case i of
      0 -> 0.0
      1 -> 1.0
      2 -> 2.0
      3 -> 3.0
      4 -> 4.0
      5 -> 5.0
      6 -> 6.0
      7 -> 7.0
      8 -> 8.0
      _ -> 1.0 + toNumber (i - 1)

-- | Helper: absolute value for Number
absNumber :: Number -> Number
absNumber n = if n < 0.0 then negate n else n

-- | Helper: show Maybe
showMaybe :: forall a. Show a => Maybe a -> String
showMaybe Nothing = "Nothing"
showMaybe (Just a) = "Just " <> show a
