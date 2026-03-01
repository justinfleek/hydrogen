-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // table // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Pagination — Helper functions for pagination state and display.
-- |
-- | ## Overview
-- |
-- | This module provides utilities for working with pagination:
-- | - Calculating total pages from item counts
-- | - Navigation predicates (hasNextPage, hasPrevPage)
-- | - Page range generation for UI display

module Hydrogen.Element.Compound.Widget.Table.Pagination
  ( -- * Pagination Helpers
    totalPages
  , hasNextPage
  , hasPrevPage
  , pageRange
  , range
  ) where

import Prelude
  ( otherwise
  , (+)
  , (-)
  , (/)
  , (*)
  , (<)
  , (>)
  , (<=)
  , (<>)
  )


import Hydrogen.Element.Compound.Widget.Table.Types (Pagination)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // pagination helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total pages from item count and page size.
totalPages :: Int -> Int -> Int
totalPages itemCount pageSize =
  if pageSize <= 0
    then 0
    else 
      let full = itemCount / pageSize
          remainder = itemCount - (full * pageSize)
      in if remainder > 0 then full + 1 else full

-- | Check if there's a next page.
hasNextPage :: Pagination -> Boolean
hasNextPage p = p.page < p.totalPages

-- | Check if there's a previous page.
hasPrevPage :: Pagination -> Boolean
hasPrevPage p = p.page > 1

-- | Get page range for pagination display.
-- |
-- | Returns array of page numbers to display, with -1 for ellipsis.
pageRange :: Pagination -> Int -> Array Int
pageRange p maxVisible =
  let
    total = p.totalPages
    current = p.page
    half = maxVisible / 2
    
    start = if current - half < 1 then 1 else current - half
    end = if start + maxVisible - 1 > total then total else start + maxVisible - 1
    adjustedStart = if end - start + 1 < maxVisible
                      then if start > 1
                             then if end - maxVisible + 1 < 1 then 1 else end - maxVisible + 1
                             else start
                      else start
  in
    range adjustedStart end

-- | Generate integer range.
range :: Int -> Int -> Array Int
range start end = range' start end []
  where
    range' :: Int -> Int -> Array Int -> Array Int
    range' s e acc
      | s > e = acc
      | otherwise = range' (s + 1) e (acc <> [s])
