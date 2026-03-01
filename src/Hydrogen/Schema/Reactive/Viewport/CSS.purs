-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // reactive // viewport // css
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS generation utilities for responsive design.
-- |
-- | This module provides functions for generating CSS media queries,
-- | container queries, and Tailwind-style breakpoint class prefixes.

module Hydrogen.Schema.Reactive.Viewport.CSS
  ( -- * CSS Generation
    mediaQuery
  , mediaQueryMax
  , mediaQueryRange
  , containerQueryCss
  , breakpointClass
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Viewport.Types
  ( Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  )
import Hydrogen.Schema.Reactive.Viewport.Breakpoints
  ( breakpointMin
  , breakpointMax
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate CSS media query for breakpoint (min-width).
-- |
-- | ```purescript
-- | mediaQuery Lg  -- "@media (min-width: 1024px)"
-- | mediaQuery Xs  -- "" (no media query for base)
-- | ```
mediaQuery :: Breakpoint -> String
mediaQuery Xs = ""
mediaQuery bp = "@media (min-width: " <> show (breakpointMin bp) <> "px)"

-- | Generate CSS media query with max-width.
mediaQueryMax :: Breakpoint -> String
mediaQueryMax bp = case breakpointMax bp of
  Nothing -> ""
  Just maxPx -> "@media (max-width: " <> show maxPx <> "px)"

-- | Generate CSS media query for exact breakpoint range.
mediaQueryRange :: Breakpoint -> String
mediaQueryRange bp =
  let minPx = breakpointMin bp
  in case breakpointMax bp of
    Nothing -> "@media (min-width: " <> show minPx <> "px)"
    Just maxPx -> "@media (min-width: " <> show minPx <> "px) and (max-width: " <> show maxPx <> "px)"

-- | Generate CSS container query string.
-- |
-- | Responds to parent element size, not viewport.
-- | For full container query support, see ContainerQuery module.
containerQueryCss :: Breakpoint -> String
containerQueryCss Xs = ""
containerQueryCss bp = "@container (min-width: " <> show (breakpointMin bp) <> "px)"

-- | Get Tailwind-style class prefix for breakpoint.
-- |
-- | ```purescript
-- | breakpointClass Lg "grid-cols-4"  -- "lg:grid-cols-4"
-- | breakpointClass Xs "grid-cols-1"  -- "grid-cols-1"
-- | ```
breakpointClass :: Breakpoint -> String -> String
breakpointClass Xs cls = cls
breakpointClass bp cls = show bp <> ":" <> cls
