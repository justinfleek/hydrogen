-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // viewport // responsive
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Responsive value system for breakpoint-aware values.
-- |
-- | This module provides types and functions for values that change
-- | based on the current breakpoint. Values cascade up — if a breakpoint
-- | is not specified, it inherits from the previous smaller breakpoint.

module Hydrogen.Schema.Reactive.Viewport.Responsive
  ( -- * ResponsiveValue
    ResponsiveSpec
  , ResponsiveValue
  , responsive
  , static
  , resolve
  , resolveFor
  ) where

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Viewport.Types
  ( Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  )
import Hydrogen.Schema.Reactive.Viewport.Core (Viewport)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // responsive value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for responsive values.
-- |
-- | `base` is required (used for Xs and as fallback).
-- | Other breakpoints are optional — Nothing means "inherit from smaller".
type ResponsiveSpec a =
  { base :: a           -- ^ Value at Xs (required)
  , sm :: Maybe a       -- ^ Value at Sm (optional)
  , md :: Maybe a       -- ^ Value at Md (optional)
  , lg :: Maybe a       -- ^ Value at Lg (optional)
  , xl :: Maybe a       -- ^ Value at Xl (optional)
  , xxl :: Maybe a      -- ^ Value at Xxl (optional)
  }

-- | A value that changes at different breakpoints.
-- |
-- | Stores resolved value at each breakpoint.
type ResponsiveValue a =
  { xs :: a
  , sm :: a
  , md :: a
  , lg :: a
  , xl :: a
  , xxl :: a
  }

-- | Create a responsive value from a spec.
-- |
-- | Values cascade up — if a breakpoint is Nothing, it inherits
-- | from the previous smaller breakpoint.
responsive :: forall a. ResponsiveSpec a -> ResponsiveValue a
responsive spec =
  let
    xs = spec.base
    sm = resolveOr xs spec.sm
    md = resolveOr sm spec.md
    lg = resolveOr md spec.lg
    xl = resolveOr lg spec.xl
    xxl = resolveOr xl spec.xxl
  in
    { xs: xs, sm: sm, md: md, lg: lg, xl: xl, xxl: xxl }

-- | Helper: resolve Maybe with fallback.
resolveOr :: forall a. a -> Maybe a -> a
resolveOr fallback maybeVal = case maybeVal of
  Nothing -> fallback
  Just v -> v

-- | Create a static value (same at all breakpoints).
static :: forall a. a -> ResponsiveValue a
static a = { xs: a, sm: a, md: a, lg: a, xl: a, xxl: a }

-- | Resolve a responsive value at a specific breakpoint.
resolve :: forall a. ResponsiveValue a -> Breakpoint -> a
resolve rv Xs = rv.xs
resolve rv Sm = rv.sm
resolve rv Md = rv.md
resolve rv Lg = rv.lg
resolve rv Xl = rv.xl
resolve rv Xxl = rv.xxl

-- | Resolve a responsive value for a viewport.
resolveFor :: forall a. ResponsiveValue a -> Viewport -> a
resolveFor rv vp = resolve rv vp.breakpoint
