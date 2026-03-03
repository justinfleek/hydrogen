-- | Loading state UI components
-- |
-- | Provides consistent loading indicators and skeleton loaders:
-- | - Spinners (various sizes)
-- | - Loading cards (skeleton placeholders)
-- | - Loading messages
-- | - Inline loading indicators
module Hydrogen.UI.Loading
  ( -- * Spinners
    spinner
  , spinnerSm
  , spinnerMd
  , spinnerLg
    -- * Loading states
  , loadingState
  , loadingInline
    -- * Skeleton loaders
  , loadingCard
  , loadingCardLarge
  , skeletonText
  , skeletonRow
  ) where

import Prelude

import Data.Array (range)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ============================================================
-- SPINNERS
-- ============================================================

-- | Animated loading spinner with configurable size
-- |
-- | ```purescript
-- | spinner "w-8 h-8"  -- 32x32 spinner
-- | spinner "w-4 h-4"  -- 16x16 spinner
-- | ```
spinner :: forall w i. String -> HH.HTML w i
spinner size =
  HH.div
    [ cls [ size, "animate-spin rounded-full border-2 border-muted-foreground border-t-primary" ] ]
    []

-- | Small inline spinner (16x16)
spinnerSm :: forall w i. HH.HTML w i
spinnerSm = spinner "w-4 h-4"

-- | Medium spinner (24x24)
spinnerMd :: forall w i. HH.HTML w i
spinnerMd = spinner "w-6 h-6"

-- | Large spinner (32x32)
spinnerLg :: forall w i. HH.HTML w i
spinnerLg = spinner "w-8 h-8"

-- ============================================================
-- LOADING STATES
-- ============================================================

-- | Centered loading state with spinner and message
-- |
-- | ```purescript
-- | loadingState "Loading your data..."
-- | ```
loadingState :: forall w i. String -> HH.HTML w i
loadingState message =
  HH.div
    [ cls [ "flex flex-col items-center justify-center py-12 text-muted-foreground" ] ]
    [ spinnerLg
    , HH.p
        [ cls [ "mt-4 text-sm" ] ]
        [ HH.text message ]
    ]

-- | Inline loading indicator with spinner and "Loading..." text
-- |
-- | Useful for inline sections or buttons
loadingInline :: forall w i. HH.HTML w i
loadingInline =
  HH.div
    [ cls [ "flex items-center gap-2 text-muted-foreground" ] ]
    [ spinnerSm
    , HH.span [ cls [ "text-sm" ] ] [ HH.text "Loading..." ]
    ]

-- ============================================================
-- SKELETON LOADERS
-- ============================================================

-- | Loading placeholder card (matches typical stat card dimensions)
-- |
-- | Shows animated pulse effect while content loads
loadingCard :: forall w i. HH.HTML w i
loadingCard =
  HH.div
    [ cls [ "bg-card border border-border rounded-lg p-4 animate-pulse" ] ]
    [ HH.div [ cls [ "h-4 w-24 bg-muted rounded mb-2" ] ] []
    , HH.div [ cls [ "h-8 w-16 bg-muted rounded mb-1" ] ] []
    , HH.div [ cls [ "h-3 w-20 bg-muted rounded" ] ] []
    ]

-- | Loading placeholder for larger content cards
loadingCardLarge :: forall w i. HH.HTML w i
loadingCardLarge =
  HH.div
    [ cls [ "bg-card border border-border rounded-lg p-6 animate-pulse" ] ]
    [ HH.div [ cls [ "h-5 w-32 bg-muted rounded mb-4" ] ] []
    , HH.div [ cls [ "space-y-3" ] ]
        [ HH.div [ cls [ "h-4 w-full bg-muted rounded" ] ] []
        , HH.div [ cls [ "h-4 w-3/4 bg-muted rounded" ] ] []
        , HH.div [ cls [ "h-4 w-1/2 bg-muted rounded" ] ] []
        ]
    ]

-- | Skeleton pulse effect for text line
-- |
-- | ```purescript
-- | skeletonText "w-32"  -- 128px wide text placeholder
-- | skeletonText "w-full"  -- Full width
-- | ```
skeletonText :: forall w i. String -> HH.HTML w i
skeletonText width =
  HH.div
    [ cls [ "h-4 bg-muted rounded animate-pulse", width ] ]
    []

-- | Skeleton for a table row with specified number of columns
-- |
-- | ```purescript
-- | skeletonRow 4  -- Row with 4 column placeholders
-- | ```
skeletonRow :: forall w i. Int -> HH.HTML w i
skeletonRow cols =
  HH.div
    [ cls [ "flex items-center gap-4 p-4 border-b border-border animate-pulse" ] ]
    (map (\_ -> HH.div [ cls [ "h-4 flex-1 bg-muted rounded" ] ] []) (range 1 cols))
