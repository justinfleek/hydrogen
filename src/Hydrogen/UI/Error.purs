-- | Error state UI components
-- |
-- | Provides consistent error display:
-- | - Full-page error states
-- | - Error cards
-- | - Inline error badges
-- | - Empty states (no data)
module Hydrogen.UI.Error
  ( -- * Error displays
    errorState
  , errorCard
  , errorBadge
  , errorInline
    -- * Empty states
  , emptyState
  ) where

import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ============================================================
-- ERROR STATES
-- ============================================================

-- | Full error state with icon and message
-- |
-- | Centered display for when a major section fails to load
-- |
-- | ```purescript
-- | case data of
-- |   Failure err -> errorState err
-- |   ...
-- | ```
errorState :: forall w i. String -> HH.HTML w i
errorState message =
  HH.div
    [ cls [ "flex flex-col items-center justify-center py-12" ] ]
    [ HH.div
        [ cls [ "w-12 h-12 rounded-full bg-destructive/20 flex items-center justify-center mb-4" ] ]
        [ HH.span [ cls [ "text-destructive text-xl" ] ] [ HH.text "!" ] ]
    , HH.p
        [ cls [ "text-destructive text-sm font-medium mb-2" ] ]
        [ HH.text "Failed to load" ]
    , HH.p
        [ cls [ "text-muted-foreground text-sm text-center max-w-sm" ] ]
        [ HH.text message ]
    ]

-- | Error card (matches card dimensions)
-- |
-- | For showing errors in card-based layouts
-- |
-- | ```purescript
-- | errorCard "Unable to fetch statistics"
-- | ```
errorCard :: forall w i. String -> HH.HTML w i
errorCard message =
  HH.div
    [ cls [ "bg-card border border-destructive/30 rounded-lg p-4" ] ]
    [ HH.div
        [ cls [ "flex items-center gap-2 text-destructive mb-1" ] ]
        [ HH.span [ cls [ "text-sm" ] ] [ HH.text "!" ]
        , HH.span [ cls [ "text-sm font-medium" ] ] [ HH.text "Error" ]
        ]
    , HH.p
        [ cls [ "text-xs text-muted-foreground" ] ]
        [ HH.text message ]
    ]

-- | Inline error badge
-- |
-- | For showing errors inline with other content
-- |
-- | ```purescript
-- | errorBadge "Invalid input"
-- | ```
errorBadge :: forall w i. String -> HH.HTML w i
errorBadge message =
  HH.div
    [ cls [ "flex items-center gap-2 px-3 py-2 bg-destructive/10 border border-destructive/30 rounded-md" ] ]
    [ HH.span [ cls [ "text-destructive text-sm" ] ] [ HH.text "Error:" ]
    , HH.span [ cls [ "text-destructive/80 text-sm" ] ] [ HH.text message ]
    ]

-- | Simple inline error text
-- |
-- | Minimal error display for forms or small sections
-- |
-- | ```purescript
-- | errorInline "This field is required"
-- | ```
errorInline :: forall w i. String -> HH.HTML w i
errorInline message =
  HH.p
    [ cls [ "text-destructive text-sm" ] ]
    [ HH.text message ]

-- ============================================================
-- EMPTY STATES
-- ============================================================

-- | Empty state for when data loads but is empty
-- |
-- | ```purescript
-- | emptyState "No items yet" "Create your first item to get started"
-- | ```
emptyState :: forall w i. String -> String -> HH.HTML w i
emptyState title description =
  HH.div
    [ cls [ "flex flex-col items-center justify-center py-12 text-center" ] ]
    [ HH.div
        [ cls [ "w-12 h-12 rounded-full bg-muted flex items-center justify-center mb-4" ] ]
        [ HH.span [ cls [ "text-muted-foreground text-xl" ] ] [ HH.text "∅" ] ]
    , HH.p
        [ cls [ "text-foreground font-medium mb-1" ] ]
        [ HH.text title ]
    , HH.p
        [ cls [ "text-muted-foreground text-sm max-w-sm" ] ]
        [ HH.text description ]
    ]
