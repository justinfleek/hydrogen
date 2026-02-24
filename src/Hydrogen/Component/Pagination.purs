-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pagination component
-- |
-- | Page navigation controls for paginated content.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Pagination as Pagination
-- |
-- | -- Basic pagination
-- | Pagination.pagination
-- |   [ Pagination.currentPage 3
-- |   , Pagination.totalPages 10
-- |   , Pagination.onPageChange HandlePageChange
-- |   ]
-- |
-- | -- With first/last buttons
-- | Pagination.pagination
-- |   [ Pagination.currentPage 5
-- |   , Pagination.totalPages 20
-- |   , Pagination.showFirstLast true
-- |   , Pagination.onPageChange HandlePageChange
-- |   ]
-- |
-- | -- Compact mode for mobile
-- | Pagination.pagination
-- |   [ Pagination.currentPage 1
-- |   , Pagination.totalPages 10
-- |   , Pagination.compact true
-- |   ]
-- |
-- | -- With page size selector
-- | Pagination.paginationWithInfo
-- |   { currentPage: 2
-- |   , totalPages: 10
-- |   , totalItems: 100
-- |   , pageSize: 10
-- |   , pageSizeOptions: [10, 25, 50, 100]
-- |   , onPageChange: HandlePageChange
-- |   , onPageSizeChange: HandlePageSizeChange
-- |   }
-- | ```
module Hydrogen.Component.Pagination
  ( -- * Pagination Components
    pagination
  , paginationWithInfo
  , paginationButton
  , paginationEllipsis
    -- * Props
  , PaginationProps
  , PaginationProp
  , PaginationInfo
  , defaultProps
    -- * Prop Builders
  , currentPage
  , totalPages
  , siblingCount
  , showFirstLast
  , compact
  , disabled
  , className
  , onPageChange
  ) where

import Prelude

import Data.Array (foldl, range, filter, nub, sort, length)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type PaginationProps i =
  { currentPage :: Int
  , totalPages :: Int
  , siblingCount :: Int   -- Pages to show on each side of current
  , showFirstLast :: Boolean
  , compact :: Boolean
  , disabled :: Boolean
  , className :: String
  , onPageChange :: Maybe (Int -> i)
  }

type PaginationProp i = PaginationProps i -> PaginationProps i

defaultProps :: forall i. PaginationProps i
defaultProps =
  { currentPage: 1
  , totalPages: 1
  , siblingCount: 1
  , showFirstLast: false
  , compact: false
  , disabled: false
  , className: ""
  , onPageChange: Nothing
  }

-- | Set current page (1-indexed)
currentPage :: forall i. Int -> PaginationProp i
currentPage p props = props { currentPage = p }

-- | Set total number of pages
totalPages :: forall i. Int -> PaginationProp i
totalPages t props = props { totalPages = t }

-- | Set number of sibling pages to show
siblingCount :: forall i. Int -> PaginationProp i
siblingCount s props = props { siblingCount = s }

-- | Show first/last page buttons
showFirstLast :: forall i. Boolean -> PaginationProp i
showFirstLast s props = props { showFirstLast = s }

-- | Compact mode (prev/next only)
compact :: forall i. Boolean -> PaginationProp i
compact c props = props { compact = c }

-- | Set disabled state
disabled :: forall i. Boolean -> PaginationProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> PaginationProp i
className c props = props { className = props.className <> " " <> c }

-- | Set page change handler
onPageChange :: forall i. (Int -> i) -> PaginationProp i
onPageChange handler props = props { onPageChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // pagination info
-- ═══════════════════════════════════════════════════════════════════════════════

type PaginationInfo i =
  { currentPage :: Int
  , totalPages :: Int
  , totalItems :: Int
  , pageSize :: Int
  , pageSizeOptions :: Array Int
  , onPageChange :: Int -> i
  , onPageSizeChange :: Int -> i
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main pagination component
pagination :: forall w i. Array (PaginationProp i) -> HH.HTML w i
pagination propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Generate page numbers with ellipsis
    pages = generatePageRange props.currentPage props.totalPages props.siblingCount
  in
    HH.nav
      [ cls [ "flex items-center gap-1", props.className ]
      , ARIA.label "Pagination"
      ]
      ( if props.compact
          then compactPagination props
          else fullPagination props pages
      )

-- | Full pagination with page numbers
fullPagination :: forall w i. PaginationProps i -> Array PageItem -> Array (HH.HTML w i)
fullPagination props pages =
  -- First button
  ( if props.showFirstLast
      then [ firstButton props ]
      else []
  )
  -- Previous button
  <> [ prevButton props ]
  -- Page numbers
  <> map (renderPageItem props) pages
  -- Next button
  <> [ nextButton props ]
  -- Last button
  <> ( if props.showFirstLast
        then [ lastButton props ]
        else []
     )

-- | Compact pagination (prev/next only)
compactPagination :: forall w i. PaginationProps i -> Array (HH.HTML w i)
compactPagination props =
  [ prevButton props
  , HH.span
      [ cls [ "text-sm text-muted-foreground px-2" ] ]
      [ HH.text (show props.currentPage <> " / " <> show props.totalPages) ]
  , nextButton props
  ]

-- | Pagination with info text and page size selector
paginationWithInfo :: forall w i. PaginationInfo i -> HH.HTML w i
paginationWithInfo info =
  let
    startItem = (info.currentPage - 1) * info.pageSize + 1
    endItem = min (info.currentPage * info.pageSize) info.totalItems
  in
    HH.div
      [ cls [ "flex flex-col sm:flex-row items-center justify-between gap-4" ] ]
      [ -- Info text
        HH.div
          [ cls [ "text-sm text-muted-foreground" ] ]
          [ HH.text ("Showing " <> show startItem <> "-" <> show endItem <> " of " <> show info.totalItems) ]
      , -- Controls row
        HH.div
          [ cls [ "flex items-center gap-4" ] ]
          [ -- Page size selector
            pageSizeSelector info
          , -- Pagination
            pagination
              [ currentPage info.currentPage
              , totalPages info.totalPages
              , onPageChange info.onPageChange
              ]
          ]
      ]

-- | Page size selector
pageSizeSelector :: forall w i. PaginationInfo i -> HH.HTML w i
pageSizeSelector info =
  HH.div
    [ cls [ "flex items-center gap-2" ] ]
    [ HH.span
        [ cls [ "text-sm text-muted-foreground" ] ]
        [ HH.text "Per page:" ]
    , HH.select
        [ cls 
            [ "h-9 rounded-md border border-input bg-background px-3 py-1 text-sm"
            , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
            ]
        , HE.onChange (\_ -> info.onPageSizeChange info.pageSize)
        ]
        (map (renderPageSizeOption info.pageSize) info.pageSizeOptions)
    ]

renderPageSizeOption :: forall w i. Int -> Int -> HH.HTML w i
renderPageSizeOption current size =
  HH.option
    [ HP.value (show size)
    , HP.selected (size == current)
    ]
    [ HH.text (show size) ]

-- | Individual pagination button
paginationButton :: forall w i. 
  { page :: Int
  , current :: Boolean
  , disabled :: Boolean
  , onClick :: Maybe (MouseEvent -> i)
  } -> 
  Array (HH.HTML w i) -> 
  HH.HTML w i
paginationButton opts children =
  let
    baseClasses = 
      "inline-flex items-center justify-center rounded-md text-sm font-medium ring-offset-background transition-colors h-9 w-9"
    
    stateClasses =
      if opts.current
        then "bg-primary text-primary-foreground"
        else "hover:bg-accent hover:text-accent-foreground"
    
    disabledClasses =
      "disabled:pointer-events-none disabled:opacity-50"
  in
    HH.button
      ( [ cls [ baseClasses, stateClasses, disabledClasses ]
        , HP.disabled opts.disabled
        , HP.attr (HH.AttrName "aria-current") (if opts.current then "page" else "false")
        ] <> case opts.onClick of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      children

-- | Pagination ellipsis
paginationEllipsis :: forall w i. HH.HTML w i
paginationEllipsis =
  HH.span
    [ cls [ "flex h-9 w-9 items-center justify-center" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "…" ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // navigation btns
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Previous page button
prevButton :: forall w i. PaginationProps i -> HH.HTML w i
prevButton props =
  HH.button
    ( [ cls 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 px-3"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , HP.disabled (props.disabled || props.currentPage <= 1)
      , ARIA.label "Previous page"
      ] <> case props.onPageChange of
        Just handler -> [ HE.onClick (\_ -> handler (props.currentPage - 1)) ]
        Nothing -> []
    )
    [ chevronLeftIcon
    , HH.span [ cls [ "sr-only sm:not-sr-only sm:ml-1" ] ] [ HH.text "Prev" ]
    ]

-- | Next page button
nextButton :: forall w i. PaginationProps i -> HH.HTML w i
nextButton props =
  HH.button
    ( [ cls 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 px-3"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , HP.disabled (props.disabled || props.currentPage >= props.totalPages)
      , ARIA.label "Next page"
      ] <> case props.onPageChange of
        Just handler -> [ HE.onClick (\_ -> handler (props.currentPage + 1)) ]
        Nothing -> []
    )
    [ HH.span [ cls [ "sr-only sm:not-sr-only sm:mr-1" ] ] [ HH.text "Next" ]
    , chevronRightIcon
    ]

-- | First page button
firstButton :: forall w i. PaginationProps i -> HH.HTML w i
firstButton props =
  HH.button
    ( [ cls 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 w-9"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , HP.disabled (props.disabled || props.currentPage <= 1)
      , ARIA.label "First page"
      ] <> case props.onPageChange of
        Just handler -> [ HE.onClick (\_ -> handler 1) ]
        Nothing -> []
    )
    [ chevronsLeftIcon ]

-- | Last page button
lastButton :: forall w i. PaginationProps i -> HH.HTML w i
lastButton props =
  HH.button
    ( [ cls 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 w-9"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , HP.disabled (props.disabled || props.currentPage >= props.totalPages)
      , ARIA.label "Last page"
      ] <> case props.onPageChange of
        Just handler -> [ HE.onClick (\_ -> handler props.totalPages) ]
        Nothing -> []
    )
    [ chevronsRightIcon ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // page range calc
-- ═══════════════════════════════════════════════════════════════════════════════

data PageItem
  = Page Int
  | Ellipsis

-- | Generate page range with ellipsis
generatePageRange :: Int -> Int -> Int -> Array PageItem
generatePageRange current total siblings =
  let
    -- Always show first, last, and pages around current
    firstPage = 1
    lastPage = total
    
    -- Calculate range around current page
    rangeStart = max 2 (current - siblings)
    rangeEnd = min (total - 1) (current + siblings)
    
    -- Build array of page numbers to show
    pageNumbers = 
      [firstPage] 
      <> range rangeStart rangeEnd 
      <> (if total > 1 then [lastPage] else [])
    
    -- Sort and dedupe
    uniquePages = sort (nub pageNumbers)
    
    -- Add ellipsis where there are gaps
    addEllipsis :: Array Int -> Array PageItem
    addEllipsis pages = go pages []
      where
        go arr acc = case arr of
          [] -> acc
          [x] -> acc <> [Page x]
          _ -> case { head: take 1 arr, tail: drop 1 arr } of
            { head: [a], tail: rest@[b] } | b - a > 1 -> 
              go rest (acc <> [Page a, Ellipsis])
            { head: [a], tail: rest } -> 
              case take 1 rest of
                [b] | b - a > 1 -> go rest (acc <> [Page a, Ellipsis])
                _ -> go rest (acc <> [Page a])
            _ -> acc
  in
    addEllipsis uniquePages
  where
    take :: forall a. Int -> Array a -> Array a
    take n arr = 
      if n <= 0 then []
      else case arr of
        [] -> []
        _ -> filter (\_ -> true) (foldl (\acc x -> if length acc < n then acc <> [x] else acc) [] arr)
    
    drop :: forall a. Int -> Array a -> Array a
    drop n arr = 
      foldl (\{ acc, i } x -> if i >= n then { acc: acc <> [x], i: i + 1 } else { acc, i: i + 1 }) { acc: [], i: 0 } arr
      # _.acc

-- | Render a page item (number or ellipsis)
renderPageItem :: forall w i. PaginationProps i -> PageItem -> HH.HTML w i
renderPageItem props item = case item of
  Page n ->
    paginationButton
      { page: n
      , current: n == props.currentPage
      , disabled: props.disabled
      , onClick: case props.onPageChange of
          Just handler -> Just (\_ -> handler n)
          Nothing -> Nothing
      }
      [ HH.text (show n) ]
  Ellipsis ->
    paginationEllipsis

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

chevronLeftIcon :: forall w i. HH.HTML w i
chevronLeftIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "15 18 9 12 15 6" ]
        []
    ]

chevronRightIcon :: forall w i. HH.HTML w i
chevronRightIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "9 18 15 12 9 6" ]
        []
    ]

chevronsLeftIcon :: forall w i. HH.HTML w i
chevronsLeftIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "11 17 6 12 11 7" ]
        []
    , HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "18 17 13 12 18 7" ]
        []
    ]

chevronsRightIcon :: forall w i. HH.HTML w i
chevronsRightIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "13 17 18 12 13 7" ]
        []
    , HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 17 11 12 6 7" ]
        []
    ]
