-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // breadcrumb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Breadcrumb navigation component
-- |
-- | Breadcrumb trails for hierarchical navigation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Breadcrumb as Breadcrumb
-- |
-- | -- Basic breadcrumb
-- | Breadcrumb.breadcrumb []
-- |   [ Breadcrumb.breadcrumbItem [ Breadcrumb.href "/" ] [ HH.text "Home" ]
-- |   , Breadcrumb.breadcrumbItem [ Breadcrumb.href "/products" ] [ HH.text "Products" ]
-- |   , Breadcrumb.breadcrumbItem [ Breadcrumb.current true ] [ HH.text "Widget" ]
-- |   ]
-- |
-- | -- With custom separator
-- | Breadcrumb.breadcrumb [ Breadcrumb.separator "/" ]
-- |   [ ... ]
-- |
-- | -- Collapsed mode (ellipsis for long paths)
-- | Breadcrumb.breadcrumb [ Breadcrumb.collapsed 2 ]
-- |   [ ... ]
-- | ```
module Hydrogen.Component.Breadcrumb
  ( -- * Breadcrumb Components
    breadcrumb
  , breadcrumbItem
  , breadcrumbSeparator
  , breadcrumbEllipsis
    -- * Props
  , BreadcrumbProps
  , BreadcrumbProp
  , ItemProps
  , ItemProp
  , defaultProps
  , defaultItemProps
    -- * Prop Builders
  , separator
  , collapsed
  , className
  , href
  , current
  , onClick
  ) where

import Prelude

import Data.Array (foldl, length, take, drop)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // breadcrumb props
-- ═══════════════════════════════════════════════════════════════════════════════

type BreadcrumbProps =
  { separator :: String
  , collapsed :: Maybe Int  -- Show first N and last N items with ellipsis
  , className :: String
  }

type BreadcrumbProp = BreadcrumbProps -> BreadcrumbProps

defaultProps :: BreadcrumbProps
defaultProps =
  { separator: "›"
  , collapsed: Nothing
  , className: ""
  }

-- | Set custom separator character
separator :: String -> BreadcrumbProp
separator s props = props { separator = s }

-- | Collapse middle items when more than N items on each side
collapsed :: Int -> BreadcrumbProp
collapsed n props = props { collapsed = Just n }

-- | Add custom class to breadcrumb container
className :: String -> BreadcrumbProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // item props
-- ═══════════════════════════════════════════════════════════════════════════════

type ItemProps i =
  { href :: Maybe String
  , current :: Boolean
  , className :: String
  , onClick :: Maybe (MouseEvent -> i)
  }

type ItemProp i = ItemProps i -> ItemProps i

defaultItemProps :: forall i. ItemProps i
defaultItemProps =
  { href: Nothing
  , current: false
  , className: ""
  , onClick: Nothing
  }

-- | Set link href
href :: forall i. String -> ItemProp i
href h props = props { href = Just h }

-- | Mark as current page
current :: forall i. Boolean -> ItemProp i
current c props = props { current = c }

-- | Set click handler
onClick :: forall i. (MouseEvent -> i) -> ItemProp i
onClick handler props = props { onClick = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Breadcrumb container
breadcrumb :: forall w i. Array BreadcrumbProp -> Array (HH.HTML w i) -> HH.HTML w i
breadcrumb propMods items =
  let 
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Handle collapsed mode
    displayItems = case props.collapsed of
      Just n | length items > (n * 2 + 1) ->
        let
          firstItems = take n items
          lastItems = drop (length items - n) items
        in
          firstItems <> [ breadcrumbEllipsis ] <> lastItems
      _ -> items
    
    -- Interleave items with separators
    withSeparators = interleaveSeparator props.separator displayItems
  in
    HH.nav
      [ cls [ "flex", props.className ]
      , ARIA.label "Breadcrumb"
      ]
      [ HH.ol
          [ cls [ "flex items-center gap-1.5 flex-wrap" ] ]
          withSeparators
      ]

-- | Breadcrumb item
breadcrumbItem :: forall w i. Array (ItemProp i) -> Array (HH.HTML w i) -> HH.HTML w i
breadcrumbItem propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    linkClasses = 
      "text-sm font-medium text-muted-foreground hover:text-foreground transition-colors"
    
    currentClasses =
      "text-sm font-medium text-foreground"
  in
    HH.li
      [ cls [ "inline-flex items-center", props.className ] ]
      [ if props.current
          then
            HH.span
              [ cls [ currentClasses ]
              , HP.attr (HH.AttrName "aria-current") "page"
              ]
              children
          else case props.href of
            Just h ->
              HH.a
                ( [ cls [ linkClasses ]
                  , HP.href h
                  ] <> case props.onClick of
                    Just handler -> [ HE.onClick handler ]
                    Nothing -> []
                )
                children
            Nothing ->
              HH.span
                ( [ cls [ linkClasses, "cursor-pointer" ]
                  ] <> case props.onClick of
                    Just handler -> [ HE.onClick handler ]
                    Nothing -> []
                )
                children
      ]

-- | Breadcrumb separator
breadcrumbSeparator :: forall w i. String -> HH.HTML w i
breadcrumbSeparator sep =
  HH.li
    [ cls [ "text-muted-foreground" ]
    , ARIA.role "presentation"
    , ARIA.hidden "true"
    ]
    [ HH.span
        [ cls [ "text-sm" ] ]
        [ HH.text sep ]
    ]

-- | Breadcrumb ellipsis (for collapsed mode)
breadcrumbEllipsis :: forall w i. HH.HTML w i
breadcrumbEllipsis =
  HH.li
    [ cls [ "inline-flex items-center" ]
    , ARIA.role "presentation"
    ]
    [ HH.span
        [ cls [ "flex h-9 w-9 items-center justify-center" ]
        , ARIA.label "More pages"
        ]
        [ HH.element (HH.ElemName "svg")
            [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
            , HP.attr (HH.AttrName "width") "16"
            , HP.attr (HH.AttrName "height") "16"
            , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
            , HP.attr (HH.AttrName "fill") "none"
            , HP.attr (HH.AttrName "stroke") "currentColor"
            , HP.attr (HH.AttrName "stroke-width") "2"
            , HP.attr (HH.AttrName "stroke-linecap") "round"
            , HP.attr (HH.AttrName "stroke-linejoin") "round"
            , cls [ "text-muted-foreground" ]
            ]
            [ HH.element (HH.ElemName "circle")
                [ HP.attr (HH.AttrName "cx") "12"
                , HP.attr (HH.AttrName "cy") "12"
                , HP.attr (HH.AttrName "r") "1"
                ]
                []
            , HH.element (HH.ElemName "circle")
                [ HP.attr (HH.AttrName "cx") "19"
                , HP.attr (HH.AttrName "cy") "12"
                , HP.attr (HH.AttrName "r") "1"
                ]
                []
            , HH.element (HH.ElemName "circle")
                [ HP.attr (HH.AttrName "cx") "5"
                , HP.attr (HH.AttrName "cy") "12"
                , HP.attr (HH.AttrName "r") "1"
                ]
                []
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Interleave items with separators
interleaveSeparator :: forall w i. String -> Array (HH.HTML w i) -> Array (HH.HTML w i)
interleaveSeparator sep items = go items []
  where
    go :: Array (HH.HTML w i) -> Array (HH.HTML w i) -> Array (HH.HTML w i)
    go arr acc = case arr of
      [] -> acc
      [x] -> acc <> [x]
      _ -> case take 1 arr of
        [x] -> go (drop 1 arr) (acc <> [x, breadcrumbSeparator sep])
        _ -> acc
