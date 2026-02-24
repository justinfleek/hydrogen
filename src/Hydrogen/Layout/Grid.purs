-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS Grid layout components
-- |
-- | Type-safe CSS Grid utilities.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Grid as Grid
-- |
-- | -- Simple grid with 3 columns
-- | Grid.grid [ Grid.cols 3, Grid.gap Grid.G4 ]
-- |   [ item1, item2, item3, item4, item5, item6 ]
-- |
-- | -- Responsive grid
-- | Grid.grid [ Grid.colsSm 1, Grid.colsMd 2, Grid.colsLg 3 ]
-- |   [ items ]
-- |
-- | -- Grid item with span
-- | Grid.gridItem [ Grid.colSpan 2 ]
-- |   [ content ]
-- | ```
module Hydrogen.Layout.Grid
  ( -- * Grid Components
    grid
  , gridItem
    -- * Grid Props
  , GridProps
  , GridProp
  , cols
  , rows
  , gap
  , gapX
  , gapY
  , className
    -- * Responsive Columns
  , colsSm
  , colsMd
  , colsLg
  , colsXl
    -- * Grid Item Props
  , GridItemProps
  , GridItemProp
  , colSpan
  , colStart
  , colEnd
  , rowSpan
  , rowStart
  , rowEnd
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // grid props
-- ═══════════════════════════════════════════════════════════════════════════════

type GridProps =
  { cols :: Maybe Int
  , rows :: Maybe Int
  , gap :: Maybe Int
  , gapX :: Maybe Int
  , gapY :: Maybe Int
  , colsSm :: Maybe Int
  , colsMd :: Maybe Int
  , colsLg :: Maybe Int
  , colsXl :: Maybe Int
  , className :: String
  }

type GridProp = GridProps -> GridProps

defaultGridProps :: GridProps
defaultGridProps =
  { cols: Nothing
  , rows: Nothing
  , gap: Nothing
  , gapX: Nothing
  , gapY: Nothing
  , colsSm: Nothing
  , colsMd: Nothing
  , colsLg: Nothing
  , colsXl: Nothing
  , className: ""
  }

-- | Set number of columns
cols :: Int -> GridProp
cols n props = props { cols = Just n }

-- | Set number of rows
rows :: Int -> GridProp
rows n props = props { rows = Just n }

-- | Set gap (both x and y)
gap :: Int -> GridProp
gap n props = props { gap = Just n }

-- | Set horizontal gap
gapX :: Int -> GridProp
gapX n props = props { gapX = Just n }

-- | Set vertical gap
gapY :: Int -> GridProp
gapY n props = props { gapY = Just n }

-- | Columns at small breakpoint
colsSm :: Int -> GridProp
colsSm n props = props { colsSm = Just n }

-- | Columns at medium breakpoint
colsMd :: Int -> GridProp
colsMd n props = props { colsMd = Just n }

-- | Columns at large breakpoint
colsLg :: Int -> GridProp
colsLg n props = props { colsLg = Just n }

-- | Columns at extra large breakpoint
colsXl :: Int -> GridProp
colsXl n props = props { colsXl = Just n }

-- | Add custom class
className :: String -> GridProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // grid item props
-- ═══════════════════════════════════════════════════════════════════════════════

type GridItemProps =
  { colSpan :: Maybe Int
  , colStart :: Maybe Int
  , colEnd :: Maybe Int
  , rowSpan :: Maybe Int
  , rowStart :: Maybe Int
  , rowEnd :: Maybe Int
  , className :: String
  }

type GridItemProp = GridItemProps -> GridItemProps

defaultItemProps :: GridItemProps
defaultItemProps =
  { colSpan: Nothing
  , colStart: Nothing
  , colEnd: Nothing
  , rowSpan: Nothing
  , rowStart: Nothing
  , rowEnd: Nothing
  , className: ""
  }

-- | Column span
colSpan :: Int -> GridItemProp
colSpan n props = props { colSpan = Just n }

-- | Column start
colStart :: Int -> GridItemProp
colStart n props = props { colStart = Just n }

-- | Column end
colEnd :: Int -> GridItemProp
colEnd n props = props { colEnd = Just n }

-- | Row span
rowSpan :: Int -> GridItemProp
rowSpan n props = props { rowSpan = Just n }

-- | Row start
rowStart :: Int -> GridItemProp
rowStart n props = props { rowStart = Just n }

-- | Row end
rowEnd :: Int -> GridItemProp
rowEnd n props = props { rowEnd = Just n }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Grid container
grid :: forall w i. Array GridProp -> Array (HH.HTML w i) -> HH.HTML w i
grid propMods children =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    classes = buildGridClasses props
  in
    HH.div
      [ cls [ "grid", classes, props.className ] ]
      children

-- | Grid item
gridItem :: forall w i. Array GridItemProp -> Array (HH.HTML w i) -> HH.HTML w i
gridItem propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    classes = buildItemClasses props
  in
    HH.div
      [ cls [ classes, props.className ] ]
      children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

buildGridClasses :: GridProps -> String
buildGridClasses props =
  maybeClass "grid-cols-" props.cols <>
  maybeClass "grid-rows-" props.rows <>
  maybeClass "gap-" props.gap <>
  maybeClass "gap-x-" props.gapX <>
  maybeClass "gap-y-" props.gapY <>
  maybeClass "sm:grid-cols-" props.colsSm <>
  maybeClass "md:grid-cols-" props.colsMd <>
  maybeClass "lg:grid-cols-" props.colsLg <>
  maybeClass "xl:grid-cols-" props.colsXl

buildItemClasses :: GridItemProps -> String
buildItemClasses props =
  maybeClass "col-span-" props.colSpan <>
  maybeClass "col-start-" props.colStart <>
  maybeClass "col-end-" props.colEnd <>
  maybeClass "row-span-" props.rowSpan <>
  maybeClass "row-start-" props.rowStart <>
  maybeClass "row-end-" props.rowEnd

maybeClass :: String -> Maybe Int -> String
maybeClass _ Nothing = ""
maybeClass prefix (Just n) = prefix <> show n <> " "
