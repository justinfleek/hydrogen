-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // masonry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Masonry grid layout component
-- |
-- | Column-based masonry layout for variable-height content like
-- | image galleries, cards, and pinterest-style layouts.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Masonry as Masonry
-- |
-- | -- Basic masonry with 3 columns
-- | Masonry.masonry [ Masonry.columns 3 ]
-- |   [ item1, item2, item3, item4, item5 ]
-- |
-- | -- Responsive columns
-- | Masonry.masonry
-- |   [ Masonry.columnsSm 1
-- |   , Masonry.columnsMd 2
-- |   , Masonry.columnsLg 3
-- |   , Masonry.gap Masonry.G4
-- |   ]
-- |   [ items ]
-- |
-- | -- With custom gap
-- | Masonry.masonry [ Masonry.columns 4, Masonry.gap Masonry.G6 ]
-- |   [ galleryItems ]
-- | ```
module Hydrogen.Layout.Masonry
  ( -- * Component
    masonry
  , masonryItem
    -- * Props
  , MasonryProps
  , MasonryProp
  , columns
  , columnsSm
  , columnsMd
  , columnsLg
  , columnsXl
  , gap
  , order
  , className
    -- * Item Props
  , MasonryItemProps
  , MasonryItemProp
  , itemSpan
  , itemOrder
  , itemClassName
    -- * Gap Values
  , Gap(..)
    -- * Hooks
  , useMasonry
  , MasonryHandle
  , relayout
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // gap
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Gap sizes
data Gap
  = G0
  | G1
  | G2
  | G3
  | G4
  | G5
  | G6
  | G8
  | G10
  | G12
  | G16

derive instance eqGap :: Eq Gap

gapClass :: Gap -> String
gapClass = case _ of
  G0 -> "gap-0"
  G1 -> "gap-1"
  G2 -> "gap-2"
  G3 -> "gap-3"
  G4 -> "gap-4"
  G5 -> "gap-5"
  G6 -> "gap-6"
  G8 -> "gap-8"
  G10 -> "gap-10"
  G12 -> "gap-12"
  G16 -> "gap-16"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type MasonryProps =
  { columns :: Int
  , columnsSm :: Maybe Int
  , columnsMd :: Maybe Int
  , columnsLg :: Maybe Int
  , columnsXl :: Maybe Int
  , gap :: Gap
  , order :: String  -- "default" | "columns" | "rows"
  , className :: String
  }

type MasonryProp = MasonryProps -> MasonryProps

defaultProps :: MasonryProps
defaultProps =
  { columns: 3
  , columnsSm: Nothing
  , columnsMd: Nothing
  , columnsLg: Nothing
  , columnsXl: Nothing
  , gap: G4
  , order: "default"
  , className: ""
  }

-- | Set number of columns
columns :: Int -> MasonryProp
columns n props = props { columns = n }

-- | Columns at small breakpoint
columnsSm :: Int -> MasonryProp
columnsSm n props = props { columnsSm = Just n }

-- | Columns at medium breakpoint
columnsMd :: Int -> MasonryProp
columnsMd n props = props { columnsMd = Just n }

-- | Columns at large breakpoint
columnsLg :: Int -> MasonryProp
columnsLg n props = props { columnsLg = Just n }

-- | Columns at extra-large breakpoint
columnsXl :: Int -> MasonryProp
columnsXl n props = props { columnsXl = Just n }

-- | Set gap
gap :: Gap -> MasonryProp
gap g props = props { gap = g }

-- | Set item order mode
order :: String -> MasonryProp
order o props = props { order = o }

-- | Add custom class
className :: String -> MasonryProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // item props
-- ═══════════════════════════════════════════════════════════════════════════════

type MasonryItemProps =
  { span :: Int
  , order :: Maybe Int
  , className :: String
  }

type MasonryItemProp = MasonryItemProps -> MasonryItemProps

defaultItemProps :: MasonryItemProps
defaultItemProps =
  { span: 1
  , order: Nothing
  , className: ""
  }

-- | Item column span
itemSpan :: Int -> MasonryItemProp
itemSpan n props = props { span = n }

-- | Item order
itemOrder :: Int -> MasonryItemProp
itemOrder n props = props { order = Just n }

-- | Add custom class to item
itemClassName :: String -> MasonryItemProp
itemClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // FFI
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Masonry handle for imperative control
foreign import data MasonryHandle :: Type

-- | Initialize masonry layout on an element
foreign import initMasonry :: EffectFn1 String MasonryHandle

-- | Re-layout after content changes
foreign import relayoutImpl :: EffectFn1 MasonryHandle Unit

-- | Hook for masonry initialization
useMasonry :: String -> Effect MasonryHandle
useMasonry selector = runEffectFn1 initMasonry selector

-- | Trigger relayout
relayout :: MasonryHandle -> Effect Unit
relayout = runEffectFn1 relayoutImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Build column classes for CSS columns masonry
buildColumnClasses :: MasonryProps -> String
buildColumnClasses props =
  let
    base = "columns-" <> show props.columns
    sm = case props.columnsSm of
      Just n -> "sm:columns-" <> show n
      Nothing -> ""
    md = case props.columnsMd of
      Just n -> "md:columns-" <> show n
      Nothing -> ""
    lg = case props.columnsLg of
      Just n -> "lg:columns-" <> show n
      Nothing -> ""
    xl = case props.columnsXl of
      Just n -> "xl:columns-" <> show n
      Nothing -> ""
  in
    base <> " " <> sm <> " " <> md <> " " <> lg <> " " <> xl

-- | Masonry grid container
-- |
-- | Uses CSS columns for a pure-CSS masonry effect. Items flow
-- | top-to-bottom within each column. For true JS-based masonry
-- | with horizontal ordering, use `useMasonry` hook.
masonry :: forall w i. Array MasonryProp -> Array (HH.HTML w i) -> HH.HTML w i
masonry propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    columnClasses = buildColumnClasses props
  in
    HH.div
      [ cls [ columnClasses, gapClass props.gap, props.className ]
      , HP.attr (HH.AttrName "data-masonry") "true"
      ]
      children

-- | Masonry item wrapper
-- |
-- | Prevents items from being split across columns and adds
-- | proper spacing.
masonryItem :: forall w i. Array MasonryItemProp -> Array (HH.HTML w i) -> HH.HTML w i
masonryItem propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    orderStyle = case props.order of
      Just n -> [ HP.style ("order: " <> show n) ]
      Nothing -> []
  in
    HH.div
      ([ cls [ "break-inside-avoid mb-4", props.className ] ] <> orderStyle)
      children
