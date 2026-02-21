-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // statcard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | StatCard/MetricCard component
-- |
-- | Display statistics and metrics with optional trend indicators.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.StatCard as StatCard
-- |
-- | -- Basic stat card
-- | StatCard.statCard
-- |   { label: "Total Users"
-- |   , value: "12,345"
-- |   }
-- |
-- | -- With trend indicator
-- | StatCard.statCard
-- |   { label: "Revenue"
-- |   , value: "$54,321"
-- |   , trend: Just { value: 12.5, direction: StatCard.Up }
-- |   , description: Just "vs last month"
-- |   }
-- |
-- | -- With icon
-- | StatCard.statCardWithIcon
-- |   { label: "Active Sessions"
-- |   , value: "1,234"
-- |   , icon: usersIcon
-- |   }
-- |
-- | -- Stats grid
-- | StatCard.statGrid []
-- |   [ StatCard.statCard { label: "Users", value: "10k" }
-- |   , StatCard.statCard { label: "Revenue", value: "$50k" }
-- |   , StatCard.statCard { label: "Orders", value: "1.2k" }
-- |   ]
-- | ```
module Hydrogen.Component.StatCard
  ( -- * StatCard Components
    statCard
  , statCardWithIcon
  , statGrid
  , miniStat
    -- * Types
  , StatCardConfig
  , StatTrend
  , TrendDirection(..)
  , Size(..)
  , Variant(..)
    -- * Props
  , StatCardProps
  , StatCardProp
  , StatGridProps
  , StatGridProp
  , defaultProps
  , defaultGridProps
    -- * Prop Builders
  , variant
  , size
  , bordered
  , hoverable
  , className
  , columns
  , gap
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Trend direction
data TrendDirection
  = Up
  | Down
  | Neutral

derive instance eqTrendDirection :: Eq TrendDirection

-- | Trend indicator
type StatTrend =
  { value :: Number
  , direction :: TrendDirection
  }

-- | StatCard configuration
type StatCardConfig w i =
  { label :: String
  , value :: String
  , trend :: Maybe StatTrend
  , description :: Maybe String
  , icon :: Maybe (HH.HTML w i)
  }

-- | Size variants
data Size
  = Small
  | Medium
  | Large

derive instance eqSize :: Eq Size

-- | Card variants
data Variant
  = Default
  | Filled
  | Outlined
  | Ghost

derive instance eqVariant :: Eq Variant

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | StatCard properties
type StatCardProps =
  { variant :: Variant
  , size :: Size
  , bordered :: Boolean
  , hoverable :: Boolean
  , className :: String
  }

-- | Property modifier
type StatCardProp = StatCardProps -> StatCardProps

-- | Default properties
defaultProps :: StatCardProps
defaultProps =
  { variant: Default
  , size: Medium
  , bordered: true
  , hoverable: false
  , className: ""
  }

-- | Grid properties
type StatGridProps =
  { columns :: Int
  , gap :: String
  , className :: String
  }

type StatGridProp = StatGridProps -> StatGridProps

defaultGridProps :: StatGridProps
defaultGridProps =
  { columns: 4
  , gap: "gap-4"
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set variant
variant :: Variant -> StatCardProp
variant v props = props { variant = v }

-- | Set size
size :: Size -> StatCardProp
size s props = props { size = s }

-- | Show border
bordered :: Boolean -> StatCardProp
bordered b props = props { bordered = b }

-- | Make hoverable
hoverable :: Boolean -> StatCardProp
hoverable h props = props { hoverable = h }

-- | Add custom class
className :: String -> StatCardProp
className c props = props { className = props.className <> " " <> c }

-- | Set columns
columns :: Int -> StatGridProp
columns c props = props { columns = c }

-- | Set gap
gap :: String -> StatGridProp
gap g props = props { gap = g }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get variant classes
variantClasses :: Variant -> String
variantClasses = case _ of
  Default -> "bg-card text-card-foreground"
  Filled -> "bg-primary/10 text-foreground"
  Outlined -> "bg-transparent border-2"
  Ghost -> "bg-transparent"

-- | Get size classes
sizeClasses :: Size -> { container :: String, value :: String, label :: String }
sizeClasses = case _ of
  Small ->
    { container: "p-4"
    , value: "text-xl font-bold"
    , label: "text-xs text-muted-foreground"
    }
  Medium ->
    { container: "p-6"
    , value: "text-2xl font-bold"
    , label: "text-sm text-muted-foreground"
    }
  Large ->
    { container: "p-8"
    , value: "text-4xl font-bold"
    , label: "text-base text-muted-foreground"
    }

-- | Card base classes
cardBaseClasses :: String
cardBaseClasses =
  "rounded-lg"

-- | Trend classes based on direction
trendClasses :: TrendDirection -> String
trendClasses = case _ of
  Up -> "text-green-500"
  Down -> "text-red-500"
  Neutral -> "text-muted-foreground"

-- | Trend container classes
trendContainerClasses :: String
trendContainerClasses =
  "flex items-center text-sm"

-- | Description classes
descriptionClasses :: String
descriptionClasses =
  "text-xs text-muted-foreground mt-1"

-- | Icon container classes
iconContainerClasses :: String
iconContainerClasses =
  "flex items-center justify-center w-12 h-12 rounded-lg bg-primary/10 text-primary"

-- | Columns classes for grid
columnsClasses :: Int -> String
columnsClasses n = case n of
  1 -> "grid-cols-1"
  2 -> "grid-cols-1 sm:grid-cols-2"
  3 -> "grid-cols-1 sm:grid-cols-2 lg:grid-cols-3"
  4 -> "grid-cols-1 sm:grid-cols-2 lg:grid-cols-4"
  5 -> "grid-cols-2 sm:grid-cols-3 lg:grid-cols-5"
  6 -> "grid-cols-2 sm:grid-cols-3 lg:grid-cols-6"
  _ -> "grid-cols-1 sm:grid-cols-2 lg:grid-cols-4"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Trend indicator
trendIndicator :: forall w i. StatTrend -> HH.HTML w i
trendIndicator trend =
  HH.span
    [ cls [ trendContainerClasses, trendClasses trend.direction ] ]
    [ case trend.direction of
        Up -> trendUpIcon
        Down -> trendDownIcon
        Neutral -> HH.text ""
    , HH.text (show trend.value <> "%")
    ]

-- | Basic stat card
statCard :: forall w i. 
  Array StatCardProp -> 
  { label :: String, value :: String, trend :: Maybe StatTrend, description :: Maybe String } -> 
  HH.HTML w i
statCard propMods config =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    cardCls = 
      cardBaseClasses 
      <> " " <> variantClasses props.variant
      <> " " <> sizes.container
      <> (if props.bordered then " border" else "")
      <> (if props.hoverable then " hover:shadow-md transition-shadow cursor-pointer" else "")
      <> " " <> props.className
  in
    HH.div
      [ cls [ cardCls ] ]
      [ -- Label
        HH.p
          [ cls [ sizes.label ] ]
          [ HH.text config.label ]
      -- Value and trend
      , HH.div
          [ cls [ "flex items-baseline gap-2 mt-2" ] ]
          [ HH.p
              [ cls [ sizes.value ] ]
              [ HH.text config.value ]
          , case config.trend of
              Just t -> trendIndicator t
              Nothing -> HH.text ""
          ]
      -- Description
      , case config.description of
          Just desc ->
            HH.p
              [ cls [ descriptionClasses ] ]
              [ HH.text desc ]
          Nothing -> HH.text ""
      ]

-- | Stat card with icon
statCardWithIcon :: forall w i. 
  Array StatCardProp -> 
  { label :: String, value :: String, icon :: HH.HTML w i, trend :: Maybe StatTrend } -> 
  HH.HTML w i
statCardWithIcon propMods config =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    cardCls = 
      cardBaseClasses 
      <> " " <> variantClasses props.variant
      <> " " <> sizes.container
      <> (if props.bordered then " border" else "")
      <> (if props.hoverable then " hover:shadow-md transition-shadow cursor-pointer" else "")
      <> " " <> props.className
  in
    HH.div
      [ cls [ cardCls, "flex items-start gap-4" ] ]
      [ -- Icon
        HH.div
          [ cls [ iconContainerClasses ] ]
          [ config.icon ]
      -- Content
      , HH.div
          [ cls [ "flex-1" ] ]
          [ HH.p
              [ cls [ sizes.label ] ]
              [ HH.text config.label ]
          , HH.div
              [ cls [ "flex items-baseline gap-2 mt-1" ] ]
              [ HH.p
                  [ cls [ sizes.value ] ]
                  [ HH.text config.value ]
              , case config.trend of
                  Just t -> trendIndicator t
                  Nothing -> HH.text ""
              ]
          ]
      ]

-- | Mini stat (compact inline display)
miniStat :: forall w i. 
  { label :: String, value :: String } -> 
  HH.HTML w i
miniStat config =
  HH.div
    [ cls [ "flex items-center gap-2" ] ]
    [ HH.span
        [ cls [ "text-sm text-muted-foreground" ] ]
        [ HH.text config.label ]
    , HH.span
        [ cls [ "text-sm font-semibold" ] ]
        [ HH.text config.value ]
    ]

-- | Stats grid container
statGrid :: forall w i. Array StatGridProp -> Array (HH.HTML w i) -> HH.HTML w i
statGrid propMods children =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    gridCls = "grid " <> columnsClasses props.columns <> " " <> props.gap <> " " <> props.className
  in
    HH.div
      [ cls [ gridCls ] ]
      children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Trend up icon
trendUpIcon :: forall w i. HH.HTML w i
trendUpIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "d") "M7 17l9.2-9.2M17 17V7H7"
        ]
        []
    ]

-- | Trend down icon
trendDownIcon :: forall w i. HH.HTML w i
trendDownIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "d") "M17 7l-9.2 9.2M7 7v10h10"
        ]
        []
    ]
