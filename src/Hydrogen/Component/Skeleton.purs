-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // skeleton
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Skeleton loading component
-- |
-- | Placeholder loading skeletons for content that is being fetched.
-- |
-- | ## Features
-- |
-- | - Text skeleton (lines of varying width)
-- | - Circle skeleton (avatar placeholder)
-- | - Rectangle skeleton (card/image placeholder)
-- | - Custom shapes
-- | - Animation variants: pulse, shimmer, wave
-- | - Composition helpers for complex layouts
-- | - Pre-built presets: card, table, list
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Skeleton as Skeleton
-- |
-- | -- Basic text skeleton
-- | Skeleton.text [ Skeleton.lines 3 ]
-- |
-- | -- Avatar skeleton
-- | Skeleton.circle [ Skeleton.size 48 ]
-- |
-- | -- Rectangle skeleton
-- | Skeleton.rectangle [ Skeleton.width 200, Skeleton.height 100 ]
-- |
-- | -- With shimmer animation
-- | Skeleton.text [ Skeleton.animation Skeleton.Shimmer ]
-- |
-- | -- Card preset
-- | Skeleton.cardSkeleton []
-- |
-- | -- Table preset
-- | Skeleton.tableSkeleton [ Skeleton.rows 5, Skeleton.columns 4 ]
-- |
-- | -- Compose custom skeleton
-- | Skeleton.group [ Skeleton.direction Skeleton.Horizontal ]
-- |   [ Skeleton.circle [ Skeleton.size 40 ]
-- |   , Skeleton.group [ Skeleton.direction Skeleton.Vertical ]
-- |       [ Skeleton.text [ Skeleton.width 120 ]
-- |       , Skeleton.text [ Skeleton.width 80 ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Component.Skeleton
  ( -- * Skeleton Components
    skeleton
  , text
  , circle
  , rectangle
  , group
    -- * Presets
  , cardSkeleton
  , tableSkeleton
  , listSkeleton
  , avatarWithText
  , paragraphSkeleton
    -- * Props
  , SkeletonProps
  , SkeletonProp
  , GroupProps
  , GroupProp
  , TableProps
  , TableProp
  , defaultProps
  , defaultGroupProps
  , defaultTableProps
    -- * Prop Builders
  , width
  , height
  , size
  , animation
  , rounded
  , lines
  , rows
  , columns
  , direction
  , gap
  , className
    -- * Types
  , Animation(..)
  , Direction(..)
  ) where

import Prelude

import Data.Array (foldl, range, replicate)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Skeleton animation type
data Animation
  = Pulse    -- Fading in/out
  | Shimmer  -- Moving highlight
  | Wave     -- Wave effect
  | None     -- No animation

derive instance eqAnimation :: Eq Animation

-- | Group direction
data Direction
  = Horizontal
  | Vertical

derive instance eqDirection :: Eq Direction

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Skeleton element properties
type SkeletonProps =
  { width :: String       -- CSS width
  , height :: String      -- CSS height
  , animation :: Animation
  , rounded :: String     -- Border radius class
  , className :: String
  }

-- | Skeleton property modifier
type SkeletonProp = SkeletonProps -> SkeletonProps

-- | Default skeleton properties
defaultProps :: SkeletonProps
defaultProps =
  { width: "100%"
  , height: "1rem"
  , animation: Pulse
  , rounded: "rounded"
  , className: ""
  }

-- | Group properties
type GroupProps =
  { direction :: Direction
  , gap :: String
  , className :: String
  }

-- | Group property modifier
type GroupProp = GroupProps -> GroupProps

-- | Default group properties
defaultGroupProps :: GroupProps
defaultGroupProps =
  { direction: Vertical
  , gap: "gap-2"
  , className: ""
  }

-- | Table skeleton properties
type TableProps =
  { rows :: Int
  , columns :: Int
  , headerHeight :: String
  , rowHeight :: String
  , animation :: Animation
  , className :: String
  }

-- | Table property modifier
type TableProp = TableProps -> TableProps

-- | Default table properties
defaultTableProps :: TableProps
defaultTableProps =
  { rows: 5
  , columns: 4
  , headerHeight: "2.5rem"
  , rowHeight: "2rem"
  , animation: Pulse
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set width (CSS value)
width :: String -> SkeletonProp
width w props = props { width = w }

-- | Set height (CSS value)
height :: String -> SkeletonProp
height h props = props { height = h }

-- | Set size (for circle - sets both width and height)
size :: Int -> SkeletonProp
size s props = props { width = show s <> "px", height = show s <> "px" }

-- | Set animation type
animation :: Animation -> SkeletonProp
animation a props = props { animation = a }

-- | Set border radius class
rounded :: String -> SkeletonProp
rounded r props = props { rounded = r }

-- | Set number of lines (for text skeleton)
lines :: Int -> SkeletonProp
lines _ props = props  -- Used by text component

-- | Set number of rows (for table)
rows :: Int -> TableProp
rows r props = props { rows = r }

-- | Set number of columns (for table)
columns :: Int -> TableProp
columns c props = props { columns = c }

-- | Set group direction
direction :: Direction -> GroupProp
direction d props = props { direction = d }

-- | Set group gap
gap :: String -> GroupProp
gap g props = props { gap = g }

-- | Add custom class
className :: String -> SkeletonProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get animation classes
animationClasses :: Animation -> String
animationClasses = case _ of
  Pulse -> "animate-pulse"
  Shimmer -> "animate-shimmer bg-gradient-to-r from-muted via-muted-foreground/10 to-muted bg-[length:200%_100%]"
  Wave -> "animate-wave"
  None -> ""

-- | Base skeleton element
-- |
-- | Generic skeleton with configurable dimensions
skeleton :: forall w i. Array SkeletonProp -> HH.HTML w i
skeleton propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    sizeStyle = "width: " <> props.width <> "; height: " <> props.height
    
    baseClasses = "skeleton bg-muted"
  in
    HH.div
      [ cls [ baseClasses, props.rounded, animationClasses props.animation, props.className ]
      , HP.attr (HH.AttrName "style") sizeStyle
      , ARIA.hidden "true"
      ]
      []

-- | Text skeleton
-- |
-- | Multiple lines of text placeholder
text :: forall w i. Array SkeletonProp -> HH.HTML w i
text propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "skeleton-text bg-muted", props.rounded, animationClasses props.animation, props.className ]
      , HP.attr (HH.AttrName "style") ("width: " <> props.width <> "; height: " <> props.height)
      , ARIA.hidden "true"
      ]
      []

-- | Circle skeleton
-- |
-- | Circular placeholder (for avatars)
circle :: forall w i. Array SkeletonProp -> HH.HTML w i
circle propMods =
  let
    props = foldl (\p f -> f p) defaultProps { rounded = "rounded-full" } propMods
    
    sizeStyle = "width: " <> props.width <> "; height: " <> props.height
  in
    HH.div
      [ cls [ "skeleton-circle bg-muted rounded-full flex-shrink-0", animationClasses props.animation, props.className ]
      , HP.attr (HH.AttrName "style") sizeStyle
      , ARIA.hidden "true"
      ]
      []

-- | Rectangle skeleton
-- |
-- | Rectangular placeholder (for cards, images)
rectangle :: forall w i. Array SkeletonProp -> HH.HTML w i
rectangle propMods =
  let
    props = foldl (\p f -> f p) defaultProps { rounded = "rounded-lg" } propMods
    
    sizeStyle = "width: " <> props.width <> "; height: " <> props.height
  in
    HH.div
      [ cls [ "skeleton-rectangle bg-muted", props.rounded, animationClasses props.animation, props.className ]
      , HP.attr (HH.AttrName "style") sizeStyle
      , ARIA.hidden "true"
      ]
      []

-- | Group skeletons together
-- |
-- | Layout container for composing skeletons
group :: forall w i. Array GroupProp -> Array (HH.HTML w i) -> HH.HTML w i
group propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    
    directionClass = case props.direction of
      Horizontal -> "flex-row items-center"
      Vertical -> "flex-col"
  in
    HH.div
      [ cls [ "skeleton-group flex", directionClass, props.gap, props.className ]
      , ARIA.hidden "true"
      ]
      children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card skeleton preset
-- |
-- | Typical card layout with image, title, and description
cardSkeleton :: forall w i. Array SkeletonProp -> HH.HTML w i
cardSkeleton propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "skeleton-card space-y-4 p-4 border rounded-lg", animationClasses props.animation, props.className ]
      , ARIA.hidden "true"
      , ARIA.label "Loading card"
      ]
      [ -- Image placeholder
        rectangle [ height "10rem" ]
      , -- Title
        text [ width "70%", height "1.25rem" ]
      , -- Description lines
        group []
          [ text [ width "100%", height "0.875rem" ]
          , text [ width "90%", height "0.875rem" ]
          , text [ width "60%", height "0.875rem" ]
          ]
      ]

-- | Table skeleton preset
-- |
-- | Table with header and rows
tableSkeleton :: forall w i. Array TableProp -> HH.HTML w i
tableSkeleton propMods =
  let
    props = foldl (\p f -> f p) defaultTableProps propMods
    
    headerCells = replicate props.columns
      (HH.div
        [ cls [ "skeleton-cell bg-muted rounded", animationClasses props.animation ]
        , HP.attr (HH.AttrName "style") ("height: " <> props.headerHeight)
        ]
        [])
    
    renderRow :: Int -> HH.HTML w i
    renderRow _ =
      HH.div
        [ cls [ "skeleton-row grid gap-4" ]
        , HP.attr (HH.AttrName "style") ("grid-template-columns: repeat(" <> show props.columns <> ", 1fr)")
        ]
        (replicate props.columns
          (HH.div
            [ cls [ "skeleton-cell bg-muted rounded", animationClasses props.animation ]
            , HP.attr (HH.AttrName "style") ("height: " <> props.rowHeight)
            ]
            []))
    
    dataRows = map renderRow (range 1 props.rows)
  in
    HH.div
      [ cls [ "skeleton-table space-y-2", props.className ]
      , ARIA.hidden "true"
      , ARIA.label "Loading table"
      ]
      [ -- Header row
        HH.div
          [ cls [ "skeleton-header grid gap-4" ]
          , HP.attr (HH.AttrName "style") ("grid-template-columns: repeat(" <> show props.columns <> ", 1fr)")
          ]
          headerCells
      , -- Separator
        HH.div [ cls [ "border-b my-2" ] ] []
      , -- Data rows
        HH.div
          [ cls [ "skeleton-body space-y-2" ] ]
          dataRows
      ]

-- | List skeleton preset
-- |
-- | List items with avatar and text
listSkeleton :: forall w i. Int -> Array SkeletonProp -> HH.HTML w i
listSkeleton count propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    items = map (\_ -> avatarWithText []) (range 1 count)
  in
    HH.div
      [ cls [ "skeleton-list space-y-4", props.className ]
      , ARIA.hidden "true"
      , ARIA.label "Loading list"
      ]
      items

-- | Avatar with text preset
-- |
-- | Common pattern: avatar circle with name and subtitle
avatarWithText :: forall w i. Array SkeletonProp -> HH.HTML w i
avatarWithText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "skeleton-avatar-text flex items-center gap-3", animationClasses props.animation, props.className ]
      , ARIA.hidden "true"
      ]
      [ -- Avatar
        circle [ size 40 ]
      , -- Text
        group [ gap "gap-1" ]
          [ text [ width "8rem", height "1rem" ]
          , text [ width "6rem", height "0.75rem" ]
          ]
      ]

-- | Paragraph skeleton
-- |
-- | Multiple lines with varying widths
paragraphSkeleton :: forall w i. Int -> Array SkeletonProp -> HH.HTML w i
paragraphSkeleton lineCount propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Vary widths based on line index
    getWidth :: Int -> String
    getWidth idx = case idx `mod` 5 of
      0 -> "100%"
      1 -> "95%"
      2 -> "85%"
      3 -> "90%"
      _ -> "70%"
    
    renderLine :: Int -> HH.HTML w i
    renderLine idx =
      text 
        [ width (getWidth idx)
        , height "0.875rem"
        , animation props.animation
        ]
  in
    HH.div
      [ cls [ "skeleton-paragraph space-y-2", props.className ]
      , ARIA.hidden "true"
      ]
      (map renderLine (range 0 (lineCount - 1)))
