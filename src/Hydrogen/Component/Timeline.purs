-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // timeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timeline visualization component
-- |
-- | A flexible timeline component for displaying chronological events,
-- | milestones, and progress indicators in both vertical and horizontal
-- | orientations.
-- |
-- | ## Features
-- |
-- | - Vertical and horizontal layouts
-- | - Alternating sides for vertical timelines
-- | - Item states: active, completed, pending
-- | - Custom icons per item
-- | - Collapsible items with expanded content
-- | - Connecting lines with customizable styles
-- | - Custom content slots
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Timeline as Timeline
-- |
-- | -- Basic vertical timeline
-- | Timeline.timeline
-- |   [ Timeline.orientation Timeline.Vertical
-- |   , Timeline.alternating true
-- |   ]
-- |   [ Timeline.timelineItem
-- |       [ Timeline.title "Project Started"
-- |       , Timeline.date "Jan 2024"
-- |       , Timeline.state Timeline.Completed
-- |       , Timeline.icon "rocket"
-- |       ]
-- |       [ HH.text "Initial project kickoff" ]
-- |   , Timeline.timelineItem
-- |       [ Timeline.title "Development Phase"
-- |       , Timeline.date "Feb 2024"
-- |       , Timeline.state Timeline.Active
-- |       ]
-- |       [ HH.text "Building core features" ]
-- |   , Timeline.timelineItem
-- |       [ Timeline.title "Launch"
-- |       , Timeline.date "Mar 2024"
-- |       , Timeline.state Timeline.Pending
-- |       ]
-- |       [ HH.text "Public release" ]
-- |   ]
-- |
-- | -- Horizontal timeline
-- | Timeline.timeline
-- |   [ Timeline.orientation Timeline.Horizontal ]
-- |   [ Timeline.timelineItem [ Timeline.title "Step 1" ] []
-- |   , Timeline.timelineItem [ Timeline.title "Step 2" ] []
-- |   , Timeline.timelineItem [ Timeline.title "Step 3" ] []
-- |   ]
-- |
-- | -- Collapsible items
-- | Timeline.timeline []
-- |   [ Timeline.timelineItem
-- |       [ Timeline.title "Event"
-- |       , Timeline.collapsible true
-- |       , Timeline.expanded false
-- |       , Timeline.onToggle HandleToggle
-- |       ]
-- |       [ HH.text "Collapsed content..." ]
-- |   ]
-- | ```
module Hydrogen.Component.Timeline
  ( -- * Timeline Components
    timeline
  , timelineItem
  , timelineConnector
  , timelineDot
  , timelineContent
    -- * Props
  , TimelineProps
  , TimelineProp
  , ItemProps
  , ItemProp
  , defaultProps
  , defaultItemProps
    -- * Prop Builders - Timeline
  , orientation
  , alternating
  , lineStyle
  , className
    -- * Prop Builders - Item
  , title
  , description
  , date
  , icon
  , state
  , collapsible
  , expanded
  , side
  , onToggle
  , itemClassName
    -- * Types
  , Orientation(Vertical, Horizontal)
  , ItemState(Pending, Active, Completed)
  , Side(Left, Right, Auto)
  , LineStyle(Solid, Dashed, Dotted)
  ) where

import Prelude

import Data.Array (foldl, mapWithIndex)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timeline orientation
data Orientation
  = Vertical
  | Horizontal

derive instance eqOrientation :: Eq Orientation

-- | Timeline item state
data ItemState
  = Pending
  | Active
  | Completed

derive instance eqItemState :: Eq ItemState

-- | Side for alternating layout
data Side
  = Left
  | Right
  | Auto

derive instance eqSide :: Eq Side

-- | Connector line style
data LineStyle
  = Solid
  | Dashed
  | Dotted

derive instance eqLineStyle :: Eq LineStyle

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timeline container properties
type TimelineProps i =
  { orientation :: Orientation
  , alternating :: Boolean
  , lineStyle :: LineStyle
  , className :: String
  }

-- | Timeline property modifier
type TimelineProp i = TimelineProps i -> TimelineProps i

-- | Default timeline properties
defaultProps :: forall i. TimelineProps i
defaultProps =
  { orientation: Vertical
  , alternating: false
  , lineStyle: Solid
  , className: ""
  }

-- | Timeline item properties
type ItemProps i =
  { title :: String
  , description :: String
  , date :: String
  , icon :: Maybe String
  , state :: ItemState
  , collapsible :: Boolean
  , expanded :: Boolean
  , side :: Side
  , className :: String
  , onToggle :: Maybe (Boolean -> i)
  }

-- | Item property modifier
type ItemProp i = ItemProps i -> ItemProps i

-- | Default item properties
defaultItemProps :: forall i. ItemProps i
defaultItemProps =
  { title: ""
  , description: ""
  , date: ""
  , icon: Nothing
  , state: Pending
  , collapsible: false
  , expanded: true
  , side: Auto
  , className: ""
  , onToggle: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set timeline orientation
orientation :: forall i. Orientation -> TimelineProp i
orientation o props = props { orientation = o }

-- | Enable alternating sides (vertical only)
alternating :: forall i. Boolean -> TimelineProp i
alternating a props = props { alternating = a }

-- | Set connector line style
lineStyle :: forall i. LineStyle -> TimelineProp i
lineStyle s props = props { lineStyle = s }

-- | Add custom class to timeline container
className :: forall i. String -> TimelineProp i
className c props = props { className = props.className <> " " <> c }

-- | Set item title
title :: forall i. String -> ItemProp i
title t props = props { title = t }

-- | Set item description
description :: forall i. String -> ItemProp i
description d props = props { description = d }

-- | Set item date
date :: forall i. String -> ItemProp i
date d props = props { date = d }

-- | Set item icon (icon name or emoji)
icon :: forall i. String -> ItemProp i
icon i props = props { icon = Just i }

-- | Set item state
state :: forall i. ItemState -> ItemProp i
state s props = props { state = s }

-- | Make item collapsible
collapsible :: forall i. Boolean -> ItemProp i
collapsible c props = props { collapsible = c }

-- | Set expanded state (for collapsible items)
expanded :: forall i. Boolean -> ItemProp i
expanded e props = props { expanded = e }

-- | Set item side (for alternating layout)
side :: forall i. Side -> ItemProp i
side s props = props { side = s }

-- | Set toggle handler for collapsible items
onToggle :: forall i. (Boolean -> i) -> ItemProp i
onToggle handler props = props { onToggle = Just handler }

-- | Add custom class to item
itemClassName :: forall i. String -> ItemProp i
itemClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timeline container
-- |
-- | Wraps timeline items with proper layout and orientation
timeline :: forall w i. Array (TimelineProp i) -> Array (HH.HTML w i) -> HH.HTML w i
timeline propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isHorizontal = props.orientation == Horizontal
    
    containerClasses = case props.orientation of
      Horizontal -> "flex items-start gap-0 overflow-x-auto"
      Vertical -> 
        if props.alternating
          then "relative"
          else "relative flex flex-col"
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-orientation") 
          (if isHorizontal then "horizontal" else "vertical")
      , HP.attr (HH.AttrName "data-alternating") 
          (if props.alternating then "true" else "false")
      , ARIA.role "list"
      ]
      children

-- | Timeline item
-- |
-- | Individual timeline entry with dot, connector, and content
timelineItem :: forall w i. Array (ItemProp i) -> Array (HH.HTML w i) -> HH.HTML w i
timelineItem propMods content =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    stateClasses = case props.state of
      Completed -> "timeline-item-completed"
      Active -> "timeline-item-active"
      Pending -> "timeline-item-pending"
    
    containerClasses = 
      "relative flex gap-4 pb-8 last:pb-0"
  in
    HH.div
      [ cls [ containerClasses, stateClasses, props.className ]
      , ARIA.role "listitem"
      ]
      [ -- Timeline indicator (dot + connector)
        HH.div
          [ cls [ "flex flex-col items-center" ] ]
          [ timelineDot props
          , timelineConnector props
          ]
      -- Content area
      , timelineContent props content
      ]

-- | Timeline dot/marker
timelineDot :: forall w i. ItemProps i -> HH.HTML w i
timelineDot props =
  let
    baseClasses = 
      "relative z-10 flex h-10 w-10 shrink-0 items-center justify-center rounded-full border-2"
    
    stateClasses = case props.state of
      Completed -> "border-primary bg-primary text-primary-foreground"
      Active -> "border-primary bg-background text-primary ring-4 ring-primary/20"
      Pending -> "border-muted-foreground/30 bg-muted text-muted-foreground"
    
    iconContent = case props.icon of
      Just i -> HH.text i
      Nothing -> case props.state of
        Completed -> HH.text "✓"
        Active -> HH.span [ cls [ "h-3 w-3 rounded-full bg-primary animate-pulse" ] ] []
        Pending -> HH.text "○"
  in
    HH.div
      [ cls [ baseClasses, stateClasses ]
      , ARIA.hidden "true"
      ]
      [ iconContent ]

-- | Timeline connector line
timelineConnector :: forall w i. ItemProps i -> HH.HTML w i
timelineConnector props =
  let
    baseClasses = "flex-1 w-0.5 min-h-8"
    
    stateClasses = case props.state of
      Completed -> "bg-primary"
      Active -> "bg-gradient-to-b from-primary to-muted-foreground/30"
      Pending -> "bg-muted-foreground/30"
  in
    HH.div
      [ cls [ baseClasses, stateClasses ]
      , ARIA.hidden "true"
      ]
      []

-- | Timeline content area
timelineContent :: forall w i. ItemProps i -> Array (HH.HTML w i) -> HH.HTML w i
timelineContent props children =
  let
    baseClasses = "flex-1 pt-1.5 pb-2"
    
    headerClasses = "flex items-start justify-between gap-2 mb-1"
    
    titleClasses = case props.state of
      Completed -> "font-semibold text-foreground"
      Active -> "font-semibold text-primary"
      Pending -> "font-medium text-muted-foreground"
    
    dateClasses = "text-xs text-muted-foreground whitespace-nowrap"
    
    descClasses = "text-sm text-muted-foreground"
    
    contentClasses = 
      if props.collapsible && not props.expanded
        then "hidden"
        else "mt-2"
    
    toggleHandler = case props.onToggle of
      Just handler -> [ HE.onClick (\_ -> handler (not props.expanded)) ]
      Nothing -> []
    
    collapsibleAttrs = 
      if props.collapsible
        then 
          [ cls [ "cursor-pointer hover:bg-muted/50 -mx-2 px-2 rounded transition-colors" ]
          , ARIA.expanded (if props.expanded then "true" else "false")
          ] <> toggleHandler
        else []
  in
    HH.div
      [ cls [ baseClasses ] ]
      [ HH.div
          ( [ cls [ headerClasses ] ] <> collapsibleAttrs )
          [ HH.div_
              [ HH.h3 [ cls [ titleClasses ] ] [ HH.text props.title ]
              , if props.description /= ""
                  then HH.p [ cls [ descClasses ] ] [ HH.text props.description ]
                  else HH.text ""
              ]
          , HH.span [ cls [ dateClasses ] ] [ HH.text props.date ]
          ]
      , if not (null children)
          then 
            HH.div
              [ cls [ contentClasses ] ]
              children
          else HH.text ""
      ]
  where
    null :: forall a. Array a -> Boolean
    null [] = true
    null _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // horizontal layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Horizontal timeline item
-- |
-- | For horizontal layouts, use this variant
horizontalTimelineItem :: forall w i. Array (ItemProp i) -> Array (HH.HTML w i) -> HH.HTML w i
horizontalTimelineItem propMods content =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    stateClasses = case props.state of
      Completed -> "timeline-item-completed"
      Active -> "timeline-item-active"
      Pending -> "timeline-item-pending"
  in
    HH.div
      [ cls [ "flex flex-col items-center min-w-32 px-4", stateClasses, props.className ]
      , ARIA.role "listitem"
      ]
      [ -- Date above
        HH.span 
          [ cls [ "text-xs text-muted-foreground mb-2" ] ] 
          [ HH.text props.date ]
      -- Dot with horizontal connectors
      , HH.div
          [ cls [ "relative flex items-center w-full" ] ]
          [ -- Left connector
            HH.div
              [ cls [ "flex-1 h-0.5", connectorClass props.state ] ]
              []
          -- Dot
          , horizontalDot props
          -- Right connector
          , HH.div
              [ cls [ "flex-1 h-0.5", connectorClass props.state ] ]
              []
          ]
      -- Content below
      , HH.div
          [ cls [ "mt-2 text-center" ] ]
          [ HH.h4 
              [ cls [ "font-medium text-sm", titleClass props.state ] ] 
              [ HH.text props.title ]
          , if props.description /= ""
              then HH.p [ cls [ "text-xs text-muted-foreground mt-1" ] ] 
                        [ HH.text props.description ]
              else HH.text ""
          ]
      ]
  where
    connectorClass :: ItemState -> String
    connectorClass s = case s of
      Completed -> "bg-primary"
      Active -> "bg-primary"
      Pending -> "bg-muted-foreground/30"
    
    titleClass :: ItemState -> String
    titleClass s = case s of
      Completed -> "text-foreground"
      Active -> "text-primary"
      Pending -> "text-muted-foreground"

-- | Horizontal timeline dot
horizontalDot :: forall w i. ItemProps i -> HH.HTML w i
horizontalDot props =
  let
    baseClasses = 
      "relative z-10 flex h-8 w-8 shrink-0 items-center justify-center rounded-full border-2"
    
    stateClasses = case props.state of
      Completed -> "border-primary bg-primary text-primary-foreground"
      Active -> "border-primary bg-background text-primary ring-4 ring-primary/20"
      Pending -> "border-muted-foreground/30 bg-muted text-muted-foreground"
    
    iconContent = case props.icon of
      Just i -> HH.text i
      Nothing -> case props.state of
        Completed -> HH.text "✓"
        Active -> HH.span [ cls [ "h-2 w-2 rounded-full bg-primary animate-pulse" ] ] []
        Pending -> HH.text ""
  in
    HH.div
      [ cls [ baseClasses, stateClasses ] ]
      [ iconContent ]
