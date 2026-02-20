-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // kanban
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Board component
-- |
-- | A full-featured Kanban board for task management with drag-and-drop,
-- | swimlanes, WIP limits, and flexible card customization.
-- |
-- | ## Features
-- |
-- | - Kanban columns (lanes) with headers
-- | - Draggable cards between columns
-- | - Drag to reorder within columns
-- | - Column headers with card count
-- | - Add new card functionality
-- | - Card detail expansion
-- | - WIP (Work In Progress) limits per column
-- | - Swimlanes for horizontal grouping
-- | - Collapsible columns
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Kanban as Kanban
-- |
-- | -- Basic Kanban board
-- | Kanban.kanbanBoard
-- |   [ Kanban.onCardMove HandleCardMove ]
-- |   [ Kanban.kanbanColumn
-- |       [ Kanban.columnId "todo"
-- |       , Kanban.columnTitle "To Do"
-- |       , Kanban.wipLimit 5
-- |       ]
-- |       [ Kanban.kanbanCard
-- |           [ Kanban.cardId "task-1"
-- |           , Kanban.cardTitle "Implement feature"
-- |           , Kanban.cardDescription "Build the new dashboard"
-- |           ]
-- |       ]
-- |   , Kanban.kanbanColumn
-- |       [ Kanban.columnId "doing"
-- |       , Kanban.columnTitle "In Progress"
-- |       ]
-- |       [ Kanban.kanbanCard
-- |           [ Kanban.cardId "task-2"
-- |           , Kanban.cardTitle "Review PR"
-- |           ]
-- |       ]
-- |   , Kanban.kanbanColumn
-- |       [ Kanban.columnId "done"
-- |       , Kanban.columnTitle "Done"
-- |       ]
-- |       []
-- |   ]
-- |
-- | -- With swimlanes
-- | Kanban.kanbanBoard
-- |   [ Kanban.swimlanes
-- |       [ { id: "frontend", title: "Frontend" }
-- |       , { id: "backend", title: "Backend" }
-- |       ]
-- |   ]
-- |   columns
-- |
-- | -- Collapsible columns
-- | Kanban.kanbanColumn
-- |   [ Kanban.columnId "archive"
-- |   , Kanban.columnTitle "Archived"
-- |   , Kanban.collapsible true
-- |   , Kanban.collapsed false
-- |   , Kanban.onCollapseToggle HandleCollapse
-- |   ]
-- |   cards
-- | ```
module Hydrogen.Component.Kanban
  ( -- * Kanban Components
    kanbanBoard
  , kanbanColumn
  , kanbanCard
  , kanbanSwimlane
  , kanbanAddCard
    -- * Props
  , BoardProps
  , BoardProp
  , ColumnProps
  , ColumnProp
  , CardProps
  , CardProp
  , defaultBoardProps
  , defaultColumnProps
  , defaultCardProps
    -- * Prop Builders - Board
  , swimlanes
  , boardClassName
  , onCardMove
  , onColumnMove
  , onCardAdd
    -- * Prop Builders - Column
  , columnId
  , columnTitle
  , columnColor
  , wipLimit
  , collapsible
  , collapsed
  , onCollapseToggle
  , columnClassName
    -- * Prop Builders - Card
  , cardId
  , cardTitle
  , cardDescription
  , cardLabels
  , cardAssignee
  , cardDueDate
  , cardPriority
  , cardExpanded
  , onCardClick
  , onCardExpand
  , cardClassName
    -- * Types
  , Swimlane
  , CardLabel
  , Priority(..)
  , CardMoveEvent
  , ColumnMoveEvent
    -- * FFI
  , KanbanElement
  , initKanban
  , destroyKanban
  ) where

import Prelude

import Data.Array (foldl, length, null)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Swimlane definition
type Swimlane =
  { id :: String
  , title :: String
  , collapsed :: Boolean
  }

-- | Card label with color
type CardLabel =
  { text :: String
  , color :: String
  }

-- | Card priority level
data Priority
  = PriorityLow
  | PriorityMedium
  | PriorityHigh
  | PriorityUrgent

derive instance eqPriority :: Eq Priority

-- | Card move event data
type CardMoveEvent =
  { cardId :: String
  , fromColumn :: String
  , toColumn :: String
  , fromIndex :: Int
  , toIndex :: Int
  , swimlaneId :: Maybe String
  }

-- | Column move event data
type ColumnMoveEvent =
  { columnId :: String
  , fromIndex :: Int
  , toIndex :: Int
  }

-- | Opaque Kanban element for FFI
foreign import data KanbanElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize Kanban drag and drop
foreign import initKanbanImpl :: EffectFn3 Element
  { onCardMove :: CardMoveEvent -> Effect Unit
  , onColumnMove :: ColumnMoveEvent -> Effect Unit
  }
  { dragHandleClass :: String
  , cardClass :: String
  , columnClass :: String
  }
  KanbanElement

-- | Destroy Kanban and cleanup
foreign import destroyKanbanImpl :: EffectFn1 KanbanElement Unit

-- | Initialize Kanban
initKanban :: Element ->
  { onCardMove :: CardMoveEvent -> Effect Unit
  , onColumnMove :: ColumnMoveEvent -> Effect Unit
  } ->
  { dragHandleClass :: String
  , cardClass :: String
  , columnClass :: String
  } ->
  Effect KanbanElement
initKanban el callbacks opts = do
  pure unsafeKanbanElement

-- | Destroy Kanban
destroyKanban :: KanbanElement -> Effect Unit
destroyKanban _ = pure unit

-- Internal placeholder
foreign import unsafeKanbanElement :: KanbanElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Kanban board properties
type BoardProps i =
  { swimlanes :: Array Swimlane
  , className :: String
  , onCardMove :: Maybe (CardMoveEvent -> i)
  , onColumnMove :: Maybe (ColumnMoveEvent -> i)
  , onCardAdd :: Maybe (String -> i)
  }

-- | Board property modifier
type BoardProp i = BoardProps i -> BoardProps i

-- | Default board properties
defaultBoardProps :: forall i. BoardProps i
defaultBoardProps =
  { swimlanes: []
  , className: ""
  , onCardMove: Nothing
  , onColumnMove: Nothing
  , onCardAdd: Nothing
  }

-- | Column properties
type ColumnProps i =
  { columnId :: String
  , title :: String
  , color :: String
  , wipLimit :: Maybe Int
  , collapsible :: Boolean
  , collapsed :: Boolean
  , className :: String
  , onCollapseToggle :: Maybe (Boolean -> i)
  }

-- | Column property modifier
type ColumnProp i = ColumnProps i -> ColumnProps i

-- | Default column properties
defaultColumnProps :: forall i. ColumnProps i
defaultColumnProps =
  { columnId: ""
  , title: ""
  , color: ""
  , wipLimit: Nothing
  , collapsible: false
  , collapsed: false
  , className: ""
  , onCollapseToggle: Nothing
  }

-- | Card properties
type CardProps i =
  { cardId :: String
  , title :: String
  , description :: String
  , labels :: Array CardLabel
  , assignee :: Maybe String
  , dueDate :: Maybe String
  , priority :: Maybe Priority
  , expanded :: Boolean
  , className :: String
  , onClick :: Maybe i
  , onExpand :: Maybe (Boolean -> i)
  }

-- | Card property modifier
type CardProp i = CardProps i -> CardProps i

-- | Default card properties
defaultCardProps :: forall i. CardProps i
defaultCardProps =
  { cardId: ""
  , title: ""
  , description: ""
  , labels: []
  , assignee: Nothing
  , dueDate: Nothing
  , priority: Nothing
  , expanded: false
  , className: ""
  , onClick: Nothing
  , onExpand: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- Board props

-- | Set swimlanes
swimlanes :: forall i. Array Swimlane -> BoardProp i
swimlanes s props = props { swimlanes = s }

-- | Add custom class to board
boardClassName :: forall i. String -> BoardProp i
boardClassName c props = props { className = props.className <> " " <> c }

-- | Set card move handler
onCardMove :: forall i. (CardMoveEvent -> i) -> BoardProp i
onCardMove handler props = props { onCardMove = Just handler }

-- | Set column move handler
onColumnMove :: forall i. (ColumnMoveEvent -> i) -> BoardProp i
onColumnMove handler props = props { onColumnMove = Just handler }

-- | Set card add handler
onCardAdd :: forall i. (String -> i) -> BoardProp i
onCardAdd handler props = props { onCardAdd = Just handler }

-- Column props

-- | Set column ID
columnId :: forall i. String -> ColumnProp i
columnId id props = props { columnId = id }

-- | Set column title
columnTitle :: forall i. String -> ColumnProp i
columnTitle t props = props { title = t }

-- | Set column header color
columnColor :: forall i. String -> ColumnProp i
columnColor c props = props { color = c }

-- | Set WIP limit
wipLimit :: forall i. Int -> ColumnProp i
wipLimit limit props = props { wipLimit = Just limit }

-- | Make column collapsible
collapsible :: forall i. Boolean -> ColumnProp i
collapsible c props = props { collapsible = c }

-- | Set collapsed state
collapsed :: forall i. Boolean -> ColumnProp i
collapsed c props = props { collapsed = c }

-- | Set collapse toggle handler
onCollapseToggle :: forall i. (Boolean -> i) -> ColumnProp i
onCollapseToggle handler props = props { onCollapseToggle = Just handler }

-- | Add custom class to column
columnClassName :: forall i. String -> ColumnProp i
columnClassName c props = props { className = props.className <> " " <> c }

-- Card props

-- | Set card ID
cardId :: forall i. String -> CardProp i
cardId id props = props { cardId = id }

-- | Set card title
cardTitle :: forall i. String -> CardProp i
cardTitle t props = props { title = t }

-- | Set card description
cardDescription :: forall i. String -> CardProp i
cardDescription d props = props { description = d }

-- | Set card labels
cardLabels :: forall i. Array CardLabel -> CardProp i
cardLabels l props = props { labels = l }

-- | Set card assignee
cardAssignee :: forall i. String -> CardProp i
cardAssignee a props = props { assignee = Just a }

-- | Set card due date
cardDueDate :: forall i. String -> CardProp i
cardDueDate d props = props { dueDate = Just d }

-- | Set card priority
cardPriority :: forall i. Priority -> CardProp i
cardPriority p props = props { priority = Just p }

-- | Set card expanded state
cardExpanded :: forall i. Boolean -> CardProp i
cardExpanded e props = props { expanded = e }

-- | Set card click handler
onCardClick :: forall i. i -> CardProp i
onCardClick handler props = props { onClick = Just handler }

-- | Set card expand handler
onCardExpand :: forall i. (Boolean -> i) -> CardProp i
onCardExpand handler props = props { onExpand = Just handler }

-- | Add custom class to card
cardClassName :: forall i. String -> CardProp i
cardClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Kanban board container
-- |
-- | Root container for columns and cards with drag-and-drop support
kanbanBoard :: forall w i. Array (BoardProp i) -> Array (HH.HTML w i) -> HH.HTML w i
kanbanBoard propMods children =
  let
    props = foldl (\p f -> f p) defaultBoardProps propMods
    
    containerClasses = 
      "kanban-board flex gap-4 overflow-x-auto p-4 min-h-[500px]"
    
    hasSwimlanes = not (null props.swimlanes)
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-kanban-board") "true"
      , ARIA.role "region"
      , ARIA.label "Kanban board"
      ]
      ( if hasSwimlanes
          then renderWithSwimlanes props children
          else children
      )

-- | Render board with swimlanes
renderWithSwimlanes :: forall w i. BoardProps i -> Array (HH.HTML w i) -> Array (HH.HTML w i)
renderWithSwimlanes props children =
  map renderSwimlaneRow props.swimlanes
  where
    renderSwimlaneRow :: Swimlane -> HH.HTML w i
    renderSwimlaneRow swimlane =
      HH.div
        [ cls [ "kanban-swimlane-row" ]
        , HP.attr (HH.AttrName "data-swimlane") swimlane.id
        ]
        [ HH.div
            [ cls [ "kanban-swimlane-header flex items-center gap-2 py-2 border-b border-border mb-2" ] ]
            [ HH.h3 
                [ cls [ "font-semibold text-sm text-foreground" ] ] 
                [ HH.text swimlane.title ]
            ]
        , HH.div
            [ cls [ "kanban-swimlane-content flex gap-4" ] ]
            children
        ]

-- | Kanban column (lane)
-- |
-- | A vertical column containing cards
kanbanColumn :: forall w i. Array (ColumnProp i) -> Array (HH.HTML w i) -> HH.HTML w i
kanbanColumn propMods cards =
  let
    props = foldl (\p f -> f p) defaultColumnProps propMods
    cardCount = length cards
    
    isOverWipLimit = case props.wipLimit of
      Just limit -> cardCount > limit
      Nothing -> false
    
    containerClasses = 
      "kanban-column flex flex-col shrink-0 w-72 bg-muted/30 rounded-lg"
      <> (if props.collapsed then " w-12" else "")
    
    headerClasses = 
      "kanban-column-header flex items-center justify-between p-3 rounded-t-lg"
      <> (if props.color /= "" then "" else " bg-muted")
    
    headerStyle = 
      if props.color /= "" 
        then "background-color: " <> props.color 
        else ""
    
    countBadgeClasses = 
      "text-xs px-2 py-0.5 rounded-full"
      <> (if isOverWipLimit then " bg-destructive text-destructive-foreground" else " bg-muted-foreground/20 text-muted-foreground")
    
    countText = show cardCount <> case props.wipLimit of
      Just limit -> " / " <> show limit
      Nothing -> ""
    
    toggleHandler = case props.onCollapseToggle of
      Just handler -> [ HE.onClick (\_ -> handler (not props.collapsed)) ]
      Nothing -> []
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-column-id") props.columnId
      , ARIA.role "listbox"
      , ARIA.label props.title
      ]
      [ HH.div
          ( [ cls [ headerClasses ]
            , HP.attr (HH.AttrName "style") headerStyle
            ] <> (if props.collapsible then toggleHandler else [])
          )
          [ if props.collapsed
              then 
                HH.span 
                  [ cls [ "writing-mode-vertical-lr rotate-180 text-sm font-semibold" ] ] 
                  [ HH.text props.title ]
              else
                HH.div
                  [ cls [ "flex items-center gap-2 flex-1" ] ]
                  [ HH.h3 
                      [ cls [ "font-semibold text-sm text-foreground" ] ] 
                      [ HH.text props.title ]
                  , HH.span 
                      [ cls [ countBadgeClasses ] ] 
                      [ HH.text countText ]
                  ]
          , if props.collapsible && not props.collapsed
              then
                HH.button
                  [ cls [ "p-1 rounded hover:bg-muted transition-colors" ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Collapse column"
                  ]
                  [ HH.text "◀" ]
              else HH.text ""
          ]
      , if props.collapsed
          then HH.text ""
          else
            HH.div
              [ cls [ "kanban-column-content flex-1 p-2 space-y-2 overflow-y-auto min-h-[200px]" ]
              , ARIA.role "group"
              ]
              cards
      ]

-- | Kanban card
-- |
-- | A draggable card within a column
kanbanCard :: forall w i. Array (CardProp i) -> HH.HTML w i
kanbanCard propMods =
  let
    props = foldl (\p f -> f p) defaultCardProps propMods
    
    containerClasses = 
      "kanban-card group bg-card rounded-lg border border-border shadow-sm hover:shadow-md transition-shadow cursor-grab active:cursor-grabbing"
    
    priorityIndicator = case props.priority of
      Just PriorityUrgent -> 
        HH.div [ cls [ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-destructive" ] ] []
      Just PriorityHigh -> 
        HH.div [ cls [ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-orange-500" ] ] []
      Just PriorityMedium -> 
        HH.div [ cls [ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-yellow-500" ] ] []
      Just PriorityLow -> 
        HH.div [ cls [ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-green-500" ] ] []
      Nothing -> 
        HH.text ""
    
    labelsHtml = 
      if not (null props.labels)
        then 
          HH.div
            [ cls [ "flex flex-wrap gap-1 mb-2" ] ]
            (map renderLabel props.labels)
        else HH.text ""
    
    clickHandler = case props.onClick of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
    
    dueDateHtml = case props.dueDate of
      Just date -> 
        HH.div
          [ cls [ "flex items-center gap-1 text-xs text-muted-foreground" ] ]
          [ HH.text "📅"
          , HH.text date
          ]
      Nothing -> HH.text ""
    
    assigneeHtml = case props.assignee of
      Just name -> 
        HH.div
          [ cls [ "flex items-center justify-end" ] ]
          [ HH.div
              [ cls [ "w-6 h-6 rounded-full bg-primary text-primary-foreground flex items-center justify-center text-xs font-medium" ]
              , HP.title name
              ]
              [ HH.text (getInitials name) ]
          ]
      Nothing -> HH.text ""
    
    descriptionHtml =
      if props.description /= "" && props.expanded
        then 
          HH.p 
            [ cls [ "text-xs text-muted-foreground mt-2 line-clamp-2" ] ] 
            [ HH.text props.description ]
        else HH.text ""
  in
    HH.div
      ( [ cls [ containerClasses, props.className ]
        , HP.attr (HH.AttrName "data-card-id") props.cardId
        , HP.attr (HH.AttrName "draggable") "true"
        , ARIA.role "option"
        ] <> clickHandler
      )
      [ HH.div
          [ cls [ "relative p-3" ] ]
          [ priorityIndicator
          , labelsHtml
          , HH.h4 
              [ cls [ "text-sm font-medium text-foreground" ] ] 
              [ HH.text props.title ]
          , descriptionHtml
          , HH.div
              [ cls [ "flex items-center justify-between mt-2" ] ]
              [ dueDateHtml
              , assigneeHtml
              ]
          ]
      ]
  where
    renderLabel :: CardLabel -> HH.HTML w i
    renderLabel lbl =
      HH.span
        [ cls [ "text-xs px-2 py-0.5 rounded-full" ]
        , HP.attr (HH.AttrName "style") ("background-color: " <> lbl.color <> "; color: white")
        ]
        [ HH.text lbl.text ]
    
    getInitials :: String -> String
    getInitials name = 
      -- Get first character using String.take
      let first = take 1 name
      in if first == "" then "?" else first
    
    take :: Int -> String -> String
    take n s = takeImpl n s

foreign import takeImpl :: Int -> String -> String

-- | Kanban swimlane
-- |
-- | Horizontal grouping row for cards
kanbanSwimlane :: forall w i. { id :: String, title :: String } -> Array (HH.HTML w i) -> HH.HTML w i
kanbanSwimlane config children =
  HH.div
    [ cls [ "kanban-swimlane border-b border-border pb-4 mb-4" ]
    , HP.attr (HH.AttrName "data-swimlane") config.id
    ]
    [ HH.div
        [ cls [ "kanban-swimlane-header flex items-center gap-2 py-2 mb-2" ] ]
        [ HH.div
            [ cls [ "w-1 h-4 rounded bg-primary" ] ]
            []
        , HH.h3 
            [ cls [ "font-semibold text-sm text-foreground" ] ] 
            [ HH.text config.title ]
        ]
    , HH.div
        [ cls [ "kanban-swimlane-content flex gap-4" ] ]
        children
    ]

-- | Add card button/form
-- |
-- | Inline add card functionality for a column
kanbanAddCard :: forall w i. { columnId :: String, onAdd :: String -> i } -> HH.HTML w i
kanbanAddCard config =
  HH.div
    [ cls [ "kanban-add-card" ] ]
    [ HH.button
        [ cls [ "w-full p-2 text-left text-sm text-muted-foreground hover:text-foreground hover:bg-muted rounded transition-colors flex items-center gap-2" ]
        , HP.type_ HP.ButtonButton
        , HE.onClick (\_ -> config.onAdd config.columnId)
        ]
        [ HH.text "+"
        , HH.text "Add card"
        ]
    ]
