-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // kanban // render // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Card Render — Pure Element rendering for Kanban cards.
-- |
-- | ## Design Philosophy
-- |
-- | Cards are the atomic units of a Kanban board. This module provides pure
-- | render functions for cards, including priority indicators, labels,
-- | assignee avatars, and drag preview states.
-- |
-- | All styling uses Schema atoms — no CSS strings, no Tailwind classes.

module Hydrogen.Element.Compound.Kanban.Render.Card
  ( -- * Card Render Functions
    renderCard
  , renderCardWithStyles
  , renderCardWithSelection
  , renderDragPreview
  
  -- * Card Parts
  , renderPriorityIndicator
  , renderCardLabels
  , renderCardFooter
  , renderAssigneeAvatar
  , renderCardActions
  
  -- * Utilities
  , priorityToColor
  ) where

import Prelude
  ( const
  , map
  , not
  , show
  , (&&)
  , (<>)
  , (==)
  , (/=)
  )

import Data.Array (foldl, null)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry

import Hydrogen.Element.Compound.Kanban.Types
  ( CardId
  , KanbanMsg
      ( RemoveCard
      , ExpandCard
      , CollapseCard
      , BeginDrag
      , EndDrag
      , CancelDrag
      , SelectCard
      )
  , Priority(PriorityLow, PriorityMedium, PriorityHigh, PriorityUrgent)
  , unwrapCardId
  )
import Hydrogen.Element.Compound.Kanban.Card
  ( KanbanCard
  , CardLabel
  , Assignee
  , cardIdOf
  , cardTitle
  , cardDescription
  , cardLabels
  , cardAssignee
  , cardDueDate
  , cardPriority
  , cardExpanded
  , labelText
  , labelColor
  , assigneeName
  , assigneeAvatar
  , assigneeInitials
  , formatDueDate
  )
import Hydrogen.Element.Compound.Kanban.State
  ( KanbanState
  , getDraggedCard
  , getSelectedCard
  )
import Hydrogen.Element.Compound.Kanban.Render.Config
  ( KanbanConfig
  , KanbanProp
  , defaultConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // card render state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a card with selection state awareness
-- |
-- | Applies visual feedback for:
-- | - Selected cards (highlighted border)
-- | - Cards being dragged (reduced opacity)
renderCardWithSelection :: KanbanConfig -> KanbanState -> KanbanCard -> E.Element KanbanMsg
renderCardWithSelection cfg state card =
  let
    cId = cardIdOf card
    isSelected = getSelectedCard state == Just cId
    isBeingDragged = getDraggedCard state == Just cId
    
    -- Build selection/drag styles
    selectionStyles = 
      if isBeingDragged
        then [ Tuple "opacity" "0.5" ]
        else if isSelected
          then [ Tuple "border-color" (Color.toHex cfg.selectedColor)
               , Tuple "box-shadow" ("0 0 0 2px " <> Color.toHex cfg.selectedColor)
               ]
          else []
  in
    renderCardWithStyles cfg card selectionStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // card render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single card (without selection state)
-- |
-- | Event handlers:
-- | - onClick: SelectCard (single click selects)
-- | - onDoubleClick: ExpandCard/CollapseCard (toggle details)
-- | - onDragStart: BeginDrag (start drag operation)
-- | - onDragEnd: EndDrag (complete drag operation)
-- | - onKeyDown: CancelDrag on Escape, DeselectCard on Escape when not dragging
renderCard :: KanbanConfig -> KanbanCard -> E.Element KanbanMsg
renderCard cfg card = renderCardWithStyles cfg card []

-- | Render a card with additional styles for selection/drag feedback
-- |
-- | This is the core card renderer that accepts extra styles for:
-- | - Selection highlighting (border, box-shadow)
-- | - Drag feedback (opacity)
renderCardWithStyles :: KanbanConfig -> KanbanCard -> Array (Tuple String String) -> E.Element KanbanMsg
renderCardWithStyles cfg card extraStyles =
  let
    cId = cardIdOf card
    priority = cardPriority card
    pColor = priorityToColor cfg priority
    labels = cardLabels card
    hasLabels = not (null labels)
    isExpanded = cardExpanded card
    desc = cardDescription card
    hasDesc = desc /= ""
    
    -- Click message: use custom callback or default to SelectCard
    clickMsg = case cfg.onCardClick of
      Just f -> f cId
      Nothing -> SelectCard cId
    
    -- Expand/collapse message: use custom callback or default messages
    -- onCardExpand receives the card ID and the NEW expanded state
    toggleExpandMsg = case cfg.onCardExpand of
      Just f -> f cId (not isExpanded)  -- Pass the new state (toggled)
      Nothing -> if isExpanded then CollapseCard cId else ExpandCard cId
    
    -- Keyboard handler: Escape cancels drag, Enter expands, other keys ignored
    -- Using const to create a handler that returns the same message regardless
    -- of key for unrecognized keys (re-selecting the current card is a no-op)
    handleKeyDown key = 
      if key == "Escape" then CancelDrag 
      else if key == "Enter" then toggleExpandMsg
      else const clickMsg key  -- Ignore other keys, keep selection
    
    -- Base card styles
    -- Note: hoverColor is included as a data attribute for the runtime.
    -- The runtime reads this value and applies it during hover state.
    -- This keeps rendering pure — we describe WHAT the hover color IS,
    -- not HOW to apply it (that's the runtime's job).
    baseStyles = 
      [ Tuple "position" "relative"
      , Tuple "padding" (show cfg.cardPadding)
      , Tuple "background-color" (Color.toHex cfg.cardBackgroundColor)
      , Tuple "border-radius" (Geometry.toLegacyCss cfg.cardRadius)
      , Tuple "border" ("1px solid " <> Color.toHex cfg.borderColor)
      , Tuple "cursor" "grab"
      , Tuple "box-shadow" "0 1px 3px rgba(0,0,0,0.1)"
      -- Hover color as data for runtime state management
      , Tuple "--hydrogen-hover-bg" (Color.toHex cfg.hoverColor)
      ]
  in
    E.div_
      ([ E.role "option"
       , E.attr "data-card-id" (unwrapCardId cId)
       , E.attr "draggable" "true"
       , E.attr "tabindex" "0"  -- Make focusable for keyboard events
       -- Click handlers: use config callbacks if provided
       , E.onClick clickMsg
       , E.onDoubleClick toggleExpandMsg
       -- Drag handlers
       , E.onDragStart (BeginDrag cId)
       , E.onDragEnd EndDrag
       -- Keyboard handler
       , E.onKeyDown handleKeyDown
       ] <> E.styles (baseStyles <> extraStyles))
      [ -- Priority indicator
        renderPriorityIndicator cfg.cardRadius pColor
      , -- Labels
        if hasLabels then renderCardLabels labels else E.empty
      , -- Title
        E.h4_
          (E.styles
              [ Tuple "font-size" "14px"
              , Tuple "font-weight" "500"
              , Tuple "color" (Color.toHex cfg.textColor)
              , Tuple "margin" "0"
              ])
          [ E.text (cardTitle card) ]
      , -- Description (if expanded)
        if isExpanded && hasDesc
          then
            E.p_
              (E.styles
                  [ Tuple "font-size" "12px"
                  , Tuple "color" (Color.toHex cfg.mutedTextColor)
                  , Tuple "margin" "8px 0 0 0"
                  ])
              [ E.text desc ]
          else E.empty
      , -- Footer (due date, assignee)
        renderCardFooter cfg card
      , -- Actions (delete button, shown when expanded)
        if isExpanded
          then renderCardActions cfg cId
          else E.empty
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // card parts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render priority indicator bar
renderPriorityIndicator :: Geometry.Radius -> Color.RGB -> E.Element KanbanMsg
renderPriorityIndicator radius color =
  E.div_
    (E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" "0"
        , Tuple "top" "0"
        , Tuple "bottom" "0"
        , Tuple "width" "4px"
        , Tuple "background-color" (Color.toHex color)
        , Tuple "border-radius" (Geometry.toLegacyCss radius <> " 0 0 " <> Geometry.toLegacyCss radius)
        ])
    []

-- | Get priority color from config
priorityToColor :: KanbanConfig -> Priority -> Color.RGB
priorityToColor cfg PriorityLow = cfg.priorityLowColor
priorityToColor cfg PriorityMedium = cfg.priorityMediumColor
priorityToColor cfg PriorityHigh = cfg.priorityHighColor
priorityToColor cfg PriorityUrgent = cfg.priorityUrgentColor

-- | Render card labels
renderCardLabels :: Array CardLabel -> E.Element KanbanMsg
renderCardLabels labels =
  E.div_
    (E.styles
        [ Tuple "display" "flex"
        , Tuple "flex-wrap" "wrap"
        , Tuple "gap" "4px"
        , Tuple "margin-bottom" "8px"
        ])
    (map renderLabel labels)
  where
    renderLabel :: CardLabel -> E.Element KanbanMsg
    renderLabel lbl =
      E.span_
        (E.styles
            [ Tuple "font-size" "12px"
            , Tuple "padding" "2px 8px"
            , Tuple "border-radius" "9999px"
            , Tuple "background-color" (Color.toHex (labelColor lbl))
            , Tuple "color" "white"
            ])
        [ E.text (labelText lbl) ]

-- | Render card footer (due date, assignee)
renderCardFooter :: KanbanConfig -> KanbanCard -> E.Element KanbanMsg
renderCardFooter cfg card =
  let
    mDueDate = cardDueDate card
    mAssignee = cardAssignee card
    hasDueDate = case mDueDate of
      Just _ -> true
      Nothing -> false
    hasAssignee = case mAssignee of
      Just _ -> true
      Nothing -> false
  in
    if not hasDueDate && not hasAssignee
      then E.empty
      else
        E.div_
          (E.styles
              [ Tuple "display" "flex"
              , Tuple "align-items" "center"
              , Tuple "justify-content" "space-between"
              , Tuple "margin-top" "8px"
              ])
          [ -- Due date
            case mDueDate of
              Just dd ->
                E.div_
                  (E.styles
                      [ Tuple "display" "flex"
                      , Tuple "align-items" "center"
                      , Tuple "gap" "4px"
                      , Tuple "font-size" "12px"
                      , Tuple "color" (Color.toHex cfg.mutedTextColor)
                      ])
                  [ E.text (formatDueDate dd) ]
              Nothing -> E.empty
          , -- Assignee avatar (image if available, initials fallback)
            case mAssignee of
              Just a -> renderAssigneeAvatar cfg a
              Nothing -> E.empty
          ]

-- | Render assignee avatar
-- |
-- | Uses avatar image URL if available, otherwise shows initials.
-- | This implements the full Assignee type: name, avatar, initials.
renderAssigneeAvatar :: KanbanConfig -> Assignee -> E.Element KanbanMsg
renderAssigneeAvatar cfg a =
  case assigneeAvatar a of
    Just avatarUrl ->
      -- Render image avatar
      E.img_
        ([ E.src avatarUrl
         , E.alt (assigneeName a)
         , E.title (assigneeName a)
         ] <> E.styles
            [ Tuple "width" "24px"
            , Tuple "height" "24px"
            , Tuple "border-radius" "9999px"
            , Tuple "object-fit" "cover"
            ])
    Nothing ->
      -- Render initials fallback
      E.div_
        ([ E.title (assigneeName a) ] <> E.styles
            [ Tuple "width" "24px"
            , Tuple "height" "24px"
            , Tuple "border-radius" "9999px"
            , Tuple "background-color" (Color.toHex cfg.selectedColor)
            , Tuple "color" (Color.toHex cfg.textColor)
            , Tuple "display" "flex"
            , Tuple "align-items" "center"
            , Tuple "justify-content" "center"
            , Tuple "font-size" "12px"
            , Tuple "font-weight" "500"
            ])
        [ E.text (assigneeInitials a) ]

-- | Render card actions (delete button)
-- |
-- | Actions are shown when the card is expanded. The delete button
-- | emits a RemoveCard message to remove the card from the board.
renderCardActions :: KanbanConfig -> CardId -> E.Element KanbanMsg
renderCardActions cfg cId =
  E.div_
    (E.styles
        [ Tuple "display" "flex"
        , Tuple "justify-content" "flex-end"
        , Tuple "margin-top" "8px"
        , Tuple "padding-top" "8px"
        , Tuple "border-top" ("1px solid " <> Color.toHex cfg.borderColor)
        ])
    [ E.button_
        ([ E.type_ "button"
         , E.ariaLabel "Delete card"
         , E.onClick (RemoveCard cId)
         ] <> E.styles
            [ Tuple "padding" "4px 8px"
            , Tuple "font-size" "12px"
            , Tuple "color" (Color.toHex cfg.priorityUrgentColor)
            , Tuple "background" "transparent"
            , Tuple "border" ("1px solid " <> Color.toHex cfg.priorityUrgentColor)
            , Tuple "border-radius" "4px"
            , Tuple "cursor" "pointer"
            ])
        [ E.text "Delete" ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drag preview
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render drag preview
renderDragPreview :: Array KanbanProp -> KanbanCard -> Number -> Number -> E.Element KanbanMsg
renderDragPreview props card x y =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
  in
    E.div_
      (E.styles
          [ Tuple "position" "fixed"
          , Tuple "left" (show x <> "px")
          , Tuple "top" (show y <> "px")
          , Tuple "width" (show cfg.columnWidth)
          , Tuple "opacity" "0.8"
          , Tuple "pointer-events" "none"
          , Tuple "z-index" "1000"
          , Tuple "transform" "rotate(3deg)"
          ])
      [ renderCard cfg card ]
