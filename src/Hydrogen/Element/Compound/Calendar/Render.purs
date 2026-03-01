-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // calendar // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Render — Element rendering functions.
-- |
-- | This module provides the rendering logic that transforms CalendarProps
-- | into Hydrogen Elements. Pure functions, no side effects.

module Hydrogen.Element.Compound.Calendar.Render
  ( -- * Main Components
    calendar
  , calendarWithNav
  ) where

import Prelude
  ( map
  , not
  , otherwise
  , show
  , (&&)
  , (<>)
  , (==)
  , (>=)
  , (<)
  , (||)
  )

import Data.Array (foldl)
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry

import Hydrogen.Element.Compound.Calendar.Types
  ( CalendarDate
  , MonthDay(DayEmpty, DayDate)
  , MonthWeek
  , MonthGrid
  , SelectionMode(Single, Range, Multiple)
  , WeekStart(Sunday, Monday)
  , Locale(EnUS)
  )
import Hydrogen.Element.Compound.Calendar.Props
  ( CalendarProps
  , CalendarProp
  , defaultProps
  )
import Hydrogen.Element.Compound.Calendar.DateOps
  ( compareDates
  , sameDate
  )
import Hydrogen.Element.Compound.Calendar.Grid
  ( buildMonthGrid
  )
import Hydrogen.Element.Compound.Calendar.Locale
  ( monthName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a calendar
calendar :: forall msg. Array (CalendarProp msg) -> E.Element msg
calendar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    renderCalendarContainer props
      [ renderHeader props
      , renderDayHeaders props
      , renderWeeks props grid
      ]

-- | Render calendar with navigation controls
calendarWithNav :: forall msg. Array (CalendarProp msg) -> E.Element msg
calendarWithNav propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    renderCalendarContainer props
      [ renderNavHeader props
      , renderDayHeaders props
      , renderWeeks props grid
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // containers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the calendar container
renderCalendarContainer :: forall msg. CalendarProps msg -> Array (E.Element msg) -> E.Element msg
renderCalendarContainer props children =
  let
    bgStyle = maybe "" Color.toLegacyCss props.backgroundColor
    brdrColor = maybe "" Color.toLegacyCss props.borderColor
    radiusStyle = maybe "" Geometry.toLegacyCss props.borderRadius
    padStyle = maybe "" show props.padding
    brdrWidth = maybe "" show props.borderWidth
  in
    E.div_
      ( [ E.attr "role" "grid"
        , E.attr "aria-label" "Calendar"
        , E.style "display" "flex"
        , E.style "flex-direction" "column"
        ] <> maybeStyle "background-color" bgStyle
          <> maybeStyle "border-color" brdrColor
          <> maybeStyle "border-radius" radiusStyle
          <> maybeStyle "padding" padStyle
          <> maybeStyle "border-width" brdrWidth
          <> (if brdrWidth == "" then [] else [ E.style "border-style" "solid" ])
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // headers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the month/year header (without navigation)
renderHeader :: forall msg. CalendarProps msg -> E.Element msg
renderHeader props =
  let
    hdrColor = maybe "" Color.toLegacyCss props.headerColor
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "justify-content" "center"
        , E.style "padding-top" "4px"
        , E.style "align-items" "center"
        ] <> maybeStyle "color" hdrColor
      )
      [ E.div_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          ]
          [ E.text (monthName EnUS props.viewMonth <> " " <> show props.viewYear) ]
      ]

-- | Render navigation header with prev/next buttons
renderNavHeader :: forall msg. CalendarProps msg -> E.Element msg
renderNavHeader props =
  let
    hdrColor = maybe "" Color.toLegacyCss props.headerColor
    navColor = maybe "" Color.toLegacyCss props.navButtonColor
    navRadius = maybe "" Geometry.toLegacyCss props.navButtonRadius
    cSize = maybe "36px" show props.cellSize
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "justify-content" "space-between"
        , E.style "align-items" "center"
        , E.style "padding" "4px 8px 8px 8px"
        ] <> maybeStyle "color" hdrColor
      )
      [ -- Previous month button
        renderNavButton props.onPrevMonth navColor navRadius cSize (E.text "\x2039")
      , -- Month/Year display
        E.div_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          ]
          [ E.text (monthName EnUS props.viewMonth <> " " <> show props.viewYear) ]
      , -- Next month button
        renderNavButton props.onNextMonth navColor navRadius cSize (E.text "\x203a")
      ]

-- | Render a navigation button
renderNavButton :: forall msg. Maybe msg -> String -> String -> String -> E.Element msg -> E.Element msg
renderNavButton handler colorStyle radiusStyle sizeStyle content =
  E.button_
    ( [ E.attr "type" "button"
      , E.style "width" sizeStyle
      , E.style "height" sizeStyle
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "font-size" "18px"
      ] <> maybeStyle "color" colorStyle
        <> maybeStyle "border-radius" radiusStyle
        <> case handler of
             Just msg -> [ E.onClick msg ]
             Nothing -> [ E.attr "disabled" "true" ]
    )
    [ content ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // day headers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render day-of-week headers
renderDayHeaders :: forall msg. CalendarProps msg -> E.Element msg
renderDayHeaders props =
  let
    baseDays = ["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"]
    days = case props.weekStartsOn of
      Sunday -> baseDays
      Monday -> rotateArray 1 baseDays
    dayHdrColor = maybe "" Color.toLegacyCss props.dayHeaderColor
    cSize = maybe "36px" show props.cellSize
  in
    E.div_
      [ E.attr "role" "row"
      , E.style "display" "flex"
      ]
      ( (if props.showWeekNumbers then [ renderWeekNumHeader dayHdrColor cSize ] else [])
        <> map (renderDayHeader dayHdrColor cSize) days
      )

-- | Render week number column header
renderWeekNumHeader :: forall msg. String -> String -> E.Element msg
renderWeekNumHeader colorStyle sizeStyle =
  E.div_
    ( [ E.style "width" sizeStyle
      , E.style "font-size" "12px"
      , E.style "text-align" "center"
      , E.style "font-weight" "400"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      ] <> maybeStyle "color" colorStyle
    )
    [ E.text "#" ]

-- | Render a day header
renderDayHeader :: forall msg. String -> String -> String -> E.Element msg
renderDayHeader colorStyle sizeStyle day =
  E.div_
    ( [ E.attr "role" "columnheader"
      , E.style "width" sizeStyle
      , E.style "font-size" "12px"
      , E.style "text-align" "center"
      , E.style "font-weight" "400"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      ] <> maybeStyle "color" colorStyle
    )
    [ E.text day ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // weeks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render all weeks
renderWeeks :: forall msg. CalendarProps msg -> MonthGrid -> E.Element msg
renderWeeks props grid =
  let
    gapStyle = maybe "" show props.gap
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        ] <> maybeStyle "gap" gapStyle
      )
      (map (renderWeek props) grid.weeks)

-- | Render a single week
renderWeek :: forall msg. CalendarProps msg -> MonthWeek -> E.Element msg
renderWeek props week =
  E.div_
    [ E.attr "role" "row"
    , E.style "display" "flex"
    ]
    ( (if props.showWeekNumbers then [ renderWeekNumber props week.weekNumber ] else [])
      <> map (renderDay props) week.days
    )

-- | Render week number
renderWeekNumber :: forall msg. CalendarProps msg -> Int -> E.Element msg
renderWeekNumber props num =
  let
    cSize = maybe "36px" show props.cellSize
    dayHdrColor = maybe "" Color.toLegacyCss props.dayHeaderColor
  in
    E.div_
      ( [ E.style "width" cSize
        , E.style "font-size" "12px"
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        ] <> maybeStyle "color" dayHdrColor
      )
      [ E.text (show num) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // days
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single day cell
renderDay :: forall msg. CalendarProps msg -> MonthDay -> E.Element msg
renderDay props day = case day of
  DayEmpty -> renderEmptyCell props
  DayDate date -> renderDateCell props date

-- | Render an empty day cell
renderEmptyCell :: forall msg. CalendarProps msg -> E.Element msg
renderEmptyCell props =
  let
    cSize = maybe "36px" show props.cellSize
  in
    E.div_
      [ E.style "width" cSize
      , E.style "height" cSize
      ]
      []

-- | Render a date cell
renderDateCell :: forall msg. CalendarProps msg -> CalendarDate -> E.Element msg
renderDateCell props date =
  let
    isDisabled = isDateDisabledProp props date
    isSelected = isDateSelected props date
    isInRange = isDateInSelectedRange props date
    isRangeStartDate = isDateRangeStart props date
    isRangeEndDate = isDateRangeEnd props date
    
    cSize = maybe "36px" show props.cellSize
    cellRadius = maybe "" Geometry.toLegacyCss props.dayCellRadius
    
    -- Determine colors based on state
    bgColor
      | isSelected = maybe "" Color.toLegacyCss props.selectedColor
      | isInRange = maybe "" Color.toLegacyCss props.rangeColor
      | otherwise = ""
    
    txtColor
      | isDisabled = maybe "" Color.toLegacyCss props.disabledColor
      | isSelected = maybe "" Color.toLegacyCss props.selectedTextColor
      | otherwise = maybe "" Color.toLegacyCss props.textColor
    
    -- Border radius adjustments for range
    radiusStyle
      | isRangeStartDate && isRangeEndDate = cellRadius
      | isRangeStartDate = cellRadius <> " 0 0 " <> cellRadius
      | isRangeEndDate = "0 " <> cellRadius <> " " <> cellRadius <> " 0"
      | isInRange = "0"
      | otherwise = cellRadius
    
    cursorStyle
      | isDisabled = "not-allowed"
      | otherwise = "pointer"
    
    opacityStyle
      | isDisabled = "0.5"
      | otherwise = "1"
  in
    E.button_
      ( [ E.attr "type" "button"
        , E.attr "role" "gridcell"
        , E.style "width" cSize
        , E.style "height" cSize
        , E.style "border" "none"
        , E.style "font-size" "14px"
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "cursor" cursorStyle
        , E.style "opacity" opacityStyle
        ] <> maybeStyle "background-color" bgColor
          <> maybeStyle "color" txtColor
          <> maybeStyle "border-radius" radiusStyle
          <> (if isDisabled then [ E.attr "disabled" "true" ] else [])
          <> (if isDisabled then [] else
                case props.onSelect of
                  Just handler -> [ E.onClick (handler date) ]
                  Nothing -> [])
      )
      [ E.text (show date.day) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a date is within a range (inclusive)
isDateInRange :: CalendarDate -> Maybe CalendarDate -> Maybe CalendarDate -> Boolean
isDateInRange date minD maxD =
  let
    afterMin = case minD of
      Nothing -> true
      Just minVal -> compareDates date minVal >= 0
    beforeMax = case maxD of
      Nothing -> true
      Just maxVal -> compareDates date maxVal < 1
  in afterMin && beforeMax

-- | Check if date is disabled based on props
isDateDisabledProp :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateDisabledProp props date =
  props.disabledDates date || not (isDateInRange date props.minDate props.maxDate)

-- | Check if date is selected
isDateSelected :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateSelected props date = case props.selectionMode of
  Single -> case props.selected of
    Just sel -> sameDate date sel
    Nothing -> false
  Range ->
    (case props.rangeStart of
      Just start -> sameDate date start
      Nothing -> false)
    ||
    (case props.rangeEnd of
      Just end -> sameDate date end
      Nothing -> false)
  Multiple -> Array.any (sameDate date) props.multiSelected

-- | Check if date is within selected range
isDateInSelectedRange :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateInSelectedRange props date = case props.selectionMode of
  Range -> case props.rangeStart, props.rangeEnd of
    Just start, Just end ->
      compareDates date start >= 0 && compareDates date end < 1
    _, _ -> false
  _ -> false

-- | Check if date is range start
isDateRangeStart :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateRangeStart props date = case props.rangeStart of
  Just start -> sameDate date start
  Nothing -> false

-- | Check if date is range end
isDateRangeEnd :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateRangeEnd props date = case props.rangeEnd of
  Just end -> sameDate date end
  Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate an array by n positions
rotateArray :: forall a. Int -> Array a -> Array a
rotateArray n arr = Array.drop n arr <> Array.take n arr

-- | Helper to add style only if value is non-empty
maybeStyle :: forall msg. String -> String -> Array (E.Attribute msg)
maybeStyle _ "" = []
maybeStyle prop val = [ E.style prop val ]
