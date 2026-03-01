-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // compound // calendar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar — Schema-native date selection component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms. It renders a monthly
-- | calendar grid with navigation and date selection capabilities.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property               | Pillar     | Type                      | CSS Output              |
-- | |------------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor        | Color      | Color.RGB                 | calendar background     |
-- | | borderColor            | Color      | Color.RGB                 | calendar border         |
-- | | textColor              | Color      | Color.RGB                 | default text color      |
-- | | headerColor            | Color      | Color.RGB                 | month/year header       |
-- | | dayHeaderColor         | Color      | Color.RGB                 | day name headers        |
-- | | selectedColor          | Color      | Color.RGB                 | selected date bg        |
-- | | selectedTextColor      | Color      | Color.RGB                 | selected date text      |
-- | | rangeColor             | Color      | Color.RGB                 | date range bg           |
-- | | todayRingColor         | Color      | Color.RGB                 | today indicator ring    |
-- | | hoverColor             | Color      | Color.RGB                 | hover background        |
-- | | disabledColor          | Color      | Color.RGB                 | disabled date color     |
-- | | borderRadius           | Geometry   | Geometry.Radius           | calendar rounding       |
-- | | dayCellRadius          | Geometry   | Geometry.Radius           | day cell rounding       |
-- | | padding                | Dimension  | Device.Pixel              | internal padding        |
-- | | cellSize               | Dimension  | Device.Pixel              | day cell size           |
-- | | gap                    | Dimension  | Device.Pixel              | spacing between weeks   |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Calendar as Calendar
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic calendar
-- | Calendar.calendar
-- |   [ Calendar.viewMonth 3
-- |   , Calendar.viewYear 2026
-- |   , Calendar.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- With selected date and brand colors
-- | Calendar.calendar
-- |   [ Calendar.viewMonth state.month
-- |   , Calendar.viewYear state.year
-- |   , Calendar.selected (Just state.selectedDate)
-- |   , Calendar.selectedColor brand.primaryColor
-- |   , Calendar.selectedTextColor brand.onPrimaryColor
-- |   , Calendar.borderRadius brand.containerRadius
-- |   , Calendar.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- Date range selection
-- | Calendar.calendar
-- |   [ Calendar.selectionMode Calendar.Range
-- |   , Calendar.rangeStart state.startDate
-- |   , Calendar.rangeEnd state.endDate
-- |   , Calendar.rangeColor brand.primaryColorLight
-- |   , Calendar.onRangeSelect HandleRangeSelect
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `Calendar.Types` — Core type definitions
-- | - `Calendar.Props` — Property types and builders
-- | - `Calendar.DateOps` — Pure date arithmetic
-- | - `Calendar.Grid` — Month grid building
-- | - `Calendar.Locale` — Internationalization
-- | - `Calendar.Render` — Element rendering

module Hydrogen.Element.Compound.Calendar
  ( module ReExports
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Calendar.Types
  ( CalendarDate
  , DateRange
  , SelectionMode(Single, Range, Multiple)
  , WeekStart(Sunday, Monday)
  , MonthDay(DayEmpty, DayDate)
  , MonthWeek
  , MonthGrid
  , Locale(EnUS, EnGB, De, Fr, Es, Ja, Zh)
  ) as ReExports

import Hydrogen.Element.Compound.Calendar.Props
  ( CalendarProps
  , CalendarProp
  , defaultProps
  , viewMonth
  , viewYear
  , selected
  , selectionMode
  , rangeStart
  , rangeEnd
  , multiSelected
  , minDate
  , maxDate
  , disabledDates
  , weekStartsOn
  , showWeekNumbers
  , backgroundColor
  , borderColor
  , textColor
  , headerColor
  , dayHeaderColor
  , selectedColor
  , selectedTextColor
  , rangeColor
  , todayRingColor
  , hoverColor
  , disabledColor
  , navButtonColor
  , navButtonHoverColor
  , borderRadius
  , dayCellRadius
  , navButtonRadius
  , padding
  , cellSize
  , gap
  , borderWidth
  , headerFontSize
  , headerFontWeight
  , dayHeaderFontSize
  , dayHeaderFontWeight
  , dayFontSize
  , dayFontWeight
  , onSelect
  , onRangeSelect
  , onMultiSelect
  , onMonthChange
  , onPrevMonth
  , onNextMonth
  ) as ReExports

import Hydrogen.Element.Compound.Calendar.DateOps
  ( isLeapYear
  , getDaysInMonth
  , dayOfWeek
  , getFirstDayOfMonth
  , compareDates
  , sameDate
  , addDays
  , addMonths
  , getWeekNumber
  ) as ReExports

import Hydrogen.Element.Compound.Calendar.Grid
  ( buildMonthGrid
  ) as ReExports

import Hydrogen.Element.Compound.Calendar.Locale
  ( monthName
  ) as ReExports

import Hydrogen.Element.Compound.Calendar.Render
  ( calendar
  , calendarWithNav
  ) as ReExports
