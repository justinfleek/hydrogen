-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // compound // calendar // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Props — Property types and builder functions.
-- |
-- | This module defines the CalendarProps record type and all property
-- | builder functions for configuring calendar appearance and behavior.

module Hydrogen.Element.Compound.Calendar.Props
  ( -- * Props Type
    CalendarProps
  , CalendarProp
  , defaultProps
  
  -- * View State Props
  , viewMonth
  , viewYear
  
  -- * Selection Props
  , selected
  , selectionMode
  , rangeStart
  , rangeEnd
  , multiSelected
  
  -- * Constraint Props
  , minDate
  , maxDate
  , disabledDates
  
  -- * Display Props
  , weekStartsOn
  , showWeekNumbers
  
  -- * Color Atoms
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
  
  -- * Geometry Atoms
  , borderRadius
  , dayCellRadius
  , navButtonRadius
  
  -- * Dimension Atoms
  , padding
  , cellSize
  , gap
  , borderWidth
  
  -- * Typography Atoms
  , headerFontSize
  , headerFontWeight
  , dayHeaderFontSize
  , dayHeaderFontWeight
  , dayFontSize
  , dayFontWeight
  
  -- * Behavior Props
  , onSelect
  , onRangeSelect
  , onMultiSelect
  , onMonthChange
  , onPrevMonth
  , onNextMonth
  ) where

import Prelude (const)

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Element.Compound.Calendar.Types
  ( CalendarDate
  , DateRange
  , SelectionMode(Single)
  , WeekStart(Sunday)
  )
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // props type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calendar properties
-- |
-- | All visual properties accept Schema atoms directly.
type CalendarProps msg =
  { -- View state
    viewMonth :: Int              -- Currently viewed month (1-12)
  , viewYear :: Int               -- Currently viewed year
  
  -- Selection state
  , selected :: Maybe CalendarDate
  , selectionMode :: SelectionMode
  , rangeStart :: Maybe CalendarDate
  , rangeEnd :: Maybe CalendarDate
  , multiSelected :: Array CalendarDate
  
  -- Constraints
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  
  -- Display options
  , weekStartsOn :: WeekStart
  , showWeekNumbers :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , headerColor :: Maybe Color.RGB
  , dayHeaderColor :: Maybe Color.RGB
  , selectedColor :: Maybe Color.RGB
  , selectedTextColor :: Maybe Color.RGB
  , rangeColor :: Maybe Color.RGB
  , todayRingColor :: Maybe Color.RGB
  , hoverColor :: Maybe Color.RGB
  , disabledColor :: Maybe Color.RGB
  , navButtonColor :: Maybe Color.RGB
  , navButtonHoverColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Radius
  , dayCellRadius :: Maybe Geometry.Radius
  , navButtonRadius :: Maybe Geometry.Radius
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , cellSize :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , headerFontSize :: Maybe FontSize.FontSize
  , headerFontWeight :: Maybe FontWeight.FontWeight
  , dayHeaderFontSize :: Maybe FontSize.FontSize
  , dayHeaderFontWeight :: Maybe FontWeight.FontWeight
  , dayFontSize :: Maybe FontSize.FontSize
  , dayFontWeight :: Maybe FontWeight.FontWeight
  
  -- Behavior
  , onSelect :: Maybe (CalendarDate -> msg)
  , onRangeSelect :: Maybe (DateRange -> msg)
  , onMultiSelect :: Maybe (Array CalendarDate -> msg)
  , onMonthChange :: Maybe ({ year :: Int, month :: Int } -> msg)
  , onPrevMonth :: Maybe msg
  , onNextMonth :: Maybe msg
  }

-- | Property modifier function
type CalendarProp msg = CalendarProps msg -> CalendarProps msg

-- | Default properties
defaultProps :: forall msg. CalendarProps msg
defaultProps =
  { viewMonth: 1
  , viewYear: 2024
  , selected: Nothing
  , selectionMode: Single
  , rangeStart: Nothing
  , rangeEnd: Nothing
  , multiSelected: []
  , minDate: Nothing
  , maxDate: Nothing
  , disabledDates: const false
  , weekStartsOn: Sunday
  , showWeekNumbers: false
  , backgroundColor: Nothing
  , borderColor: Nothing
  , textColor: Nothing
  , headerColor: Nothing
  , dayHeaderColor: Nothing
  , selectedColor: Nothing
  , selectedTextColor: Nothing
  , rangeColor: Nothing
  , todayRingColor: Nothing
  , hoverColor: Nothing
  , disabledColor: Nothing
  , navButtonColor: Nothing
  , navButtonHoverColor: Nothing
  , borderRadius: Nothing
  , dayCellRadius: Nothing
  , navButtonRadius: Nothing
  , padding: Nothing
  , cellSize: Nothing
  , gap: Nothing
  , borderWidth: Nothing
  , headerFontSize: Nothing
  , headerFontWeight: Nothing
  , dayHeaderFontSize: Nothing
  , dayHeaderFontWeight: Nothing
  , dayFontSize: Nothing
  , dayFontWeight: Nothing
  , onSelect: Nothing
  , onRangeSelect: Nothing
  , onMultiSelect: Nothing
  , onMonthChange: Nothing
  , onPrevMonth: Nothing
  , onNextMonth: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- View state props

viewMonth :: forall msg. Int -> CalendarProp msg
viewMonth m props = props { viewMonth = m }

viewYear :: forall msg. Int -> CalendarProp msg
viewYear y props = props { viewYear = y }

-- Selection props

selected :: forall msg. Maybe CalendarDate -> CalendarProp msg
selected d props = props { selected = d }

selectionMode :: forall msg. SelectionMode -> CalendarProp msg
selectionMode m props = props { selectionMode = m }

rangeStart :: forall msg. Maybe CalendarDate -> CalendarProp msg
rangeStart d props = props { rangeStart = d }

rangeEnd :: forall msg. Maybe CalendarDate -> CalendarProp msg
rangeEnd d props = props { rangeEnd = d }

multiSelected :: forall msg. Array CalendarDate -> CalendarProp msg
multiSelected dates props = props { multiSelected = dates }

-- Constraint props

minDate :: forall msg. CalendarDate -> CalendarProp msg
minDate d props = props { minDate = Just d }

maxDate :: forall msg. CalendarDate -> CalendarProp msg
maxDate d props = props { maxDate = Just d }

disabledDates :: forall msg. (CalendarDate -> Boolean) -> CalendarProp msg
disabledDates pred props = props { disabledDates = pred }

-- Display props

weekStartsOn :: forall msg. WeekStart -> CalendarProp msg
weekStartsOn ws props = props { weekStartsOn = ws }

showWeekNumbers :: forall msg. Boolean -> CalendarProp msg
showWeekNumbers b props = props { showWeekNumbers = b }

-- Color atom props

backgroundColor :: forall msg. Color.RGB -> CalendarProp msg
backgroundColor c props = props { backgroundColor = Just c }

borderColor :: forall msg. Color.RGB -> CalendarProp msg
borderColor c props = props { borderColor = Just c }

textColor :: forall msg. Color.RGB -> CalendarProp msg
textColor c props = props { textColor = Just c }

headerColor :: forall msg. Color.RGB -> CalendarProp msg
headerColor c props = props { headerColor = Just c }

dayHeaderColor :: forall msg. Color.RGB -> CalendarProp msg
dayHeaderColor c props = props { dayHeaderColor = Just c }

selectedColor :: forall msg. Color.RGB -> CalendarProp msg
selectedColor c props = props { selectedColor = Just c }

selectedTextColor :: forall msg. Color.RGB -> CalendarProp msg
selectedTextColor c props = props { selectedTextColor = Just c }

rangeColor :: forall msg. Color.RGB -> CalendarProp msg
rangeColor c props = props { rangeColor = Just c }

todayRingColor :: forall msg. Color.RGB -> CalendarProp msg
todayRingColor c props = props { todayRingColor = Just c }

hoverColor :: forall msg. Color.RGB -> CalendarProp msg
hoverColor c props = props { hoverColor = Just c }

disabledColor :: forall msg. Color.RGB -> CalendarProp msg
disabledColor c props = props { disabledColor = Just c }

navButtonColor :: forall msg. Color.RGB -> CalendarProp msg
navButtonColor c props = props { navButtonColor = Just c }

navButtonHoverColor :: forall msg. Color.RGB -> CalendarProp msg
navButtonHoverColor c props = props { navButtonHoverColor = Just c }

-- Geometry atom props

borderRadius :: forall msg. Geometry.Radius -> CalendarProp msg
borderRadius r props = props { borderRadius = Just r }

dayCellRadius :: forall msg. Geometry.Radius -> CalendarProp msg
dayCellRadius r props = props { dayCellRadius = Just r }

navButtonRadius :: forall msg. Geometry.Radius -> CalendarProp msg
navButtonRadius r props = props { navButtonRadius = Just r }

-- Dimension atom props

padding :: forall msg. Device.Pixel -> CalendarProp msg
padding p props = props { padding = Just p }

cellSize :: forall msg. Device.Pixel -> CalendarProp msg
cellSize s props = props { cellSize = Just s }

gap :: forall msg. Device.Pixel -> CalendarProp msg
gap g props = props { gap = Just g }

borderWidth :: forall msg. Device.Pixel -> CalendarProp msg
borderWidth w props = props { borderWidth = Just w }

-- Typography atom props

headerFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
headerFontSize s props = props { headerFontSize = Just s }

headerFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
headerFontWeight w props = props { headerFontWeight = Just w }

dayHeaderFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
dayHeaderFontSize s props = props { dayHeaderFontSize = Just s }

dayHeaderFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
dayHeaderFontWeight w props = props { dayHeaderFontWeight = Just w }

dayFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
dayFontSize s props = props { dayFontSize = Just s }

dayFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
dayFontWeight w props = props { dayFontWeight = Just w }

-- Behavior props

onSelect :: forall msg. (CalendarDate -> msg) -> CalendarProp msg
onSelect handler props = props { onSelect = Just handler }

onRangeSelect :: forall msg. (DateRange -> msg) -> CalendarProp msg
onRangeSelect handler props = props { onRangeSelect = Just handler }

onMultiSelect :: forall msg. (Array CalendarDate -> msg) -> CalendarProp msg
onMultiSelect handler props = props { onMultiSelect = Just handler }

onMonthChange :: forall msg. ({ year :: Int, month :: Int } -> msg) -> CalendarProp msg
onMonthChange handler props = props { onMonthChange = Just handler }

onPrevMonth :: forall msg. msg -> CalendarProp msg
onPrevMonth m props = props { onPrevMonth = Just m }

onNextMonth :: forall msg. msg -> CalendarProp msg
onNextMonth m props = props { onNextMonth = Just m }
