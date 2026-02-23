-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // calendar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar — Schema-native date selection component.
-- |
-- | A full-featured calendar component with month view, navigation, and various
-- | selection modes. Pure PureScript implementation with no JavaScript FFI.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms** for ALL visual properties.
-- | No hardcoded CSS strings. No Tailwind classes. No JavaScript FFI.
-- | Date arithmetic and locale data are pure PureScript.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                   | CSS Output           |
-- | |-----------------------|------------|------------------------|----------------------|
-- | | backgroundColor       | Color      | Color.RGB              | background           |
-- | | borderColor           | Color      | Color.RGB              | border-color         |
-- | | textColor             | Color      | Color.RGB              | color                |
-- | | selectedColor         | Color      | Color.RGB              | selected day bg      |
-- | | selectedTextColor     | Color      | Color.RGB              | selected day text    |
-- | | todayColor            | Color      | Color.RGB              | today indicator      |
-- | | disabledColor         | Color      | Color.RGB              | disabled day color   |
-- | | rangeColor            | Color      | Color.RGB              | range highlight      |
-- | | headerTextColor       | Color      | Color.RGB              | header text color    |
-- | | borderRadius          | Geometry   | Geometry.Corners       | panel border-radius  |
-- | | cellBorderRadius      | Geometry   | Geometry.Corners       | cell border-radius   |
-- | | padding               | Dimension  | Device.Pixel           | panel padding        |
-- | | gap                   | Dimension  | Device.Pixel           | gap between elements |
-- | | cellSize              | Dimension  | Device.Pixel           | day cell size        |
-- | | borderWidth           | Dimension  | Device.Pixel           | border-width         |
-- | | dayFontSize           | Typography | FontSize.FontSize      | day number font-size |
-- | | dayFontWeight         | Typography | FontWeight.FontWeight  | day number weight    |
-- | | headerFontSize        | Typography | FontSize.FontSize      | header font-size     |
-- | | headerFontWeight      | Typography | FontWeight.FontWeight  | header font-weight   |
-- | | weekdayFontSize       | Typography | FontSize.FontSize      | weekday header size  |
-- | | weekdayFontWeight     | Typography | FontWeight.FontWeight  | weekday header weight|
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.Calendar as Calendar
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Single date selection
-- | Calendar.calendar
-- |   [ Calendar.selected (Just myDate)
-- |   , Calendar.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- With brand atoms
-- | Calendar.calendar
-- |   [ Calendar.selected state.selectedDate
-- |   , Calendar.onSelect HandleDateSelect
-- |   , Calendar.backgroundColor brand.surfaceColor
-- |   , Calendar.selectedColor brand.primaryColor
-- |   , Calendar.borderRadius brand.corners
-- |   ]
-- | ```

module Hydrogen.Element.Component.Calendar
  ( -- * Component
    calendar
  
  -- * Types
  , CalendarDate
  , DateRange
  , SelectionMode(Single, Range, Multiple)
  , WeekStart(Sunday, Monday)
  , Locale(EnUS, DeDE, FrFR, EsES, ItIT, PtBR, JaJP, ZhCN)
  
  -- * Props
  , CalendarProps
  , CalendarProp
  , defaultProps
  
  -- * Prop Builders: State
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
  , locale
  , showWeekNumbers
  
  -- * Prop Builders: Color Atoms
  , backgroundColor
  , borderColor
  , textColor
  , selectedColor
  , selectedTextColor
  , todayColor
  , disabledColor
  , rangeColor
  , headerTextColor
  
  -- * Prop Builders: Geometry Atoms
  , borderRadius
  , cellBorderRadius
  
  -- * Prop Builders: Dimension Atoms
  , padding
  , gap
  , cellSize
  , borderWidth
  
  -- * Prop Builders: Typography Atoms
  , dayFontSize
  , dayFontWeight
  , headerFontSize
  , headerFontWeight
  , weekdayFontSize
  , weekdayFontWeight
  
  -- * Prop Builders: Behavior
  , onSelect
  , onRangeSelect
  , onMultiSelect
  , onMonthChange
  
  -- * Date Operations (Pure PureScript)
  , daysInMonth
  , isLeapYear
  , dayOfWeek
  , compareDates
  , compareDatesOrd
  , sameDate
  , addDays
  , addMonths
  , weekNumber
  , isDateInRange
  , dateToInt
  , dateToNumber
  , monthProgress
  
  -- * Locale Operations
  , monthName
  , monthNameShort
  , dayName
  , dayNameShort
  , dayNameNarrow
  ) where

import Prelude
  ( class Eq
  , class Ord
  , show
  , map
  , const
  , not
  , otherwise
  , negate
  , (<>)
  , ($)
  , (-)
  , (+)
  , (*)
  , (/)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , compare
  , Ordering(LT, GT, EQ)
  )

import Data.Array (elem, foldl, range, snoc, take, drop, findMap)
import Data.Int (rem, quot, toNumber)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A date represented as year, month (1-12), and day (1-31)
type CalendarDate =
  { year :: Int
  , month :: Int  -- 1-indexed: 1 = January, 12 = December
  , day :: Int
  }

-- | A date range with start and end dates
type DateRange =
  { start :: CalendarDate
  , end :: CalendarDate
  }

-- | Selection mode for the calendar
data SelectionMode
  = Single    -- Select a single date
  | Range     -- Select a date range (start to end)
  | Multiple  -- Select multiple individual dates

derive instance eqSelectionMode :: Eq SelectionMode

-- | Which day the week starts on
data WeekStart
  = Sunday
  | Monday

derive instance eqWeekStart :: Eq WeekStart

-- | Supported locales for month/day names
data Locale
  = EnUS  -- English (US)
  | DeDE  -- German
  | FrFR  -- French
  | EsES  -- Spanish
  | ItIT  -- Italian
  | PtBR  -- Portuguese (Brazil)
  | JaJP  -- Japanese
  | ZhCN  -- Chinese (Simplified)

derive instance eqLocale :: Eq Locale

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calendar properties
type CalendarProps msg =
  { -- State
    viewMonth :: Int
  , viewYear :: Int
  , selected :: Maybe CalendarDate
  , selectionMode :: SelectionMode
  , rangeStart :: Maybe CalendarDate
  , rangeEnd :: Maybe CalendarDate
  , multiSelected :: Array CalendarDate
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  , weekStartsOn :: WeekStart
  , locale :: Locale
  , showWeekNumbers :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , selectedColor :: Maybe Color.RGB
  , selectedTextColor :: Maybe Color.RGB
  , todayColor :: Maybe Color.RGB
  , disabledColor :: Maybe Color.RGB
  , rangeColor :: Maybe Color.RGB
  , headerTextColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , cellBorderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , cellSize :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , dayFontSize :: Maybe FontSize.FontSize
  , dayFontWeight :: Maybe FontWeight.FontWeight
  , headerFontSize :: Maybe FontSize.FontSize
  , headerFontWeight :: Maybe FontWeight.FontWeight
  , weekdayFontSize :: Maybe FontSize.FontSize
  , weekdayFontWeight :: Maybe FontWeight.FontWeight
  
  -- Behavior
  , onSelect :: Maybe (CalendarDate -> msg)
  , onRangeSelect :: Maybe (DateRange -> msg)
  , onMultiSelect :: Maybe (Array CalendarDate -> msg)
  , onMonthChange :: Maybe ({ year :: Int, month :: Int } -> msg)
  }

-- | Property modifier
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
  , locale: EnUS
  , showWeekNumbers: false
  , backgroundColor: Nothing
  , borderColor: Nothing
  , textColor: Nothing
  , selectedColor: Nothing
  , selectedTextColor: Nothing
  , todayColor: Nothing
  , disabledColor: Nothing
  , rangeColor: Nothing
  , headerTextColor: Nothing
  , borderRadius: Nothing
  , cellBorderRadius: Nothing
  , padding: Nothing
  , gap: Nothing
  , cellSize: Nothing
  , borderWidth: Nothing
  , dayFontSize: Nothing
  , dayFontWeight: Nothing
  , headerFontSize: Nothing
  , headerFontWeight: Nothing
  , weekdayFontSize: Nothing
  , weekdayFontWeight: Nothing
  , onSelect: Nothing
  , onRangeSelect: Nothing
  , onMultiSelect: Nothing
  , onMonthChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // prop builders: state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set the currently viewed month (1-12)
viewMonth :: forall msg. Int -> CalendarProp msg
viewMonth m props = props { viewMonth = clampMonth m }

-- | Set the currently viewed year
viewYear :: forall msg. Int -> CalendarProp msg
viewYear y props = props { viewYear = y }

-- | Set the selected date
selected :: forall msg. Maybe CalendarDate -> CalendarProp msg
selected d props = props { selected = d }

-- | Set selection mode
selectionMode :: forall msg. SelectionMode -> CalendarProp msg
selectionMode m props = props { selectionMode = m }

-- | Set range start date
rangeStart :: forall msg. Maybe CalendarDate -> CalendarProp msg
rangeStart d props = props { rangeStart = d }

-- | Set range end date
rangeEnd :: forall msg. Maybe CalendarDate -> CalendarProp msg
rangeEnd d props = props { rangeEnd = d }

-- | Set multiple selected dates
multiSelected :: forall msg. Array CalendarDate -> CalendarProp msg
multiSelected dates props = props { multiSelected = dates }

-- | Set minimum selectable date
minDate :: forall msg. CalendarDate -> CalendarProp msg
minDate d props = props { minDate = Just d }

-- | Set maximum selectable date
maxDate :: forall msg. CalendarDate -> CalendarProp msg
maxDate d props = props { maxDate = Just d }

-- | Set custom disabled dates predicate
disabledDates :: forall msg. (CalendarDate -> Boolean) -> CalendarProp msg
disabledDates pred props = props { disabledDates = pred }

-- | Set which day the week starts on
weekStartsOn :: forall msg. WeekStart -> CalendarProp msg
weekStartsOn ws props = props { weekStartsOn = ws }

-- | Set locale for month/day names
locale :: forall msg. Locale -> CalendarProp msg
locale l props = props { locale = l }

-- | Show week numbers
showWeekNumbers :: forall msg. Boolean -> CalendarProp msg
showWeekNumbers s props = props { showWeekNumbers = s }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // prop builders: color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> CalendarProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> CalendarProp msg
borderColor c props = props { borderColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> CalendarProp msg
textColor c props = props { textColor = Just c }

-- | Set selected day background color (Color.RGB atom)
selectedColor :: forall msg. Color.RGB -> CalendarProp msg
selectedColor c props = props { selectedColor = Just c }

-- | Set selected day text color (Color.RGB atom)
selectedTextColor :: forall msg. Color.RGB -> CalendarProp msg
selectedTextColor c props = props { selectedTextColor = Just c }

-- | Set today indicator color (Color.RGB atom)
todayColor :: forall msg. Color.RGB -> CalendarProp msg
todayColor c props = props { todayColor = Just c }

-- | Set disabled day color (Color.RGB atom)
disabledColor :: forall msg. Color.RGB -> CalendarProp msg
disabledColor c props = props { disabledColor = Just c }

-- | Set range highlight color (Color.RGB atom)
rangeColor :: forall msg. Color.RGB -> CalendarProp msg
rangeColor c props = props { rangeColor = Just c }

-- | Set header text color (Color.RGB atom)
headerTextColor :: forall msg. Color.RGB -> CalendarProp msg
headerTextColor c props = props { headerTextColor = Just c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set panel border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> CalendarProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set cell border radius (Geometry.Corners atom)
cellBorderRadius :: forall msg. Geometry.Corners -> CalendarProp msg
cellBorderRadius r props = props { cellBorderRadius = Just r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: dimension
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> CalendarProp msg
padding p props = props { padding = Just p }

-- | Set gap between elements (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> CalendarProp msg
gap g props = props { gap = Just g }

-- | Set day cell size (Device.Pixel atom)
cellSize :: forall msg. Device.Pixel -> CalendarProp msg
cellSize s props = props { cellSize = Just s }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> CalendarProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: typography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set day number font size (FontSize atom)
dayFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
dayFontSize s props = props { dayFontSize = Just s }

-- | Set day number font weight (FontWeight atom)
dayFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
dayFontWeight w props = props { dayFontWeight = Just w }

-- | Set header font size (FontSize atom)
headerFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
headerFontSize s props = props { headerFontSize = Just s }

-- | Set header font weight (FontWeight atom)
headerFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
headerFontWeight w props = props { headerFontWeight = Just w }

-- | Set weekday header font size (FontSize atom)
weekdayFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
weekdayFontSize s props = props { weekdayFontSize = Just s }

-- | Set weekday header font weight (FontWeight atom)
weekdayFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
weekdayFontWeight w props = props { weekdayFontWeight = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set single date select handler
onSelect :: forall msg. (CalendarDate -> msg) -> CalendarProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set range select handler
onRangeSelect :: forall msg. (DateRange -> msg) -> CalendarProp msg
onRangeSelect handler props = props { onRangeSelect = Just handler }

-- | Set multi-select handler
onMultiSelect :: forall msg. (Array CalendarDate -> msg) -> CalendarProp msg
onMultiSelect handler props = props { onMultiSelect = Just handler }

-- | Set month change handler
onMonthChange :: forall msg. ({ year :: Int, month :: Int } -> msg) -> CalendarProp msg
onMonthChange handler props = props { onMonthChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // date operations: pure purescript
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a year is a leap year
-- |
-- | A year is a leap year if:
-- | - Divisible by 4 AND not divisible by 100, OR
-- | - Divisible by 400
isLeapYear :: Int -> Boolean
isLeapYear year =
  (year `rem` 4 == 0 && year `rem` 100 /= 0) || (year `rem` 400 == 0)

-- | Get the number of days in a month (1-12)
-- |
-- | Pure PureScript implementation using leap year calculation.
daysInMonth :: Int -> Int -> Int
daysInMonth year month = case month of
  1 -> 31   -- January
  2 -> if isLeapYear year then 29 else 28  -- February
  3 -> 31   -- March
  4 -> 30   -- April
  5 -> 31   -- May
  6 -> 30   -- June
  7 -> 31   -- July
  8 -> 31   -- August
  9 -> 30   -- September
  10 -> 31  -- October
  11 -> 30  -- November
  12 -> 31  -- December
  _ -> 30   -- Fallback (should not happen with valid input)

-- | Get the day of the week for a date (0 = Sunday, 6 = Saturday)
-- |
-- | Uses Zeller's congruence algorithm (pure math, no FFI).
dayOfWeek :: CalendarDate -> Int
dayOfWeek date =
  let
    -- Adjust month and year for Zeller's formula
    -- January and February are treated as months 13 and 14 of previous year
    m = if date.month < 3 then date.month + 12 else date.month
    y = if date.month < 3 then date.year - 1 else date.year
    
    q = date.day
    k = y `rem` 100
    j = y `quot` 100
    
    -- Zeller's congruence
    h = (q + ((13 * (m + 1)) `quot` 5) + k + (k `quot` 4) + (j `quot` 4) - (2 * j)) `rem` 7
    
    -- Convert from Zeller's (0 = Saturday) to standard (0 = Sunday)
    dow = (h + 6) `rem` 7
  in
    if dow < 0 then dow + 7 else dow

-- | Get the day of week for the first day of a month
firstDayOfMonth :: Int -> Int -> Int
firstDayOfMonth year month = dayOfWeek { year, month, day: 1 }

-- | Compare two dates
-- |
-- | Returns: LT if a < b, EQ if equal, GT if a > b
compareDates :: CalendarDate -> CalendarDate -> Ordering
compareDates a b
  | a.year < b.year = LT
  | a.year > b.year = GT
  | a.month < b.month = LT
  | a.month > b.month = GT
  | a.day < b.day = LT
  | a.day > b.day = GT
  | otherwise = EQ

-- | Check if two dates are the same
sameDate :: CalendarDate -> CalendarDate -> Boolean
sameDate a b = a.year == b.year && a.month == b.month && a.day == b.day

-- | Add days to a date
-- |
-- | Pure PureScript implementation handling month/year overflow.
addDays :: CalendarDate -> Int -> CalendarDate
addDays date days
  | days == 0 = date
  | days > 0 = addDaysPositive date days
  | otherwise = addDaysNegative date (negate days)

-- | Add positive days
addDaysPositive :: CalendarDate -> Int -> CalendarDate
addDaysPositive date days =
  let
    daysThisMonth = daysInMonth date.year date.month
    remainingInMonth = daysThisMonth - date.day
  in
    if days <= remainingInMonth
      then date { day = date.day + days }
      else
        let
          nextMonth = if date.month == 12 then 1 else date.month + 1
          nextYear = if date.month == 12 then date.year + 1 else date.year
          nextDate = { year: nextYear, month: nextMonth, day: 1 }
        in
          addDaysPositive nextDate (days - remainingInMonth - 1)

-- | Subtract days (add negative)
addDaysNegative :: CalendarDate -> Int -> CalendarDate
addDaysNegative date days =
  if days < date.day
    then date { day = date.day - days }
    else
      let
        prevMonth = if date.month == 1 then 12 else date.month - 1
        prevYear = if date.month == 1 then date.year - 1 else date.year
        daysInPrevMonth = daysInMonth prevYear prevMonth
        prevDate = { year: prevYear, month: prevMonth, day: daysInPrevMonth }
      in
        addDaysNegative prevDate (days - date.day)

-- | Add months to a date
-- |
-- | Clamps day to valid range if target month has fewer days.
addMonths :: CalendarDate -> Int -> CalendarDate
addMonths date months =
  let
    totalMonths = (date.year * 12 + date.month - 1) + months
    newYear = totalMonths `quot` 12
    newMonth = (totalMonths `rem` 12) + 1
    adjustedMonth = if newMonth <= 0 then newMonth + 12 else newMonth
    adjustedYear = if newMonth <= 0 then newYear - 1 else newYear
    maxDay = daysInMonth adjustedYear adjustedMonth
    newDay = if date.day > maxDay then maxDay else date.day
  in
    { year: adjustedYear, month: adjustedMonth, day: newDay }

-- | Get ISO week number for a date
-- |
-- | Pure PureScript implementation of ISO 8601 week numbering.
weekNumber :: CalendarDate -> Int
weekNumber date =
  let
    -- Find the Thursday of the week containing this date
    dow = dayOfWeek date
    daysToThursday = 4 - (if dow == 0 then 7 else dow)
    thursday = addDays date daysToThursday
    
    -- Find Jan 1 of that year
    jan1 = { year: thursday.year, month: 1, day: 1 }
    
    -- Count days from Jan 1 to Thursday
    dayCount = daysBetween jan1 thursday
  in
    (dayCount `quot` 7) + 1

-- | Count days between two dates (a must be <= b)
daysBetween :: CalendarDate -> CalendarDate -> Int
daysBetween a b = go a 0
  where
  go current acc
    | sameDate current b = acc
    | otherwise = go (addDays current 1) (acc + 1)

-- | Check if date is within a range (inclusive)
isDateInRange :: CalendarDate -> Maybe CalendarDate -> Maybe CalendarDate -> Boolean
isDateInRange date minD maxD =
  let
    dateVal = dateToInt date
    afterMin = case minD of
      Nothing -> true
      Just minDate' -> dateVal >= dateToInt minDate'
    beforeMax = case maxD of
      Nothing -> true
      Just maxDate' -> dateVal <= dateToInt maxDate'
  in
    afterMin && beforeMax

-- | Convert date to comparable integer (YYYYMMDD format)
-- |
-- | Enables use of standard comparison operators on dates.
dateToInt :: CalendarDate -> Int
dateToInt d = d.year * 10000 + d.month * 100 + d.day

-- | Convert date to Number for fractional calculations
dateToNumber :: CalendarDate -> Number
dateToNumber d = toNumber (dateToInt d)

-- | Compare dates using standard Ord comparison
-- |
-- | Uses `compare` from Prelude on the integer representation.
compareDatesOrd :: CalendarDate -> CalendarDate -> Ordering
compareDatesOrd a b = compare (dateToInt a) (dateToInt b)

-- | Calculate progress through the month as a fraction (0.0 to 1.0)
-- |
-- | Useful for progress indicators or visual representations.
monthProgress :: CalendarDate -> Number
monthProgress date =
  let
    totalDays = toNumber (daysInMonth date.year date.month)
    currentDay = toNumber date.day
  in
    currentDay / totalDays

-- ═══════════════════════════════════════════════════════════════════════════════
--                                              // locale data: pure purescript
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get full month name for locale
monthName :: Locale -> Int -> String
monthName loc month = case loc of
  EnUS -> monthNameEnUS month
  DeDE -> monthNameDeDE month
  FrFR -> monthNameFrFR month
  EsES -> monthNameEsES month
  ItIT -> monthNameItIT month
  PtBR -> monthNamePtBR month
  JaJP -> monthNameJaJP month
  ZhCN -> monthNameZhCN month

-- | Get short month name for locale
monthNameShort :: Locale -> Int -> String
monthNameShort loc month = case loc of
  EnUS -> monthNameShortEnUS month
  DeDE -> monthNameShortDeDE month
  FrFR -> monthNameShortFrFR month
  EsES -> monthNameShortEsES month
  ItIT -> monthNameShortItIT month
  PtBR -> monthNameShortPtBR month
  JaJP -> monthNameShortJaJP month
  ZhCN -> monthNameShortZhCN month

-- | Get full day name for locale (0 = Sunday)
dayName :: Locale -> Int -> String
dayName loc dow = case loc of
  EnUS -> dayNameEnUS dow
  DeDE -> dayNameDeDE dow
  FrFR -> dayNameFrFR dow
  EsES -> dayNameEsES dow
  ItIT -> dayNameItIT dow
  PtBR -> dayNamePtBR dow
  JaJP -> dayNameJaJP dow
  ZhCN -> dayNameZhCN dow

-- | Get short day name for locale (0 = Sunday)
dayNameShort :: Locale -> Int -> String
dayNameShort loc dow = case loc of
  EnUS -> dayNameShortEnUS dow
  DeDE -> dayNameShortDeDE dow
  FrFR -> dayNameShortFrFR dow
  EsES -> dayNameShortEsES dow
  ItIT -> dayNameShortItIT dow
  PtBR -> dayNameShortPtBR dow
  JaJP -> dayNameShortJaJP dow
  ZhCN -> dayNameShortZhCN dow

-- | Get narrow day name for locale (0 = Sunday)
dayNameNarrow :: Locale -> Int -> String
dayNameNarrow loc dow = case loc of
  EnUS -> dayNameNarrowEnUS dow
  DeDE -> dayNameNarrowDeDE dow
  FrFR -> dayNameNarrowFrFR dow
  EsES -> dayNameNarrowEsES dow
  ItIT -> dayNameNarrowItIT dow
  PtBR -> dayNameNarrowPtBR dow
  JaJP -> dayNameNarrowJaJP dow
  ZhCN -> dayNameNarrowZhCN dow

-- ─────────────────────────────────────────────────────────────────────────────
--                                                               // english (us)
-- ─────────────────────────────────────────────────────────────────────────────

monthNameEnUS :: Int -> String
monthNameEnUS m = case m of
  1 -> "January"
  2 -> "February"
  3 -> "March"
  4 -> "April"
  5 -> "May"
  6 -> "June"
  7 -> "July"
  8 -> "August"
  9 -> "September"
  10 -> "October"
  11 -> "November"
  12 -> "December"
  _ -> "Unknown"

monthNameShortEnUS :: Int -> String
monthNameShortEnUS m = case m of
  1 -> "Jan"
  2 -> "Feb"
  3 -> "Mar"
  4 -> "Apr"
  5 -> "May"
  6 -> "Jun"
  7 -> "Jul"
  8 -> "Aug"
  9 -> "Sep"
  10 -> "Oct"
  11 -> "Nov"
  12 -> "Dec"
  _ -> "???"

dayNameEnUS :: Int -> String
dayNameEnUS d = case d of
  0 -> "Sunday"
  1 -> "Monday"
  2 -> "Tuesday"
  3 -> "Wednesday"
  4 -> "Thursday"
  5 -> "Friday"
  6 -> "Saturday"
  _ -> "Unknown"

dayNameShortEnUS :: Int -> String
dayNameShortEnUS d = case d of
  0 -> "Sun"
  1 -> "Mon"
  2 -> "Tue"
  3 -> "Wed"
  4 -> "Thu"
  5 -> "Fri"
  6 -> "Sat"
  _ -> "???"

dayNameNarrowEnUS :: Int -> String
dayNameNarrowEnUS d = case d of
  0 -> "S"
  1 -> "M"
  2 -> "T"
  3 -> "W"
  4 -> "T"
  5 -> "F"
  6 -> "S"
  _ -> "?"

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                     // german
-- ─────────────────────────────────────────────────────────────────────────────

monthNameDeDE :: Int -> String
monthNameDeDE m = case m of
  1 -> "Januar"
  2 -> "Februar"
  3 -> "März"
  4 -> "April"
  5 -> "Mai"
  6 -> "Juni"
  7 -> "Juli"
  8 -> "August"
  9 -> "September"
  10 -> "Oktober"
  11 -> "November"
  12 -> "Dezember"
  _ -> "Unbekannt"

monthNameShortDeDE :: Int -> String
monthNameShortDeDE m = case m of
  1 -> "Jan"
  2 -> "Feb"
  3 -> "Mär"
  4 -> "Apr"
  5 -> "Mai"
  6 -> "Jun"
  7 -> "Jul"
  8 -> "Aug"
  9 -> "Sep"
  10 -> "Okt"
  11 -> "Nov"
  12 -> "Dez"
  _ -> "???"

dayNameDeDE :: Int -> String
dayNameDeDE d = case d of
  0 -> "Sonntag"
  1 -> "Montag"
  2 -> "Dienstag"
  3 -> "Mittwoch"
  4 -> "Donnerstag"
  5 -> "Freitag"
  6 -> "Samstag"
  _ -> "Unbekannt"

dayNameShortDeDE :: Int -> String
dayNameShortDeDE d = case d of
  0 -> "So"
  1 -> "Mo"
  2 -> "Di"
  3 -> "Mi"
  4 -> "Do"
  5 -> "Fr"
  6 -> "Sa"
  _ -> "??"

dayNameNarrowDeDE :: Int -> String
dayNameNarrowDeDE d = case d of
  0 -> "S"
  1 -> "M"
  2 -> "D"
  3 -> "M"
  4 -> "D"
  5 -> "F"
  6 -> "S"
  _ -> "?"

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                     // french
-- ─────────────────────────────────────────────────────────────────────────────

monthNameFrFR :: Int -> String
monthNameFrFR m = case m of
  1 -> "janvier"
  2 -> "février"
  3 -> "mars"
  4 -> "avril"
  5 -> "mai"
  6 -> "juin"
  7 -> "juillet"
  8 -> "août"
  9 -> "septembre"
  10 -> "octobre"
  11 -> "novembre"
  12 -> "décembre"
  _ -> "inconnu"

monthNameShortFrFR :: Int -> String
monthNameShortFrFR m = case m of
  1 -> "janv."
  2 -> "févr."
  3 -> "mars"
  4 -> "avr."
  5 -> "mai"
  6 -> "juin"
  7 -> "juil."
  8 -> "août"
  9 -> "sept."
  10 -> "oct."
  11 -> "nov."
  12 -> "déc."
  _ -> "???"

dayNameFrFR :: Int -> String
dayNameFrFR d = case d of
  0 -> "dimanche"
  1 -> "lundi"
  2 -> "mardi"
  3 -> "mercredi"
  4 -> "jeudi"
  5 -> "vendredi"
  6 -> "samedi"
  _ -> "inconnu"

dayNameShortFrFR :: Int -> String
dayNameShortFrFR d = case d of
  0 -> "dim."
  1 -> "lun."
  2 -> "mar."
  3 -> "mer."
  4 -> "jeu."
  5 -> "ven."
  6 -> "sam."
  _ -> "???"

dayNameNarrowFrFR :: Int -> String
dayNameNarrowFrFR d = case d of
  0 -> "D"
  1 -> "L"
  2 -> "M"
  3 -> "M"
  4 -> "J"
  5 -> "V"
  6 -> "S"
  _ -> "?"

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                    // spanish
-- ─────────────────────────────────────────────────────────────────────────────

monthNameEsES :: Int -> String
monthNameEsES m = case m of
  1 -> "enero"
  2 -> "febrero"
  3 -> "marzo"
  4 -> "abril"
  5 -> "mayo"
  6 -> "junio"
  7 -> "julio"
  8 -> "agosto"
  9 -> "septiembre"
  10 -> "octubre"
  11 -> "noviembre"
  12 -> "diciembre"
  _ -> "desconocido"

monthNameShortEsES :: Int -> String
monthNameShortEsES m = case m of
  1 -> "ene"
  2 -> "feb"
  3 -> "mar"
  4 -> "abr"
  5 -> "may"
  6 -> "jun"
  7 -> "jul"
  8 -> "ago"
  9 -> "sep"
  10 -> "oct"
  11 -> "nov"
  12 -> "dic"
  _ -> "???"

dayNameEsES :: Int -> String
dayNameEsES d = case d of
  0 -> "domingo"
  1 -> "lunes"
  2 -> "martes"
  3 -> "miércoles"
  4 -> "jueves"
  5 -> "viernes"
  6 -> "sábado"
  _ -> "desconocido"

dayNameShortEsES :: Int -> String
dayNameShortEsES d = case d of
  0 -> "dom"
  1 -> "lun"
  2 -> "mar"
  3 -> "mié"
  4 -> "jue"
  5 -> "vie"
  6 -> "sáb"
  _ -> "???"

dayNameNarrowEsES :: Int -> String
dayNameNarrowEsES d = case d of
  0 -> "D"
  1 -> "L"
  2 -> "M"
  3 -> "X"
  4 -> "J"
  5 -> "V"
  6 -> "S"
  _ -> "?"

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                    // italian
-- ─────────────────────────────────────────────────────────────────────────────

monthNameItIT :: Int -> String
monthNameItIT m = case m of
  1 -> "gennaio"
  2 -> "febbraio"
  3 -> "marzo"
  4 -> "aprile"
  5 -> "maggio"
  6 -> "giugno"
  7 -> "luglio"
  8 -> "agosto"
  9 -> "settembre"
  10 -> "ottobre"
  11 -> "novembre"
  12 -> "dicembre"
  _ -> "sconosciuto"

monthNameShortItIT :: Int -> String
monthNameShortItIT m = case m of
  1 -> "gen"
  2 -> "feb"
  3 -> "mar"
  4 -> "apr"
  5 -> "mag"
  6 -> "giu"
  7 -> "lug"
  8 -> "ago"
  9 -> "set"
  10 -> "ott"
  11 -> "nov"
  12 -> "dic"
  _ -> "???"

dayNameItIT :: Int -> String
dayNameItIT d = case d of
  0 -> "domenica"
  1 -> "lunedì"
  2 -> "martedì"
  3 -> "mercoledì"
  4 -> "giovedì"
  5 -> "venerdì"
  6 -> "sabato"
  _ -> "sconosciuto"

dayNameShortItIT :: Int -> String
dayNameShortItIT d = case d of
  0 -> "dom"
  1 -> "lun"
  2 -> "mar"
  3 -> "mer"
  4 -> "gio"
  5 -> "ven"
  6 -> "sab"
  _ -> "???"

dayNameNarrowItIT :: Int -> String
dayNameNarrowItIT d = case d of
  0 -> "D"
  1 -> "L"
  2 -> "M"
  3 -> "M"
  4 -> "G"
  5 -> "V"
  6 -> "S"
  _ -> "?"

-- ─────────────────────────────────────────────────────────────────────────────
--                                                        // portuguese (brazil)
-- ─────────────────────────────────────────────────────────────────────────────

monthNamePtBR :: Int -> String
monthNamePtBR m = case m of
  1 -> "janeiro"
  2 -> "fevereiro"
  3 -> "março"
  4 -> "abril"
  5 -> "maio"
  6 -> "junho"
  7 -> "julho"
  8 -> "agosto"
  9 -> "setembro"
  10 -> "outubro"
  11 -> "novembro"
  12 -> "dezembro"
  _ -> "desconhecido"

monthNameShortPtBR :: Int -> String
monthNameShortPtBR m = case m of
  1 -> "jan"
  2 -> "fev"
  3 -> "mar"
  4 -> "abr"
  5 -> "mai"
  6 -> "jun"
  7 -> "jul"
  8 -> "ago"
  9 -> "set"
  10 -> "out"
  11 -> "nov"
  12 -> "dez"
  _ -> "???"

dayNamePtBR :: Int -> String
dayNamePtBR d = case d of
  0 -> "domingo"
  1 -> "segunda-feira"
  2 -> "terça-feira"
  3 -> "quarta-feira"
  4 -> "quinta-feira"
  5 -> "sexta-feira"
  6 -> "sábado"
  _ -> "desconhecido"

dayNameShortPtBR :: Int -> String
dayNameShortPtBR d = case d of
  0 -> "dom"
  1 -> "seg"
  2 -> "ter"
  3 -> "qua"
  4 -> "qui"
  5 -> "sex"
  6 -> "sáb"
  _ -> "???"

dayNameNarrowPtBR :: Int -> String
dayNameNarrowPtBR d = case d of
  0 -> "D"
  1 -> "S"
  2 -> "T"
  3 -> "Q"
  4 -> "Q"
  5 -> "S"
  6 -> "S"
  _ -> "?"

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                   // japanese
-- ─────────────────────────────────────────────────────────────────────────────

monthNameJaJP :: Int -> String
monthNameJaJP m = case m of
  1 -> "1月"
  2 -> "2月"
  3 -> "3月"
  4 -> "4月"
  5 -> "5月"
  6 -> "6月"
  7 -> "7月"
  8 -> "8月"
  9 -> "9月"
  10 -> "10月"
  11 -> "11月"
  12 -> "12月"
  _ -> "不明"

monthNameShortJaJP :: Int -> String
monthNameShortJaJP = monthNameJaJP  -- Same in Japanese

dayNameJaJP :: Int -> String
dayNameJaJP d = case d of
  0 -> "日曜日"
  1 -> "月曜日"
  2 -> "火曜日"
  3 -> "水曜日"
  4 -> "木曜日"
  5 -> "金曜日"
  6 -> "土曜日"
  _ -> "不明"

dayNameShortJaJP :: Int -> String
dayNameShortJaJP d = case d of
  0 -> "日"
  1 -> "月"
  2 -> "火"
  3 -> "水"
  4 -> "木"
  5 -> "金"
  6 -> "土"
  _ -> "?"

dayNameNarrowJaJP :: Int -> String
dayNameNarrowJaJP = dayNameShortJaJP  -- Same in Japanese

-- ─────────────────────────────────────────────────────────────────────────────
--                                                       // chinese (simplified)
-- ─────────────────────────────────────────────────────────────────────────────

monthNameZhCN :: Int -> String
monthNameZhCN m = case m of
  1 -> "一月"
  2 -> "二月"
  3 -> "三月"
  4 -> "四月"
  5 -> "五月"
  6 -> "六月"
  7 -> "七月"
  8 -> "八月"
  9 -> "九月"
  10 -> "十月"
  11 -> "十一月"
  12 -> "十二月"
  _ -> "未知"

monthNameShortZhCN :: Int -> String
monthNameShortZhCN m = show m <> "月"

dayNameZhCN :: Int -> String
dayNameZhCN d = case d of
  0 -> "星期日"
  1 -> "星期一"
  2 -> "星期二"
  3 -> "星期三"
  4 -> "星期四"
  5 -> "星期五"
  6 -> "星期六"
  _ -> "未知"

dayNameShortZhCN :: Int -> String
dayNameShortZhCN d = case d of
  0 -> "周日"
  1 -> "周一"
  2 -> "周二"
  3 -> "周三"
  4 -> "周四"
  5 -> "周五"
  6 -> "周六"
  _ -> "?"

dayNameNarrowZhCN :: Int -> String
dayNameNarrowZhCN d = case d of
  0 -> "日"
  1 -> "一"
  2 -> "二"
  3 -> "三"
  4 -> "四"
  5 -> "五"
  6 -> "六"
  _ -> "?"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // resolved config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Resolved configuration with defaults applied
type ResolvedConfig =
  { bgColor :: Color.RGB
  , borderCol :: Color.RGB
  , textCol :: Color.RGB
  , selectedCol :: Color.RGB
  , selectedTextCol :: Color.RGB
  , todayCol :: Color.RGB
  , disabledCol :: Color.RGB
  , rangeCol :: Color.RGB
  , headerTextCol :: Color.RGB
  , panelRadius :: String
  , cellRadius :: String
  , paddingVal :: String
  , gapVal :: String
  , cellSizeVal :: String
  , borderWidthVal :: String
  , dayFontSizeVal :: String
  , dayFontWeightVal :: String
  , headerFontSizeVal :: String
  , headerFontWeightVal :: String
  , weekdayFontSizeVal :: String
  , weekdayFontWeightVal :: String
  }

-- | Resolve props to config with defaults
resolveConfig :: forall msg. CalendarProps msg -> ResolvedConfig
resolveConfig props =
  { bgColor: maybe (Color.rgb 30 30 30) (\c -> c) props.backgroundColor
  , borderCol: maybe (Color.rgb 60 60 60) (\c -> c) props.borderColor
  , textCol: maybe (Color.rgb 220 220 220) (\c -> c) props.textColor
  , selectedCol: maybe (Color.rgb 59 130 246) (\c -> c) props.selectedColor
  , selectedTextCol: maybe (Color.rgb 255 255 255) (\c -> c) props.selectedTextColor
  , todayCol: maybe (Color.rgb 59 130 246) (\c -> c) props.todayColor
  , disabledCol: maybe (Color.rgb 100 100 100) (\c -> c) props.disabledColor
  , rangeCol: maybe (Color.rgb 59 130 246) (\c -> c) props.rangeColor
  , headerTextCol: maybe (Color.rgb 180 180 180) (\c -> c) props.headerTextColor
  , panelRadius: maybe "8px" Geometry.cornersToCss props.borderRadius
  , cellRadius: maybe "4px" Geometry.cornersToCss props.cellBorderRadius
  , paddingVal: maybe "12px" show props.padding
  , gapVal: maybe "4px" show props.gap
  , cellSizeVal: maybe "36px" show props.cellSize
  , borderWidthVal: maybe "1px" show props.borderWidth
  , dayFontSizeVal: maybe "14px" FontSize.toCss props.dayFontSize
  , dayFontWeightVal: maybe "400" FontWeight.toCss props.dayFontWeight
  , headerFontSizeVal: maybe "14px" FontSize.toCss props.headerFontSize
  , headerFontWeightVal: maybe "600" FontWeight.toCss props.headerFontWeight
  , weekdayFontSizeVal: maybe "12px" FontSize.toCss props.weekdayFontSize
  , weekdayFontWeightVal: maybe "400" FontWeight.toCss props.weekdayFontWeight
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // main component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a calendar
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | No JavaScript FFI. Pure PureScript date arithmetic and locale data.
calendar :: forall msg. Array (CalendarProp msg) -> E.Element msg
calendar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    config = resolveConfig props
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    E.div_
      (buildPanelAttrs config) $
      [ renderHeader props config
      , renderDayHeaders props config
      , renderWeeks props config grid
      ]

-- | Build panel container attributes
buildPanelAttrs :: forall msg. ResolvedConfig -> Array (E.Attribute msg)
buildPanelAttrs config =
  [ E.style "display" "flex"
  , E.style "flex-direction" "column"
  , E.style "gap" config.gapVal
  , E.style "padding" config.paddingVal
  , E.style "background-color" (Color.toCss config.bgColor)
  , E.style "border-style" "solid"
  , E.style "border-width" config.borderWidthVal
  , E.style "border-color" (Color.toCss config.borderCol)
  , E.style "border-radius" config.panelRadius
  , E.role "grid"
  , E.ariaLabel "Calendar"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // header
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the month/year header
renderHeader :: forall msg. CalendarProps msg -> ResolvedConfig -> E.Element msg
renderHeader props config =
  E.div_
    [ E.style "display" "flex"
    , E.style "justify-content" "center"
    , E.style "align-items" "center"
    , E.style "padding" "4px 0"
    ]
    [ E.span_
        [ E.style "font-size" config.headerFontSizeVal
        , E.style "font-weight" config.headerFontWeightVal
        , E.style "color" (Color.toCss config.textCol)
        ]
        [ E.text (monthName props.locale props.viewMonth <> " " <> show props.viewYear) ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // day headers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render day-of-week headers
renderDayHeaders :: forall msg. CalendarProps msg -> ResolvedConfig -> E.Element msg
renderDayHeaders props config =
  let
    -- Get day indices based on week start
    dayIndices = case props.weekStartsOn of
      Sunday -> [0, 1, 2, 3, 4, 5, 6]
      Monday -> [1, 2, 3, 4, 5, 6, 0]
    
    weekNumHeader = if props.showWeekNumbers
      then [ renderWeekNumHeader config ]
      else []
  in
    E.div_
      [ E.style "display" "flex"
      , E.role "row"
      ]
      (weekNumHeader <> map (renderDayHeader props config) dayIndices)

-- | Render week number header cell
renderWeekNumHeader :: forall msg. ResolvedConfig -> E.Element msg
renderWeekNumHeader config =
  E.div_
    [ E.style "width" config.cellSizeVal
    , E.style "height" config.cellSizeVal
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "font-size" config.weekdayFontSizeVal
    , E.style "font-weight" config.weekdayFontWeightVal
    , E.style "color" (Color.toCss config.headerTextCol)
    ]
    [ E.text "#" ]

-- | Render a single day-of-week header
renderDayHeader :: forall msg. CalendarProps msg -> ResolvedConfig -> Int -> E.Element msg
renderDayHeader props config dow =
  E.div_
    [ E.style "width" config.cellSizeVal
    , E.style "height" config.cellSizeVal
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "font-size" config.weekdayFontSizeVal
    , E.style "font-weight" config.weekdayFontWeightVal
    , E.style "color" (Color.toCss config.headerTextCol)
    , E.role "columnheader"
    ]
    [ E.text (dayNameShort props.locale dow) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // month grid
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A day cell in the month grid
data MonthDay
  = DayEmpty
  | DayDate CalendarDate

derive instance eqMonthDay :: Eq MonthDay

-- | A week row
type MonthWeek =
  { weekNum :: Int
  , days :: Array MonthDay
  }

-- | The complete month grid
type MonthGrid =
  { year :: Int
  , month :: Int
  , weeks :: Array MonthWeek
  }

-- | Build the month grid for a given year/month
buildMonthGrid :: Int -> Int -> WeekStart -> MonthGrid
buildMonthGrid year month ws =
  let
    numDays = daysInMonth year month
    firstDow = firstDayOfMonth year month
    startOffset = weekStartOffset ws firstDow
    
    -- Build all day cells
    allDays = buildDayCells year month numDays startOffset
    
    -- Split into weeks
    weeks = splitIntoWeeks allDays year month
  in
    { year, month, weeks }

-- | Calculate offset for first day based on week start
weekStartOffset :: WeekStart -> Int -> Int
weekStartOffset ws firstDow =
  let
    startIdx = case ws of
      Sunday -> 0
      Monday -> 1
  in
    (firstDow - startIdx + 7) `rem` 7

-- | Build day cells with leading padding
buildDayCells :: Int -> Int -> Int -> Int -> Array MonthDay
buildDayCells year month numDays offset =
  let
    leadingEmpty = map (const DayEmpty) (range 1 offset)
    dayCells = map (\d -> DayDate { year, month, day: d }) (range 1 numDays)
    totalCells = offset + numDays
    trailingCount = (7 - (totalCells `rem` 7)) `rem` 7
    trailingEmpty = map (const DayEmpty) (range 1 trailingCount)
  in
    leadingEmpty <> dayCells <> trailingEmpty

-- | Split day cells into weeks
splitIntoWeeks :: Array MonthDay -> Int -> Int -> Array MonthWeek
splitIntoWeeks days year month = go 1 days []
  where
  go :: Int -> Array MonthDay -> Array MonthWeek -> Array MonthWeek
  go _ [] acc = acc
  go weekIdx remaining acc =
    let
      week = take 7 remaining
      rest = drop 7 remaining
      -- Calculate week number from first non-empty day, or estimate from year/month
      weekNum' = case findMap getDateFromDay week of
        Just d -> weekNumber d
        Nothing -> weekNumber { year, month, day: (weekIdx * 7) }
    in
      go (weekIdx + 1) rest (acc `snoc` { weekNum: weekNum', days: week })
  
  getDateFromDay :: MonthDay -> Maybe CalendarDate
  getDateFromDay (DayDate d) = Just d
  getDateFromDay DayEmpty = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // render weeks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render all weeks
renderWeeks :: forall msg. CalendarProps msg -> ResolvedConfig -> MonthGrid -> E.Element msg
renderWeeks props config grid =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" config.gapVal
    ]
    (map (renderWeek props config) grid.weeks)

-- | Render a single week
renderWeek :: forall msg. CalendarProps msg -> ResolvedConfig -> MonthWeek -> E.Element msg
renderWeek props config week =
  let
    weekNumCell = if props.showWeekNumbers
      then [ renderWeekNumber config week.weekNum ]
      else []
  in
    E.div_
      [ E.style "display" "flex"
      , E.role "row"
      ]
      (weekNumCell <> map (renderDay props config) week.days)

-- | Render week number cell
renderWeekNumber :: forall msg. ResolvedConfig -> Int -> E.Element msg
renderWeekNumber config num =
  E.div_
    [ E.style "width" config.cellSizeVal
    , E.style "height" config.cellSizeVal
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "font-size" config.weekdayFontSizeVal
    , E.style "color" (Color.toCss config.headerTextCol)
    ]
    [ E.text (show num) ]

-- | Render a single day cell
renderDay :: forall msg. CalendarProps msg -> ResolvedConfig -> MonthDay -> E.Element msg
renderDay props config day = case day of
  DayEmpty -> renderEmptyDay config
  DayDate date -> renderDateDay props config date

-- | Render empty day cell
renderEmptyDay :: forall msg. ResolvedConfig -> E.Element msg
renderEmptyDay config =
  E.div_
    [ E.style "width" config.cellSizeVal
    , E.style "height" config.cellSizeVal
    ]
    []

-- | Render date day cell
renderDateDay :: forall msg. CalendarProps msg -> ResolvedConfig -> CalendarDate -> E.Element msg
renderDateDay props config date =
  let
    isDisabled = isDateDisabledCheck props date
    isSelected = isDateSelectedCheck props date
    isInRange = isDateInSelectedRange props date
    isRangeStart' = isDateRangeStart props date
    isRangeEnd' = isDateRangeEnd props date
    
    -- Determine colors based on state
    bgColor = 
      if isSelected then Color.toCss config.selectedCol
      else if isInRange then Color.toCss config.rangeCol <> "40"  -- With alpha
      else "transparent"
    
    txtColor =
      if isDisabled then Color.toCss config.disabledCol
      else if isSelected then Color.toCss config.selectedTextCol
      else Color.toCss config.textCol
    
    cursor = if isDisabled then "not-allowed" else "pointer"
    opacity = if isDisabled then "0.5" else "1"
    
    -- Border radius modifications for range
    borderRadiusStyle = 
      if isRangeStart' && not isRangeEnd' then "border-top-left-radius: " <> config.cellRadius <> "; border-bottom-left-radius: " <> config.cellRadius
      else if isRangeEnd' && not isRangeStart' then "border-top-right-radius: " <> config.cellRadius <> "; border-bottom-right-radius: " <> config.cellRadius
      else if isSelected || (isRangeStart' && isRangeEnd') then config.cellRadius
      else "0"
    
    clickHandler = if isDisabled
      then []
      else case props.onSelect of
        Just handler -> [ E.onClick (handler date) ]
        Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.style "width" config.cellSizeVal
        , E.style "height" config.cellSizeVal
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "background-color" bgColor
        , E.style "color" txtColor
        , E.style "border" "none"
        , E.style "border-radius" borderRadiusStyle
        , E.style "font-size" config.dayFontSizeVal
        , E.style "font-weight" config.dayFontWeightVal
        , E.style "cursor" cursor
        , E.style "opacity" opacity
        , E.disabled isDisabled
        , E.role "gridcell"
        , E.tabIndex (if isSelected then 0 else (negate 1))
        ] <> clickHandler
      )
      [ E.text (show date.day) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // state checks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if date is disabled
isDateDisabledCheck :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateDisabledCheck props date =
  props.disabledDates date || not (isDateInRange date props.minDate props.maxDate)

-- | Check if date is selected
isDateSelectedCheck :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateSelectedCheck props date = case props.selectionMode of
  Single -> case props.selected of
    Just sel -> sameDate date sel
    Nothing -> false
  Range ->
    (case props.rangeStart of
      Just start -> sameDate date start
      Nothing -> false)
    ||
    (case props.rangeEnd of
      Just end' -> sameDate date end'
      Nothing -> false)
  Multiple -> 
    let dateVal = dateToInt date
    in elem dateVal (map dateToInt props.multiSelected)

-- | Check if date is within selected range
isDateInSelectedRange :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateInSelectedRange props date = case props.selectionMode of
  Range -> case props.rangeStart, props.rangeEnd of
    Just start, Just end' ->
      let
        dateVal = dateToInt date
        startVal = dateToInt start
        endVal = dateToInt end'
      in
        dateVal >= startVal && dateVal <= endVal
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
  Just end' -> sameDate date end'
  Nothing -> false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clamp month to valid range 1-12
clampMonth :: Int -> Int
clampMonth m
  | m < 1 = 1
  | m > 12 = 12
  | otherwise = m
