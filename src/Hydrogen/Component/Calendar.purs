-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // calendar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar component for date selection
-- |
-- | A full-featured calendar component with month view, navigation, and various
-- | selection modes. Supports locale-aware month/day names and ARIA grid pattern.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Calendar as Calendar
-- |
-- | -- Single date selection
-- | Calendar.calendar
-- |   [ Calendar.selected (Just myDate)
-- |   , Calendar.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- Date range selection
-- | Calendar.calendar
-- |   [ Calendar.selectionMode Calendar.Range
-- |   , Calendar.rangeStart state.startDate
-- |   , Calendar.rangeEnd state.endDate
-- |   , Calendar.onRangeSelect HandleRangeSelect
-- |   ]
-- |
-- | -- With constraints
-- | Calendar.calendar
-- |   [ Calendar.minDate { year: 2024, month: 1, day: 1 }
-- |   , Calendar.maxDate { year: 2024, month: 12, day: 31 }
-- |   , Calendar.disabledDates (\d -> d.day == 25)
-- |   ]
-- |
-- | -- Week starts on Monday
-- | Calendar.calendar
-- |   [ Calendar.weekStartsOn Calendar.Monday
-- |   , Calendar.locale "de-DE"
-- |   ]
-- | ```
module Hydrogen.Component.Calendar
  ( -- * Calendar Component
    calendar
  , calendarWithNav
    -- * Types
  , CalendarDate
  , DateRange
  , SelectionMode(..)
  , WeekStart(..)
    -- * Props
  , CalendarProps
  , CalendarProp
  , defaultProps
    -- * Prop Builders
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
  , className
  , onSelect
  , onRangeSelect
  , onMultiSelect
  , onMonthChange
    -- * Date Operations
  , today
  , getMonthNames
  , getMonthNamesShort
  , getDayNames
  , getDayNamesShort
  , getDayNamesNarrow
  , getDaysInMonth
  , getFirstDayOfMonth
  , formatDate
  , parseDate
  , compareDates
  , sameDate
  , addDays
  , addMonths
  , getWeekNumber
  , isLeapYear
  , isDateInRange
  , isDateDisabled
    -- * Month Grid
  , MonthGrid
  , MonthWeek
  , MonthDay(..)
  , buildMonthGrid
  ) where

import Prelude

import Data.Array (foldl, range, snoc)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Int (rem)
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A date represented as year, month (1-12), and day
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
  = Single    -- ^ Select a single date
  | Range     -- ^ Select a date range (start to end)
  | Multiple  -- ^ Select multiple individual dates

derive instance eqSelectionMode :: Eq SelectionMode

-- | Which day the week starts on
data WeekStart
  = Sunday
  | Monday

derive instance eqWeekStart :: Eq WeekStart

-- | Convert WeekStart to day index (0 = Sunday)
weekStartIndex :: WeekStart -> Int
weekStartIndex Sunday = 0
weekStartIndex Monday = 1

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calendar properties
type CalendarProps i =
  { viewMonth :: Int              -- Currently viewed month (1-12)
  , viewYear :: Int               -- Currently viewed year
  , selected :: Maybe CalendarDate
  , selectionMode :: SelectionMode
  , rangeStart :: Maybe CalendarDate
  , rangeEnd :: Maybe CalendarDate
  , multiSelected :: Array CalendarDate
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  , weekStartsOn :: WeekStart
  , locale :: String
  , showWeekNumbers :: Boolean
  , className :: String
  , onSelect :: Maybe (CalendarDate -> i)
  , onRangeSelect :: Maybe (DateRange -> i)
  , onMultiSelect :: Maybe (Array CalendarDate -> i)
  , onMonthChange :: Maybe ({ year :: Int, month :: Int } -> i)
  }

-- | Property modifier
type CalendarProp i = CalendarProps i -> CalendarProps i

-- | Default calendar properties
defaultProps :: forall i. CalendarProps i
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
  , locale: "en-US"
  , showWeekNumbers: false
  , className: ""
  , onSelect: Nothing
  , onRangeSelect: Nothing
  , onMultiSelect: Nothing
  , onMonthChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set the selected date
selected :: forall i. Maybe CalendarDate -> CalendarProp i
selected d props = props { selected = d }

-- | Set selection mode
selectionMode :: forall i. SelectionMode -> CalendarProp i
selectionMode m props = props { selectionMode = m }

-- | Set range start date
rangeStart :: forall i. Maybe CalendarDate -> CalendarProp i
rangeStart d props = props { rangeStart = d }

-- | Set range end date
rangeEnd :: forall i. Maybe CalendarDate -> CalendarProp i
rangeEnd d props = props { rangeEnd = d }

-- | Set multiple selected dates
multiSelected :: forall i. Array CalendarDate -> CalendarProp i
multiSelected dates props = props { multiSelected = dates }

-- | Set minimum selectable date
minDate :: forall i. CalendarDate -> CalendarProp i
minDate d props = props { minDate = Just d }

-- | Set maximum selectable date
maxDate :: forall i. CalendarDate -> CalendarProp i
maxDate d props = props { maxDate = Just d }

-- | Set custom disabled dates predicate
disabledDates :: forall i. (CalendarDate -> Boolean) -> CalendarProp i
disabledDates pred props = props { disabledDates = pred }

-- | Set which day the week starts on
weekStartsOn :: forall i. WeekStart -> CalendarProp i
weekStartsOn ws props = props { weekStartsOn = ws }

-- | Set locale for month/day names
locale :: forall i. String -> CalendarProp i
locale l props = props { locale = l }

-- | Show week numbers
showWeekNumbers :: forall i. Boolean -> CalendarProp i
showWeekNumbers show props = props { showWeekNumbers = show }

-- | Add custom class
className :: forall i. String -> CalendarProp i
className c props = props { className = props.className <> " " <> c }

-- | Set single date select handler
onSelect :: forall i. (CalendarDate -> i) -> CalendarProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set range select handler
onRangeSelect :: forall i. (DateRange -> i) -> CalendarProp i
onRangeSelect handler props = props { onRangeSelect = Just handler }

-- | Set multi-select handler
onMultiSelect :: forall i. (Array CalendarDate -> i) -> CalendarProp i
onMultiSelect handler props = props { onMultiSelect = Just handler }

-- | Set month change handler
onMonthChange :: forall i. ({ year :: Int, month :: Int } -> i) -> CalendarProp i
onMonthChange handler props = props { onMonthChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // date operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get today's date
today :: Effect CalendarDate
today = getTodayImpl

-- | Get localized month names (January, February, ...)
getMonthNames :: String -> Effect (Array String)
getMonthNames = getMonthNamesImpl

-- | Get short localized month names (Jan, Feb, ...)
getMonthNamesShort :: String -> Effect (Array String)
getMonthNamesShort = getMonthNamesShortImpl

-- | Get localized day names starting from Sunday
getDayNames :: String -> Effect (Array String)
getDayNames = getDayNamesImpl

-- | Get short localized day names starting from Sunday
getDayNamesShort :: String -> Effect (Array String)
getDayNamesShort = getDayNamesShortImpl

-- | Get narrow localized day names (S, M, T, ...)
getDayNamesNarrow :: String -> Effect (Array String)
getDayNamesNarrow = getDayNamesNarrowImpl

-- | Get number of days in a month
getDaysInMonth :: Int -> Int -> Int
getDaysInMonth = getDaysInMonthImpl

-- | Get day of week for first day of month (0 = Sunday)
getFirstDayOfMonth :: Int -> Int -> Int
getFirstDayOfMonth = getFirstDayOfMonthImpl

-- | Format a date according to locale
formatDate :: String -> CalendarDate -> String -> Effect String
formatDate = formatDateImpl

-- | Parse a date string
parseDate :: String -> Effect (Maybe CalendarDate)
parseDate str = do
  result <- parseDateImpl str
  pure $ toMaybe result

-- | Compare two dates: -1 (a < b), 0 (equal), 1 (a > b)
compareDates :: CalendarDate -> CalendarDate -> Int
compareDates = compareDatesImpl

-- | Check if two dates are the same
sameDate :: CalendarDate -> CalendarDate -> Boolean
sameDate = sameDateImpl

-- | Add days to a date
addDays :: CalendarDate -> Int -> CalendarDate
addDays = addDaysImpl

-- | Add months to a date
addMonths :: CalendarDate -> Int -> CalendarDate
addMonths = addMonthsImpl

-- | Get ISO week number
getWeekNumber :: CalendarDate -> Int
getWeekNumber = getWeekNumberImpl

-- | Check if a year is a leap year
isLeapYear :: Int -> Boolean
isLeapYear = isLeapYearImpl

-- | Check if date is within a range (inclusive)
isDateInRange :: CalendarDate -> Maybe CalendarDate -> Maybe CalendarDate -> Boolean
isDateInRange date minD maxD =
  let
    afterMin = case minD of
      Nothing -> true
      Just min -> compareDates date min >= 0
    beforeMax = case maxD of
      Nothing -> true
      Just max -> compareDates date max <= 0
  in afterMin && beforeMax

-- | Check if a date is disabled
isDateDisabled :: CalendarProps Unit -> CalendarDate -> Boolean
isDateDisabled props date =
  props.disabledDates date || not (isDateInRange date props.minDate props.maxDate)

-- FFI imports
foreign import getTodayImpl :: Effect CalendarDate
foreign import getMonthNamesImpl :: String -> Effect (Array String)
foreign import getMonthNamesShortImpl :: String -> Effect (Array String)
foreign import getDayNamesImpl :: String -> Effect (Array String)
foreign import getDayNamesShortImpl :: String -> Effect (Array String)
foreign import getDayNamesNarrowImpl :: String -> Effect (Array String)
foreign import getDaysInMonthImpl :: Int -> Int -> Int
foreign import getFirstDayOfMonthImpl :: Int -> Int -> Int
foreign import formatDateImpl :: String -> CalendarDate -> String -> Effect String
foreign import parseDateImpl :: String -> Effect (Nullable CalendarDate)
foreign import compareDatesImpl :: CalendarDate -> CalendarDate -> Int
foreign import sameDateImpl :: CalendarDate -> CalendarDate -> Boolean
foreign import addDaysImpl :: CalendarDate -> Int -> CalendarDate
foreign import addMonthsImpl :: CalendarDate -> Int -> CalendarDate
foreign import getWeekNumberImpl :: CalendarDate -> Int
foreign import isLeapYearImpl :: Int -> Boolean

-- Nullable handling
foreign import data Nullable :: Type -> Type

toMaybe :: forall a. Nullable a -> Maybe a
toMaybe = toMaybeImpl Just Nothing

foreign import toMaybeImpl :: forall a. (a -> Maybe a) -> Maybe a -> Nullable a -> Maybe a

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // month grid
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A day cell in the month grid
data MonthDay
  = DayEmpty                           -- Empty cell (padding)
  | DayDate CalendarDate               -- A date cell
  | DayDateDisabled CalendarDate       -- A disabled date cell

derive instance eqMonthDay :: Eq MonthDay

-- | A week row in the month grid
type MonthWeek =
  { weekNumber :: Int
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
buildMonthGrid year month weekStart =
  let
    daysInMonth = getDaysInMonth year month
    firstDayOfWeek = getFirstDayOfMonth year month
    startOffset = weekStartIndex weekStart
    
    -- Adjust first day based on week start
    adjustedFirstDay = (firstDayOfWeek - startOffset + 7) `rem` 7
    
    -- Build all day cells
    allDays = buildDayCells year month daysInMonth adjustedFirstDay
    
    -- Split into weeks
    weeks = splitIntoWeeks allDays year month
  in
    { year, month, weeks }

-- | Build day cells with padding
buildDayCells :: Int -> Int -> Int -> Int -> Array MonthDay
buildDayCells year month daysInMonth offset =
  let
    -- Leading empty cells
    leadingEmpty = map (const DayEmpty) (range 1 offset)
    
    -- Actual day cells
    dayCells = map (\d -> DayDate { year, month, day: d }) (range 1 daysInMonth)
    
    -- Trailing empty cells to complete last week
    totalCells = offset + daysInMonth
    trailingCount = (7 - (totalCells `rem` 7)) `rem` 7
    trailingEmpty = map (const DayEmpty) (range 1 trailingCount)
  in
    leadingEmpty <> dayCells <> trailingEmpty

-- | Split day cells into weeks
splitIntoWeeks :: Array MonthDay -> Int -> Int -> Array MonthWeek
splitIntoWeeks days _year _month = go 0 days []
  where
  go :: Int -> Array MonthDay -> Array MonthWeek -> Array MonthWeek
  go _ [] acc = acc
  go weekIdx remaining acc =
    let
      week = Array.take 7 remaining
      rest = Array.drop 7 remaining
      -- Calculate week number from first non-empty day
      weekNum = case Array.findMap getDateFromDay week of
        Just d -> getWeekNumber d
        Nothing -> weekIdx + 1
    in
      go (weekIdx + 1) rest (acc `snoc` { weekNumber: weekNum, days: week })
  
  getDateFromDay :: MonthDay -> Maybe CalendarDate
  getDateFromDay (DayDate d) = Just d
  getDateFromDay (DayDateDisabled d) = Just d
  getDateFromDay DayEmpty = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base calendar classes
baseClasses :: String
baseClasses = "p-3 bg-background rounded-lg border"

-- | Day cell classes
dayCellClasses :: String
dayCellClasses = "h-9 w-9 text-center text-sm p-0 relative"

-- | Render a calendar
calendar :: forall w i. Array (CalendarProp i) -> HH.HTML w i
calendar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    HH.div
      [ cls [ baseClasses, props.className ]
      , ARIA.role "grid"
      , ARIA.label "Calendar"
      ]
      [ renderHeader props
      , renderDayHeaders props
      , renderWeeks props grid
      ]

-- | Render calendar with navigation controls
calendarWithNav :: forall w i. Array (CalendarProp i) -> HH.HTML w i
calendarWithNav propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    HH.div
      [ cls [ baseClasses, props.className ]
      , ARIA.role "grid"
      , ARIA.label "Calendar"
      ]
      [ renderNavHeader props
      , renderDayHeaders props
      , renderWeeks props grid
      ]

-- | Render the month/year header
renderHeader :: forall w i. CalendarProps i -> HH.HTML w i
renderHeader props =
  HH.div
    [ cls [ "flex justify-center pt-1 relative items-center" ] ]
    [ HH.div
        [ cls [ "text-sm font-medium" ] ]
        [ HH.text $ monthName props.viewMonth <> " " <> show props.viewYear ]
    ]
  where
  -- Simplified month name (would use FFI in real app)
  monthName m = case m of
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

-- | Render navigation header with prev/next buttons
renderNavHeader :: forall w i. CalendarProps i -> HH.HTML w i
renderNavHeader props =
  HH.div
    [ cls [ "flex justify-between items-center px-1 pb-2" ] ]
    [ -- Previous month button
      HH.button
        [ cls [ navButtonClasses ]
        , HP.type_ HP.ButtonButton
        , ARIA.label "Previous month"
        ]
        [ HH.text "‹" ]
    , -- Month/Year display
      HH.div
        [ cls [ "text-sm font-medium" ] ]
        [ HH.text $ monthName props.viewMonth <> " " <> show props.viewYear ]
    , -- Next month button
      HH.button
        [ cls [ navButtonClasses ]
        , HP.type_ HP.ButtonButton
        , ARIA.label "Next month"
        ]
        [ HH.text "›" ]
    ]
  where
  navButtonClasses = "h-7 w-7 bg-transparent p-0 hover:bg-accent hover:text-accent-foreground rounded-md inline-flex items-center justify-center"
  
  monthName m = case m of
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

-- | Render day-of-week headers
renderDayHeaders :: forall w i. CalendarProps i -> HH.HTML w i
renderDayHeaders props =
  let
    baseDays = ["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"]
    days = case props.weekStartsOn of
      Sunday -> baseDays
      Monday -> rotateArray 1 baseDays
  in
    HH.div
      [ cls [ "flex" ]
      , ARIA.role "row"
      ]
      ( (if props.showWeekNumbers then [ weekNumHeaderCell ] else [])
        <> map renderDayHeader days
      )
  where
  weekNumHeaderCell =
    HH.div
      [ cls [ "w-9 text-muted-foreground text-xs text-center font-normal" ] ]
      [ HH.text "#" ]
  
  renderDayHeader day =
    HH.div
      [ cls [ "w-9 text-muted-foreground text-xs text-center font-normal" ]
      , ARIA.role "columnheader"
      ]
      [ HH.text day ]

-- | Render all weeks
renderWeeks :: forall w i. CalendarProps i -> MonthGrid -> HH.HTML w i
renderWeeks props grid =
  HH.div
    [ cls [ "flex flex-col gap-1" ] ]
    (map (renderWeek props) grid.weeks)

-- | Render a single week
renderWeek :: forall w i. CalendarProps i -> MonthWeek -> HH.HTML w i
renderWeek props week =
  HH.div
    [ cls [ "flex" ]
    , ARIA.role "row"
    ]
    ( (if props.showWeekNumbers then [ renderWeekNumber week.weekNumber ] else [])
      <> map (renderDay props) week.days
    )

-- | Render week number
renderWeekNumber :: forall w i. Int -> HH.HTML w i
renderWeekNumber num =
  HH.div
    [ cls [ "w-9 text-muted-foreground text-xs flex items-center justify-center" ] ]
    [ HH.text (show num) ]

-- | Render a single day cell
renderDay :: forall w i. CalendarProps i -> MonthDay -> HH.HTML w i
renderDay props day = case day of
  DayEmpty ->
    HH.div [ cls [ dayCellClasses ] ] []
  
  DayDate date ->
    let
      isDisabled = isDateDisabledProp props date
      isSelected = isDateSelected props date
      isInRange = isDateInSelectedRange props date
      isRangeStart = isDateRangeStart props date
      isRangeEnd = isDateRangeEnd props date
      isToday' = false -- Would check against actual today in real app
      
      cellClasses = dayCellClasses <> " " <>
        (if isDisabled then "text-muted-foreground opacity-50 cursor-not-allowed"
         else if isSelected then "bg-primary text-primary-foreground hover:bg-primary hover:text-primary-foreground"
         else if isInRange then "bg-accent"
         else "hover:bg-accent hover:text-accent-foreground cursor-pointer") <>
        (if isRangeStart then " rounded-l-md" else "") <>
        (if isRangeEnd then " rounded-r-md" else "") <>
        (if isToday' then " ring-1 ring-ring" else "")
    in
      HH.button
        ( [ cls [ cellClasses ]
          , HP.type_ HP.ButtonButton
          , HP.disabled isDisabled
          , ARIA.role "gridcell"
          , HP.tabIndex (if isSelected then 0 else (-1))
          ]
          <> if isDisabled then [] else
              case props.onSelect of
                Just handler -> [ HE.onClick \_ -> handler date ]
                Nothing -> []
        )
        [ HH.text (show date.day) ]
  
  DayDateDisabled date ->
    HH.div
      [ cls [ dayCellClasses, "text-muted-foreground opacity-50" ]
      , ARIA.role "gridcell"
      ]
      [ HH.text (show date.day) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if date is disabled based on props
isDateDisabledProp :: forall i. CalendarProps i -> CalendarDate -> Boolean
isDateDisabledProp props date =
  props.disabledDates date || not (isDateInRange date props.minDate props.maxDate)

-- | Check if date is selected
isDateSelected :: forall i. CalendarProps i -> CalendarDate -> Boolean
isDateSelected props date = case props.selectionMode of
  Single -> case props.selected of
    Just sel -> sameDate date sel
    Nothing -> false
  Range ->
    case props.rangeStart of
      Just start -> sameDate date start
      Nothing -> false
    ||
    case props.rangeEnd of
      Just end -> sameDate date end
      Nothing -> false
  Multiple -> Array.any (sameDate date) props.multiSelected

-- | Check if date is within selected range
isDateInSelectedRange :: forall i. CalendarProps i -> CalendarDate -> Boolean
isDateInSelectedRange props date = case props.selectionMode of
  Range -> case props.rangeStart, props.rangeEnd of
    Just start, Just end ->
      compareDates date start >= 0 && compareDates date end <= 0
    _, _ -> false
  _ -> false

-- | Check if date is range start
isDateRangeStart :: forall i. CalendarProps i -> CalendarDate -> Boolean
isDateRangeStart props date = case props.rangeStart of
  Just start -> sameDate date start
  Nothing -> false

-- | Check if date is range end
isDateRangeEnd :: forall i. CalendarProps i -> CalendarDate -> Boolean
isDateRangeEnd props date = case props.rangeEnd of
  Just end -> sameDate date end
  Nothing -> false

-- | Rotate an array by n positions
rotateArray :: forall a. Int -> Array a -> Array a
rotateArray n arr = Array.drop n arr <> Array.take n arr
