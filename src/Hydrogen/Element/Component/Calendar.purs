-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // calendar
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
-- | import Hydrogen.Element.Component.Calendar as Calendar
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

module Hydrogen.Element.Component.Calendar
  ( -- * Component
    calendar
  , calendarWithNav
  
  -- * Types
  , CalendarDate
  , DateRange
  , SelectionMode(..)
  , WeekStart(..)
  , MonthDay(..)
  , MonthWeek
  , MonthGrid
  
  -- * Props
  , CalendarProps
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
  
  -- * Date Operations (re-exported from FFI)
  , getDaysInMonth
  , getFirstDayOfMonth
  , compareDates
  , sameDate
  , addDays
  , addMonths
  , getWeekNumber
  , isLeapYear
  
  -- * Grid Building
  , buildMonthGrid
  ) where

import Prelude
  ( class Eq
  , class Show
  , const
  , map
  , not
  , otherwise
  , show
  , (&&)
  , (+)
  , (-)
  , (<)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (||)
  )

import Data.Array (foldl, snoc)
import Data.Array as Array
import Data.Int (rem)
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

instance showSelectionMode :: Show SelectionMode where
  show Single = "Single"
  show Range = "Range"
  show Multiple = "Multiple"

-- | Which day the week starts on
data WeekStart
  = Sunday
  | Monday

derive instance eqWeekStart :: Eq WeekStart

instance showWeekStart :: Show WeekStart where
  show Sunday = "Sunday"
  show Monday = "Monday"

-- | Convert WeekStart to day index (0 = Sunday)
weekStartIndex :: WeekStart -> Int
weekStartIndex Sunday = 0
weekStartIndex Monday = 1

-- | A day cell in the month grid
data MonthDay
  = DayEmpty                           -- Empty cell (padding)
  | DayDate CalendarDate               -- A date cell

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // date operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get number of days in a month
getDaysInMonth :: Int -> Int -> Int
getDaysInMonth = getDaysInMonthImpl

-- | Get day of week for first day of month (0 = Sunday)
getFirstDayOfMonth :: Int -> Int -> Int
getFirstDayOfMonth = getFirstDayOfMonthImpl

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

-- FFI imports
foreign import getDaysInMonthImpl :: Int -> Int -> Int
foreign import getFirstDayOfMonthImpl :: Int -> Int -> Int
foreign import compareDatesImpl :: CalendarDate -> CalendarDate -> Int
foreign import sameDateImpl :: CalendarDate -> CalendarDate -> Boolean
foreign import addDaysImpl :: CalendarDate -> Int -> CalendarDate
foreign import addMonthsImpl :: CalendarDate -> Int -> CalendarDate
foreign import getWeekNumberImpl :: CalendarDate -> Int
foreign import isLeapYearImpl :: Int -> Boolean

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // month grid
-- ═══════════════════════════════════════════════════════════════════════════════

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
    leadingEmpty = buildEmptyCells offset
    
    -- Actual day cells
    dayCells = buildDateCells year month daysInMonth
    
    -- Trailing empty cells to complete last week
    totalCells = offset + daysInMonth
    trailingCount = (7 - (totalCells `rem` 7)) `rem` 7
    trailingEmpty = buildEmptyCells trailingCount
  in
    leadingEmpty <> dayCells <> trailingEmpty

-- | Build empty cells
buildEmptyCells :: Int -> Array MonthDay
buildEmptyCells count = go count []
  where
  go :: Int -> Array MonthDay -> Array MonthDay
  go n acc
    | n < 1 = acc
    | otherwise = go (n - 1) (acc `snoc` DayEmpty)

-- | Build date cells
buildDateCells :: Int -> Int -> Int -> Array MonthDay
buildDateCells year month daysInMonth = go 1 []
  where
  go :: Int -> Array MonthDay -> Array MonthDay
  go day acc
    | day > daysInMonth = acc
    | otherwise = go (day + 1) (acc `snoc` DayDate { year, month, day })

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
  getDateFromDay DayEmpty = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

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
          [ E.text (monthName props.viewMonth <> " " <> show props.viewYear) ]
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
          [ E.text (monthName props.viewMonth <> " " <> show props.viewYear) ]
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- | Month name lookup
monthName :: Int -> String
monthName = case _ of
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

-- | Rotate an array by n positions
rotateArray :: forall a. Int -> Array a -> Array a
rotateArray n arr = Array.drop n arr <> Array.take n arr

-- | Helper to add style only if value is non-empty
maybeStyle :: forall msg. String -> String -> Array (E.Attribute msg)
maybeStyle _ "" = []
maybeStyle prop val = [ E.style prop val ]
