-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // daterangepicker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DateRangePicker component for selecting date ranges
-- |
-- | A date range picker with two side-by-side calendars, preset ranges,
-- | and optional comparison mode for analytics and reporting use cases.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.DateRangePicker as DateRangePicker
-- |
-- | -- Basic range picker
-- | DateRangePicker.dateRangePicker
-- |   [ DateRangePicker.startDate state.start
-- |   , DateRangePicker.endDate state.end
-- |   , DateRangePicker.onChange HandleRangeChange
-- |   ]
-- |
-- | -- With presets
-- | DateRangePicker.dateRangePicker
-- |   [ DateRangePicker.startDate state.start
-- |   , DateRangePicker.endDate state.end
-- |   , DateRangePicker.showPresets true
-- |   , DateRangePicker.onChange HandleRangeChange
-- |   ]
-- |
-- | -- With comparison mode
-- | DateRangePicker.dateRangePicker
-- |   [ DateRangePicker.startDate state.start
-- |   , DateRangePicker.endDate state.end
-- |   , DateRangePicker.enableComparison true
-- |   , DateRangePicker.comparisonMode DateRangePicker.PreviousPeriod
-- |   , DateRangePicker.onChange HandleRangeChange
-- |   ]
-- |
-- | -- Custom presets
-- | DateRangePicker.dateRangePicker
-- |   [ DateRangePicker.presets
-- |       [ { label: "Last Quarter", getRange: lastQuarterRange }
-- |       , { label: "Year to Date", getRange: yearToDateRange }
-- |       ]
-- |   , DateRangePicker.onChange HandleRangeChange
-- |   ]
-- | ```
module Hydrogen.Component.DateRangePicker
  ( -- * DateRangePicker Component
    dateRangePicker
  , dateRangePickerWithLabel
    -- * Types
  , DateRange
  , PresetRange
  , ComparisonMode(PreviousPeriod, PreviousYear, Custom)
  , defaultPresets
    -- * Props
  , DateRangePickerProps
  , DateRangePickerProp
  , defaultProps
    -- * Prop Builders
  , startDate
  , endDate
  , minDate
  , maxDate
  , disabledDates
  , weekStartsOn
  , locale
  , showPresets
  , presets
  , enableComparison
  , comparisonMode
  , comparisonStart
  , comparisonEnd
  , className
  , isOpen
  , disabled
  , placeholder
  , onChange
  , onComparisonChange
  , onPresetSelect
  , onOpen
  , onClose
    -- * Preset Generators
  , todayRange
  , yesterdayRange
  , last7DaysRange
  , last30DaysRange
  , thisWeekRange
  , lastWeekRange
  , thisMonthRange
  , lastMonthRange
  , thisYearRange
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Component.Calendar (CalendarDate, WeekStart(Sunday, Monday), addDays, addMonths)
import Hydrogen.Component.Calendar as Calendar
import Hydrogen.Component.DatePicker (formatDateString, DateFormat(ISO))
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A date range
type DateRange =
  { start :: CalendarDate
  , end :: CalendarDate
  }

-- | A preset range definition
type PresetRange =
  { label :: String
  , getRange :: Effect DateRange
  }

-- | Comparison mode for analytics
data ComparisonMode
  = PreviousPeriod   -- ^ Same duration, immediately before
  | PreviousYear     -- ^ Same dates, previous year
  | Custom           -- ^ Custom comparison range

derive instance eqComparisonMode :: Eq ComparisonMode

instance showComparisonMode :: Show ComparisonMode where
  show PreviousPeriod = "Previous period"
  show PreviousYear = "Previous year"
  show Custom = "Custom"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | DateRangePicker properties
type DateRangePickerProps i =
  { startDate :: Maybe CalendarDate
  , endDate :: Maybe CalendarDate
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  , weekStartsOn :: WeekStart
  , locale :: String
  , showPresets :: Boolean
  , presets :: Array PresetRange
  , enableComparison :: Boolean
  , comparisonMode :: ComparisonMode
  , comparisonStart :: Maybe CalendarDate
  , comparisonEnd :: Maybe CalendarDate
  , className :: String
  , isOpen :: Boolean
  , disabled :: Boolean
  , placeholder :: String
  , leftMonth :: Int
  , leftYear :: Int
  , rightMonth :: Int
  , rightYear :: Int
  , selectingStart :: Boolean
  , onChange :: Maybe (DateRange -> i)
  , onComparisonChange :: Maybe (DateRange -> i)
  , onPresetSelect :: Maybe (String -> i)
  , onOpen :: Maybe (Unit -> i)
  , onClose :: Maybe (Unit -> i)
  }

-- | Property modifier
type DateRangePickerProp i = DateRangePickerProps i -> DateRangePickerProps i

-- | Default properties
defaultProps :: forall i. DateRangePickerProps i
defaultProps =
  { startDate: Nothing
  , endDate: Nothing
  , minDate: Nothing
  , maxDate: Nothing
  , disabledDates: const false
  , weekStartsOn: Sunday
  , locale: "en-US"
  , showPresets: true
  , presets: []
  , enableComparison: false
  , comparisonMode: PreviousPeriod
  , comparisonStart: Nothing
  , comparisonEnd: Nothing
  , className: ""
  , isOpen: false
  , disabled: false
  , placeholder: "Select date range..."
  , leftMonth: 1
  , leftYear: 2024
  , rightMonth: 2
  , rightYear: 2024
  , selectingStart: true
  , onChange: Nothing
  , onComparisonChange: Nothing
  , onPresetSelect: Nothing
  , onOpen: Nothing
  , onClose: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set start date
startDate :: forall i. Maybe CalendarDate -> DateRangePickerProp i
startDate d props = props { startDate = d }

-- | Set end date
endDate :: forall i. Maybe CalendarDate -> DateRangePickerProp i
endDate d props = props { endDate = d }

-- | Set minimum date
minDate :: forall i. CalendarDate -> DateRangePickerProp i
minDate d props = props { minDate = Just d }

-- | Set maximum date
maxDate :: forall i. CalendarDate -> DateRangePickerProp i
maxDate d props = props { maxDate = Just d }

-- | Set disabled dates predicate
disabledDates :: forall i. (CalendarDate -> Boolean) -> DateRangePickerProp i
disabledDates pred props = props { disabledDates = pred }

-- | Set week start day
weekStartsOn :: forall i. WeekStart -> DateRangePickerProp i
weekStartsOn ws props = props { weekStartsOn = ws }

-- | Set locale
locale :: forall i. String -> DateRangePickerProp i
locale l props = props { locale = l }

-- | Show preset ranges
showPresets :: forall i. Boolean -> DateRangePickerProp i
showPresets show props = props { showPresets = show }

-- | Set custom presets
presets :: forall i. Array PresetRange -> DateRangePickerProp i
presets p props = props { presets = p }

-- | Enable comparison mode
enableComparison :: forall i. Boolean -> DateRangePickerProp i
enableComparison e props = props { enableComparison = e }

-- | Set comparison mode
comparisonMode :: forall i. ComparisonMode -> DateRangePickerProp i
comparisonMode m props = props { comparisonMode = m }

-- | Set comparison start date
comparisonStart :: forall i. Maybe CalendarDate -> DateRangePickerProp i
comparisonStart d props = props { comparisonStart = d }

-- | Set comparison end date
comparisonEnd :: forall i. Maybe CalendarDate -> DateRangePickerProp i
comparisonEnd d props = props { comparisonEnd = d }

-- | Add custom class
className :: forall i. String -> DateRangePickerProp i
className c props = props { className = props.className <> " " <> c }

-- | Set open state
isOpen :: forall i. Boolean -> DateRangePickerProp i
isOpen o props = props { isOpen = o }

-- | Set disabled state
disabled :: forall i. Boolean -> DateRangePickerProp i
disabled d props = props { disabled = d }

-- | Set placeholder text
placeholder :: forall i. String -> DateRangePickerProp i
placeholder p props = props { placeholder = p }

-- | Set change handler
onChange :: forall i. (DateRange -> i) -> DateRangePickerProp i
onChange handler props = props { onChange = Just handler }

-- | Set comparison change handler
onComparisonChange :: forall i. (DateRange -> i) -> DateRangePickerProp i
onComparisonChange handler props = props { onComparisonChange = Just handler }

-- | Set preset select handler
onPresetSelect :: forall i. (String -> i) -> DateRangePickerProp i
onPresetSelect handler props = props { onPresetSelect = Just handler }

-- | Set open handler
onOpen :: forall i. (Unit -> i) -> DateRangePickerProp i
onOpen handler props = props { onOpen = Just handler }

-- | Set close handler
onClose :: forall i. (Unit -> i) -> DateRangePickerProp i
onClose handler props = props { onClose = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // preset helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get today's date as a range
todayRange :: Effect DateRange
todayRange = do
  t <- Calendar.today
  pure { start: t, end: t }

-- | Yesterday as a range
yesterdayRange :: Effect DateRange
yesterdayRange = do
  t <- Calendar.today
  let yesterday = addDays t (-1)
  pure { start: yesterday, end: yesterday }

-- | Last 7 days
last7DaysRange :: Effect DateRange
last7DaysRange = do
  t <- Calendar.today
  let start = addDays t (-6)
  pure { start, end: t }

-- | Last 30 days
last30DaysRange :: Effect DateRange
last30DaysRange = do
  t <- Calendar.today
  let start = addDays t (-29)
  pure { start, end: t }

-- | This week (starting Sunday or Monday based on locale)
thisWeekRange :: WeekStart -> Effect DateRange
thisWeekRange weekStart = do
  t <- Calendar.today
  -- Would need to calculate actual week start
  let daysBack = case weekStart of
        Sunday -> 0  -- Simplified
        Monday -> 0
  let start = addDays t (-daysBack)
  pure { start, end: t }

-- | Last week
lastWeekRange :: WeekStart -> Effect DateRange
lastWeekRange _ = do
  t <- Calendar.today
  let end = addDays t (-7)
  let start = addDays end (-6)
  pure { start, end }

-- | This month (1st to today)
thisMonthRange :: Effect DateRange
thisMonthRange = do
  t <- Calendar.today
  let start = { year: t.year, month: t.month, day: 1 }
  pure { start, end: t }

-- | Last month
lastMonthRange :: Effect DateRange
lastMonthRange = do
  t <- Calendar.today
  let lastMonth = addMonths t (-1)
  let start = { year: lastMonth.year, month: lastMonth.month, day: 1 }
  let daysInLastMonth = Calendar.getDaysInMonth lastMonth.year lastMonth.month
  let end = { year: lastMonth.year, month: lastMonth.month, day: daysInLastMonth }
  pure { start, end }

-- | This year (Jan 1 to today)
thisYearRange :: Effect DateRange
thisYearRange = do
  t <- Calendar.today
  let start = { year: t.year, month: 1, day: 1 }
  pure { start, end: t }

-- | Default preset ranges
defaultPresets :: Array PresetRange
defaultPresets =
  [ { label: "Today", getRange: todayRange }
  , { label: "Yesterday", getRange: yesterdayRange }
  , { label: "Last 7 days", getRange: last7DaysRange }
  , { label: "Last 30 days", getRange: last30DaysRange }
  , { label: "This month", getRange: thisMonthRange }
  , { label: "Last month", getRange: lastMonthRange }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base input classes
inputClasses :: String
inputClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Render a date range picker
dateRangePicker :: forall w i. Array (DateRangePickerProp i) -> HH.HTML w i
dateRangePicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    displayText = case props.startDate, props.endDate of
      Just start, Just end ->
        formatDateString ISO start <> " - " <> formatDateString ISO end
      Just start, Nothing ->
        formatDateString ISO start <> " - ..."
      Nothing, Just end ->
        "... - " <> formatDateString ISO end
      Nothing, Nothing ->
        props.placeholder
  in
    HH.div
      [ cls [ "relative inline-block", props.className ] ]
      [ -- Trigger button
        HH.button
          ( [ cls [ inputClasses, "text-left justify-start" ]
            , HP.type_ HP.ButtonButton
            , HP.disabled props.disabled
            , ARIA.hasPopup "dialog"
            , ARIA.expanded (show props.isOpen)
            ]
            <> case props.onOpen of
                Just handler -> [ HE.onClick \_ -> handler unit ]
                Nothing -> []
          )
          [ -- Calendar icon
            HH.span
              [ cls [ "mr-2 text-muted-foreground" ] ]
              [ calendarIcon ]
          , HH.text displayText
          ]
      
      , -- Popup panel
        if props.isOpen then
          HH.div
            [ cls [ "absolute z-50 mt-1 bg-background border rounded-lg shadow-lg p-4" ]
            , ARIA.role "dialog"
            , ARIA.modal "true"
            ]
            [ HH.div
                [ cls [ "flex gap-4" ] ]
                [ -- Presets sidebar
                  if props.showPresets then
                    renderPresetsSidebar props
                  else HH.text ""
                
                , -- Calendars
                  HH.div
                    [ cls [ "flex gap-4" ] ]
                    [ -- Left calendar
                      HH.div
                        []
                        [ HH.div
                            [ cls [ "text-sm font-medium text-center mb-2" ] ]
                            [ HH.text $ monthName props.leftMonth <> " " <> show props.leftYear ]
                        , Calendar.calendar
                            [ Calendar.selectionMode Calendar.Range
                            , Calendar.rangeStart props.startDate
                            , Calendar.rangeEnd props.endDate
                            , Calendar.weekStartsOn props.weekStartsOn
                            , case props.minDate of
                                Just d -> Calendar.minDate d
                                Nothing -> identity
                            , case props.maxDate of
                                Just d -> Calendar.maxDate d
                                Nothing -> identity
                            , Calendar.disabledDates props.disabledDates
                            ]
                        ]
                    
                    , -- Right calendar
                      HH.div
                        []
                        [ HH.div
                            [ cls [ "text-sm font-medium text-center mb-2" ] ]
                            [ HH.text $ monthName props.rightMonth <> " " <> show props.rightYear ]
                        , Calendar.calendar
                            [ Calendar.selectionMode Calendar.Range
                            , Calendar.rangeStart props.startDate
                            , Calendar.rangeEnd props.endDate
                            , Calendar.weekStartsOn props.weekStartsOn
                            , case props.minDate of
                                Just d -> Calendar.minDate d
                                Nothing -> identity
                            , case props.maxDate of
                                Just d -> Calendar.maxDate d
                                Nothing -> identity
                            , Calendar.disabledDates props.disabledDates
                            ]
                        ]
                    ]
                ]
            
            , -- Comparison section
              if props.enableComparison then
                renderComparisonSection props
              else HH.text ""
            
            , -- Footer with inputs and buttons
              renderFooter props
            ]
        else HH.text ""
      ]

-- | Render presets sidebar
renderPresetsSidebar :: forall w i. DateRangePickerProps i -> HH.HTML w i
renderPresetsSidebar props =
  let
    presetsToUse = if null props.presets then defaultPresets else props.presets
  in
    HH.div
      [ cls [ "border-r pr-4 min-w-[140px]" ] ]
      [ HH.div
          [ cls [ "text-sm font-medium mb-2" ] ]
          [ HH.text "Quick select" ]
      , HH.div
          [ cls [ "flex flex-col gap-1" ] ]
          (map renderPresetButton presetsToUse)
      ]
  where
  renderPresetButton preset =
    HH.button
      ( [ cls [ "text-sm text-left px-2 py-1.5 rounded hover:bg-accent hover:text-accent-foreground" ]
        , HP.type_ HP.ButtonButton
        ]
        <> case props.onPresetSelect of
            Just handler -> [ HE.onClick \_ -> handler preset.label ]
            Nothing -> []
      )
      [ HH.text preset.label ]

-- | Render comparison section
renderComparisonSection :: forall w i. DateRangePickerProps i -> HH.HTML w i
renderComparisonSection props =
  HH.div
    [ cls [ "border-t mt-4 pt-4" ] ]
    [ HH.div
        [ cls [ "flex items-center gap-4" ] ]
        [ HH.label
            [ cls [ "text-sm font-medium" ] ]
            [ HH.text "Compare to:" ]
        , HH.select
            [ cls [ "text-sm border rounded px-2 py-1" ] ]
            [ HH.option [ HP.value "previous" ] [ HH.text "Previous period" ]
            , HH.option [ HP.value "year" ] [ HH.text "Previous year" ]
            , HH.option [ HP.value "custom" ] [ HH.text "Custom" ]
            ]
        , -- Display comparison dates
          case props.comparisonStart, props.comparisonEnd of
            Just start, Just end ->
              HH.span
                [ cls [ "text-sm text-muted-foreground" ] ]
                [ HH.text $ formatDateString ISO start <> " - " <> formatDateString ISO end ]
            _, _ -> HH.text ""
        ]
    ]

-- | Render footer with inputs
renderFooter :: forall w i. DateRangePickerProps i -> HH.HTML w i
renderFooter props =
  HH.div
    [ cls [ "border-t mt-4 pt-4 flex items-center justify-between" ] ]
    [ -- Date inputs
      HH.div
        [ cls [ "flex items-center gap-2" ] ]
        [ HH.input
            [ cls [ "w-28 text-sm border rounded px-2 py-1" ]
            , HP.type_ HP.InputText
            , HP.placeholder "Start date"
            , HP.value $ fromMaybe "" (map (formatDateString ISO) props.startDate)
            ]
        , HH.span
            [ cls [ "text-muted-foreground" ] ]
            [ HH.text "-" ]
        , HH.input
            [ cls [ "w-28 text-sm border rounded px-2 py-1" ]
            , HP.type_ HP.InputText
            , HP.placeholder "End date"
            , HP.value $ fromMaybe "" (map (formatDateString ISO) props.endDate)
            ]
        ]
    , -- Action buttons
      HH.div
        [ cls [ "flex gap-2" ] ]
        [ HH.button
            ( [ cls [ "text-sm px-3 py-1.5 border rounded hover:bg-accent" ]
              , HP.type_ HP.ButtonButton
              ]
              <> case props.onClose of
                  Just handler -> [ HE.onClick \_ -> handler unit ]
                  Nothing -> []
            )
            [ HH.text "Cancel" ]
        , HH.button
            ( [ cls [ "text-sm px-3 py-1.5 bg-primary text-primary-foreground rounded hover:bg-primary/90" ]
              , HP.type_ HP.ButtonButton
              ]
            )
            [ HH.text "Apply" ]
        ]
    ]

-- | Date range picker with label
dateRangePickerWithLabel :: forall w i. String -> Array (DateRangePickerProp i) -> HH.HTML w i
dateRangePickerWithLabel labelText propMods =
  HH.div
    [ cls [ "space-y-2" ] ]
    [ HH.label
        [ cls [ "text-sm font-medium leading-none" ] ]
        [ HH.text labelText ]
    , dateRangePicker propMods
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calendar icon SVG
calendarIcon :: forall w i. HH.HTML w i
calendarIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "rect") 
        [ HP.attr (HH.AttrName "width") "18"
        , HP.attr (HH.AttrName "height") "18"
        , HP.attr (HH.AttrName "x") "3"
        , HP.attr (HH.AttrName "y") "4"
        , HP.attr (HH.AttrName "rx") "2"
        ] []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "16"
        , HP.attr (HH.AttrName "x2") "16"
        , HP.attr (HH.AttrName "y1") "2"
        , HP.attr (HH.AttrName "y2") "6"
        ] []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "8"
        , HP.attr (HH.AttrName "x2") "8"
        , HP.attr (HH.AttrName "y1") "2"
        , HP.attr (HH.AttrName "y2") "6"
        ] []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "3"
        , HP.attr (HH.AttrName "x2") "21"
        , HP.attr (HH.AttrName "y1") "10"
        , HP.attr (HH.AttrName "y2") "10"
        ] []
    ]

-- | Month name lookup
monthName :: Int -> String
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

-- | Check if array is empty
null :: forall a. Array a -> Boolean
null arr = case arr of
  [] -> true
  _ -> false
