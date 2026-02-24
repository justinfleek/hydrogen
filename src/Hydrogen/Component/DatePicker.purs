-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // datepicker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DatePicker component with text input and calendar popup
-- |
-- | A date picker combining a text input for direct date entry with a calendar
-- | popup for visual selection. Supports date formatting, validation, and
-- | keyboard navigation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.DatePicker as DatePicker
-- |
-- | -- Basic date picker
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.onChange HandleDateChange
-- |   ]
-- |
-- | -- With format and placeholder
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.dateFormat "MM/dd/yyyy"
-- |   , DatePicker.placeholder "Select a date..."
-- |   , DatePicker.onChange HandleDateChange
-- |   ]
-- |
-- | -- With constraints
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.minDate { year: 2024, month: 1, day: 1 }
-- |   , DatePicker.maxDate { year: 2025, month: 12, day: 31 }
-- |   , DatePicker.onChange HandleDateChange
-- |   ]
-- |
-- | -- With today/clear buttons
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.showTodayButton true
-- |   , DatePicker.showClearButton true
-- |   , DatePicker.onChange HandleDateChange
-- |   ]
-- |
-- | -- Disabled/readonly
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.disabled true
-- |   ]
-- | ```
module Hydrogen.Component.DatePicker
  ( -- * DatePicker Component
    datePicker
  , datePickerWithLabel
    -- * Types
  , DateFormat(ISO, USShort, USLong, EUShort, EULong, Custom)
  , ValidationError(InvalidFormat, DateOutOfRange, DateDisabled, EmptyValue)
    -- * Props
  , DatePickerProps
  , DatePickerProp
  , defaultProps
    -- * Prop Builders
  , value
  , inputValue
  , dateFormat
  , placeholder
  , disabled
  , readOnly
  , required
  , showTodayButton
  , showClearButton
  , showCalendarIcon
  , minDate
  , maxDate
  , disabledDates
  , weekStartsOn
  , locale
  , className
  , id
  , name
  , isOpen
  , hasError
  , errorMessage
  , onChange
  , onInputChange
  , onOpen
  , onClose
  , onClear
  , onToday
    -- * Validation
  , validateDate
  , formatDateString
  ) where

import Prelude

import Data.Array (foldl)
import Data.Array as Array
import Data.Either (Either(Left, Right))
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Nothing, Just), fromMaybe, isJust)
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Component.Calendar (CalendarDate, WeekStart(Sunday), isDateInRange)
import Hydrogen.Component.Calendar as Calendar
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Date format patterns
data DateFormat
  = ISO           -- ^ YYYY-MM-DD
  | USShort       -- ^ MM/DD/YYYY
  | USLong        -- ^ MMMM D, YYYY
  | EUShort       -- ^ DD/MM/YYYY
  | EULong        -- ^ D MMMM YYYY
  | Custom String -- ^ Custom format string

derive instance eqDateFormat :: Eq DateFormat

-- | Date validation errors
data ValidationError
  = InvalidFormat
  | DateOutOfRange
  | DateDisabled
  | EmptyValue

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show InvalidFormat = "Invalid date format"
  show DateOutOfRange = "Date is out of allowed range"
  show DateDisabled = "This date is not available"
  show EmptyValue = "Please enter a date"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | DatePicker properties
type DatePickerProps i =
  { value :: Maybe CalendarDate
  , inputValue :: String
  , dateFormat :: DateFormat
  , placeholder :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , showTodayButton :: Boolean
  , showClearButton :: Boolean
  , showCalendarIcon :: Boolean
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  , weekStartsOn :: WeekStart
  , locale :: String
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , isOpen :: Boolean
  , hasError :: Boolean
  , errorMessage :: Maybe String
  , onChange :: Maybe (Maybe CalendarDate -> i)
  , onInputChange :: Maybe (String -> i)
  , onOpen :: Maybe (Unit -> i)
  , onClose :: Maybe (Unit -> i)
  , onClear :: Maybe (Unit -> i)
  , onToday :: Maybe (Unit -> i)
  }

-- | Property modifier
type DatePickerProp i = DatePickerProps i -> DatePickerProps i

-- | Default date picker properties
defaultProps :: forall i. DatePickerProps i
defaultProps =
  { value: Nothing
  , inputValue: ""
  , dateFormat: ISO
  , placeholder: "Select date..."
  , disabled: false
  , readOnly: false
  , required: false
  , showTodayButton: false
  , showClearButton: false
  , showCalendarIcon: true
  , minDate: Nothing
  , maxDate: Nothing
  , disabledDates: const false
  , weekStartsOn: Sunday
  , locale: "en-US"
  , className: ""
  , id: Nothing
  , name: Nothing
  , isOpen: false
  , hasError: false
  , errorMessage: Nothing
  , onChange: Nothing
  , onInputChange: Nothing
  , onOpen: Nothing
  , onClose: Nothing
  , onClear: Nothing
  , onToday: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set the selected date value
value :: forall i. Maybe CalendarDate -> DatePickerProp i
value v props = props { value = v }

-- | Set the raw input value
inputValue :: forall i. String -> DatePickerProp i
inputValue v props = props { inputValue = v }

-- | Set date format
dateFormat :: forall i. DateFormat -> DatePickerProp i
dateFormat f props = props { dateFormat = f }

-- | Set placeholder text
placeholder :: forall i. String -> DatePickerProp i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall i. Boolean -> DatePickerProp i
disabled d props = props { disabled = d }

-- | Set read-only state
readOnly :: forall i. Boolean -> DatePickerProp i
readOnly r props = props { readOnly = r }

-- | Set required state
required :: forall i. Boolean -> DatePickerProp i
required r props = props { required = r }

-- | Show "Today" button
showTodayButton :: forall i. Boolean -> DatePickerProp i
showTodayButton show props = props { showTodayButton = show }

-- | Show clear button
showClearButton :: forall i. Boolean -> DatePickerProp i
showClearButton show props = props { showClearButton = show }

-- | Show calendar icon
showCalendarIcon :: forall i. Boolean -> DatePickerProp i
showCalendarIcon show props = props { showCalendarIcon = show }

-- | Set minimum date
minDate :: forall i. CalendarDate -> DatePickerProp i
minDate d props = props { minDate = Just d }

-- | Set maximum date
maxDate :: forall i. CalendarDate -> DatePickerProp i
maxDate d props = props { maxDate = Just d }

-- | Set disabled dates predicate
disabledDates :: forall i. (CalendarDate -> Boolean) -> DatePickerProp i
disabledDates pred props = props { disabledDates = pred }

-- | Set week start day
weekStartsOn :: forall i. WeekStart -> DatePickerProp i
weekStartsOn ws props = props { weekStartsOn = ws }

-- | Set locale
locale :: forall i. String -> DatePickerProp i
locale l props = props { locale = l }

-- | Add custom class
className :: forall i. String -> DatePickerProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> DatePickerProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> DatePickerProp i
name n props = props { name = Just n }

-- | Set open state
isOpen :: forall i. Boolean -> DatePickerProp i
isOpen o props = props { isOpen = o }

-- | Set error state
hasError :: forall i. Boolean -> DatePickerProp i
hasError e props = props { hasError = e }

-- | Set error message
errorMessage :: forall i. String -> DatePickerProp i
errorMessage msg props = props { errorMessage = Just msg }

-- | Set change handler (fires when valid date selected)
onChange :: forall i. (Maybe CalendarDate -> i) -> DatePickerProp i
onChange handler props = props { onChange = Just handler }

-- | Set input change handler (fires on every keystroke)
onInputChange :: forall i. (String -> i) -> DatePickerProp i
onInputChange handler props = props { onInputChange = Just handler }

-- | Set open handler
onOpen :: forall i. (Unit -> i) -> DatePickerProp i
onOpen handler props = props { onOpen = Just handler }

-- | Set close handler
onClose :: forall i. (Unit -> i) -> DatePickerProp i
onClose handler props = props { onClose = Just handler }

-- | Set clear handler
onClear :: forall i. (Unit -> i) -> DatePickerProp i
onClear handler props = props { onClear = Just handler }

-- | Set today handler
onToday :: forall i. (Unit -> i) -> DatePickerProp i
onToday handler props = props { onToday = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // validation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Validate a date string
validateDate 
  :: DatePickerProps Unit 
  -> String 
  -> Either ValidationError CalendarDate
validateDate props str
  | String.null str && props.required = Left EmptyValue
  | String.null str = Left EmptyValue
  | otherwise = case parseDateFromFormat props.dateFormat str of
      Nothing -> Left InvalidFormat
      Just date ->
        if not (isDateInRange date props.minDate props.maxDate) then
          Left DateOutOfRange
        else if props.disabledDates date then
          Left DateDisabled
        else
          Right date

-- | Format a date to string based on format
formatDateString :: DateFormat -> CalendarDate -> String
formatDateString format date = case format of
  ISO -> 
    padZero 4 date.year <> "-" <> padZero 2 date.month <> "-" <> padZero 2 date.day
  USShort ->
    padZero 2 date.month <> "/" <> padZero 2 date.day <> "/" <> show date.year
  USLong ->
    monthNameLong date.month <> " " <> show date.day <> ", " <> show date.year
  EUShort ->
    padZero 2 date.day <> "/" <> padZero 2 date.month <> "/" <> show date.year
  EULong ->
    show date.day <> " " <> monthNameLong date.month <> " " <> show date.year
  Custom _ ->
    -- Custom format would need more sophisticated parsing
    padZero 4 date.year <> "-" <> padZero 2 date.month <> "-" <> padZero 2 date.day

-- | Parse date from format
parseDateFromFormat :: DateFormat -> String -> Maybe CalendarDate
parseDateFromFormat format str = case format of
  ISO -> parseISO str
  USShort -> parseUSShort str
  EUShort -> parseEUShort str
  _ -> parseISO str  -- Fallback to ISO

-- | Parse ISO format (YYYY-MM-DD)
parseISO :: String -> Maybe CalendarDate
parseISO str = case String.split (String.Pattern "-") str of
  [y, m, d] -> do
    year <- parseInt y
    month <- parseInt m
    day <- parseInt d
    if isValidDate year month day then Just { year, month, day } else Nothing
  _ -> Nothing

-- | Parse US short format (MM/DD/YYYY)
parseUSShort :: String -> Maybe CalendarDate
parseUSShort str = case String.split (String.Pattern "/") str of
  [m, d, y] -> do
    year <- parseInt y
    month <- parseInt m
    day <- parseInt d
    if isValidDate year month day then Just { year, month, day } else Nothing
  _ -> Nothing

-- | Parse EU short format (DD/MM/YYYY)
parseEUShort :: String -> Maybe CalendarDate
parseEUShort str = case String.split (String.Pattern "/") str of
  [d, m, y] -> do
    year <- parseInt y
    month <- parseInt m
    day <- parseInt d
    if isValidDate year month day then Just { year, month, day } else Nothing
  _ -> Nothing

-- | Check if date components are valid
isValidDate :: Int -> Int -> Int -> Boolean
isValidDate year month day =
  year >= 1 && year <= 9999 &&
  month >= 1 && month <= 12 &&
  day >= 1 && day <= Calendar.getDaysInMonth year month

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base input classes
inputClasses :: String
inputClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background file:border-0 file:bg-transparent file:text-sm file:font-medium placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Error input classes
errorInputClasses :: String
errorInputClasses = "border-destructive focus-visible:ring-destructive"

-- | Render a date picker
datePicker :: forall w i. Array (DatePickerProp i) -> HH.HTML w i
datePicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputClass = inputClasses <> 
      (if props.hasError then " " <> errorInputClasses else "") <>
      (if props.showCalendarIcon then " pl-10" else "") <>
      (if props.showClearButton && isJust props.value then " pr-10" else "")
  in
    HH.div
      [ cls [ "relative inline-block", props.className ] ]
      [ -- Input wrapper
        HH.div
          [ cls [ "relative" ] ]
          [ -- Calendar icon (left)
            if props.showCalendarIcon then
              HH.div
                [ cls [ "absolute left-3 top-1/2 -translate-y-1/2 text-muted-foreground pointer-events-none" ] ]
                [ calendarIcon ]
            else
              HH.text ""
          
          , -- Input field
            HH.input
              ( [ cls [ inputClass ]
                , HP.type_ HP.InputText
                , HP.value (fromMaybe props.inputValue (map (formatDateString props.dateFormat) props.value))
                , HP.placeholder props.placeholder
                , HP.disabled props.disabled
                , HP.readOnly props.readOnly
                , HP.required props.required
                , ARIA.label "Date input"
                , ARIA.hasPopup "dialog"
                , ARIA.expanded (show props.isOpen)
                ]
                <> maybeAttr HP.id props.id
                <> maybeAttr HP.name props.name
                <> case props.onInputChange of
                    Just handler -> [ HE.onValueInput handler ]
                    Nothing -> []
              )
          
          , -- Clear button (right)
            if props.showClearButton && isJust props.value && not props.disabled then
              HH.button
                ( [ cls [ "absolute right-3 top-1/2 -translate-y-1/2 text-muted-foreground hover:text-foreground" ]
                  , HP.type_ HP.ButtonButton
                  , ARIA.label "Clear date"
                  ]
                  <> case props.onClear of
                      Just handler -> [ HE.onClick \_ -> handler unit ]
                      Nothing -> []
                )
                [ closeIcon ]
            else
              HH.text ""
          ]
      
      , -- Error message
        case props.errorMessage of
          Just msg ->
            HH.p
              [ cls [ "text-sm text-destructive mt-1" ] ]
              [ HH.text msg ]
          Nothing -> HH.text ""
      
      , -- Calendar popup
        if props.isOpen then
          HH.div
            [ cls [ "absolute z-50 mt-1 bg-background border rounded-md shadow-lg" ]
            , ARIA.role "dialog"
            , ARIA.modal "true"
            ]
            [ Calendar.calendarWithNav
                [ Calendar.selected props.value
                , Calendar.weekStartsOn props.weekStartsOn
                , case props.minDate of
                    Just d -> Calendar.minDate d
                    Nothing -> identity
                , case props.maxDate of
                    Just d -> Calendar.maxDate d
                    Nothing -> identity
                , Calendar.disabledDates props.disabledDates
                ]
            , -- Footer with Today/Clear buttons
              if props.showTodayButton || props.showClearButton then
                HH.div
                  [ cls [ "border-t px-3 py-2 flex justify-between" ] ]
                  [ if props.showTodayButton then
                      HH.button
                        ( [ cls [ "text-sm text-primary hover:underline" ]
                          , HP.type_ HP.ButtonButton
                          ]
                          <> case props.onToday of
                              Just handler -> [ HE.onClick \_ -> handler unit ]
                              Nothing -> []
                        )
                        [ HH.text "Today" ]
                    else HH.text ""
                  , if props.showClearButton then
                      HH.button
                        ( [ cls [ "text-sm text-muted-foreground hover:text-foreground" ]
                          , HP.type_ HP.ButtonButton
                          ]
                          <> case props.onClear of
                              Just handler -> [ HE.onClick \_ -> handler unit ]
                              Nothing -> []
                        )
                        [ HH.text "Clear" ]
                    else HH.text ""
                  ]
              else HH.text ""
            ]
        else
          HH.text ""
      ]

-- | Date picker with label
datePickerWithLabel :: forall w i. String -> Array (DatePickerProp i) -> HH.HTML w i
datePickerWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputId = fromMaybe ("datepicker-" <> labelText) props.id
    propsWithId = propMods <> [ id inputId ]
  in
    HH.div
      [ cls [ "space-y-2" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
          , HP.for inputId
          ]
          [ HH.text labelText
          , if props.required then
              HH.span [ cls [ "text-destructive ml-1" ] ] [ HH.text "*" ]
            else HH.text ""
          ]
      , datePicker propsWithId
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
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "rect") 
        [ HP.attr (HH.AttrName "width") "18"
        , HP.attr (HH.AttrName "height") "18"
        , HP.attr (HH.AttrName "x") "3"
        , HP.attr (HH.AttrName "y") "4"
        , HP.attr (HH.AttrName "rx") "2"
        , HP.attr (HH.AttrName "ry") "2"
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

-- | Close/X icon SVG
closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ] []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ] []
    ]

-- | Optional attribute helper
maybeAttr :: forall r i a. (a -> HH.IProp r i) -> Maybe a -> Array (HH.IProp r i)
maybeAttr _ Nothing = []
maybeAttr f (Just a) = [ f a ]

-- | Pad number with leading zeros
padZero :: Int -> Int -> String
padZero width n =
  let str = show n
      len = String.length str
  in if len >= width
     then str
     else String.joinWith "" (Array.replicate (width - len) "0") <> str

-- | Simple month name lookup
monthNameLong :: Int -> String
monthNameLong m = case m of
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

-- | Parse an integer from string
-- | Pure implementation using Data.Int.fromString
-- | Handles trimming whitespace before parsing
parseInt :: String -> Maybe Int
parseInt str = 
  let trimmed = String.trim str
  in if String.null trimmed
     then Nothing
     else Int.fromString trimmed
