-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // timepicker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimePicker component for time selection
-- |
-- | A time picker with hour/minute/second inputs, supporting both 12-hour and
-- | 24-hour formats with keyboard input and increment buttons.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.TimePicker as TimePicker
-- |
-- | -- Basic time picker (24h format)
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- |
-- | -- 12-hour format with AM/PM
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.hourFormat TimePicker.Hour12
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- |
-- | -- With seconds
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.showSeconds true
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- |
-- | -- With constraints
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.minTime { hour: 9, minute: 0, second: 0 }
-- |   , TimePicker.maxTime { hour: 17, minute: 30, second: 0 }
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- |
-- | -- With step intervals
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.minuteStep 15  -- 15-minute intervals
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- | ```
module Hydrogen.Component.TimePicker
  ( -- * TimePicker Component
    timePicker
  , timePickerWithLabel
  , timePickerInline
    -- * Types
  , Time
  , HourFormat(..)
  , Period(..)
    -- * Props
  , TimePickerProps
  , TimePickerProp
  , defaultProps
    -- * Prop Builders
  , value
  , hourFormat
  , showSeconds
  , minuteStep
  , secondStep
  , minTime
  , maxTime
  , disabled
  , readOnly
  , className
  , id
  , name
  , placeholder
  , showIncrementButtons
  , onChange
  , onHourChange
  , onMinuteChange
  , onSecondChange
  , onPeriodChange
    -- * Time Operations
  , timeToString
  , timeFromString
  , timeToMinutes
  , minutesToTime
  , compareTime
  , isTimeInRange
  , normalizeTime
  , togglePeriod
  , to12Hour
  , to24Hour
    -- * Constants
  , midnight
  , noon
  , endOfDay
  ) where

import Prelude

import Data.Array (foldl, range)
import Data.Int (rem)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Time represented as hours (0-23), minutes (0-59), seconds (0-59)
type Time =
  { hour :: Int
  , minute :: Int
  , second :: Int
  }

-- | Hour format (12-hour or 24-hour)
data HourFormat
  = Hour12  -- ^ 12-hour format with AM/PM
  | Hour24  -- ^ 24-hour format

derive instance eqHourFormat :: Eq HourFormat

-- | AM/PM period
data Period
  = AM
  | PM

derive instance eqPeriod :: Eq Period

instance showPeriod :: Show Period where
  show AM = "AM"
  show PM = "PM"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Midnight (00:00:00)
midnight :: Time
midnight = { hour: 0, minute: 0, second: 0 }

-- | Noon (12:00:00)
noon :: Time
noon = { hour: 12, minute: 0, second: 0 }

-- | End of day (23:59:59)
endOfDay :: Time
endOfDay = { hour: 23, minute: 59, second: 59 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TimePicker properties
type TimePickerProps i =
  { value :: Maybe Time
  , hourFormat :: HourFormat
  , showSeconds :: Boolean
  , minuteStep :: Int
  , secondStep :: Int
  , minTime :: Maybe Time
  , maxTime :: Maybe Time
  , disabled :: Boolean
  , readOnly :: Boolean
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , placeholder :: String
  , showIncrementButtons :: Boolean
  , onChange :: Maybe (Time -> i)
  , onHourChange :: Maybe (Int -> i)
  , onMinuteChange :: Maybe (Int -> i)
  , onSecondChange :: Maybe (Int -> i)
  , onPeriodChange :: Maybe (Period -> i)
  }

-- | Property modifier
type TimePickerProp i = TimePickerProps i -> TimePickerProps i

-- | Default time picker properties
defaultProps :: forall i. TimePickerProps i
defaultProps =
  { value: Nothing
  , hourFormat: Hour24
  , showSeconds: false
  , minuteStep: 1
  , secondStep: 1
  , minTime: Nothing
  , maxTime: Nothing
  , disabled: false
  , readOnly: false
  , className: ""
  , id: Nothing
  , name: Nothing
  , placeholder: "--:--"
  , showIncrementButtons: true
  , onChange: Nothing
  , onHourChange: Nothing
  , onMinuteChange: Nothing
  , onSecondChange: Nothing
  , onPeriodChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set time value
value :: forall i. Maybe Time -> TimePickerProp i
value v props = props { value = v }

-- | Set hour format (12h or 24h)
hourFormat :: forall i. HourFormat -> TimePickerProp i
hourFormat f props = props { hourFormat = f }

-- | Show seconds field
showSeconds :: forall i. Boolean -> TimePickerProp i
showSeconds s props = props { showSeconds = s }

-- | Set minute step interval
minuteStep :: forall i. Int -> TimePickerProp i
minuteStep s props = props { minuteStep = max 1 s }

-- | Set second step interval
secondStep :: forall i. Int -> TimePickerProp i
secondStep s props = props { secondStep = max 1 s }

-- | Set minimum time
minTime :: forall i. Time -> TimePickerProp i
minTime t props = props { minTime = Just t }

-- | Set maximum time
maxTime :: forall i. Time -> TimePickerProp i
maxTime t props = props { maxTime = Just t }

-- | Set disabled state
disabled :: forall i. Boolean -> TimePickerProp i
disabled d props = props { disabled = d }

-- | Set read-only state
readOnly :: forall i. Boolean -> TimePickerProp i
readOnly r props = props { readOnly = r }

-- | Add custom class
className :: forall i. String -> TimePickerProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> TimePickerProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> TimePickerProp i
name n props = props { name = Just n }

-- | Set placeholder
placeholder :: forall i. String -> TimePickerProp i
placeholder p props = props { placeholder = p }

-- | Show increment/decrement buttons
showIncrementButtons :: forall i. Boolean -> TimePickerProp i
showIncrementButtons s props = props { showIncrementButtons = s }

-- | Set change handler (fires when time changes)
onChange :: forall i. (Time -> i) -> TimePickerProp i
onChange handler props = props { onChange = Just handler }

-- | Set hour change handler
onHourChange :: forall i. (Int -> i) -> TimePickerProp i
onHourChange handler props = props { onHourChange = Just handler }

-- | Set minute change handler
onMinuteChange :: forall i. (Int -> i) -> TimePickerProp i
onMinuteChange handler props = props { onMinuteChange = Just handler }

-- | Set second change handler
onSecondChange :: forall i. (Int -> i) -> TimePickerProp i
onSecondChange handler props = props { onSecondChange = Just handler }

-- | Set period change handler
onPeriodChange :: forall i. (Period -> i) -> TimePickerProp i
onPeriodChange handler props = props { onPeriodChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // time operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert time to string (HH:MM or HH:MM:SS)
timeToString :: HourFormat -> Boolean -> Time -> String
timeToString format includeSeconds time =
  let
    { displayHour, period } = to12Hour time
    hourStr = case format of
      Hour12 -> padZero 2 displayHour
      Hour24 -> padZero 2 time.hour
    minuteStr = padZero 2 time.minute
    secondStr = padZero 2 time.second
    baseStr = hourStr <> ":" <> minuteStr
    withSeconds = if includeSeconds then baseStr <> ":" <> secondStr else baseStr
  in
    case format of
      Hour12 -> withSeconds <> " " <> show period
      Hour24 -> withSeconds

-- | Parse time from string
timeFromString :: String -> Maybe Time
timeFromString str =
  let
    -- Remove AM/PM suffix
    cleaned = String.toUpper $ String.trim str
    hasPM = String.contains (String.Pattern "PM") cleaned
    hasAM = String.contains (String.Pattern "AM") cleaned
    timeStr = String.replaceAll (String.Pattern " AM") (String.Replacement "")
              $ String.replaceAll (String.Pattern " PM") (String.Replacement "")
              $ String.replaceAll (String.Pattern "AM") (String.Replacement "")
              $ String.replaceAll (String.Pattern "PM") (String.Replacement "") cleaned
    parts = String.split (String.Pattern ":") timeStr
  in
    case parts of
      [h, m, s] -> do
        hour <- parseInt h
        minute <- parseInt m
        second <- parseInt s
        let adjustedHour = adjustFor12Hour hour hasPM hasAM
        if isValidTime adjustedHour minute second
          then Just { hour: adjustedHour, minute, second }
          else Nothing
      [h, m] -> do
        hour <- parseInt h
        minute <- parseInt m
        let adjustedHour = adjustFor12Hour hour hasPM hasAM
        if isValidTime adjustedHour minute 0
          then Just { hour: adjustedHour, minute, second: 0 }
          else Nothing
      _ -> Nothing

-- | Adjust hour for 12-hour format parsing
adjustFor12Hour :: Int -> Boolean -> Boolean -> Int
adjustFor12Hour hour hasPM hasAM
  | hasPM && hour < 12 = hour + 12
  | hasAM && hour == 12 = 0
  | otherwise = hour

-- | Check if time components are valid
isValidTime :: Int -> Int -> Int -> Boolean
isValidTime hour minute second =
  hour >= 0 && hour <= 23 &&
  minute >= 0 && minute <= 59 &&
  second >= 0 && second <= 59

-- | Convert time to total minutes (for comparison)
timeToMinutes :: Time -> Int
timeToMinutes t = t.hour * 60 + t.minute

-- | Convert total minutes to time
minutesToTime :: Int -> Time
minutesToTime totalMinutes =
  { hour: totalMinutes / 60 `rem` 24
  , minute: totalMinutes `rem` 60
  , second: 0
  }

-- | Compare two times: -1 (a < b), 0 (equal), 1 (a > b)
compareTime :: Time -> Time -> Int
compareTime a b =
  let
    aSeconds = a.hour * 3600 + a.minute * 60 + a.second
    bSeconds = b.hour * 3600 + b.minute * 60 + b.second
  in
    if aSeconds < bSeconds then -1
    else if aSeconds > bSeconds then 1
    else 0

-- | Check if time is within range
isTimeInRange :: Time -> Maybe Time -> Maybe Time -> Boolean
isTimeInRange time minT maxT =
  let
    afterMin = case minT of
      Nothing -> true
      Just min -> compareTime time min >= 0
    beforeMax = case maxT of
      Nothing -> true
      Just max -> compareTime time max <= 0
  in afterMin && beforeMax

-- | Normalize time to valid range
normalizeTime :: Time -> Time
normalizeTime t =
  { hour: clamp 0 23 t.hour
  , minute: clamp 0 59 t.minute
  , second: clamp 0 59 t.second
  }

-- | Toggle AM/PM period
togglePeriod :: Period -> Period
togglePeriod AM = PM
togglePeriod PM = AM

-- | Convert 24-hour time to 12-hour display
to12Hour :: Time -> { displayHour :: Int, period :: Period }
to12Hour time
  | time.hour == 0 = { displayHour: 12, period: AM }
  | time.hour < 12 = { displayHour: time.hour, period: AM }
  | time.hour == 12 = { displayHour: 12, period: PM }
  | otherwise = { displayHour: time.hour - 12, period: PM }

-- | Convert 12-hour time to 24-hour
to24Hour :: Int -> Period -> Int
to24Hour hour period
  | period == AM && hour == 12 = 0
  | period == AM = hour
  | period == PM && hour == 12 = 12
  | otherwise = hour + 12

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base segment input classes
segmentInputClasses :: String
segmentInputClasses =
  "w-10 h-9 text-center text-sm bg-transparent border-0 focus:outline-none focus:ring-0 appearance-none"

-- | Segment container classes
segmentContainerClasses :: String
segmentContainerClasses =
  "flex flex-col items-center"

-- | Increment button classes
incrementButtonClasses :: String
incrementButtonClasses =
  "w-6 h-6 flex items-center justify-center text-muted-foreground hover:text-foreground hover:bg-accent rounded transition-colors"

-- | Render a time picker
timePicker :: forall w i. Array (TimePickerProp i) -> HH.HTML w i
timePicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    time = fromMaybe midnight props.value
    { displayHour, period } = to12Hour time
    effectiveHour = case props.hourFormat of
      Hour12 -> displayHour
      Hour24 -> time.hour
    maxHour = case props.hourFormat of
      Hour12 -> 12
      Hour24 -> 23
    minHour = case props.hourFormat of
      Hour12 -> 1
      Hour24 -> 0
  in
    HH.div
      [ cls [ "inline-flex items-center gap-1 border rounded-md px-2 py-1 bg-background", props.className ]
      , ARIA.role "group"
      , ARIA.label "Time picker"
      ]
      [ -- Hour segment
        renderTimeSegment props
          { value: effectiveHour
          , min: minHour
          , max: maxHour
          , step: 1
          , label: "Hour"
          , disabled: props.disabled
          , readOnly: props.readOnly
          , showButtons: props.showIncrementButtons
          }
      
      , -- Separator
        HH.span
          [ cls [ "text-muted-foreground font-medium" ] ]
          [ HH.text ":" ]
      
      , -- Minute segment
        renderTimeSegment props
          { value: time.minute
          , min: 0
          , max: 59
          , step: props.minuteStep
          , label: "Minute"
          , disabled: props.disabled
          , readOnly: props.readOnly
          , showButtons: props.showIncrementButtons
          }
      
      , -- Seconds segment (optional)
        if props.showSeconds then
          HH.span_ 
            [ HH.span
                [ cls [ "text-muted-foreground font-medium" ] ]
                [ HH.text ":" ]
            , renderTimeSegment props
                { value: time.second
                , min: 0
                , max: 59
                , step: props.secondStep
                , label: "Second"
                , disabled: props.disabled
                , readOnly: props.readOnly
                , showButtons: props.showIncrementButtons
                }
            ]
        else HH.text ""
      
      , -- AM/PM toggle (for 12-hour format)
        if props.hourFormat == Hour12 then
          renderPeriodToggle props period
        else HH.text ""
      ]

-- | Render inline time picker (larger, for embedded use)
timePickerInline :: forall w i. Array (TimePickerProp i) -> HH.HTML w i
timePickerInline propMods =
  let
    props = foldl (\p f -> f p) (defaultProps { showIncrementButtons = true }) propMods
  in
    HH.div
      [ cls [ "inline-flex flex-col items-center gap-2 p-4 border rounded-lg bg-background", props.className ] ]
      [ timePicker propMods ]

-- | Time picker with label
timePickerWithLabel :: forall w i. String -> Array (TimePickerProp i) -> HH.HTML w i
timePickerWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputId = fromMaybe ("timepicker-" <> labelText) props.id
    propsWithId = propMods <> [ id inputId ]
  in
    HH.div
      [ cls [ "space-y-2" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium leading-none" ]
          , HP.for inputId
          ]
          [ HH.text labelText ]
      , timePicker propsWithId
      ]

-- | Render a time segment (hour, minute, or second)
renderTimeSegment :: forall w i. TimePickerProps i -> 
  { value :: Int
  , min :: Int
  , max :: Int
  , step :: Int
  , label :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , showButtons :: Boolean
  } -> HH.HTML w i
renderTimeSegment props segment =
  HH.div
    [ cls [ segmentContainerClasses ] ]
    [ -- Increment button
      if segment.showButtons && not segment.disabled then
        HH.button
          [ cls [ incrementButtonClasses ]
          , HP.type_ HP.ButtonButton
          , HP.tabIndex (-1)
          , ARIA.label $ "Increase " <> segment.label
          , HP.disabled segment.disabled
          ]
          [ chevronUpIcon ]
      else HH.text ""
    
    , -- Input field
      HH.input
        [ cls [ segmentInputClasses ]
        , HP.type_ HP.InputText
        , HP.value (padZero 2 segment.value)
        , HP.disabled segment.disabled
        , HP.readOnly segment.readOnly
        , ARIA.label segment.label
        , HP.attr (HH.AttrName "inputmode") "numeric"
        , HP.attr (HH.AttrName "pattern") "[0-9]*"
        ]
    
    , -- Decrement button
      if segment.showButtons && not segment.disabled then
        HH.button
          [ cls [ incrementButtonClasses ]
          , HP.type_ HP.ButtonButton
          , HP.tabIndex (-1)
          , ARIA.label $ "Decrease " <> segment.label
          , HP.disabled segment.disabled
          ]
          [ chevronDownIcon ]
      else HH.text ""
    ]

-- | Render AM/PM toggle
renderPeriodToggle :: forall w i. TimePickerProps i -> Period -> HH.HTML w i
renderPeriodToggle props period =
  HH.div
    [ cls [ "ml-2 flex flex-col text-xs" ] ]
    [ HH.button
        ( [ cls 
              [ "px-2 py-0.5 rounded-t border-b-0"
              , if period == AM then "bg-primary text-primary-foreground" else "bg-muted hover:bg-accent"
              ]
          , HP.type_ HP.ButtonButton
          , HP.disabled props.disabled
          , ARIA.pressed (show $ period == AM)
          ]
          <> case props.onPeriodChange of
              Just handler -> [ HE.onClick \_ -> handler AM ]
              Nothing -> []
        )
        [ HH.text "AM" ]
    , HH.button
        ( [ cls 
              [ "px-2 py-0.5 rounded-b"
              , if period == PM then "bg-primary text-primary-foreground" else "bg-muted hover:bg-accent"
              ]
          , HP.type_ HP.ButtonButton
          , HP.disabled props.disabled
          , ARIA.pressed (show $ period == PM)
          ]
          <> case props.onPeriodChange of
              Just handler -> [ HE.onClick \_ -> handler PM ]
              Nothing -> []
        )
        [ HH.text "PM" ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chevron up icon
chevronUpIcon :: forall w i. HH.HTML w i
chevronUpIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "18 15 12 9 6 15" ] []
    ]

-- | Chevron down icon
chevronDownIcon :: forall w i. HH.HTML w i
chevronDownIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 9 12 15 18 9" ] []
    ]

-- | Pad number with leading zeros
padZero :: Int -> Int -> String
padZero width n =
  let str = show n
      len = String.length str
  in if len >= width
     then str
     else String.joinWith "" (replicate (width - len) "0") <> str

-- | Replicate a value n times
replicate :: forall a. Int -> a -> Array a
replicate n x = if n <= 0 then [] else map (const x) (range 1 n)

-- | Clamp a value between min and max
clamp :: Int -> Int -> Int -> Int
clamp minV maxV v = max minV (min maxV v)

-- | Parse integer
parseInt :: String -> Maybe Int
parseInt = parseIntImpl Just Nothing

foreign import parseIntImpl :: (Int -> Maybe Int) -> Maybe Int -> String -> Maybe Int
