-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // scraper // transition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transition detection for behavioral visual capture.
-- |
-- | Detects and captures CSS transitions by:
-- | 1. Reading transition-* computed properties
-- | 2. Observing actual state changes over time
-- | 3. Computing state diffs with timing information
-- |
-- | ## Output
-- |
-- | Transitions are captured as:
-- | - Before state (CapturedState)
-- | - After state (CapturedState)
-- | - Duration (Millisecond)
-- | - Easing (CubicBezierEasing or named)
-- | - Delay (Millisecond)
-- | - Properties that changed
-- |
-- | ## Integration with Hydrogen.Schema.Temporal
-- |
-- | All timing values map to:
-- | - Hydrogen.Schema.Temporal.Millisecond
-- | - Hydrogen.Schema.Temporal.CubicBezierEasing
-- | - Hydrogen.Schema.Temporal.Easing

module Hydrogen.Scraper.Transition
  ( -- * Detection
    detectTransitions
  , detectElementTransitions
  
  -- * Observation
  , observeTransition
  , measureTransitionTiming
  
  -- * Types
  , TransitionConfig
  , ObservedTransition
  , PropertyTransition
  , InterpolationType(..)
  , TimingConfig
  , EasingConfig
  , CubicBezierPoints
  , StepsConfig
  
  -- * Diff Computation
  , computeStateDiff
  , changedProperties
  
  -- * Easing
  , parseEasingString
  , easingToCubicBezier
  ) where

import Prelude

import Data.Array (snoc) as Array
import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (fromString)
import Data.String (Pattern(Pattern), drop, dropWhile, indexOf, length, null, split, takeWhile, trim)
import Data.String.CodePoints (codePointFromChar) as CP
import Data.String.CodeUnits (charAt, singleton)
import Data.String.CodePoints (CodePoint)
import Data.Tuple (Tuple(Tuple))
import Effect.Aff (Aff, delay)
import Effect.Class (liftEffect)
import Hydrogen.Playwright as PW
import Hydrogen.Playwright (Page, Locator)
import Hydrogen.Scraper.Capture (CapturedState, CapturedColor, captureElementState)
import Hydrogen.Scraper.Types.State (InteractionState(Hover, Focus, Active))
import Data.Time.Duration (Milliseconds(Milliseconds))
import Data.Int (toNumber) as Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // transition types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS transition configuration for an element
type TransitionConfig =
  { property :: String                -- "all" or specific property
  , durationMs :: Number
  , timingFunction :: String          -- ease, linear, cubic-bezier(...)
  , delayMs :: Number
  }

-- | Observed transition between states
type ObservedTransition =
  { selector :: String
  , fromState :: InteractionState
  , toState :: InteractionState
  , beforeCapture :: CapturedState
  , afterCapture :: CapturedState
  , config :: TransitionConfig
  , changedProps :: Array PropertyTransition
  , actualDurationMs :: Number        -- Measured, not declared
  }

-- | Single property that transitioned
type PropertyTransition =
  { property :: String
  , fromValue :: String
  , toValue :: String
  , interpolationType :: InterpolationType
  }

-- | How a property interpolates
data InterpolationType
  = InterpolateColor      -- Color interpolation (OKLCH space)
  | InterpolateNumber     -- Numeric interpolation
  | InterpolateLength     -- Length with unit
  | InterpolateTransform  -- Transform matrix
  | InterpolateDiscrete   -- No interpolation (instant switch)

derive instance eqInterpolationType :: Eq InterpolationType

-- | Timing configuration in Hydrogen types
type TimingConfig =
  { durationMs :: Number
  , delayMs :: Number
  , easing :: EasingConfig
  }

-- | Easing configuration
type EasingConfig =
  { name :: String                    -- "ease", "linear", etc.
  , cubicBezier :: Maybe CubicBezierPoints
  , steps :: Maybe StepsConfig
  }

-- | Cubic bezier control points
type CubicBezierPoints =
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  }

-- | Steps easing config
type StepsConfig =
  { count :: Int
  , position :: String                -- "start" or "end"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // detection javascript
-- ═══════════════════════════════════════════════════════════════════════════════

-- | JavaScript to detect transition config for an element
detectTransitionJS :: String -> String
detectTransitionJS selector = """
(() => {
  const el = document.querySelector('""" <> selector <> """');
  if (!el) return JSON.stringify({ error: 'not found' });
  
  const style = getComputedStyle(el);
  
  // Parse transition properties
  const properties = style.transitionProperty.split(',').map(s => s.trim());
  const durations = style.transitionDuration.split(',').map(parseTime);
  const timings = style.transitionTimingFunction.split(/,(?![^(]*\))/).map(s => s.trim());
  const delays = style.transitionDelay.split(',').map(parseTime);
  
  const transitions = [];
  for (let i = 0; i < properties.length; i++) {
    const prop = properties[i];
    if (prop === 'none' || prop === '') continue;
    
    transitions.push({
      property: prop,
      durationMs: durations[i % durations.length] || 0,
      timingFunction: timings[i % timings.length] || 'ease',
      delayMs: delays[i % delays.length] || 0
    });
  }
  
  return JSON.stringify({
    hasTransition: transitions.length > 0 && transitions.some(t => t.durationMs > 0),
    transitions: transitions
  });
  
  function parseTime(str) {
    if (!str) return 0;
    const match = str.trim().match(/([\d.]+)(ms|s)?/);
    if (!match) return 0;
    const value = parseFloat(match[1]);
    if (match[2] === 'ms') return value;
    if (match[2] === 's') return value * 1000;
    return value;  // Assume ms if no unit
  }
})()
"""

-- | JavaScript to measure actual transition duration by observing transitionend
measureTransitionJS :: String -> String
measureTransitionJS selector = """
(() => {
  return new Promise((resolve) => {
    const el = document.querySelector('""" <> selector <> """');
    if (!el) {
      resolve(JSON.stringify({ error: 'not found' }));
      return;
    }
    
    const startTime = performance.now();
    let endTime = startTime;
    let properties = [];
    
    const handler = (e) => {
      endTime = performance.now();
      properties.push(e.propertyName);
    };
    
    el.addEventListener('transitionend', handler);
    
    // Wait max 5 seconds
    setTimeout(() => {
      el.removeEventListener('transitionend', handler);
      resolve(JSON.stringify({
        actualDurationMs: endTime - startTime,
        transitionedProperties: properties
      }));
    }, 5000);
  });
})()
"""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // detection functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detect all elements with transitions on the page
detectTransitions :: Page -> Aff (Array { selector :: String, config :: Array TransitionConfig })
detectTransitions page = do
  -- Find all elements with transitions
  selectorsJson <- PW.evaluate page findTransitionElementsJS
  pure (parseTransitionElements selectorsJson)

-- | JavaScript to find all elements with transitions
findTransitionElementsJS :: String
findTransitionElementsJS = """
(() => {
  const results = [];
  const elements = document.querySelectorAll('*');
  
  for (const el of elements) {
    const style = getComputedStyle(el);
    const duration = style.transitionDuration;
    
    // Check if has non-zero transition
    if (duration && duration !== '0s' && duration !== '0ms') {
      const selector = getSelector(el);
      const properties = style.transitionProperty.split(',').map(s => s.trim());
      const durations = style.transitionDuration.split(',').map(parseTime);
      const timings = style.transitionTimingFunction.split(/,(?![^(]*\))/).map(s => s.trim());
      const delays = style.transitionDelay.split(',').map(parseTime);
      
      const transitions = [];
      for (let i = 0; i < properties.length; i++) {
        const prop = properties[i];
        if (prop === 'none' || prop === '') continue;
        
        transitions.push({
          property: prop,
          durationMs: durations[i % durations.length] || 0,
          timingFunction: timings[i % timings.length] || 'ease',
          delayMs: delays[i % delays.length] || 0
        });
      }
      
      if (transitions.some(t => t.durationMs > 0)) {
        results.push({ selector, transitions });
      }
    }
  }
  
  return JSON.stringify(results);
  
  function getSelector(el) {
    if (el.id) return '#' + CSS.escape(el.id);
    const path = [];
    while (el && el.nodeType === Node.ELEMENT_NODE) {
      let selector = el.tagName.toLowerCase();
      if (el.id) {
        selector = '#' + CSS.escape(el.id);
        path.unshift(selector);
        break;
      } else {
        let sibling = el;
        let nth = 1;
        while (sibling = sibling.previousElementSibling) {
          if (sibling.tagName === el.tagName) nth++;
        }
        if (nth > 1) selector += ':nth-of-type(' + nth + ')';
      }
      path.unshift(selector);
      el = el.parentElement;
    }
    return path.join(' > ');
  }
  
  function parseTime(str) {
    if (!str) return 0;
    const match = str.trim().match(/([\d.]+)(ms|s)?/);
    if (!match) return 0;
    const value = parseFloat(match[1]);
    if (match[2] === 'ms') return value;
    if (match[2] === 's') return value * 1000;
    return value;
  }
})()
"""

-- | Detect transitions for a specific element
detectElementTransitions :: Page -> String -> Aff (Array TransitionConfig)
detectElementTransitions page selector = do
  resultJson <- PW.evaluate page (detectTransitionJS selector)
  pure (parseTransitionConfigs resultJson)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // observation functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Observe a transition by triggering it and capturing before/after
observeTransition 
  :: Page 
  -> Locator 
  -> String 
  -> InteractionState 
  -> InteractionState 
  -> Aff ObservedTransition
observeTransition page loc selector fromState toState = do
  -- Capture before state
  beforeCapture <- captureElementState page selector
  
  -- Get transition config
  configs <- detectElementTransitions page selector
  let config = Array.head configs
  let maxDuration = case config of
        Just c -> c.durationMs + c.delayMs + 100.0  -- Add buffer
        Nothing -> 500.0  -- Default wait
  
  -- Trigger the interaction
  case toState of
    Hover -> PW.hover loc
    Focus -> PW.focus loc
    Active -> PW.click loc
    _ -> pure unit
  
  -- Wait for transition to complete
  delay (Milliseconds maxDuration)
  
  -- Capture after state
  afterCapture <- captureElementState page selector
  
  -- Compute diff
  let changedProps = computeStateDiff beforeCapture afterCapture
  
  pure
    { selector: selector
    , fromState: fromState
    , toState: toState
    , beforeCapture: beforeCapture
    , afterCapture: afterCapture
    , config: case config of
        Just c -> c
        Nothing -> { property: "all", durationMs: 0.0, timingFunction: "ease", delayMs: 0.0 }
    , changedProps: changedProps
    , actualDurationMs: maxDuration
    }

-- | Measure actual transition timing
-- |
-- | Uses Playwright's evaluate to run measureTransitionJS, which sets up
-- | a transitionend event listener and returns the actual measured duration.
-- |
-- | The JavaScript returns a Promise that Playwright automatically awaits.
measureTransitionTiming :: Page -> String -> Aff { actualDurationMs :: Number, properties :: Array String }
measureTransitionTiming page selector = do
  resultJson <- PW.evaluate page (measureTransitionJS selector)
  pure (parseMeasuredTiming resultJson)
  where
    -- | Parse the timing measurement result
    -- | Expected format: {"actualDurationMs": 123.45, "transitionedProperties": ["opacity", "transform"]}
    parseMeasuredTiming :: String -> { actualDurationMs :: Number, properties :: Array String }
    parseMeasuredTiming json =
      { actualDurationMs: case extractNumber "actualDurationMs" json of
          Just n -> n
          Nothing -> 0.0
      , properties: parsePropertyArray json
      }
    
    -- | Extract a number field from JSON
    extractNumber :: String -> String -> Maybe Number
    extractNumber field json = 
      case findFieldValue field json of
        Just valueStr -> parseJSONNumber valueStr
        Nothing -> Nothing
    
    -- | Find field value (simplified surgical extraction)
    findFieldValue :: String -> String -> Maybe String
    findFieldValue fieldName json =
      let pattern = "\"" <> fieldName <> "\":"
      in case indexOf (Pattern pattern) json of
           Nothing -> Nothing
           Just idx ->
             let afterColon = drop (idx + length pattern) json
             in Just afterColon
    
    -- | Parse JSON number from start of string
    parseJSONNumber :: String -> Maybe Number
    parseJSONNumber str =
      let numChars = takeWhile isNumChar str
      in if null numChars then Nothing
         else fromString numChars
    
    -- | Check if character is part of a number
    isNumChar :: CodePoint -> Boolean
    isNumChar cp = 
      let c = fromEnum cp
      in (c >= 48 && c <= 57) || c == 46 || c == 45 || c == 43 || c == 101 || c == 69
    
    -- | Parse the transitionedProperties array
    parsePropertyArray :: String -> Array String
    parsePropertyArray json =
      case findFieldValue "transitionedProperties" json of
        Nothing -> []
        Just arrStart -> extractStringArray arrStart

    -- | Extract strings from a JSON array like ["a", "b", "c"]
    extractStringArray :: String -> Array String
    extractStringArray str =
      let trimmed = dropWhile (\cp -> fromEnum cp == 32 || fromEnum cp == 91) str  -- skip whitespace and [
      in parseStrings trimmed []
    
    -- | Parse individual strings from array contents
    parseStrings :: String -> Array String -> Array String
    parseStrings remaining acc =
      let trimmed = dropWhile (\cp -> fromEnum cp == 32 || fromEnum cp == 44) remaining  -- skip whitespace and commas
      in case charAt 0 trimmed of
           Nothing -> acc
           Just ']' -> acc
           Just '"' -> 
             let content = extractQuotedContent (drop 1 trimmed)
                 rest = dropPastQuote (drop 1 trimmed)
             in parseStrings rest (Array.snoc acc content)
           _ -> acc
    
    -- | Extract content up to closing quote
    extractQuotedContent :: String -> String
    extractQuotedContent str = takeWhile (\cp -> fromEnum cp /= 34) str  -- stop at "
    
    -- | Drop past the closing quote
    dropPastQuote :: String -> String
    dropPastQuote str = 
      let content = takeWhile (\cp -> fromEnum cp /= 34) str
      in drop (length content + 1) str

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // diff computation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute which properties changed between states
computeStateDiff :: CapturedState -> CapturedState -> Array PropertyTransition
computeStateDiff before after = Array.catMaybes
  [ diffColor "backgroundColor" before.backgroundColor after.backgroundColor
  , diffColor "color" before.color after.color
  , diffColor "borderColor" before.borderColor after.borderColor
  , diffNumber "opacity" before.opacity after.opacity
  , diffNumber "width" before.width after.width
  , diffNumber "height" before.height after.height
  ]

-- | Check if a color changed
diffColor :: String -> Maybe CapturedColor -> Maybe CapturedColor -> Maybe PropertyTransition
diffColor prop before after = case Tuple before after of
  Tuple Nothing Nothing -> Nothing
  Tuple (Just b) (Just a) ->
    if b.l == a.l && b.c == a.c && b.h == a.h && b.a == a.a
      then Nothing
      else Just
        { property: prop
        , fromValue: colorToString b
        , toValue: colorToString a
        , interpolationType: InterpolateColor
        }
  Tuple Nothing (Just a) -> Just
    { property: prop
    , fromValue: "transparent"
    , toValue: colorToString a
    , interpolationType: InterpolateColor
    }
  Tuple (Just b) Nothing -> Just
    { property: prop
    , fromValue: colorToString b
    , toValue: "transparent"
    , interpolationType: InterpolateColor
    }

-- | Check if a number changed
diffNumber :: String -> Number -> Number -> Maybe PropertyTransition
diffNumber prop before after =
  if before == after
    then Nothing
    else Just
      { property: prop
      , fromValue: show before
      , toValue: show after
      , interpolationType: InterpolateNumber
      }

-- | Color to string for debugging
colorToString :: CapturedColor -> String
colorToString c = "oklch(" <> show c.l <> " " <> show c.c <> " " <> show c.h <> " / " <> show c.a <> ")"

-- | Get list of properties that changed
changedProperties :: CapturedState -> CapturedState -> Array String
changedProperties before after = map (\p -> p.property) (computeStateDiff before after)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // easing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse easing string to config
parseEasingString :: String -> EasingConfig
parseEasingString str = case str of
  "linear" -> { name: "linear", cubicBezier: Just { x1: 0.0, y1: 0.0, x2: 1.0, y2: 1.0 }, steps: Nothing }
  "ease" -> { name: "ease", cubicBezier: Just { x1: 0.25, y1: 0.1, x2: 0.25, y2: 1.0 }, steps: Nothing }
  "ease-in" -> { name: "ease-in", cubicBezier: Just { x1: 0.42, y1: 0.0, x2: 1.0, y2: 1.0 }, steps: Nothing }
  "ease-out" -> { name: "ease-out", cubicBezier: Just { x1: 0.0, y1: 0.0, x2: 0.58, y2: 1.0 }, steps: Nothing }
  "ease-in-out" -> { name: "ease-in-out", cubicBezier: Just { x1: 0.42, y1: 0.0, x2: 0.58, y2: 1.0 }, steps: Nothing }
  _ -> 
    -- Try to parse cubic-bezier
    case parseCubicBezier str of
      Just points -> { name: "cubic-bezier", cubicBezier: Just points, steps: Nothing }
      Nothing -> { name: "ease", cubicBezier: Just { x1: 0.25, y1: 0.1, x2: 0.25, y2: 1.0 }, steps: Nothing }

-- | Parse cubic-bezier string
-- |
-- | Parses strings like "cubic-bezier(0.4, 0.0, 0.2, 1.0)" into control points.
-- | Returns Nothing if the string doesn't match the expected format.
parseCubicBezier :: String -> Maybe CubicBezierPoints
parseCubicBezier str =
  -- Check if it starts with "cubic-bezier("
  case indexOf (Pattern "cubic-bezier(") str of
    Just 0 -> 
      -- Extract the content between parentheses
      let afterPrefix = drop 13 str  -- "cubic-bezier(" is 13 chars
          closeParen = CP.codePointFromChar ')'
          -- Find closing paren
          content = takeWhile (\c -> c /= closeParen) afterPrefix
          -- Split by comma
          parts = split (Pattern ",") content
          -- Parse each number
          numbers = Array.mapMaybe (\s -> fromString (trim s)) parts
      in case numbers of
        [x1, y1, x2, y2] -> Just { x1, y1, x2, y2 }
        _ -> Nothing
    _ -> Nothing

-- | Convert easing config to Hydrogen CubicBezierEasing
easingToCubicBezier :: EasingConfig -> Maybe CubicBezierPoints
easingToCubicBezier config = config.cubicBezier

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // parsing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse transition elements from JSON
-- |
-- | Expected format from findTransitionElementsJS:
-- | [{"selector": "...", "transitions": [{"property": "...", "durationMs": 300, ...}, ...]}, ...]
parseTransitionElements :: String -> Array { selector :: String, config :: Array TransitionConfig }
parseTransitionElements json =
  let elementJsons = extractArrayElements json
  in Array.mapMaybe parseTransitionElement elementJsons
  where
    parseTransitionElement :: String -> Maybe { selector :: String, config :: Array TransitionConfig }
    parseTransitionElement elementJson = do
      selector <- extractStringField "selector" elementJson
      let transitionsJson = extractArrayField "transitions" elementJson
          configs = parseTransitionConfigs transitionsJson
      Just { selector, config: configs }

-- | Parse transition configs from JSON
-- |
-- | Expected format (either from detectTransitionJS or as nested array):
-- | [{"property": "opacity", "durationMs": 300, "timingFunction": "ease", "delayMs": 0}, ...]
-- | or: {"hasTransition": true, "transitions": [...]}
parseTransitionConfigs :: String -> Array TransitionConfig
parseTransitionConfigs json =
  -- Check if this is a wrapper object with "transitions" field
  let transitionsArray = case extractArrayField "transitions" json of
        "" -> json  -- json is already the array
        arr -> arr
      configJsons = extractArrayElements transitionsArray
  in Array.mapMaybe parseTransitionConfig configJsons
  where
    parseTransitionConfig :: String -> Maybe TransitionConfig
    parseTransitionConfig configJson = do
      property <- extractStringField "property" configJson
      durationMs <- extractNumberField "durationMs" configJson
      let timingFunction = case extractStringField "timingFunction" configJson of
            Just tf -> tf
            Nothing -> "ease"
          delayMs = case extractNumberField "delayMs" configJson of
            Just d -> d
            Nothing -> 0.0
      Just { property, durationMs, timingFunction, delayMs }

-- | Extract a string field from JSON
extractStringField :: String -> String -> Maybe String
extractStringField fieldName json =
  let pattern = "\"" <> fieldName <> "\":\""
  in case indexOf (Pattern pattern) json of
       Nothing -> Nothing
       Just idx ->
         let afterQuote = drop (idx + length pattern) json
             content = takeWhile (\cp -> fromEnum cp /= 34) afterQuote  -- stop at "
         in Just content

-- | Extract a number field from JSON
extractNumberField :: String -> String -> Maybe Number
extractNumberField fieldName json =
  let pattern = "\"" <> fieldName <> "\":"
  in case indexOf (Pattern pattern) json of
       Nothing -> Nothing
       Just idx ->
         let afterColon = drop (idx + length pattern) json
             trimmed = dropWhile (\cp -> fromEnum cp == 32) afterColon  -- skip whitespace
             numChars = takeWhile isNumberChar trimmed
         in if null numChars then Nothing else fromString numChars

-- | Extract an array field as raw string
extractArrayField :: String -> String -> String
extractArrayField fieldName json =
  let pattern = "\"" <> fieldName <> "\":["
  in case indexOf (Pattern pattern) json of
       Nothing -> ""
       Just idx ->
         let fromBracket = drop (idx + length pattern - 1) json  -- keep the [
         in extractBalanced '[' ']' fromBracket

-- | Extract array elements as individual JSON strings
extractArrayElements :: String -> Array String
extractArrayElements arrJson =
  case charAt 0 arrJson of
    Just '[' -> splitElements (drop 1 arrJson) []
    _ -> []
  where
    splitElements :: String -> Array String -> Array String
    splitElements remaining acc =
      let trimmed = dropWhile (\cp -> fromEnum cp == 32 || fromEnum cp == 44) remaining
      in case charAt 0 trimmed of
           Nothing -> acc
           Just ']' -> acc
           Just '{' ->
             let element = extractBalanced '{' '}' trimmed
                 rest = drop (length element) trimmed
             in splitElements rest (Array.snoc acc element)
           _ -> acc

-- | Extract balanced delimiters
extractBalanced :: Char -> Char -> String -> String
extractBalanced open close str = go str 0 ""
  where
    go :: String -> Int -> String -> String
    go remaining depth acc =
      case charAt 0 remaining of
        Nothing -> acc
        Just c
          | c == open -> go (drop 1 remaining) (depth + 1) (acc <> charToString c)
          | c == close ->
              if depth <= 1 then acc <> charToString c
              else go (drop 1 remaining) (depth - 1) (acc <> charToString c)
          | c == '"' ->
              let quoted = extractQuotedString remaining
                  rest = drop (length quoted) remaining
              in go rest depth (acc <> quoted)
          | otherwise -> go (drop 1 remaining) depth (acc <> charToString c)

-- | Extract a quoted string including quotes
extractQuotedString :: String -> String
extractQuotedString str =
  case charAt 0 str of
    Just '"' -> goQuote (drop 1 str) "\""
    _ -> ""
  where
    goQuote :: String -> String -> String
    goQuote remaining acc =
      case charAt 0 remaining of
        Nothing -> acc
        Just '"' -> acc <> "\""
        Just '\\' -> 
          let escaped = takeN 2 remaining
          in goQuote (drop 2 remaining) (acc <> escaped)
        Just c -> goQuote (drop 1 remaining) (acc <> charToString c)

-- | Take first N characters
takeN :: Int -> String -> String
takeN n str = go n str ""
  where
    go :: Int -> String -> String -> String
    go 0 _ acc = acc
    go remaining s acc = case charAt 0 s of
      Nothing -> acc
      Just c -> go (remaining - 1) (drop 1 s) (acc <> charToString c)

-- | Convert Char to String
charToString :: Char -> String
charToString = singleton

-- | Check if character is part of a number
isNumberChar :: CodePoint -> Boolean
isNumberChar cp =
  let c = fromEnum cp
  in (c >= 48 && c <= 57) || c == 46 || c == 45 || c == 43 || c == 101 || c == 69
