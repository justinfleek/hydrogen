-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // scraper // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Extraction for behavioral visual capture.
-- |
-- | Extracts ALL animation data from a page:
-- |
-- | ## Lottie Animations
-- | - Detect lottie-web, bodymovin, @lottiefiles/lottie-player
-- | - Extract the full animation JSON
-- | - Capture playback state (loop, speed, direction)
-- |
-- | ## CSS Keyframe Animations  
-- | - Find all @keyframes rules
-- | - Extract keyframe percentages and properties
-- | - Capture animation timing (duration, easing, delay, iterations)
-- |
-- | ## Scroll-Linked Animations
-- | - Detect CSS scroll-timeline
-- | - Detect Intersection Observer usage
-- | - Capture scroll-triggered state changes
-- |
-- | ## Canvas/WebGL Animations
-- | - Sample canvas at intervals
-- | - Extract requestAnimationFrame patterns
-- |
-- | ## SVG Animations
-- | - SMIL animations (<animate>, <animateTransform>)
-- | - CSS animations on SVG elements

module Hydrogen.Scraper.Animation
  ( -- * Detection
    detectAnimations
  , detectLottie
  , detectCSSAnimations
  , detectScrollAnimations
  , detectSVGAnimations
  
  -- * Extraction
  , extractLottieData
  , extractKeyframeAnimation
  , extractScrollAnimation
  
  -- * Types
  , DetectedAnimation(..)
  , LottieAnimation
  , CSSKeyframeAnimation
  , ScrollLinkedAnimation
  , SVGAnimation
  , CanvasAnimation
  , FrameSample
  , AnimationKeyframe
  , KeyframeProperty
  , AnimationTiming
  , EasingFunction(..)
  ) where

import Prelude

import Data.Array (snoc) as Array
import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Int (floor) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (fromString)
import Data.String (Pattern(Pattern), drop, dropWhile, indexOf, length, null, takeWhile)
import Data.String.CodeUnits (charAt, singleton)
import Data.String.CodePoints (CodePoint)
import Effect.Aff (Aff)
import Hydrogen.Playwright as PW
import Hydrogen.Playwright (Page)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // animation types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detected animation on the page
data DetectedAnimation
  = DetectedLottie LottieAnimation
  | DetectedCSSKeyframes CSSKeyframeAnimation
  | DetectedScrollLinked ScrollLinkedAnimation
  | DetectedSVG SVGAnimation
  | DetectedCanvas CanvasAnimation

derive instance eqDetectedAnimation :: Eq DetectedAnimation

-- | Lottie animation data
type LottieAnimation =
  { elementSelector :: String
  , animationJson :: String           -- Full Lottie JSON
  , name :: Maybe String              -- Animation name
  , durationMs :: Number
  , frameRate :: Number
  , totalFrames :: Int
  , loop :: Boolean
  , autoplay :: Boolean
  , direction :: Int                  -- 1 = forward, -1 = reverse
  }

-- | CSS @keyframes animation
type CSSKeyframeAnimation =
  { name :: String                    -- Animation name
  , elementSelector :: String         -- Element using this animation
  , keyframes :: Array AnimationKeyframe
  , timing :: AnimationTiming
  }

-- | Single keyframe in an animation
type AnimationKeyframe =
  { offset :: Number                  -- 0.0 to 1.0 (percentage)
  , properties :: Array KeyframeProperty
  , easing :: Maybe EasingFunction
  }

-- | Property in a keyframe
type KeyframeProperty =
  { property :: String
  , value :: String                   -- Raw value, parsed later
  }

-- | Animation timing configuration
type AnimationTiming =
  { durationMs :: Number
  , delayMs :: Number
  , iterations :: Number              -- Infinity represented as -1
  , direction :: String               -- normal, reverse, alternate, alternate-reverse
  , fillMode :: String                -- none, forwards, backwards, both
  , easing :: EasingFunction
  , playState :: String               -- running, paused
  }

-- | Easing function
data EasingFunction
  = Linear
  | Ease
  | EaseIn
  | EaseOut
  | EaseInOut
  | CubicBezier Number Number Number Number
  | Steps Int String                  -- steps(n, start|end)
  | Spring Number Number Number       -- spring(mass, stiffness, damping)

derive instance eqEasingFunction :: Eq EasingFunction

-- | Scroll-linked animation
type ScrollLinkedAnimation =
  { elementSelector :: String
  , scrollSource :: String            -- nearest, root, or element selector
  , axis :: String                    -- block, inline, x, y
  , startOffset :: Number             -- 0.0 to 1.0
  , endOffset :: Number
  , animation :: CSSKeyframeAnimation
  }

-- | SVG animation (SMIL)
type SVGAnimation =
  { elementSelector :: String
  , attributeName :: String
  , from :: String
  , to :: String
  , values :: Maybe (Array String)    -- For multi-step
  , durationMs :: Number
  , repeatCount :: String             -- indefinite or number
  , fill :: String                    -- freeze, remove
  }

-- | Canvas animation (sampled)
type CanvasAnimation =
  { canvasSelector :: String
  , frameSamples :: Array FrameSample
  , estimatedFps :: Number
  }

-- | Single frame sample from canvas
type FrameSample =
  { timestampMs :: Number
  , dataUrl :: String                 -- Base64 PNG of canvas state
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // detection javascript
-- ═══════════════════════════════════════════════════════════════════════════════

-- | JavaScript to detect all animations on page
detectAnimationsJS :: String
detectAnimationsJS = """
(() => {
  const animations = {
    lottie: [],
    cssKeyframes: [],
    scrollLinked: [],
    svg: [],
    canvas: []
  };
  
  // =========================================================================
  // LOTTIE DETECTION
  // =========================================================================
  
  // Method 1: Look for lottie-web instances
  if (window.lottie) {
    const players = document.querySelectorAll('[data-lottie], lottie-player, dotlottie-player');
    for (const player of players) {
      try {
        const anim = player.getLottie ? player.getLottie() : null;
        if (anim && anim.animationData) {
          animations.lottie.push({
            elementSelector: getSelector(player),
            animationJson: JSON.stringify(anim.animationData),
            name: anim.animationData.nm || null,
            durationMs: (anim.totalFrames / anim.frameRate) * 1000,
            frameRate: anim.frameRate,
            totalFrames: anim.totalFrames,
            loop: anim.loop,
            autoplay: anim.autoplay,
            direction: anim.playDirection || 1
          });
        }
      } catch (e) {}
    }
  }
  
  // Method 2: Check for bodymovin data attributes
  const bodymovinElements = document.querySelectorAll('[data-animation-path], [data-anim-path]');
  for (const el of bodymovinElements) {
    const path = el.getAttribute('data-animation-path') || el.getAttribute('data-anim-path');
    if (path) {
      animations.lottie.push({
        elementSelector: getSelector(el),
        animationJson: null,  // Would need to fetch
        animationPath: path,
        name: null,
        durationMs: 0,
        frameRate: 0,
        totalFrames: 0,
        loop: el.getAttribute('data-anim-loop') === 'true',
        autoplay: el.getAttribute('data-anim-autoplay') !== 'false',
        direction: 1
      });
    }
  }
  
  // =========================================================================
  // CSS KEYFRAMES DETECTION
  // =========================================================================
  
  // Get all @keyframes rules
  const keyframesMap = new Map();
  for (const sheet of document.styleSheets) {
    try {
      for (const rule of sheet.cssRules) {
        if (rule instanceof CSSKeyframesRule) {
          const keyframes = [];
          for (const kf of rule.cssRules) {
            const offset = kf.keyText === 'from' ? 0 : 
                          kf.keyText === 'to' ? 1 : 
                          parseFloat(kf.keyText) / 100;
            const properties = [];
            for (let i = 0; i < kf.style.length; i++) {
              const prop = kf.style[i];
              properties.push({
                property: prop,
                value: kf.style.getPropertyValue(prop)
              });
            }
            keyframes.push({ offset, properties, easing: null });
          }
          keyframesMap.set(rule.name, keyframes);
        }
      }
    } catch (e) {}  // Cross-origin stylesheets
  }
  
  // Find elements using these animations
  const allElements = document.querySelectorAll('*');
  for (const el of allElements) {
    const style = getComputedStyle(el);
    const animName = style.animationName;
    if (animName && animName !== 'none' && keyframesMap.has(animName)) {
      animations.cssKeyframes.push({
        name: animName,
        elementSelector: getSelector(el),
        keyframes: keyframesMap.get(animName),
        timing: {
          durationMs: parseTime(style.animationDuration),
          delayMs: parseTime(style.animationDelay),
          iterations: style.animationIterationCount === 'infinite' ? -1 : parseFloat(style.animationIterationCount),
          direction: style.animationDirection,
          fillMode: style.animationFillMode,
          easing: parseEasing(style.animationTimingFunction),
          playState: style.animationPlayState
        }
      });
    }
  }
  
  // =========================================================================
  // SCROLL-LINKED DETECTION
  // =========================================================================
  
  // CSS scroll-timeline (newer API)
  for (const el of allElements) {
    const style = getComputedStyle(el);
    const scrollTimeline = style.scrollTimeline || style.scrollTimelineName;
    if (scrollTimeline && scrollTimeline !== 'none') {
      animations.scrollLinked.push({
        elementSelector: getSelector(el),
        scrollSource: 'root',  // TODO: parse scroll-timeline-axis
        axis: 'block',
        startOffset: 0,
        endOffset: 1,
        animation: null  // Would need to link to the animation
      });
    }
    
    // animation-timeline property
    const animTimeline = style.animationTimeline;
    if (animTimeline && animTimeline !== 'auto' && animTimeline !== 'none') {
      animations.scrollLinked.push({
        elementSelector: getSelector(el),
        scrollSource: animTimeline,
        axis: 'block',
        startOffset: 0,
        endOffset: 1,
        animation: null
      });
    }
  }
  
  // =========================================================================
  // SVG ANIMATION DETECTION
  // =========================================================================
  
  const svgAnimElements = document.querySelectorAll('animate, animateTransform, animateMotion, animateColor');
  for (const anim of svgAnimElements) {
    const parent = anim.parentElement;
    animations.svg.push({
      elementSelector: getSelector(parent),
      attributeName: anim.getAttribute('attributeName') || anim.getAttribute('attributeType') || 'transform',
      from: anim.getAttribute('from') || '',
      to: anim.getAttribute('to') || '',
      values: anim.getAttribute('values')?.split(';') || null,
      durationMs: parseTime(anim.getAttribute('dur') || '0s'),
      repeatCount: anim.getAttribute('repeatCount') || '1',
      fill: anim.getAttribute('fill') || 'remove'
    });
  }
  
  // =========================================================================
  // CANVAS DETECTION
  // =========================================================================
  
  const canvases = document.querySelectorAll('canvas');
  for (const canvas of canvases) {
    // Check if canvas has content (non-empty)
    try {
      const ctx = canvas.getContext('2d');
      const data = ctx.getImageData(0, 0, 1, 1);
      if (data.data.some(v => v > 0)) {
        animations.canvas.push({
          canvasSelector: getSelector(canvas),
          frameSamples: [],  // Would need to sample over time
          estimatedFps: 0
        });
      }
    } catch (e) {}
  }
  
  return JSON.stringify(animations);
  
  // =========================================================================
  // HELPERS
  // =========================================================================
  
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
    const match = str.match(/([\d.]+)(ms|s)/);
    if (!match) return 0;
    const value = parseFloat(match[1]);
    return match[2] === 's' ? value * 1000 : value;
  }
  
  function parseEasing(str) {
    if (str === 'linear') return { type: 'linear' };
    if (str === 'ease') return { type: 'ease' };
    if (str === 'ease-in') return { type: 'ease-in' };
    if (str === 'ease-out') return { type: 'ease-out' };
    if (str === 'ease-in-out') return { type: 'ease-in-out' };
    
    const bezier = str.match(/cubic-bezier\(([\d.]+),\s*([\d.]+),\s*([\d.]+),\s*([\d.]+)\)/);
    if (bezier) {
      return {
        type: 'cubic-bezier',
        x1: parseFloat(bezier[1]),
        y1: parseFloat(bezier[2]),
        x2: parseFloat(bezier[3]),
        y2: parseFloat(bezier[4])
      };
    }
    
    const steps = str.match(/steps\((\d+)(?:,\s*(start|end))?\)/);
    if (steps) {
      return {
        type: 'steps',
        count: parseInt(steps[1]),
        position: steps[2] || 'end'
      };
    }
    
    return { type: 'ease' };  // Default
  }
})()
"""

-- | JavaScript to extract Lottie animation data from a specific element
extractLottieJS :: String -> String
extractLottieJS selector = """
(() => {
  const el = document.querySelector('""" <> selector <> """');
  if (!el) return JSON.stringify({ error: 'not found' });
  
  // Try various methods to get Lottie data
  
  // Method 1: lottie-player web component
  if (el.getLottie) {
    const anim = el.getLottie();
    if (anim && anim.animationData) {
      return JSON.stringify({
        animationJson: JSON.stringify(anim.animationData),
        name: anim.animationData.nm || null,
        durationMs: (anim.totalFrames / anim.frameRate) * 1000,
        frameRate: anim.frameRate,
        totalFrames: anim.totalFrames,
        loop: anim.loop,
        autoplay: anim.autoplay,
        direction: anim.playDirection || 1
      });
    }
  }
  
  // Method 2: Check __lottie__ property (some implementations)
  if (el.__lottie__) {
    const anim = el.__lottie__;
    if (anim.animationData) {
      return JSON.stringify({
        animationJson: JSON.stringify(anim.animationData),
        name: anim.animationData.nm || null,
        durationMs: (anim.totalFrames / anim.frameRate) * 1000,
        frameRate: anim.frameRate,
        totalFrames: anim.totalFrames,
        loop: anim.loop,
        autoplay: anim.autoplay,
        direction: 1
      });
    }
  }
  
  // Method 3: Check for src attribute (fetch the JSON)
  const src = el.getAttribute('src') || el.getAttribute('data-src') || el.getAttribute('data-animation-path');
  if (src) {
    return JSON.stringify({
      animationPath: src,
      needsFetch: true
    });
  }
  
  return JSON.stringify({ error: 'no lottie data found' });
})()
"""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // detection functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detect all animations on the page
detectAnimations :: Page -> Aff (Array DetectedAnimation)
detectAnimations page = do
  resultJson <- PW.evaluate page detectAnimationsJS
  pure (parseDetectedAnimations resultJson)

-- | Detect Lottie animations specifically
detectLottie :: Page -> Aff (Array LottieAnimation)
detectLottie page = do
  animations <- detectAnimations page
  pure (Array.mapMaybe extractLottieFromDetected animations)
  where
    extractLottieFromDetected :: DetectedAnimation -> Maybe LottieAnimation
    extractLottieFromDetected (DetectedLottie l) = Just l
    extractLottieFromDetected _ = Nothing

-- | Detect CSS keyframe animations
detectCSSAnimations :: Page -> Aff (Array CSSKeyframeAnimation)
detectCSSAnimations page = do
  animations <- detectAnimations page
  pure (Array.mapMaybe extractCSSFromDetected animations)
  where
    extractCSSFromDetected :: DetectedAnimation -> Maybe CSSKeyframeAnimation
    extractCSSFromDetected (DetectedCSSKeyframes c) = Just c
    extractCSSFromDetected _ = Nothing

-- | Detect scroll-linked animations
detectScrollAnimations :: Page -> Aff (Array ScrollLinkedAnimation)
detectScrollAnimations page = do
  animations <- detectAnimations page
  pure (Array.mapMaybe extractScrollFromDetected animations)
  where
    extractScrollFromDetected :: DetectedAnimation -> Maybe ScrollLinkedAnimation
    extractScrollFromDetected (DetectedScrollLinked s) = Just s
    extractScrollFromDetected _ = Nothing

-- | Detect SVG animations
detectSVGAnimations :: Page -> Aff (Array SVGAnimation)
detectSVGAnimations page = do
  animations <- detectAnimations page
  pure (Array.mapMaybe extractSVGFromDetected animations)
  where
    extractSVGFromDetected :: DetectedAnimation -> Maybe SVGAnimation
    extractSVGFromDetected (DetectedSVG s) = Just s
    extractSVGFromDetected _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // extraction functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract full Lottie data from a specific element
extractLottieData :: Page -> String -> Aff (Maybe LottieAnimation)
extractLottieData page selector = do
  resultJson <- PW.evaluate page (extractLottieJS selector)
  pure (parseLottieAnimation selector resultJson)

-- | Extract keyframe animation details
extractKeyframeAnimation :: Page -> String -> Aff (Maybe CSSKeyframeAnimation)
extractKeyframeAnimation _ _ = pure Nothing  -- TODO: implement

-- | Extract scroll-linked animation details
extractScrollAnimation :: Page -> String -> Aff (Maybe ScrollLinkedAnimation)
extractScrollAnimation _ _ = pure Nothing  -- TODO: implement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // parsing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse detected animations from JSON
-- |
-- | Expected format from detectAnimationsJS:
-- | {"lottie": [...], "cssKeyframes": [...], "scrollLinked": [...], "svg": [...], "canvas": [...]}
parseDetectedAnimations :: String -> Array DetectedAnimation
parseDetectedAnimations json =
  let lottieAnims = parseLottieArray (extractArrayField "lottie" json)
      cssAnims = parseCSSKeyframeArray (extractArrayField "cssKeyframes" json)
      scrollAnims = parseScrollArray (extractArrayField "scrollLinked" json)
      svgAnims = parseSVGArray (extractArrayField "svg" json)
      canvasAnims = parseCanvasArray (extractArrayField "canvas" json)
  in (map DetectedLottie lottieAnims)
     <> (map DetectedCSSKeyframes cssAnims)
     <> (map DetectedScrollLinked scrollAnims)
     <> (map DetectedSVG svgAnims)
     <> (map DetectedCanvas canvasAnims)

-- | Parse Lottie animation from JSON
-- |
-- | Expected format from extractLottieJS:
-- | {"animationJson": "...", "name": "...", "durationMs": 1000, ...}
parseLottieAnimation :: String -> String -> Maybe LottieAnimation
parseLottieAnimation selector json = do
  -- animationJson is required
  animationJson <- extractStringField "animationJson" json
  let name = extractStringField "name" json
      durationMs = extractNumberOrZero "durationMs" json
      frameRate = extractNumberOrZero "frameRate" json
      totalFrames = Int.floor (extractNumberOrZero "totalFrames" json)
      loop = extractBoolOrFalse "loop" json
      autoplay = extractBoolOrFalse "autoplay" json
      direction = Int.floor (extractNumberOrDefault "direction" 1.0 json)
  Just 
    { elementSelector: selector
    , animationJson
    , name
    , durationMs
    , frameRate
    , totalFrames
    , loop
    , autoplay
    , direction
    }

-- | Parse array of Lottie animations
parseLottieArray :: String -> Array LottieAnimation
parseLottieArray arrJson =
  let elementJsons = extractArrayElements arrJson
  in Array.mapMaybe parseLottieElement elementJsons
  where
    parseLottieElement :: String -> Maybe LottieAnimation
    parseLottieElement json = do
      selector <- extractStringField "elementSelector" json
      parseLottieAnimation selector json

-- | Parse array of CSS keyframe animations
parseCSSKeyframeArray :: String -> Array CSSKeyframeAnimation
parseCSSKeyframeArray arrJson =
  let elementJsons = extractArrayElements arrJson
  in Array.mapMaybe parseCSSKeyframeElement elementJsons
  where
    parseCSSKeyframeElement :: String -> Maybe CSSKeyframeAnimation
    parseCSSKeyframeElement json = do
      name <- extractStringField "name" json
      elementSelector <- extractStringField "elementSelector" json
      let keyframesJson = extractArrayField "keyframes" json
          keyframes = parseKeyframeArray keyframesJson
          timingJson = extractObjectField "timing" json
          timing = parseAnimationTiming timingJson
      Just { name, elementSelector, keyframes, timing }

-- | Parse animation keyframes
parseKeyframeArray :: String -> Array AnimationKeyframe
parseKeyframeArray arrJson =
  let elementJsons = extractArrayElements arrJson
  in Array.mapMaybe parseKeyframe elementJsons
  where
    parseKeyframe :: String -> Maybe AnimationKeyframe
    parseKeyframe json =
      let offset = extractNumberOrZero "offset" json
          propsJson = extractArrayField "properties" json
          properties = parseKeyframeProperties propsJson
          easing = Nothing  -- TODO: parse easing from keyframe
      in Just { offset, properties, easing }
    
    parseKeyframeProperties :: String -> Array KeyframeProperty
    parseKeyframeProperties arrJson' =
      let propJsons = extractArrayElements arrJson'
      in Array.mapMaybe parseProperty propJsons
    
    parseProperty :: String -> Maybe KeyframeProperty
    parseProperty json = do
      property <- extractStringField "property" json
      value <- extractStringField "value" json
      Just { property, value }

-- | Parse animation timing
parseAnimationTiming :: String -> AnimationTiming
parseAnimationTiming json =
  { durationMs: extractNumberOrZero "durationMs" json
  , delayMs: extractNumberOrZero "delayMs" json
  , iterations: extractNumberOrDefault "iterations" 1.0 json
  , direction: extractStringOrDefault "direction" "normal" json
  , fillMode: extractStringOrDefault "fillMode" "none" json
  , easing: parseEasingFromJson json
  , playState: extractStringOrDefault "playState" "running" json
  }

-- | Parse easing from JSON object
parseEasingFromJson :: String -> EasingFunction
parseEasingFromJson json =
  let easingJson = extractObjectField "easing" json
      easingType = extractStringOrDefault "type" "ease" easingJson
  in case easingType of
       "linear" -> Linear
       "ease-in" -> EaseIn
       "ease-out" -> EaseOut
       "ease-in-out" -> EaseInOut
       "cubic-bezier" ->
         let x1 = extractNumberOrZero "x1" easingJson
             y1 = extractNumberOrZero "y1" easingJson
             x2 = extractNumberOrZero "x2" easingJson
             y2 = extractNumberOrZero "y2" easingJson
         in CubicBezier x1 y1 x2 y2
       "steps" ->
         let count = Int.floor (extractNumberOrDefault "count" 1.0 easingJson)
             position = extractStringOrDefault "position" "end" easingJson
         in Steps count position
       _ -> Ease

-- | Parse scroll-linked animations
parseScrollArray :: String -> Array ScrollLinkedAnimation
parseScrollArray arrJson =
  let elementJsons = extractArrayElements arrJson
  in Array.mapMaybe parseScrollElement elementJsons
  where
    parseScrollElement :: String -> Maybe ScrollLinkedAnimation
    parseScrollElement json = do
      elementSelector <- extractStringField "elementSelector" json
      let scrollSource = extractStringOrDefault "scrollSource" "root" json
          axis = extractStringOrDefault "axis" "block" json
          startOffset = extractNumberOrZero "startOffset" json
          endOffset = extractNumberOrDefault "endOffset" 1.0 json
          -- animation field is null in the JS, create placeholder
          animation = 
            { name: ""
            , elementSelector
            , keyframes: []
            , timing: parseAnimationTiming ""
            }
      Just { elementSelector, scrollSource, axis, startOffset, endOffset, animation }

-- | Parse SVG animations
parseSVGArray :: String -> Array SVGAnimation
parseSVGArray arrJson =
  let elementJsons = extractArrayElements arrJson
  in Array.mapMaybe parseSVGElement elementJsons
  where
    parseSVGElement :: String -> Maybe SVGAnimation
    parseSVGElement json = do
      elementSelector <- extractStringField "elementSelector" json
      let attributeName = extractStringOrDefault "attributeName" "transform" json
          from = extractStringOrDefault "from" "" json
          to = extractStringOrDefault "to" "" json
          valuesStr = extractStringField "values" json
          values = case valuesStr of
            Just _ -> Nothing  -- TODO: split by semicolon
            Nothing -> Nothing
          durationMs = extractNumberOrZero "durationMs" json
          repeatCount = extractStringOrDefault "repeatCount" "1" json
          fill = extractStringOrDefault "fill" "remove" json
      Just { elementSelector, attributeName, from, to, values, durationMs, repeatCount, fill }

-- | Parse canvas animations
parseCanvasArray :: String -> Array CanvasAnimation
parseCanvasArray arrJson =
  let elementJsons = extractArrayElements arrJson
  in Array.mapMaybe parseCanvasElement elementJsons
  where
    parseCanvasElement :: String -> Maybe CanvasAnimation
    parseCanvasElement json = do
      canvasSelector <- extractStringField "canvasSelector" json
      let frameSamples = []  -- Frame samples require runtime sampling
          estimatedFps = extractNumberOrZero "estimatedFps" json
      Just { canvasSelector, frameSamples, estimatedFps }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // json extraction helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract a string field from JSON
extractStringField :: String -> String -> Maybe String
extractStringField fieldName json =
  let pattern = "\"" <> fieldName <> "\":\""
  in case indexOf (Pattern pattern) json of
       Nothing -> Nothing
       Just idx ->
         let afterQuote = drop (idx + length pattern) json
             content = takeWhile (\cp -> fromEnum cp /= 34) afterQuote
         in Just content

-- | Extract a number field with default
extractNumberOrDefault :: String -> Number -> String -> Number
extractNumberOrDefault fieldName defaultVal json =
  case extractNumberField fieldName json of
    Just n -> n
    Nothing -> defaultVal

-- | Extract a number field, returning 0 if not found
extractNumberOrZero :: String -> String -> Number
extractNumberOrZero = flip extractNumberOrDefault 0.0

-- | Extract a number field from JSON
extractNumberField :: String -> String -> Maybe Number
extractNumberField fieldName json =
  let pattern = "\"" <> fieldName <> "\":"
  in case indexOf (Pattern pattern) json of
       Nothing -> Nothing
       Just idx ->
         let afterColon = drop (idx + length pattern) json
             trimmed = dropWhile (\cp -> fromEnum cp == 32) afterColon
             numChars = takeWhile isNumberChar trimmed
         in if null numChars then Nothing else fromString numChars

-- | Extract a boolean field with default false
extractBoolOrFalse :: String -> String -> Boolean
extractBoolOrFalse fieldName json =
  let pattern = "\"" <> fieldName <> "\":"
  in case indexOf (Pattern pattern) json of
       Nothing -> false
       Just idx ->
         let afterColon = drop (idx + length pattern) json
             trimmed = dropWhile (\cp -> fromEnum cp == 32) afterColon
         in case takeWhile (\cp -> fromEnum cp >= 97 && fromEnum cp <= 122) trimmed of
              "true" -> true
              _ -> false

-- | Extract a string field with default
extractStringOrDefault :: String -> String -> String -> String
extractStringOrDefault fieldName defaultVal json =
  case extractStringField fieldName json of
    Just s -> s
    Nothing -> defaultVal

-- | Extract an array field as raw string
extractArrayField :: String -> String -> String
extractArrayField fieldName json =
  let pattern = "\"" <> fieldName <> "\":["
  in case indexOf (Pattern pattern) json of
       Nothing -> "[]"
       Just idx ->
         let fromBracket = drop (idx + length pattern - 1) json
         in extractBalanced '[' ']' fromBracket

-- | Extract an object field as raw string
extractObjectField :: String -> String -> String
extractObjectField fieldName json =
  let pattern = "\"" <> fieldName <> "\":{"
  in case indexOf (Pattern pattern) json of
       Nothing -> "{}"
       Just idx ->
         let fromBrace = drop (idx + length pattern - 1) json
         in extractBalanced '{' '}' fromBrace

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
          | c == open -> go (drop 1 remaining) (depth + 1) (acc <> singleton c)
          | c == close ->
              if depth <= 1 then acc <> singleton c
              else go (drop 1 remaining) (depth - 1) (acc <> singleton c)
          | c == '"' ->
              let quoted = extractQuotedString remaining
                  rest = drop (length quoted) remaining
              in go rest depth (acc <> quoted)
          | otherwise -> go (drop 1 remaining) depth (acc <> singleton c)

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
          let first = charAt 0 remaining
              second = charAt 1 remaining
              escaped = case first of
                Just c1 -> case second of
                  Just c2 -> singleton c1 <> singleton c2
                  Nothing -> singleton c1
                Nothing -> ""
          in goQuote (drop 2 remaining) (acc <> escaped)
        Just c -> goQuote (drop 1 remaining) (acc <> singleton c)

-- | Check if character is part of a number
isNumberChar :: CodePoint -> Boolean
isNumberChar cp =
  let c = fromEnum cp
  in (c >= 48 && c <= 57) || c == 46 || c == 45 || c == 43 || c == 101 || c == 69

-- | Parse easing string to EasingFunction
parseEasingFunction :: String -> EasingFunction
parseEasingFunction "linear" = Linear
parseEasingFunction "ease" = Ease
parseEasingFunction "ease-in" = EaseIn
parseEasingFunction "ease-out" = EaseOut
parseEasingFunction "ease-in-out" = EaseInOut
parseEasingFunction _ = Ease  -- Default
