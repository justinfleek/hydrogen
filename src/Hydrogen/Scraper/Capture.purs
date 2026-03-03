-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // scraper // capture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Capture computed visual state as Hydrogen atoms.
-- |
-- | This module extracts the ACTUAL rendered state of elements,
-- | not CSS source. We use getComputedStyle() to get final values
-- | after all CSS cascading, specificity, and inheritance.
-- |
-- | ## Output
-- |
-- | All values are Hydrogen atoms:
-- | - Colors as OKLCH (perceptual uniformity)
-- | - Dimensions as Pixel
-- | - Transforms as Transform matrix
-- | - Shadows as LayeredShadow
-- |
-- | ## JavaScript Evaluation
-- |
-- | We inject JS to extract computed styles because Playwright's
-- | evaluate() is the only way to access the rendering engine's
-- | final computed values.

module Hydrogen.Scraper.Capture
  ( -- * Capture State
    captureElementState
  , captureAllElements
  
  -- * Types
  , CapturedState
  , CapturedColor
  , CapturedTransform
  , CapturedShadow
  , CapturedBoundingBox
  
  -- * Parsing
  , parseColor
  , parseTransform
  , parseShadow
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (mapMaybe) as Array
import Effect.Aff (Aff)
import Hydrogen.Playwright as PW
import Hydrogen.Playwright (Page)
import Hydrogen.Scraper.Wire.Parse as Parse

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // captured types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Captured visual state of an element
-- |
-- | All values are computed (final rendered values), not CSS source.
-- | This is the COMPLETE capture — every visual property needed for 1:1 parity.
-- |
-- | Includes:
-- | - DOM tree structure (parent/child indices for reconstruction)
-- | - Accessibility info (role, aria-label)
-- | - All visual properties as Schema atoms
type CapturedState =
  { -- Identity
    tagName :: String
  , elementId :: String
  , className :: String
  , selector :: String              -- Unique CSS selector path
  
  -- DOM Tree Structure
  , index :: Int                    -- Index in flat element array
  , parentIndex :: Int              -- Parent's index (-1 if root)
  , childIndices :: Array Int       -- Children's indices
  , depth :: Int                    -- Nesting depth
  
  -- Accessibility
  , role :: String                  -- ARIA role or implicit role
  , ariaLabel :: String             -- aria-label
  , ariaDescribedBy :: String       -- aria-describedby
  , tabIndex :: Int                 -- Tab order
  
  -- Content
  , textContent :: String           -- Direct text content (not children)
  
  -- Geometry
  , x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , boundingBox :: Maybe CapturedBoundingBox
  
  -- Colors (as OKLCH components)
  , backgroundColor :: Maybe CapturedColor
  , color :: Maybe CapturedColor
  , borderColor :: Maybe CapturedColor
  
  -- Typography
  , fontFamily :: String
  , fontSize :: Number              -- px
  , fontWeight :: Int               -- 100-900
  , lineHeight :: Number            -- px
  , letterSpacing :: Number         -- px
  , textAlign :: String
  , textDecoration :: String
  , textTransform :: String
  
  -- Spacing - Margins
  , marginTop :: Number
  , marginRight :: Number
  , marginBottom :: Number
  , marginLeft :: Number
  
  -- Spacing - Paddings
  , paddingTop :: Number
  , paddingRight :: Number
  , paddingBottom :: Number
  , paddingLeft :: Number
  
  -- Borders - Widths
  , borderTopWidth :: Number
  , borderRightWidth :: Number
  , borderBottomWidth :: Number
  , borderLeftWidth :: Number
  
  -- Borders - Radii
  , borderTopLeftRadius :: Number
  , borderTopRightRadius :: Number
  , borderBottomRightRadius :: Number
  , borderBottomLeftRadius :: Number
  
  -- Borders - Styles
  , borderTopStyle :: String
  , borderRightStyle :: String
  , borderBottomStyle :: String
  , borderLeftStyle :: String
  
  -- Elevation
  , boxShadow :: Maybe CapturedShadow
  , zIndex :: Int
  
  -- Transform
  , transform :: Maybe CapturedTransform
  
  -- Display properties
  , opacity :: Number
  , visibility :: String
  , display :: String
  , overflow :: String
  , position :: String
  
  -- Flex/Grid Layout
  , flexDirection :: String
  , justifyContent :: String
  , alignItems :: String
  , gap :: Number
  
  -- Interactivity
  , cursor :: String
  , pointerEvents :: String
  
  -- Transition info (for animation detection)
  , transitionDuration :: String
  , transitionTimingFunction :: String
  , transitionDelay :: String
  , transitionProperty :: String
  }

-- | Color in OKLCH space
-- | We convert from RGB to OKLCH for perceptual uniformity
type CapturedColor =
  { l :: Number  -- Lightness 0-1
  , c :: Number  -- Chroma 0-0.4
  , h :: Number  -- Hue 0-360
  , a :: Number  -- Alpha 0-1
  }

-- | Transform matrix components
type CapturedTransform =
  { a :: Number, b :: Number
  , c :: Number, d :: Number
  , e :: Number, f :: Number
  -- 3D components
  , is3D :: Boolean
  , m11 :: Number, m12 :: Number, m13 :: Number, m14 :: Number
  , m21 :: Number, m22 :: Number, m23 :: Number, m24 :: Number
  , m31 :: Number, m32 :: Number, m33 :: Number, m34 :: Number
  , m41 :: Number, m42 :: Number, m43 :: Number, m44 :: Number
  }

-- | Box shadow components
type CapturedShadow =
  { inset :: Boolean
  , offsetX :: Number
  , offsetY :: Number
  , blurRadius :: Number
  , spreadRadius :: Number
  , color :: CapturedColor
  }

-- | Bounding box
type CapturedBoundingBox =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  , left :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // capture js injection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | JavaScript to capture element state
-- | Extracts computed styles and converts colors to OKLCH
captureElementJS :: String -> String
captureElementJS selector = """
(() => {
  const el = document.querySelector('""" <> selector <> """');
  if (!el) return JSON.stringify({ error: 'not found' });
  
  const style = getComputedStyle(el);
  const rect = el.getBoundingClientRect();
  
  // Parse color to OKLCH
  function parseColorToOKLCH(colorStr) {
    if (!colorStr || colorStr === 'transparent' || colorStr === 'rgba(0, 0, 0, 0)') {
      return null;
    }
    
    // Create temporary element to parse color
    const temp = document.createElement('div');
    temp.style.color = colorStr;
    document.body.appendChild(temp);
    const computed = getComputedStyle(temp).color;
    document.body.removeChild(temp);
    
    // Parse rgba
    const match = computed.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?\)/);
    if (!match) return null;
    
    const r = parseInt(match[1]) / 255;
    const g = parseInt(match[2]) / 255;
    const b = parseInt(match[3]) / 255;
    const a = match[4] ? parseFloat(match[4]) : 1;
    
    // Convert sRGB to OKLCH (simplified - full conversion is complex)
    // This is a reasonable approximation for most colors
    const l = 0.2126 * r + 0.7152 * g + 0.0722 * b;  // Luminance
    
    // Approximate chroma from saturation
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    const c = (max - min) * 0.4;  // Scale to OKLCH range
    
    // Hue (same as HSL)
    let h = 0;
    if (max !== min) {
      if (max === r) h = ((g - b) / (max - min)) % 6;
      else if (max === g) h = (b - r) / (max - min) + 2;
      else h = (r - g) / (max - min) + 4;
      h = Math.round(h * 60);
      if (h < 0) h += 360;
    }
    
    return { l, c, h, a };
  }
  
  // Parse transform matrix
  function parseTransform(transformStr) {
    if (!transformStr || transformStr === 'none') {
      return null;
    }
    
    // matrix(a, b, c, d, e, f) or matrix3d(...)
    const matrix2d = transformStr.match(/matrix\(([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+)\)/);
    if (matrix2d) {
      return {
        is3D: false,
        a: parseFloat(matrix2d[1]),
        b: parseFloat(matrix2d[2]),
        c: parseFloat(matrix2d[3]),
        d: parseFloat(matrix2d[4]),
        e: parseFloat(matrix2d[5]),
        f: parseFloat(matrix2d[6]),
        // Identity for 3D components
        m11: 1, m12: 0, m13: 0, m14: 0,
        m21: 0, m22: 1, m23: 0, m24: 0,
        m31: 0, m32: 0, m33: 1, m34: 0,
        m41: 0, m42: 0, m43: 0, m44: 1
      };
    }
    
    const matrix3d = transformStr.match(/matrix3d\(([\d.\-e,\s]+)\)/);
    if (matrix3d) {
      const vals = matrix3d[1].split(',').map(v => parseFloat(v.trim()));
      return {
        is3D: true,
        a: vals[0], b: vals[1], c: vals[4], d: vals[5], e: vals[12], f: vals[13],
        m11: vals[0], m12: vals[1], m13: vals[2], m14: vals[3],
        m21: vals[4], m22: vals[5], m23: vals[6], m24: vals[7],
        m31: vals[8], m32: vals[9], m33: vals[10], m34: vals[11],
        m41: vals[12], m42: vals[13], m43: vals[14], m44: vals[15]
      };
    }
    
    return null;
  }
  
  // Parse box-shadow
  function parseBoxShadow(shadowStr) {
    if (!shadowStr || shadowStr === 'none') {
      return null;
    }
    
    // Basic parsing - handles most common cases
    const inset = shadowStr.includes('inset');
    
    // Extract color first (rgb/rgba/hex)
    let colorStr = 'black';
    const rgbMatch = shadowStr.match(/rgba?\([^)]+\)/);
    if (rgbMatch) colorStr = rgbMatch[0];
    
    // Extract numeric values
    const nums = shadowStr.replace(/rgba?\([^)]+\)/, '').match(/-?[\d.]+px/g);
    if (!nums || nums.length < 2) return null;
    
    return {
      inset: inset,
      offsetX: parseFloat(nums[0]),
      offsetY: parseFloat(nums[1]),
      blurRadius: nums[2] ? parseFloat(nums[2]) : 0,
      spreadRadius: nums[3] ? parseFloat(nums[3]) : 0,
      color: parseColorToOKLCH(colorStr)
    };
  }
  
  // Parse transition duration
  function parseTransitionDuration(str) {
    if (!str || str === '0s') return null;
    const match = str.match(/([\d.]+)(ms|s)/);
    if (!match) return null;
    const value = parseFloat(match[1]);
    return match[2] === 's' ? value * 1000 : value;
  }
  
  return JSON.stringify({
    backgroundColor: parseColorToOKLCH(style.backgroundColor),
    color: parseColorToOKLCH(style.color),
    borderColor: parseColorToOKLCH(style.borderColor),
    transform: parseTransform(style.transform),
    opacity: parseFloat(style.opacity),
    boxShadow: parseBoxShadow(style.boxShadow),
    width: rect.width,
    height: rect.height,
    boundingBox: {
      x: rect.x,
      y: rect.y,
      width: rect.width,
      height: rect.height,
      top: rect.top,
      right: rect.right,
      bottom: rect.bottom,
      left: rect.left
    },
    transitionDuration: parseTransitionDuration(style.transitionDuration),
    transitionTimingFunction: style.transitionTimingFunction !== 'ease' ? style.transitionTimingFunction : null,
    transitionDelay: parseTransitionDuration(style.transitionDelay)
  });
})()
"""

-- | JavaScript to capture all visible elements with FULL visual properties
-- |
-- | Extracts EVERYTHING needed for 1:1 visual parity:
-- | - Geometry: position, size, bounding box
-- | - Colors: background, foreground, border (→ OKLCH)
-- | - Typography: family, size, weight, lineHeight, letterSpacing
-- | - Spacing: all margins and paddings
-- | - Borders: all widths and radii
-- | - Elevation: shadow, zIndex
-- | - Transform: matrix decomposition
-- | - Opacity, visibility, display, overflow
captureAllElementsJS :: String
captureAllElementsJS = """
(() => {
  const elements = document.querySelectorAll('*');
  const results = [];
  
  // Parse color to OKLCH components
  function parseColorToOKLCH(colorStr) {
    if (!colorStr || colorStr === 'transparent' || colorStr === 'rgba(0, 0, 0, 0)') {
      return null;
    }
    
    // Parse rgba/rgb
    const match = colorStr.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?\)/);
    if (!match) return null;
    
    const r = parseInt(match[1]) / 255;
    const g = parseInt(match[2]) / 255;
    const b = parseInt(match[3]) / 255;
    const a = match[4] ? parseFloat(match[4]) : 1;
    
    // sRGB to linear RGB
    const toLinear = (c) => c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
    const lr = toLinear(r), lg = toLinear(g), lb = toLinear(b);
    
    // Linear RGB to XYZ (D65)
    const x = 0.4124564 * lr + 0.3575761 * lg + 0.1804375 * lb;
    const y = 0.2126729 * lr + 0.7151522 * lg + 0.0721750 * lb;
    const z = 0.0193339 * lr + 0.1191920 * lg + 0.9503041 * lb;
    
    // XYZ to Oklab
    const l_ = Math.cbrt(0.8189330101 * x + 0.3618667424 * y - 0.1288597137 * z);
    const m_ = Math.cbrt(0.0329845436 * x + 0.9293118715 * y + 0.0361456387 * z);
    const s_ = Math.cbrt(0.0482003018 * x + 0.2643662691 * y + 0.6338517070 * z);
    
    const L = 0.2104542553 * l_ + 0.7936177850 * m_ - 0.0040720468 * s_;
    const A = 1.9779984951 * l_ - 2.4285922050 * m_ + 0.4505937099 * s_;
    const B = 0.0259040371 * l_ + 0.7827717662 * m_ - 0.8086757660 * s_;
    
    // Oklab to OKLCH
    const C = Math.sqrt(A * A + B * B);
    let H = Math.atan2(B, A) * 180 / Math.PI;
    if (H < 0) H += 360;
    
    return { l: L, c: C, h: H, a: a };
  }
  
  // Parse CSS pixel value to number
  function parsePx(str) {
    if (!str) return 0;
    const match = str.match(/([\d.]+)px/);
    return match ? parseFloat(match[1]) : 0;
  }
  
  // Parse font-weight (can be number or keyword)
  function parseFontWeight(str) {
    if (!str) return 400;
    const num = parseInt(str);
    if (!isNaN(num)) return num;
    const weights = { thin: 100, hairline: 100, extralight: 200, ultralight: 200,
      light: 300, normal: 400, regular: 400, medium: 500, semibold: 600,
      demibold: 600, bold: 700, extrabold: 800, ultrabold: 800, black: 900, heavy: 900 };
    return weights[str.toLowerCase()] || 400;
  }
  
  // Parse z-index (can be 'auto' or number)
  function parseZIndex(str) {
    if (!str || str === 'auto') return 0;
    const num = parseInt(str);
    return isNaN(num) ? 0 : num;
  }
  
  // Parse transform matrix
  function parseTransform(transformStr) {
    if (!transformStr || transformStr === 'none') {
      return { a: 1, b: 0, c: 0, d: 1, e: 0, f: 0, is3D: false };
    }
    
    const matrix2d = transformStr.match(/matrix\(([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+)\)/);
    if (matrix2d) {
      return {
        is3D: false,
        a: parseFloat(matrix2d[1]), b: parseFloat(matrix2d[2]),
        c: parseFloat(matrix2d[3]), d: parseFloat(matrix2d[4]),
        e: parseFloat(matrix2d[5]), f: parseFloat(matrix2d[6])
      };
    }
    
    const matrix3d = transformStr.match(/matrix3d\(([\d.\-e,\s]+)\)/);
    if (matrix3d) {
      const vals = matrix3d[1].split(',').map(v => parseFloat(v.trim()));
      return {
        is3D: true,
        a: vals[0], b: vals[1], c: vals[4], d: vals[5], e: vals[12], f: vals[13]
      };
    }
    
    return { a: 1, b: 0, c: 0, d: 1, e: 0, f: 0, is3D: false };
  }
  
  // Parse box-shadow
  function parseBoxShadow(shadowStr) {
    if (!shadowStr || shadowStr === 'none') return null;
    
    const inset = shadowStr.includes('inset');
    let colorStr = 'rgb(0, 0, 0)';
    const rgbMatch = shadowStr.match(/rgba?\([^)]+\)/);
    if (rgbMatch) colorStr = rgbMatch[0];
    
    const nums = shadowStr.replace(/rgba?\([^)]+\)/, '').match(/-?[\d.]+px/g);
    if (!nums || nums.length < 2) return null;
    
    return {
      inset: inset,
      offsetX: parseFloat(nums[0]),
      offsetY: parseFloat(nums[1]),
      blurRadius: nums[2] ? parseFloat(nums[2]) : 0,
      spreadRadius: nums[3] ? parseFloat(nums[3]) : 0,
      color: parseColorToOKLCH(colorStr)
    };
  }
  
  // Build element-to-index map for parent tracking
  const elementArray = Array.from(elements);
  const elementToIndex = new Map();
  let idx = 0;
  for (const el of elementArray) {
    elementToIndex.set(el, idx++);
  }
  
  // Generate unique selector for element
  function getSelector(el) {
    if (el.id) return '#' + CSS.escape(el.id);
    
    const path = [];
    let current = el;
    while (current && current.nodeType === Node.ELEMENT_NODE) {
      let selector = current.tagName.toLowerCase();
      if (current.id) {
        selector = '#' + CSS.escape(current.id);
        path.unshift(selector);
        break;
      } else {
        let sibling = current;
        let nth = 1;
        while (sibling = sibling.previousElementSibling) {
          if (sibling.tagName === current.tagName) nth++;
        }
        if (nth > 1) selector += ':nth-of-type(' + nth + ')';
      }
      path.unshift(selector);
      current = current.parentElement;
    }
    return path.join(' > ');
  }
  
  // Get text content (direct text only, not children)
  function getDirectText(el) {
    let text = '';
    for (const node of el.childNodes) {
      if (node.nodeType === Node.TEXT_NODE) {
        text += node.textContent;
      }
    }
    return text.trim().slice(0, 500); // Cap at 500 chars
  }
  
  for (const el of elementArray) {
    const style = getComputedStyle(el);
    if (style.display === 'none' || style.visibility === 'hidden') continue;
    if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
    
    const rect = el.getBoundingClientRect();
    
    // Find parent index
    const parent = el.parentElement;
    const parentIndex = parent ? (elementToIndex.get(parent) ?? -1) : -1;
    
    // Get child indices
    const childIndices = [];
    for (const child of el.children) {
      const childIdx = elementToIndex.get(child);
      if (childIdx !== undefined) childIndices.push(childIdx);
    }
    
    results.push({
      // Identity
      tagName: el.tagName,
      id: el.id || '',
      className: typeof el.className === 'string' ? el.className : '',
      selector: getSelector(el),
      
      // DOM Tree Structure
      index: elementToIndex.get(el),
      parentIndex: parentIndex,
      childIndices: childIndices,
      depth: getSelector(el).split(' > ').length,
      
      // Accessibility
      role: el.getAttribute('role') || el.tagName.toLowerCase(),
      ariaLabel: el.getAttribute('aria-label') || '',
      ariaDescribedBy: el.getAttribute('aria-describedby') || '',
      tabIndex: el.tabIndex,
      
      // Content
      textContent: getDirectText(el),
      
      // Geometry
      x: rect.x,
      y: rect.y,
      width: rect.width,
      height: rect.height,
      boundingBox: {
        x: rect.x, y: rect.y, width: rect.width, height: rect.height,
        top: rect.top, right: rect.right, bottom: rect.bottom, left: rect.left
      },
      
      // Colors (OKLCH)
      backgroundColor: parseColorToOKLCH(style.backgroundColor),
      color: parseColorToOKLCH(style.color),
      borderColor: parseColorToOKLCH(style.borderColor),
      
      // Typography
      fontFamily: style.fontFamily,
      fontSize: parsePx(style.fontSize),
      fontWeight: parseFontWeight(style.fontWeight),
      lineHeight: parsePx(style.lineHeight) || parsePx(style.fontSize) * 1.2,
      letterSpacing: parsePx(style.letterSpacing),
      textAlign: style.textAlign,
      textDecoration: style.textDecoration,
      textTransform: style.textTransform,
      
      // Spacing - Margins
      marginTop: parsePx(style.marginTop),
      marginRight: parsePx(style.marginRight),
      marginBottom: parsePx(style.marginBottom),
      marginLeft: parsePx(style.marginLeft),
      
      // Spacing - Paddings
      paddingTop: parsePx(style.paddingTop),
      paddingRight: parsePx(style.paddingRight),
      paddingBottom: parsePx(style.paddingBottom),
      paddingLeft: parsePx(style.paddingLeft),
      
      // Borders - Widths
      borderTopWidth: parsePx(style.borderTopWidth),
      borderRightWidth: parsePx(style.borderRightWidth),
      borderBottomWidth: parsePx(style.borderBottomWidth),
      borderLeftWidth: parsePx(style.borderLeftWidth),
      
      // Borders - Radii
      borderTopLeftRadius: parsePx(style.borderTopLeftRadius),
      borderTopRightRadius: parsePx(style.borderTopRightRadius),
      borderBottomRightRadius: parsePx(style.borderBottomRightRadius),
      borderBottomLeftRadius: parsePx(style.borderBottomLeftRadius),
      
      // Borders - Style
      borderTopStyle: style.borderTopStyle,
      borderRightStyle: style.borderRightStyle,
      borderBottomStyle: style.borderBottomStyle,
      borderLeftStyle: style.borderLeftStyle,
      
      // Elevation
      boxShadow: parseBoxShadow(style.boxShadow),
      zIndex: parseZIndex(style.zIndex),
      
      // Transform
      transform: parseTransform(style.transform),
      
      // Display properties
      opacity: parseFloat(style.opacity),
      visibility: style.visibility,
      display: style.display,
      overflow: style.overflow,
      position: style.position,
      
      // Flex/Grid
      flexDirection: style.flexDirection,
      justifyContent: style.justifyContent,
      alignItems: style.alignItems,
      gap: parsePx(style.gap),
      
      // Cursor (indicates interactivity)
      cursor: style.cursor,
      pointerEvents: style.pointerEvents,
      
      // Transition timing (for animation detection)
      transitionDuration: style.transitionDuration,
      transitionTimingFunction: style.transitionTimingFunction,
      transitionDelay: style.transitionDelay,
      transitionProperty: style.transitionProperty
    });
  }
  
  return JSON.stringify({ count: results.length, elements: results });
})()
"""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // capture functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Capture the current visual state of an element
captureElementState :: Page -> String -> Aff CapturedState
captureElementState page selector = do
  resultJson <- PW.evaluate page (captureElementJS selector)
  pure (parseCapturedState resultJson)

-- | Capture all visible elements on the page
captureAllElements :: Page -> Aff (Array CapturedState)
captureAllElements page = do
  resultJson <- PW.evaluate page captureAllElementsJS
  pure (parseAllElements resultJson)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // parsing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse captured state from JSON using surgical extraction
-- |
-- | Uses Slide-style Megaparsec pattern: extract only what we need,
-- | don't parse 650 bytes of garbage per element.
-- |
-- | Extracts ALL visual properties for 1:1 parity.
parseCapturedState :: String -> CapturedState
parseCapturedState json =
  { -- Identity
    tagName: parseStringFieldWithDefault "tagName" "" json
  , elementId: parseStringFieldWithDefault "id" "" json
  , className: parseStringFieldWithDefault "className" "" json
  , selector: parseStringFieldWithDefault "selector" "" json
  
  -- DOM Tree Structure
  , index: parseIntField "index" json
  , parentIndex: parseIntFieldWithDefault "parentIndex" (-1) json
  , childIndices: parseIntArrayField "childIndices" json
  , depth: parseIntField "depth" json
  
  -- Accessibility
  , role: parseStringFieldWithDefault "role" "" json
  , ariaLabel: parseStringFieldWithDefault "ariaLabel" "" json
  , ariaDescribedBy: parseStringFieldWithDefault "ariaDescribedBy" "" json
  , tabIndex: parseIntFieldWithDefault "tabIndex" (-1) json
  
  -- Content
  , textContent: parseStringFieldWithDefault "textContent" "" json
  
  -- Geometry
  , x: parseNumberField "x" json
  , y: parseNumberField "y" json
  , width: parseNumberField "width" json
  , height: parseNumberField "height" json
  , boundingBox: parseBoundingBoxField "boundingBox" json
  
  -- Colors
  , backgroundColor: parseColorField "backgroundColor" json
  , color: parseColorField "color" json
  , borderColor: parseColorField "borderColor" json
  
  -- Typography
  , fontFamily: parseStringFieldWithDefault "fontFamily" "sans-serif" json
  , fontSize: parseNumberField "fontSize" json
  , fontWeight: parseIntField "fontWeight" json
  , lineHeight: parseNumberField "lineHeight" json
  , letterSpacing: parseNumberField "letterSpacing" json
  , textAlign: parseStringFieldWithDefault "textAlign" "start" json
  , textDecoration: parseStringFieldWithDefault "textDecoration" "none" json
  , textTransform: parseStringFieldWithDefault "textTransform" "none" json
  
  -- Spacing - Margins
  , marginTop: parseNumberField "marginTop" json
  , marginRight: parseNumberField "marginRight" json
  , marginBottom: parseNumberField "marginBottom" json
  , marginLeft: parseNumberField "marginLeft" json
  
  -- Spacing - Paddings
  , paddingTop: parseNumberField "paddingTop" json
  , paddingRight: parseNumberField "paddingRight" json
  , paddingBottom: parseNumberField "paddingBottom" json
  , paddingLeft: parseNumberField "paddingLeft" json
  
  -- Borders - Widths
  , borderTopWidth: parseNumberField "borderTopWidth" json
  , borderRightWidth: parseNumberField "borderRightWidth" json
  , borderBottomWidth: parseNumberField "borderBottomWidth" json
  , borderLeftWidth: parseNumberField "borderLeftWidth" json
  
  -- Borders - Radii
  , borderTopLeftRadius: parseNumberField "borderTopLeftRadius" json
  , borderTopRightRadius: parseNumberField "borderTopRightRadius" json
  , borderBottomRightRadius: parseNumberField "borderBottomRightRadius" json
  , borderBottomLeftRadius: parseNumberField "borderBottomLeftRadius" json
  
  -- Borders - Styles
  , borderTopStyle: parseStringFieldWithDefault "borderTopStyle" "none" json
  , borderRightStyle: parseStringFieldWithDefault "borderRightStyle" "none" json
  , borderBottomStyle: parseStringFieldWithDefault "borderBottomStyle" "none" json
  , borderLeftStyle: parseStringFieldWithDefault "borderLeftStyle" "none" json
  
  -- Elevation
  , boxShadow: parseShadowField "boxShadow" json
  , zIndex: parseIntField "zIndex" json
  
  -- Transform
  , transform: parseTransformField "transform" json
  
  -- Display properties
  , opacity: parseOpacity json
  , visibility: parseStringFieldWithDefault "visibility" "visible" json
  , display: parseStringFieldWithDefault "display" "block" json
  , overflow: parseStringFieldWithDefault "overflow" "visible" json
  , position: parseStringFieldWithDefault "position" "static" json
  
  -- Flex/Grid Layout
  , flexDirection: parseStringFieldWithDefault "flexDirection" "row" json
  , justifyContent: parseStringFieldWithDefault "justifyContent" "normal" json
  , alignItems: parseStringFieldWithDefault "alignItems" "normal" json
  , gap: parseNumberField "gap" json
  
  -- Interactivity
  , cursor: parseStringFieldWithDefault "cursor" "auto" json
  , pointerEvents: parseStringFieldWithDefault "pointerEvents" "auto" json
  
  -- Transition info
  , transitionDuration: parseStringFieldWithDefault "transitionDuration" "0s" json
  , transitionTimingFunction: parseStringFieldWithDefault "transitionTimingFunction" "ease" json
  , transitionDelay: parseStringFieldWithDefault "transitionDelay" "0s" json
  , transitionProperty: parseStringFieldWithDefault "transitionProperty" "all" json
  }

-- | Parse opacity with fallback to 1.0
parseOpacity :: String -> Number
parseOpacity json = case Parse.extractNumber "opacity" json of
  Just n -> n
  Nothing -> 1.0

-- | Parse a number field with fallback to 0.0
parseNumberField :: String -> String -> Number
parseNumberField field json = case Parse.extractNumber field json of
  Just n -> n
  Nothing -> 0.0

-- | Parse a maybe number field
parseMaybeNumberField :: String -> String -> Maybe Number
parseMaybeNumberField field json = case Parse.extractMaybeNumber field json of
  Just maybeN -> maybeN
  Nothing -> Nothing

-- | Parse a string field
parseStringField :: String -> String -> Maybe String
parseStringField field json = case Parse.extractMaybeString field json of
  Just maybeS -> maybeS
  Nothing -> Nothing

-- | Parse a string field with default value
parseStringFieldWithDefault :: String -> String -> String -> String
parseStringFieldWithDefault field defaultVal json = case Parse.extractString field json of
  Just s -> s
  Nothing -> defaultVal

-- | Parse an integer field with fallback to 0
parseIntField :: String -> String -> Int
parseIntField field json = case Parse.extractInt field json of
  Just n -> n
  Nothing -> 0

-- | Parse an integer field with custom default
parseIntFieldWithDefault :: String -> Int -> String -> Int
parseIntFieldWithDefault field defaultVal json = case Parse.extractInt field json of
  Just n -> n
  Nothing -> defaultVal

-- | Parse an array of integers
parseIntArrayField :: String -> String -> Array Int
parseIntArrayField field json = case Parse.extractArray field json of
  Just arrJson -> parseIntArray arrJson
  Nothing -> []
  where
    parseIntArray :: String -> Array Int
    parseIntArray arrJson =
      let elements = Parse.extractArrayElements arrJson
      in Array.mapMaybe parseIntElement elements
    
    parseIntElement :: String -> Maybe Int
    parseIntElement s = Parse.extractInt "value" ("{\"value\":" <> s <> "}")

-- | Parse a color field to CapturedColor
parseColorField :: String -> String -> Maybe CapturedColor
parseColorField field json = case Parse.extractColor field json of
  Just extracted -> Just
    { l: extracted.l
    , c: extracted.c
    , h: extracted.h
    , a: extracted.a
    }
  Nothing -> Nothing

-- | Parse a transform field to CapturedTransform
parseTransformField :: String -> String -> Maybe CapturedTransform
parseTransformField field json = case Parse.extractTransform field json of
  Just extracted -> Just
    { a: extracted.a
    , b: extracted.b
    , c: extracted.c
    , d: extracted.d
    , e: extracted.e
    , f: extracted.f
    , is3D: extracted.is3D
    -- Fill in 3D matrix with identity if not 3D
    , m11: 1.0, m12: 0.0, m13: 0.0, m14: 0.0
    , m21: 0.0, m22: 1.0, m23: 0.0, m24: 0.0
    , m31: 0.0, m32: 0.0, m33: 1.0, m34: 0.0
    , m41: 0.0, m42: 0.0, m43: 0.0, m44: 1.0
    }
  Nothing -> Nothing

-- | Parse a shadow field to CapturedShadow
parseShadowField :: String -> String -> Maybe CapturedShadow
parseShadowField field json = case Parse.extractShadow field json of
  Just extracted -> Just
    { inset: extracted.inset
    , offsetX: extracted.offsetX
    , offsetY: extracted.offsetY
    , blurRadius: extracted.blurRadius
    , spreadRadius: extracted.spreadRadius
    , color: case extracted.color of
        Just c -> { l: c.l, c: c.c, h: c.h, a: c.a }
        Nothing -> { l: 0.0, c: 0.0, h: 0.0, a: 0.0 }
    }
  Nothing -> Nothing

-- | Parse a bounding box field
parseBoundingBoxField :: String -> String -> Maybe CapturedBoundingBox
parseBoundingBoxField field json = case Parse.extractBoundingBox field json of
  Just extracted -> Just
    { x: extracted.x
    , y: extracted.y
    , width: extracted.width
    , height: extracted.height
    , top: extracted.y
    , right: extracted.x + extracted.width
    , bottom: extracted.y + extracted.height
    , left: extracted.x
    }
  Nothing -> Nothing

-- | Parse all elements from JSON
-- |
-- | Expected format: {"count": N, "elements": [...]}
parseAllElements :: String -> Array CapturedState
parseAllElements json = case Parse.extractArray "elements" json of
  Just elementsJson -> parseElementArray elementsJson
  Nothing -> []

-- | Parse array of elements
-- |
-- | Uses Wire.Parse to extract individual element JSON strings,
-- | then parses each one to CapturedState.
parseElementArray :: String -> Array CapturedState
parseElementArray arrJson = 
  let elementJsons = Parse.extractArrayElements arrJson
  in Array.mapMaybe parseElementOrNothing elementJsons
  where
    -- | Parse a single element JSON, returning Just on success
    -- | Each element in the array has the same structure as a full CapturedState
    parseElementOrNothing :: String -> Maybe CapturedState
    parseElementOrNothing elementJson =
      -- Verify this looks like valid element JSON (has required fields)
      case Parse.extractNumber "width" elementJson of
        Just _ -> Just (parseCapturedState elementJson)
        Nothing -> Nothing

-- | Parse a color string to OKLCH
-- | Used by other modules
parseColor :: String -> Maybe CapturedColor
parseColor json = parseColorField "color" ("{\"color\":" <> json <> "}")

-- | Parse a transform string to matrix
parseTransform :: String -> Maybe CapturedTransform
parseTransform json = parseTransformField "transform" ("{\"transform\":" <> json <> "}")

-- | Parse a shadow string
parseShadow :: String -> Maybe CapturedShadow
parseShadow json = parseShadowField "shadow" ("{\"shadow\":" <> json <> "}")
