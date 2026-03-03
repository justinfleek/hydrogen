// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // foundry // extension // content
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Content script that extracts visual DNA from any page.
// Runs in the page context, has full DOM access.
// Outputs Hydrogen Schema atoms (bounded, OKLCH colors).
//
// ARCHITECTURE:
//   1. Listen for extraction request from popup/background
//   2. Extract all computed styles from DOM
//   3. Convert colors to OKLCH (perceptual uniformity)
//   4. Build z-indexed layer stack
//   5. Send results back to extension
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color conversion
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Convert CSS color string to OKLCH components.
 * 
 * OKLCH provides perceptual uniformity - equal numeric distances
 * produce equal perceived color differences. Essential for brand
 * extraction where color relationships must be preserved.
 * 
 * @param {string} colorStr - CSS color value (rgb, rgba, hex, named)
 * @returns {Object|null} - { l: 0-1, c: 0-0.4, h: 0-360, a: 0-1 } or null if transparent
 */
function parseColorToOKLCH(colorStr) {
  if (!colorStr || colorStr === "transparent" || colorStr === "rgba(0, 0, 0, 0)") {
    return null;
  }

  // Parse rgba/rgb from computed style (always returns rgb/rgba format)
  const match = colorStr.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?\)/);
  if (!match) return null;

  const r = parseInt(match[1]) / 255;
  const g = parseInt(match[2]) / 255;
  const b = parseInt(match[3]) / 255;
  const a = match[4] ? parseFloat(match[4]) : 1;

  // sRGB to linear RGB (inverse gamma)
  const toLinear = (c) => c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
  const lr = toLinear(r), lg = toLinear(g), lb = toLinear(b);

  // Linear RGB to XYZ (D65 illuminant)
  const x = 0.4124564 * lr + 0.3575761 * lg + 0.1804375 * lb;
  const y = 0.2126729 * lr + 0.7151522 * lg + 0.0721750 * lb;
  const z = 0.0193339 * lr + 0.1191920 * lg + 0.9503041 * lb;

  // XYZ to Oklab (via LMS cone response)
  const l_ = Math.cbrt(0.8189330101 * x + 0.3618667424 * y - 0.1288597137 * z);
  const m_ = Math.cbrt(0.0329845436 * x + 0.9293118715 * y + 0.0361456387 * z);
  const s_ = Math.cbrt(0.0482003018 * x + 0.2643662691 * y + 0.6338517070 * z);

  // Oklab L, a, b
  const L = 0.2104542553 * l_ + 0.7936177850 * m_ - 0.0040720468 * s_;
  const A = 1.9779984951 * l_ - 2.4285922050 * m_ + 0.4505937099 * s_;
  const B = 0.0259040371 * l_ + 0.7827717662 * m_ - 0.8086757660 * s_;

  // Oklab to OKLCH (polar form)
  const C = Math.sqrt(A * A + B * B);
  let H = Math.atan2(B, A) * 180 / Math.PI;
  if (H < 0) H += 360;

  return { l: L, c: C, h: H, a: a };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // css parsing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Parse CSS pixel value to number.
 * @param {string} str - CSS value like "16px"
 * @returns {number} - Numeric value (0 if unparseable)
 */
function parsePx(str) {
  if (!str) return 0;
  const match = str.match(/([\d.]+)px/);
  return match ? parseFloat(match[1]) : 0;
}

/**
 * Parse font-weight (handles both numeric and keyword values).
 * @param {string} str - CSS font-weight value
 * @returns {number} - Weight as integer 100-900
 */
function parseFontWeight(str) {
  if (!str) return 400;
  const num = parseInt(str);
  if (!isNaN(num)) return num;
  
  const weights = {
    thin: 100, hairline: 100,
    extralight: 200, ultralight: 200,
    light: 300,
    normal: 400, regular: 400,
    medium: 500,
    semibold: 600, demibold: 600,
    bold: 700,
    extrabold: 800, ultrabold: 800,
    black: 900, heavy: 900
  };
  return weights[str.toLowerCase()] || 400;
}

/**
 * Parse z-index (handles "auto" and numeric).
 * @param {string} str - CSS z-index value
 * @returns {number} - Integer z-index (0 for "auto")
 */
function parseZIndex(str) {
  if (!str || str === "auto") return 0;
  const num = parseInt(str);
  return isNaN(num) ? 0 : num;
}

/**
 * Parse CSS transform to matrix components.
 * Decomposes matrix(a,b,c,d,e,f) or matrix3d() to individual values.
 * 
 * @param {string} transformStr - CSS transform value
 * @returns {Object} - { a, b, c, d, e, f, is3D } matrix components
 */
function parseTransform(transformStr) {
  if (!transformStr || transformStr === "none") {
    return { a: 1, b: 0, c: 0, d: 1, e: 0, f: 0, is3D: false };
  }

  // 2D matrix: matrix(a, b, c, d, e, f)
  const matrix2d = transformStr.match(
    /matrix\(([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+)\)/
  );
  if (matrix2d) {
    return {
      is3D: false,
      a: parseFloat(matrix2d[1]), b: parseFloat(matrix2d[2]),
      c: parseFloat(matrix2d[3]), d: parseFloat(matrix2d[4]),
      e: parseFloat(matrix2d[5]), f: parseFloat(matrix2d[6])
    };
  }

  // 3D matrix: matrix3d(16 values)
  const matrix3d = transformStr.match(/matrix3d\(([\d.\-e,\s]+)\)/);
  if (matrix3d) {
    const vals = matrix3d[1].split(",").map(v => parseFloat(v.trim()));
    return {
      is3D: true,
      a: vals[0], b: vals[1], c: vals[4], d: vals[5], e: vals[12], f: vals[13]
    };
  }

  return { a: 1, b: 0, c: 0, d: 1, e: 0, f: 0, is3D: false };
}

/**
 * Parse box-shadow to components.
 * @param {string} shadowStr - CSS box-shadow value
 * @returns {Object|null} - Shadow components or null if none
 */
function parseBoxShadow(shadowStr) {
  if (!shadowStr || shadowStr === "none") return null;

  const inset = shadowStr.includes("inset");
  let colorStr = "rgb(0, 0, 0)";
  const rgbMatch = shadowStr.match(/rgba?\([^)]+\)/);
  if (rgbMatch) colorStr = rgbMatch[0];

  const nums = shadowStr.replace(/rgba?\([^)]+\)/, "").match(/-?[\d.]+px/g);
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

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // selector generation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Generate a unique CSS selector for an element.
 * Uses ID if available, otherwise builds nth-of-type path.
 * 
 * @param {Element} el - DOM element
 * @returns {string} - Unique CSS selector
 */
function getSelector(el) {
  if (el.id) return "#" + CSS.escape(el.id);

  const path = [];
  let current = el;
  while (current && current.nodeType === Node.ELEMENT_NODE) {
    let selector = current.tagName.toLowerCase();
    if (current.id) {
      selector = "#" + CSS.escape(current.id);
      path.unshift(selector);
      break;
    } else {
      let sibling = current.previousElementSibling;
      let nth = 1;
      while (sibling) {
        if (sibling.tagName === current.tagName) nth++;
        sibling = sibling.previousElementSibling;
      }
      if (nth > 1) selector += ":nth-of-type(" + nth + ")";
    }
    path.unshift(selector);
    current = current.parentElement;
  }
  return path.join(" > ");
}

/**
 * Get direct text content of element (not children).
 * @param {Element} el - DOM element
 * @returns {string} - Direct text content (trimmed, max 500 chars)
 */
function getDirectText(el) {
  let text = "";
  for (const node of el.childNodes) {
    if (node.nodeType === Node.TEXT_NODE) {
      text += node.textContent;
    }
  }
  return text.trim().slice(0, 500);
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // uuid5 implementation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Generate UUID5 from namespace and name.
 * Deterministic - same input always produces same UUID.
 * 
 * Uses SHA-1 hash (as per UUID5 spec).
 * Namespace: "foundry.layer" → 6ba7b810-9dad-11d1-80b4-00c04fd430c8
 * 
 * @param {string} name - Input string to hash
 * @returns {string} - UUID5 string
 */
async function uuid5(name) {
  // Foundry namespace UUID (derived from URL namespace)
  const NAMESPACE = "6ba7b810-9dad-11d1-80b4-00c04fd430c8";
  
  // Convert namespace UUID to bytes
  const namespaceBytes = new Uint8Array(16);
  const hex = NAMESPACE.replace(/-/g, "");
  for (let i = 0; i < 16; i++) {
    namespaceBytes[i] = parseInt(hex.substr(i * 2, 2), 16);
  }
  
  // Combine namespace + name
  const encoder = new TextEncoder();
  const nameBytes = encoder.encode(name);
  const combined = new Uint8Array(namespaceBytes.length + nameBytes.length);
  combined.set(namespaceBytes);
  combined.set(nameBytes, namespaceBytes.length);
  
  // SHA-1 hash
  const hashBuffer = await crypto.subtle.digest("SHA-1", combined);
  const hashArray = new Uint8Array(hashBuffer);
  
  // Format as UUID5 (set version and variant bits)
  hashArray[6] = (hashArray[6] & 0x0f) | 0x50; // Version 5
  hashArray[8] = (hashArray[8] & 0x3f) | 0x80; // Variant 1
  
  // Convert to hex string with dashes
  const hexChars = [];
  for (let i = 0; i < 16; i++) {
    hexChars.push(hashArray[i].toString(16).padStart(2, "0"));
  }
  return [
    hexChars.slice(0, 4).join(""),
    hexChars.slice(4, 6).join(""),
    hexChars.slice(6, 8).join(""),
    hexChars.slice(8, 10).join(""),
    hexChars.slice(10, 16).join("")
  ].join("-");
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // main extraction
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Extract all visible elements from the current page.
 * 
 * Returns an array of CapturedState objects with:
 * - All visual properties (colors as OKLCH, dimensions as pixels)
 * - DOM tree structure (parent/child indices)
 * - Accessibility info (role, aria-label)
 * - Transition/animation timing
 * 
 * @returns {Promise<Object>} - { count, elements, layers, url, title }
 */
async function extractAllElements() {
  const elements = document.querySelectorAll("*");
  const results = [];

  // Build element-to-index map for parent tracking
  const elementArray = Array.from(elements);
  const elementToIndex = new Map();
  let idx = 0;
  for (const el of elementArray) {
    elementToIndex.set(el, idx++);
  }

  for (const el of elementArray) {
    const style = getComputedStyle(el);
    
    // Skip invisible elements
    if (style.display === "none" || style.visibility === "hidden") continue;
    if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;

    const rect = el.getBoundingClientRect();
    
    // Skip elements outside viewport (optimization)
    if (rect.bottom < 0 || rect.top > window.innerHeight * 2) continue;

    // Find parent index
    const parent = el.parentElement;
    const parentIndex = parent ? (elementToIndex.get(parent) ?? -1) : -1;

    // Get child indices
    const childIndices = [];
    for (const child of el.children) {
      const childIdx = elementToIndex.get(child);
      if (childIdx !== undefined) childIndices.push(childIdx);
    }

    // Generate deterministic UUID5 from selector
    const selector = getSelector(el);
    const layerId = await uuid5(selector);

    results.push({
      // Identity
      tagName: el.tagName,
      elementId: el.id || "",
      className: typeof el.className === "string" ? el.className : "",
      selector: selector,
      layerId: layerId,

      // DOM Tree Structure
      index: elementToIndex.get(el),
      parentIndex: parentIndex,
      childIndices: childIndices,
      depth: selector.split(" > ").length,

      // Accessibility
      role: el.getAttribute("role") || el.tagName.toLowerCase(),
      ariaLabel: el.getAttribute("aria-label") || "",
      ariaDescribedBy: el.getAttribute("aria-describedby") || "",
      tabIndex: el.tabIndex,

      // Content
      textContent: getDirectText(el),

      // Geometry (pixels, relative to viewport)
      x: rect.x,
      y: rect.y,
      width: rect.width,
      height: rect.height,
      boundingBox: {
        x: rect.x, y: rect.y, width: rect.width, height: rect.height,
        top: rect.top, right: rect.right, bottom: rect.bottom, left: rect.left
      },

      // Colors (OKLCH - perceptually uniform)
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

  // Group by z-index to form layers
  const layerMap = new Map();
  for (const el of results) {
    const z = el.zIndex;
    if (!layerMap.has(z)) {
      layerMap.set(z, []);
    }
    layerMap.get(z).push(el);
  }

  // Sort layers by z-index
  const layers = Array.from(layerMap.entries())
    .sort((a, b) => a[0] - b[0])
    .map(([zIndex, elements]) => ({ zIndex, elements, count: elements.length }));

  return {
    url: window.location.href,
    title: document.title,
    viewportWidth: window.innerWidth,
    viewportHeight: window.innerHeight,
    count: results.length,
    elements: results,
    layers: layers,
    layerCount: layers.length
  };
}

/**
 * Capture screenshot of current viewport.
 * Uses html2canvas if available, otherwise returns null.
 * 
 * @returns {Promise<string|null>} - Data URL of screenshot or null
 */
async function captureScreenshot() {
  // Check if html2canvas is available (injected by extension)
  if (typeof html2canvas === "function") {
    try {
      const canvas = await html2canvas(document.body, {
        useCORS: true,
        allowTaint: true,
        scale: window.devicePixelRatio
      });
      return canvas.toDataURL("image/png");
    } catch (e) {
      console.error("Screenshot capture failed:", e);
      return null;
    }
  }
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // message handling
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Listen for messages from popup/background script.
 */
chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
  if (request.action === "extract") {
    // Extract all elements and send back
    extractAllElements().then(result => {
      sendResponse({ success: true, data: result });
    }).catch(err => {
      sendResponse({ success: false, error: err.message });
    });
    return true; // Indicates async response
  }

  if (request.action === "screenshot") {
    // Capture screenshot
    captureScreenshot().then(dataUrl => {
      sendResponse({ success: true, data: dataUrl });
    }).catch(err => {
      sendResponse({ success: false, error: err.message });
    });
    return true;
  }

  if (request.action === "ping") {
    // Health check
    sendResponse({ success: true, ready: true });
    return false;
  }
});

// Signal that content script is loaded
console.log("[Foundry] Content script loaded");
