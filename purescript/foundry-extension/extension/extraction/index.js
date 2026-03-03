// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // foundry // extraction // index
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Main extraction orchestrator.
// Coordinates between instant snapshot, interaction recording, and analysis.
//
// USAGE:
//   1. instantSnapshot() - Quick static capture of all visual DNA
//   2. fullRecording() - 30-second interaction testing and animation capture
//   3. analyze() - Process results into brand atoms
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

import { PILLARS } from "./pillars.js";
import { startRecording } from "./recorder.js";
import { extractAllLottieAnimations } from "./lottie.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // instant snapshot
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Capture instant snapshot of all visual DNA.
 * 
 * This is the quick static capture - no interaction testing.
 * Use for:
 *   - Initial page analysis
 *   - A:B comparison baseline
 *   - Quick brand extraction
 * 
 * @returns {Promise<Object>} - Full snapshot with all pillar data
 */
export async function instantSnapshot() {
  const startTime = performance.now();
  
  // Capture screenshot via canvas
  const screenshot = await captureScreenshot();
  
  // Extract all elements with pillar data
  const elements = await extractAllElements();
  
  // Extract Lottie animations
  const lottieAnimations = extractAllLottieAnimations();
  
  // Group by z-index for layer view
  const layers = groupByZIndex(elements);
  
  // Extract brand summary
  const brandSummary = extractBrandSummary(elements);
  
  const endTime = performance.now();
  
  return {
    type: "snapshot",
    timestamp: new Date().toISOString(),
    duration: endTime - startTime,
    
    // Page metadata
    url: window.location.href,
    title: document.title,
    viewport: {
      width: window.innerWidth,
      height: window.innerHeight,
      devicePixelRatio: window.devicePixelRatio,
      scrollX: window.scrollX,
      scrollY: window.scrollY
    },
    
    // Screenshot
    screenshot: screenshot,
    
    // Full element extraction
    elements: {
      count: elements.length,
      data: elements
    },
    
    // Z-index layers
    layers: {
      count: layers.length,
      data: layers
    },
    
    // Lottie animations
    lottie: {
      count: lottieAnimations.length,
      animations: lottieAnimations
    },
    
    // Brand summary
    brand: brandSummary
  };
}

/**
 * Extract all visible elements with full pillar data.
 */
async function extractAllElements() {
  const elements = document.querySelectorAll("*");
  const results = [];
  
  // Build element-to-index map for tree structure
  const elementArray = Array.from(elements);
  const elementToIndex = new Map();
  elementArray.forEach((el, idx) => elementToIndex.set(el, idx));
  
  for (const el of elementArray) {
    const style = getComputedStyle(el);
    
    // Skip invisible
    if (style.display === "none" || style.visibility === "hidden") continue;
    if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
    
    // Skip elements far outside viewport (performance)
    const rect = el.getBoundingClientRect();
    if (rect.bottom < -1000 || rect.top > window.innerHeight + 1000) continue;
    
    // Extract all applicable pillar data
    const pillars = {};
    for (const [pillarName, pillar] of Object.entries(PILLARS)) {
      try {
        if (pillar.detect(el)) {
          const extracted = pillar.extract(el, style);
          if (extracted !== null && Object.keys(extracted).length > 0) {
            pillars[pillarName] = extracted;
          }
        }
      } catch (e) {
        // Skip failed extractions silently
      }
    }
    
    // Skip elements with no extractable data
    if (Object.keys(pillars).length === 0) continue;
    
    // Get tree structure
    const parent = el.parentElement;
    const parentIndex = parent ? (elementToIndex.get(parent) ?? -1) : -1;
    const childIndices = Array.from(el.children)
      .map(child => elementToIndex.get(child))
      .filter(idx => idx !== undefined);
    
    results.push({
      // Identity
      selector: getSelector(el),
      uuid: await uuid5(getSelector(el)),
      
      // Tree structure
      index: elementToIndex.get(el),
      parentIndex: parentIndex,
      childIndices: childIndices,
      depth: getSelector(el).split(" > ").length,
      
      // All pillar data
      pillars: pillars
    });
  }
  
  return results;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // full recording
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Start 30-second full recording with interaction testing.
 * 
 * This tests:
 *   - Hover states for all interactive elements
 *   - Focus states
 *   - Scroll-triggered animations
 *   - Active animations and their timing
 * 
 * @param {Function} onProgress - Progress callback (percent, message)
 * @returns {Promise<Object>} - Full recording results
 */
export async function fullRecording(onProgress = () => {}) {
  // Capture initial snapshot first
  onProgress(0, "Capturing initial snapshot...");
  const initialSnapshot = await instantSnapshot();
  
  // Start interaction recording
  return new Promise((resolve) => {
    startRecording(
      (percent, message) => onProgress(percent, message),
      (recordingResults) => {
        // Combine snapshot with recording
        resolve({
          type: "recording",
          timestamp: new Date().toISOString(),
          
          // Initial state
          initialSnapshot: initialSnapshot,
          
          // Interaction results
          interactions: recordingResults.interactions,
          
          // Animations
          animations: recordingResults.animations,
          
          // Combined summary
          summary: {
            ...recordingResults.summary,
            lottieAnimations: initialSnapshot.lottie.count,
            brandColors: initialSnapshot.brand.colors.length
          }
        });
      }
    );
  });
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // brand extraction
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Extract brand summary from elements.
 */
function extractBrandSummary(elements) {
  const colors = new Map();
  const fonts = new Map();
  const spacing = new Map();
  const buttons = [];
  
  for (const element of elements) {
    const pillars = element.pillars;
    
    // Collect colors
    if (pillars.color) {
      collectColor(colors, pillars.color.background, "background");
      collectColor(colors, pillars.color.foreground, "foreground");
      collectColor(colors, pillars.color.border, "border");
    }
    
    // Collect fonts
    if (pillars.typography?.fontFamily) {
      const family = pillars.typography.fontFamily;
      fonts.set(family, (fonts.get(family) || 0) + 1);
    }
    
    // Collect spacing patterns
    if (pillars.dimension) {
      const { width, height } = pillars.dimension;
      // Track common dimensions
      if (width > 0) spacing.set(`w:${Math.round(width)}`, (spacing.get(`w:${Math.round(width)}`) || 0) + 1);
      if (height > 0) spacing.set(`h:${Math.round(height)}`, (spacing.get(`h:${Math.round(height)}`) || 0) + 1);
    }
    
    // Collect buttons
    if (pillars.element?.buttonType) {
      buttons.push({
        selector: element.selector,
        type: pillars.element.buttonType,
        text: pillars.typography?.textContent?.slice(0, 50)
      });
    }
  }
  
  return {
    // Top colors by usage
    colors: Array.from(colors.entries())
      .sort((a, b) => b[1].count - a[1].count)
      .slice(0, 20)
      .map(([key, value]) => ({
        oklch: value.color,
        count: value.count,
        usage: value.usage
      })),
    
    // Top fonts by usage
    fonts: Array.from(fonts.entries())
      .sort((a, b) => b[1] - a[1])
      .slice(0, 10)
      .map(([family, count]) => ({ family, count })),
    
    // Button classification summary
    buttons: {
      total: buttons.length,
      byType: groupBy(buttons, b => b.type)
    }
  };
}

/**
 * Collect a color into the frequency map.
 */
function collectColor(map, oklch, usage) {
  if (!oklch) return;
  
  // Create a key from OKLCH values (rounded for grouping)
  const key = `${Math.round(oklch.l * 100)}-${Math.round(oklch.c * 100)}-${Math.round(oklch.h)}`;
  
  if (map.has(key)) {
    const entry = map.get(key);
    entry.count++;
    if (!entry.usage.includes(usage)) entry.usage.push(usage);
  } else {
    map.set(key, {
      color: oklch,
      count: 1,
      usage: [usage]
    });
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // layer grouping
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Group elements by z-index into layers.
 */
function groupByZIndex(elements) {
  const layerMap = new Map();
  
  for (const element of elements) {
    const zIndex = element.pillars.elevation?.zIndex || 0;
    
    if (!layerMap.has(zIndex)) {
      layerMap.set(zIndex, []);
    }
    layerMap.get(zIndex).push(element.selector);
  }
  
  return Array.from(layerMap.entries())
    .sort((a, b) => a[0] - b[0])
    .map(([zIndex, selectors]) => ({
      zIndex,
      count: selectors.length,
      selectors
    }));
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // screenshot capture
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Capture screenshot using html2canvas if available.
 */
async function captureScreenshot() {
  // Try html2canvas if available
  if (typeof html2canvas === "function") {
    try {
      const canvas = await html2canvas(document.body, {
        useCORS: true,
        allowTaint: true,
        scale: window.devicePixelRatio,
        logging: false
      });
      return canvas.toDataURL("image/png");
    } catch (e) {
      console.warn("[Foundry] Screenshot capture failed:", e);
    }
  }
  
  // Fallback: return null (screenshot will be captured by background script)
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // utilities
// ═══════════════════════════════════════════════════════════════════════════════

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

async function uuid5(name) {
  const NAMESPACE = "6ba7b810-9dad-11d1-80b4-00c04fd430c8";
  
  const namespaceBytes = new Uint8Array(16);
  const hex = NAMESPACE.replace(/-/g, "");
  for (let i = 0; i < 16; i++) {
    namespaceBytes[i] = parseInt(hex.substr(i * 2, 2), 16);
  }
  
  const encoder = new TextEncoder();
  const nameBytes = encoder.encode(name);
  const combined = new Uint8Array(namespaceBytes.length + nameBytes.length);
  combined.set(namespaceBytes);
  combined.set(nameBytes, namespaceBytes.length);
  
  const hashBuffer = await crypto.subtle.digest("SHA-1", combined);
  const hashArray = new Uint8Array(hashBuffer);
  
  hashArray[6] = (hashArray[6] & 0x0f) | 0x50;
  hashArray[8] = (hashArray[8] & 0x3f) | 0x80;
  
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

function groupBy(array, keyFn) {
  const result = {};
  for (const item of array) {
    const key = keyFn(item);
    if (!result[key]) result[key] = [];
    result[key].push(item);
  }
  return result;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // message handler
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Handle messages from extension popup/background.
 */
chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
  switch (request.action) {
    case "instantSnapshot":
      instantSnapshot()
        .then(result => sendResponse({ success: true, data: result }))
        .catch(err => sendResponse({ success: false, error: err.message }));
      return true;  // Async response
      
    case "fullRecording":
      fullRecording((percent, message) => {
        // Send progress updates
        chrome.runtime.sendMessage({
          type: "progress",
          percent,
          message
        });
      })
        .then(result => sendResponse({ success: true, data: result }))
        .catch(err => sendResponse({ success: false, error: err.message }));
      return true;
      
    case "extractLottie": {
      const lottieData = extractAllLottieAnimations();
      sendResponse({ success: true, data: lottieData });
      return false;
    }
      
    case "ping":
      sendResponse({ success: true, ready: true, version: "2.0.0" });
      return false;
  }
});

// Signal ready
console.log("[Foundry] Full extraction module loaded (v2.0.0)");
