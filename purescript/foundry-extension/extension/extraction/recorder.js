// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // foundry // extraction // recorder
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// 30-second screen recording with interaction testing.
// Systematically tests every interactive element for hover/click reactions.
//
// ARCHITECTURE:
//   1. Record initial state (instant snapshot)
//   2. Discover all interactive elements
//   3. Systematically hover each element, record reactions
//   4. Test keyboard focus states
//   5. Capture any triggered animations/effects
//   6. Build complete interaction map
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

import { PILLARS } from "./pillars.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // configuration
// ═══════════════════════════════════════════════════════════════════════════════

const CONFIG = {
  // Total recording duration (ms)
  recordingDuration: 30000,
  
  // Time to wait after hover before capturing state (ms)
  hoverSettleTime: 150,
  
  // Time between element tests (ms)
  interElementDelay: 50,
  
  // Maximum elements to test (performance limit)
  maxElementsToTest: 500,
  
  // Frames per second for state capture
  captureFramerate: 10,
  
  // Screenshot interval during recording
  screenshotInterval: 1000
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // state types
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Interaction state captured during hover/focus.
 */
class InteractionState {
  constructor(element, type) {
    this.element = element;
    this.type = type;  // "hover", "focus", "active"
    this.timestamp = performance.now();
    this.beforeStyles = null;
    this.afterStyles = null;
    this.animationsTriggered = [];
    this.transitionsTriggered = [];
    this.effectsDetected = [];
  }
}

/**
 * Complete recording session.
 */
class RecordingSession {
  constructor() {
    this.startTime = null;
    this.endTime = null;
    this.initialSnapshot = null;
    this.interactiveElements = [];
    this.hoverReactions = new Map();
    this.focusReactions = new Map();
    this.clickReactions = new Map();
    this.scrollReactions = [];
    this.animationsObserved = [];
    this.screenshots = [];
    this.frames = [];
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // main recorder
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Start a 30-second recording session.
 * 
 * @param {Function} onProgress - Progress callback (0-100)
 * @param {Function} onComplete - Completion callback with session data
 * @returns {Function} - Cancel function
 */
export async function startRecording(onProgress, onComplete) {
  const session = new RecordingSession();
  session.startTime = performance.now();
  
  let cancelled = false;
  
  // Phase 1: Initial snapshot
  onProgress(0, "Capturing initial snapshot...");
  session.initialSnapshot = await captureFullSnapshot();
  
  // Phase 2: Discover interactive elements
  onProgress(5, "Discovering interactive elements...");
  session.interactiveElements = discoverInteractiveElements();
  
  // Phase 3: Test hover reactions (bulk of time)
  const hoverProgress = await testHoverReactions(
    session,
    (progress) => onProgress(5 + progress * 0.6, `Testing hover reactions... (${Math.round(progress * 100)}%)`),
    () => cancelled
  );
  
  if (cancelled) return;
  
  // Phase 4: Test focus reactions
  onProgress(65, "Testing focus reactions...");
  await testFocusReactions(session, () => cancelled);
  
  if (cancelled) return;
  
  // Phase 5: Capture scroll-triggered animations
  onProgress(80, "Testing scroll triggers...");
  await testScrollReactions(session, () => cancelled);
  
  if (cancelled) return;
  
  // Phase 6: Observe any running animations
  onProgress(90, "Capturing active animations...");
  await captureActiveAnimations(session);
  
  // Phase 7: Final snapshot
  onProgress(95, "Capturing final state...");
  session.endTime = performance.now();
  
  // Compile results
  onProgress(100, "Processing results...");
  const results = compileSessionResults(session);
  
  onComplete(results);
  
  return () => { cancelled = true; };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // snapshot capture
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Capture full page snapshot with all pillar data.
 */
async function captureFullSnapshot() {
  const elements = document.querySelectorAll("*");
  const results = [];
  
  for (const el of elements) {
    const style = getComputedStyle(el);
    
    // Skip invisible
    if (style.display === "none" || style.visibility === "hidden") continue;
    if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
    
    // Extract all pillar data
    const elementData = {};
    for (const [pillarName, pillar] of Object.entries(PILLARS)) {
      if (pillar.detect(el)) {
        try {
          const extracted = pillar.extract(el, style);
          if (extracted !== null) {
            elementData[pillarName] = extracted;
          }
        } catch (e) {
          console.warn(`[Foundry] Failed to extract ${pillarName}:`, e);
        }
      }
    }
    
    if (Object.keys(elementData).length > 0) {
      results.push({
        selector: getSelector(el),
        pillars: elementData
      });
    }
  }
  
  return {
    timestamp: performance.now(),
    url: window.location.href,
    title: document.title,
    viewport: {
      width: window.innerWidth,
      height: window.innerHeight,
      scrollX: window.scrollX,
      scrollY: window.scrollY
    },
    elements: results
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                     // interactive discovery
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Discover all interactive elements on the page.
 */
function discoverInteractiveElements() {
  const elements = [];
  
  // Query all potentially interactive elements
  const selectors = [
    "a",
    "button",
    "input",
    "select",
    "textarea",
    "[role='button']",
    "[tabindex]",
    "[onclick]",
    "[data-action]",
    ".btn",
    ".button",
    "[class*='click']",
    "[class*='hover']",
    "[class*='interactive']"
  ];
  
  const candidates = document.querySelectorAll(selectors.join(", "));
  
  for (const el of candidates) {
    const style = getComputedStyle(el);
    
    // Skip invisible
    if (style.display === "none" || style.visibility === "hidden") continue;
    if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
    
    // Check for transitions/animations that might trigger on interaction
    const hasTransitions = style.transitionProperty !== "none";
    const hasHoverStyles = detectHoverStyles(el);
    
    elements.push({
      element: el,
      selector: getSelector(el),
      rect: el.getBoundingClientRect(),
      hasTransitions,
      hasHoverStyles,
      interactionType: classifyInteractionType(el)
    });
  }
  
  // Sort by visual prominence (larger, higher elements first)
  elements.sort((a, b) => {
    const aScore = (a.rect.width * a.rect.height) - a.rect.top;
    const bScore = (b.rect.width * b.rect.height) - b.rect.top;
    return bScore - aScore;
  });
  
  // Limit to max
  return elements.slice(0, CONFIG.maxElementsToTest);
}

/**
 * Detect if element has hover-specific styles defined.
 */
function detectHoverStyles(el) {
  // Check if any stylesheet has :hover rules for this element
  const sheets = document.styleSheets;
  
  for (const sheet of sheets) {
    try {
      const rules = sheet.cssRules || sheet.rules;
      for (const rule of rules) {
        if (rule.selectorText && rule.selectorText.includes(":hover")) {
          // Check if this rule might apply to our element
          const baseSelector = rule.selectorText.replace(/:hover/g, "");
          try {
            if (el.matches(baseSelector)) return true;
          } catch {
            // Invalid selector
          }
        }
      }
    } catch {
      // CORS restriction on stylesheet
    }
  }
  
  return false;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // hover testing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Test hover reactions for all interactive elements.
 */
async function testHoverReactions(session, onProgress, isCancelled) {
  const elements = session.interactiveElements;
  const total = elements.length;
  
  for (let i = 0; i < total; i++) {
    if (isCancelled()) return;
    
    const { element, selector } = elements[i];
    
    // Capture before state
    const beforeStyle = captureElementStyles(element);
    
    // Simulate hover
    const hoverState = await simulateHover(element);
    
    // Wait for transitions to settle
    await sleep(CONFIG.hoverSettleTime);
    
    // Capture after state
    const afterStyle = captureElementStyles(element);
    
    // Detect animations triggered
    const animationsTriggered = detectTriggeredAnimations(element);
    
    // Calculate differences
    const styleDiff = diffStyles(beforeStyle, afterStyle);
    
    if (Object.keys(styleDiff).length > 0 || animationsTriggered.length > 0) {
      session.hoverReactions.set(selector, {
        selector,
        beforeStyle,
        afterStyle,
        styleDiff,
        animationsTriggered,
        duration: CONFIG.hoverSettleTime
      });
    }
    
    // Remove hover
    await simulateHoverEnd(element);
    
    // Progress
    onProgress(i / total);
    
    // Brief delay between elements
    await sleep(CONFIG.interElementDelay);
  }
  
  return true;
}

/**
 * Simulate hover on element using mouseenter event.
 */
async function simulateHover(element) {
  const rect = element.getBoundingClientRect();
  const centerX = rect.left + rect.width / 2;
  const centerY = rect.top + rect.height / 2;
  
  // Dispatch mouse events
  element.dispatchEvent(new MouseEvent("mouseenter", {
    bubbles: true,
    cancelable: true,
    view: window,
    clientX: centerX,
    clientY: centerY
  }));
  
  element.dispatchEvent(new MouseEvent("mouseover", {
    bubbles: true,
    cancelable: true,
    view: window,
    clientX: centerX,
    clientY: centerY
  }));
  
  // Also try pointer events for modern handlers
  element.dispatchEvent(new PointerEvent("pointerenter", {
    bubbles: true,
    cancelable: true,
    view: window,
    clientX: centerX,
    clientY: centerY,
    pointerType: "mouse"
  }));
  
  return { centerX, centerY };
}

/**
 * End hover simulation.
 */
async function simulateHoverEnd(element) {
  element.dispatchEvent(new MouseEvent("mouseleave", {
    bubbles: true,
    cancelable: true,
    view: window
  }));
  
  element.dispatchEvent(new MouseEvent("mouseout", {
    bubbles: true,
    cancelable: true,
    view: window
  }));
  
  element.dispatchEvent(new PointerEvent("pointerleave", {
    bubbles: true,
    cancelable: true,
    view: window,
    pointerType: "mouse"
  }));
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // focus testing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Test focus reactions for focusable elements.
 */
async function testFocusReactions(session, isCancelled) {
  const focusable = session.interactiveElements.filter(({ element }) => {
    return element.tabIndex >= 0 || 
           ["a", "button", "input", "select", "textarea"].includes(element.tagName.toLowerCase());
  });
  
  for (const { element, selector } of focusable) {
    if (isCancelled()) return;
    
    // Capture before
    const beforeStyle = captureElementStyles(element);
    
    // Focus
    element.focus();
    await sleep(50);
    
    // Capture after
    const afterStyle = captureElementStyles(element);
    const focusVisible = element.matches(":focus-visible");
    
    // Diff
    const styleDiff = diffStyles(beforeStyle, afterStyle);
    
    if (Object.keys(styleDiff).length > 0 || focusVisible) {
      session.focusReactions.set(selector, {
        selector,
        beforeStyle,
        afterStyle,
        styleDiff,
        focusVisible
      });
    }
    
    // Blur
    element.blur();
    await sleep(CONFIG.interElementDelay);
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // scroll testing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Test scroll-triggered animations and effects.
 */
async function testScrollReactions(session, isCancelled) {
  const originalScrollY = window.scrollY;
  const maxScroll = document.documentElement.scrollHeight - window.innerHeight;
  const steps = 10;
  
  for (let i = 0; i <= steps; i++) {
    if (isCancelled()) return;
    
    const targetY = (maxScroll / steps) * i;
    window.scrollTo({ top: targetY, behavior: "instant" });
    
    await sleep(100);
    
    // Capture elements that became visible or animated
    const visibleAnimations = detectVisibleAnimations();
    
    if (visibleAnimations.length > 0) {
      session.scrollReactions.push({
        scrollY: targetY,
        scrollPercent: targetY / maxScroll,
        animations: visibleAnimations
      });
    }
  }
  
  // Restore scroll position
  window.scrollTo({ top: originalScrollY, behavior: "instant" });
}

/**
 * Detect animations currently visible in viewport.
 */
function detectVisibleAnimations() {
  const animations = [];
  const elements = document.querySelectorAll("*");
  
  for (const el of elements) {
    const rect = el.getBoundingClientRect();
    
    // Check if in viewport
    if (rect.bottom < 0 || rect.top > window.innerHeight) continue;
    
    // Check for running animations
    const elAnimations = el.getAnimations ? el.getAnimations() : [];
    for (const anim of elAnimations) {
      if (anim.playState === "running") {
        animations.push({
          selector: getSelector(el),
          animationName: anim.animationName || anim.id,
          currentTime: anim.currentTime,
          duration: anim.effect?.getTiming().duration
        });
      }
    }
  }
  
  return animations;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // animation capture
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Capture all currently active animations on the page.
 */
async function captureActiveAnimations(session) {
  const allAnimations = document.getAnimations ? document.getAnimations() : [];
  
  for (const anim of allAnimations) {
    const target = anim.effect?.target;
    if (!target) continue;
    
    const timing = anim.effect?.getTiming();
    const keyframes = anim.effect?.getKeyframes ? anim.effect.getKeyframes() : [];
    
    session.animationsObserved.push({
      selector: getSelector(target),
      id: anim.id,
      playState: anim.playState,
      currentTime: anim.currentTime,
      timing: timing ? {
        duration: timing.duration,
        iterations: timing.iterations,
        direction: timing.direction,
        easing: timing.easing,
        fill: timing.fill
      } : null,
      keyframes: keyframes.map(kf => ({
        offset: kf.offset,
        easing: kf.easing,
        composite: kf.composite,
        properties: Object.keys(kf).filter(k => !["offset", "easing", "composite"].includes(k))
      }))
    });
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // style capture
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Capture relevant styles for comparison.
 */
function captureElementStyles(element) {
  const style = getComputedStyle(element);
  
  // Properties that commonly change on interaction
  return {
    // Colors
    backgroundColor: style.backgroundColor,
    color: style.color,
    borderColor: style.borderColor,
    outlineColor: style.outlineColor,
    
    // Box model
    width: style.width,
    height: style.height,
    padding: style.padding,
    margin: style.margin,
    
    // Borders
    borderWidth: style.borderWidth,
    borderRadius: style.borderRadius,
    
    // Transform
    transform: style.transform,
    
    // Shadows
    boxShadow: style.boxShadow,
    textShadow: style.textShadow,
    
    // Opacity
    opacity: style.opacity,
    
    // Filters
    filter: style.filter,
    backdropFilter: style.backdropFilter,
    
    // Text
    textDecoration: style.textDecoration,
    letterSpacing: style.letterSpacing,
    
    // Cursor
    cursor: style.cursor,
    
    // Outline (focus indicator)
    outline: style.outline,
    outlineOffset: style.outlineOffset,
    
    // Scale (for hover zoom effects)
    scale: style.scale
  };
}

/**
 * Diff two style objects, returning only changed properties.
 */
function diffStyles(before, after) {
  const diff = {};
  
  for (const prop of Object.keys(before)) {
    if (before[prop] !== after[prop]) {
      diff[prop] = {
        from: before[prop],
        to: after[prop]
      };
    }
  }
  
  return diff;
}

/**
 * Detect animations that were triggered (started recently).
 */
function detectTriggeredAnimations(element) {
  const animations = element.getAnimations ? element.getAnimations() : [];
  
  return animations
    .filter(anim => anim.playState === "running" && anim.currentTime < 500)
    .map(anim => ({
      id: anim.id,
      name: anim.animationName,
      duration: anim.effect?.getTiming().duration,
      easing: anim.effect?.getTiming().easing
    }));
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // result compilation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Compile session data into final results.
 */
function compileSessionResults(session) {
  return {
    // Metadata
    url: session.initialSnapshot.url,
    title: session.initialSnapshot.title,
    duration: session.endTime - session.startTime,
    recordedAt: new Date().toISOString(),
    
    // Viewport
    viewport: session.initialSnapshot.viewport,
    
    // Static snapshot (all pillar data)
    snapshot: {
      elementCount: session.initialSnapshot.elements.length,
      elements: session.initialSnapshot.elements
    },
    
    // Interaction analysis
    interactions: {
      // Interactive element count
      interactiveElementCount: session.interactiveElements.length,
      
      // Hover reactions
      hoverReactions: Array.from(session.hoverReactions.values()).map(reaction => ({
        selector: reaction.selector,
        changes: Object.keys(reaction.styleDiff),
        styleDiff: reaction.styleDiff,
        animationsTriggered: reaction.animationsTriggered
      })),
      
      // Focus reactions
      focusReactions: Array.from(session.focusReactions.values()).map(reaction => ({
        selector: reaction.selector,
        focusVisible: reaction.focusVisible,
        changes: Object.keys(reaction.styleDiff),
        styleDiff: reaction.styleDiff
      })),
      
      // Scroll-triggered animations
      scrollAnimations: session.scrollReactions
    },
    
    // Active animations
    animations: {
      count: session.animationsObserved.length,
      animations: session.animationsObserved
    },
    
    // Summary statistics
    summary: {
      totalElements: session.initialSnapshot.elements.length,
      interactiveElements: session.interactiveElements.length,
      elementsWithHoverEffects: session.hoverReactions.size,
      elementsWithFocusEffects: session.focusReactions.size,
      activeAnimations: session.animationsObserved.length,
      scrollTriggeredAnimations: session.scrollReactions.reduce(
        (sum, sr) => sum + sr.animations.length, 0
      )
    }
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // utilities
// ═══════════════════════════════════════════════════════════════════════════════

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

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

function classifyInteractionType(el) {
  const tag = el.tagName.toLowerCase();
  
  if (tag === "a") return "link";
  if (tag === "button") return "button";
  if (tag === "input") return `input-${el.type || "text"}`;
  if (tag === "select") return "select";
  if (tag === "textarea") return "textarea";
  if (el.getAttribute("role") === "button") return "button-role";
  
  const style = getComputedStyle(el);
  if (style.cursor === "pointer") return "clickable";
  if (el.getAttribute("tabindex") !== null) return "focusable";
  
  return "unknown";
}
