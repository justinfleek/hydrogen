// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // foundry // extraction // pillars
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Full 38-pillar extraction from DOM elements.
// Maps every visual property to Hydrogen Schema atoms.
//
// ARCHITECTURE:
//   Phase 1: Instant Snapshot (static visual DNA)
//   Phase 2: 30-second Recording (interaction testing)
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // pillar definitions
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * The 38 Schema Pillars mapped to DOM extraction.
 * 
 * Each pillar defines:
 *   - extract: Function to extract from element/computedStyle
 *   - detect: Function to detect if pillar applies to this element
 */
export const PILLARS = {
  // ─────────────────────────────────────────────────────────────────────────────
  // VISUAL FOUNDATION (Static)
  // ─────────────────────────────────────────────────────────────────────────────
  
  color: {
    name: "Color",
    extract: extractColor,
    detect: () => true  // All elements have color properties
  },
  
  dimension: {
    name: "Dimension",
    extract: extractDimension,
    detect: () => true
  },
  
  geometry: {
    name: "Geometry",
    extract: extractGeometry,
    detect: () => true
  },
  
  typography: {
    name: "Typography",
    extract: extractTypography,
    detect: (el) => hasTextContent(el) || isTextElement(el)
  },
  
  surface: {
    name: "Surface",
    extract: extractSurface,
    detect: () => true
  },
  
  elevation: {
    name: "Elevation",
    extract: extractElevation,
    detect: () => true
  },
  
  // ─────────────────────────────────────────────────────────────────────────────
  // MOTION & ANIMATION
  // ─────────────────────────────────────────────────────────────────────────────
  
  motion: {
    name: "Motion",
    extract: extractMotion,
    detect: hasAnimations
  },
  
  temporal: {
    name: "Temporal",
    extract: extractTemporal,
    detect: hasTransitions
  },
  
  // ─────────────────────────────────────────────────────────────────────────────
  // INTERACTION
  // ─────────────────────────────────────────────────────────────────────────────
  
  reactive: {
    name: "Reactive",
    extract: extractReactive,
    detect: isInteractive
  },
  
  gestural: {
    name: "Gestural",
    extract: extractGestural,
    detect: isInteractive
  },
  
  haptic: {
    name: "Haptic",
    extract: extractHaptic,
    detect: () => false  // Requires device API
  },
  
  // ─────────────────────────────────────────────────────────────────────────────
  // MEDIA
  // ─────────────────────────────────────────────────────────────────────────────
  
  audio: {
    name: "Audio",
    extract: extractAudio,
    detect: isAudioElement
  },
  
  media: {
    name: "Media",
    extract: extractMedia,
    detect: isMediaElement
  },
  
  // ─────────────────────────────────────────────────────────────────────────────
  // SPATIAL & 3D
  // ─────────────────────────────────────────────────────────────────────────────
  
  spatial: {
    name: "Spatial",
    extract: extractSpatial,
    detect: has3DTransform
  },
  
  // ─────────────────────────────────────────────────────────────────────────────
  // SEMANTIC & IDENTITY
  // ─────────────────────────────────────────────────────────────────────────────
  
  brand: {
    name: "Brand",
    extract: extractBrand,
    detect: () => true  // Aggregate from other pillars
  },
  
  accessibility: {
    name: "Accessibility",
    extract: extractAccessibility,
    detect: () => true
  },
  
  navigation: {
    name: "Navigation",
    extract: extractNavigation,
    detect: isNavigationElement
  },
  
  identity: {
    name: "Identity",
    extract: extractIdentity,
    detect: () => true
  },
  
  // ─────────────────────────────────────────────────────────────────────────────
  // SEMANTIC BUTTON CLASSIFICATION
  // ─────────────────────────────────────────────────────────────────────────────
  
  element: {
    name: "Element",
    extract: extractElement,
    detect: () => true
  }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractColor(el, style) {
  return {
    background: parseColorToOKLCH(style.backgroundColor),
    foreground: parseColorToOKLCH(style.color),
    border: parseColorToOKLCH(style.borderColor),
    outline: parseColorToOKLCH(style.outlineColor),
    textDecoration: parseColorToOKLCH(style.textDecorationColor),
    caretColor: parseColorToOKLCH(style.caretColor),
    // Gradient detection
    gradient: parseGradient(style.backgroundImage),
    // Accent color (form elements)
    accent: parseColorToOKLCH(style.accentColor)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // dimension extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractDimension(el, style) {
  const rect = el.getBoundingClientRect();
  return {
    // Position (absolute, relative to viewport)
    x: rect.x,
    y: rect.y,
    
    // Size
    width: rect.width,
    height: rect.height,
    
    // Intrinsic size
    naturalWidth: el.naturalWidth || null,
    naturalHeight: el.naturalHeight || null,
    
    // Scroll dimensions
    scrollWidth: el.scrollWidth,
    scrollHeight: el.scrollHeight,
    
    // Computed box model
    boxSizing: style.boxSizing,
    
    // Aspect ratio
    aspectRatio: parseAspectRatio(style.aspectRatio),
    
    // Min/max constraints
    minWidth: parsePx(style.minWidth),
    maxWidth: parsePx(style.maxWidth),
    minHeight: parsePx(style.minHeight),
    maxHeight: parsePx(style.maxHeight),
    
    // Device pixel ratio context
    devicePixelRatio: window.devicePixelRatio
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // geometry extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractGeometry(el, style) {
  return {
    // Border radii
    borderTopLeftRadius: parsePx(style.borderTopLeftRadius),
    borderTopRightRadius: parsePx(style.borderTopRightRadius),
    borderBottomRightRadius: parsePx(style.borderBottomRightRadius),
    borderBottomLeftRadius: parsePx(style.borderBottomLeftRadius),
    
    // Clip path
    clipPath: style.clipPath,
    
    // Shape outside (for text wrapping)
    shapeOutside: style.shapeOutside,
    shapeMargin: parsePx(style.shapeMargin),
    
    // Object fit/position (for images/video)
    objectFit: style.objectFit,
    objectPosition: style.objectPosition,
    
    // Transform (2D/3D)
    transform: parseTransform(style.transform),
    transformOrigin: style.transformOrigin,
    
    // SVG-specific
    svgPath: el.tagName === "path" ? el.getAttribute("d") : null,
    svgViewBox: el.tagName === "svg" ? el.getAttribute("viewBox") : null
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                     // typography extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractTypography(el, style) {
  return {
    // Font family (full stack)
    fontFamily: style.fontFamily,
    
    // Size and weight
    fontSize: parsePx(style.fontSize),
    fontWeight: parseInt(style.fontWeight) || 400,
    fontStyle: style.fontStyle,
    
    // Line and letter spacing
    lineHeight: parsePx(style.lineHeight) || parsePx(style.fontSize) * 1.2,
    letterSpacing: parsePx(style.letterSpacing),
    wordSpacing: parsePx(style.wordSpacing),
    
    // Text alignment
    textAlign: style.textAlign,
    verticalAlign: style.verticalAlign,
    
    // Text decoration
    textDecoration: style.textDecoration,
    textDecorationLine: style.textDecorationLine,
    textDecorationStyle: style.textDecorationStyle,
    textDecorationThickness: parsePx(style.textDecorationThickness),
    
    // Text transform
    textTransform: style.textTransform,
    
    // Indentation and wrapping
    textIndent: parsePx(style.textIndent),
    whiteSpace: style.whiteSpace,
    wordBreak: style.wordBreak,
    overflowWrap: style.overflowWrap,
    hyphens: style.hyphens,
    
    // Font features
    fontVariantNumeric: style.fontVariantNumeric,
    fontVariantLigatures: style.fontVariantLigatures,
    fontFeatureSettings: style.fontFeatureSettings,
    fontVariationSettings: style.fontVariationSettings,
    
    // Text content
    textContent: getDirectText(el)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // surface extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractSurface(el, style) {
  return {
    // Background
    background: style.background,
    backgroundImage: style.backgroundImage,
    backgroundSize: style.backgroundSize,
    backgroundPosition: style.backgroundPosition,
    backgroundRepeat: style.backgroundRepeat,
    backgroundAttachment: style.backgroundAttachment,
    backgroundBlendMode: style.backgroundBlendMode,
    
    // Backdrop filter (glassmorphism)
    backdropFilter: style.backdropFilter,
    webkitBackdropFilter: style.webkitBackdropFilter,
    
    // Filter effects
    filter: style.filter,
    
    // Blend modes
    mixBlendMode: style.mixBlendMode,
    isolation: style.isolation,
    
    // Borders
    borderStyle: style.borderStyle,
    borderWidth: parsePx(style.borderWidth),
    borderImage: style.borderImage,
    
    // Outline
    outline: style.outline,
    outlineOffset: parsePx(style.outlineOffset),
    
    // Opacity
    opacity: parseFloat(style.opacity)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // elevation extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractElevation(el, style) {
  return {
    // Z-index stacking
    zIndex: parseZIndex(style.zIndex),
    
    // Box shadow (multiple shadows supported)
    boxShadow: parseBoxShadow(style.boxShadow),
    
    // Text shadow
    textShadow: parseTextShadow(style.textShadow),
    
    // Drop shadow filter
    dropShadow: parseDropShadowFilter(style.filter),
    
    // Position in stacking context
    position: style.position,
    
    // Creates stacking context?
    createsStackingContext: detectsStackingContext(el, style)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // motion extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractMotion(el, style) {
  const animations = el.getAnimations ? el.getAnimations() : [];
  
  return {
    // CSS Animations
    animationName: style.animationName,
    animationDuration: style.animationDuration,
    animationTimingFunction: style.animationTimingFunction,
    animationDelay: style.animationDelay,
    animationIterationCount: style.animationIterationCount,
    animationDirection: style.animationDirection,
    animationFillMode: style.animationFillMode,
    animationPlayState: style.animationPlayState,
    
    // Web Animations API
    webAnimations: animations.map(anim => ({
      id: anim.id,
      playState: anim.playState,
      currentTime: anim.currentTime,
      effect: anim.effect ? {
        duration: anim.effect.getTiming().duration,
        iterations: anim.effect.getTiming().iterations,
        easing: anim.effect.getTiming().easing
      } : null
    })),
    
    // Lottie detection
    lottie: detectLottie(el),
    
    // GSAP detection
    gsap: detectGSAP(el),
    
    // Motion path
    offsetPath: style.offsetPath,
    offsetDistance: style.offsetDistance,
    offsetRotate: style.offsetRotate
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // temporal extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractTemporal(el, style) {
  return {
    // CSS Transitions
    transitionProperty: style.transitionProperty,
    transitionDuration: style.transitionDuration,
    transitionTimingFunction: style.transitionTimingFunction,
    transitionDelay: style.transitionDelay,
    
    // Will-change hints
    willChange: style.willChange,
    
    // Contain (performance optimization)
    contain: style.contain,
    contentVisibility: style.contentVisibility
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // reactive extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractReactive(el, style) {
  return {
    // Interaction states (current)
    cursor: style.cursor,
    pointerEvents: style.pointerEvents,
    userSelect: style.userSelect,
    touchAction: style.touchAction,
    
    // Focus indicators
    focusVisible: el.matches(":focus-visible"),
    
    // Scroll behavior
    overflowX: style.overflowX,
    overflowY: style.overflowY,
    scrollBehavior: style.scrollBehavior,
    scrollSnapType: style.scrollSnapType,
    scrollSnapAlign: style.scrollSnapAlign,
    
    // Resize behavior
    resize: style.resize,
    
    // Interactive element classification
    interactionType: classifyInteractionType(el)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // gestural extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractGestural(el, style) {
  return {
    // Touch/pointer targets
    touchAction: style.touchAction,
    
    // Draggable
    draggable: el.draggable,
    
    // Keyboard interaction
    tabIndex: el.tabIndex,
    accessKey: el.accessKey,
    
    // Gesture hints
    gestureTarget: detectGestureTarget(el)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // haptic extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractHaptic(el, style) {
  // Haptic feedback is device-dependent, extract hints
  return {
    // Vibration hints from attributes
    vibrationPattern: el.dataset?.hapticPattern || null,
    
    // Force touch support (Safari)
    webkitForce: null  // Requires event
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // audio extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractAudio(el, style) {
  if (!isAudioElement(el)) return null;
  
  return {
    src: el.src || null,
    currentTime: el.currentTime,
    duration: el.duration,
    volume: el.volume,
    muted: el.muted,
    loop: el.loop,
    autoplay: el.autoplay,
    controls: el.controls,
    preload: el.preload
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // media extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractMedia(el, style) {
  const tag = el.tagName.toLowerCase();
  
  if (tag === "img") {
    return {
      type: "image",
      src: el.src,
      alt: el.alt,
      naturalWidth: el.naturalWidth,
      naturalHeight: el.naturalHeight,
      loading: el.loading,
      decoding: el.decoding,
      srcset: el.srcset,
      sizes: el.sizes
    };
  }
  
  if (tag === "video") {
    return {
      type: "video",
      src: el.src,
      poster: el.poster,
      width: el.videoWidth,
      height: el.videoHeight,
      duration: el.duration,
      currentTime: el.currentTime,
      playbackRate: el.playbackRate,
      muted: el.muted,
      loop: el.loop,
      autoplay: el.autoplay,
      controls: el.controls
    };
  }
  
  if (tag === "canvas") {
    return {
      type: "canvas",
      width: el.width,
      height: el.height,
      contextType: detectCanvasContext(el)
    };
  }
  
  if (tag === "iframe") {
    return {
      type: "iframe",
      src: el.src,
      srcdoc: el.srcdoc ? "[has srcdoc]" : null,
      sandbox: el.sandbox?.value || null
    };
  }
  
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // spatial extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractSpatial(el, style) {
  return {
    // 3D transforms
    perspective: parsePx(style.perspective),
    perspectiveOrigin: style.perspectiveOrigin,
    transformStyle: style.transformStyle,
    backfaceVisibility: style.backfaceVisibility,
    
    // Transform 3D components
    transform3D: parse3DTransform(style.transform)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // brand extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractBrand(el, style) {
  // Brand is an aggregate of other pillars, extracted at page level
  return {
    // Logo detection
    isLogo: detectLogo(el),
    
    // Primary CTA detection
    isPrimaryCTA: detectPrimaryCTA(el),
    
    // Brand color usage
    usesBrandColor: detectBrandColorUsage(el, style)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                   // accessibility extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractAccessibility(el, style) {
  return {
    // ARIA attributes
    role: el.getAttribute("role") || getImplicitRole(el),
    ariaLabel: el.getAttribute("aria-label"),
    ariaDescribedBy: el.getAttribute("aria-describedby"),
    ariaLabelledBy: el.getAttribute("aria-labelledby"),
    ariaHidden: el.getAttribute("aria-hidden") === "true",
    ariaDisabled: el.getAttribute("aria-disabled") === "true",
    ariaExpanded: el.getAttribute("aria-expanded"),
    ariaPressed: el.getAttribute("aria-pressed"),
    ariaSelected: el.getAttribute("aria-selected"),
    ariaCurrent: el.getAttribute("aria-current"),
    ariaLive: el.getAttribute("aria-live"),
    ariaAtomic: el.getAttribute("aria-atomic"),
    
    // Tab order
    tabIndex: el.tabIndex,
    
    // Focus visible
    isFocusable: isFocusable(el),
    
    // Alt text (images)
    alt: el.alt || null,
    
    // Form labels
    labels: el.labels ? Array.from(el.labels).map(l => l.textContent) : null
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                     // navigation extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractNavigation(el, style) {
  const tag = el.tagName.toLowerCase();
  
  if (tag === "a") {
    return {
      type: "link",
      href: el.href,
      target: el.target,
      rel: el.rel,
      download: el.download || null,
      isExternal: isExternalLink(el),
      isAnchor: el.href.includes("#")
    };
  }
  
  if (tag === "button" || el.getAttribute("role") === "button") {
    return {
      type: "button",
      buttonType: el.type || "button",
      disabled: el.disabled,
      formAction: el.formAction || null,
      semanticType: classifyButtonType(el)
    };
  }
  
  if (tag === "nav") {
    return {
      type: "nav",
      navType: classifyNavType(el)
    };
  }
  
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // identity extraction
// ═══════════════════════════════════════════════════════════════════════════════

async function extractIdentity(el, style) {
  const selector = getSelector(el);
  
  return {
    // Deterministic UUID5
    uuid: await uuid5(selector),
    
    // DOM identity
    tagName: el.tagName.toLowerCase(),
    id: el.id || null,
    className: el.className || null,
    selector: selector,
    
    // Data attributes
    dataset: { ...el.dataset },
    
    // Custom element
    isCustomElement: el.tagName.includes("-")
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // element extraction
// ═══════════════════════════════════════════════════════════════════════════════

function extractElement(el, style) {
  return {
    // Tag and semantic role
    tagName: el.tagName.toLowerCase(),
    semanticRole: getSemanticRole(el),
    
    // Button classification
    buttonType: classifyButtonType(el),
    
    // Content type
    contentType: classifyContentType(el),
    
    // Layout role
    layoutRole: classifyLayoutRole(el, style),
    
    // Interactive state
    isInteractive: isInteractive(el),
    isDisabled: el.disabled || el.getAttribute("aria-disabled") === "true",
    isHidden: style.display === "none" || style.visibility === "hidden",
    
    // Form element specifics
    formElement: extractFormElement(el)
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                     // button classification
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Classify button semantic type based on content and context.
 * 
 * Types:
 *   - play: Plays media (video, audio)
 *   - pause: Pauses media
 *   - cta: Call to action (links to other sections, sign up, etc.)
 *   - submit: Form submission
 *   - close: Closes modal/dialog
 *   - menu: Opens menu
 *   - toggle: Toggles state
 *   - nav: Navigation (prev/next)
 *   - action: Generic action button
 */
function classifyButtonType(el) {
  const tag = el.tagName.toLowerCase();
  if (tag !== "button" && tag !== "a" && el.getAttribute("role") !== "button") {
    return null;
  }
  
  const text = (el.textContent || "").toLowerCase().trim();
  const ariaLabel = (el.getAttribute("aria-label") || "").toLowerCase();
  const title = (el.title || "").toLowerCase();
  const className = (el.className || "").toLowerCase();
  const combinedText = `${text} ${ariaLabel} ${title} ${className}`;
  
  // Media controls
  if (hasPlayIndicator(el) || /\bplay\b/.test(combinedText)) {
    return "play";
  }
  if (hasPauseIndicator(el) || /\bpause\b/.test(combinedText)) {
    return "pause";
  }
  if (/\b(stop|halt)\b/.test(combinedText)) {
    return "stop";
  }
  if (/\b(mute|unmute|volume)\b/.test(combinedText)) {
    return "volume";
  }
  if (/\b(fullscreen|expand)\b/.test(combinedText)) {
    return "fullscreen";
  }
  
  // Close/dismiss
  if (/\b(close|dismiss|×|✕|x)\b/.test(combinedText) || hasCloseIcon(el)) {
    return "close";
  }
  
  // Menu
  if (/\b(menu|hamburger|≡|☰)\b/.test(combinedText) || hasHamburgerIcon(el)) {
    return "menu";
  }
  
  // Navigation
  if (/\b(previous|prev|back|←|‹)\b/.test(combinedText)) {
    return "nav-prev";
  }
  if (/\b(next|forward|→|›)\b/.test(combinedText)) {
    return "nav-next";
  }
  
  // CTA detection
  if (tag === "a" || el.closest("a")) {
    if (/\b(sign.?up|register|subscribe|join|get.?started|try|buy|shop|learn.?more|read.?more|download|contact)\b/.test(combinedText)) {
      return "cta-primary";
    }
    return "cta-link";
  }
  
  // Form submission
  if (el.type === "submit" || /\b(submit|send|save|confirm|ok|done)\b/.test(combinedText)) {
    return "submit";
  }
  
  // Reset
  if (el.type === "reset" || /\b(reset|clear|cancel)\b/.test(combinedText)) {
    return "reset";
  }
  
  // Toggle
  if (el.getAttribute("aria-pressed") !== null || /\b(toggle|switch)\b/.test(combinedText)) {
    return "toggle";
  }
  
  // Expand/collapse
  if (el.getAttribute("aria-expanded") !== null || /\b(expand|collapse|show|hide)\b/.test(combinedText)) {
    return "expand";
  }
  
  // Share
  if (/\b(share|tweet|post)\b/.test(combinedText)) {
    return "share";
  }
  
  // Search
  if (/\b(search|find)\b/.test(combinedText) || el.type === "search") {
    return "search";
  }
  
  // Edit
  if (/\b(edit|modify|change)\b/.test(combinedText)) {
    return "edit";
  }
  
  // Delete
  if (/\b(delete|remove|trash)\b/.test(combinedText)) {
    return "delete";
  }
  
  // Add
  if (/\b(add|create|new|\+)\b/.test(combinedText)) {
    return "add";
  }
  
  // Generic action
  return "action";
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // helper functions
// ═══════════════════════════════════════════════════════════════════════════════

function hasPlayIndicator(el) {
  // Check for play icon (triangle)
  const svg = el.querySelector("svg");
  if (svg) {
    const path = svg.querySelector("path");
    if (path) {
      const d = path.getAttribute("d") || "";
      // Common play icon path patterns
      if (/M\s*\d+[\s,]+\d+[\s,]*L[\s,]*\d+/.test(d)) return true;
    }
  }
  // Check for play emoji/unicode
  if (/[▶►▷▸▹]/.test(el.textContent)) return true;
  return false;
}

function hasPauseIndicator(el) {
  const svg = el.querySelector("svg");
  if (svg) {
    const rects = svg.querySelectorAll("rect");
    if (rects.length === 2) return true;  // Two bars = pause
  }
  if (/[⏸❚❚║]/.test(el.textContent)) return true;
  return false;
}

function hasCloseIcon(el) {
  const svg = el.querySelector("svg");
  if (svg) {
    const paths = svg.querySelectorAll("path, line");
    // X pattern: two crossing lines
    if (paths.length === 2) return true;
  }
  if (/[×✕✖✗✘]/.test(el.textContent)) return true;
  return false;
}

function hasHamburgerIcon(el) {
  const svg = el.querySelector("svg");
  if (svg) {
    const lines = svg.querySelectorAll("line, rect, path");
    // Three horizontal lines
    if (lines.length === 3) return true;
  }
  if (/[≡☰]/.test(el.textContent)) return true;
  return false;
}

function isInteractive(el) {
  const tag = el.tagName.toLowerCase();
  const interactiveTags = ["a", "button", "input", "select", "textarea", "details", "summary"];
  if (interactiveTags.includes(tag)) return true;
  if (el.getAttribute("role") === "button") return true;
  if (el.getAttribute("tabindex") !== null) return true;
  if (el.onclick || el.getAttribute("onclick")) return true;
  return false;
}

function hasTextContent(el) {
  return el.textContent && el.textContent.trim().length > 0;
}

function isTextElement(el) {
  const tag = el.tagName.toLowerCase();
  return ["p", "h1", "h2", "h3", "h4", "h5", "h6", "span", "label", "a", "li", "td", "th", "caption", "figcaption", "blockquote", "cite", "q", "pre", "code"].includes(tag);
}

function isAudioElement(el) {
  return el.tagName.toLowerCase() === "audio";
}

function isMediaElement(el) {
  const tag = el.tagName.toLowerCase();
  return ["img", "video", "audio", "canvas", "iframe", "svg", "picture"].includes(tag);
}

function isNavigationElement(el) {
  const tag = el.tagName.toLowerCase();
  if (["a", "button", "nav"].includes(tag)) return true;
  if (el.getAttribute("role") === "button") return true;
  return false;
}

function hasAnimations(el) {
  if (el.getAnimations && el.getAnimations().length > 0) return true;
  const style = getComputedStyle(el);
  if (style.animationName && style.animationName !== "none") return true;
  return false;
}

function hasTransitions(el) {
  const style = getComputedStyle(el);
  return style.transitionProperty && style.transitionProperty !== "none";
}

function has3DTransform(el) {
  const style = getComputedStyle(el);
  const transform = style.transform;
  if (!transform || transform === "none") return false;
  return /matrix3d|rotate[XYZ]|translate[Z3]|scale[Z3]|perspective/.test(transform);
}

function isFocusable(el) {
  if (el.disabled) return false;
  if (el.tabIndex < 0) return false;
  const tag = el.tagName.toLowerCase();
  if (["a", "button", "input", "select", "textarea"].includes(tag)) return true;
  if (el.tabIndex >= 0) return true;
  return false;
}

function isExternalLink(el) {
  if (el.tagName.toLowerCase() !== "a") return false;
  try {
    const url = new URL(el.href);
    return url.host !== window.location.host;
  } catch {
    return false;
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // color conversion
// ═══════════════════════════════════════════════════════════════════════════════

// Imported from content.js - parseColorToOKLCH
function parseColorToOKLCH(colorStr) {
  if (!colorStr || colorStr === "transparent" || colorStr === "rgba(0, 0, 0, 0)") {
    return null;
  }

  const match = colorStr.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?\)/);
  if (!match) return null;

  const r = parseInt(match[1]) / 255;
  const g = parseInt(match[2]) / 255;
  const b = parseInt(match[3]) / 255;
  const a = match[4] ? parseFloat(match[4]) : 1;

  const toLinear = (c) => c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
  const lr = toLinear(r), lg = toLinear(g), lb = toLinear(b);

  const x = 0.4124564 * lr + 0.3575761 * lg + 0.1804375 * lb;
  const y = 0.2126729 * lr + 0.7151522 * lg + 0.0721750 * lb;
  const z = 0.0193339 * lr + 0.1191920 * lg + 0.9503041 * lb;

  const l_ = Math.cbrt(0.8189330101 * x + 0.3618667424 * y - 0.1288597137 * z);
  const m_ = Math.cbrt(0.0329845436 * x + 0.9293118715 * y + 0.0361456387 * z);
  const s_ = Math.cbrt(0.0482003018 * x + 0.2643662691 * y + 0.6338517070 * z);

  const L = 0.2104542553 * l_ + 0.7936177850 * m_ - 0.0040720468 * s_;
  const A = 1.9779984951 * l_ - 2.4285922050 * m_ + 0.4505937099 * s_;
  const B = 0.0259040371 * l_ + 0.7827717662 * m_ - 0.8086757660 * s_;

  const C = Math.sqrt(A * A + B * B);
  let H = Math.atan2(B, A) * 180 / Math.PI;
  if (H < 0) H += 360;

  return { l: L, c: C, h: H, a: a };
}

function parsePx(str) {
  if (!str) return 0;
  const match = str.match(/([\d.]+)px/);
  return match ? parseFloat(match[1]) : 0;
}

function parseZIndex(str) {
  if (!str || str === "auto") return 0;
  const num = parseInt(str);
  return isNaN(num) ? 0 : num;
}

function parseTransform(transformStr) {
  if (!transformStr || transformStr === "none") {
    return { type: "identity" };
  }

  const matrix2d = transformStr.match(
    /matrix\(([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+),\s*([\d.\-e]+)\)/
  );
  if (matrix2d) {
    return {
      type: "matrix2d",
      a: parseFloat(matrix2d[1]), b: parseFloat(matrix2d[2]),
      c: parseFloat(matrix2d[3]), d: parseFloat(matrix2d[4]),
      e: parseFloat(matrix2d[5]), f: parseFloat(matrix2d[6])
    };
  }

  const matrix3d = transformStr.match(/matrix3d\(([\d.\-e,\s]+)\)/);
  if (matrix3d) {
    const vals = matrix3d[1].split(",").map(v => parseFloat(v.trim()));
    return { type: "matrix3d", values: vals };
  }

  return { type: "unknown", raw: transformStr };
}

function parse3DTransform(transformStr) {
  if (!transformStr || transformStr === "none") return null;
  
  const result = {
    translateX: 0, translateY: 0, translateZ: 0,
    rotateX: 0, rotateY: 0, rotateZ: 0,
    scaleX: 1, scaleY: 1, scaleZ: 1,
    perspective: null
  };
  
  // Parse individual functions
  const translate3d = transformStr.match(/translate3d\(([\d.\-]+)px,\s*([\d.\-]+)px,\s*([\d.\-]+)px\)/);
  if (translate3d) {
    result.translateX = parseFloat(translate3d[1]);
    result.translateY = parseFloat(translate3d[2]);
    result.translateZ = parseFloat(translate3d[3]);
  }
  
  const rotateX = transformStr.match(/rotateX\(([\d.\-]+)deg\)/);
  if (rotateX) result.rotateX = parseFloat(rotateX[1]);
  
  const rotateY = transformStr.match(/rotateY\(([\d.\-]+)deg\)/);
  if (rotateY) result.rotateY = parseFloat(rotateY[1]);
  
  const rotateZ = transformStr.match(/rotateZ\(([\d.\-]+)deg\)/);
  if (rotateZ) result.rotateZ = parseFloat(rotateZ[1]);
  
  return result;
}

function parseBoxShadow(shadowStr) {
  if (!shadowStr || shadowStr === "none") return [];
  
  // Split multiple shadows
  const shadows = [];
  let current = "";
  let parenDepth = 0;
  
  for (const char of shadowStr) {
    if (char === "(") parenDepth++;
    if (char === ")") parenDepth--;
    if (char === "," && parenDepth === 0) {
      if (current.trim()) shadows.push(parseSingleShadow(current.trim()));
      current = "";
    } else {
      current += char;
    }
  }
  if (current.trim()) shadows.push(parseSingleShadow(current.trim()));
  
  return shadows.filter(s => s !== null);
}

function parseSingleShadow(shadowStr) {
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

function parseTextShadow(shadowStr) {
  if (!shadowStr || shadowStr === "none") return [];
  // Similar to box-shadow but without spread
  const shadows = [];
  // Simplified parsing
  const parts = shadowStr.split(",").map(s => s.trim());
  for (const part of parts) {
    const rgbMatch = part.match(/rgba?\([^)]+\)/);
    const colorStr = rgbMatch ? rgbMatch[0] : "rgb(0, 0, 0)";
    const nums = part.replace(/rgba?\([^)]+\)/, "").match(/-?[\d.]+px/g);
    if (nums && nums.length >= 2) {
      shadows.push({
        offsetX: parseFloat(nums[0]),
        offsetY: parseFloat(nums[1]),
        blurRadius: nums[2] ? parseFloat(nums[2]) : 0,
        color: parseColorToOKLCH(colorStr)
      });
    }
  }
  return shadows;
}

function parseDropShadowFilter(filterStr) {
  if (!filterStr || !filterStr.includes("drop-shadow")) return null;
  const match = filterStr.match(/drop-shadow\(([^)]+)\)/);
  if (!match) return null;
  return parseSingleShadow(match[1]);
}

function parseGradient(bgImage) {
  if (!bgImage || bgImage === "none") return null;
  
  const linearMatch = bgImage.match(/linear-gradient\(([^)]+)\)/);
  if (linearMatch) {
    return { type: "linear", raw: linearMatch[1] };
  }
  
  const radialMatch = bgImage.match(/radial-gradient\(([^)]+)\)/);
  if (radialMatch) {
    return { type: "radial", raw: radialMatch[1] };
  }
  
  const conicMatch = bgImage.match(/conic-gradient\(([^)]+)\)/);
  if (conicMatch) {
    return { type: "conic", raw: conicMatch[1] };
  }
  
  return null;
}

function parseAspectRatio(ratioStr) {
  if (!ratioStr || ratioStr === "auto") return null;
  const parts = ratioStr.split("/").map(s => parseFloat(s.trim()));
  if (parts.length === 2 && !isNaN(parts[0]) && !isNaN(parts[1])) {
    return { width: parts[0], height: parts[1] };
  }
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // semantic detection
// ═══════════════════════════════════════════════════════════════════════════════

function getImplicitRole(el) {
  const tag = el.tagName.toLowerCase();
  const implicitRoles = {
    a: el.href ? "link" : null,
    article: "article",
    aside: "complementary",
    button: "button",
    footer: "contentinfo",
    form: "form",
    h1: "heading", h2: "heading", h3: "heading",
    h4: "heading", h5: "heading", h6: "heading",
    header: "banner",
    img: el.alt ? "img" : "presentation",
    input: getInputRole(el),
    li: "listitem",
    main: "main",
    nav: "navigation",
    ol: "list",
    option: "option",
    progress: "progressbar",
    section: "region",
    select: "listbox",
    table: "table",
    textarea: "textbox",
    ul: "list"
  };
  return implicitRoles[tag] || null;
}

function getInputRole(el) {
  const type = el.type || "text";
  const inputRoles = {
    button: "button",
    checkbox: "checkbox",
    email: "textbox",
    image: "button",
    number: "spinbutton",
    radio: "radio",
    range: "slider",
    reset: "button",
    search: "searchbox",
    submit: "button",
    tel: "textbox",
    text: "textbox",
    url: "textbox"
  };
  return inputRoles[type] || "textbox";
}

function getSemanticRole(el) {
  return el.getAttribute("role") || getImplicitRole(el);
}

function classifyContentType(el) {
  const tag = el.tagName.toLowerCase();
  
  if (["p", "span", "label", "blockquote", "cite", "q"].includes(tag)) return "text";
  if (["h1", "h2", "h3", "h4", "h5", "h6"].includes(tag)) return "heading";
  if (["ul", "ol", "li"].includes(tag)) return "list";
  if (["table", "thead", "tbody", "tr", "td", "th"].includes(tag)) return "table";
  if (["form", "input", "select", "textarea", "button"].includes(tag)) return "form";
  if (["img", "picture", "figure"].includes(tag)) return "image";
  if (["video", "audio"].includes(tag)) return "media";
  if (["nav"].includes(tag)) return "navigation";
  if (["header", "footer", "main", "article", "section", "aside"].includes(tag)) return "landmark";
  if (["div", "span"].includes(tag)) return "container";
  
  return "unknown";
}

function classifyLayoutRole(el, style) {
  const display = style.display;
  
  if (display === "flex") return "flex-container";
  if (display === "inline-flex") return "inline-flex-container";
  if (display === "grid") return "grid-container";
  if (display === "inline-grid") return "inline-grid-container";
  if (display === "block") return "block";
  if (display === "inline") return "inline";
  if (display === "inline-block") return "inline-block";
  if (display === "none") return "hidden";
  
  return display;
}

function classifyInteractionType(el) {
  const tag = el.tagName.toLowerCase();
  
  if (tag === "a") return "link";
  if (tag === "button") return "button";
  if (tag === "input") return `input-${el.type || "text"}`;
  if (tag === "select") return "select";
  if (tag === "textarea") return "textarea";
  if (el.getAttribute("role") === "button") return "button-role";
  if (el.getAttribute("tabindex") !== null) return "focusable";
  if (style.cursor === "pointer") return "clickable";
  
  return null;
}

function classifyNavType(el) {
  const text = el.textContent.toLowerCase();
  if (el.querySelector("a[href='#']") || /breadcrumb/i.test(el.className)) return "breadcrumb";
  if (/pagination|page/i.test(el.className)) return "pagination";
  if (/tab/i.test(el.className)) return "tabs";
  if (/social/i.test(el.className)) return "social";
  if (/footer/i.test(el.className)) return "footer";
  if (el.closest("header")) return "header";
  if (el.closest("aside")) return "sidebar";
  return "main";
}

function detectLogo(el) {
  const tag = el.tagName.toLowerCase();
  if (tag !== "img" && tag !== "svg") return false;
  
  const src = el.src || "";
  const className = el.className || "";
  const id = el.id || "";
  const alt = el.alt || "";
  
  const combined = `${src} ${className} ${id} ${alt}`.toLowerCase();
  return /logo|brand|icon/.test(combined);
}

function detectPrimaryCTA(el) {
  const className = (el.className || "").toLowerCase();
  const text = (el.textContent || "").toLowerCase().trim();
  
  // Check for primary CTA patterns
  if (/btn.?primary|button.?primary|cta.?primary|primary.?cta/.test(className)) return true;
  if (/get.?started|sign.?up|try.?free|start.?now|buy.?now/.test(text)) return true;
  
  return false;
}

function detectBrandColorUsage(el, style) {
  // This would compare against extracted brand colors
  // For now, return indicator that this needs brand context
  return null;
}

function detectsStackingContext(el, style) {
  // Elements that create stacking context
  if (style.position !== "static" && style.zIndex !== "auto") return true;
  if (parseFloat(style.opacity) < 1) return true;
  if (style.transform !== "none") return true;
  if (style.filter !== "none") return true;
  if (style.perspective !== "none") return true;
  if (style.clipPath !== "none") return true;
  if (style.mask !== "none") return true;
  if (style.isolation === "isolate") return true;
  if (style.mixBlendMode !== "normal") return true;
  if (style.willChange !== "auto") return true;
  if (style.contain === "layout" || style.contain === "paint" || style.contain === "strict" || style.contain === "content") return true;
  return false;
}

function detectGestureTarget(el) {
  const style = getComputedStyle(el);
  if (style.touchAction === "none") return "none";
  if (style.touchAction === "pan-x") return "horizontal-scroll";
  if (style.touchAction === "pan-y") return "vertical-scroll";
  if (style.touchAction === "pinch-zoom") return "pinch-zoom";
  if (el.draggable) return "draggable";
  return null;
}

function extractFormElement(el) {
  const tag = el.tagName.toLowerCase();
  if (!["input", "select", "textarea", "button"].includes(tag)) return null;
  
  return {
    type: el.type || tag,
    name: el.name || null,
    value: el.value || null,
    placeholder: el.placeholder || null,
    required: el.required,
    disabled: el.disabled,
    readonly: el.readOnly,
    pattern: el.pattern || null,
    min: el.min || null,
    max: el.max || null,
    step: el.step || null,
    options: tag === "select" ? Array.from(el.options).map(o => ({ value: o.value, text: o.text, selected: o.selected })) : null
  };
}

function detectCanvasContext(el) {
  try {
    if (el.getContext("webgl2")) return "webgl2";
    if (el.getContext("webgl")) return "webgl";
    if (el.getContext("2d")) return "2d";
  } catch {
    return "unknown";
  }
  return "unknown";
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // lottie detection
// ═══════════════════════════════════════════════════════════════════════════════

function detectLottie(el) {
  // Check for common Lottie container patterns
  if (el.querySelector("lottie-player")) {
    return { type: "lottie-player", container: true };
  }
  
  if (el.classList.contains("lottie") || el.dataset.lottie) {
    return { type: "lottie-web", src: el.dataset.lottie || null };
  }
  
  // Check for dotLottie
  if (el.querySelector("dotlottie-player")) {
    return { type: "dotlottie", container: true };
  }
  
  // Check for Bodymovin
  if (el.classList.contains("bodymovin")) {
    return { type: "bodymovin", container: true };
  }
  
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // gsap detection
// ═══════════════════════════════════════════════════════════════════════════════

function detectGSAP(el) {
  // Check for GSAP data attributes
  if (el.dataset.gsap || el.dataset.scrollTrigger) {
    return { hasGsap: true, scrollTrigger: !!el.dataset.scrollTrigger };
  }
  
  // Check if element has _gsap property (runtime)
  if (el._gsap) {
    return { hasGsap: true, active: true };
  }
  
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // uuid5 helper
// ═══════════════════════════════════════════════════════════════════════════════

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

function getDirectText(el) {
  let text = "";
  for (const node of el.childNodes) {
    if (node.nodeType === Node.TEXT_NODE) {
      text += node.textContent;
    }
  }
  return text.trim().slice(0, 500);
}
