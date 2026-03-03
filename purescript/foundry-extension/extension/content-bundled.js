"use strict";
(() => {
  // purescript/foundry-extension/extension/extraction/pillars.js
  var PILLARS = {
    // ─────────────────────────────────────────────────────────────────────────────
    // VISUAL FOUNDATION (Static)
    // ─────────────────────────────────────────────────────────────────────────────
    color: {
      name: "Color",
      extract: extractColor,
      detect: () => true
      // All elements have color properties
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
      detect: () => false
      // Requires device API
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
      detect: () => true
      // Aggregate from other pillars
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
  function extractColor(el, style2) {
    return {
      background: parseColorToOKLCH(style2.backgroundColor),
      foreground: parseColorToOKLCH(style2.color),
      border: parseColorToOKLCH(style2.borderColor),
      outline: parseColorToOKLCH(style2.outlineColor),
      textDecoration: parseColorToOKLCH(style2.textDecorationColor),
      caretColor: parseColorToOKLCH(style2.caretColor),
      // Gradient detection
      gradient: parseGradient(style2.backgroundImage),
      // Accent color (form elements)
      accent: parseColorToOKLCH(style2.accentColor)
    };
  }
  function extractDimension(el, style2) {
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
      boxSizing: style2.boxSizing,
      // Aspect ratio
      aspectRatio: parseAspectRatio(style2.aspectRatio),
      // Min/max constraints
      minWidth: parsePx(style2.minWidth),
      maxWidth: parsePx(style2.maxWidth),
      minHeight: parsePx(style2.minHeight),
      maxHeight: parsePx(style2.maxHeight),
      // Device pixel ratio context
      devicePixelRatio: window.devicePixelRatio
    };
  }
  function extractGeometry(el, style2) {
    return {
      // Border radii
      borderTopLeftRadius: parsePx(style2.borderTopLeftRadius),
      borderTopRightRadius: parsePx(style2.borderTopRightRadius),
      borderBottomRightRadius: parsePx(style2.borderBottomRightRadius),
      borderBottomLeftRadius: parsePx(style2.borderBottomLeftRadius),
      // Clip path
      clipPath: style2.clipPath,
      // Shape outside (for text wrapping)
      shapeOutside: style2.shapeOutside,
      shapeMargin: parsePx(style2.shapeMargin),
      // Object fit/position (for images/video)
      objectFit: style2.objectFit,
      objectPosition: style2.objectPosition,
      // Transform (2D/3D)
      transform: parseTransform(style2.transform),
      transformOrigin: style2.transformOrigin,
      // SVG-specific
      svgPath: el.tagName === "path" ? el.getAttribute("d") : null,
      svgViewBox: el.tagName === "svg" ? el.getAttribute("viewBox") : null
    };
  }
  function extractTypography(el, style2) {
    return {
      // Font family (full stack)
      fontFamily: style2.fontFamily,
      // Size and weight
      fontSize: parsePx(style2.fontSize),
      fontWeight: parseInt(style2.fontWeight) || 400,
      fontStyle: style2.fontStyle,
      // Line and letter spacing
      lineHeight: parsePx(style2.lineHeight) || parsePx(style2.fontSize) * 1.2,
      letterSpacing: parsePx(style2.letterSpacing),
      wordSpacing: parsePx(style2.wordSpacing),
      // Text alignment
      textAlign: style2.textAlign,
      verticalAlign: style2.verticalAlign,
      // Text decoration
      textDecoration: style2.textDecoration,
      textDecorationLine: style2.textDecorationLine,
      textDecorationStyle: style2.textDecorationStyle,
      textDecorationThickness: parsePx(style2.textDecorationThickness),
      // Text transform
      textTransform: style2.textTransform,
      // Indentation and wrapping
      textIndent: parsePx(style2.textIndent),
      whiteSpace: style2.whiteSpace,
      wordBreak: style2.wordBreak,
      overflowWrap: style2.overflowWrap,
      hyphens: style2.hyphens,
      // Font features
      fontVariantNumeric: style2.fontVariantNumeric,
      fontVariantLigatures: style2.fontVariantLigatures,
      fontFeatureSettings: style2.fontFeatureSettings,
      fontVariationSettings: style2.fontVariationSettings,
      // Text content
      textContent: getDirectText(el)
    };
  }
  function extractSurface(el, style2) {
    return {
      // Background
      background: style2.background,
      backgroundImage: style2.backgroundImage,
      backgroundSize: style2.backgroundSize,
      backgroundPosition: style2.backgroundPosition,
      backgroundRepeat: style2.backgroundRepeat,
      backgroundAttachment: style2.backgroundAttachment,
      backgroundBlendMode: style2.backgroundBlendMode,
      // Backdrop filter (glassmorphism)
      backdropFilter: style2.backdropFilter,
      webkitBackdropFilter: style2.webkitBackdropFilter,
      // Filter effects
      filter: style2.filter,
      // Blend modes
      mixBlendMode: style2.mixBlendMode,
      isolation: style2.isolation,
      // Borders
      borderStyle: style2.borderStyle,
      borderWidth: parsePx(style2.borderWidth),
      borderImage: style2.borderImage,
      // Outline
      outline: style2.outline,
      outlineOffset: parsePx(style2.outlineOffset),
      // Opacity
      opacity: parseFloat(style2.opacity)
    };
  }
  function extractElevation(el, style2) {
    return {
      // Z-index stacking
      zIndex: parseZIndex(style2.zIndex),
      // Box shadow (multiple shadows supported)
      boxShadow: parseBoxShadow(style2.boxShadow),
      // Text shadow
      textShadow: parseTextShadow(style2.textShadow),
      // Drop shadow filter
      dropShadow: parseDropShadowFilter(style2.filter),
      // Position in stacking context
      position: style2.position,
      // Creates stacking context?
      createsStackingContext: detectsStackingContext(el, style2)
    };
  }
  function extractMotion(el, style2) {
    const animations = el.getAnimations ? el.getAnimations() : [];
    return {
      // CSS Animations
      animationName: style2.animationName,
      animationDuration: style2.animationDuration,
      animationTimingFunction: style2.animationTimingFunction,
      animationDelay: style2.animationDelay,
      animationIterationCount: style2.animationIterationCount,
      animationDirection: style2.animationDirection,
      animationFillMode: style2.animationFillMode,
      animationPlayState: style2.animationPlayState,
      // Web Animations API
      webAnimations: animations.map((anim) => ({
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
      offsetPath: style2.offsetPath,
      offsetDistance: style2.offsetDistance,
      offsetRotate: style2.offsetRotate
    };
  }
  function extractTemporal(el, style2) {
    return {
      // CSS Transitions
      transitionProperty: style2.transitionProperty,
      transitionDuration: style2.transitionDuration,
      transitionTimingFunction: style2.transitionTimingFunction,
      transitionDelay: style2.transitionDelay,
      // Will-change hints
      willChange: style2.willChange,
      // Contain (performance optimization)
      contain: style2.contain,
      contentVisibility: style2.contentVisibility
    };
  }
  function extractReactive(el, style2) {
    return {
      // Interaction states (current)
      cursor: style2.cursor,
      pointerEvents: style2.pointerEvents,
      userSelect: style2.userSelect,
      touchAction: style2.touchAction,
      // Focus indicators
      focusVisible: el.matches(":focus-visible"),
      // Scroll behavior
      overflowX: style2.overflowX,
      overflowY: style2.overflowY,
      scrollBehavior: style2.scrollBehavior,
      scrollSnapType: style2.scrollSnapType,
      scrollSnapAlign: style2.scrollSnapAlign,
      // Resize behavior
      resize: style2.resize,
      // Interactive element classification
      interactionType: classifyInteractionType(el)
    };
  }
  function extractGestural(el, style2) {
    return {
      // Touch/pointer targets
      touchAction: style2.touchAction,
      // Draggable
      draggable: el.draggable,
      // Keyboard interaction
      tabIndex: el.tabIndex,
      accessKey: el.accessKey,
      // Gesture hints
      gestureTarget: detectGestureTarget(el)
    };
  }
  function extractHaptic(el, style2) {
    return {
      // Vibration hints from attributes
      vibrationPattern: el.dataset?.hapticPattern || null,
      // Force touch support (Safari)
      webkitForce: null
      // Requires event
    };
  }
  function extractAudio(el, style2) {
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
  function extractMedia(el, style2) {
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
  function extractSpatial(el, style2) {
    return {
      // 3D transforms
      perspective: parsePx(style2.perspective),
      perspectiveOrigin: style2.perspectiveOrigin,
      transformStyle: style2.transformStyle,
      backfaceVisibility: style2.backfaceVisibility,
      // Transform 3D components
      transform3D: parse3DTransform(style2.transform)
    };
  }
  function extractBrand(el, style2) {
    return {
      // Logo detection
      isLogo: detectLogo(el),
      // Primary CTA detection
      isPrimaryCTA: detectPrimaryCTA(el),
      // Brand color usage
      usesBrandColor: detectBrandColorUsage(el, style2)
    };
  }
  function extractAccessibility(el, style2) {
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
      labels: el.labels ? Array.from(el.labels).map((l) => l.textContent) : null
    };
  }
  function extractNavigation(el, style2) {
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
  async function extractIdentity(el, style2) {
    const selector = getSelector(el);
    return {
      // Deterministic UUID5
      uuid: await uuid5(selector),
      // DOM identity
      tagName: el.tagName.toLowerCase(),
      id: el.id || null,
      className: el.className || null,
      selector,
      // Data attributes
      dataset: { ...el.dataset },
      // Custom element
      isCustomElement: el.tagName.includes("-")
    };
  }
  function extractElement(el, style2) {
    return {
      // Tag and semantic role
      tagName: el.tagName.toLowerCase(),
      semanticRole: getSemanticRole(el),
      // Button classification
      buttonType: classifyButtonType(el),
      // Content type
      contentType: classifyContentType(el),
      // Layout role
      layoutRole: classifyLayoutRole(el, style2),
      // Interactive state
      isInteractive: isInteractive(el),
      isDisabled: el.disabled || el.getAttribute("aria-disabled") === "true",
      isHidden: style2.display === "none" || style2.visibility === "hidden",
      // Form element specifics
      formElement: extractFormElement(el)
    };
  }
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
    if (/\b(close|dismiss|×|✕|x)\b/.test(combinedText) || hasCloseIcon(el)) {
      return "close";
    }
    if (/\b(menu|hamburger|≡|☰)\b/.test(combinedText) || hasHamburgerIcon(el)) {
      return "menu";
    }
    if (/\b(previous|prev|back|←|‹)\b/.test(combinedText)) {
      return "nav-prev";
    }
    if (/\b(next|forward|→|›)\b/.test(combinedText)) {
      return "nav-next";
    }
    if (tag === "a" || el.closest("a")) {
      if (/\b(sign.?up|register|subscribe|join|get.?started|try|buy|shop|learn.?more|read.?more|download|contact)\b/.test(combinedText)) {
        return "cta-primary";
      }
      return "cta-link";
    }
    if (el.type === "submit" || /\b(submit|send|save|confirm|ok|done)\b/.test(combinedText)) {
      return "submit";
    }
    if (el.type === "reset" || /\b(reset|clear|cancel)\b/.test(combinedText)) {
      return "reset";
    }
    if (el.getAttribute("aria-pressed") !== null || /\b(toggle|switch)\b/.test(combinedText)) {
      return "toggle";
    }
    if (el.getAttribute("aria-expanded") !== null || /\b(expand|collapse|show|hide)\b/.test(combinedText)) {
      return "expand";
    }
    if (/\b(share|tweet|post)\b/.test(combinedText)) {
      return "share";
    }
    if (/\b(search|find)\b/.test(combinedText) || el.type === "search") {
      return "search";
    }
    if (/\b(edit|modify|change)\b/.test(combinedText)) {
      return "edit";
    }
    if (/\b(delete|remove|trash)\b/.test(combinedText)) {
      return "delete";
    }
    if (/\b(add|create|new|\+)\b/.test(combinedText)) {
      return "add";
    }
    return "action";
  }
  function hasPlayIndicator(el) {
    const svg = el.querySelector("svg");
    if (svg) {
      const path = svg.querySelector("path");
      if (path) {
        const d = path.getAttribute("d") || "";
        if (/M\s*\d+[\s,]+\d+[\s,]*L[\s,]*\d+/.test(d)) return true;
      }
    }
    if (/[▶►▷▸▹]/.test(el.textContent)) return true;
    return false;
  }
  function hasPauseIndicator(el) {
    const svg = el.querySelector("svg");
    if (svg) {
      const rects = svg.querySelectorAll("rect");
      if (rects.length === 2) return true;
    }
    if (/[⏸❚❚║]/.test(el.textContent)) return true;
    return false;
  }
  function hasCloseIcon(el) {
    const svg = el.querySelector("svg");
    if (svg) {
      const paths = svg.querySelectorAll("path, line");
      if (paths.length === 2) return true;
    }
    if (/[×✕✖✗✘]/.test(el.textContent)) return true;
    return false;
  }
  function hasHamburgerIcon(el) {
    const svg = el.querySelector("svg");
    if (svg) {
      const lines = svg.querySelectorAll("line, rect, path");
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
    const style2 = getComputedStyle(el);
    if (style2.animationName && style2.animationName !== "none") return true;
    return false;
  }
  function hasTransitions(el) {
    const style2 = getComputedStyle(el);
    return style2.transitionProperty && style2.transitionProperty !== "none";
  }
  function has3DTransform(el) {
    const style2 = getComputedStyle(el);
    const transform = style2.transform;
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
    const y = 0.2126729 * lr + 0.7151522 * lg + 0.072175 * lb;
    const z = 0.0193339 * lr + 0.119192 * lg + 0.9503041 * lb;
    const l_ = Math.cbrt(0.8189330101 * x + 0.3618667424 * y - 0.1288597137 * z);
    const m_ = Math.cbrt(0.0329845436 * x + 0.9293118715 * y + 0.0361456387 * z);
    const s_ = Math.cbrt(0.0482003018 * x + 0.2643662691 * y + 0.633851707 * z);
    const L = 0.2104542553 * l_ + 0.793617785 * m_ - 0.0040720468 * s_;
    const A = 1.9779984951 * l_ - 2.428592205 * m_ + 0.4505937099 * s_;
    const B = 0.0259040371 * l_ + 0.7827717662 * m_ - 0.808675766 * s_;
    const C = Math.sqrt(A * A + B * B);
    let H = Math.atan2(B, A) * 180 / Math.PI;
    if (H < 0) H += 360;
    return { l: L, c: C, h: H, a };
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
        a: parseFloat(matrix2d[1]),
        b: parseFloat(matrix2d[2]),
        c: parseFloat(matrix2d[3]),
        d: parseFloat(matrix2d[4]),
        e: parseFloat(matrix2d[5]),
        f: parseFloat(matrix2d[6])
      };
    }
    const matrix3d = transformStr.match(/matrix3d\(([\d.\-e,\s]+)\)/);
    if (matrix3d) {
      const vals = matrix3d[1].split(",").map((v) => parseFloat(v.trim()));
      return { type: "matrix3d", values: vals };
    }
    return { type: "unknown", raw: transformStr };
  }
  function parse3DTransform(transformStr) {
    if (!transformStr || transformStr === "none") return null;
    const result = {
      translateX: 0,
      translateY: 0,
      translateZ: 0,
      rotateX: 0,
      rotateY: 0,
      rotateZ: 0,
      scaleX: 1,
      scaleY: 1,
      scaleZ: 1,
      perspective: null
    };
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
    return shadows.filter((s) => s !== null);
  }
  function parseSingleShadow(shadowStr) {
    const inset = shadowStr.includes("inset");
    let colorStr = "rgb(0, 0, 0)";
    const rgbMatch = shadowStr.match(/rgba?\([^)]+\)/);
    if (rgbMatch) colorStr = rgbMatch[0];
    const nums = shadowStr.replace(/rgba?\([^)]+\)/, "").match(/-?[\d.]+px/g);
    if (!nums || nums.length < 2) return null;
    return {
      inset,
      offsetX: parseFloat(nums[0]),
      offsetY: parseFloat(nums[1]),
      blurRadius: nums[2] ? parseFloat(nums[2]) : 0,
      spreadRadius: nums[3] ? parseFloat(nums[3]) : 0,
      color: parseColorToOKLCH(colorStr)
    };
  }
  function parseTextShadow(shadowStr) {
    if (!shadowStr || shadowStr === "none") return [];
    const shadows = [];
    const parts = shadowStr.split(",").map((s) => s.trim());
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
    const parts = ratioStr.split("/").map((s) => parseFloat(s.trim()));
    if (parts.length === 2 && !isNaN(parts[0]) && !isNaN(parts[1])) {
      return { width: parts[0], height: parts[1] };
    }
    return null;
  }
  function getImplicitRole(el) {
    const tag = el.tagName.toLowerCase();
    const implicitRoles = {
      a: el.href ? "link" : null,
      article: "article",
      aside: "complementary",
      button: "button",
      footer: "contentinfo",
      form: "form",
      h1: "heading",
      h2: "heading",
      h3: "heading",
      h4: "heading",
      h5: "heading",
      h6: "heading",
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
  function classifyLayoutRole(el, style2) {
    const display = style2.display;
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
    if (/btn.?primary|button.?primary|cta.?primary|primary.?cta/.test(className)) return true;
    if (/get.?started|sign.?up|try.?free|start.?now|buy.?now/.test(text)) return true;
    return false;
  }
  function detectBrandColorUsage(el, style2) {
    return null;
  }
  function detectsStackingContext(el, style2) {
    if (style2.position !== "static" && style2.zIndex !== "auto") return true;
    if (parseFloat(style2.opacity) < 1) return true;
    if (style2.transform !== "none") return true;
    if (style2.filter !== "none") return true;
    if (style2.perspective !== "none") return true;
    if (style2.clipPath !== "none") return true;
    if (style2.mask !== "none") return true;
    if (style2.isolation === "isolate") return true;
    if (style2.mixBlendMode !== "normal") return true;
    if (style2.willChange !== "auto") return true;
    if (style2.contain === "layout" || style2.contain === "paint" || style2.contain === "strict" || style2.contain === "content") return true;
    return false;
  }
  function detectGestureTarget(el) {
    const style2 = getComputedStyle(el);
    if (style2.touchAction === "none") return "none";
    if (style2.touchAction === "pan-x") return "horizontal-scroll";
    if (style2.touchAction === "pan-y") return "vertical-scroll";
    if (style2.touchAction === "pinch-zoom") return "pinch-zoom";
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
      options: tag === "select" ? Array.from(el.options).map((o) => ({ value: o.value, text: o.text, selected: o.selected })) : null
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
  function detectLottie(el) {
    if (el.querySelector("lottie-player")) {
      return { type: "lottie-player", container: true };
    }
    if (el.classList.contains("lottie") || el.dataset.lottie) {
      return { type: "lottie-web", src: el.dataset.lottie || null };
    }
    if (el.querySelector("dotlottie-player")) {
      return { type: "dotlottie", container: true };
    }
    if (el.classList.contains("bodymovin")) {
      return { type: "bodymovin", container: true };
    }
    return null;
  }
  function detectGSAP(el) {
    if (el.dataset.gsap || el.dataset.scrollTrigger) {
      return { hasGsap: true, scrollTrigger: !!el.dataset.scrollTrigger };
    }
    if (el._gsap) {
      return { hasGsap: true, active: true };
    }
    return null;
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
    hashArray[6] = hashArray[6] & 15 | 80;
    hashArray[8] = hashArray[8] & 63 | 128;
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

  // purescript/foundry-extension/extension/extraction/recorder.js
  var CONFIG = {
    // Total recording duration (ms)
    recordingDuration: 3e4,
    // Time to wait after hover before capturing state (ms)
    hoverSettleTime: 150,
    // Time between element tests (ms)
    interElementDelay: 50,
    // Maximum elements to test (performance limit)
    maxElementsToTest: 500,
    // Frames per second for state capture
    captureFramerate: 10,
    // Screenshot interval during recording
    screenshotInterval: 1e3
  };
  var RecordingSession = class {
    constructor() {
      this.startTime = null;
      this.endTime = null;
      this.initialSnapshot = null;
      this.interactiveElements = [];
      this.hoverReactions = /* @__PURE__ */ new Map();
      this.focusReactions = /* @__PURE__ */ new Map();
      this.clickReactions = /* @__PURE__ */ new Map();
      this.scrollReactions = [];
      this.animationsObserved = [];
      this.screenshots = [];
      this.frames = [];
    }
  };
  async function startRecording(onProgress, onComplete) {
    const session = new RecordingSession();
    session.startTime = performance.now();
    let cancelled = false;
    onProgress(0, "Capturing initial snapshot...");
    session.initialSnapshot = await captureFullSnapshot();
    onProgress(5, "Discovering interactive elements...");
    session.interactiveElements = discoverInteractiveElements();
    const hoverProgress = await testHoverReactions(
      session,
      (progress) => onProgress(5 + progress * 0.6, `Testing hover reactions... (${Math.round(progress * 100)}%)`),
      () => cancelled
    );
    if (cancelled) return;
    onProgress(65, "Testing focus reactions...");
    await testFocusReactions(session, () => cancelled);
    if (cancelled) return;
    onProgress(80, "Testing scroll triggers...");
    await testScrollReactions(session, () => cancelled);
    if (cancelled) return;
    onProgress(90, "Capturing active animations...");
    await captureActiveAnimations(session);
    onProgress(95, "Capturing final state...");
    session.endTime = performance.now();
    onProgress(100, "Processing results...");
    const results = compileSessionResults(session);
    onComplete(results);
    return () => {
      cancelled = true;
    };
  }
  async function captureFullSnapshot() {
    const elements = document.querySelectorAll("*");
    const results = [];
    for (const el of elements) {
      const style2 = getComputedStyle(el);
      if (style2.display === "none" || style2.visibility === "hidden") continue;
      if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
      const elementData = {};
      for (const [pillarName, pillar] of Object.entries(PILLARS)) {
        if (pillar.detect(el)) {
          try {
            const extracted = pillar.extract(el, style2);
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
          selector: getSelector2(el),
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
  function discoverInteractiveElements() {
    const elements = [];
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
      const style2 = getComputedStyle(el);
      if (style2.display === "none" || style2.visibility === "hidden") continue;
      if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
      const hasTransitions2 = style2.transitionProperty !== "none";
      const hasHoverStyles = detectHoverStyles(el);
      elements.push({
        element: el,
        selector: getSelector2(el),
        rect: el.getBoundingClientRect(),
        hasTransitions: hasTransitions2,
        hasHoverStyles,
        interactionType: classifyInteractionType2(el)
      });
    }
    elements.sort((a, b) => {
      const aScore = a.rect.width * a.rect.height - a.rect.top;
      const bScore = b.rect.width * b.rect.height - b.rect.top;
      return bScore - aScore;
    });
    return elements.slice(0, CONFIG.maxElementsToTest);
  }
  function detectHoverStyles(el) {
    const sheets = document.styleSheets;
    for (const sheet of sheets) {
      try {
        const rules = sheet.cssRules || sheet.rules;
        for (const rule of rules) {
          if (rule.selectorText && rule.selectorText.includes(":hover")) {
            const baseSelector = rule.selectorText.replace(/:hover/g, "");
            try {
              if (el.matches(baseSelector)) return true;
            } catch {
            }
          }
        }
      } catch {
      }
    }
    return false;
  }
  async function testHoverReactions(session, onProgress, isCancelled) {
    const elements = session.interactiveElements;
    const total = elements.length;
    for (let i = 0; i < total; i++) {
      if (isCancelled()) return;
      const { element, selector } = elements[i];
      const beforeStyle = captureElementStyles(element);
      const hoverState = await simulateHover(element);
      await sleep(CONFIG.hoverSettleTime);
      const afterStyle = captureElementStyles(element);
      const animationsTriggered = detectTriggeredAnimations(element);
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
      await simulateHoverEnd(element);
      onProgress(i / total);
      await sleep(CONFIG.interElementDelay);
    }
    return true;
  }
  async function simulateHover(element) {
    const rect = element.getBoundingClientRect();
    const centerX = rect.left + rect.width / 2;
    const centerY = rect.top + rect.height / 2;
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
  async function testFocusReactions(session, isCancelled) {
    const focusable = session.interactiveElements.filter(({ element }) => {
      return element.tabIndex >= 0 || ["a", "button", "input", "select", "textarea"].includes(element.tagName.toLowerCase());
    });
    for (const { element, selector } of focusable) {
      if (isCancelled()) return;
      const beforeStyle = captureElementStyles(element);
      element.focus();
      await sleep(50);
      const afterStyle = captureElementStyles(element);
      const focusVisible = element.matches(":focus-visible");
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
      element.blur();
      await sleep(CONFIG.interElementDelay);
    }
  }
  async function testScrollReactions(session, isCancelled) {
    const originalScrollY = window.scrollY;
    const maxScroll = document.documentElement.scrollHeight - window.innerHeight;
    const steps = 10;
    for (let i = 0; i <= steps; i++) {
      if (isCancelled()) return;
      const targetY = maxScroll / steps * i;
      window.scrollTo({ top: targetY, behavior: "instant" });
      await sleep(100);
      const visibleAnimations = detectVisibleAnimations();
      if (visibleAnimations.length > 0) {
        session.scrollReactions.push({
          scrollY: targetY,
          scrollPercent: targetY / maxScroll,
          animations: visibleAnimations
        });
      }
    }
    window.scrollTo({ top: originalScrollY, behavior: "instant" });
  }
  function detectVisibleAnimations() {
    const animations = [];
    const elements = document.querySelectorAll("*");
    for (const el of elements) {
      const rect = el.getBoundingClientRect();
      if (rect.bottom < 0 || rect.top > window.innerHeight) continue;
      const elAnimations = el.getAnimations ? el.getAnimations() : [];
      for (const anim of elAnimations) {
        if (anim.playState === "running") {
          animations.push({
            selector: getSelector2(el),
            animationName: anim.animationName || anim.id,
            currentTime: anim.currentTime,
            duration: anim.effect?.getTiming().duration
          });
        }
      }
    }
    return animations;
  }
  async function captureActiveAnimations(session) {
    const allAnimations = document.getAnimations ? document.getAnimations() : [];
    for (const anim of allAnimations) {
      const target = anim.effect?.target;
      if (!target) continue;
      const timing = anim.effect?.getTiming();
      const keyframes = anim.effect?.getKeyframes ? anim.effect.getKeyframes() : [];
      session.animationsObserved.push({
        selector: getSelector2(target),
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
        keyframes: keyframes.map((kf) => ({
          offset: kf.offset,
          easing: kf.easing,
          composite: kf.composite,
          properties: Object.keys(kf).filter((k) => !["offset", "easing", "composite"].includes(k))
        }))
      });
    }
  }
  function captureElementStyles(element) {
    const style2 = getComputedStyle(element);
    return {
      // Colors
      backgroundColor: style2.backgroundColor,
      color: style2.color,
      borderColor: style2.borderColor,
      outlineColor: style2.outlineColor,
      // Box model
      width: style2.width,
      height: style2.height,
      padding: style2.padding,
      margin: style2.margin,
      // Borders
      borderWidth: style2.borderWidth,
      borderRadius: style2.borderRadius,
      // Transform
      transform: style2.transform,
      // Shadows
      boxShadow: style2.boxShadow,
      textShadow: style2.textShadow,
      // Opacity
      opacity: style2.opacity,
      // Filters
      filter: style2.filter,
      backdropFilter: style2.backdropFilter,
      // Text
      textDecoration: style2.textDecoration,
      letterSpacing: style2.letterSpacing,
      // Cursor
      cursor: style2.cursor,
      // Outline (focus indicator)
      outline: style2.outline,
      outlineOffset: style2.outlineOffset,
      // Scale (for hover zoom effects)
      scale: style2.scale
    };
  }
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
  function detectTriggeredAnimations(element) {
    const animations = element.getAnimations ? element.getAnimations() : [];
    return animations.filter((anim) => anim.playState === "running" && anim.currentTime < 500).map((anim) => ({
      id: anim.id,
      name: anim.animationName,
      duration: anim.effect?.getTiming().duration,
      easing: anim.effect?.getTiming().easing
    }));
  }
  function compileSessionResults(session) {
    return {
      // Metadata
      url: session.initialSnapshot.url,
      title: session.initialSnapshot.title,
      duration: session.endTime - session.startTime,
      recordedAt: (/* @__PURE__ */ new Date()).toISOString(),
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
        hoverReactions: Array.from(session.hoverReactions.values()).map((reaction) => ({
          selector: reaction.selector,
          changes: Object.keys(reaction.styleDiff),
          styleDiff: reaction.styleDiff,
          animationsTriggered: reaction.animationsTriggered
        })),
        // Focus reactions
        focusReactions: Array.from(session.focusReactions.values()).map((reaction) => ({
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
          (sum, sr) => sum + sr.animations.length,
          0
        )
      }
    };
  }
  function sleep(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }
  function getSelector2(el) {
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
  function classifyInteractionType2(el) {
    const tag = el.tagName.toLowerCase();
    if (tag === "a") return "link";
    if (tag === "button") return "button";
    if (tag === "input") return `input-${el.type || "text"}`;
    if (tag === "select") return "select";
    if (tag === "textarea") return "textarea";
    if (el.getAttribute("role") === "button") return "button-role";
    const style2 = getComputedStyle(el);
    if (style2.cursor === "pointer") return "clickable";
    if (el.getAttribute("tabindex") !== null) return "focusable";
    return "unknown";
  }

  // purescript/foundry-extension/extension/extraction/lottie.js
  function extractAllLottieAnimations() {
    const animations = [];
    const lottiePlayers = document.querySelectorAll("lottie-player");
    for (const player of lottiePlayers) {
      const data = extractFromLottiePlayer(player);
      if (data) animations.push(data);
    }
    const dotLottiePlayers = document.querySelectorAll("dotlottie-player");
    for (const player of dotLottiePlayers) {
      const data = extractFromDotLottiePlayer(player);
      if (data) animations.push(data);
    }
    const lottieContainers = document.querySelectorAll("[data-animation-path], .lottie, .bodymovin");
    for (const container of lottieContainers) {
      const data = extractFromLottieWeb(container);
      if (data) animations.push(data);
    }
    if (window.lottie) {
      const registeredAnimations = extractFromGlobalLottie();
      animations.push(...registeredAnimations);
    }
    return animations;
  }
  function extractFromLottiePlayer(player) {
    try {
      const animData = player.getLottie?.() || player.animation;
      if (!animData) return null;
      const src = player.getAttribute("src");
      return {
        type: "lottie-player",
        selector: getSelector3(player),
        src,
        container: {
          width: player.offsetWidth,
          height: player.offsetHeight
        },
        animation: extractAnimationData(animData)
      };
    } catch (e) {
      console.warn("[Foundry] Failed to extract from lottie-player:", e);
      return null;
    }
  }
  function extractFromDotLottiePlayer(player) {
    try {
      const animData = player.getLottie?.();
      if (!animData) return null;
      const src = player.getAttribute("src");
      return {
        type: "dotlottie-player",
        selector: getSelector3(player),
        src,
        container: {
          width: player.offsetWidth,
          height: player.offsetHeight
        },
        animation: extractAnimationData(animData)
      };
    } catch (e) {
      console.warn("[Foundry] Failed to extract from dotlottie-player:", e);
      return null;
    }
  }
  function extractFromLottieWeb(container) {
    try {
      const animData = container.__lottie || container._lottie;
      if (!animData) return null;
      return {
        type: "lottie-web",
        selector: getSelector3(container),
        container: {
          width: container.offsetWidth,
          height: container.offsetHeight
        },
        animation: extractAnimationData(animData)
      };
    } catch (e) {
      return null;
    }
  }
  function extractFromGlobalLottie() {
    const animations = [];
    try {
      const registered = window.lottie.getRegisteredAnimations?.() || [];
      for (const anim of registered) {
        const container = anim.wrapper;
        if (!container) continue;
        animations.push({
          type: "lottie-global",
          selector: getSelector3(container),
          container: {
            width: container.offsetWidth,
            height: container.offsetHeight
          },
          animation: extractAnimationData(anim)
        });
      }
    } catch (e) {
      console.warn("[Foundry] Failed to extract from global lottie:", e);
    }
    return animations;
  }
  function extractAnimationData(anim) {
    const animData = anim.animationData || anim;
    if (!animData) return null;
    return {
      // Metadata
      version: animData.v,
      name: animData.nm || animData.name,
      // Timing
      frameRate: animData.fr,
      inPoint: animData.ip,
      outPoint: animData.op,
      duration: (animData.op - animData.ip) / animData.fr,
      // Dimensions
      width: animData.w,
      height: animData.h,
      // 3D flag
      is3D: animData.ddd === 1,
      // Layers
      layers: extractLayers(animData.layers || []),
      // Assets (images, precomps)
      assets: extractAssets(animData.assets || []),
      // Fonts
      fonts: extractFonts(animData.fonts),
      // Markers (named cue points)
      markers: extractMarkers(animData.markers || []),
      // Motion paths (extracted from all layers)
      motionPaths: extractAllMotionPaths(animData.layers || [])
    };
  }
  function extractLayers(layers) {
    return layers.map((layer) => ({
      // Identity
      name: layer.nm,
      index: layer.ind,
      // Type
      type: getLayerType(layer.ty),
      // Timing
      inPoint: layer.ip,
      outPoint: layer.op,
      startTime: layer.st,
      // Hierarchy
      parent: layer.parent,
      // Transform
      transform: extractTransform(layer.ks),
      // Type-specific data
      shapes: layer.ty === 4 ? extractShapes(layer.shapes || []) : null,
      text: layer.ty === 5 ? extractTextData(layer.t) : null,
      // Effects
      effects: extractEffects(layer.ef || []),
      // Masks
      masks: extractMasks(layer.masksProperties || []),
      // Blend mode
      blendMode: getBlendMode(layer.bm),
      // Matte
      matteMode: getMatteMode(layer.tt),
      matteTarget: layer.td
    }));
  }
  function getLayerType(ty) {
    const types = {
      0: "precomp",
      1: "solid",
      2: "image",
      3: "null",
      4: "shape",
      5: "text",
      6: "audio",
      7: "videoPlaceholder",
      8: "imagePlaceholder",
      9: "guide",
      10: "adjustment",
      11: "camera",
      12: "light",
      13: "data"
    };
    return types[ty] || "unknown";
  }
  function extractTransform(ks) {
    if (!ks) return null;
    return {
      // Anchor point
      anchorPoint: extractAnimatedValue(ks.a),
      // Position (can be separated x/y or combined)
      position: ks.p ? extractAnimatedValue(ks.p) : null,
      positionX: ks.px ? extractAnimatedValue(ks.px) : null,
      positionY: ks.py ? extractAnimatedValue(ks.py) : null,
      positionZ: ks.pz ? extractAnimatedValue(ks.pz) : null,
      // Scale
      scale: extractAnimatedValue(ks.s),
      // Rotation (can be separated for 3D)
      rotation: ks.r ? extractAnimatedValue(ks.r) : null,
      rotationX: ks.rx ? extractAnimatedValue(ks.rx) : null,
      rotationY: ks.ry ? extractAnimatedValue(ks.ry) : null,
      rotationZ: ks.rz ? extractAnimatedValue(ks.rz) : null,
      orientation: ks.or ? extractAnimatedValue(ks.or) : null,
      // Opacity
      opacity: extractAnimatedValue(ks.o),
      // Skew
      skew: ks.sk ? extractAnimatedValue(ks.sk) : null,
      skewAxis: ks.sa ? extractAnimatedValue(ks.sa) : null
    };
  }
  function extractAnimatedValue(prop) {
    if (!prop) return null;
    if (prop.a === 1 || Array.isArray(prop.k?.[0]?.s)) {
      return {
        animated: true,
        keyframes: extractKeyframes(prop.k)
      };
    }
    return {
      animated: false,
      value: prop.k
    };
  }
  function extractKeyframes(keyframes) {
    if (!Array.isArray(keyframes)) return [];
    return keyframes.map((kf, index) => ({
      // Time
      time: kf.t,
      // Values
      startValue: kf.s,
      endValue: kf.e,
      // Hold keyframe (no interpolation)
      hold: kf.h === 1,
      // Bezier easing
      easing: kf.o && kf.i ? {
        outTangent: { x: kf.o.x, y: kf.o.y },
        inTangent: { x: kf.i.x, y: kf.i.y }
      } : null,
      // Spatial bezier (for position paths)
      spatialTangent: kf.to && kf.ti ? {
        to: kf.to,
        ti: kf.ti
      } : null
    }));
  }
  function extractShapes(shapes) {
    return shapes.map((shape) => {
      const baseData = {
        type: getShapeType(shape.ty),
        name: shape.nm,
        hidden: shape.hd
      };
      switch (shape.ty) {
        case "gr":
          return {
            ...baseData,
            items: extractShapes(shape.it || [])
          };
        case "sh":
          return {
            ...baseData,
            path: extractPath(shape.ks)
          };
        case "rc":
          return {
            ...baseData,
            position: extractAnimatedValue(shape.p),
            size: extractAnimatedValue(shape.s),
            roundness: extractAnimatedValue(shape.r)
          };
        case "el":
          return {
            ...baseData,
            position: extractAnimatedValue(shape.p),
            size: extractAnimatedValue(shape.s)
          };
        case "sr":
          return {
            ...baseData,
            position: extractAnimatedValue(shape.p),
            points: extractAnimatedValue(shape.pt),
            rotation: extractAnimatedValue(shape.r),
            innerRadius: extractAnimatedValue(shape.ir),
            outerRadius: extractAnimatedValue(shape.or),
            innerRoundness: extractAnimatedValue(shape.is),
            outerRoundness: extractAnimatedValue(shape.os),
            starType: shape.sy
            // 1 = star, 2 = polygon
          };
        case "fl":
          return {
            ...baseData,
            color: extractAnimatedValue(shape.c),
            opacity: extractAnimatedValue(shape.o)
          };
        case "st":
          return {
            ...baseData,
            color: extractAnimatedValue(shape.c),
            opacity: extractAnimatedValue(shape.o),
            width: extractAnimatedValue(shape.w),
            lineCap: shape.lc,
            // 1=butt, 2=round, 3=square
            lineJoin: shape.lj,
            // 1=miter, 2=round, 3=bevel
            miterLimit: shape.ml
          };
        case "gf":
          return {
            ...baseData,
            gradientType: shape.t,
            // 1=linear, 2=radial
            startPoint: extractAnimatedValue(shape.s),
            endPoint: extractAnimatedValue(shape.e),
            colors: extractGradientColors(shape.g),
            opacity: extractAnimatedValue(shape.o)
          };
        case "tr":
          return {
            ...baseData,
            transform: {
              anchorPoint: extractAnimatedValue(shape.a),
              position: extractAnimatedValue(shape.p),
              scale: extractAnimatedValue(shape.s),
              rotation: extractAnimatedValue(shape.r),
              opacity: extractAnimatedValue(shape.o),
              skew: extractAnimatedValue(shape.sk),
              skewAxis: extractAnimatedValue(shape.sa)
            }
          };
        case "tm":
          return {
            ...baseData,
            start: extractAnimatedValue(shape.s),
            end: extractAnimatedValue(shape.e),
            offset: extractAnimatedValue(shape.o)
          };
        case "rd":
          return {
            ...baseData,
            radius: extractAnimatedValue(shape.r)
          };
        case "rp":
          return {
            ...baseData,
            copies: extractAnimatedValue(shape.c),
            offset: extractAnimatedValue(shape.o),
            transform: shape.tr ? extractTransform(shape.tr) : null
          };
        default:
          return baseData;
      }
    });
  }
  function getShapeType(ty) {
    const types = {
      "gr": "group",
      "sh": "path",
      "rc": "rectangle",
      "el": "ellipse",
      "sr": "polystar",
      "fl": "fill",
      "st": "stroke",
      "gf": "gradientFill",
      "gs": "gradientStroke",
      "tr": "transform",
      "tm": "trim",
      "rd": "roundCorners",
      "pb": "pucker/bloat",
      "tw": "twist",
      "mm": "merge",
      "rp": "repeater",
      "op": "offset"
    };
    return types[ty] || ty;
  }
  function extractPath(ks) {
    const pathData = extractAnimatedValue(ks);
    if (!pathData) return null;
    if (pathData.animated) {
      return {
        animated: true,
        keyframes: pathData.keyframes.map((kf) => ({
          ...kf,
          path: kf.startValue ? parsePathData(kf.startValue) : null
        }))
      };
    }
    return {
      animated: false,
      path: parsePathData(pathData.value)
    };
  }
  function parsePathData(data) {
    if (!data) return null;
    return {
      vertices: data.v,
      // Array of [x, y] points
      inTangents: data.i,
      // Bezier in tangents
      outTangents: data.o,
      // Bezier out tangents
      closed: data.c
      // Whether path is closed
    };
  }
  function extractGradientColors(g) {
    if (!g || !g.k) return null;
    const count = g.p;
    const colors = g.k.k;
    const stops = [];
    for (let i = 0; i < count; i++) {
      const idx = i * 4;
      stops.push({
        offset: colors[idx],
        r: colors[idx + 1],
        g: colors[idx + 2],
        b: colors[idx + 3]
      });
    }
    return stops;
  }
  function extractTextData(t) {
    if (!t) return null;
    return {
      // Document data
      text: t.d?.k?.[0]?.s?.t || null,
      font: t.d?.k?.[0]?.s?.f || null,
      fontSize: t.d?.k?.[0]?.s?.s || null,
      color: t.d?.k?.[0]?.s?.fc || null,
      // Text path
      path: t.p ? {
        mask: t.p.m,
        firstMargin: t.p.f,
        lastMargin: t.p.l,
        perpendicular: t.p.p,
        reversed: t.p.r
      } : null,
      // Animators
      animators: t.a ? t.a.map((animator) => ({
        name: animator.nm,
        selectors: animator.s,
        properties: animator.a
      })) : null
    };
  }
  function extractEffects(effects) {
    return effects.map((effect) => ({
      type: getEffectType(effect.ty),
      name: effect.nm,
      enabled: effect.en !== 0,
      properties: effect.ef?.map((prop) => ({
        name: prop.nm,
        value: extractAnimatedValue(prop.v)
      })) || []
    }));
  }
  function getEffectType(ty) {
    const types = {
      0: "slider",
      1: "angle",
      2: "color",
      3: "point",
      4: "checkbox",
      5: "group",
      6: "dropdown",
      7: "layer",
      10: "layerStyles",
      20: "tint",
      21: "fill",
      22: "stroke",
      23: "tritone",
      24: "proLevels",
      25: "dropShadow",
      26: "radialWipe",
      27: "displacementMap",
      28: "matte3",
      29: "gaussianBlur",
      30: "twirl",
      31: "mesh",
      32: "wavy"
    };
    return types[ty] || "unknown";
  }
  function extractMasks(masks) {
    return masks.map((mask) => ({
      name: mask.nm,
      mode: getMaskMode(mask.mode),
      inverted: mask.inv,
      path: extractPath(mask.pt),
      opacity: extractAnimatedValue(mask.o),
      expansion: extractAnimatedValue(mask.x)
    }));
  }
  function getMaskMode(mode) {
    const modes = {
      "n": "none",
      "a": "add",
      "s": "subtract",
      "i": "intersect",
      "l": "lighten",
      "d": "darken",
      "f": "difference"
    };
    return modes[mode] || mode;
  }
  function getBlendMode(bm) {
    const modes = {
      0: "normal",
      1: "multiply",
      2: "screen",
      3: "overlay",
      4: "darken",
      5: "lighten",
      6: "colorDodge",
      7: "colorBurn",
      8: "hardLight",
      9: "softLight",
      10: "difference",
      11: "exclusion",
      12: "hue",
      13: "saturation",
      14: "color",
      15: "luminosity"
    };
    return modes[bm] || "normal";
  }
  function getMatteMode(tt) {
    const modes = {
      0: "none",
      1: "alpha",
      2: "invertedAlpha",
      3: "luma",
      4: "invertedLuma"
    };
    return modes[tt] || "none";
  }
  function extractAssets(assets) {
    return assets.map((asset) => {
      if (asset.layers) {
        return {
          type: "precomp",
          id: asset.id,
          name: asset.nm,
          width: asset.w,
          height: asset.h,
          layers: extractLayers(asset.layers)
        };
      }
      if (asset.u || asset.p) {
        return {
          type: "image",
          id: asset.id,
          name: asset.nm,
          path: asset.u,
          filename: asset.p,
          width: asset.w,
          height: asset.h,
          embedded: asset.e === 1
        };
      }
      return {
        type: "unknown",
        id: asset.id
      };
    });
  }
  function extractFonts(fonts) {
    if (!fonts || !fonts.list) return [];
    return fonts.list.map((font) => ({
      family: font.fFamily,
      name: font.fName,
      style: font.fStyle,
      path: font.fPath,
      weight: font.fWeight,
      origin: font.origin
      // 0=local, 1=CSS/Google, 2=script/typekit, 3=fontURL
    }));
  }
  function extractMarkers(markers) {
    return markers.map((marker) => ({
      name: marker.cm,
      time: marker.tm,
      duration: marker.dr
    }));
  }
  function extractAllMotionPaths(layers) {
    const paths = [];
    for (const layer of layers) {
      if (layer.ks?.p?.a === 1) {
        const keyframes = layer.ks.p.k;
        const hasMotionPath = keyframes.some((kf) => kf.to && kf.ti);
        if (hasMotionPath) {
          paths.push({
            layerName: layer.nm,
            layerIndex: layer.ind,
            keyframes: keyframes.map((kf) => ({
              time: kf.t,
              position: kf.s,
              to: kf.to,
              // Spatial out tangent
              ti: kf.ti,
              // Spatial in tangent
              easing: kf.o && kf.i ? {
                outX: kf.o.x,
                outY: kf.o.y,
                inX: kf.i.x,
                inY: kf.i.y
              } : null
            }))
          });
        }
      }
      if (layer.shapes) {
        const shapePaths = extractShapeMotionPaths(layer.shapes, layer.nm);
        paths.push(...shapePaths);
      }
    }
    return paths;
  }
  function extractShapeMotionPaths(shapes, layerName) {
    const paths = [];
    for (const shape of shapes) {
      if (shape.ty === "gr") {
        const groupPaths = extractShapeMotionPaths(shape.it || [], layerName);
        paths.push(...groupPaths);
      }
      if (shape.ty === "sh" && shape.ks?.a === 1) {
        paths.push({
          type: "shapePath",
          layerName,
          shapeName: shape.nm,
          keyframes: shape.ks.k.map((kf) => ({
            time: kf.t,
            path: parsePathData(kf.s?.[0] || kf.s)
          }))
        });
      }
    }
    return paths;
  }
  function getSelector3(el) {
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

  // purescript/foundry-extension/extension/extraction/index.js
  async function instantSnapshot() {
    const startTime = performance.now();
    const screenshot = await captureScreenshot();
    const elements = await extractAllElements();
    const lottieAnimations = extractAllLottieAnimations();
    const layers = groupByZIndex(elements);
    const brandSummary = extractBrandSummary(elements);
    const endTime = performance.now();
    return {
      type: "snapshot",
      timestamp: (/* @__PURE__ */ new Date()).toISOString(),
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
      screenshot,
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
  async function extractAllElements() {
    const elements = document.querySelectorAll("*");
    const results = [];
    const elementArray = Array.from(elements);
    const elementToIndex = /* @__PURE__ */ new Map();
    elementArray.forEach((el, idx) => elementToIndex.set(el, idx));
    for (const el of elementArray) {
      const style2 = getComputedStyle(el);
      if (style2.display === "none" || style2.visibility === "hidden") continue;
      if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
      const rect = el.getBoundingClientRect();
      if (rect.bottom < -1e3 || rect.top > window.innerHeight + 1e3) continue;
      const pillars = {};
      for (const [pillarName, pillar] of Object.entries(PILLARS)) {
        try {
          if (pillar.detect(el)) {
            const extracted = pillar.extract(el, style2);
            if (extracted !== null && Object.keys(extracted).length > 0) {
              pillars[pillarName] = extracted;
            }
          }
        } catch (e) {
        }
      }
      if (Object.keys(pillars).length === 0) continue;
      const parent = el.parentElement;
      const parentIndex = parent ? elementToIndex.get(parent) ?? -1 : -1;
      const childIndices = Array.from(el.children).map((child) => elementToIndex.get(child)).filter((idx) => idx !== void 0);
      results.push({
        // Identity
        selector: getSelector4(el),
        uuid: await uuid52(getSelector4(el)),
        // Tree structure
        index: elementToIndex.get(el),
        parentIndex,
        childIndices,
        depth: getSelector4(el).split(" > ").length,
        // All pillar data
        pillars
      });
    }
    return results;
  }
  async function fullRecording(onProgress = () => {
  }) {
    onProgress(0, "Capturing initial snapshot...");
    const initialSnapshot = await instantSnapshot();
    return new Promise((resolve) => {
      startRecording(
        (percent, message) => onProgress(percent, message),
        (recordingResults) => {
          resolve({
            type: "recording",
            timestamp: (/* @__PURE__ */ new Date()).toISOString(),
            // Initial state
            initialSnapshot,
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
  function extractBrandSummary(elements) {
    const colors = /* @__PURE__ */ new Map();
    const fonts = /* @__PURE__ */ new Map();
    const spacing = /* @__PURE__ */ new Map();
    const buttons = [];
    for (const element of elements) {
      const pillars = element.pillars;
      if (pillars.color) {
        collectColor(colors, pillars.color.background, "background");
        collectColor(colors, pillars.color.foreground, "foreground");
        collectColor(colors, pillars.color.border, "border");
      }
      if (pillars.typography?.fontFamily) {
        const family = pillars.typography.fontFamily;
        fonts.set(family, (fonts.get(family) || 0) + 1);
      }
      if (pillars.dimension) {
        const { width, height } = pillars.dimension;
        if (width > 0) spacing.set(`w:${Math.round(width)}`, (spacing.get(`w:${Math.round(width)}`) || 0) + 1);
        if (height > 0) spacing.set(`h:${Math.round(height)}`, (spacing.get(`h:${Math.round(height)}`) || 0) + 1);
      }
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
      colors: Array.from(colors.entries()).sort((a, b) => b[1].count - a[1].count).slice(0, 20).map(([key, value]) => ({
        oklch: value.color,
        count: value.count,
        usage: value.usage
      })),
      // Top fonts by usage
      fonts: Array.from(fonts.entries()).sort((a, b) => b[1] - a[1]).slice(0, 10).map(([family, count]) => ({ family, count })),
      // Button classification summary
      buttons: {
        total: buttons.length,
        byType: groupBy(buttons, (b) => b.type)
      }
    };
  }
  function collectColor(map, oklch, usage) {
    if (!oklch) return;
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
  function groupByZIndex(elements) {
    const layerMap = /* @__PURE__ */ new Map();
    for (const element of elements) {
      const zIndex = element.pillars.elevation?.zIndex || 0;
      if (!layerMap.has(zIndex)) {
        layerMap.set(zIndex, []);
      }
      layerMap.get(zIndex).push(element.selector);
    }
    return Array.from(layerMap.entries()).sort((a, b) => a[0] - b[0]).map(([zIndex, selectors]) => ({
      zIndex,
      count: selectors.length,
      selectors
    }));
  }
  async function captureScreenshot() {
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
    return null;
  }
  function getSelector4(el) {
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
  async function uuid52(name) {
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
    hashArray[6] = hashArray[6] & 15 | 80;
    hashArray[8] = hashArray[8] & 63 | 128;
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
  chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
    switch (request.action) {
      case "instantSnapshot":
        instantSnapshot().then((result) => sendResponse({ success: true, data: result })).catch((err) => sendResponse({ success: false, error: err.message }));
        return true;
      // Async response
      case "fullRecording":
        fullRecording((percent, message) => {
          chrome.runtime.sendMessage({
            type: "progress",
            percent,
            message
          });
        }).then((result) => sendResponse({ success: true, data: result })).catch((err) => sendResponse({ success: false, error: err.message }));
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
  console.log("[Foundry] Full extraction module loaded (v2.0.0)");
})();
