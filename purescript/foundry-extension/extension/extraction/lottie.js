// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // foundry // extraction // lottie
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Lottie animation extraction and path analysis.
// Extracts motion paths, keyframes, and asset references from Lottie JSONs.
//
// ARCHITECTURE:
//   1. Detect Lottie players/containers
//   2. Extract animation JSON data
//   3. Parse layers, shapes, and keyframes
//   4. Convert motion paths to Schema Motion atoms
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // lottie types
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Extracted Lottie animation data.
 */
class LottieAnimation {
  constructor() {
    this.version = null;
    this.name = null;
    this.frameRate = 0;
    this.inPoint = 0;
    this.outPoint = 0;
    this.width = 0;
    this.height = 0;
    this.layers = [];
    this.assets = [];
    this.fonts = [];
    this.markers = [];
  }
}

/**
 * Lottie layer with motion paths.
 */
class LottieLayer {
  constructor() {
    this.name = null;
    this.index = 0;
    this.type = null;  // "shape", "solid", "image", "text", "null", "precomp"
    this.inPoint = 0;
    this.outPoint = 0;
    this.transform = null;
    this.shapes = [];
    this.effects = [];
    this.masks = [];
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // main extraction
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Find and extract all Lottie animations on the page.
 * 
 * @returns {Array<Object>} - Array of extracted Lottie data
 */
export function extractAllLottieAnimations() {
  const animations = [];
  
  // Method 1: lottie-player elements (LottieFiles Web Component)
  const lottiePlayers = document.querySelectorAll("lottie-player");
  for (const player of lottiePlayers) {
    const data = extractFromLottiePlayer(player);
    if (data) animations.push(data);
  }
  
  // Method 2: dotlottie-player elements
  const dotLottiePlayers = document.querySelectorAll("dotlottie-player");
  for (const player of dotLottiePlayers) {
    const data = extractFromDotLottiePlayer(player);
    if (data) animations.push(data);
  }
  
  // Method 3: lottie-web instances (bodymovin)
  const lottieContainers = document.querySelectorAll("[data-animation-path], .lottie, .bodymovin");
  for (const container of lottieContainers) {
    const data = extractFromLottieWeb(container);
    if (data) animations.push(data);
  }
  
  // Method 4: Check for global lottie object
  if (window.lottie) {
    const registeredAnimations = extractFromGlobalLottie();
    animations.push(...registeredAnimations);
  }
  
  return animations;
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // player extraction
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Extract from <lottie-player> web component.
 */
function extractFromLottiePlayer(player) {
  try {
    // Get animation data from player
    const animData = player.getLottie?.() || player.animation;
    if (!animData) return null;
    
    // Get source URL
    const src = player.getAttribute("src");
    
    return {
      type: "lottie-player",
      selector: getSelector(player),
      src: src,
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

/**
 * Extract from <dotlottie-player> web component.
 */
function extractFromDotLottiePlayer(player) {
  try {
    // dotLottie uses a different API
    const animData = player.getLottie?.();
    if (!animData) return null;
    
    const src = player.getAttribute("src");
    
    return {
      type: "dotlottie-player",
      selector: getSelector(player),
      src: src,
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

/**
 * Extract from lottie-web (bodymovin) container.
 */
function extractFromLottieWeb(container) {
  try {
    // lottie-web stores animation on container.__lottie
    const animData = container.__lottie || container._lottie;
    if (!animData) return null;
    
    return {
      type: "lottie-web",
      selector: getSelector(container),
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

/**
 * Extract from global lottie object.
 */
function extractFromGlobalLottie() {
  const animations = [];
  
  try {
    // lottie.getRegisteredAnimations() returns all active animations
    const registered = window.lottie.getRegisteredAnimations?.() || [];
    
    for (const anim of registered) {
      const container = anim.wrapper;
      if (!container) continue;
      
      animations.push({
        type: "lottie-global",
        selector: getSelector(container),
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

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // animation parsing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Extract detailed animation data from a Lottie animation object.
 */
function extractAnimationData(anim) {
  // Get the raw animation data
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

/**
 * Extract layer data.
 */
function extractLayers(layers) {
  return layers.map(layer => ({
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

/**
 * Get layer type name from numeric code.
 */
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

/**
 * Extract transform (position, scale, rotation, etc).
 */
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

/**
 * Extract animated value (static or keyframed).
 */
function extractAnimatedValue(prop) {
  if (!prop) return null;
  
  // Check if animated (has keyframes)
  if (prop.a === 1 || Array.isArray(prop.k?.[0]?.s)) {
    return {
      animated: true,
      keyframes: extractKeyframes(prop.k)
    };
  }
  
  // Static value
  return {
    animated: false,
    value: prop.k
  };
}

/**
 * Extract keyframes from property.
 */
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

/**
 * Extract shapes from shape layer.
 */
function extractShapes(shapes) {
  return shapes.map(shape => {
    const baseData = {
      type: getShapeType(shape.ty),
      name: shape.nm,
      hidden: shape.hd
    };
    
    // Type-specific data
    switch (shape.ty) {
      case "gr":  // Group
        return {
          ...baseData,
          items: extractShapes(shape.it || [])
        };
        
      case "sh":  // Path
        return {
          ...baseData,
          path: extractPath(shape.ks)
        };
        
      case "rc":  // Rectangle
        return {
          ...baseData,
          position: extractAnimatedValue(shape.p),
          size: extractAnimatedValue(shape.s),
          roundness: extractAnimatedValue(shape.r)
        };
        
      case "el":  // Ellipse
        return {
          ...baseData,
          position: extractAnimatedValue(shape.p),
          size: extractAnimatedValue(shape.s)
        };
        
      case "sr":  // Polystar
        return {
          ...baseData,
          position: extractAnimatedValue(shape.p),
          points: extractAnimatedValue(shape.pt),
          rotation: extractAnimatedValue(shape.r),
          innerRadius: extractAnimatedValue(shape.ir),
          outerRadius: extractAnimatedValue(shape.or),
          innerRoundness: extractAnimatedValue(shape.is),
          outerRoundness: extractAnimatedValue(shape.os),
          starType: shape.sy  // 1 = star, 2 = polygon
        };
        
      case "fl":  // Fill
        return {
          ...baseData,
          color: extractAnimatedValue(shape.c),
          opacity: extractAnimatedValue(shape.o)
        };
        
      case "st":  // Stroke
        return {
          ...baseData,
          color: extractAnimatedValue(shape.c),
          opacity: extractAnimatedValue(shape.o),
          width: extractAnimatedValue(shape.w),
          lineCap: shape.lc,  // 1=butt, 2=round, 3=square
          lineJoin: shape.lj,  // 1=miter, 2=round, 3=bevel
          miterLimit: shape.ml
        };
        
      case "gf":  // Gradient fill
        return {
          ...baseData,
          gradientType: shape.t,  // 1=linear, 2=radial
          startPoint: extractAnimatedValue(shape.s),
          endPoint: extractAnimatedValue(shape.e),
          colors: extractGradientColors(shape.g),
          opacity: extractAnimatedValue(shape.o)
        };
        
      case "tr":  // Transform
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
        
      case "tm":  // Trim paths
        return {
          ...baseData,
          start: extractAnimatedValue(shape.s),
          end: extractAnimatedValue(shape.e),
          offset: extractAnimatedValue(shape.o)
        };
        
      case "rd":  // Round corners
        return {
          ...baseData,
          radius: extractAnimatedValue(shape.r)
        };
        
      case "rp":  // Repeater
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

/**
 * Get shape type name from code.
 */
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

/**
 * Extract path data.
 */
function extractPath(ks) {
  const pathData = extractAnimatedValue(ks);
  
  if (!pathData) return null;
  
  if (pathData.animated) {
    return {
      animated: true,
      keyframes: pathData.keyframes.map(kf => ({
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

/**
 * Parse path data (vertices, in/out tangents, closed).
 */
function parsePathData(data) {
  if (!data) return null;
  
  return {
    vertices: data.v,  // Array of [x, y] points
    inTangents: data.i,  // Bezier in tangents
    outTangents: data.o,  // Bezier out tangents
    closed: data.c  // Whether path is closed
  };
}

/**
 * Extract gradient colors.
 */
function extractGradientColors(g) {
  if (!g || !g.k) return null;
  
  const count = g.p;  // Number of color stops
  const colors = g.k.k;  // Color values array
  
  // Colors are stored as [offset, r, g, b, offset, r, g, b, ...]
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

/**
 * Extract text layer data.
 */
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
    animators: t.a ? t.a.map(animator => ({
      name: animator.nm,
      selectors: animator.s,
      properties: animator.a
    })) : null
  };
}

/**
 * Extract effects.
 */
function extractEffects(effects) {
  return effects.map(effect => ({
    type: getEffectType(effect.ty),
    name: effect.nm,
    enabled: effect.en !== 0,
    properties: effect.ef?.map(prop => ({
      name: prop.nm,
      value: extractAnimatedValue(prop.v)
    })) || []
  }));
}

/**
 * Get effect type name.
 */
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

/**
 * Extract masks.
 */
function extractMasks(masks) {
  return masks.map(mask => ({
    name: mask.nm,
    mode: getMaskMode(mask.mode),
    inverted: mask.inv,
    path: extractPath(mask.pt),
    opacity: extractAnimatedValue(mask.o),
    expansion: extractAnimatedValue(mask.x)
  }));
}

/**
 * Get mask mode name.
 */
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

/**
 * Get blend mode name.
 */
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

/**
 * Get matte mode name.
 */
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

/**
 * Extract assets (precomps, images).
 */
function extractAssets(assets) {
  return assets.map(asset => {
    if (asset.layers) {
      // Precomp
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
      // Image
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

/**
 * Extract fonts.
 */
function extractFonts(fonts) {
  if (!fonts || !fonts.list) return [];
  
  return fonts.list.map(font => ({
    family: font.fFamily,
    name: font.fName,
    style: font.fStyle,
    path: font.fPath,
    weight: font.fWeight,
    origin: font.origin  // 0=local, 1=CSS/Google, 2=script/typekit, 3=fontURL
  }));
}

/**
 * Extract markers.
 */
function extractMarkers(markers) {
  return markers.map(marker => ({
    name: marker.cm,
    time: marker.tm,
    duration: marker.dr
  }));
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // motion path extraction
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Extract all motion paths from layers (position animations with spatial tangents).
 */
function extractAllMotionPaths(layers) {
  const paths = [];
  
  for (const layer of layers) {
    // Check position animation
    if (layer.ks?.p?.a === 1) {
      const keyframes = layer.ks.p.k;
      
      // Motion path exists when we have spatial tangents
      const hasMotionPath = keyframes.some(kf => kf.to && kf.ti);
      
      if (hasMotionPath) {
        paths.push({
          layerName: layer.nm,
          layerIndex: layer.ind,
          keyframes: keyframes.map(kf => ({
            time: kf.t,
            position: kf.s,
            to: kf.to,  // Spatial out tangent
            ti: kf.ti,  // Spatial in tangent
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
    
    // Check shape paths
    if (layer.shapes) {
      const shapePaths = extractShapeMotionPaths(layer.shapes, layer.nm);
      paths.push(...shapePaths);
    }
  }
  
  return paths;
}

/**
 * Extract animated paths from shapes.
 */
function extractShapeMotionPaths(shapes, layerName) {
  const paths = [];
  
  for (const shape of shapes) {
    if (shape.ty === "gr") {
      // Recurse into groups
      const groupPaths = extractShapeMotionPaths(shape.it || [], layerName);
      paths.push(...groupPaths);
    }
    
    if (shape.ty === "sh" && shape.ks?.a === 1) {
      // Animated path
      paths.push({
        type: "shapePath",
        layerName,
        shapeName: shape.nm,
        keyframes: shape.ks.k.map(kf => ({
          time: kf.t,
          path: parsePathData(kf.s?.[0] || kf.s)
        }))
      });
    }
  }
  
  return paths;
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
