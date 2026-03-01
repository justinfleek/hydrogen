// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // presence
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// BROWSER BOUNDARY: Enter/exit animations for components
//
// This entire file is browser boundary code:
// - MutationObserver for DOM changes
// - requestAnimationFrame for animation timing
// - CSS transition event listeners
// - DOM element style manipulation
// - WeakMap for element state tracking
//
// All presence state and variant logic is pure data in PureScript:
// - Hydrogen.Motion.Presence.PresenceState
// - Hydrogen.Motion.Presence.Variant
// - Hydrogen.Motion.Presence.interpolate
// - Hydrogen.Motion.Presence.variantToRecord

// ═══════════════════════════════════════════════════════════════════════════════
//                                           // browser boundary // presence state
// ═══════════════════════════════════════════════════════════════════════════════

// BROWSER BOUNDARY: WeakMap for tracking DOM element state
const presenceStates = new WeakMap();

// BROWSER BOUNDARY: Reads mutable state from WeakMap
export const usePresenceImpl = (element) => () => {
  const state = presenceStates.get(element) || { state: "present", isPresent: true };
  return state;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                          // browser boundary // animate presence
// ═══════════════════════════════════════════════════════════════════════════════

// BROWSER BOUNDARY: DOM queries, MutationObserver, event listeners
const initAnimatePresence = () => {
  const containers = document.querySelectorAll("[data-animate-presence]");
  
  for (const container of containers) {
    if (container._presenceInitialized) continue;
    container._presenceInitialized = true;
    
    const mode = container.getAttribute("data-presence-mode") || "sync";
    const initial = container.getAttribute("data-presence-initial") !== "false";
    
    // Observe children for mount/unmount
    const observer = new MutationObserver((mutations) => {
      for (const mutation of mutations) {
        // Handle added nodes
        for (const node of mutation.addedNodes) {
          if (node.nodeType === 1 && node.hasAttribute("data-motion")) {
            handleEnter(node, initial, mode);
          }
        }
        
        // Handle removed nodes
        for (const node of mutation.removedNodes) {
          if (node.nodeType === 1 && node.hasAttribute("data-motion")) {
            handleExit(node, mode, container);
          }
        }
      }
    });
    
    observer.observe(container, { childList: true });
    
    // Initial animation for existing children
    if (initial) {
      const motionElements = container.querySelectorAll("[data-motion]");
      for (const el of motionElements) {
        handleEnter(el, true, mode);
      }
    }
  }
};

// BROWSER BOUNDARY: DOM style manipulation, requestAnimationFrame, transitionend events
const handleEnter = (element, animate, mode) => {
  if (!animate) {
    presenceStates.set(element, { state: "present", isPresent: true });
    return;
  }
  
  presenceStates.set(element, { state: "entering", isPresent: true });
  
  const initialVariant = parseVariant(element.getAttribute("data-motion-initial"));
  const animateVariant = parseVariant(element.getAttribute("data-motion-animate"));
  
  // Apply initial state
  applyVariant(element, initialVariant);
  
  // Trigger animation
  requestAnimationFrame(() => {
    requestAnimationFrame(() => {
      element.style.transition = buildTransition(animateVariant);
      applyVariant(element, animateVariant);
      
      const onEnd = () => {
        presenceStates.set(element, { state: "present", isPresent: true });
        element.removeEventListener("transitionend", onEnd);
        
        // Trigger callback
        if (element.hasAttribute("data-motion-on-complete")) {
          element.dispatchEvent(new CustomEvent("motion:complete"));
        }
      };
      
      element.addEventListener("transitionend", onEnd);
      
      // Trigger start callback
      if (element.hasAttribute("data-motion-on-start")) {
        element.dispatchEvent(new CustomEvent("motion:start"));
      }
    });
  });
};

// BROWSER BOUNDARY: DOM cloning, getBoundingClientRect, style manipulation
const handleExit = (element, mode, container) => {
  const exitVariant = parseVariant(element.getAttribute("data-motion-exit"));
  
  if (!exitVariant || Object.keys(exitVariant).length === 0) {
    return; // No exit animation
  }
  
  presenceStates.set(element, { state: "exiting", isPresent: false });
  
  // Clone element for exit animation
  const clone = element.cloneNode(true);
  
  if (mode === "pop-layout") {
    // Position absolutely to pop out of layout
    const rect = element.getBoundingClientRect();
    clone.style.position = "fixed";
    clone.style.top = rect.top + "px";
    clone.style.left = rect.left + "px";
    clone.style.width = rect.width + "px";
    clone.style.height = rect.height + "px";
    clone.style.pointerEvents = "none";
  }
  
  container.appendChild(clone);
  
  // Animate exit
  requestAnimationFrame(() => {
    clone.style.transition = buildTransition(exitVariant);
    applyVariant(clone, exitVariant);
    
    const onEnd = () => {
      clone.remove();
      clone.removeEventListener("transitionend", onEnd);
      
      // Trigger exit complete callback
      if (element.hasAttribute("data-motion-on-exit")) {
        element.dispatchEvent(new CustomEvent("motion:exit"));
      }
    };
    
    clone.addEventListener("transitionend", onEnd);
  });
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                              // browser boundary // css variants
// ═══════════════════════════════════════════════════════════════════════════════

// BROWSER BOUNDARY: JSON parsing from DOM data attributes
// Pure variant logic is in PureScript: Hydrogen.Motion.Presence.Variant
const parseVariant = (str) => {
  if (!str) return {};
  try {
    return JSON.parse(str);
  } catch {
    return {};
  }
};

// BROWSER BOUNDARY: Direct DOM style manipulation
const applyVariant = (element, variant) => {
  if (variant.opacity !== undefined) {
    element.style.opacity = variant.opacity;
  }
  
  const transforms = [];
  if (variant.scale !== undefined) {
    transforms.push(`scale(${variant.scale})`);
  }
  if (variant.scaleX !== undefined) {
    transforms.push(`scaleX(${variant.scaleX})`);
  }
  if (variant.scaleY !== undefined) {
    transforms.push(`scaleY(${variant.scaleY})`);
  }
  if (variant.x !== undefined) {
    transforms.push(`translateX(${variant.x}px)`);
  }
  if (variant.y !== undefined) {
    transforms.push(`translateY(${variant.y}px)`);
  }
  if (variant.rotate !== undefined) {
    transforms.push(`rotate(${variant.rotate}deg)`);
  }
  
  if (transforms.length > 0) {
    element.style.transform = transforms.join(" ");
  }
};

// BROWSER BOUNDARY: CSS transition string building for DOM
const buildTransition = (variant) => {
  const duration = variant.duration || 300;
  const delay = variant.delay || 0;
  const easing = variant.easing || "ease-out";
  
  const props = [];
  if (variant.opacity !== undefined) props.push("opacity");
  if (variant.scale !== undefined || variant.scaleX !== undefined || 
      variant.scaleY !== undefined || variant.x !== undefined || 
      variant.y !== undefined || variant.rotate !== undefined) {
    props.push("transform");
  }
  
  if (props.length === 0) props.push("all");
  
  return props.map((p) => `${p} ${duration}ms ${easing} ${delay}ms`).join(", ");
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                            // browser boundary // initialization
// ═══════════════════════════════════════════════════════════════════════════════

// Auto-initialize when DOM is ready
if (typeof document !== "undefined") {
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initAnimatePresence);
  } else {
    initAnimatePresence();
  }
  
  // Re-initialize on dynamic content
  const bodyObserver = new MutationObserver(() => {
    initAnimatePresence();
  });
  
  if (document.body) {
    bodyObserver.observe(document.body, { childList: true, subtree: true });
  }
}
