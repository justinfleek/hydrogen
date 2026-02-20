// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                    // hydrogen // colorpicker
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Color picker interaction handling and color utilities

/**
 * Clamp a value between min and max
 */
const clamp = (value, min, max) => Math.min(Math.max(value, min), max);

/**
 * Initialize saturation panel pointer events
 */
export const initSaturationPanelImpl = (element, onChange, opts) => {
  let isDragging = false;

  const calculateSV = (e) => {
    const rect = element.getBoundingClientRect();
    const x = clamp((e.clientX - rect.left) / rect.width, 0, 1);
    const y = clamp((e.clientY - rect.top) / rect.height, 0, 1);
    return {
      s: x * 100,
      v: (1 - y) * 100,
    };
  };

  const handlePointerDown = (e) => {
    isDragging = true;
    element.setPointerCapture(e.pointerId);
    const sv = calculateSV(e);
    onChange(sv)();
  };

  const handlePointerMove = (e) => {
    if (!isDragging) return;
    const sv = calculateSV(e);
    onChange(sv)();
  };

  const handlePointerUp = (e) => {
    if (isDragging) {
      isDragging = false;
      element.releasePointerCapture(e.pointerId);
    }
  };

  element.addEventListener("pointerdown", handlePointerDown);
  element.addEventListener("pointermove", handlePointerMove);
  element.addEventListener("pointerup", handlePointerUp);
  element.addEventListener("pointercancel", handlePointerUp);

  return {
    element,
    cleanup: () => {
      element.removeEventListener("pointerdown", handlePointerDown);
      element.removeEventListener("pointermove", handlePointerMove);
      element.removeEventListener("pointerup", handlePointerUp);
      element.removeEventListener("pointercancel", handlePointerUp);
    },
  };
};

/**
 * Initialize hue slider pointer events
 */
export const initHueSliderImpl = (element, onChange) => {
  let isDragging = false;

  const calculateHue = (e) => {
    const rect = element.getBoundingClientRect();
    const x = clamp((e.clientX - rect.left) / rect.width, 0, 1);
    return x * 360;
  };

  const handlePointerDown = (e) => {
    isDragging = true;
    element.setPointerCapture(e.pointerId);
    onChange(calculateHue(e))();
  };

  const handlePointerMove = (e) => {
    if (!isDragging) return;
    onChange(calculateHue(e))();
  };

  const handlePointerUp = (e) => {
    if (isDragging) {
      isDragging = false;
      element.releasePointerCapture(e.pointerId);
    }
  };

  element.addEventListener("pointerdown", handlePointerDown);
  element.addEventListener("pointermove", handlePointerMove);
  element.addEventListener("pointerup", handlePointerUp);
  element.addEventListener("pointercancel", handlePointerUp);

  return {
    element,
    cleanup: () => {
      element.removeEventListener("pointerdown", handlePointerDown);
      element.removeEventListener("pointermove", handlePointerMove);
      element.removeEventListener("pointerup", handlePointerUp);
      element.removeEventListener("pointercancel", handlePointerUp);
    },
  };
};

/**
 * Initialize alpha slider pointer events
 */
export const initAlphaSliderImpl = (element, onChange) => {
  let isDragging = false;

  const calculateAlpha = (e) => {
    const rect = element.getBoundingClientRect();
    return clamp((e.clientX - rect.left) / rect.width, 0, 1);
  };

  const handlePointerDown = (e) => {
    isDragging = true;
    element.setPointerCapture(e.pointerId);
    onChange(calculateAlpha(e))();
  };

  const handlePointerMove = (e) => {
    if (!isDragging) return;
    onChange(calculateAlpha(e))();
  };

  const handlePointerUp = (e) => {
    if (isDragging) {
      isDragging = false;
      element.releasePointerCapture(e.pointerId);
    }
  };

  element.addEventListener("pointerdown", handlePointerDown);
  element.addEventListener("pointermove", handlePointerMove);
  element.addEventListener("pointerup", handlePointerUp);
  element.addEventListener("pointercancel", handlePointerUp);

  return {
    element,
    cleanup: () => {
      element.removeEventListener("pointerdown", handlePointerDown);
      element.removeEventListener("pointermove", handlePointerMove);
      element.removeEventListener("pointerup", handlePointerUp);
      element.removeEventListener("pointercancel", handlePointerUp);
    },
  };
};

/**
 * Cleanup color picker element
 */
export const destroyColorPickerImpl = (pickerObj) => {
  if (pickerObj && pickerObj.cleanup) {
    pickerObj.cleanup();
  }
};

/**
 * Open eyedropper (EyeDropper API)
 */
export const openEyedropperImpl = (onColor) => {
  if (!("EyeDropper" in window)) {
    console.warn("EyeDropper API not supported");
    return;
  }

  const eyeDropper = new window.EyeDropper();
  eyeDropper
    .open()
    .then((result) => {
      onColor(result.sRGBHex)();
    })
    .catch((err) => {
      // User cancelled or error
      console.log("EyeDropper cancelled:", err);
    });
};

/**
 * Copy text to clipboard
 */
export const copyToClipboardImpl = (text) => {
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text).catch((err) => {
      console.error("Failed to copy:", err);
      fallbackCopy(text);
    });
  } else {
    fallbackCopy(text);
  }
};

/**
 * Fallback copy using textarea
 */
const fallbackCopy = (text) => {
  const textarea = document.createElement("textarea");
  textarea.value = text;
  textarea.style.position = "fixed";
  textarea.style.opacity = "0";
  document.body.appendChild(textarea);
  textarea.select();
  try {
    document.execCommand("copy");
  } catch (err) {
    console.error("Fallback copy failed:", err);
  }
  document.body.removeChild(textarea);
};

/**
 * Check if eyedropper is supported
 */
export const isEyedropperSupportedImpl = () => {
  return "EyeDropper" in window;
};

/**
 * Map implementation for arrays
 */
export const mapImpl = (f) => (arr) => arr.map(f);

/**
 * Parse hex pair to integer
 */
export const parseHexPairImpl = (hex) => {
  return parseInt(hex, 16) || 0;
};

/**
 * Parse RGB/RGBA string
 */
export const parseRgbStringImpl = (str) => {
  const match = str.match(
    /rgba?\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*(?:,\s*([\d.]+))?\s*\)/i
  );
  if (match) {
    return {
      just: {
        r: parseInt(match[1], 10),
        g: parseInt(match[2], 10),
        b: parseInt(match[3], 10),
        a: match[4] !== undefined ? parseFloat(match[4]) : 1.0,
      },
    };
  }
  return { nothing: true };
};

/**
 * Parse HSL/HSLA string
 */
export const parseHslStringImpl = (str) => {
  const match = str.match(
    /hsla?\s*\(\s*(\d+)\s*,\s*(\d+)%?\s*,\s*(\d+)%?\s*(?:,\s*([\d.]+))?\s*\)/i
  );
  if (match) {
    const h = parseInt(match[1], 10);
    const s = parseInt(match[2], 10);
    const l = parseInt(match[3], 10);
    const a = match[4] !== undefined ? parseFloat(match[4]) : 1.0;
    // Convert HSL to RGB
    const rgb = hslToRgb(h, s, l, a);
    return { just: rgb };
  }
  return { nothing: true };
};

/**
 * HSL to RGB conversion
 */
const hslToRgb = (h, s, l, a) => {
  s /= 100;
  l /= 100;

  const c = (1 - Math.abs(2 * l - 1)) * s;
  const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
  const m = l - c / 2;

  let r, g, b;
  if (h < 60) {
    [r, g, b] = [c, x, 0];
  } else if (h < 120) {
    [r, g, b] = [x, c, 0];
  } else if (h < 180) {
    [r, g, b] = [0, c, x];
  } else if (h < 240) {
    [r, g, b] = [0, x, c];
  } else if (h < 300) {
    [r, g, b] = [x, 0, c];
  } else {
    [r, g, b] = [c, 0, x];
  }

  return {
    r: Math.round((r + m) * 255),
    g: Math.round((g + m) * 255),
    b: Math.round((b + m) * 255),
    a: a,
  };
};
