// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // extension // response // ffi
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

/**
 * Parse Foreign to RawResponse.
 * 
 * Safely extracts fields with defaults for missing values.
 * This matches the expected shape from background.js.
 * 
 * @param {Object} foreign - The Foreign value from JS
 * @returns {Object} - RawResponse record
 */
export const parseRawResponse = function(foreign) {
  // Default to failed response if foreign is invalid
  if (!foreign || typeof foreign !== "object") {
    return {
      success: false,
      error: "Invalid response object",
      data: null
    };
  }

  // Extract success flag
  const success = !!foreign.success;
  
  // Extract error message
  const error = foreign.error || null;
  
  // Extract data payload
  let data = null;
  if (foreign.data && typeof foreign.data === "object") {
    const rawData = foreign.data;
    
    // Extract screenshot (nullable string)
    const screenshot = typeof rawData.screenshot === "string" 
      ? rawData.screenshot 
      : null;
    
    // Extract extraction data
    let extraction = null;
    if (rawData.extraction && typeof rawData.extraction === "object") {
      const ext = rawData.extraction;
      extraction = {
        url: typeof ext.url === "string" ? ext.url : "",
        title: typeof ext.title === "string" ? ext.title : "",
        count: typeof ext.count === "number" ? ext.count : 0,
        layerCount: typeof ext.layerCount === "number" ? ext.layerCount : 0,
        layers: Array.isArray(ext.layers) 
          ? ext.layers.map(function(layer) {
              return {
                zIndex: typeof layer.zIndex === "number" ? layer.zIndex : 0,
                count: typeof layer.count === "number" ? layer.count : 0
              };
            })
          : []
      };
    }
    
    data = {
      screenshot: screenshot,
      extraction: extraction
    };
  }
  
  return {
    success: success,
    error: error,
    data: data
  };
};
