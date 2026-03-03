// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                            // foundry // extension // background
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Service worker that coordinates between content scripts and popup.
// Handles message routing and screenshot capture via chrome.tabs API.
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

/**
 * Capture visible tab as screenshot.
 * Uses chrome.tabs.captureVisibleTab which requires activeTab permission.
 * 
 * @param {number} tabId - Tab ID to capture
 * @returns {Promise<string>} - Data URL of screenshot
 */
async function captureTabScreenshot(tabId) {
  const tab = await chrome.tabs.get(tabId);
  if (!tab.windowId) throw new Error("Tab has no window");
  
  const dataUrl = await chrome.tabs.captureVisibleTab(tab.windowId, {
    format: "png",
    quality: 100
  });
  
  return dataUrl;
}

/**
 * Extract elements from a tab using instant snapshot.
 * Sends message to content script and awaits response.
 * Uses the full 38-pillar extraction system.
 * 
 * @param {number} tabId - Tab ID to extract from
 * @returns {Promise<Object>} - Extraction result with all pillar data
 */
async function extractFromTab(tabId) {
  return new Promise((resolve, reject) => {
    chrome.tabs.sendMessage(tabId, { action: "instantSnapshot" }, response => {
      if (chrome.runtime.lastError) {
        reject(new Error(chrome.runtime.lastError.message));
      } else if (response && response.success) {
        resolve(response.data);
      } else {
        reject(new Error(response?.error || "Extraction failed"));
      }
    });
  });
}

/**
 * Extract elements with full 30-second interaction recording.
 * Tests hover effects, focus states, scroll animations.
 * 
 * @param {number} tabId - Tab ID to extract from
 * @returns {Promise<Object>} - Full recording with interaction data
 */
async function fullRecordingFromTab(tabId) {
  return new Promise((resolve, reject) => {
    chrome.tabs.sendMessage(tabId, { action: "fullRecording" }, response => {
      if (chrome.runtime.lastError) {
        reject(new Error(chrome.runtime.lastError.message));
      } else if (response && response.success) {
        resolve(response.data);
      } else {
        reject(new Error(response?.error || "Recording failed"));
      }
    });
  });
}

/**
 * Full extraction: screenshot + element data.
 * 
 * @param {number} tabId - Tab ID
 * @returns {Promise<Object>} - { screenshot, extraction }
 */
async function fullExtraction(tabId) {
  // Capture screenshot first (before any DOM changes)
  const screenshot = await captureTabScreenshot(tabId);
  
  // Then extract elements
  const extraction = await extractFromTab(tabId);
  
  return {
    screenshot,
    extraction
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // message handling
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Listen for messages from popup.
 */
chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
  if (request.action === "fullExtract") {
    const tabId = request.tabId;
    fullExtraction(tabId)
      .then(result => sendResponse({ success: true, data: result }))
      .catch(err => sendResponse({ success: false, error: err.message }));
    return true; // Async response
  }

  if (request.action === "screenshot") {
    const tabId = request.tabId;
    captureTabScreenshot(tabId)
      .then(dataUrl => sendResponse({ success: true, data: dataUrl }))
      .catch(err => sendResponse({ success: false, error: err.message }));
    return true;
  }

  if (request.action === "extract") {
    const tabId = request.tabId;
    extractFromTab(tabId)
      .then(data => sendResponse({ success: true, data }))
      .catch(err => sendResponse({ success: false, error: err.message }));
    return true;
  }

  if (request.action === "fullRecording") {
    const tabId = request.tabId;
    fullRecordingFromTab(tabId)
      .then(data => sendResponse({ success: true, data }))
      .catch(err => sendResponse({ success: false, error: err.message }));
    return true;
  }

  return false;
});

// Log service worker start
console.log("[Foundry] Background service worker started");
