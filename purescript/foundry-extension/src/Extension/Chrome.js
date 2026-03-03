// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // extension // chrome // ffi.js
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

"use strict";

/**
 * Query the active tab in the current window.
 * 
 * @param {Function} onSuccess - Callback with Tab object
 * @param {Function} onError - Callback with error string
 * @returns {Function} - Effect thunk
 */
export const queryActiveTabImpl = onSuccess => onError => () => {
  chrome.tabs.query({ active: true, currentWindow: true }, tabs => {
    if (chrome.runtime.lastError) {
      onError(chrome.runtime.lastError.message)();
    } else if (tabs && tabs.length > 0) {
      const tab = tabs[0];
      onSuccess({
        id: tab.id,
        url: tab.url || "",
        title: tab.title || "",
        windowId: tab.windowId
      })();
    } else {
      onError("No active tab found")();
    }
  });
};

/**
 * Send a message to a specific tab's content script.
 * 
 * @param {number} tabId - Target tab ID
 * @param {Object} message - Message to send (Foreign)
 * @param {Function} onSuccess - Callback with response
 * @param {Function} onError - Callback with error string
 * @returns {Function} - Effect thunk
 */
export const sendMessageToTabImpl = tabId => message => onSuccess => onError => () => {
  chrome.tabs.sendMessage(tabId, message, response => {
    if (chrome.runtime.lastError) {
      onError(chrome.runtime.lastError.message)();
    } else {
      onSuccess(response)();
    }
  });
};

/**
 * Send a message to the background script.
 * 
 * @param {Object} message - Message to send (Foreign)
 * @param {Function} onSuccess - Callback with response
 * @param {Function} onError - Callback with error string
 * @returns {Function} - Effect thunk
 */
export const sendMessageToBackgroundImpl = message => onSuccess => onError => () => {
  chrome.runtime.sendMessage(message, response => {
    if (chrome.runtime.lastError) {
      onError(chrome.runtime.lastError.message)();
    } else {
      onSuccess(response)();
    }
  });
};
