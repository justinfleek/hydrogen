// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // clipboard
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// BROWSER BOUNDARY: These FFIs wrap navigator.clipboard (Async Clipboard API)
// and ClipboardEvent.clipboardData (Clipboard Events API).
//
// Corresponding PureScript module: Hydrogen.Util.Clipboard (pending creation)
// Schema types: see Hydrogen.Schema.Storage.Clipboard for pure ADT types.

// BROWSER BOUNDARY: navigator.clipboard.writeText() with document.execCommand fallback
export const copyToClipboardImpl = (text) => (onError) => (onSuccess) => () => {
  // Try modern Clipboard API first
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text)
      .then(() => onSuccess())
      .catch((err) => onError(new Error(err.message || "Failed to copy")));
    return;
  }
  
  // Fallback to execCommand
  try {
    const textarea = document.createElement("textarea");
    textarea.value = text;
    textarea.style.position = "fixed";
    textarea.style.left = "-9999px";
    textarea.style.top = "-9999px";
    document.body.appendChild(textarea);
    textarea.select();
    textarea.setSelectionRange(0, textarea.value.length);
    
    const success = document.execCommand("copy");
    document.body.removeChild(textarea);
    
    if (success) {
      onSuccess();
    } else {
      onError(new Error("execCommand copy failed"))();
    }
  } catch (err) {
    onError(err)();
  }
};

// BROWSER BOUNDARY: navigator.clipboard.readText() for reading clipboard contents
export const readFromClipboardImpl = (onError) => (onSuccess) => () => {
  if (navigator.clipboard && navigator.clipboard.readText) {
    navigator.clipboard.readText()
      .then((text) => onSuccess(text)())
      .catch((err) => onError(new Error(err.message || "Failed to read clipboard"))());
    return;
  }
  
  onError(new Error("Clipboard API not supported"))();
};

// BROWSER BOUNDARY: ClipboardEvent.clipboardData for paste event handling
export const getClipboardData = (event) => () => {
  const data = event.clipboardData;
  if (data) {
    const text = data.getData("text/plain");
    return text || null;
  }
  return null;
};

// Note: Result reference helpers removed.
// Use Effect.Ref from PureScript for mutable references.
