// FFI for Hydrogen.UI.AriaHider
// Effect-based ARIA hiding for modal dialogs (Halogen compatibility)

// Hide all siblings of an element from screen readers
export const hideOthers = element => () => {
  const state = {
    // Store original aria-hidden values for restoration
    hidden: []
  };
  
  // Walk up to find all siblings that need hiding
  const hideFromRoot = (node, exclude) => {
    if (!node || !node.parentElement) return;
    
    const parent = node.parentElement;
    const siblings = parent.children;
    
    for (let i = 0; i < siblings.length; i++) {
      const sibling = siblings[i];
      if (sibling !== node && sibling.nodeType === 1) {
        // Store original state
        const original = sibling.getAttribute('aria-hidden');
        state.hidden.push({
          element: sibling,
          original: original
        });
        // Hide from screen readers
        sibling.setAttribute('aria-hidden', 'true');
      }
    }
    
    // Continue up the tree
    if (parent !== document.body && parent !== document.documentElement) {
      hideFromRoot(parent, exclude);
    }
  };
  
  hideFromRoot(element, element);
  return state;
};

// Restore original aria-hidden values
export const restoreOthers = state => () => {
  if (!state || !state.hidden) return;
  
  for (const item of state.hidden) {
    if (item.original === null) {
      item.element.removeAttribute('aria-hidden');
    } else {
      item.element.setAttribute('aria-hidden', item.original);
    }
  }
};
