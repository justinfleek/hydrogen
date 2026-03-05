// FFI stubs for Hydrogen.UI.FocusTrap
"use strict";

export const createFocusScopeImpl = (el) => () => {
  return { element: el, active: false };
};

export const activateImpl = (scope) => () => {
  scope.active = true;
};

export const deactivateImpl = (scope) => () => {
  scope.active = false;
};

export const refEq = (a) => (b) => a === b;
export const elementToHTMLElementImpl = (el) => () => el;
export const isVisible = (el) => () => {
  if (!el) return false;
  const style = window.getComputedStyle(el);
  return style.display !== 'none' && style.visibility !== 'hidden';
};
