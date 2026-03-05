// FFI stubs for Hydrogen.UI.Drag.DocumentEvents
"use strict";

export const setupDragImpl = (callbacks) => () => {
  const handle = { active: false };
  
  const onMouseMove = (e) => {
    if (handle.active) {
      callbacks.onDrag({ x: e.clientX, y: e.clientY })();
    }
  };
  
  const onMouseUp = (e) => {
    handle.active = false;
    callbacks.onEnd({ x: e.clientX, y: e.clientY })();
  };
  
  document.addEventListener('mousemove', onMouseMove);
  document.addEventListener('mouseup', onMouseUp);
  
  return handle;
};

export const startDragImpl = (handle) => () => {
  handle.active = true;
};

export const getMovementXImpl = (handle) => () => 0;
export const getMovementYImpl = (handle) => () => 0;
export const getClientXImpl = (handle) => () => 0;
export const getClientYImpl = (handle) => () => 0;
export const stopDragImpl = (handle) => () => { handle.active = false; };
