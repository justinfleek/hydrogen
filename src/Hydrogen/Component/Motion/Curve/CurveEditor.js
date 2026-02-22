// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                       // hydrogen // component // motion // curve // curveeditor
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for CurveEditor.purs

// | Extract clientX from a mouse event
export const getClientX = function(event) {
  return event.clientX;
};

// | Extract clientY from a mouse event
export const getClientY = function(event) {
  return event.clientY;
};

// | Get element bounding rect left
export const getTargetLeft = function(event) {
  var target;
  if (event.currentTarget && event.currentTarget.getBoundingClientRect) {
    target = event.currentTarget.getBoundingClientRect();
    return target.left;
  }
  return 0;
};

// | Get element bounding rect top
export const getTargetTop = function(event) {
  var target;
  if (event.currentTarget && event.currentTarget.getBoundingClientRect) {
    target = event.currentTarget.getBoundingClientRect();
    return target.top;
  }
  return 0;
};
