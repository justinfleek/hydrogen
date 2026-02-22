// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // eventbus
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

export const traverseImpl = (f) => (arr) => () => {
  const results = [];
  for (let i = 0; i < arr.length; i++) {
    results.push(f(arr[i])());
  }
  return results;
};

export const logEvent = (maybeName) => (event) => () => {
  const busName = maybeName ? `[${maybeName.value0}]` : "[EventBus]";
  console.log(`${busName} Event:`, event);
};

export const nowImpl = () => Date.now();

export const mapImpl = (f) => (arr) => arr.map(f);

// Typed channel support for heterogeneous events
const eventTypeKey = Symbol("hydrogen.event.type");

export const wrapEvent = (typeName) => (event) => {
  return { [eventTypeKey]: typeName, payload: event };
};

export const unwrapEvent = (typeName) => (anyEvent) => {
  if (anyEvent && anyEvent[eventTypeKey] === typeName) {
    return anyEvent.payload; // Just
  }
  return null; // Nothing
};
