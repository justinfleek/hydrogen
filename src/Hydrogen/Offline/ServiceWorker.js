// FFI for Hydrogen.Offline.ServiceWorker
// Service Worker registration and messaging

export const isAvailableImpl = () => 
  typeof navigator !== 'undefined' && 'serviceWorker' in navigator;

export const isControlledImpl = () => 
  typeof navigator !== 'undefined' && 
  navigator.serviceWorker && 
  navigator.serviceWorker.controller !== null;

export const isSupportedImpl = () => 'serviceWorker' in navigator;

export const getRegistrationImpl = onSuccess => onError => () => {
  if (!('serviceWorker' in navigator)) {
    onError("Service workers not supported")();
    return;
  }
  navigator.serviceWorker.getRegistration().then(
    reg => onSuccess(reg || null)(),
    err => onError(err.message)()
  );
};

export const registerImpl = url => options => () => {
  if ('serviceWorker' in navigator) {
    return navigator.serviceWorker.register(url, options);
  }
  return Promise.reject(new Error('Service workers not supported'));
};

export const unregisterImpl = registration => onSuccess => onError => () => {
  registration.unregister().then(
    result => onSuccess(result)(),
    err => onError(err.message)()
  );
};

export const updateImpl = registration => onSuccess => onError => () => {
  registration.update().then(
    () => onSuccess()(),
    err => onError(err.message)()
  );
};

export const skipWaitingImpl = registration => () => {
  if (registration.waiting) {
    registration.waiting.postMessage({ type: 'SKIP_WAITING' });
  }
};

export const postMessageImpl = message => () => {
  if (navigator.serviceWorker.controller) {
    navigator.serviceWorker.controller.postMessage(message);
  }
};

export const onMessageImpl = callback => () => {
  const handler = event => callback(event.data)();
  navigator.serviceWorker.addEventListener('message', handler);
  return () => navigator.serviceWorker.removeEventListener('message', handler);
};

export const onStateChangeImpl = registration => callback => () => {
  const worker = registration.installing || registration.waiting || registration.active;
  if (worker) {
    const handler = () => callback(worker.state)();
    worker.addEventListener('statechange', handler);
    return () => worker.removeEventListener('statechange', handler);
  }
  return () => {};
};

export const onUpdateFoundImpl = registration => callback => () => {
  const handler = () => callback()();
  registration.addEventListener('updatefound', handler);
  return () => registration.removeEventListener('updatefound', handler);
};
