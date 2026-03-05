// FFI for Hydrogen.Router
// Effect-based browser routing operations

export const getPathname = () => window.location.pathname;

export const getHostname = () => window.location.hostname;

export const getOrigin = () => window.location.origin;

export const pushState = url => () => {
  window.history.pushState({}, '', url);
};

export const replaceState = url => () => {
  window.history.replaceState({}, '', url);
};

export const onPopState = callback => () => {
  const handler = () => {
    callback(window.location.pathname)();
  };
  window.addEventListener('popstate', handler);
  return () => window.removeEventListener('popstate', handler);
};

export const interceptLinks = callback => () => {
  const handler = event => {
    const link = event.target.closest('a');
    if (!link) return;
    
    const href = link.getAttribute('href');
    if (!href) return;
    
    // Only intercept relative paths (not external links)
    if (href.startsWith('/') && !href.startsWith('//')) {
      event.preventDefault();
      callback(href)();
    }
  };
  
  document.addEventListener('click', handler);
  return () => document.removeEventListener('click', handler);
};
