// FFI for Hydrogen.Target.DOM
// DOM rendering and manipulation

export const renderToElementImpl = element => el => () => {
  console.warn("DOM.renderToElement: stub implementation");
  return { element: null, cleanup: () => {} };
};

export const createDocument = () => () => document;

export const getElementByIdImpl = id => () => document.getElementById(id);

// Set a namespaced attribute
export const setAttributeNS = namespace => name => value => element => () => {
  if (namespace) {
    element.setAttributeNS(namespace, name, value);
  } else {
    element.setAttribute(name, value);
  }
};

// Set a DOM property directly
export const setProperty = name => value => element => () => {
  element[name] = value;
};

// Set a style property
export const setStyleProperty = name => value => element => () => {
  element.style[name] = value;
};
