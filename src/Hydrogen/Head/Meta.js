// FFI for Hydrogen.Head.Meta
// Document head manipulation (title, meta tags, links, favicon)

export const setTitleImpl = title => () => {
  document.title = title;
};

export const getTitleImpl = () => document.title;

export const setMetaImpl = name => content => () => {
  let meta = document.querySelector(`meta[name="${name}"]`);
  if (!meta) {
    meta = document.createElement('meta');
    meta.name = name;
    document.head.appendChild(meta);
  }
  meta.content = content;
};

export const removeMetaImpl = name => () => {
  const meta = document.querySelector(`meta[name="${name}"]`);
  if (meta) meta.remove();
};

export const getMetaImpl = name => () => {
  const meta = document.querySelector(`meta[name="${name}"]`);
  return meta ? meta.content : null;
};

export const addLinkImpl = rel => href => type => () => {
  let link = document.querySelector(`link[rel="${rel}"][href="${href}"]`);
  if (!link) {
    link = document.createElement('link');
    link.rel = rel;
    link.href = href;
    if (type) link.type = type;
    document.head.appendChild(link);
  }
};

export const removeLinkImpl = href => () => {
  const link = document.querySelector(`link[href="${href}"]`);
  if (link) link.remove();
};

export const setFaviconImpl = href => () => {
  let link = document.querySelector('link[rel="icon"]');
  if (!link) {
    link = document.createElement('link');
    link.rel = 'icon';
    document.head.appendChild(link);
  }
  link.href = href;
};
