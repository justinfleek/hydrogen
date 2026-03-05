// FFI for Hydrogen.HTML.Renderer
// Static HTML rendering utilities

// Convert a PropValue to its string representation
export const propValueToString = value => {
  if (value === null || value === undefined) return '';
  if (typeof value === 'boolean') return value ? 'true' : 'false';
  if (typeof value === 'number') return String(value);
  if (typeof value === 'string') return value;
  return String(value);
};
