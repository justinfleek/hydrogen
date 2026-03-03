# Foundry Browser Extension

Extract visual DNA from any website into Hydrogen Schema atoms.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Browser Extension                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────┐    ┌─────────────────┐    ┌──────────────────┐   │
│  │ Content      │    │ Background      │    │ Popup            │   │
│  │ Script       │◄──►│ Service Worker  │◄──►│ (Halogen)        │   │
│  │              │    │                 │    │                  │   │
│  │ - Extract    │    │ - Screenshot    │    │ - Display        │   │
│  │   computed   │    │   capture       │    │   results        │   │
│  │   styles     │    │ - Message       │    │ - Layer          │   │
│  │ - Build      │    │   routing       │    │   inspector      │   │
│  │   layer tree │    │                 │    │                  │   │
│  └──────────────┘    └─────────────────┘    └──────────────────┘   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
                                │
                                ▼
                    ┌───────────────────────┐
                    │   Hydrogen Schema     │
                    │   Atoms               │
                    │                       │
                    │   - OKLCH colors      │
                    │   - Pixel dimensions  │
                    │   - FontWeight 1-1000 │
                    │   - ZIndex integers   │
                    │   - UUID5 layer IDs   │
                    └───────────────────────┘
```

## Files

```
extension/
├── manifest.json      # Chrome extension manifest v3
├── content.js         # Runs on every page, extracts styles
├── background.js      # Service worker, screenshot capture
├── popup.html         # Extension popup HTML
├── popup.css          # OKLCH-based styling
├── popup.js           # Compiled from PureScript (spago bundle)
└── icons/             # Extension icons

src/
├── Main.purs          # Entry point
└── Extension/
    ├── Chrome.purs    # FFI to chrome.* APIs
    ├── Chrome.js      # FFI implementation
    └── Popup.purs     # Halogen popup component
```

## Building

```bash
# Enter nix shell with PureScript tools
nix develop

# Build PureScript to popup.js
cd purescript/foundry-extension
spago bundle --module Main --outfile extension/popup.js

# Load extension in Chrome:
# 1. Go to chrome://extensions
# 2. Enable Developer Mode
# 3. Click "Load unpacked"
# 4. Select the `extension/` directory
```

## How It Works

1. **User visits a website**
   - Content script is injected automatically

2. **User clicks extension icon**
   - Popup opens with "Extract" button

3. **User clicks "Extract"**
   - Popup sends message to background script
   - Background captures screenshot via `chrome.tabs.captureVisibleTab`
   - Background sends "extract" message to content script
   - Content script runs `extractAllElements()`:
     - Queries all DOM elements
     - Gets computed styles via `getComputedStyle()`
     - Converts colors to OKLCH (perceptual uniformity)
     - Builds parent/child tree structure
     - Groups elements by z-index into layers
     - Generates UUID5 for each layer
   - Results sent back to popup

4. **Popup displays results**
   - Element count
   - Layer count
   - Z-index layer breakdown
   - Screenshot preview

## Output Format

Each extracted element contains:

```javascript
{
  // Identity
  tagName: "DIV",
  selector: "#main > div:nth-of-type(2)",
  layerId: "550e8400-e29b-41d4-a716-446655440000", // UUID5

  // Geometry (pixels)
  x: 100, y: 200, width: 300, height: 48,

  // Colors (OKLCH - perceptually uniform)
  backgroundColor: { l: 0.5, c: 0.2, h: 250, a: 1.0 },
  color: { l: 0.95, c: 0.01, h: 0, a: 1.0 },

  // Typography
  fontFamily: "Inter, sans-serif",
  fontSize: 16,          // px
  fontWeight: 500,       // 100-900
  lineHeight: 24,        // px
  letterSpacing: 0,      // px

  // Spacing (px)
  marginTop: 0, marginRight: 16, marginBottom: 0, marginLeft: 16,
  paddingTop: 12, paddingRight: 24, paddingBottom: 12, paddingLeft: 24,

  // Borders (px)
  borderTopWidth: 1, borderRightWidth: 1,
  borderBottomWidth: 1, borderLeftWidth: 1,
  borderTopLeftRadius: 8, borderTopRightRadius: 8,
  borderBottomRightRadius: 8, borderBottomLeftRadius: 8,

  // Elevation
  zIndex: 0,
  boxShadow: { offsetX: 0, offsetY: 4, blurRadius: 6, ... },

  // DOM tree
  index: 42,
  parentIndex: 10,
  childIndices: [43, 44, 45],
  depth: 5
}
```

## Why OKLCH?

All colors are converted to OKLCH because:

1. **Perceptual uniformity** - Equal numeric distances produce equal perceived color differences
2. **Human-intuitive** - L (lightness), C (chroma), H (hue) map to how we think about color
3. **Brand preservation** - Color relationships are maintained during extraction
4. **CSS native** - Modern browsers support `oklch()` directly

## UUID5 for Determinism

Each layer gets a UUID5 derived from its CSS selector:

```javascript
uuid5("foundry.layer", "#main > div.card:nth-of-type(3)")
// Always produces the same UUID for the same selector
```

This enables:
- Reproducible extractions across runs
- Diff tracking between page versions
- Cache keying for incremental updates

## No TypeScript. No Node.js scraper.

This extension replaces the previous TypeScript scraper approaches.
The correct architecture is:

- **Content script runs IN the browser** (not Node.js)
- **Direct DOM access** (not Playwright)
- **PureScript popup** (compiles to JS)
- **Hydrogen Schema atoms** (bounded, typed)
