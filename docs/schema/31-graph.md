━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // 31 // graph
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Graph Pillar

Layout algorithms, node content, viewport state, and connection rendering for
hierarchical graph and tree visualization.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Graph/`
- **Files**: 19 modules
- **Lines**: ~2,816
- **Key features**: Layout algorithms (15 types), node content model with slots,
  viewport zoom/pan/virtualization, connection routing and animation

## Purpose

Graph provides bounded, deterministic primitives for:
- Hierarchical layout algorithms (tree, treemap, radial, force-directed)
- Node content composition (slots, templates, card fields)
- Viewport state management (zoom, pan, bounds, transitions)
- Level-of-detail rendering for large graphs (100k+ nodes)
- Connection styling and animation (routing, terminals, bundling)
- Progressive loading and virtualization

## Module Structure

```
src/Hydrogen/Schema/Graph/
├── Connection.purs           # Connection routing, styling, animation
├── Layout.purs               # Leader module (re-exports)
│   ├── Layout/Types.purs     # LayoutAlgorithm, LayoutDirection, NodeSizing
│   ├── Layout/Spacing.purs   # LayoutSpacing configuration
│   ├── Layout/Constraints.purs # LayoutBounds, NodePosition
│   ├── Layout/Params.purs    # TreemapParams, RadialParams, ForceParams
│   └── Layout/Config.purs    # LayoutConfig compound
├── NodeContent.purs          # Leader module (re-exports)
│   ├── NodeContent/Types.purs     # ContentSlot, ContentTemplate
│   ├── NodeContent/SlotContent.purs # SlotContent, TextContent
│   ├── NodeContent/ContentTypes.purs # Badge, Action, Progress
│   ├── NodeContent/CardAndShape.purs # CardField, NodeShape
│   └── NodeContent/Config.purs    # ContentConfig, NodeStateVisual
├── Viewport.purs             # Leader module (re-exports)
│   ├── Viewport/Types.purs   # ViewportZoom, ViewportPosition, ViewportBounds
│   ├── Viewport/State.purs   # ViewportState compound
│   ├── Viewport/LOD.purs     # LevelOfDetail, CullResult
│   ├── Viewport/Virtualization.purs # VirtualWindow, LoadingPriority
│   └── Viewport/Animation.purs # ViewportTransition, ViewportConstraints
```

────────────────────────────────────────────────────────────────────────────────
                                                             // layout // atoms
────────────────────────────────────────────────────────────────────────────────

## Layout Atoms

Core primitives for spatial arrangement of hierarchical data.

### LayoutAlgorithm Enum

Determines how nodes are positioned in space.

| Constructor | String ID | Category | Description |
|-------------|-----------|----------|-------------|
| `IndentedList` | `"indented-list"` | Linear | Traditional file explorer style |
| `Outline` | `"outline"` | Linear | Outline/bullet list style |
| `Radial` | `"radial"` | Radial | Nodes on concentric circles |
| `Sunburst` | `"sunburst"` | Radial | Arcs representing hierarchy |
| `CirclePack` | `"circle-pack"` | Radial | Nested circles |
| `Treemap` | `"treemap"` | Space-filling | Nested rectangles (Shneiderman 1992) |
| `Icicle` | `"icicle"` | Space-filling | Vertical/horizontal partitions |
| `Partition` | `"partition"` | Space-filling | Generic partition layout |
| `Tidy` | `"tidy"` | Node-link | Aesthetic tree (Reingold-Tilford 1981) |
| `Cluster` | `"cluster"` | Node-link | Leaves at same level |
| `Dendrogram` | `"dendrogram"` | Node-link | With branch lengths |
| `OrgChart` | `"org-chart"` | Node-link | Organizational hierarchy |
| `MindMap` | `"mind-map"` | Node-link | Central node radiating outward |
| `Force` | `"force"` | Force-directed | Physics simulation |
| `HierarchicalForce` | `"hierarchical-force"` | Force-directed | Force with hierarchy constraints |

**Category Predicates:**
- `isLinearLayout` — IndentedList, Outline
- `isRadialLayout` — Radial, Sunburst, CirclePack
- `isSpaceFillingLayout` — Treemap, Icicle, Partition
- `isNodeLinkLayout` — Tidy, Cluster, Dendrogram, OrgChart, MindMap
- `isForceLayout` — Force, HierarchicalForce

### LayoutDirection Enum

Primary axis direction for linear layouts.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Horizontal` | `"horizontal"` | Nodes arranged left-to-right |
| `Vertical` | `"vertical"` | Nodes arranged top-to-bottom |

**Operations:**
- `isHorizontal :: LayoutDirection -> Boolean`
- `isVertical :: LayoutDirection -> Boolean`
- `flipDirection :: LayoutDirection -> LayoutDirection`

### LayoutOrientation Enum

Flow direction for hierarchical layouts.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TopDown` | `"top-down"` | Root at top, children below |
| `BottomUp` | `"bottom-up"` | Root at bottom, children above |
| `LeftRight` | `"left-right"` | Root at left, children to right |
| `RightLeft` | `"right-left"` | Root at right, children to left |

### NodeSizing Sum Type

How node dimensions are determined.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `FixedSize` | `Number, Number` | Fixed width × height in pixels |
| `FitContent` | `Number, Number` | Fit to content with min w × h |
| `Proportional` | — | Size proportional to value |
| `AspectRatio` | `Number` | Maintain aspect ratio |

**Predicates:**
- `isFixedSize :: NodeSizing -> Boolean`
- `isFitContent :: NodeSizing -> Boolean`
- `isProportional :: NodeSizing -> Boolean`

────────────────────────────────────────────────────────────────────────────────
                                                          // layout // molecules
────────────────────────────────────────────────────────────────────────────────

## Layout Molecules

Composed configurations for layout algorithms.

### LayoutSpacing

Spacing between nodes at various hierarchy levels.

```purescript
type LayoutSpacing =
  { siblingGap :: Number   -- Gap between siblings (same parent)
  , levelGap :: Number     -- Gap between hierarchy levels
  , subtreeGap :: Number   -- Gap between subtrees
  , padding :: Number      -- Padding around entire tree
  }
```

**Presets:**

| Name | siblingGap | levelGap | subtreeGap | padding |
|------|------------|----------|------------|---------|
| `defaultSpacing` | 16px | 24px | 32px | 16px |
| `compactSpacing` | 4px | 8px | 12px | 8px |
| `spaciousSpacing` | 24px | 40px | 56px | 32px |

**Modifiers:**
- `withSiblingGap :: Number -> LayoutSpacing -> LayoutSpacing`
- `withLevelGap :: Number -> LayoutSpacing -> LayoutSpacing`
- `withSubtreeGap :: Number -> LayoutSpacing -> LayoutSpacing`
- `withPadding :: Number -> LayoutSpacing -> LayoutSpacing`

### LayoutBounds

Bounding box for layout constraints.

```purescript
type LayoutBounds =
  { width :: Maybe Number
  , height :: Maybe Number
  }
```

**Constructors:**
- `layoutBounds :: Number -> Number -> LayoutBounds` — Bounded
- `unbounded :: LayoutBounds` — Grow to fit content

### LayoutConstraints

Full constraint specification for layout algorithms.

```purescript
type LayoutConstraints =
  { bounds :: LayoutBounds
  , minNodeWidth :: Number
  , minNodeHeight :: Number
  , maxNodeWidth :: Maybe Number
  , maxNodeHeight :: Maybe Number
  , aspectRatio :: Maybe Number
  }
```

**Default:** `minNodeWidth = 50px`, `minNodeHeight = 24px`, unbounded

**Modifiers:**
- `withBounds :: LayoutBounds -> LayoutConstraints -> LayoutConstraints`
- `withMinNodeSize :: Number -> Number -> LayoutConstraints -> LayoutConstraints`
- `withMaxNodeSize :: Number -> Number -> LayoutConstraints -> LayoutConstraints`
- `withAspectRatio :: Number -> LayoutConstraints -> LayoutConstraints`

### NodePosition

Computed layout result for a single node.

```purescript
type NodePosition =
  { x :: Number       -- X coordinate
  , y :: Number       -- Y coordinate
  , width :: Number   -- Computed width
  , height :: Number  -- Computed height
  , rotation :: Number  -- Rotation in degrees (for radial)
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                   // layout // algorithm params
────────────────────────────────────────────────────────────────────────────────

## Algorithm-Specific Parameters

### TreemapAlgorithm Enum

Tiling algorithm for treemap layouts.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Squarify` | `"squarify"` | Optimal squareness (Bruls et al.) |
| `Binary` | `"binary"` | Binary split |
| `Slice` | `"slice"` | Horizontal slices |
| `Dice` | `"dice"` | Vertical slices |
| `SliceDice` | `"slice-dice"` | Alternating per level |

### TreemapParams

```purescript
type TreemapParams =
  { algorithm :: TreemapAlgorithm
  , paddingInner :: Number    -- Padding between siblings
  , paddingOuter :: Number    -- Padding around groups
  , paddingTop :: Number      -- Extra top padding (for labels)
  , ratio :: Number           -- Target aspect ratio for squarify
  }
```

**Default:** `algorithm = Squarify`, `paddingInner = 2px`, `paddingOuter = 4px`,
`paddingTop = 20px`, `ratio = 1.618` (golden ratio)

### RadialParams

Configuration for radial and sunburst layouts.

```purescript
type RadialParams =
  { startAngle :: Number      -- Start angle in radians (0 = right)
  , endAngle :: Number        -- End angle in radians
  , innerRadius :: Number     -- Inner radius (root position)
  , outerRadius :: Number     -- Outer radius (leaf positions)
  , clockwise :: Boolean      -- Direction of layout
  }
```

**Default:** Full circle (0 to 2π), `innerRadius = 50px`, `outerRadius = 300px`

### ForceParams

Physics simulation parameters for force-directed layouts.

```purescript
type ForceParams =
  { repulsion :: Number       -- Node repulsion strength
  , attraction :: Number      -- Edge attraction strength
  , gravity :: Number         -- Center gravity
  , damping :: Number         -- Velocity damping (0-1)
  , iterations :: Int         -- Simulation iterations
  , linkDistance :: Number    -- Ideal edge length
  }
```

**Default:** `repulsion = 100`, `attraction = 0.1`, `gravity = 0.05`,
`damping = 0.9`, `iterations = 300`, `linkDistance = 100px`

────────────────────────────────────────────────────────────────────────────────
                                                          // layout // compound
────────────────────────────────────────────────────────────────────────────────

## LayoutConfig (Compound)

Complete layout configuration combining all settings.

```purescript
type LayoutConfig =
  { algorithm :: LayoutAlgorithm
  , orientation :: LayoutOrientation
  , spacing :: LayoutSpacing
  , sizing :: NodeSizing
  , constraints :: LayoutConstraints
  , treemapParams :: Maybe TreemapParams
  , radialParams :: Maybe RadialParams
  , forceParams :: Maybe ForceParams
  }
```

**Preset Layouts:**

| Name | Algorithm | Orientation | Sizing | Notes |
|------|-----------|-------------|--------|-------|
| `indentedListLayout` | IndentedList | TopDown | FitContent | File explorer |
| `radialLayout` | Radial | TopDown | FitContent | Radial tree |
| `sunburstLayout` | Sunburst | TopDown | Proportional | Arc diagram |
| `treemapLayout` | Treemap | TopDown | Proportional | Nested rects |
| `dendrogramLayout` | Dendrogram | LeftRight | FitContent | Biological tree |
| `orgChartLayout` | OrgChart | TopDown | FixedSize(180×80) | Org hierarchy |
| `mindMapLayout` | MindMap | LeftRight | FitContent | Central radiating |
| `circlePackLayout` | CirclePack | TopDown | Proportional | Nested circles |
| `forceLayout` | Force | TopDown | FitContent | Physics sim |
| `tidyLayout` | Tidy | TopDown | FitContent | Reingold-Tilford |

────────────────────────────────────────────────────────────────────────────────
                                                        // connection // routing
────────────────────────────────────────────────────────────────────────────────

## Connection Routing

How the path between nodes is computed.

### ConnectionRouting Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `RoutingStraight` | `"straight"` | Direct line between nodes |
| `RoutingCurved` | `"curved"` | Bezier curve |
| `RoutingOrthogonal` | `"orthogonal"` | Right-angle connectors (elbow) |
| `RoutingDiagonal` | `"diagonal"` | Angled segments |
| `RoutingStep` | `"step"` | Step/staircase pattern |
| `RoutingBundle` | `"bundle"` | Bundled edges (for dense graphs) |
| `RoutingArc` | `"arc"` | Arc segments |
| `RoutingSpline` | `"spline"` | Smooth spline through control points |

**Predicates:**
- `isStraightRouting` — RoutingStraight only
- `isCurvedRouting` — RoutingCurved, RoutingSpline
- `isOrthogonalRouting` — RoutingOrthogonal, RoutingStep

### CurveStyle Enum

Interpolation style for curved paths.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `CurveBasis` | `"basis"` | B-spline |
| `CurveBezier` | `"bezier"` | Cubic bezier |
| `CurveCardinal` | `"cardinal"` | Cardinal spline |
| `CurveCatmullRom` | `"catmull-rom"` | Catmull-Rom spline |
| `CurveMonotone` | `"monotone"` | Monotone cubic |
| `CurveNatural` | `"natural"` | Natural cubic spline |
| `CurveLinear` | `"linear"` | Linear interpolation (straight) |

**Curve Tension:**
```purescript
curveTension :: Number -> Number
-- Clamped to [0.0, 1.0]
-- 0 = straight, 1 = tight curve
```

────────────────────────────────────────────────────────────────────────────────
                                                      // connection // terminals
────────────────────────────────────────────────────────────────────────────────

## Connection Terminals

Visual markers at connection endpoints.

### TerminalStyle Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TerminalNone` | `"none"` | No marker |
| `TerminalArrow` | `"arrow"` | Standard arrow head |
| `TerminalArrowFilled` | `"arrow-filled"` | Filled arrow head |
| `TerminalArrowOpen` | `"arrow-open"` | Open arrow head |
| `TerminalDot` | `"dot"` | Circle dot |
| `TerminalDotFilled` | `"dot-filled"` | Filled circle |
| `TerminalDiamond` | `"diamond"` | Diamond shape |
| `TerminalSquare` | `"square"` | Square marker |
| `TerminalBar` | `"bar"` | Perpendicular bar |

**Predicates:**
- `isArrowTerminal` — Arrow, ArrowFilled, ArrowOpen
- `isDotTerminal` — Dot, DotFilled
- `isNoneTerminal` — None only

### TerminalPosition Enum

Which end(s) to apply terminal markers.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TerminalStart` | `"start"` | At source/parent |
| `TerminalEnd` | `"end"` | At target/child |
| `TerminalBoth` | `"both"` | Both ends |

────────────────────────────────────────────────────────────────────────────────
                                                        // connection // stroke
────────────────────────────────────────────────────────────────────────────────

## Stroke Patterns

Dash patterns for connection lines.

### StrokePattern Sum Type

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `StrokeSolid` | — | Continuous line |
| `StrokeDashed` | `Number, Number` | Dash length, gap length |
| `StrokeDotted` | — | Dot pattern |
| `StrokeDashDot` | — | Dash-dot pattern |
| `StrokeCustom` | `Array Number` | Custom dash array |

**Predicates:**
- `isSolidStroke :: StrokePattern -> Boolean`
- `isDashedStroke :: StrokePattern -> Boolean`
- `isDottedStroke :: StrokePattern -> Boolean`

────────────────────────────────────────────────────────────────────────────────
                                                     // connection // molecules
────────────────────────────────────────────────────────────────────────────────

## ConnectionStyle (Molecule)

Visual style for all connections.

```purescript
type ConnectionStyle =
  { routing :: ConnectionRouting
  , curveStyle :: CurveStyle
  , curveTension :: Number
  , strokeWidth :: Number
  , strokeColor :: String       -- Hex color
  , strokePattern :: StrokePattern
  , startTerminal :: TerminalStyle
  , endTerminal :: TerminalStyle
  , terminalSize :: Number
  , opacity :: Number
  , visible :: Boolean
  }
```

**Default:** `routing = RoutingCurved`, `curveStyle = CurveBezier`,
`curveTension = 0.5`, `strokeWidth = 1px`, `strokeColor = "#94a3b8"` (slate-400),
`pattern = StrokeSolid`, no terminals, `opacity = 1.0`

**Modifiers:**
- `withRouting :: ConnectionRouting -> ConnectionStyle -> ConnectionStyle`
- `withStrokeWidth :: Number -> ConnectionStyle -> ConnectionStyle`
- `withStrokeColor :: String -> ConnectionStyle -> ConnectionStyle`
- `withStrokePattern :: StrokePattern -> ConnectionStyle -> ConnectionStyle`
- `withStartTerminal :: TerminalStyle -> ConnectionStyle -> ConnectionStyle`
- `withEndTerminal :: TerminalStyle -> ConnectionStyle -> ConnectionStyle`
- `withOpacity :: Number -> ConnectionStyle -> ConnectionStyle`
- `withCurveTension :: Number -> ConnectionStyle -> ConnectionStyle`

### BundleStyle

Style for bundled edges (edge bundling for dense graphs).

```purescript
type BundleStyle =
  { strength :: Number    -- Bundle tightness (0 = none, 1 = tight)
  , radius :: Number      -- Bundle corner radius
  , enabled :: Boolean
  }
```

**Default:** `strength = 0.85`, `radius = 30px`

────────────────────────────────────────────────────────────────────────────────
                                                    // connection // animation
────────────────────────────────────────────────────────────────────────────────

## Connection Animation

Animated effects for connections.

### ConnectionAnimation Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `AnimationStatic` | `"static"` | No animation |
| `AnimationDraw` | `"draw"` | Draw line progressively |
| `AnimationFlow` | `"flow"` | Animated flow along path |
| `AnimationPulse` | `"pulse"` | Pulsing effect |
| `AnimationDash` | `"dash"` | Moving dashes |

### DrawAnimationParams

```purescript
type DrawAnimationParams =
  { duration :: Number     -- Animation duration in ms
  , delay :: Number        -- Start delay in ms
  , easing :: String       -- Easing function name
  , direction :: String    -- "forward" | "reverse" | "both"
  }
```

### FlowAnimationParams

```purescript
type FlowAnimationParams =
  { speed :: Number        -- Flow speed (px/s)
  , particleSize :: Number -- Size of flow particles
  , particleGap :: Number  -- Gap between particles
  , color :: Maybe String  -- Override color
  }
```

**Default:** `particleSize = 4px`, `particleGap = 20px`

### PulseAnimationParams

```purescript
type PulseAnimationParams =
  { frequency :: Number    -- Pulses per second
  , minOpacity :: Number   -- Minimum opacity (0.3)
  , maxOpacity :: Number   -- Maximum opacity (1.0)
  , minWidth :: Number     -- Minimum stroke width (1px)
  , maxWidth :: Number     -- Maximum stroke width (3px)
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                      // connection // compound
────────────────────────────────────────────────────────────────────────────────

## ConnectionConfig (Compound)

Complete connection configuration.

```purescript
type ConnectionConfig =
  { style :: ConnectionStyle
  , bundleStyle :: Maybe BundleStyle
  , animation :: ConnectionAnimation
  , drawParams :: Maybe DrawAnimationParams
  , flowParams :: Maybe FlowAnimationParams
  , pulseParams :: Maybe PulseAnimationParams
  , renderOrder :: String    -- "behind" | "front" | "interleaved"
  }
```

**Presets:**

| Name | Routing | Animation | Notes |
|------|---------|-----------|-------|
| `simpleConnections` | Straight | Static | Basic lines |
| `curvedConnections` | Curved | Static | Default bezier |
| `orthogonalConnections` | Orthogonal | Static | Elbow connectors |
| `bundledConnections` | Bundle | Static | Edge bundling enabled |
| `animatedConnections` | Curved | Flow | Animated particles |
| `noConnectionLines` | — | — | Hidden connections |

### EdgeStyle

Per-edge style overrides.

```purescript
type EdgeStyle =
  { color :: Maybe String
  , width :: Maybe Number
  , pattern :: Maybe StrokePattern
  , label :: Maybe String
  , labelPosition :: Number    -- 0-1 position along edge
  , visible :: Boolean
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                     // node-content // slots
────────────────────────────────────────────────────────────────────────────────

## Node Content Slots

Named regions within a node where content appears.

### ContentSlot Enum

```
┌─────────────────────────────────────────────────────────┐
│ [Leading]  [Icon]  [Main Content]  [Trailing] [Actions]│
│                    [Subtitle]                          │
│                    [Below Content / Details]           │
└─────────────────────────────────────────────────────────┘
```

| Constructor | String ID | Priority | Description |
|-------------|-----------|----------|-------------|
| `SlotBackground` | `"background"` | 0 | Behind all content |
| `SlotLeading` | `"leading"` | 1 | Before main (expand icon, checkbox) |
| `SlotIcon` | `"icon"` | 2 | Node icon area |
| `SlotMain` | `"main"` | 3 | Primary content area |
| `SlotSubtitle` | `"subtitle"` | 4 | Secondary text below main |
| `SlotTrailing` | `"trailing"` | 5 | After main (badges, status) |
| `SlotActions` | `"actions"` | 6 | Action buttons (show on hover) |
| `SlotBelow` | `"below"` | 7 | Content below the main row |
| `SlotOverlay` | `"overlay"` | 8 | Overlaid on top of node |

**Predicates:**
- `isLeadingSlot :: ContentSlot -> Boolean`
- `isMainSlot :: ContentSlot -> Boolean`
- `isTrailingSlot :: ContentSlot -> Boolean`
- `slotPriority :: ContentSlot -> Int` — Lower = rendered first

────────────────────────────────────────────────────────────────────────────────
                                                  // node-content // templates
────────────────────────────────────────────────────────────────────────────────

## Content Templates

Pre-built content configurations.

### ContentTemplate Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TemplateTextOnly` | `"text-only"` | Simple text label |
| `TemplateIconText` | `"icon-text"` | Icon + text (file explorer) |
| `TemplateTitleSubtitle` | `"title-subtitle"` | Title + subtitle |
| `TemplateCard` | `"card"` | Multi-field card |
| `TemplateAvatar` | `"avatar"` | Avatar + name |
| `TemplateMetric` | `"metric"` | Value + label (dashboards) |
| `TemplateProgress` | `"progress"` | Progress indicator |
| `TemplateThumbnail` | `"thumbnail"` | Image thumbnail |
| `TemplateCustom` | `"custom"` | Custom Element |

**Predicates:**
- `isTextTemplate` — TextOnly, TitleSubtitle
- `isCardTemplate` — Card only
- `isCustomTemplate` — Custom only

────────────────────────────────────────────────────────────────────────────────
                                              // node-content // slot-content
────────────────────────────────────────────────────────────────────────────────

## SlotContent Sum Type

Content types that can appear in a slot.

| Constructor | Parameter | Description |
|-------------|-----------|-------------|
| `ContentText` | `TextContent` | Text with formatting |
| `ContentIcon` | `String` | Icon identifier |
| `ContentBadge` | `BadgeContent` | Counter/status badge |
| `ContentAction` | `ActionContent` | Button/action |
| `ContentProgress` | `ProgressContent` | Progress indicator |
| `ContentImage` | `String` | Image URL |
| `ContentCustom` | `String` | Custom Element key |

**Constructors:**
- `textContent :: String -> SlotContent`
- `iconContent :: String -> SlotContent`
- `badgeContent :: Int -> SlotContent`
- `actionContent :: String -> String -> SlotContent` — id, label
- `progressContent :: Number -> SlotContent` — percentage
- `customContent :: String -> SlotContent`

### TextContent

Text content with formatting options.

```purescript
type TextContent =
  { text :: String
  , editable :: Boolean
  , truncate :: Boolean
  , maxLines :: Int
  , highlight :: Maybe String    -- Highlight matching text
  , fontWeight :: Maybe String
  , fontSize :: Maybe String
  , color :: Maybe String
  }
```

**Constructors:**
- `simpleText :: String -> TextContent` — Basic text
- `richText :: String -> String -> String -> TextContent` — text, weight, size
- `editableText :: String -> TextContent` — Inline editable

────────────────────────────────────────────────────────────────────────────────
                                            // node-content // content-types
────────────────────────────────────────────────────────────────────────────────

## BadgeContent

Badge/indicator content.

```purescript
type BadgeContent =
  { badgeType :: String          -- "count" | "status" | "dot"
  , value :: Maybe Int
  , status :: Maybe String       -- "success" | "warning" | "error" | "info"
  , label :: Maybe String
  , color :: Maybe String
  , maxCount :: Int              -- Show "99+" if exceeded
  }
```

**Constructors:**
- `badgeCount :: Int -> BadgeContent` — Count badge (e.g., "5")
- `badgeStatus :: String -> String -> BadgeContent` — Status with label
- `badgeDot :: String -> BadgeContent` — Simple colored dot

## ActionContent

Action button/menu content.

```purescript
type ActionContent =
  { actionType :: String         -- "button" | "icon" | "menu"
  , actionId :: String
  , label :: Maybe String
  , icon :: Maybe String
  , disabled :: Boolean
  , tooltip :: Maybe String
  }
```

**Constructors:**
- `buttonAction :: String -> String -> ActionContent` — id, label
- `iconAction :: String -> String -> ActionContent` — id, icon
- `menuAction :: String -> String -> ActionContent` — id, label

## ProgressContent

Progress indicator content.

```purescript
type ProgressContent =
  { progressType :: String       -- "bar" | "circle" | "sparkline"
  , value :: Number              -- 0-100 percentage
  , showLabel :: Boolean
  , color :: Maybe String
  , secondaryColor :: Maybe String
  , sparklineData :: Array Number  -- For sparkline type
  }
```

**Constructors:**
- `progressBar :: Number -> ProgressContent` — Horizontal bar
- `progressCircle :: Number -> ProgressContent` — Circular progress
- `progressSparkline :: Array Number -> ProgressContent` — Mini chart

────────────────────────────────────────────────────────────────────────────────
                                               // node-content // card-fields
────────────────────────────────────────────────────────────────────────────────

## CardField Sum Type

Fields for card-style nodes.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `FieldTitle` | `String` | Title text |
| `FieldSubtitle` | `String` | Subtitle text |
| `FieldMetadata` | `String, String` | Label, value pair |
| `FieldImage` | `String` | Image URL |
| `FieldAvatar` | `String, String` | URL, name |
| `FieldBadge` | `BadgeContent` | Badge display |
| `FieldProgress` | `ProgressContent` | Progress display |
| `FieldDivider` | — | Horizontal divider |
| `FieldSpacer` | `Number` | Vertical space |

**Constructors:**
- `titleField :: String -> CardField`
- `subtitleField :: String -> CardField`
- `metadataField :: String -> String -> CardField`
- `imageField :: String -> CardField`
- `avatarField :: String -> String -> CardField`

────────────────────────────────────────────────────────────────────────────────
                                                // node-content // node-shape
────────────────────────────────────────────────────────────────────────────────

## NodeShape Enum

Visual shape of the node container.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ShapeRectangle` | `"rectangle"` | Standard rectangle |
| `ShapeRoundedRect` | `"rounded-rect"` | Rounded corners |
| `ShapePill` | `"pill"` | Fully rounded ends |
| `ShapeCircle` | `"circle"` | Circle (for radial) |
| `ShapeEllipse` | `"ellipse"` | Ellipse |
| `ShapeDiamond` | `"diamond"` | Rotated square |
| `ShapeHexagon` | `"hexagon"` | Six-sided |
| `ShapeOctagon` | `"octagon"` | Eight-sided |
| `ShapeParallelogram` | `"parallelogram"` | Skewed rectangle |
| `ShapeCylinder` | `"cylinder"` | Database-style |
| `ShapeDocument` | `"document"` | Document shape |
| `ShapeCloud` | `"cloud"` | Cloud shape |
| `ShapeCustomPath` | `"custom"` | Custom SVG path (String) |

**Predicates:**
- `isRectangle` — ShapeRectangle, ShapeRoundedRect
- `isCircle` — ShapeCircle, ShapeEllipse
- `isDiamond` — ShapeDiamond only

────────────────────────────────────────────────────────────────────────────────
                                              // node-content // state-visual
────────────────────────────────────────────────────────────────────────────────

## NodeStateVisual

Visual styling for different node states.

```purescript
type NodeStateVisual =
  { defaultBg :: Maybe String
  , defaultBorder :: Maybe String
  , hoverBg :: Maybe String
  , hoverBorder :: Maybe String
  , selectedBg :: Maybe String
  , selectedBorder :: Maybe String
  , focusBorder :: Maybe String
  , focusRing :: Maybe String
  , disabledOpacity :: Number      -- Default: 0.5
  , pressedScale :: Number         -- Default: 0.98
  }
```

**Modifiers:**
- `withHoverStyle :: String -> String -> NodeStateVisual -> NodeStateVisual`
- `withSelectedStyle :: String -> String -> NodeStateVisual -> NodeStateVisual`
- `withFocusStyle :: String -> String -> NodeStateVisual -> NodeStateVisual`
- `withDisabledStyle :: Number -> NodeStateVisual -> NodeStateVisual`

────────────────────────────────────────────────────────────────────────────────
                                              // node-content // config compound
────────────────────────────────────────────────────────────────────────────────

## ContentConfig (Compound)

Complete content configuration for nodes.

```purescript
type ContentConfig =
  { template :: ContentTemplate
  , shape :: NodeShape
  , slots :: Array { slot :: ContentSlot, content :: SlotContent }
  , fields :: Array CardField        -- For card template
  , stateVisual :: NodeStateVisual
  , padding :: Number
  , minWidth :: Maybe Number
  , maxWidth :: Maybe Number
  , aspectRatio :: Maybe Number
  }
```

**Presets:**

| Name | Template | Shape | Padding | Notes |
|------|----------|-------|---------|-------|
| `textOnlyContent` | TextOnly | Rectangle | 8px | Simple label |
| `iconTextContent` | IconText | Rectangle | 8px | File explorer |
| `cardContent` | Card | RoundedRect | 16px | Org chart |
| `avatarContent` | Avatar | RoundedRect | 12px | People list |
| `metricContent` | Metric | RoundedRect | 8px | Dashboard |
| `customContentConfig` | Custom | Rectangle | 8px | Custom Element |

### SlotLayout

Layout for slots within a node.

```purescript
type SlotLayout =
  { direction :: String          -- "horizontal" | "vertical" | "grid"
  , gap :: Number
  , alignItems :: String         -- "start" | "center" | "end" | "stretch"
  , justifyContent :: String     -- "start" | "center" | "end" | "space-between"
  , wrap :: Boolean
  , gridColumns :: Int
  }
```

**Presets:**
- `horizontalSlots` — direction = "horizontal", gap = 8px
- `verticalSlots` — direction = "vertical", gap = 4px
- `gridSlots :: Int -> SlotLayout` — Grid with N columns

────────────────────────────────────────────────────────────────────────────────
                                                          // viewport // atoms
────────────────────────────────────────────────────────────────────────────────

## Viewport Atoms

Core primitives for graph viewport state.

### ViewportZoom (newtype)

Zoom level for graph viewport.

```purescript
newtype ViewportZoom = ViewportZoom Number
```

| Property | Value | Notes |
|----------|-------|-------|
| Min | 0.01 (1%) | Prevents degenerate states |
| Max | 100.0 (10000%) | Bounded at construction |
| Default | 1.0 (100%) | 1:1 mapping |
| Step | 1.2 | Zoom in/out multiplier |

**Operations:**
- `viewportZoom :: Number -> ViewportZoom` — Clamped to [0.01, 100.0]
- `zoomIn :: ViewportZoom -> ViewportZoom` — Multiply by 1.2
- `zoomOut :: ViewportZoom -> ViewportZoom` — Divide by 1.2
- `zoomTo :: Number -> ViewportZoom` — Set exact level
- `zoomToFit :: Number -> Number -> Number -> Number -> ViewportZoom`
  — contentWidth, contentHeight, viewportWidth, viewportHeight
- `zoomLevel :: ViewportZoom -> Number` — Get numeric value
- `zoomPercentage :: ViewportZoom -> Number` — Get as percentage
- `isMinZoom :: ViewportZoom -> Boolean`
- `isMaxZoom :: ViewportZoom -> Boolean`

**Presets:**

| Name | Value | Percentage |
|------|-------|------------|
| `zoom25` | 0.25 | 25% |
| `zoom50` | 0.50 | 50% |
| `zoom100` | 1.00 | 100% |
| `zoom200` | 2.00 | 200% |
| `zoom400` | 4.00 | 400% |

### ViewportPosition

Pan position in graph space coordinates.

```purescript
type ViewportPosition =
  { x :: Number  -- X offset (positive = right)
  , y :: Number  -- Y offset (positive = down)
  }
```

**Operations:**
- `viewportPosition :: Number -> Number -> ViewportPosition`
- `origin :: ViewportPosition` — {x: 0, y: 0}
- `panX :: ViewportPosition -> Number`
- `panY :: ViewportPosition -> Number`
- `panBy :: Number -> Number -> ViewportPosition -> ViewportPosition`
- `panTo :: Number -> Number -> ViewportPosition`
- `centerOn :: Number -> Number -> Number -> Number -> ViewportPosition`
  — targetX, targetY, viewportWidth, viewportHeight

### ViewportBounds

Rectangular bounds in graph space.

```purescript
type ViewportBounds =
  { left :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  }
```

**Constructors:**
- `viewportBounds :: Number -> Number -> Number -> Number -> ViewportBounds`
  — left, top, right, bottom (auto-normalizes)
- `boundsFromCenter :: Number -> Number -> Number -> Number -> ViewportBounds`
  — centerX, centerY, width, height

**Accessors:**
- `boundsLeft`, `boundsTop`, `boundsRight`, `boundsBottom`
- `boundsWidth`, `boundsHeight`
- `boundsCenter :: ViewportBounds -> { x :: Number, y :: Number }`

**Operations:**
- `containsPoint :: Number -> Number -> ViewportBounds -> Boolean`
- `boundsIntersect :: ViewportBounds -> ViewportBounds -> Boolean`
- `expandBounds :: Number -> ViewportBounds -> ViewportBounds`

────────────────────────────────────────────────────────────────────────────────
                                                       // viewport // compound
────────────────────────────────────────────────────────────────────────────────

## ViewportState (Compound)

Complete viewport state combining zoom, pan, and screen dimensions.

```purescript
type ViewportState =
  { zoom :: ViewportZoom
  , pan :: ViewportPosition
  , screenWidth :: Number   -- Viewport width in screen pixels
  , screenHeight :: Number  -- Viewport height in screen pixels
  }
```

**Operations:**
- `viewportState :: ViewportZoom -> ViewportPosition -> Number -> Number -> ViewportState`
- `initialViewport :: Number -> Number -> ViewportState` — Centered, 100% zoom
- `viewportZoomLevel :: ViewportState -> ViewportZoom`
- `viewportPan :: ViewportState -> ViewportPosition`
- `viewportBoundsAt :: ViewportState -> ViewportBounds` — Calculate visible bounds
- `setZoom :: ViewportZoom -> ViewportState -> ViewportState`
- `setPan :: ViewportPosition -> ViewportState -> ViewportState`
- `applyZoom :: ViewportZoom -> ViewportState -> ViewportState` — Preserves center
- `applyPan :: Number -> Number -> ViewportState -> ViewportState` — Accounts for zoom
- `fitContent :: ViewportBounds -> ViewportState -> ViewportState`

────────────────────────────────────────────────────────────────────────────────
                                                             // viewport // lod
────────────────────────────────────────────────────────────────────────────────

## Level of Detail (LOD)

Render optimization based on zoom and visibility.

### LevelOfDetail Enum

| Constructor | String ID | Render Nodes | Render Labels | Render Connections |
|-------------|-----------|--------------|---------------|-------------------|
| `LOD_Full` | `"full"` | Yes | Yes | Yes |
| `LOD_Simplified` | `"simplified"` | Yes | Yes | Yes |
| `LOD_Minimal` | `"minimal"` | Yes | No | Yes |
| `LOD_Dot` | `"dot"` | Yes (dot) | No | No |
| `LOD_Hidden` | `"hidden"` | No | No | No |

**LOD Calculation:**
```purescript
lodForZoom :: ViewportZoom -> Number -> LevelOfDetail
-- screenSize = zoom × nodeSize
-- >= 50px → Full
-- >= 20px → Simplified
-- >= 8px  → Minimal
-- >= 2px  → Dot
-- < 2px   → Hidden
```

**Predicates:**
- `shouldRenderNode :: LevelOfDetail -> Boolean` — true unless Hidden
- `shouldRenderLabel :: LevelOfDetail -> Boolean` — Full or Simplified
- `shouldRenderConnection :: LevelOfDetail -> Boolean` — not Hidden or Dot

### CullResult Enum

Result of culling check.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Visible` | `"visible"` | Fully visible |
| `PartiallyVisible` | `"partial"` | Partially in viewport |
| `Culled` | `"culled"` | Not visible, don't render |

**Culling Operations:**
- `cullNode :: ViewportBounds -> Number -> Number -> Number -> Number -> CullResult`
  — viewport, nodeX, nodeY, nodeWidth, nodeHeight
- `cullConnection :: ViewportBounds -> Number -> Number -> Number -> Number -> CullResult`
  — viewport, x1, y1, x2, y2

────────────────────────────────────────────────────────────────────────────────
                                                  // viewport // virtualization
────────────────────────────────────────────────────────────────────────────────

## Virtualization

Efficient rendering of large graphs (100k+ nodes).

### VirtualWindow

What portion of data to load/render.

```purescript
type VirtualWindow =
  { bounds :: ViewportBounds      -- Visible bounds
  , overscan :: Number            -- Extra margin for smooth scrolling
  , nodeCount :: Int              -- Estimated visible nodes
  , connectionCount :: Int        -- Estimated visible connections
  }
```

**Operations:**
- `virtualWindow :: ViewportState -> Number -> VirtualWindow`
- `windowNodes :: VirtualWindow -> Int`
- `windowConnections :: VirtualWindow -> Int`
- `windowOverscan :: VirtualWindow -> Number`
- `expandWindow :: Number -> VirtualWindow -> VirtualWindow`
- `isInWindow :: Number -> Number -> VirtualWindow -> Boolean`

### LoadingPriority Enum

Priority for progressive loading.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Immediate` | `"immediate"` | Load immediately (viewport center) |
| `High` | `"high"` | Load soon (in viewport) |
| `Normal` | `"normal"` | Load eventually (in overscan) |
| `Low` | `"low"` | Lazy load (outside viewport) |
| `Deferred` | `"deferred"` | Don't load until requested |

**Priority Calculation:**
```purescript
loadingPriority :: ViewportState -> Number -> Number -> LoadingPriority
-- Center quarter → Immediate
-- In viewport → High
-- Within 200px → Normal
-- Within 500px → Low
-- Beyond → Deferred
```

### LoadingRegion

Spatial region with loading priority.

```purescript
type LoadingRegion =
  { bounds :: ViewportBounds
  , priority :: LoadingPriority
  }
```

**Constructors:**
- `loadingRegion :: ViewportBounds -> LoadingPriority -> LoadingRegion`
- `priorityRegion :: ViewportState -> LoadingRegion` — Center, Immediate
- `backgroundRegion :: ViewportState -> Number -> LoadingRegion` — Expanded, Low

────────────────────────────────────────────────────────────────────────────────
                                                      // viewport // animation
────────────────────────────────────────────────────────────────────────────────

## Viewport Transitions

Smooth transitions for viewport changes.

### ViewportTransition Sum Type

| Constructor | Parameters | Duration | Description |
|-------------|------------|----------|-------------|
| `Instant` | — | 0ms | No animation |
| `Linear` | `Number` | param | Constant velocity |
| `EaseInOut` | `Number` | param | Smooth acceleration/deceleration |
| `Spring` | `Number, Number` | ~600ms | Physics (tension, friction) |

**Constructors:**
- `instantTransition :: ViewportTransition`
- `smoothTransition :: Number -> ViewportTransition` — EaseInOut(duration)
- `springTransition :: Number -> Number -> ViewportTransition` — tension, friction

**Operations:**
- `transitionDuration :: ViewportTransition -> Number`
- `isAnimating :: ViewportTransition -> Boolean`

### ViewportConstraints

Limits on viewport movement.

```purescript
type ViewportConstraints =
  { minZoom :: ViewportZoom
  , maxZoom :: ViewportZoom
  , panBounds :: Maybe ViewportBounds  -- Nothing = unlimited
  }
```

**Operations:**
- `viewportConstraints :: ViewportZoom -> ViewportZoom -> Maybe ViewportBounds -> ViewportConstraints`
- `unconstrainedViewport :: ViewportConstraints` — No limits
- `constrainZoom :: ViewportConstraints -> ViewportZoom -> ViewportZoom`
- `constrainPan :: ViewportConstraints -> ViewportState -> ViewportPosition -> ViewportPosition`
- `withMinZoom :: ViewportZoom -> ViewportConstraints -> ViewportConstraints`
- `withMaxZoom :: ViewportZoom -> ViewportConstraints -> ViewportConstraints`
- `withPanBounds :: ViewportBounds -> ViewportConstraints -> ViewportConstraints`

────────────────────────────────────────────────────────────────────────────────
                                                        // academic // references
────────────────────────────────────────────────────────────────────────────────

## Academic References

Layout algorithms based on established research:

| Algorithm | Paper | Year | Key Contribution |
|-----------|-------|------|------------------|
| Tidy Tree | Reingold-Tilford | 1981 | O(n) aesthetic tree drawing |
| Walker | Walker | 1990 | Improvements to R-T algorithm |
| Buchheim | Buchheim et al. | 2002 | Linear time R-T implementation |
| Treemap | Shneiderman | 1992 | Space-filling hierarchy |
| Squarify | Bruls et al. | 2000 | Optimal aspect ratio treemaps |
| Force-Directed | Fruchterman-Reingold | 1991 | Physics-based layout |

────────────────────────────────────────────────────────────────────────────────
                                                        // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Why These Primitives Matter

Graph visualization is one of the most complex rendering challenges. The Graph
pillar provides a **complete, bounded vocabulary** for:

**Layout**: Pure geometry. Given structure + constraints → positions.
- Same tree + same config = same layout (deterministic)
- All algorithms are well-studied with known complexity bounds
- No hidden state, no side effects

**Node Content**: Composable slots.
- Slot architecture separates what goes where from how it renders
- Templates provide instant configuration for common patterns
- Card fields support rich org-chart style nodes

**Viewport**: Infinite canvas with finite resources.
- Zoom bounded [0.01, 100.0] — no divide-by-zero, no overflow
- LOD ensures 100k+ nodes render efficiently
- Virtualization loads only what's needed

**Connections**: Pure visual description.
- 8 routing algorithms for any edge style
- 9 terminal markers for directed graphs
- Animation as data, not imperative code

### At Billion-Agent Scale

When an agent needs to visualize a hierarchy:

1. **Choose layout** — LayoutAlgorithm enum is exhaustive
2. **Configure nodes** — ContentTemplate + slots
3. **Set connections** — ConnectionRouting + terminals
4. **Manage viewport** — ViewportState with constraints

Same configuration → same visualization. Always.

No CSS to interpret differently. No framework quirks.
Pure data describing how graphs are drawn.

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Graph/
├── Connection.purs              # 450 lines
├── Layout/
│   ├── Config.purs              # 140 lines
│   ├── Constraints.purs         # 130 lines
│   ├── Params.purs              # 175 lines
│   ├── Spacing.purs             # 90 lines
│   └── Types.purs               # 170 lines
├── Layout.purs                  # 35 lines (re-exports)
├── NodeContent/
│   ├── CardAndShape.purs        # 115 lines
│   ├── Config.purs              # 160 lines
│   ├── ContentTypes.purs        # 135 lines
│   ├── SlotContent.purs         # 120 lines
│   └── Types.purs               # 105 lines
├── NodeContent.purs             # 70 lines (re-exports)
├── Viewport/
│   ├── Animation.purs           # 145 lines
│   ├── LOD.purs                 # 130 lines
│   ├── State.purs               # 115 lines
│   ├── Types.purs               # 230 lines
│   └── Virtualization.purs      # 155 lines
└── Viewport.purs                # 75 lines (re-exports)
```

19 files, ~2,816 lines total.

────────────────────────────────────────────────────────────────────────────────
