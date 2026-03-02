━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // 35 // accessibility
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Accessibility Pillar

WAI-ARIA 1.2 roles, states, properties, live regions, and landmarks.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Accessibility/`
- **Files**: 6 modules
- **Lines**: 1,115 total
- **Key features**: Complete WAI-ARIA 1.2 vocabulary, type-safe states/properties,
  landmark navigation, live region configuration, accessibility molecules

## Purpose

Accessibility provides bounded, deterministic primitives for:
- ARIA roles (widget, composite, structure, window, landmark)
- ARIA states (expanded, selected, pressed, checked, etc.)
- ARIA properties (relationships, widgets, labels)
- Live regions (politeness levels, atomic announcements, relevance filtering)
- Landmark navigation (banner, main, navigation, etc.)
- Accessibility molecules (disclosure, selection, range, tab, dialog patterns)

## Why Accessibility Must Be First-Class

At billion-agent scale, accessibility cannot be an afterthought. When autonomous
AI agents generate UI, they must produce **semantically correct** output that
works for all users. A button must be announced as a button. A disclosure must
track its expanded state. A live region must respect politeness levels.

**Type-safe ARIA means:**
- Invalid role/state combinations are impossible by construction
- Screen reader announcements are deterministic
- Agents can reason algebraically about accessibility semantics
- Compliance is verified at compile time, not runtime

## WAI-ARIA 1.2 Reference

https://www.w3.org/TR/wai-aria-1.2/

All types in this pillar conform to the WAI-ARIA 1.2 specification. Role names,
state values, property semantics — all directly mapped from the specification.

────────────────────────────────────────────────────────────────────────────────
                                                              // role // taxonomy
────────────────────────────────────────────────────────────────────────────────

## Role Categories

ARIA roles are organized into a taxonomy. Each role tells assistive technology
what an element **is** — its fundamental nature and expected behavior.

### Role Hierarchy

```
role
├── widget (interactive)
│   ├── standalone widgets (button, checkbox, link, ...)
│   └── composite widgets (combobox, grid, menu, ...)
├── document structure (article, heading, list, ...)
├── landmark (banner, main, navigation, ...)
├── live region (alert, log, status, timer)
└── window (dialog, alertdialog)
```

────────────────────────────────────────────────────────────────────────────────
                                                              // widget // roles
────────────────────────────────────────────────────────────────────────────────

## WidgetRole (20 Roles)

Interactive elements users manipulate directly.

**WidgetRole Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `RoleButton` | `button` | Clickable action trigger |
| `RoleCheckbox` | `checkbox` | Binary or tristate selection |
| `RoleGridcell` | `gridcell` | Cell within a grid or treegrid |
| `RoleLink` | `link` | Navigational hyperlink |
| `RoleMenuitem` | `menuitem` | Option within a menu |
| `RoleMenuitemcheckbox` | `menuitemcheckbox` | Checkable menu item |
| `RoleMenuitemradio` | `menuitemradio` | Radio button menu item |
| `RoleOption` | `option` | Item within a listbox |
| `RoleProgressbar` | `progressbar` | Task completion indicator |
| `RoleRadio` | `radio` | Exclusive selection within group |
| `RoleScrollbar` | `scrollbar` | Content scrolling control |
| `RoleSearchbox` | `searchbox` | Text input for search queries |
| `RoleSeparator` | `separator` | Visual/semantic divider |
| `RoleSlider` | `slider` | Range value selection |
| `RoleSpinbutton` | `spinbutton` | Numeric input with increment/decrement |
| `RoleSwitch` | `switch` | Binary on/off toggle |
| `RoleTab` | `tab` | Tab in a tablist |
| `RoleTabpanel` | `tabpanel` | Content panel for a tab |
| `RoleTextbox` | `textbox` | Text input field |
| `RoleTreeitem` | `treeitem` | Item within a tree |

**Usage:**

```purescript
import Hydrogen.Schema.Accessibility.Role (WidgetRole(..), widgetRoleToString)

-- Type-safe role assignment
buttonRole :: String
buttonRole = widgetRoleToString RoleButton  -- "button"
```

────────────────────────────────────────────────────────────────────────────────
                                                           // composite // roles
────────────────────────────────────────────────────────────────────────────────

## CompositeRole (9 Roles)

Container widgets that manage child widgets and focus.

**CompositeRole Enum:**

| Constructor | ARIA String | Required Children | Description |
|-------------|-------------|-------------------|-------------|
| `RoleCombobox` | `combobox` | textbox + listbox | Combined input + dropdown |
| `RoleGrid` | `grid` | row, gridcell | Interactive data table |
| `RoleListbox` | `listbox` | option | List of selectable options |
| `RoleMenu` | `menu` | menuitem, menuitemcheckbox, menuitemradio | Action/option list |
| `RoleMenubar` | `menubar` | menuitem | Horizontal menu strip |
| `RoleRadiogroup` | `radiogroup` | radio | Exclusive selection group |
| `RoleTablist` | `tablist` | tab | Tab navigation container |
| `RoleTree` | `tree` | treeitem | Hierarchical list |
| `RoleTreegrid` | `treegrid` | row, gridcell | Expandable table rows |

**Focus Management:**

Composite widgets manage focus among their children. Keyboard navigation follows
WAI-ARIA patterns:
- Arrow keys move between items
- Home/End jump to first/last
- Enter/Space activate items

────────────────────────────────────────────────────────────────────────────────
                                                           // structure // roles
────────────────────────────────────────────────────────────────────────────────

## StructureRole (27 Roles)

Document structure and content organization.

**StructureRole Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `RoleApplication` | `application` | Web application region |
| `RoleArticle` | `article` | Self-contained composition |
| `RoleBlockquote` | `blockquote` | Extended quotation |
| `RoleCaption` | `caption` | Caption for figure/table |
| `RoleCell` | `cell` | Cell within a table |
| `RoleColumnheader` | `columnheader` | Column header cell |
| `RoleDefinition` | `definition` | Term definition |
| `RoleDirectory` | `directory` | Static table of contents |
| `RoleDocument` | `document` | Document content region |
| `RoleFeed` | `feed` | Scrollable article stream |
| `RoleFigure` | `figure` | Figure with optional caption |
| `RoleGroup` | `group` | Related element grouping |
| `RoleHeading` | `heading` | Section heading (with level) |
| `RoleImg` | `img` | Image container |
| `RoleList` | `list` | List container |
| `RoleListitem` | `listitem` | Item within a list |
| `RoleMath` | `math` | Mathematical expression |
| `RoleMeter` | `meter` | Scalar measurement |
| `RoleNote` | `note` | Parenthetic/ancillary content |
| `RoleParagraph` | `paragraph` | Paragraph of content |
| `RoleRow` | `row` | Row within table/grid/treegrid |
| `RoleRowgroup` | `rowgroup` | Row group (thead/tbody/tfoot) |
| `RoleRowheader` | `rowheader` | Row header cell |
| `RoleTable` | `table` | Data table (not grid) |
| `RoleTerm` | `term` | Term being defined |
| `RoleToolbar` | `toolbar` | Toolbar of controls |
| `RoleTooltip` | `tooltip` | Popup tooltip |

**Semantic Hierarchy:**

```
table
├── rowgroup (thead)
│   └── row
│       └── columnheader
├── rowgroup (tbody)
│   └── row
│       ├── rowheader
│       └── cell
└── caption
```

────────────────────────────────────────────────────────────────────────────────
                                                              // window // roles
────────────────────────────────────────────────────────────────────────────────

## WindowRole (3 Roles)

Overlay and dialog roles.

**WindowRole Enum:**

| Constructor | ARIA String | Modal | Description |
|-------------|-------------|-------|-------------|
| `RoleAlert` | `alert` | No | Urgent message (live region) |
| `RoleAlertdialog` | `alertdialog` | Yes | Alert requiring confirmation |
| `RoleDialog` | `dialog` | Optional | Modal or non-modal dialog |

**Alert vs. Dialog:**

- `alert`: Announces immediately, no user interaction required
- `alertdialog`: Modal dialog requiring user response before proceeding
- `dialog`: General purpose dialog, may be modal or non-modal

────────────────────────────────────────────────────────────────────────────────
                                                            // landmark // roles
────────────────────────────────────────────────────────────────────────────────

## LandmarkRole (8 Roles)

Page region navigation for screen reader users.

**LandmarkRole Enum:**

| Constructor | ARIA String | HTML5 Element | Unique | Label Required |
|-------------|-------------|---------------|--------|----------------|
| `LandmarkBanner` | `banner` | `<header>` (top-level) | Yes | No |
| `LandmarkComplementary` | `complementary` | `<aside>` | No | Recommended |
| `LandmarkContentinfo` | `contentinfo` | `<footer>` (top-level) | Yes | No |
| `LandmarkForm` | `form` | `<form>` (with name) | No | **Yes** |
| `LandmarkMain` | `main` | `<main>` | **Yes** | No |
| `LandmarkNavigation` | `navigation` | `<nav>` | No | Recommended |
| `LandmarkRegion` | `region` | `<section>` (with name) | No | **Yes** |
| `LandmarkSearch` | `search` | — | No | Recommended |

**Uniqueness Rules:**

```purescript
isUniqueLandmark :: LandmarkRole -> Boolean
isUniqueLandmark LandmarkMain = true        -- Exactly one per page
isUniqueLandmark LandmarkBanner = true      -- At most one at top level
isUniqueLandmark LandmarkContentinfo = true -- At most one at top level
isUniqueLandmark _ = false
```

**Label Requirements:**

```purescript
requiresLabel :: LandmarkRole -> Boolean
requiresLabel LandmarkForm = true    -- Must have accessible name
requiresLabel LandmarkRegion = true  -- Must have accessible name
requiresLabel _ = false              -- Optional but recommended for multiples
```

**Best Practices:**

1. Use exactly one `main` landmark per page
2. `banner` and `contentinfo` should be at page root (not nested)
3. Multiple `navigation` landmarks should have distinct `aria-label` values
4. `search` is for site-wide search, not in-page filtering
5. `region` without an accessible name is meaningless to screen readers

────────────────────────────────────────────────────────────────────────────────
                                                           // tristate // values
────────────────────────────────────────────────────────────────────────────────

## Tristate

Three-valued state for `aria-pressed` and `aria-checked`.

**Tristate Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `TriFalse` | `false` | Not pressed/checked |
| `TriTrue` | `true` | Pressed/checked |
| `TriMixed` | `mixed` | Indeterminate state |

**Use Cases:**

- **Toggle buttons**: Pressed (true), not pressed (false), partially pressed (mixed)
- **Checkboxes**: Checked (true), unchecked (false), indeterminate (mixed)
- **Tree selection**: All children selected (true), none selected (false), some selected (mixed)

```purescript
import Hydrogen.Schema.Accessibility.State (Tristate(..), tristateToString)

-- Indeterminate checkbox (some children selected)
indeterminateState :: String
indeterminateState = tristateToString TriMixed  -- "mixed"
```

────────────────────────────────────────────────────────────────────────────────
                                                                // aria // states
────────────────────────────────────────────────────────────────────────────────

## ARIA States (10 State Types)

States reflect current element conditions that change during interaction.

### AriaExpanded

Collapsible element expansion state.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaExpanded Boolean` | `true`, `false` | `aria-expanded` |

**Used with:** disclosure buttons, accordions, tree items, menus

### AriaSelected

Selection state within composite widgets.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaSelected Boolean` | `true`, `false` | `aria-selected` |

**Used with:** listbox options, grid cells, tabs, tree items

### AriaPressed

Toggle button pressed state.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaPressed Tristate` | `true`, `false`, `mixed` | `aria-pressed` |

**Used with:** toggle buttons, toolbar buttons

### AriaChecked

Checkbox/radio checked state.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaChecked Tristate` | `true`, `false`, `mixed` | `aria-checked` |

**Used with:** checkboxes, radios, menu item checkboxes, switches

### AriaDisabled

Perceivable but not operable state.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaDisabled Boolean` | `true`, `false` | `aria-disabled` |

**Used with:** any interactive element

**Note:** Unlike HTML `disabled`, `aria-disabled` elements remain focusable.
Use this when you want to explain *why* something is disabled.

### AriaHidden

Hide element from accessibility API.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaHidden Boolean` | `true`, `false` | `aria-hidden` |

**Warning:** `aria-hidden="true"` removes the element AND all descendants from
the accessibility tree. Use carefully — hidden content is completely invisible
to screen reader users.

### AriaInvalid

Input validation state.

**AriaInvalid Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `InvalidFalse` | `false` | Valid input |
| `InvalidTrue` | `true` | Invalid input (unspecified reason) |
| `InvalidGrammar` | `grammar` | Grammatical error detected |
| `InvalidSpelling` | `spelling` | Spelling error detected |

**Used with:** textbox, searchbox, spinbutton, combobox

### AriaBusy

Element is being modified (loading state).

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaBusy Boolean` | `true`, `false` | `aria-busy` |

**Used with:** live regions, feeds, dynamic content areas

**Behavior:** When `aria-busy="true"`, assistive technology should wait before
announcing changes. Set to `false` when update is complete.

### AriaCurrent

Current item within a set or process.

**AriaCurrent Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `CurrentFalse` | `false` | Not current |
| `CurrentTrue` | `true` | Current (generic) |
| `CurrentPage` | `page` | Current page in pagination |
| `CurrentStep` | `step` | Current step in wizard/process |
| `CurrentLocation` | `location` | Current location in navigation |
| `CurrentDate` | `date` | Current date in calendar |
| `CurrentTime` | `time` | Current time in schedule |

**Used with:** navigation links, breadcrumbs, pagination, wizards

### AriaGrabbed

Drag-and-drop grabbed state.

| Type | Values | ARIA Attribute |
|------|--------|----------------|
| `AriaGrabbed (Maybe Boolean)` | `undefined`, `true`, `false` | `aria-grabbed` |

**Values:**
- `Nothing` → `undefined` (not draggable)
- `Just false` → `false` (draggable but not grabbed)
- `Just true` → `true` (currently being dragged)

**Note:** `aria-grabbed` and `aria-dropeffect` are deprecated in ARIA 1.1.
Prefer using native HTML drag-and-drop with accessible descriptions.

────────────────────────────────────────────────────────────────────────────────
                                                            // aria // properties
────────────────────────────────────────────────────────────────────────────────

## ARIA Properties

Properties define relationships and characteristics. Unlike states, properties
change infrequently or never during element lifetime.

### Relationship Properties (7 Types)

Define connections between elements.

**AriaLabelledBy**

Elements that provide accessible name.

```purescript
newtype AriaLabelledBy = AriaLabelledBy (Array String)
-- aria-labelledby="title-id subtitle-id"
```

**AriaDescribedBy**

Elements that provide additional description.

```purescript
newtype AriaDescribedBy = AriaDescribedBy (Array String)
-- aria-describedby="help-text error-msg"
```

**AriaControls**

Elements controlled by this element.

```purescript
newtype AriaControls = AriaControls (Array String)
-- aria-controls="panel-1 panel-2"
```

**AriaOwns**

Elements owned by this element (virtual parent/child relationship).

```purescript
newtype AriaOwns = AriaOwns (Array String)
-- aria-owns="popup-menu"
```

**Use case:** When DOM structure doesn't reflect accessibility tree structure.
A combobox might `aria-owns` a listbox popup that's rendered at document root.

**AriaFlowTo**

Next elements in alternate reading order.

```purescript
newtype AriaFlowTo = AriaFlowTo (Array String)
-- aria-flowto="summary section-1"
```

**AriaDetails**

Element containing extended description.

```purescript
newtype AriaDetails = AriaDetails String
-- aria-details="chart-data-table"
```

**Use case:** Link a chart to its data table, an image to extended description.

**AriaErrorMessage**

Element containing error message.

```purescript
newtype AriaErrorMessage = AriaErrorMessage String
-- aria-errormessage="email-error"
```

**Note:** Only exposed when `aria-invalid="true"`.

────────────────────────────────────────────────────────────────────────────────
                                                          // widget // properties
────────────────────────────────────────────────────────────────────────────────

## Widget Properties (10 Types)

### AriaAutocomplete

Autocomplete interaction type.

**AriaAutocomplete Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `AutocompleteNone` | `none` | No autocomplete suggestions |
| `AutocompleteInline` | `inline` | Completion in input field |
| `AutocompleteList` | `list` | Popup list of suggestions |
| `AutocompleteBoth` | `both` | Inline completion + popup list |

### AriaHaspopup

Type of popup element triggered.

**AriaHaspopup Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `HasPopupFalse` | `false` | No popup |
| `HasPopupTrue` | `true` | Generic popup (legacy) |
| `HasPopupMenu` | `menu` | Context menu |
| `HasPopupListbox` | `listbox` | Selection listbox |
| `HasPopupTree` | `tree` | Hierarchical tree |
| `HasPopupGrid` | `grid` | Data grid |
| `HasPopupDialog` | `dialog` | Modal/non-modal dialog |

### AriaOrientation

Widget orientation.

**AriaOrientation Enum:**

| Constructor | ARIA String | Description |
|-------------|-------------|-------------|
| `OrientationHorizontal` | `horizontal` | Horizontal layout |
| `OrientationVertical` | `vertical` | Vertical layout |
| `OrientationUndefined` | `undefined` | Orientation not applicable |

**Used with:** scrollbar, slider, separator, tablist, toolbar, menu

### AriaPosInSet

Position within current set (1-indexed).

```purescript
newtype AriaPosInSet = AriaPosInSet Int
-- aria-posinset="3" (third item)
```

**Required when:** DOM doesn't contain all items (virtualized lists).

### AriaSetSize

Total number of items in set.

```purescript
newtype AriaSetSize = AriaSetSize (Maybe Int)
-- aria-setsize="100" or aria-setsize="-1" (unknown)
```

**Values:**
- `Just n` → Known size
- `Nothing` → Unknown/infinite size (renders as `-1`)

### AriaLevel

Hierarchical level (1-indexed).

```purescript
newtype AriaLevel = AriaLevel Int
-- aria-level="2" (like <h2>)
```

**Used with:** heading, listitem, treeitem, row

### AriaValueNow, AriaValueMin, AriaValueMax

Range widget values.

```purescript
newtype AriaValueNow = AriaValueNow Number  -- Current value
newtype AriaValueMin = AriaValueMin Number  -- Minimum value
newtype AriaValueMax = AriaValueMax Number  -- Maximum value
```

**Used with:** progressbar, scrollbar, slider, spinbutton, meter

### AriaValueText

Human-readable value representation.

```purescript
newtype AriaValueText = AriaValueText String
-- aria-valuetext="Medium (50%)"
```

**Use case:** When numeric value isn't meaningful. A slider with values 1-5
might have `aria-valuetext="Medium"` when `aria-valuenow="3"`.

────────────────────────────────────────────────────────────────────────────────
                                                           // label // properties
────────────────────────────────────────────────────────────────────────────────

## Label Properties (3 Types)

### AriaLabel

Accessible name string.

```purescript
newtype AriaLabel = AriaLabel String
-- aria-label="Close dialog"
```

**Priority:** `aria-labelledby` > `aria-label` > native label (`<label>`) > content

### AriaPlaceholder

Input hint text.

```purescript
newtype AriaPlaceholder = AriaPlaceholder String
-- aria-placeholder="Enter your email"
```

**Note:** Placeholder is NOT a substitute for a label. Always provide both.

### AriaRoleDescription

Human-readable role description.

```purescript
newtype AriaRoleDescription = AriaRoleDescription String
-- aria-roledescription="slide"
```

**Warning:** Use sparingly. Most roles shouldn't override their description.
Valid use case: A custom carousel item described as "slide" rather than "group".

────────────────────────────────────────────────────────────────────────────────
                                                            // live // regions
────────────────────────────────────────────────────────────────────────────────

## Live Region Fundamentals

Live regions allow assistive technology to announce dynamic content changes
without requiring user navigation.

### Politeness

How urgently content should be announced.

**Politeness Enum:**

| Constructor | ARIA String | Behavior | Use When |
|-------------|-------------|----------|----------|
| `Off` | `off` | No announcements | Default, or for decorative updates |
| `Polite` | `polite` | Announce after current speech | Most updates |
| `Assertive` | `assertive` | Interrupt immediately | **Critical alerts only** |

**Critical Guidance:**

```
                     ╔═══════════════════════════════════════╗
                     ║  assertive interrupts the user.       ║
                     ║  Use it ONLY for critical alerts.     ║
                     ║                                       ║
                     ║  - Form submission errors             ║
                     ║  - Session expiration warnings        ║
                     ║  - Connection lost notifications      ║
                     ║                                       ║
                     ║  NOT for:                             ║
                     ║  - "Item added to cart"               ║
                     ║  - "Message received"                 ║
                     ║  - Loading indicators                 ║
                     ╚═══════════════════════════════════════╝
```

### AriaAtomic

Announce entire region or just changes.

| Value | Behavior |
|-------|----------|
| `true` | Announce entire region contents on any change |
| `false` | Announce only the changed nodes (default) |

**Use `atomic: true` when:**
- Status message replaces previous status
- Counter updates (announce "3 items" not "3")
- Formatted values ("$1,234.56" not "6")

### Relevance

Which types of changes to announce.

**Relevance Enum:**

| Constructor | ARIA String | Announces |
|-------------|-------------|-----------|
| `RelevanceAdditions` | `additions` | New nodes inserted |
| `RelevanceRemovals` | `removals` | Nodes removed |
| `RelevanceText` | `text` | Text content changed |
| `RelevanceAll` | `all` | All changes (additions, removals, text) |

**AriaRelevant** accepts an array — values are space-separated:

```purescript
newtype AriaRelevant = AriaRelevant (Array Relevance)
-- aria-relevant="additions text" (default)
```

────────────────────────────────────────────────────────────────────────────────
                                                      // live // region // molecule
────────────────────────────────────────────────────────────────────────────────

## LiveRegionConfig

Composed live region configuration.

```purescript
type LiveRegionConfig =
  { live :: Politeness
  , atomic :: Boolean
  , relevant :: Array Relevance
  }
```

### Presets

**defaultLiveRegion** — Standard polite region

```purescript
defaultLiveRegion :: LiveRegionConfig
defaultLiveRegion =
  { live: Polite
  , atomic: false
  , relevant: [ RelevanceAdditions, RelevanceText ]
  }
```

**assertive** — Urgent messages

```purescript
assertive :: LiveRegionConfig
assertive = defaultLiveRegion { live = Assertive }
```

**statusRegion** — Replacing status messages

```purescript
statusRegion :: LiveRegionConfig
statusRegion =
  { live: Polite
  , atomic: true
  , relevant: [ RelevanceAdditions, RelevanceText ]
  }
```

Use for: "Saving...", "Saved", "3 results found"

**alertRegion** — Critical alerts

```purescript
alertRegion :: LiveRegionConfig
alertRegion =
  { live: Assertive
  , atomic: true
  , relevant: [ RelevanceAll ]
  }
```

Use for: "Session expires in 1 minute", "Connection lost"

**logRegion** — Append-only logs

```purescript
logRegion :: LiveRegionConfig
logRegion =
  { live: Polite
  , atomic: false
  , relevant: [ RelevanceAdditions ]
  }
```

Use for: Chat messages, activity feeds, console output

────────────────────────────────────────────────────────────────────────────────
                                                     // accessibility // molecules
────────────────────────────────────────────────────────────────────────────────

## Accessibility Molecules

Composed patterns that combine multiple ARIA attributes.

### DisclosureState

Expandable content pattern (accordions, details, dropdowns).

```purescript
type DisclosureState =
  { expanded :: Boolean
  , controlsId :: Maybe String
  }
```

**Constructor Functions:**

```purescript
disclosureExpanded :: Maybe String -> DisclosureState
disclosureExpanded controlsId = { expanded: true, controlsId }

disclosureCollapsed :: Maybe String -> DisclosureState
disclosureCollapsed controlsId = { expanded: false, controlsId }
```

**Rendered Attributes:**
- `aria-expanded="true"` or `aria-expanded="false"`
- `aria-controls="panel-id"` (if controlsId provided)

### SelectionState

Selectable item pattern (listbox, tree, grid).

```purescript
type SelectionState =
  { selected :: Boolean
  , multiselectable :: Boolean
  , posInSet :: Maybe Int
  , setSize :: Maybe Int
  }
```

**Constructor Functions:**

```purescript
-- Single selection (listbox item)
singleSelect :: Boolean -> SelectionState
singleSelect selected =
  { selected
  , multiselectable: false
  , posInSet: Nothing
  , setSize: Nothing
  }

-- Multi-selection with position (virtualized list)
multiSelect :: Boolean -> Int -> Int -> SelectionState
multiSelect selected pos size =
  { selected
  , multiselectable: true
  , posInSet: Just pos
  , setSize: Just size
  }
```

**Rendered Attributes:**
- `aria-selected="true"` or `aria-selected="false"`
- `aria-multiselectable="true"` (on container, if multiselectable)
- `aria-posinset="3"` (if posInSet provided)
- `aria-setsize="100"` (if setSize provided)

### RangeState

Range widget pattern (sliders, progress bars, spinbuttons).

```purescript
type RangeState =
  { valueNow :: Number
  , valueMin :: Number
  , valueMax :: Number
  , valueText :: Maybe String
  }
```

**Constructor Function:**

```purescript
mkRange :: Number -> Number -> Number -> RangeState
mkRange minVal maxVal nowVal =
  { valueNow: nowVal
  , valueMin: minVal
  , valueMax: maxVal
  , valueText: Nothing
  }
```

**Normalization Formula:**

```purescript
normalizeRange :: RangeState -> Number
normalizeRange r =
  let range = r.valueMax - r.valueMin
  in if range == 0.0
     then 0.0
     else (r.valueNow - r.valueMin) / range
```

Returns value in range `[0.0, 1.0]` for progress bar rendering.

**Rendered Attributes:**
- `aria-valuenow="50"`
- `aria-valuemin="0"`
- `aria-valuemax="100"`
- `aria-valuetext="Medium"` (if valueText provided)

### TabState

Tab/tablist pattern.

```purescript
type TabState =
  { selected :: Boolean
  , posInSet :: Int
  , setSize :: Int
  , controlsPanelId :: String
  }
```

**Constructor Function:**

```purescript
mkTabState :: Boolean -> Int -> Int -> String -> TabState
mkTabState selected pos size panelId =
  { selected
  , posInSet: pos
  , setSize: size
  , controlsPanelId: panelId
  }
```

**Rendered Attributes (on tab):**
- `role="tab"`
- `aria-selected="true"` or `aria-selected="false"`
- `aria-posinset="2"`
- `aria-setsize="5"`
- `aria-controls="panel-2"`
- `tabindex="0"` (if selected) or `tabindex="-1"` (if not)

### DialogState

Modal/non-modal dialog pattern.

```purescript
type DialogState =
  { modal :: Boolean
  , labelledById :: Maybe String
  , describedById :: Maybe String
  }
```

**Constructor Functions:**

```purescript
modalDialog :: Maybe String -> Maybe String -> DialogState
modalDialog labelId descId =
  { modal: true
  , labelledById: labelId
  , describedById: descId
  }

nonModalDialog :: Maybe String -> Maybe String -> DialogState
nonModalDialog labelId descId =
  { modal: false
  , labelledById: labelId
  , describedById: descId
  }
```

**Rendered Attributes:**
- `role="dialog"`
- `aria-modal="true"` (if modal)
- `aria-labelledby="dialog-title"` (if labelledById provided)
- `aria-describedby="dialog-desc"` (if describedById provided)

────────────────────────────────────────────────────────────────────────────────
                                                    // state // rendering // rules
────────────────────────────────────────────────────────────────────────────────

## State-to-Attribute Functions

Each state type has a corresponding rendering function.

| Function | Input Type | Output Example |
|----------|------------|----------------|
| `expandedToAttr` | `AriaExpanded` | `"true"` / `"false"` |
| `selectedToAttr` | `AriaSelected` | `"true"` / `"false"` |
| `pressedToAttr` | `AriaPressed` | `"true"` / `"false"` / `"mixed"` |
| `checkedToAttr` | `AriaChecked` | `"true"` / `"false"` / `"mixed"` |
| `disabledToAttr` | `AriaDisabled` | `"true"` / `"false"` |
| `hiddenToAttr` | `AriaHidden` | `"true"` / `"false"` |
| `invalidToAttr` | `AriaInvalid` | `"false"` / `"true"` / `"grammar"` / `"spelling"` |
| `busyToAttr` | `AriaBusy` | `"true"` / `"false"` |
| `currentToAttr` | `AriaCurrent` | `"false"` / `"true"` / `"page"` / `"step"` / ... |
| `grabbedToAttr` | `AriaGrabbed` | `"undefined"` / `"true"` / `"false"` |

**Type Safety:**

These functions guarantee valid ARIA attribute values. You cannot produce
`aria-expanded="yes"` or `aria-checked="partial"` — the type system prevents it.

────────────────────────────────────────────────────────────────────────────────
                                                       // role // state // matrix
────────────────────────────────────────────────────────────────────────────────

## Required/Supported States by Role

Not all states apply to all roles. This matrix shows key relationships.

| Role | expanded | selected | pressed | checked | disabled | required states |
|------|----------|----------|---------|---------|----------|-----------------|
| button | — | — | ✓ | — | ✓ | none |
| checkbox | — | — | — | **✓** | ✓ | `aria-checked` |
| combobox | **✓** | — | — | — | ✓ | `aria-expanded` |
| gridcell | **✓** | ✓ | — | — | ✓ | none |
| link | — | — | — | — | ✓ | none |
| listbox | — | — | — | — | ✓ | none |
| menuitem | — | — | — | — | ✓ | none |
| menuitemcheckbox | — | — | — | **✓** | ✓ | `aria-checked` |
| option | — | ✓ | — | — | ✓ | `aria-selected` (if selectable) |
| radio | — | — | — | **✓** | ✓ | `aria-checked` |
| slider | — | — | — | — | ✓ | `aria-valuenow` |
| switch | — | — | — | **✓** | ✓ | `aria-checked` |
| tab | — | **✓** | — | — | ✓ | `aria-selected` |
| tree | — | — | — | — | ✓ | none |
| treeitem | **✓** | ✓ | — | ✓ | ✓ | none |

**Legend:**
- **✓** = Required state for this role
- ✓ = Supported state for this role
- — = Not applicable

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Accessibility/
├── Landmark.purs     # 8 landmark roles, uniqueness/label queries
├── LiveRegion.purs   # Politeness, atomic, relevance, presets
├── Molecules.purs    # Disclosure, selection, range, tab, dialog patterns
├── Property.purs     # 17 relationship/widget/label properties
├── Role.purs         # 59 roles (widget, composite, structure, window)
└── State.purs        # 10 ARIA states with rendering functions
```

6 files, 1,115 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Type-Safe Accessibility

### The Problem with String-Based ARIA

Traditional ARIA is stringly-typed:

```html
<!-- Valid? Invalid? Runtime only knows. -->
<div role="buttn" aria-expanded="yes" aria-pressed="maybe">
```

Typos (`buttn`), invalid values (`yes`), impossible combinations — all silently
accepted, breaking assistive technology.

### The Hydrogen Solution

Every ARIA concept is a bounded type:

```purescript
-- Compile-time guarantee: only valid roles
data WidgetRole = RoleButton | RoleCheckbox | ...

-- Compile-time guarantee: only valid tristate values
data Tristate = TriFalse | TriTrue | TriMixed

-- Compile-time guarantee: correct relationship
buttonWithDisclosure :: { role :: WidgetRole, expanded :: AriaExpanded }
buttonWithDisclosure = { role: RoleButton, expanded: AriaExpanded true }
```

### At Billion-Agent Scale

When autonomous agents generate UI:

1. **Invalid ARIA is impossible** — Types prevent malformed output
2. **Roles compose correctly** — Composite roles contain correct children
3. **Live regions are predictable** — Politeness levels are explicit
4. **Landmarks are unique** — One main, one banner, one contentinfo
5. **States match roles** — Checkboxes have checked, tabs have selected

An agent producing accessible UI doesn't need to memorize ARIA spec details.
The type system encodes the specification. Correct-by-construction.

### Accessibility as Infrastructure

Hydrogen treats accessibility as **foundational infrastructure**, not a compliance
checkbox. Every Element carries its accessibility semantics as pure data.

When you compose:
```purescript
Tab { selected: true, controls: "panel-1" } [ text "Overview" ]
```

The accessibility information is intrinsic to the Element. The runtime renders
correct ARIA attributes. Screen readers work. Keyboard navigation works.
Because it cannot be any other way.

────────────────────────────────────────────────────────────────────────────────
                                                          // keyboard // patterns
────────────────────────────────────────────────────────────────────────────────

## Standard Keyboard Navigation

WAI-ARIA defines keyboard patterns for composite widgets.

### Tab Key

- **Tab** moves focus to the composite widget
- Once inside, **Tab** moves to next focusable element outside
- Arrow keys navigate within the widget

### Arrow Keys by Role

| Role | ↑/↓ | ←/→ | Home/End |
|------|-----|-----|----------|
| `listbox` | Previous/next option | — | First/last option |
| `menu` | Previous/next item | Submenu in/out | First/last item |
| `menubar` | Submenu | Previous/next menu | First/last menu |
| `tablist` | (vertical) | Previous/next tab | First/last tab |
| `tree` | Previous/next visible | Expand/collapse | First/last |
| `grid` | Previous/next row | Previous/next cell | Row start/end |
| `radiogroup` | Previous/next radio | — | First/last radio |

### Activation Keys

| Key | Action |
|-----|--------|
| **Enter** | Activate button, link, menuitem |
| **Space** | Toggle checkbox, activate button |
| **Escape** | Close dialog, menu, tooltip |

────────────────────────────────────────────────────────────────────────────────
                                                             // focus // management
────────────────────────────────────────────────────────────────────────────────

## Focus Management Patterns

### Roving tabindex

For composite widgets, one child is tabbable at a time:

```
tablist (tabindex="-1")
├── tab (tabindex="0", selected)    ← Focus lands here
├── tab (tabindex="-1")
└── tab (tabindex="-1")
```

Arrow keys move `tabindex="0"` between children.

### Focus Trapping

Modal dialogs trap focus:
- Tab wraps from last to first focusable element
- Shift+Tab wraps from first to last
- Escape closes dialog, returns focus to trigger

### Focus on Disclosure

When expanding content:
1. Focus may stay on trigger (accordion)
2. Focus may move to content (dropdown menu)
3. Depends on pattern — menuitem moves focus, button doesn't

────────────────────────────────────────────────────────────────────────────────
                                                            // complete // summary
────────────────────────────────────────────────────────────────────────────────

## Complete Type Inventory

### Roles (59 total)

| Category | Count | Types |
|----------|-------|-------|
| Widget | 20 | `WidgetRole` |
| Composite | 9 | `CompositeRole` |
| Structure | 27 | `StructureRole` |
| Window | 3 | `WindowRole` |
| Landmark | 8 | `LandmarkRole` |

### States (10 total)

| Type | Values |
|------|--------|
| `AriaExpanded` | Boolean |
| `AriaSelected` | Boolean |
| `AriaPressed` | Tristate |
| `AriaChecked` | Tristate |
| `AriaDisabled` | Boolean |
| `AriaHidden` | Boolean |
| `AriaInvalid` | 4-variant enum |
| `AriaBusy` | Boolean |
| `AriaCurrent` | 7-variant enum |
| `AriaGrabbed` | Maybe Boolean |

### Properties (17 total)

| Category | Count | Types |
|----------|-------|-------|
| Relationship | 7 | LabelledBy, DescribedBy, Controls, Owns, FlowTo, Details, ErrorMessage |
| Widget | 10 | Autocomplete, Haspopup, Orientation, PosInSet, SetSize, Level, ValueNow/Min/Max, ValueText |
| Label | 3 | Label, Placeholder, RoleDescription |

### Live Region (4 types)

| Type | Purpose |
|------|---------|
| `Politeness` | Announcement urgency |
| `AriaAtomic` | Whole vs. partial announce |
| `Relevance` | Change type filtering |
| `LiveRegionConfig` | Composed configuration |

### Molecules (5 patterns)

| Pattern | ARIA Attributes Combined |
|---------|-------------------------|
| `DisclosureState` | expanded, controls |
| `SelectionState` | selected, multiselectable, posinset, setsize |
| `RangeState` | valuenow, valuemin, valuemax, valuetext |
| `TabState` | selected, posinset, setsize, controls |
| `DialogState` | modal, labelledby, describedby |

────────────────────────────────────────────────────────────────────────────────
