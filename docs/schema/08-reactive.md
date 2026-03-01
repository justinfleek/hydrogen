━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 08 // reactive
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Reactive Pillar

State management, validation, focus, interaction feedback.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Reactive/`
- **Files**: 48 modules
- **Key features**: Interactive states, validation, focus management, loading

## Purpose

Reactive provides bounded, deterministic primitives for:
- Interactive element states (hover, focus, press)
- Form validation lifecycle
- Async data fetching states
- Focus management and accessibility
- Progress tracking (upload, download, render)
- Selection and drag states

────────────────────────────────────────────────────────────────────────────────
                                                         // interactive // state
────────────────────────────────────────────────────────────────────────────────

## Interactive State

Combined state for UI elements responding to user input.

### PointerState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `PointerIdle` | `"idle"` | Not interacting |
| `PointerHover` | `"hover"` | Pointer over element |
| `PointerPressed` | `"pressed"` | Pointer down on element |
| `PointerDragging` | `"dragging"` | Being dragged |

### FocusState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FocusNone` | `"none"` | Not focused |
| `FocusKeyboard` | `"keyboard"` | Focus via Tab/arrows |
| `FocusPointer` | `"pointer"` | Focus via click |
| `FocusProgrammatic` | `"programmatic"` | Focus via JavaScript |

**Key insight:** Distinguishing focus source enables `:focus-visible` behavior —
show focus rings for keyboard users but not mouse users.

### ActivationState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Inactive` | `"inactive"` | Default state |
| `Activating` | `"activating"` | Enter animation |
| `Active` | `"active"` | Fully active |
| `Deactivating` | `"deactivating"` | Exit animation |

### InteractiveState Molecule

```purescript
type InteractiveState =
  { pointer :: PointerState
  , focus :: FocusState
  , activation :: ActivationState
  , disabled :: Boolean
  , loading :: Boolean
  , device :: PointerDevice
  }
```

**Predicates:**
- `isInteractable` — Not disabled and not loading
- `isEngaged` — Pointer over or focused

**Outputs:**
- `toAriaAttributes` — Generate ARIA attributes
- `toLegacyCssClasses` — Generate CSS class list

────────────────────────────────────────────────────────────────────────────────
                                                          // validation // state
────────────────────────────────────────────────────────────────────────────────

## Validation State

Form field validation lifecycle.

### ValidationResult Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ValidationValid` | `"valid"` | Passes all rules |
| `ValidationInvalid` | `"invalid"` | Fails one or more rules |
| `ValidationPending` | `"pending"` | Async validation in progress |
| `ValidationSkipped` | `"skipped"` | Not performed (disabled field) |

### ValidationSeverity Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `SeverityError` | `"error"` | Blocks submission |
| `SeverityWarning` | `"warning"` | Allows submission with caution |
| `SeverityInfo` | `"info"` | Informational only |

### ModificationState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Pristine` | `"pristine"` | Value equals initial value |
| `Modified` | `"modified"` | Value differs from initial |

### TouchState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Untouched` | `"untouched"` | Never focused |
| `Touched` | `"touched"` | Has been focused and blurred |

### FieldValidation Molecule

```purescript
type FieldValidation =
  { result :: ValidationResult
  , messages :: Array ValidationMessage
  , modification :: ModificationState
  , touch :: TouchState
  , isValidating :: Boolean
  , validateOnBlur :: Boolean
  , validateOnChange :: Boolean
  }
```

**Key insight:** `shouldShowError` only returns true for touched fields — 
don't punish users before they've had a chance to interact.

### FormValidation Compound

```purescript
type FormValidation =
  { fields :: Array { name :: String, validation :: FieldValidation }
  , isSubmitting :: Boolean
  , isSubmitted :: Boolean
  , submitCount :: Int
  , isValid :: Boolean
  , isDirty :: Boolean
  }
```

**Computed:**
- `isFormSubmittable` — Valid and not submitting
- `touchedFieldCount`, `dirtyFieldCount`, `invalidFieldCount`

────────────────────────────────────────────────────────────────────────────────
                                                               // data // state
────────────────────────────────────────────────────────────────────────────────

## Data State

Async data fetching lifecycle.

### FetchState Enum

| Constructor | Description |
|-------------|-------------|
| `Idle` | Not yet requested |
| `Fetching` | Request in flight |
| `Revalidating a` | Refetching with stale data |
| `Success a` | Request succeeded |
| `Failure e` | Request failed |

Complements RemoteData with stale-while-revalidate support.

### Freshness Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Fresh` | `"fresh"` | Data is current |
| `Stale` | `"stale"` | Data may be outdated |
| `FreshnessUnknown` | `"unknown"` | No freshness info |

### MutationState Enum

| Constructor | Description |
|-------------|-------------|
| `MutationIdle` | No mutation in progress |
| `MutationPending` | Mutation submitted |
| `MutationOptimistic` | Optimistic update applied |
| `MutationSuccess` | Mutation confirmed |
| `MutationError e` | Mutation failed |
| `MutationRollingBack` | Reverting optimistic update |

### LoadingState Molecule

```purescript
type LoadingState e =
  { loading :: Boolean
  , progress :: Number      -- 0.0 to 1.0
  , error :: Maybe e
  , indeterminate :: Boolean
  , message :: Maybe String
  }
```

**Constructors:**
- `notLoading` — Initial state
- `loadingIndeterminate` — Spinner
- `loadingProgress` — Progress bar
- `loadingWithMessage` — With status text
- `loadingComplete` — Finished
- `loadingFailed` — Error state

────────────────────────────────────────────────────────────────────────────────
                                                               // focus // mgmt
────────────────────────────────────────────────────────────────────────────────

## Focus Management

Keyboard navigation and focus indicators.

### FocusVisibility Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FocusVisible` | `"visible"` | Always show indicator |
| `FocusHidden` | `"hidden"` | Never show indicator |
| `FocusAuto` | `"auto"` | Only for keyboard (:focus-visible) |

### FocusOrigin Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `KeyboardOrigin` | `"keyboard"` | Tab or arrow keys |
| `MouseOrigin` | `"mouse"` | Mouse click |
| `TouchOrigin` | `"touch"` | Touch |
| `ProgrammaticOrigin` | `"programmatic"` | JavaScript |

### FocusRingStyle Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `OutlineRing` | `"outline"` | CSS outline (no layout impact) |
| `ShadowRing` | `"shadow"` | Box shadow |
| `BorderRing` | `"border"` | Border change |

### FocusRing Molecule

```purescript
type FocusRing =
  { style :: FocusRingStyle
  , color :: RGBA
  , width :: Number
  , offset :: Number
  , visibility :: FocusVisibility
  , enabled :: Boolean
  -- Two-ring pattern for accessibility
  , twoRingEnabled :: Boolean
  , innerColor :: RGBA
  , outerColor :: RGBA
  , innerWidth :: Number
  , outerWidth :: Number
  }
```

**WCAG 2.2 Focus Appearance:**
- Focus indicator must have 3:1 contrast
- Minimum 2px thickness
- Must be visible on both light and dark backgrounds

**Two-Ring Pattern (Figma, VS Code):**
Inner dark ring + outer light ring guarantees contrast on any background.

**Presets:**
- `defaultFocusRing` — Blue outline, auto visibility
- `accessibleFocusRing` — Two-ring for WCAG compliance
- `highContrastFocusRing` — Maximum visibility
- `invertedFocusRing` — For dark backgrounds

### FocusTrap Molecule

```purescript
type FocusTrap =
  { mode :: FocusTrapMode
  , active :: Boolean
  , returnFocusOnDeactivate :: Boolean
  , initialFocusId :: Maybe String
  , finalFocusId :: Maybe String
  , clickOutsideDeactivates :: Boolean
  , escapeDeactivates :: Boolean
  }
```

**Modes:**
- `HardTrap` — Focus cannot leave (modals)
- `SoftTrap` — Focus returns after leaving (panels)
- `NoTrap` — No trapping

### RovingTabindex Molecule

For composite widgets (toolbars, menus, listboxes):

```purescript
type RovingTabindex =
  { focusedIndex :: Int
  , itemCount :: Int
  , wrap :: Boolean
  , vertical :: Boolean
  }
```

**Operations:**
- `rovingMoveNext`, `rovingMovePrev`
- `rovingMoveFirst`, `rovingMoveLast`

────────────────────────────────────────────────────────────────────────────────
                                                                    // progress
────────────────────────────────────────────────────────────────────────────────

## Progress

Normalized progress tracking.

### Progress Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Progress | Number | 0.0 | 1.0 | clamps | Normalized progress |

### Specialized Progress Types

| Type | Purpose |
|------|---------|
| `UploadProgress` | File upload |
| `DownloadProgress` | File download |
| `BufferProgress` | Media buffering |
| `RenderProgress` | Video/image rendering |
| `ProcessingProgress` | General computation |
| `SeekProgress` | Media playhead position |

### TransferProgress Molecule

For uploads/downloads with byte counts:

```purescript
type TransferProgress =
  { loaded :: Number        -- Bytes transferred
  , total :: Number         -- Total bytes
  , rate :: Number          -- Bytes per second
  , progress :: Progress    -- Normalized 0-1
  }
```

### StepProgress Molecule

For wizard/multi-step processes:

```purescript
type StepProgress =
  { current :: Int          -- Current step (1-indexed)
  , total :: Int            -- Total steps
  , progress :: Progress    -- Normalized 0-1
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                               // source // files
────────────────────────────────────────────────────────────────────────────────

## Source Structure

```
src/Hydrogen/Schema/Reactive/
├── ButtonSemantics.purs      # Button semantic states
├── ContainerQuery.purs       # Container query atoms
├── DataState.purs            # Async data lifecycle
├── DataValidity.purs         # Data validity (leader)
├── DataValidity/             # Validity submodules
├── DragState.purs            # Drag and drop states
├── Feedback.purs             # User feedback (leader)
├── Feedback/                 # Feedback submodules
├── Flags.purs                # Boolean state flags
├── FocusManagement.purs      # Focus ring, trap, roving
├── HoverEffect.purs          # Hover effects (leader)
├── HoverEffect/              # Hover submodules
├── InteractiveState.purs     # Pointer, focus, activation
├── MediaState.purs           # Media playback state
├── NetworkState.purs         # Online/offline states
├── PresenceState.purs        # User presence
├── Progress.purs             # Progress atoms
├── ScrollState.purs          # Scroll position state
├── SelectionState.purs       # Selection atoms
├── SkeletonConfig.purs       # Loading skeleton config
├── ValidationState.purs      # Form validation lifecycle
└── Viewport.purs             # Viewport queries (leader)
    └── Viewport/             # Viewport submodules
```

**48 files total.**

────────────────────────────────────────────────────────────────────────────────
                                                        // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

The Reactive pillar models **UI state machines** that map directly to:
- CSS pseudo-classes (`:hover`, `:focus`, `:focus-visible`, `:active`)
- ARIA states (`aria-disabled`, `aria-busy`, `aria-invalid`)
- Form library APIs (React Hook Form, Formik, Valibot)

**State vs. Event:**
Reactive types model **states**, not events. An element IS in `PointerHover`
state, not "received a mouseenter event." This matches declarative UI —
the view is a function of state, not a sequence of mutations.

**Validation UX Pattern:**
`shouldShowError` encodes best practice: only show errors after the user
has interacted (touched) with the field. This prevents intimidating users
with errors before they've had a chance to fill in the form.

**Accessibility First:**
Focus management types encode WCAG requirements:
- `:focus-visible` via `FocusOrigin`
- Two-ring pattern for contrast on any background
- Focus trap modes for modal dialogs
- Roving tabindex for composite widgets

**Why This Matters:**
At billion-agent scale, when an agent composes a form, it needs to know:
- What validation states exist and when to transition
- How focus should behave for keyboard navigation
- What ARIA attributes to generate

The Reactive pillar gives agents a **complete vocabulary for interaction** —
not "make the button highlight on hover" but `pointerState: PointerHover`.

────────────────────────────────────────────────────────────────────────────────
