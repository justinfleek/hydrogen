━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 08 // reactive
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Reactive Pillar

State management, validation, focus, interaction feedback, data lifecycle.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Reactive/`
- **Files**: 47 modules across 7 subdomains
- **Lines**: ~11,000 total
- **Key features**: Interactive states, validation lifecycle, focus management,
  async data states, progress tracking, drag/drop, skeleton loading,
  container queries, hover effects, presence animation

## Purpose

Reactive provides bounded, deterministic primitives for modeling UI state 
machines. At billion-agent scale, agents need a complete vocabulary for:

- Interactive element states (hover, focus, press, disabled)
- Form validation lifecycle (pristine, touched, valid, invalid)
- Async data fetching states (idle, loading, success, failure, stale)
- Focus management and accessibility (traps, roving tabindex, rings)
- Progress tracking (upload, download, buffer, render)
- Selection and drag states (single, multi, range, hierarchical)
- Feedback notifications (toast, snackbar, banner, dialog)
- Presence animations (enter, exit, mount lifecycle)
- Container queries (responsive to parent size)
- Data validity for safety-critical systems (DO-178C, FDA compliance)

## Architectural Principle

**State, Not Events.**

Reactive types model **states**, not events. An element IS in `PointerHover`
state, not "received a mouseenter event." This matches declarative UI —
the view is a function of state, not a sequence of mutations.

────────────────────────────────────────────────────────────────────────────────
                                                              // boolean // flags
────────────────────────────────────────────────────────────────────────────────

## Boolean Flags (Atoms)

The most primitive reactive atoms — typed boolean wrappers.

### Core Interactive Flags

| Type | Description |
|------|-------------|
| `EnabledFlag` | Element can receive interaction |
| `DisabledFlag` | Element cannot receive interaction |
| `VisibleFlag` | Element is rendered and takes space |
| `HiddenFlag` | Element is not rendered |
| `FocusedFlag` | Element has keyboard focus |
| `HoveredFlag` | Pointer is over element |
| `PressedFlag` | Element is being pressed |
| `ActiveFlag` | Element is in active/current state |

### Selection Flags

| Type | Description |
|------|-------------|
| `SelectedFlag` | Item is selected in a list/grid |
| `CheckedFlag` | Checkbox/toggle is checked |
| `IndeterminateFlag` | Partial selection (some children) |
| `ExpandedFlag` | Accordion/tree is expanded |
| `CollapsedFlag` | Accordion/tree is collapsed |
| `OpenFlag` | Dropdown/popover/modal is open |

### Data Flags

| Type | Description |
|------|-------------|
| `LoadingFlag` | Data is being fetched |
| `LoadedFlag` | Data has been successfully fetched |
| `RefreshingFlag` | Data is being refetched (SWR) |
| `StaleFlag` | Cached data may be outdated |
| `EmptyFlag` | No data present |
| `BusyFlag` | Operation in progress |

### Form Flags

| Type | Description |
|------|-------------|
| `PristineFlag` | Field has never been modified |
| `DirtyFlag` | Field has been modified |
| `TouchedFlag` | Field has been focused and blurred |
| `UntouchedFlag` | Field has never been focused |
| `ValidFlag` | Field passes validation |
| `InvalidFlag` | Field fails validation |
| `RequiredFlag` | Field must have a value |
| `ReadOnlyFlag` | Field is visible but not editable |

### Media Flags

| Type | Description |
|------|-------------|
| `PlayingFlag` | Media is playing |
| `PausedFlag` | Media is paused |
| `MutedFlag` | Audio is muted |
| `BufferingFlag` | Media is buffering |
| `FullscreenFlag` | Media is in fullscreen mode |

### Presence Flags

| Type | Description |
|------|-------------|
| `MountedFlag` | Component is mounted in DOM |
| `EnteringFlag` | Component is entering (animation) |
| `ExitingFlag` | Component is exiting (animation) |
| `AnimatingFlag` | Any animation is in progress |

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

**Predicates:**
- `isPointerOver :: PointerState -> Boolean`
- `isPointerDown :: PointerState -> Boolean`

### FocusState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FocusNone` | `"none"` | Not focused |
| `FocusKeyboard` | `"keyboard"` | Focus via Tab/arrows |
| `FocusPointer` | `"pointer"` | Focus via click |
| `FocusProgrammatic` | `"programmatic"` | Focus via JavaScript |

**Key insight:** Distinguishing focus source enables `:focus-visible` behavior —
show focus rings for keyboard users but not mouse users.

**Predicates:**
- `hasFocus :: FocusState -> Boolean`
- `showFocusRing :: FocusState -> Boolean` — Only true for keyboard

### ActivationState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Inactive` | `"inactive"` | Default state |
| `Activating` | `"activating"` | Enter animation |
| `Active` | `"active"` | Fully active |
| `Deactivating` | `"deactivating"` | Exit animation |

### PointerDevice Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Mouse` | `"mouse"` | Mouse pointer |
| `Touch` | `"touch"` | Touch screen |
| `Pen` | `"pen"` | Stylus/pen |
| `Unknown` | `"unknown"` | Unidentified |

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

**Presets:**
- `defaultInteractive` — Idle, no focus, inactive

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

### ValidationMessage Molecule

```purescript
type ValidationMessage =
  { severity :: ValidationSeverity
  , message :: String
  , rule :: String        -- Rule identifier ("required", "minLength")
  , params :: Array String -- Rule parameters (["8"] for minLength 8)
  }
```

**Constructors:**
- `errorMessage rule message`
- `warningMessage rule message`
- `infoMessage rule message`

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

**Predicates:**
- `shouldShowError` — Touched AND invalid
- `shouldShowWarning` — Touched AND has warnings
- `hasMessages` — Has any messages
- `firstError` — First error message
- `allErrors` — All error messages
- `allWarnings` — All warning messages

**Presets:**
- `defaultFieldValidation` — Pristine, untouched, valid
- `validField` — Valid field state
- `invalidField rule message` — Invalid with error
- `pendingField` — Async validation in progress

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
- `isFormValid` — All fields valid
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

**Predicates:**
- `isFetchIdle`, `isFetching`, `isFetchSuccess`, `isFetchError`

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

**Predicates:**
- `isMutating` — Mutation in progress
- `isSettled` — Idle, success, or error (not pending)

### DataMeta Molecule

```purescript
type DataMeta =
  { isFetching :: Boolean
  , isStale :: Boolean
  , isRefreshing :: Boolean
  , lastFetchedAt :: Maybe Number
  , errorCount :: Int
  , retryCount :: Int
  }
```

**Predicates:**
- `shouldShowLoading` — Fetching but not refreshing
- `shouldShowStale` — Stale and refreshing
- `canRefresh` — Not currently fetching

### RetryState Molecule

For exponential backoff:

```purescript
type RetryState =
  { attempt :: Int
  , maxAttempts :: Int
  , baseDelayMs :: Number
  , maxDelayMs :: Number
  , lastAttemptAt :: Maybe Number
  }
```

**The Math:**
```
nextRetryDelay = min(maxDelayMs, baseDelayMs × 2^attempt)
```

### LoadingState Molecule

Combined loading + progress + error:

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
- `loadingProgress progress` — Progress bar
- `loadingWithMessage msg` — With status text
- `loadingComplete` — Finished
- `loadingFailed err` — Error state

────────────────────────────────────────────────────────────────────────────────
                                                          // focus // management
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
  , color :: RGBA             -- Primary ring color
  , width :: Number           -- Ring width in pixels
  , offset :: Number          -- Gap between element and ring
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

**WCAG 2.2 Focus Appearance (Level AAA):**
- Focus indicator must have 3:1 contrast against adjacent colors
- Minimum 2px thickness
- Must be visible on both light and dark backgrounds

**Two-Ring Pattern (Figma, VS Code):**
Inner dark ring + outer light ring guarantees contrast on any background.

**Presets:**
- `defaultFocusRing` — Blue outline, auto visibility
- `accessibleFocusRing` — Two-ring for WCAG compliance
- `highContrastFocusRing` — Maximum visibility (black + white)
- `invertedFocusRing` — For dark backgrounds
- `noFocusRing` — Disabled (use sparingly)

**Modifiers:**
- `withRingColor color ring`
- `withRingWidth width ring`
- `withRingOffset offset ring`
- `withTwoRing innerCol outerCol ring`

### FocusTrapMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `HardTrap` | `"hard"` | Focus cannot leave (modals) |
| `SoftTrap` | `"soft"` | Focus returns after leaving |
| `NoTrap` | `"none"` | No trapping behavior |

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

**Presets:**
- `hardTrap` — For modals (no escape, no click outside)
- `softTrap` — For panels (escape and click outside work)
- `disabledTrap` — No trapping

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
- `isRovingFocused index roving`

### FocusScope Compound

```purescript
type FocusScope =
  { id :: String
  , active :: Boolean
  , trap :: FocusTrap
  , ring :: FocusRing
  , focusedElementId :: Maybe String
  , lastFocusedId :: Maybe String
  , parentScopeId :: Maybe String
  }
```

**Presets:**
- `defaultScope id` — No trap
- `modalScope id` — Hard trap

────────────────────────────────────────────────────────────────────────────────
                                                                    // progress
────────────────────────────────────────────────────────────────────────────────

## Progress

Normalized progress tracking.

### Progress Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Progress | Number | 0.0 | 1.0 | clamps | Normalized progress |

**Predicates:**
- `isComplete :: Progress -> Boolean`
- `toPercent :: Progress -> Number` — 0-100

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
                                                            // selection // state
────────────────────────────────────────────────────────────────────────────────

## Selection State

Selection models for lists, grids, and trees.

### SelectionMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `SelectionNone` | `"none"` | No selection allowed |
| `SelectionSingle` | `"single"` | Only one item at a time |
| `SelectionMultiple` | `"multiple"` | Any number of items |
| `SelectionRange` | `"range"` | Contiguous range (shift+click) |

### SelectionStatus Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Selected` | `"selected"` | Item is selected |
| `Unselected` | `"unselected"` | Item is not selected |
| `Indeterminate` | `"indeterminate"` | Partial selection (parent) |

### SelectionAnchor Molecule

Anchor point for range selection:

```purescript
type SelectionAnchor = { index :: Maybe Int }
```

### SelectionRange Molecule

Contiguous selection range:

```purescript
type SelectionRange = { start :: Int, end :: Int }
```

**Operations:**
- `isInRange index range`
- `expandRange index range`
- `rangeSize range`

### SingleSelection Molecule

```purescript
type SingleSelection =
  { selected :: Maybe Int
  , lastSelected :: Maybe Int
  }
```

### MultiSelection Molecule

```purescript
type MultiSelection =
  { indices :: Array Int
  , anchor :: SelectionAnchor
  , lastToggled :: Maybe Int
  , totalCount :: Int
  }
```

**Operations:**
- `selectIndex`, `deselectIndex`, `toggleIndex`
- `selectAll`, `deselectAll`
- `selectRange index` — From anchor to index
- `isAllSelected`, `isNoneSelected`, `isSomeSelected`

### HierarchicalStatus Enum (For Trees)

| Constructor | Description |
|-------------|-------------|
| `FullySelected` | Node and all descendants selected |
| `PartiallySelected` | Some but not all descendants |
| `NotSelected` | Node and all descendants unselected |

**Operations:**
- `computeParentStatus children` — From child statuses

────────────────────────────────────────────────────────────────────────────────
                                                              // drag // state
────────────────────────────────────────────────────────────────────────────────

## Drag State

Drag and drop interaction atoms.

### DragStatus Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `DragIdle` | `"idle"` | No drag in progress |
| `Dragging` | `"dragging"` | Item is being dragged |
| `DraggedOver` | `"dragged-over"` | Drag is over valid target |
| `Dropping` | `"dropping"` | Drop is in progress |

### DropEffect Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `DropCopy` | `"copy"` | Copy data |
| `DropMove` | `"move"` | Move data |
| `DropLink` | `"link"` | Create link |
| `DropNone` | `"none"` | No drop allowed |

### DragType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FileDrag` | `"file"` | File(s) from filesystem |
| `ElementDrag` | `"element"` | DOM element within page |
| `TextDrag` | `"text"` | Text selection |
| `ExternalDrag` | `"external"` | From another application |

### DragPosition Molecule

```purescript
type DragPosition =
  { originX :: Number
  , originY :: Number
  , currentX :: Number
  , currentY :: Number
  }
```

**Operations:**
- `deltaX`, `deltaY` — Change from origin
- `totalDistance` — Euclidean distance traveled

### DragSource Molecule

```purescript
type DragSource =
  { id :: Maybe String
  , dragType :: DragType
  , data :: Maybe String
  , allowedEffects :: Array DropEffect
  , active :: Boolean
  }
```

### DropTarget Molecule

```purescript
type DropTarget =
  { id :: Maybe String
  , accepts :: Array DragType
  , effect :: DropEffect
  , active :: Boolean
  , valid :: Boolean
  }
```

### DropZoneFeedback Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `DropZoneAccepting` | `"accepting"` | Zone will accept drop |
| `DropZoneRejecting` | `"rejecting"` | Zone will reject drop |
| `DropZoneNeutral` | `"neutral"` | No feedback |

### DragState Compound

```purescript
type DragState =
  { status :: DragStatus
  , source :: DragSource
  , target :: DropTarget
  , position :: Maybe DragPosition
  , preview :: DragPreview
  , feedback :: DropZoneFeedback
  }
```

**State Transitions:**
- `startDrag source x y state`
- `updateDragPosition x y state`
- `enterDropZone target state`
- `leaveDropZone state`
- `drop state`
- `cancelDrag state`

**Computed:**
- `isDragActive`, `hasValidDropTarget`, `shouldShowPreview`

────────────────────────────────────────────────────────────────────────────────
                                                            // scroll // state
────────────────────────────────────────────────────────────────────────────────

## Scroll State

Scroll position and behavior atoms.

### ScrollDirection Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ScrollUp` | `"up"` | Scrolling toward top |
| `ScrollDown` | `"down"` | Scrolling toward bottom |
| `ScrollLeft` | `"left"` | Scrolling toward left |
| `ScrollRight` | `"right"` | Scrolling toward right |
| `ScrollIdle` | `"idle"` | Not actively scrolling |

### ScrollBehavior Enum (CSS)

| Constructor | CSS Value | Description |
|-------------|-----------|-------------|
| `SmoothScroll` | `smooth` | Animated scrolling |
| `InstantScroll` | `instant` | Jump immediately |
| `AutoScroll` | `auto` | Browser default |

### OverflowBehavior Enum (CSS)

| Constructor | CSS Value | Description |
|-------------|-----------|-------------|
| `OverflowAuto` | `auto` | Scrollbar when needed |
| `OverflowScroll` | `scroll` | Always show scrollbar |
| `OverflowHidden` | `hidden` | Clip content |
| `OverflowVisible` | `visible` | Content overflows |

### OverscrollBehavior Enum (CSS)

| Constructor | CSS Value | Description |
|-------------|-----------|-------------|
| `OverscrollAuto` | `auto` | Allow scroll chaining |
| `OverscrollContain` | `contain` | Prevent chaining, allow bounce |
| `OverscrollNone` | `none` | Prevent chaining and bounce |

### ScrollSnapType Enum

| Constructor | CSS Value | Description |
|-------------|-----------|-------------|
| `SnapMandatory` | `mandatory` | Must snap to point |
| `SnapProximity` | `proximity` | Snap if close |
| `SnapNone` | `none` | No snapping |

### ScrollSnapAlign Enum

| Constructor | CSS Value | Description |
|-------------|-----------|-------------|
| `SnapAlignStart` | `start` | Snap to start edge |
| `SnapAlignCenter` | `center` | Snap to center |
| `SnapAlignEnd` | `end` | Snap to end edge |

### ScrollProgress Molecule

```purescript
type ScrollProgress = { x :: Number, y :: Number }  -- 0.0 - 1.0
```

**Predicates:**
- `isAtStart`, `isAtEnd`, `isNearEnd` (90% — for infinite scroll)

### ScrollVelocity Molecule

```purescript
type ScrollVelocity = { vx :: Number, vy :: Number }  -- px/sec
```

**Predicates:**
- `isScrolling` — Any velocity
- `isFastScroll` — > 1000 px/s

### ScrollState Compound

```purescript
type ScrollState =
  { position :: ScrollPosition
  , bounds :: ScrollBounds
  , velocity :: ScrollVelocity
  , direction :: ScrollDirection
  , behavior :: ScrollBehavior
  , overflow :: OverflowBehavior
  , overscroll :: OverscrollBehavior
  , snapType :: ScrollSnapType
  , isLocked :: Boolean
  }
```

**Computed:**
- `shouldShowScrollbar`, `shouldLoadMore` (infinite scroll)
- `distanceToEnd`, `scrollPercentage`

────────────────────────────────────────────────────────────────────────────────
                                                            // media // state
────────────────────────────────────────────────────────────────────────────────

## Media State

Audio/video playback state atoms.

### PlaybackStatus Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Playing` | `"playing"` | Actively playing |
| `Paused` | `"paused"` | Paused by user |
| `Stopped` | `"stopped"` | Stopped (at beginning) |
| `Buffering` | `"buffering"` | Waiting for data |
| `Seeking` | `"seeking"` | Seeking to position |
| `Ended` | `"ended"` | Reached end |
| `Error msg` | `"error"` | Playback error |

### ReadyState Enum (HTMLMediaElement.readyState)

| Constructor | Value | Description |
|-------------|-------|-------------|
| `HaveNothing` | 0 | No information |
| `HaveMetadata` | 1 | Duration, dimensions loaded |
| `HaveCurrentData` | 2 | Current frame available |
| `HaveFutureData` | 3 | Some future frames available |
| `HaveEnoughData` | 4 | Can play through without buffering |

### PlaybackRate Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| PlaybackRate | Number | 0.25 | 4.0 | clamps | Speed multiplier |

**Presets:**
- `normalSpeed` — 1.0x
- `halfSpeed` — 0.5x
- `doubleSpeed` — 2.0x

### VolumeLevel Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| VolumeLevel | Number | 0.0 | 1.0 | clamps | Audio volume |

**Presets:**
- `fullVolume` — 1.0
- `halfVolume` — 0.5
- `muted` — 0.0

### TimePosition Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TimePosition | Number | 0.0 | 604800 | clamps | Seconds (7 days max) |

### MediaProgress Molecule

```purescript
type MediaProgress =
  { currentTime :: TimePosition
  , duration :: Duration
  , buffered :: Array BufferedRange
  }
```

**Computed:**
- `progressPercent`, `bufferedPercent`, `remainingTime`

### MediaState Compound

```purescript
type MediaState =
  { status :: PlaybackStatus
  , readyState :: ReadyState
  , networkState :: NetworkLoadState
  , progress :: MediaProgress
  , volume :: VolumeLevel
  , isMuted :: Boolean
  , playbackRate :: PlaybackRate
  , isFullscreen :: Boolean
  , isPictureInPicture :: Boolean
  , loop :: Boolean
  , autoplay :: Boolean
  }
```

**State Transitions:**
- `play`, `pause`, `stop`, `seek pos`
- `setVolume vol`, `toggleMute`, `setPlaybackRate rate`

**Computed:**
- `shouldShowControls`, `shouldShowBuffering`, `canSeek`

────────────────────────────────────────────────────────────────────────────────
                                                           // network // state
────────────────────────────────────────────────────────────────────────────────

## Network State

Connection status and quality atoms.

### ConnectionStatus Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Online` | `"online"` | Connected |
| `Offline` | `"offline"` | No connection |
| `Reconnecting` | `"reconnecting"` | Attempting to restore |

### ConnectionType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Wifi` | `"wifi"` | WiFi connection |
| `Cellular` | `"cellular"` | Mobile data |
| `Ethernet` | `"ethernet"` | Wired connection |
| `Bluetooth` | `"bluetooth"` | Bluetooth tethering |
| `None` | `"none"` | No connection |
| `UnknownType` | `"unknown"` | Cannot determine |

### EffectiveType Enum (Network Information API)

| Constructor | String ID | RTT | Downlink |
|-------------|-----------|-----|----------|
| `Slow2g` | `"slow-2g"` | >2000ms | <50 Kbps |
| `Ect2g` | `"2g"` | >1400ms | <70 Kbps |
| `Ect3g` | `"3g"` | >270ms | <700 Kbps |
| `Ect4g` | `"4g"` | <=270ms | >=700 Kbps |

### RoundTripTime Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| RoundTripTime | Number | 0 | 30000 | clamps | Latency in ms |

**Predicates:**
- `isLowLatency` — < 100ms
- `isHighLatency` — > 300ms

### Downlink Atom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Downlink | Number | 0 | 10000 | clamps | Bandwidth in Mbps |

**Predicates:**
- `isFastDownlink` — > 5 Mbps
- `isSlowDownlink` — < 1 Mbps

### ConnectionQuality Molecule

```purescript
type ConnectionQuality =
  { effectiveType :: EffectiveType
  , rtt :: RoundTripTime
  , downlink :: Downlink
  , saveData :: Boolean
  }
```

**Predicates:**
- `isHighQuality` — 4G, low latency, fast
- `isLowQuality` — Slow 2G/2G or high latency
- `shouldReduceData` — saveData or low quality

### NetworkState Compound

```purescript
type NetworkState =
  { status :: ConnectionStatus
  , connectionType :: ConnectionType
  , quality :: ConnectionQuality
  , lastOnlineAt :: Maybe Number
  , reconnectAttempts :: Int
  , wasOffline :: Boolean
  }
```

**Computed:**
- `canFetch` — Online
- `shouldDeferLargeRequests` — Offline or slow
- `adaptiveImageQuality` — 0.0-1.0 based on connection

────────────────────────────────────────────────────────────────────────────────
                                                          // presence // state
────────────────────────────────────────────────────────────────────────────────

## Presence State

Component mount/unmount lifecycle and animation states.

### PresencePhase Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `PhaseEntering` | `"entering"` | Enter animation in progress |
| `PhaseEntered` | `"entered"` | Fully visible and interactive |
| `PhaseExiting` | `"exiting"` | Exit animation in progress |
| `PhaseExited` | `"exited"` | Ready to unmount |

**Predicates:**
- `isPresent` — Entering, entered, or exiting
- `isAnimating` — Entering or exiting

### MountStatus Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Unmounted` | `"unmounted"` | Not in DOM |
| `Mounting` | `"mounting"` | Being added |
| `Mounted` | `"mounted"` | In DOM |
| `Unmounting` | `"unmounting"` | Being removed |

### AnimationDirection Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Forward` | `"forward"` | Enter from right |
| `Backward` | `"backward"` | Enter from left |
| `NoDirection` | `"none"` | No directional animation |

### PresenceConfig Molecule

```purescript
type PresenceConfig =
  { enterDurationMs :: Number
  , exitDurationMs :: Number
  , enterDelay :: Number
  , exitDelay :: Number
  , animateOnMount :: Boolean
  , exitBeforeEnter :: Boolean  -- mode="wait"
  }
```

**Presets:**
- `defaultPresenceConfig` — 300ms enter/exit
- `instantConfig` — No animation

### PresenceState Molecule

```purescript
type PresenceState =
  { phase :: PresencePhase
  , mount :: MountStatus
  , direction :: AnimationDirection
  , config :: PresenceConfig
  , startedAt :: Maybe Number
  , progress :: Number
  }
```

**State Transitions:**
- `startEnter timestamp`, `completeEnter`
- `startExit timestamp`, `completeExit`
- `cancelAnimation`

**Computed:**
- `shouldRender` — Phase is present
- `shouldAnimate` — Phase is animating
- `animationRemainingTime currentTime`

### PresenceGroup Compound

For AnimatePresence patterns:

```purescript
type PresenceGroup =
  { items :: Array { key :: String, presence :: PresenceState }
  , pendingExits :: Array String
  , exitBeforeEnter :: Boolean
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                            // hover // effect
────────────────────────────────────────────────────────────────────────────────

## Hover Effect

Interactive hover behaviors for UI elements.

### HoverState Enum

| Constructor | Description |
|-------------|-------------|
| `HoverIdle` | Not interacting |
| `HoverEntering` | Enter animation |
| `HoverActive` | Fully hovered |
| `HoverLeaving` | Exit animation |

### HoverTransform Molecule

Transform on hover:
- Scale, translate, rotate
- Origin specification

**Presets:**
- `identityTransform`, `defaultHoverTransform`
- `liftTransform` — Y -2px lift
- `pressTransform` — Scale 0.98
- `scaleUpTransform` — Scale 1.05
- `elevatedHoverTransform` — Lift with shadow

### HoverStyle Molecule

Style changes on hover:
- Brightness, opacity changes
- Shadow intensity, filter effects

**Presets:**
- `identityStyle`, `defaultHoverStyle`
- `subtleHoverStyle`, `prominentHoverStyle`
- `glowHoverStyle`, `dimHoverStyle`

### HoverAudio Molecule

Sound triggers on hover:
- Enter sound, leave sound, loop sound
- Volume control

### HoverAnimation Molecule

Animation triggers:
- Lottie animations
- CSS animations
- Spring physics

### HoverParticle Molecule

Particle effects:
- Burst on enter
- Continuous emission
- Trail following cursor

**ParticleType Enum:**
- `SparkleParticle`, `ConfettiParticle`, `StarParticle`
- `HeartParticle`, `SnowParticle`, `FireParticle`

### HoverEffect Compound

```purescript
newtype HoverEffect = HoverEffect
  { transform :: HoverTransform
  , style :: HoverStyle
  , audio :: HoverAudio
  , animation :: HoverAnimation
  , particle :: HoverParticle
  , transitionDurationMs :: Number
  , transitionDelay :: Number
  }
```

**Presets:**
- `noHoverEffect` — Completely inert
- `defaultHoverEffect` — 150ms, subtle lift + brightness
- `subtleHoverEffect` — Minimal feedback (100ms)
- `prominentHoverEffect` — More noticeable (200ms)
- `glowHoverEffect` — Emissive appearance (250ms)
- `sparkleHoverEffect` — With particle burst

────────────────────────────────────────────────────────────────────────────────
                                                                   // feedback
────────────────────────────────────────────────────────────────────────────────

## Feedback

Notification and messaging atoms.

### FeedbackType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ToastType` | `"toast"` | Brief, non-blocking |
| `SnackbarType` | `"snackbar"` | Brief with optional action |
| `BannerType` | `"banner"` | Persistent top/bottom |
| `AlertType` | `"alert"` | Inline alert box |
| `DialogType'` | `"dialog"` | Modal dialog |

### FeedbackSeverity Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FeedbackSuccess` | `"success"` | Operation succeeded |
| `FeedbackInfo` | `"info"` | Informational |
| `FeedbackWarning` | `"warning"` | Warning/caution |
| `FeedbackError` | `"error"` | Error occurred |
| `FeedbackNeutral` | `"neutral"` | No specific severity |

### FeedbackPosition Enum

| Constructor | String ID |
|-------------|-----------|
| `TopLeft`, `TopCenter`, `TopRight` | Position names |
| `BottomLeft`, `BottomCenter`, `BottomRight` | Position names |

### FeedbackDuration Enum

| Constructor | Duration | Description |
|-------------|----------|-------------|
| `DurationShort` | 2000ms | Brief messages |
| `DurationMedium` | 4000ms | Standard messages |
| `DurationLong` | 8000ms | Important messages |
| `DurationPersistent` | infinite | Manual dismiss |

### DismissalMethod Enum

| Constructor | Description |
|-------------|-------------|
| `AutoDismiss` | After duration |
| `ManualDismiss` | Requires close action |
| `ActionDismiss` | When action taken |
| `SwipeDismiss` | Swiped away (mobile) |

### FeedbackAction Molecule

```purescript
type FeedbackAction =
  { label :: String
  , actionId :: String
  , dismissOnAction :: Boolean
  }
```

**Presets:**
- `undoAction`, `retryAction`, `dismissAction`

### Toast, Snackbar, Banner, Alert, Dialog

Full molecules for each feedback type with appropriate configuration.

### NotificationQueue Compound

For managing multiple notifications:
- `enqueue`, `dequeue`
- `currentNotification`

### Tooltip, Popover Molecules

For contextual information display.

### Drawer, Sheet Compounds

For overlay panels with snap points.

────────────────────────────────────────────────────────────────────────────────
                                                                   // viewport
────────────────────────────────────────────────────────────────────────────────

## Viewport

First-class container for displaying content.

### Breakpoint Enum (Tailwind-aligned)

| Constructor | Min | Max | Description |
|-------------|-----|-----|-------------|
| `Xs` | 0 | 639 | Mobile portrait |
| `Sm` | 640 | 767 | Mobile landscape |
| `Md` | 768 | 1023 | Tablet portrait |
| `Lg` | 1024 | 1279 | Tablet landscape |
| `Xl` | 1280 | 1535 | Desktop |
| `Xxl` | 1536 | infinite | Large desktop |

### Orientation Enum

| Constructor | Condition | Description |
|-------------|-----------|-------------|
| `Portrait` | height > width | Taller than wide |
| `Landscape` | width > height | Wider than tall |
| `Square` | width = height | Equal dimensions |

### DeviceClass Enum

| Constructor | Breakpoints | Description |
|-------------|-------------|-------------|
| `Phone` | Xs, Sm | Handheld, touch-primary |
| `Tablet` | Md, Lg | Portable, touch or stylus |
| `Desktop` | Xl | Stationary, mouse/keyboard |
| `LargeDesktop` | Xxl | Multi-monitor, ultrawide |

### ViewportControl Enum

| Constructor | Description |
|-------------|-------------|
| `Zoom`, `Pan`, `Scroll` | Navigation controls |
| `Fullscreen`, `Refresh`, `Close` | Window controls |

### ZoomLevel Atom

| Name | Type | Min | Max | Notes |
|------|------|-----|-----|-------|
| ZoomLevel | Number | 0.1 | 10.0 | 1.0 = 100% |

**Presets:**
- `zoomFit`, `zoom100`, `zoom50`, `zoom200`

### ResponsiveValue System

Values that change at breakpoints:

```purescript
type ResponsiveSpec a =
  { base :: a
  , sm :: Maybe a
  , md :: Maybe a
  , lg :: Maybe a
  , xl :: Maybe a
  , xxl :: Maybe a
  }
```

**Operations:**
- `resolveAtWidth responsive width`

────────────────────────────────────────────────────────────────────────────────
                                                        // container // query
────────────────────────────────────────────────────────────────────────────────

## Container Query

Respond to parent container size, not viewport.

### ContainerType Enum

| Constructor | CSS Value | Description |
|-------------|-----------|-------------|
| `InlineSize` | `inline-size` | Width-based queries |
| `BlockSize` | `block-size` | Height-based queries |
| `Size` | `size` | Both width and height |
| `Normal` | `normal` | Not a query container |

### QueryCondition Type

| Constructor | CSS Equivalent |
|-------------|----------------|
| `MinWidth Int` | `(min-width: Xpx)` |
| `MaxWidth Int` | `(max-width: Xpx)` |
| `MinHeight Int` | `(min-height: Xpx)` |
| `MaxHeight Int` | `(max-height: Xpx)` |
| `WidthRange Int Int` | `(min-width: X) and (max-width: Y)` |
| `OrientationQuery Orientation` | `(orientation: X)` |
| `AspectRatio Number` | `(aspect-ratio: X)` |

### ContainerResponsive System

Values that change at container breakpoints (same thresholds as viewport).

**Why Container Queries Matter:**

A card in a 3-column grid needs to render differently than the same card
in a sidebar, even if the viewport is identical. Components respond to
their context, not the window.

────────────────────────────────────────────────────────────────────────────────
                                                        // data // validity
────────────────────────────────────────────────────────────────────────────────

## Data Validity (Safety-Critical)

Graduated failure modes for DO-178C and FDA compliance.

### DataValidity Enum

| Constructor | Description |
|-------------|-------------|
| `Valid { confidence, source, timestamp }` | Trustworthy data |
| `Degraded { reason, usable, confidence, ... }` | Reduced quality |
| `Stale { age, lastValid, source }` | Data may be outdated |
| `SensorFailure { sensor, failureMode, ... }` | Sensor failed |
| `CommsLost { since, lastPacket, source }` | Communication lost |
| `CrossCheckFailed { sources, disagreement, ... }` | Sensors disagree |
| `OutOfRange { value, minBound, maxBound, ... }` | Value out of bounds |
| `RateOfChangeExceeded { current, previous, ... }` | Changed too fast |
| `NeverReceived` | No data ever received |

### FailureMode Enum

| Constructor | Description |
|-------------|-------------|
| `HardwareFault` | Physical sensor failure |
| `CalibrationError` | Needs recalibration |
| `RangeExceeded` | Outside sensor capability |
| `SelfTestFailed` | Built-in test failed |
| `PowerFailure` | Sensor lost power |
| `ConnectionLost` | Physical connection broken |

### DegradationReason Enum

| Constructor | Description |
|-------------|-------------|
| `ReducedAccuracy` | Degraded mode |
| `InterferenceDet` | Electromagnetic interference |
| `EnvironmentalLimit` | Temperature/pressure outside range |
| `BackupSensor` | Using backup instead of primary |
| `FilteredData` | Data has been filtered |
| `Interpolated` | Value interpolated |

### DisplayResponse Enum (DO-178C)

| Constructor | Visual Treatment |
|-------------|------------------|
| `DisplayNormal` | Normal display |
| `DisplayWithAge` | Show data age |
| `DisplayCrossHatch` | Yellow cross-hatch overlay |
| `DisplayXThrough` | X through display element |
| `DisplayRemove` | Remove from display entirely |
| `DisplayFlash` | Flashing indication |

### DataAge Enum (DO-178C thresholds)

| Constructor | Age | Action |
|-------------|-----|--------|
| `Fresh` | < 250ms | Normal display |
| `Aging` | 250ms - 2s | Cross-hatch overlay |
| `StaleAge` | 2s - 10s | X through display |
| `Invalid` | > 10s | Remove from display |

### SignalQuality Enum (Medical)

| Constructor | Description |
|-------------|-------------|
| `QualityGood` | Signal is strong |
| `QualityMarginal` | Signal is acceptable |
| `QualityPoor` | Signal is weak |
| `QualityInvalid` | Signal is unusable |
| `QualityLeadOff` | Electrode disconnected |

────────────────────────────────────────────────────────────────────────────────
                                                       // button // semantics
────────────────────────────────────────────────────────────────────────────────

## Button Semantics

Semantic purpose taxonomy for button elements.

### ButtonPurpose Enum

| Constructor | Description | ARIA Role |
|-------------|-------------|-----------|
| `ActionButton` | General action ("Save", "Apply") | button |
| `FormSubmit` | Form submission | button |
| `FormReset` | Form reset | button |
| `NavigationButton` | Navigation trigger | link |
| `MediaControl` | Media playback control | button |
| `ToggleControl` | Stateful toggle | switch |
| `MenuTrigger` | Opens dropdown/menu | button + haspopup |
| `DialogTrigger` | Opens modal/dialog | button + haspopup |
| `DisclosureTrigger` | Expands/collapses content | button + expanded |
| `DangerAction` | Destructive action | button |
| `IconAction` | Icon-only action | button (requires label) |
| `FloatingAction` | FAB | button (requires label) |

### ToggleState Enum (aria-pressed)

| Constructor | ARIA Value |
|-------------|------------|
| `Pressed` | `"true"` |
| `Unpressed` | `"false"` |
| `Mixed` | `"mixed"` |

### PopupType Enum (aria-haspopup)

| Constructor | ARIA Value |
|-------------|------------|
| `MenuPopup` | `"menu"` |
| `ListboxPopup` | `"listbox"` |
| `TreePopup` | `"tree"` |
| `GridPopup` | `"grid"` |
| `DialogPopup` | `"dialog"` |

### MediaAction Enum

| Constructor | Label |
|-------------|-------|
| `PlayAction` | "Play" |
| `PauseAction` | "Pause" |
| `StopAction` | "Stop" |
| `SkipForwardAction` | "Skip forward" |
| `SkipBackwardAction` | "Skip backward" |
| `NextTrackAction` | "Next track" |
| `MuteAction` / `UnmuteAction` | "Mute" / "Unmute" |
| `FullscreenAction` / `ExitFullscreenAction` | Fullscreen toggle |
| `PictureInPictureAction` | "Picture in picture" |
| `ClosedCaptionsAction` | "Closed captions" |

### ButtonIdentity (UUID5)

Deterministic button identity — same semantic config produces same UUID5:

```purescript
type ButtonIdentity =
  { purpose :: ButtonPurpose
  , label :: String
  , toggleState :: Maybe ToggleState
  , popupType :: Maybe PopupType
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                        // skeleton // config
────────────────────────────────────────────────────────────────────────────────

## Skeleton Config

Configuration atoms for skeleton loading states.

### Research-Based Timing

| Parameter | Default | Description |
|-----------|---------|-------------|
| `delayBeforeShow` | 200ms | Skip skeleton if content loads faster |
| `minDisplayTime` | 300ms | Minimum display once shown (prevents flash) |
| `maxDisplayTime` | 3000ms | Consider "slow" after this |

### SkeletonTiming Presets

| Preset | Delay | Min | Max |
|--------|-------|-----|-----|
| `defaultTiming` | 200ms | 300ms | 3000ms |
| `aggressiveTiming` | 100ms | 200ms | 2000ms |
| `patientTiming` | 400ms | 500ms | 5000ms |

### SkeletonShape Enum

| Constructor | Description |
|-------------|-------------|
| `ShapeRectangle w h r` | Rectangle with border radius |
| `ShapeCircle d` | Circle with diameter |
| `ShapeTextLine w h` | Single text line |
| `ShapeParagraph lines lh gap` | Multiple lines |
| `ShapeAvatar d` | Circle for user avatar |
| `ShapeCard w h` | Card with header |
| `ShapeCustomPath path` | Custom SVG path |

### ContentType Validation

**Skeleton-appropriate content:**
- `ContentText`, `ContentMedia`, `ContentData`, `ContentCard`

**Never use skeletons on:**
- `ContentButton`, `ContentInput`, `ContentNavigation`, `ContentAction`

### SlowConnectionBehavior Enum

| Constructor | Description |
|-------------|-------------|
| `ShowWarningText msg` | "Taking longer than expected..." |
| `ShowProgressBar` | Switch to indeterminate progress |
| `ShowRetryButton` | Offer retry option |
| `KeepAnimating` | Continue skeleton animation |
| `FadeToStatic` | Stop animation, show static |

### ShimmerDirection Enum

| Constructor | Description |
|-------------|-------------|
| `ShimmerLTR` | Left to right (LTR languages) |
| `ShimmerRTL` | Right to left (RTL languages) |
| `ShimmerTTB` | Top to bottom |
| `ShimmerBTT` | Bottom to top |

────────────────────────────────────────────────────────────────────────────────
                                                             // source // files
────────────────────────────────────────────────────────────────────────────────

## Source Structure

```
src/Hydrogen/Schema/Reactive/
├── ButtonSemantics.purs      # Button semantic purpose taxonomy
├── ContainerQuery.purs       # Container query atoms
├── DataState.purs            # Async data lifecycle
├── DataValidity.purs         # Safety-critical validity (leader)
│   ├── Arithmetic.purs       # Validity calculations
│   ├── DataAge.purs          # DO-178C data age
│   ├── Display.purs          # Display response types
│   ├── Operations.purs       # Validity operations
│   ├── SensorSource.purs     # Sensor source tracking
│   ├── SignalQuality.purs    # Medical signal quality
│   └── Types.purs            # Core types
├── DragState.purs            # Drag and drop states
├── Feedback.purs             # User feedback (leader)
│   ├── Alert.purs            # Inline alerts
│   ├── Banner.purs           # Persistent banners
│   ├── Dialog.purs           # Modal dialogs
│   ├── Overlay.purs          # Drawers and sheets
│   ├── Popover.purs          # Popovers
│   ├── Queue.purs            # Notification queue
│   ├── Snackbar.purs         # Snackbars with actions
│   ├── Toast.purs            # Brief notifications
│   ├── Tooltip.purs          # Tooltips
│   └── Types.purs            # Core feedback types
├── Flags.purs                # Boolean state flags
├── FocusManagement.purs      # Focus ring, trap, roving
├── HoverEffect.purs          # Hover effects (leader)
│   ├── Animation.purs        # Animation triggers
│   ├── Audio.purs            # Audio triggers
│   ├── Combined.purs         # Combined effect
│   ├── Particle.purs         # Particle effects
│   ├── State.purs            # Hover state machine
│   ├── Style.purs            # Style changes
│   └── Transform.purs        # Transform effects
├── InteractiveState.purs     # Pointer, focus, activation
├── MediaState.purs           # Media playback state
├── NetworkState.purs         # Online/offline states
├── PresenceState.purs        # Mount/animation lifecycle
├── Progress.purs             # Progress atoms
├── ScrollState.purs          # Scroll position state
├── SelectionState.purs       # Selection atoms
├── SkeletonConfig.purs       # Loading skeleton config
├── ValidationState.purs      # Form validation lifecycle
└── Viewport.purs             # Viewport queries (leader)
    ├── Breakpoints.purs      # Breakpoint values
    ├── Core.purs             # Viewport type
    ├── CSS.purs              # CSS generation
    ├── Responsive.purs       # Responsive values
    └── Types.purs            # Core types
```

**47 files, ~11,000 lines total.**

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

The Reactive pillar models **UI state machines** that map directly to:

### CSS Pseudo-Classes
- `:hover` maps to `PointerHover`
- `:focus` maps to `FocusState != FocusNone`
- `:focus-visible` maps to `FocusKeyboard`
- `:active` maps to `PointerPressed`
- `:disabled` maps to `disabled == true`

### ARIA States
- `aria-disabled` maps to `disabled`
- `aria-busy` maps to `loading`
- `aria-invalid` maps to `ValidationInvalid`
- `aria-pressed` maps to `ToggleState`
- `aria-expanded` maps to `ExpandedFlag`
- `aria-haspopup` maps to `PopupType`

### Form Library APIs
Reactive types map to React Hook Form, Formik, Valibot patterns:
- `pristine/dirty` maps to `ModificationState`
- `touched/untouched` maps to `TouchState`
- `isSubmitting` maps to `FormValidation.isSubmitting`
- `isValid` maps to `FormValidation.isValid`

## State vs. Event Philosophy

**State:** An element IS in `PointerHover` state.
**Event:** An element received a `mouseenter` event.

Reactive models states, not events. This matches declarative UI —
the view is a function of state, not a sequence of mutations.

## Validation UX Pattern

`shouldShowError` encodes best practice: only show errors after the user
has interacted (touched) with the field. This prevents intimidating users
with errors before they've had a chance to fill in the form.

## Accessibility First

Focus management types encode WCAG requirements:
- `:focus-visible` via `FocusOrigin`
- Two-ring pattern for contrast on any background
- Focus trap modes for modal dialogs
- Roving tabindex for composite widgets

## Safety-Critical Systems

DataValidity provides the complete vocabulary for DO-178C (avionics) and
FDA 21 CFR Part 11 (medical) compliance:
- Graduated failure modes (not just boolean stale)
- Sensor source tracking
- Cross-check validation
- Display response computation

## Why This Matters at Billion-Agent Scale

When an agent composes a form, it needs to know:
- What validation states exist and when to transition
- How focus should behave for keyboard navigation
- What ARIA attributes to generate

When an agent displays sensor data, it needs to know:
- How old data can be before showing warning
- When to remove data from display entirely
- How to indicate degraded confidence

The Reactive pillar gives agents a **complete vocabulary for interaction** —
not "make the button highlight on hover" but `pointerState: PointerHover`.
Not "show a spinner" but `loadingState: loadingIndeterminate`.
Not "data is old" but `validity: Stale { age: 5000, lastValid: ... }`.

**Deterministic. Bounded. Complete.**

────────────────────────────────────────────────────────────────────────────────
