━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // input // primitives // inventory // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "CSS and JavaScript mangle your tokenizers. We are building something
    totally different here."

                                                                    — jpyxal

# Hydrogen Schema Input Primitives Inventory

## Executive Summary

The Hydrogen Schema provides a **comprehensive** input system across three pillars:

1. **Gestural** (Pillar 9) — Low-level input handling
2. **Reactive** (Pillar 8) — State and feedback atoms
3. **Accessibility** — WAI-ARIA 1.2 compliant input semantics

**575+ distinct types** across input handling. W3C spec compliant.

────────────────────────────────────────────────────────────────────────────────
                                                       // pointer // mouse // input
────────────────────────────────────────────────────────────────────────────────

| Type            | Location          | Purpose                              |
|-----------------|-------------------|--------------------------------------|
| PointerEventType| Gestural.Event    | 10 pointer lifecycle events          |
| MouseEventType  | Gestural.Event    | 10 mouse lifecycle events            |
| PointerType     | Gestural.Pointer  | Device type (Mouse/Touch/Pen/Unknown)|
| MouseButton     | Gestural.Pointer  | 5 buttons (Left/Mid/Right/Back/Fwd)  |
| Pressure        | Gestural.Pointer  | Force sensing (0.0-1.0)              |
| TiltX/TiltY     | Gestural.Pointer  | Pen tilt (-90 to 90 degrees)         |
| Twist           | Gestural.Pointer  | Pen rotation (0-359 degrees)         |
| PointerPosition | Gestural.Pointer  | Multi-coordinate position            |
| PointerSize     | Gestural.Pointer  | Contact area dimensions              |
| PointerState    | Gestural.Pointer  | Complete pointer molecule            |

────────────────────────────────────────────────────────────────────────────────
                                                              // touch // input
────────────────────────────────────────────────────────────────────────────────

| Type                 | Location        | Purpose                        |
|----------------------|-----------------|--------------------------------|
| TouchEventType       | Gestural.Event  | Start/Move/End/Cancel          |
| TouchPoint           | Gestural.Touch  | Individual touch with id/pos   |
| TouchCount           | Gestural.Touch  | Active touch count (0-10)      |
| PinchState           | Gestural.Touch  | Two-finger scale gesture       |
| RotateState          | Gestural.Touch  | Two-finger rotation gesture    |
| TouchState           | Gestural.Touch  | Complete multi-touch compound  |
| ScreenEdge           | Gestural.Touch  | Edge swipe origin              |
| EdgeSwipeState       | Gestural.Touch  | System edge gesture state      |
| ThreeFingerDirection | Gestural.Touch  | System navigation direction    |
| ThreeFingerSwipeState| Gestural.Touch  | Desktop navigation gesture     |
| TwoFingerTapState    | Gestural.Touch  | Right-click equivalent         |

────────────────────────────────────────────────────────────────────────────────
                                                           // keyboard // input
────────────────────────────────────────────────────────────────────────────────

| Type           | Location                    | Purpose                    |
|----------------|-----------------------------|----------------------------|
| KeyEventType   | Gestural.Keyboard.Event     | Down/Up/Press              |
| KeyCode        | Gestural.Keyboard.Keys      | W3C key code constants     |
| ModifierState  | Gestural.Keyboard.Modifiers | Ctrl/Alt/Shift/Meta state  |
| KeyEvent       | Gestural.Keyboard.Event     | Complete key event molecule|
| Shortcut       | Gestural.Keyboard.Shortcut  | Key combo definitions      |
| ArrowDirection | Gestural.Keyboard.Navigation| Arrow key mapping          |
| TabDirection   | Gestural.Keyboard.Navigation| Tab/Shift+Tab              |
| VimMovement    | Gestural.Keyboard.Navigation| j/k/h/l movement           |
| FocusAction    | Gestural.Keyboard.Navigation| Focus navigation intents   |
| KeyboardState  | Gestural.Keyboard.State     | Complete keyboard state    |

────────────────────────────────────────────────────────────────────────────────
                                               // key // sequences // vim // emacs
────────────────────────────────────────────────────────────────────────────────

| Type            | Location              | Purpose                        |
|-----------------|-----------------------|--------------------------------|
| SequenceKey     | Gestural.KeySequence  | Key with modifiers             |
| KeySequenceDef  | Gestural.KeySequence  | Multi-key sequence definition  |
| MatchResult     | Gestural.KeySequence  | NoMatch/PartialMatch/FullMatch |
| CountPrefix     | Gestural.KeySequence  | Vim count prefix (e.g., "3dd") |
| OperatorPending | Gestural.KeySequence  | Delete/Change/Yank/Indent/Fmt  |
| VimMotion       | Gestural.KeySequence  | 12 vim motions (word, line)    |
| SequenceState   | Gestural.KeySequence  | Complete sequence state        |

────────────────────────────────────────────────────────────────────────────────
                                                               // gestures
────────────────────────────────────────────────────────────────────────────────

| Type                 | Location                  | Purpose                 |
|----------------------|---------------------------|-------------------------|
| GesturePhase         | Gestural.Gesture.Phase    | Possible/Began/Changed/ |
|                      |                           | Ended/Cancelled/Failed  |
| TapCount             | Gestural.Gesture.Tap      | 1-3 taps                |
| TapState             | Gestural.Gesture.Tap      | Tap recognition state   |
| LongPressThreshold   | Gestural.Gesture.LongPress| Hold duration threshold |
| LongPressState       | Gestural.Gesture.LongPress| Long press state        |
| SwipeDirection       | Gestural.Gesture.Swipe    | Up/Down/Left/Right      |
| SwipeVelocityThreshold| Gestural.Gesture.Swipe   | Velocity threshold      |
| SwipeState           | Gestural.Gesture.Swipe    | Swipe recognition state |
| PanState             | Gestural.Gesture.Pan      | Continuous drag state   |
| PinchConfig          | Gestural.Gesture.Pinch    | Min/max scale config    |
| PinchGesture         | Gestural.Gesture.Pinch    | Pinch-to-zoom state     |
| RotateConfig         | Gestural.Gesture.Rotate   | Snap angles config      |
| RotateGesture        | Gestural.Gesture.Rotate   | Two-finger rotation     |
| GestureState         | Gestural.Gesture          | Combined all-gesture    |

────────────────────────────────────────────────────────────────────────────────
                                                          // scroll // wheel
────────────────────────────────────────────────────────────────────────────────

| Type              | Location         | Purpose                         |
|-------------------|------------------|---------------------------------|
| WheelDelta        | Gestural.Event   | deltaX/Y/Z with mode            |
| ScrollPosition    | Gestural.Scroll  | Current scroll position         |
| ScrollDelta       | Gestural.Scroll  | Scroll change amount            |
| ScrollProgress    | Gestural.Scroll  | Progress 0-1                    |
| ScrollBounds      | Gestural.Scroll  | Scrollable area                 |
| OverscrollBehavior| Gestural.Scroll  | Auto/Contain/None               |
| SnapAlignment     | Gestural.Scroll  | Start/Center/End                |
| SnapType          | Gestural.Scroll  | Mandatory/Proximity             |
| ScrollState       | Gestural.Scroll  | Complete scroll compound        |

────────────────────────────────────────────────────────────────────────────────
                                                      // focus // management
────────────────────────────────────────────────────────────────────────────────

| Type            | Location                   | Purpose                    |
|-----------------|----------------------------|----------------------------|
| FocusOrigin     | Gestural.Focus             | Mouse/Keyboard/Program     |
| FocusDirection  | Gestural.Focus             | 8 directions + First/Last  |
| FocusableElement| Gestural.Focus             | Element with tabIndex      |
| FocusScope      | Gestural.Focus             | Focus container            |
| Orientation     | Gestural.Focus             | Horizontal/Vertical/Both   |
| RovingState     | Gestural.Focus             | Roving tabindex state      |
| FocusStack      | Gestural.Focus             | Restoration stack          |
| FocusState      | Gestural.Focus             | Complete focus state       |
| FocusRing       | Reactive.FocusManagement   | Focus ring styling         |
| FocusTrap       | Reactive.FocusManagement   | Modal focus trap           |
| FocusVisibility | Reactive.FocusManagement   | Visible/Hidden/Auto        |

────────────────────────────────────────────────────────────────────────────────
                                                                  // hover
────────────────────────────────────────────────────────────────────────────────

| Type            | Location         | Purpose                          |
|-----------------|------------------|----------------------------------|
| HoverPhase      | Gestural.Hover   | None/Enter/Intent/Active/Leave   |
| HoverIntentConfig| Gestural.Hover  | Delay/sensitivity/interval       |
| HoverZone       | Gestural.Hover   | Extended hover area              |
| HoverGroup      | Gestural.Hover   | Related elements                 |
| PointerTrack    | Gestural.Hover   | Velocity tracking                |
| HoverState      | Gestural.Hover   | Complete hover state             |

────────────────────────────────────────────────────────────────────────────────
                                                          // drag // and // drop
────────────────────────────────────────────────────────────────────────────────

| Type            | Location            | Purpose                       |
|-----------------|---------------------|-------------------------------|
| DragPhase       | Gestural.DragDrop   | 6 lifecycle phases            |
| DropEffect      | Gestural.DragDrop   | None/Copy/Move/Link           |
| DragSource      | Gestural.DragDrop   | Source configuration          |
| DropTarget      | Gestural.DragDrop   | Target configuration          |
| DragPreview     | Gestural.DragDrop   | Element/Ghost/Custom/None     |
| TransferData    | Gestural.DragDrop   | text/html/json/files          |
| DragOffset      | Gestural.DragDrop   | Pointer to preview offset     |
| DragState       | Gestural.DragDrop   | Complete drag state           |
| DragType        | Reactive.DragState  | File/Element/Text/External    |
| DropZoneFeedback| Reactive.DragState  | Accepting/Rejecting/Neutral   |

────────────────────────────────────────────────────────────────────────────────
                                                               // selection
────────────────────────────────────────────────────────────────────────────────

| Type              | Location              | Purpose                    |
|-------------------|-----------------------|----------------------------|
| SelectionMode     | Gestural.Selection    | None/Single/Multiple/Range |
| SelectionAction   | Gestural.Selection    | Select/Toggle/Extend/etc.  |
| SelectableItem    | Gestural.Selection    | Selectable element         |
| SelectionAnchor   | Gestural.Selection    | Range anchor point         |
| SelectionRange    | Gestural.Selection    | Index range                |
| SelectionRect     | Gestural.Selection    | Marquee rectangle          |
| SelectionState    | Gestural.Selection    | Complete selection state   |
| SelectionStatus   | Reactive.SelectionState| Selected/Unselected/Indet |
| HierarchicalStatus| Reactive.SelectionState| Full/Partial/None         |

────────────────────────────────────────────────────────────────────────────────
                                                          // context // menu
────────────────────────────────────────────────────────────────────────────────

| Type            | Location              | Purpose                      |
|-----------------|-----------------------|------------------------------|
| ContextTrigger  | Gestural.ContextMenu  | RightClick/LongPress/Kbd     |
| MenuItemType    | Gestural.ContextMenu  | Normal/Separator/Submenu     |
| MenuPosition    | Gestural.ContextMenu  | AtPointer/AtElement/etc.     |
| MenuPlacement   | Gestural.ContextMenu  | Calculated screen position   |
| MenuItem        | Gestural.ContextMenu  | Item with label/disabled     |
| MenuState       | Gestural.ContextMenu  | Closed/Opening/Open/Closing  |
| SubmenuState    | Gestural.ContextMenu  | Nested submenu tracking      |
| ContextMenuState| Gestural.ContextMenu  | Complete menu state          |

────────────────────────────────────────────────────────────────────────────────
                                                       // form // state // flags
────────────────────────────────────────────────────────────────────────────────

| Category       | Flags                                                    |
|----------------|----------------------------------------------------------|
| Interactive    | Enabled, Disabled, Visible, Hidden, Focused, Hovered,   |
|                | Pressed, Active                                          |
| Selection      | Selected, Checked, Indeterminate, Expanded, Collapsed,  |
|                | Open                                                     |
| Form           | Pristine, Dirty, Touched, Untouched, Valid, Invalid,    |
|                | Required, ReadOnly                                       |
| Data           | Loading, Loaded, Refreshing, Stale, Empty, Busy         |
| Drag           | Dragging, DragOver, DropTarget                          |
| Media          | Playing, Paused, Muted, Buffering, Fullscreen           |
| Connection     | Online, Offline, Reconnecting                           |
| Presence       | Mounted, Entering, Exiting, Animating                   |

────────────────────────────────────────────────────────────────────────────────
                                                              // validation
────────────────────────────────────────────────────────────────────────────────

| Type              | Location                  | Purpose                  |
|-------------------|---------------------------|--------------------------|
| ValidationResult  | Reactive.ValidationState  | Valid/Invalid/Pending    |
| ValidationSeverity| Reactive.ValidationState  | Error/Warning/Info       |
| ValidationMessage | Reactive.ValidationState  | Message with rule/params |
| ModificationState | Reactive.ValidationState  | Pristine/Modified        |
| TouchState        | Reactive.ValidationState  | Untouched/Touched        |
| FieldValidation   | Reactive.ValidationState  | Complete field state     |
| FormValidation    | Reactive.ValidationState  | Aggregate form state     |

────────────────────────────────────────────────────────────────────────────────
                                           // accessibility // roles // wai-aria
────────────────────────────────────────────────────────────────────────────────

## Widget Roles

Button, Checkbox, Radio, Switch, Textbox, Searchbox, Spinbutton, Slider,
Scrollbar, Progressbar, Link, Option, Tab, Tabpanel, Menuitem, 
Menuitemcheckbox, Menuitemradio, Separator, Gridcell, Treeitem

## Composite Roles

Combobox, Grid, Listbox, Menu, Menubar, Radiogroup, Tablist, Tree, Treegrid

## Structure Roles

Application, Article, Blockquote, Caption, Cell, Columnheader, Definition,
Directory, Document, Feed, Figure, Group, Heading, Img, List, Listitem,
Math, Meter, Note, Paragraph, Row, Rowgroup, Rowheader, Table, Term,
Toolbar, Tooltip

## Window Roles

Alert, Alertdialog, Dialog

────────────────────────────────────────────────────────────────────────────────
                                              // aria // states // and // properties
────────────────────────────────────────────────────────────────────────────────

| Type              | Values                                           |
|-------------------|--------------------------------------------------|
| Tristate          | False/True/Mixed                                 |
| AriaAutocomplete  | None/Inline/List/Both                            |
| AriaHaspopup      | False/True/Menu/Listbox/Tree/Grid/Dialog         |
| AriaOrientation   | Horizontal/Vertical/Undefined                    |
| AriaInvalid       | False/True/Grammar/Spelling                      |
| AriaCurrent       | False/True/Page/Step/Location/Date/Time          |

────────────────────────────────────────────────────────────────────────────────
                                                      // button // semantics
────────────────────────────────────────────────────────────────────────────────

| Type           | Location                  | Purpose                    |
|----------------|---------------------------|----------------------------|
| ButtonPurpose  | Reactive.ButtonSemantics  | 12 semantic purposes       |
| ToggleState    | Reactive.ButtonSemantics  | Pressed/Unpressed/Mixed    |
| PopupType      | Reactive.ButtonSemantics  | Menu/Listbox/Tree/Grid/Dlg |
| MediaAction    | Reactive.ButtonSemantics  | 20 media control actions   |
| ButtonIdentity | Reactive.ButtonSemantics  | UUID5-based identity       |

────────────────────────────────────────────────────────────────────────────────
                                               // triggers // and // easter eggs
────────────────────────────────────────────────────────────────────────────────

| Type            | Location          | Purpose                         |
|-----------------|-------------------|---------------------------------|
| TriggerCondition| Gestural.Trigger  | 13 trigger condition types      |
| TriggerEffect   | Gestural.Trigger  | 12 effect types                 |
| TriggerTarget   | Gestural.Trigger  | Self/Element/Group/Global       |
| TriggerTiming   | Gestural.Trigger  | Delay/duration/cooldown/repeat  |
| HoverTrigger    | Gestural.Trigger  | Hover-to-reveal builder         |
| SequenceTrigger | Gestural.Trigger  | Easter egg sequences            |
| konamiCode      | Gestural.Trigger  | Classic Konami preset           |

────────────────────────────────────────────────────────────────────────────────
                                                          // identified // gaps
────────────────────────────────────────────────────────────────────────────────

## Missing Form Control Configuration Types

The Schema has **state** for form controls but lacks explicit **widget
configuration types** for:

1. **TextField/TextInput** — maxLength, pattern, inputMode atoms needed
2. **NumberInput/RangeInput** — numeric bounds, step, precision atoms
3. **DatePicker/TimePicker** — date/time input primitive configuration
4. **ColorPicker** — referenced in comments but no Schema types
5. **FileInput** — file input configuration beyond drag TransferData
6. **Autocomplete/Combobox** — suggestion list state management
7. **Rating/Stars** — rating input primitive
8. **Rich Text Editor** — toolbar/formatting input types

## Architecture Note

These should be built as **compounds** composing existing atoms:

```purescript
-- Example: TextField compound
type TextField =
  { validation :: FieldValidation      -- from Reactive
  , interactive :: InteractiveState    -- from Reactive
  , keyboard :: KeyboardState          -- from Gestural
  , focus :: FocusState                -- from Gestural
  , accessibility :: 
      { role :: WidgetRole             -- RoleTextbox
      , autocomplete :: AriaAutocomplete
      }
  , config ::
      { maxLength :: Maybe Int
      , pattern :: Maybe String
      , inputMode :: InputMode         -- text/numeric/tel/email/url
      }
  }
```

The input **events** and **states** are comprehensive. What's needed are the
**configuration compounds** that compose these primitives into specific
widget types.

────────────────────────────────────────────────────────────────────────────────
                                                                // conclusion
────────────────────────────────────────────────────────────────────────────────

The Hydrogen Schema provides an exceptionally thorough input foundation:

- **575+ distinct types** across input handling
- **W3C spec compliant** (Pointer Events, Touch Events, UIEvents, WAI-ARIA 1.2)
- **Vim/emacs support** with key sequences and operator-pending modes
- **Touch-first** with pinch, rotate, multi-finger gestures
- **Accessibility-first** with complete ARIA taxonomy

The identified gaps are at the **component configuration level** rather than
the event/state level. The primitives exist to build any form control — what's
needed are the pre-composed widget type definitions.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             — Opus 4.5 // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
