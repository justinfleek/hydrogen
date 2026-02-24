# Hydrogen Session Notes

**Last Updated:** 2026-02-24
**Build Status:** Zero warnings, zero errors

---

## Current Goal

Port remaining Halogen-based components (`Hydrogen.Component.*`) to Schema-native Element-based components (`Hydrogen.Element.Component.*`). All components must use Schema atoms exclusively — no hardcoded CSS strings, no Tailwind classes, no JavaScript FFI except at true system boundaries.

---

## Key Constraints

- **Pure Schema, no Tailwind**: Components use Schema atoms for all visual properties
- **extraAttributes for edge cases**: Escape hatch exists but should be used sparingly (testing, a11y)
- **No JS FFI in components**: FFI only at true system boundaries (Target.DOM runtime)
- **Pure PureScript locale data**: Use lookup tables for locale strings, not JavaScript's Intl API
- **500 line max per file**: Files must be split when exceeding this limit
- **Explicit imports only**: Never use `(..)` imports — they are canaries for incomplete work
- **Fix all warnings**: Zero warnings required — NEVER DELETE CODE TO FIX WARNINGS
- **UUID5 for identifiers**: Deterministic ID generation for contacts, events, etc.

---

## Build Command

```bash
nix develop --command spago build
```

---

## Component Porting Status

### Ported to Element (49 components)

| Component | Status | Notes |
|-----------|--------|-------|
| Accordion | Complete | Element-only (new) |
| Alert | Complete | |
| AlertDialog | Complete | |
| AutoComplete | Complete | |
| Avatar | Complete | |
| Badge | Complete | |
| Breadcrumb | Complete | |
| Button | Complete | |
| Calendar | Complete | |
| Card | Complete | + submodules (Shape, Media, Hover, Badge) |
| Carousel | Complete | + submodules (Gestures, Transitions, Effects) |
| ChatBubble | Complete | |
| Checkbox | Complete | |
| CodeBlock | Complete | |
| Collapsible | Complete | |
| ColorPicker | Complete | |
| DataGrid | Complete | + submodules (Types, Cell, Column, Processing) |
| DatePicker | Complete | + submodules (Types, Format, Render) |
| DateRangePicker | Complete | + submodules (Types, Presets, Render) |
| GradientEditor | Complete | |
| Input | Complete | |
| Kanban | Complete | + submodules (Types, State, Render, Card, Column) |
| LoadingBar | Complete | |
| NumberInput | Complete | |
| OTPInput | Complete | + submodules (Types, Props, Render, Digit, Animation, Validation, Accessibility) |
| Pagination | Complete | |
| PasswordInput | Complete | |
| Progress | Complete | |
| Radio | Complete | |
| Rating | Complete | |
| SearchInput | Complete | |
| Select | Complete | |
| Separator | Complete | |
| Sheet | Complete | |
| Skeleton | Complete | |
| Slider | Complete | |
| StatCard | Complete | |
| Stepper | Complete | |
| Swatch | Complete | Element-only (new) |
| Switch | Complete | |
| Table | Complete | |
| Tabs | Complete | Element-only (new) |
| TagInput | Complete | |
| Textarea | Complete | |
| Timeline | Complete | |
| TimePicker | Complete | + submodules (Types, Format, Render) |
| Toast | Complete | |
| Toggle | Complete | |
| TreeView | Complete | + submodules (Types, State, Node, Render, Selection, Navigation, Layout, DragDrop, Animation, InlineEdit, Content, Accessibility, Connection, Viewport) |

### Not Yet Ported (7 components)

| Component | Halogen Lines | Notes |
|-----------|---------------|-------|
| Confetti | 398 | Particle system |
| CreditCard | 802 | Card detection/formatting |
| MeshGradientRenderer | 155 | Complex gradient |
| PhoneInput | 547 | International format |
| QRCode | 638 | Image generation |
| Signature | 701 | Canvas drawing |
| Tour | 666 | Onboarding overlay |

### Motion Subsystem — Not Yet Ported (19 Halogen components)

**Curve/** (6 components)
- BezierCurve, CurveEditor, CurveHandle, CurveKeyframe, EasingPicker, EasingPreview

**Property/** (7 components)
- AngleDial, KeyframeToggle, PositionXY, PositionXYZ, PropertyGroup, PropertyRow, ScrubableNumber

**Timeline/** (6 components)
- AnimationTimeline, KeyframeMarker, LayerTrack, Playhead, PropertyTrack, TimeRuler

---

## Schema Pillar Completeness

### Complete (~80%+)

| Pillar | Files | Notes |
|--------|-------|-------|
| Color | 37 | Missing: Value, camera log curves, LUT modules |
| Dimension | 14+ | Missing: SI prefixes, explicit pixel types |
| Typography | 17 | Missing: TabSize, TextDecoration, OpenType features |
| Reactive | 13 | Mostly complete |
| Gestural | 16+ | Missing: Pinch, Rotate multi-touch |

### Partial (15-50%)

| Pillar | Files | Major Gaps |
|--------|-------|------------|
| Temporal | 6 | Missing: Frames, FPS, Spring physics, Progress atoms |
| Elevation | 2 | Missing: Perspective, DoF, semantic elevation compounds |
| Geometry | 1 | Only Radius.purs exists — missing angles, shapes, paths, transforms, beziers |
| Audio | 2 | Only Frequency/Level — missing synthesis, envelopes, filters |

### Missing (0%)

| Pillar | Priority | Description |
|--------|----------|-------------|
| Material | High | Blur, filters, noise, borders, gradients, surfaces |
| Haptic | Medium | Vibration, impact feedback, audio cues |
| Spatial | Medium | 3D transforms, cameras, lights, PBR materials |
| Brand | High | Design tokens, themes, semantic colors, component tokens |

---

## (..) Import Canaries

**111 files with 188 (..) imports need fixing.**

### Highest Priority (5 occurrences)

- `src/Hydrogen/Query.purs`
- `src/Hydrogen/API/Client.purs`

### High Priority (3-4 occurrences)

- `src/Hydrogen/HTML/Renderer.purs` (4)
- `src/Hydrogen/Schema/Dimension/Camera.purs` (3)
- `src/Hydrogen/Realtime/WebSocket.purs` (3)
- `src/Hydrogen/Motion/LayoutAnimation.purs` (3)
- `src/Hydrogen/Error/Boundary.purs` (3)
- `src/Hydrogen/Component/DatePicker.purs` (3)
- `src/Hydrogen/Component/DataGrid.purs` (3)

### Common Patterns to Fix

```purescript
-- BAD (canary)
import Data.Maybe (..)

-- GOOD (explicit)
import Data.Maybe (Maybe(Nothing, Just), isJust, isNothing, fromMaybe)
```

---

## Scheduling System (Completed This Session)

New modules in `src/Hydrogen/Schema/Scheduling/`:

| Module | Lines | Description |
|--------|-------|-------------|
| RSVP.purs | ~100 | Pending, Accepted, Declined, Tentative, Delegated |
| Recurrence.purs | ~400 | RFC 5545 rules (daily, weekly, monthly, yearly) |
| Contact.purs | ~250 | Person, Room, Resource, Group with ContactId |
| Invite.purs | ~280 | AttendeeRole, RSVP tracking, ContactId reference |
| Event.purs | 405 | Core types, constructors, accessors |
| EventQuery.purs | 150 | Boolean predicates, computed properties |
| EventMod.purs | 203 | Modifiers, offset ops, iCal export |

New modules in `src/Hydrogen/Schema/Temporal/`:

| Module | Lines | Description |
|--------|-------|-------------|
| Millisecond.purs | ~90 | Bounded 0-999 |
| TimeOfDay.purs | 300 | Hour + Minute + Second + Millisecond molecule |
| Timezone.purs | ~310 | UtcOffset, TimezoneId, 13 common zones |

---

## Recommended Next Steps (Priority Order)

### 1. Port Remaining 7 Components

```
Confetti.purs → Element/Component/Confetti.purs
CreditCard.purs → Element/Component/CreditCard.purs
MeshGradientRenderer.purs → Element/Component/MeshGradientRenderer.purs
PhoneInput.purs → Element/Component/PhoneInput.purs
QRCode.purs → Element/Component/QRCode.purs
Signature.purs → Element/Component/Signature.purs
Tour.purs → Element/Component/Tour.purs
```

### 2. Create Missing Schema Pillars

**Material Pillar** (highest impact):
- BlurRadius, BlurSigma atoms
- Filter atoms (Brightness, Contrast, Saturation, etc.)
- BorderWidth, BorderStyle atoms
- GradientFill, SolidFill compounds
- BackdropBlur, Frosted effects

**Brand Pillar** (required for theming):
- ColorToken, SpacingToken, SizeToken molecules
- SemanticColors compound
- ThemeLight, ThemeDark compounds

**Geometry Pillar** (required for many components):
- Angle atoms (Degrees, Radians, Turns)
- Point2D, Point3D molecules
- Circle, Rectangle, Path compounds
- Transform molecules (Translate, Rotate, Scale)

### 3. Fix (..) Imports in Core Modules

Start with highest-impact:
- `Hydrogen/Query.purs`
- `Hydrogen/API/Client.purs`
- `Hydrogen/HTML/Renderer.purs`

### 4. Port Motion Subsystem

This is the largest remaining undertaking (19 Halogen components). Consider:
- Start with core timeline components
- Bezier/easing can reuse Schema/Motion/Easing
- Property/ components are good candidates for early porting

---

## File Locations

### Documentation
- `docs/SCHEMA.md` — Full 12 pillar enumeration
- `docs/design-ontology.md` — Implementation details
- `docs/COMPONENT_ARCHITECTURE.md` — Component porting spec
- `CLAUDE.md` — Project rules and attestation

### Halogen Components (to port FROM)
- `src/Hydrogen/Component/*.purs`
- `src/Hydrogen/Component/Motion/**/*.purs`

### Element Components (to port TO)
- `src/Hydrogen/Element/Component/*.purs`

### Schema Atoms
- `src/Hydrogen/Schema/Color/`
- `src/Hydrogen/Schema/Dimension/`
- `src/Hydrogen/Schema/Geometry/`
- `src/Hydrogen/Schema/Typography/`
- `src/Hydrogen/Schema/Elevation/`
- `src/Hydrogen/Schema/Temporal/`
- `src/Hydrogen/Schema/Reactive/`
- `src/Hydrogen/Schema/Gestural/`
- `src/Hydrogen/Schema/Audio/`
- `src/Hydrogen/Schema/Motion/`
- `src/Hydrogen/Schema/Scheduling/` (NEW)

### Missing Schema Directories (to create)
- `src/Hydrogen/Schema/Material/`
- `src/Hydrogen/Schema/Haptic/`
- `src/Hydrogen/Schema/Spatial/`
- `src/Hydrogen/Schema/Brand/`

---

## Session Summary (2026-02-23)

### Created (Scheduling Schema)

- `Millisecond.purs` — Bounded millisecond atom
- `TimeOfDay.purs` — Time molecule
- `Timezone.purs` — UTC offset and IANA zones
- `RSVP.purs` — Attendee response status
- `Recurrence.purs` — RFC 5545 recurrence rules
- `Contact.purs` — Person/Room/Resource/Group
- `Invite.purs` — Event invitation with roles
- `Event.purs` — Core event types (split into 3 modules)
- `EventQuery.purs` — Query functions
- `EventMod.purs` — Modifiers and display

### Created (DatePicker Element Port)

- `Element/Component/DatePicker.purs` — Main component (464 lines)
- `Element/Component/DatePicker/Types.purs` — DateFormat, ValidationError (80 lines)
- `Element/Component/DatePicker/Format.purs` — Pure PureScript formatting (228 lines)
- `Element/Component/DatePicker/Render.purs` — Render helpers (297 lines)

### Created (TimePicker Element Port)

- `Element/Component/TimePicker.purs` — Main component (496 lines)
- `Element/Component/TimePicker/Types.purs` — HourFormat, Period, ValidationError (121 lines)
- `Element/Component/TimePicker/Format.purs` — Pure PureScript formatting/parsing (268 lines)
- `Element/Component/TimePicker/Render.purs` — Render helpers (346 lines)

### Fixed

- `Hour.purs` — Added missing Show class import
- `Minute.purs` — Added missing Show class import
- `Second.purs` — Added missing Show class import
- `DatePicker.purs` — Fixed unused imports ((<>), formatDate)
- Removed monolithic `Time.purs` (replaced by individual modules)

### Verified

- Full build: 0 warnings, 0 errors
- All new modules under 500 line limit
- All imports explicit (no `(..)`)
- No JavaScript FFI in any component (caught and fixed FFI attempt in TimePicker/Format.purs)
