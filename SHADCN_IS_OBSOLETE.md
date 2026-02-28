# SHADCN IS OBSOLETE

**A Technical Assessment**

*Prepared by the Straylight Framework Team*

---

## Abstract

This document presents a technical argument that shadcn/ui, while popular and
well-designed for its ecosystem, represents an obsolete approach to component
library architecture. We demonstrate this through systematic comparison with
algebraically-grounded alternatives, using purescript-radix (behavioral
extraction) and verified-purescript (proof-carrying code) as reference
implementations. The argument is not that shadcn lacks utility, but that its
foundational dependencies—React, JavaScript, and runtime interpretation—have
been superseded by approaches offering stronger guarantees with equivalent or
superior expressiveness.

---

## 1. The Dependency Chain Problem

shadcn/ui is not a library—it's a collection of copy-paste React components
built on Radix UI primitives. Every shadcn component inherits the full
dependency chain:

```
shadcn/ui
  └─ Radix UI
       └─ React
            └─ JavaScript runtime
                 └─ No static guarantees
```

**Transitive dependencies for a single Dialog component:**

| Layer | Dependencies | Bundle Impact |
|-------|--------------|---------------|
| shadcn/ui | tailwind-merge, class-variance-authority, clsx | ~15KB |
| Radix Dialog | @radix-ui/react-dialog, @radix-ui/react-portal | ~25KB |
| Radix Primitives | @radix-ui/react-primitive, @radix-ui/react-compose-refs | ~10KB |
| React | react, react-dom | ~45KB (gzip) |
| **Total** | | **~95KB** for one dialog |

### The Pure Alternative

purescript-radix implements the same Dialog behavior in **407 lines of
PureScript** with **19 lines of FFI**:

```
src/Radix/Pure/Dialog.purs      407 loc
src/Radix/Pure/Dialog.js         19 loc
src/Radix/Pure/FocusTrap.purs   195 loc
src/Radix/Pure/FocusTrap.js      15 loc
src/Radix/Pure/AriaHider.purs    31 loc
src/Radix/Pure/AriaHider.js      34 loc
────────────────────────────────────────
Total                           701 loc
```

**No React. No Radix runtime. Just behavior.**

The compiled output is a fraction of the size because it doesn't ship a
framework runtime—only the code that actually executes.

---

## 2. The Behavior Extraction Principle

Radix UI components are fundamentally **state machines with DOM effects**:

```
Dialog   Closed ↔ Open   + focus trap + scroll lock + aria-hidden
Tabs     Selected(v)     + keyboard nav + roving tabindex
Popover  Closed ↔ Open   + positioning + collision detection
```

None of this requires React. The React dependency is an implementation detail,
not a semantic necessity.

### purescript-radix: Behavioral Parity

The pure Dialog implementation provides identical behavior:

| Feature | Radix (React) | purescript-radix |
|---------|---------------|------------------|
| Focus trap | ✓ | ✓ `FocusTrap.trapFocus` |
| Scroll lock | ✓ | ✓ `lockBodyScroll` FFI |
| Screen reader isolation | ✓ | ✓ `AriaHider.hideOthers` |
| Escape to close | ✓ | ✓ `HandleKeyDown` action |
| Click outside to close | ✓ | ✓ `HandleOverlayClick` |
| Focus restoration | ✓ | ✓ `previousActiveElement` |
| Controlled/uncontrolled | ✓ | ✓ `Input.open` |
| ARIA attributes | ✓ | ✓ Full implementation |

```purescript
-- Pure PureScript Dialog with full accessibility
type Input =
  { open :: Maybe Boolean           -- Controlled open state
  , defaultOpen :: Boolean          -- Initial state if uncontrolled
  , modal :: Boolean                -- Modal vs modeless
  , closeOnEscape :: Boolean        -- Close on Escape key
  , closeOnOutsideClick :: Boolean  -- Close on click outside
  }
```

The difference: **type-safe, no runtime framework**.

---

## 3. The Accessibility Paradox

shadcn/ui's value proposition is "accessible by default" through Radix
primitives. But accessibility is a **specification**, not an implementation.

### The Specification

WAI-ARIA defines Dialog behavior:

1. `role="dialog"` on content
2. `aria-modal="true"` for modal dialogs
3. `aria-labelledby` referencing the title
4. `aria-describedby` referencing the description
5. Focus trapped within dialog
6. Escape key closes dialog
7. Focus returns to trigger on close

### Implementation Comparison

**shadcn/ui (via Radix):**
```tsx
<Dialog.Root>
  <Dialog.Trigger>Open</Dialog.Trigger>
  <Dialog.Portal>
    <Dialog.Overlay />
    <Dialog.Content>
      <Dialog.Title>Title</Dialog.Title>
      <Dialog.Description>Description</Dialog.Description>
    </Dialog.Content>
  </Dialog.Portal>
</Dialog.Root>
```

**purescript-radix:**
```purescript
render state =
  HH.div [ HP.class_ (HH.ClassName "dialog-root") ]
    [ renderTrigger state
    , if state.isOpen then renderPortal state else HH.text ""
    ]

renderContent state =
  HH.div
    [ HP.id state.contentId
    , HP.attr (HH.AttrName "role") "dialog"
    , HP.attr (HH.AttrName "aria-modal") (if state.input.modal then "true" else "false")
    , ARIA.labelledBy state.titleId
    , ARIA.describedBy state.descriptionId
    ]
    [ ... ]
```

Both satisfy the specification. One requires React. One doesn't.

---

## 4. The Type Safety Gap

shadcn/ui components are TypeScript, but TypeScript's type system is
fundamentally limited:

### 4.1 Impossible States Are Representable

```typescript
// shadcn Dialog props (simplified)
interface DialogProps {
  open?: boolean;
  defaultOpen?: boolean;
  onOpenChange?: (open: boolean) => void;
}

// What happens with both controlled AND default?
<Dialog open={true} defaultOpen={false} />  // ??? TypeScript allows this
```

### 4.2 Component Composition Is Stringly-Typed

```typescript
// Radix requires specific DOM structure, enforced by... convention
<Dialog.Root>
  <Dialog.Content>  {/* Must be inside Root */}
    <Dialog.Title /> {/* Must be inside Content */}
  </Dialog.Content>
</Dialog.Root>

// This compiles but breaks at runtime:
<Dialog.Title />  // Outside Content - no error until runtime
```

### The PureScript Alternative

```purescript
-- The component IS the composition - no runtime surprises
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , finalize = Just Finalize
      , receive = Just <<< Receive
      }
  }
```

The type signature guarantees:
- `Query` defines external control interface
- `Input` defines props
- `Output` defines events
- `MonadAff m` constraint tracks effects

No runtime composition errors. The compiler enforces correctness.

---

## 5. The Lean Compiler: Behavioral Specification

purescript-radix includes a Lean 4 compiler that generates Halogen component
skeletons from behavioral specifications:

```lean
def dialogSpec : ComponentSpec := {
  name := "Dialog"
  behaviors := [.modal, .disclosure]
  parts := [
    { name := "Root", element := "div"
      props := [
        { name := "open", ty := .bool },
        { name := "modal", ty := .bool }
      ] },
    { name := "Trigger", element := "button" },
    { name := "Content", element := "div" }
  ]
}
```

Behaviors drive code generation:

| Behavior | Generated Code |
|----------|----------------|
| `.modal` | FocusTrap import, AriaHider import, scroll lock |
| `.disclosure` | Open/Close/Toggle queries, isOpen state |
| `.selection` | value state, ValueChanged output |
| `.navigation` | keyboard event handlers |

```bash
nix run . -- Dialog        # Enhanced: focus trap, scroll lock, aria
nix run . -- Tabs          # Enhanced: keyboard nav, roving tabindex
nix run . -- Button        # Generic skeleton
nix run . -- <anything>    # Works for any component name
```

**The specification becomes the implementation.**

---

## 6. Verified Components: Proof-Carrying Code

While shadcn/ui offers no formal guarantees, verified-purescript demonstrates
how to generate PureScript with machine-checked properties:

### 6.1 Algebraic Laws Proven in Lean 4

```lean
-- All proven by rfl (definitional equality)
theorem flip_flip     : flip (flip f) = f                    := rfl
theorem compose_assoc : (f ∘ g) ∘ h = f ∘ (g ∘ h)           := rfl
theorem identity_left : identity ∘ f = f                     := rfl
theorem identity_right: f ∘ identity = f                     := rfl
```

### 6.2 Type Class Laws Verified

```lean
-- Monad laws for List - the hard case, fully proven
structure SemMonad (m : Type → Type) extends SemFunctor m where
  pure : {α : Type} → α → m α
  bind : {α β : Type} → m α → (α → m β) → m β
  left_id  : ∀ {α β} (a : α) (f : α → m β), bind (pure a) f = f a
  right_id : ∀ {α} (ma : m α), bind ma pure = ma
  assoc    : ∀ {α β γ} (ma : m α) (f : α → m β) (g : β → m γ),
             bind (bind ma f) g = bind ma (fun x => bind (f x) g)

-- Instance with proofs
def monadList : SemMonad List where
  toSemFunctor := functorList
  pure := fun a => [a]
  bind := List.flatMap
  left_id := by intros; simp [List.flatMap]
  right_id := by intros; induction ma <;> simp_all [List.flatMap]
  assoc := by intros; induction ma <;> simp_all [List.flatMap]
```

### 6.3 Generated Code Carries Proof Status

```purescript
module Data.Function where

-- flip_flip: flip (flip f) = f
-- Status: ✓ PROVEN (PS.flip_flip)
flip f b a = f a b

-- compose_assoc: (f <<< g) <<< h = f <<< (g <<< h)
-- Status: ✓ PROVEN (PS.compose_assoc)
compose f g x = f (g x)
```

shadcn/ui components have **zero verified properties**. They rely on:
- Manual testing
- Property-based testing (samples, not proofs)
- "Trust us, Radix is battle-tested"

This is not a formal guarantee. It's social proof.

---

## 7. The Build Pipeline Comparison

### shadcn/ui Build

```
TypeScript → Babel/SWC → Bundler (Webpack/Vite/etc.) → Minifier → Output

Dependencies:
- Node.js runtime
- npm/pnpm/yarn
- TypeScript compiler
- Bundler configuration
- React runtime
- Tailwind CSS build
- PostCSS pipeline
```

### purescript-radix Build

```
PureScript → purs compile → Bundler (optional) → Output

Dependencies:
- PureScript compiler (single binary)
- spago (package manager)
- That's it
```

The PureScript compiler is a **total function from source to JavaScript**. No
configuration hell. No bundler compatibility matrix. No "works on my machine."

---

## 8. The Copy-Paste Anti-Pattern

shadcn/ui's core innovation is "copy-paste, not install." This is presented as
a feature:

> "This is NOT a component library. It's a collection of re-usable components
> that you can copy and paste into your apps."

This is an **anti-pattern** that trades:

| Benefit | Cost |
|---------|------|
| No version conflicts | No upstream bug fixes |
| Full customization | Full maintenance burden |
| No dependency | Code duplication across projects |
| "Ownership" | Divergence from best practices |

### The Alternative: Actual Libraries

purescript-radix is a **library**:

```yaml
# spago.yaml
package:
  dependencies:
    - radix-halogen
```

Updates flow through the package manager. Bug fixes are shared. The community
maintains one implementation, not thousands of forks.

---

## 9. The Tailwind Coupling

shadcn/ui is inseparable from Tailwind CSS. This creates:

### 9.1 Build Complexity

```javascript
// tailwind.config.js - required for shadcn
module.exports = {
  content: ["./components/**/*.{ts,tsx}"],
  theme: {
    extend: {
      // shadcn's custom theme tokens
    },
  },
  plugins: [require("tailwindcss-animate")],
}
```

### 9.2 Utility Class Explosion

```tsx
// Actual shadcn Button component
<button
  className={cn(
    "inline-flex items-center justify-center rounded-md text-sm font-medium",
    "ring-offset-background transition-colors focus-visible:outline-none",
    "focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2",
    "disabled:pointer-events-none disabled:opacity-50",
    variants[variant],
    sizes[size],
    className
  )}
>
```

This is not styling. This is **embedding design decisions in markup**.

### The Alternative: Separation of Concerns

```purescript
-- Style is data, not strings
renderTrigger state =
  HH.button
    [ HP.class_ (HH.ClassName "dialog-trigger")
    , HP.type_ HP.ButtonButton
    , HE.onClick \_ -> HandleTriggerClick
    ]
    [ HH.text "Open Dialog" ]
```

CSS is CSS. Behavior is behavior. They compose independently.

---

## 10. Line Count Comparison

### shadcn/ui Dialog (approximate)

```
node_modules/@radix-ui/react-dialog/    ~2,000 loc
node_modules/@radix-ui/react-portal/      ~500 loc
node_modules/@radix-ui/react-focus-*    ~1,500 loc
components/ui/dialog.tsx                   ~100 loc
React runtime                           ~15,000 loc
─────────────────────────────────────────────────────
Total shipped code                      ~19,100 loc
```

### purescript-radix Dialog

```
src/Radix/Pure/Dialog.purs                 407 loc
src/Radix/Pure/Dialog.js                    19 loc
src/Radix/Pure/FocusTrap.purs              195 loc
src/Radix/Pure/FocusTrap.js                 15 loc
src/Radix/Pure/AriaHider.purs               31 loc
src/Radix/Pure/AriaHider.js                 34 loc
src/Radix/Pure/Id.purs                      41 loc
─────────────────────────────────────────────────────
Total shipped code                         742 loc
```

**25x less code for equivalent functionality.**

---

## 11. The Ecosystem Argument

"But shadcn has more components!"

True. shadcn/ui provides ~40 components. purescript-radix currently provides 2
(Dialog, Tabs) with a compiler that generates skeletons for any component.

This is a temporary state, not a permanent limitation. The architecture scales:

```bash
# Generate any component skeleton
nix run . -- Accordion
nix run . -- AlertDialog
nix run . -- Avatar
nix run . -- Checkbox
# ... etc
```

More importantly: **fewer dependencies means fewer security vulnerabilities**,
faster builds, and simpler maintenance.

---

## 12. Conclusion

shadcn/ui is not obsolete in the market. It is obsolete **in principle**.

The evidence:

1. **Dependency chain** ships 95KB+ for a single component
2. **Behavior** is framework-independent but implementation is React-locked
3. **Accessibility** is a specification, not a React feature
4. **Type safety** is limited by TypeScript's structural type system
5. **Verification** is absent—no formal guarantees
6. **Build pipeline** requires extensive tooling
7. **Copy-paste model** creates maintenance burden
8. **Tailwind coupling** conflates styling with structure

The alternative exists:

- **purescript-radix**: Behavioral parity without React
- **verified-purescript**: Machine-checked algebraic properties
- **Lean 4 compiler**: Specification-driven code generation

For teams that value correctness, minimal dependencies, and long-term
maintainability, shadcn/ui is the wrong choice.

---

## Appendix: The Component Hierarchy

### shadcn/ui Architecture

```
User Code
    ↓
shadcn Component (copied)
    ↓
Radix Primitive
    ↓
React Component
    ↓
React Runtime
    ↓
Virtual DOM
    ↓
Real DOM
```

### purescript-radix Architecture

```
User Code
    ↓
Halogen Component
    ↓
Halogen VDom
    ↓
Real DOM
```

Three fewer layers. Three fewer places for bugs.

---

*"The purpose of abstraction is not to be vague, but to create a new semantic
level in which one can be absolutely precise."*

— Edsger W. Dijkstra

---

**Document version**: 1.0  
**Reference implementations**:
- purescript-radix (github:straylight-software/purescript-radix)
- verified-purescript (github:straylight-software/verified-purescript)
- Hydrogen 0.1.0

**Date**: 2026-02-21
