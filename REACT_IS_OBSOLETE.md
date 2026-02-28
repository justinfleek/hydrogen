# REACT IS OBSOLETE

**A Technical Assessment**

*Prepared by the Hydrogen Framework Team*

---

## Abstract

This document presents a technical argument that React.js, while commercially
dominant, represents an obsolete approach to web application development. We
demonstrate this through systematic comparison with algebraically-grounded
alternatives, using the Hydrogen framework (PureScript/Halogen) as a reference
implementation. The argument is not that React lacks users, but that its core
paradigm—runtime virtual DOM diffing with simulated purity—has been superseded
by approaches offering stronger guarantees with equivalent or superior
expressiveness.

---

## 1. The Fundamental Problem: Impossible States

React applications routinely permit states that should be logically impossible.
Consider the canonical data fetching pattern:

```javascript
// React: The "standard" approach
const [loading, setLoading] = useState(false);
const [error, setError] = useState(null);
const [data, setData] = useState(null);

useEffect(() => {
  setLoading(true);
  fetch('/api/user')
    .then(res => res.json())
    .then(data => {
      setData(data);
      setLoading(false);
    })
    .catch(err => {
      setError(err);
      setLoading(false);
    });
}, []);
```

This permits the following impossible states:

| loading | error    | data     | Meaning                          | Possible? |
|---------|----------|----------|----------------------------------|-----------|
| `true`  | `null`   | `null`   | Loading                          | Valid     |
| `false` | `null`   | `{...}`  | Success                          | Valid     |
| `false` | `Error`  | `null`   | Failure                          | Valid     |
| `true`  | `Error`  | `null`   | Loading AND failed?              | **BUG**   |
| `true`  | `null`   | `{...}`  | Loading AND has data?            | **BUG**   |
| `false` | `Error`  | `{...}`  | Failed AND has data?             | **BUG**   |
| `true`  | `Error`  | `{...}`  | All three?                       | **BUG**   |
| `false` | `null`   | `null`   | Not loading, no error, no data?  | **BUG**   |

**Eight possible states. Three are valid. Five are bugs waiting to happen.**

The React community's response is TanStack Query, which mitigates but does not
eliminate this problem—it still exposes `{ data, error, isLoading, isFetching,
isError, isSuccess, ... }` as independent flags that the developer must
interpret correctly.

### The Algebraic Solution

Hydrogen's `RemoteData` type makes impossible states unrepresentable:

```purescript
data RemoteData e a
  = NotAsked    -- Request has not been made
  | Loading     -- Request is in flight  
  | Failure e   -- Request failed with error e
  | Success a   -- Request succeeded with value a
```

**Four states. Four valid states. Zero bugs from state incoherence.**

The compiler enforces exhaustive handling:

```purescript
render :: forall e a. RemoteData String User -> HTML
render = case _ of
  NotAsked  -> HH.text "Click to load"
  Loading   -> spinner
  Failure e -> errorCard e
  Success u -> userCard u
-- Compiler error if any case is missing
```

---

## 2. The Hooks Disaster

React Hooks were introduced in 2019 to bring "functional" patterns to React.
They failed.

### 2.1 Stale Closures

```javascript
function Counter() {
  const [count, setCount] = useState(0);
  
  useEffect(() => {
    const interval = setInterval(() => {
      console.log(count);  // Always logs initial value
      setCount(count + 1); // Always sets to 1
    }, 1000);
    return () => clearInterval(interval);
  }, []);  // Missing dependency
  
  return <div>{count}</div>;
}
```

This is a **fundamental design flaw**, not a user error. The `useEffect`
dependency array is a manual, error-prone mechanism that attempts to simulate
referential transparency in a language that lacks it.

### 2.2 Rules of Hooks

React Hooks require adherence to "Rules of Hooks":

1. Only call Hooks at the top level
2. Only call Hooks from React functions
3. Dependencies must be complete and correct

These are not "rules"—they are **symptoms of a leaky abstraction**. Pure
functional languages don't need "rules" because the type system enforces
correct composition automatically.

### 2.3 The PureScript Alternative

In PureScript, effects are tracked in the type system:

```purescript
-- The type signature declares what effects this computation performs
fetchUser :: String -> Aff (Either String User)
--                     ^^^ Async effect explicitly tracked

-- Composition is safe by construction
fetchDashboard :: String -> Aff DashboardData
fetchDashboard userId = do
  user  <- fetchUser userId
  posts <- fetchPosts userId
  stats <- fetchStats userId
  pure { user, posts, stats }
```

No dependency arrays. No stale closures. No rules to memorize. The compiler
ensures correctness.

---

## 3. Stringly-Typed Routing

React Router, the dominant routing solution, relies on string matching:

```javascript
// React Router: Stringly-typed, error-prone
<Routes>
  <Route path="/" element={<Home />} />
  <Route path="/user/:id" element={<User />} />
  <Route path="/dashbaord" element={<Dashboard />} />  {/* Typo undetected */}
</Routes>

// Navigation is equally fragile
navigate('/dashbaord');  // Runtime 404, compile-time silence
```

### The Type-Safe Alternative

Hydrogen routes are algebraic data types:

```purescript
-- Routes are a sum type
data Route = Home | User String | Dashboard | NotFound

-- Typeclass instance ensures bidirectional consistency
instance isRouteRoute :: IsRoute Route where
  parseRoute "/" = Home
  parseRoute s | Just id <- stripPrefix "/user/" s = User id
  parseRoute "/dashboard" = Dashboard
  parseRoute _ = NotFound
  
  routeToPath Home = "/"
  routeToPath (User id) = "/user/" <> id
  routeToPath Dashboard = "/dashboard"
  routeToPath NotFound = "/"

-- Type-safe navigation
navigate :: forall route. IsRoute route => route -> Effect Unit
navigate Dashboard   -- Compiles
navigate Dashbaord   -- COMPILE ERROR: Unknown data constructor
```

**Law**: `parseRoute (routeToPath r) == r` for all valid routes.

The compiler enforces that routes are valid. Typos become compile errors, not
runtime 404s.

---

## 4. The Composition Problem

React lacks principled composition mechanisms. The community has produced:

- Higher-Order Components (HOCs)
- Render Props
- Hooks
- Context
- State machines (XState)
- Signals (Jotai, Zustand)

Each is an attempt to solve the same underlying problem: **React components
don't compose algebraically**.

### 4.1 RemoteData Composes

Because `RemoteData` is a lawful Monad, queries combine naturally:

```purescript
-- Applicative: parallel semantics
let dashboard = ado
      user  <- userQuery.data
      posts <- postsQuery.data
      stats <- statsQuery.data
      in { user, posts, stats }

-- Monad: sequential semantics (for dependent queries)
let userPosts = do
      user <- userQuery.data
      posts <- fetchPostsFor user.id
      pure { user, posts }
```

**Laws satisfied**:

- **Functor**: `map id == id`
- **Applicative**: `pure id <*> v == v`
- **Monad**: `pure a >>= f == f a`

React Query provides similar functionality but cannot satisfy these laws because
JavaScript lacks the type system to enforce them.

### 4.2 Automatic Error Propagation

When combining `RemoteData` values, errors propagate automatically:

```purescript
-- If ANY query fails, the combined result is Failure
-- If ANY query is loading, the combined result is Loading
-- Only if ALL queries succeed is the result Success

instance applyRemoteData :: Apply (RemoteData e) where
  apply (Success f) (Success a) = Success (f a)
  apply (Failure e) _ = Failure e
  apply _ (Failure e) = Failure e
  apply Loading _ = Loading
  apply _ Loading = Loading
  apply NotAsked _ = NotAsked
  apply _ NotAsked = NotAsked
```

No manual error handling required. The algebra handles it.

---

## 5. The Virtual DOM Tax

React's core innovation (2013) was the virtual DOM: render everything, diff
against the previous render, apply minimal patches. This was revolutionary—and
is now a liability.

### 5.1 Runtime Overhead

Every React render:

1. Executes all component functions
2. Builds a new virtual DOM tree
3. Diffs against the previous tree
4. Patches the real DOM

This happens on **every state change**, even when the outcome is predictable at
compile time.

### 5.2 The Compiled Alternative

Frameworks like Svelte and Solid compile away the runtime:

```javascript
// Svelte: Compiled to surgical DOM updates
let count = 0;
$: doubled = count * 2;  // Reactive, no virtual DOM
```

```javascript
// Solid: Fine-grained reactivity, no virtual DOM
const [count, setCount] = createSignal(0);
const doubled = () => count() * 2;  // Derivation, no diffing
```

Halogen (which Hydrogen builds upon) uses a virtual DOM, but the type system
ensures components only re-render when necessary—and side effects are tracked
explicitly, preventing the "useEffect hell" common in React.

---

## 6. The TypeScript Retrofit

React was designed for JavaScript. TypeScript support is a retrofit:

```typescript
// Common React/TypeScript pain points

// 1. Generic components require verbose annotation
function List<T>({ items, render }: { 
  items: T[], 
  render: (item: T) => ReactNode 
}) { ... }

// 2. Event handlers lose type inference
<input onChange={(e) => setValue(e.target.value)} />
//                      ^^^^^^^ e is ChangeEvent<HTMLInputElement>
//                               but this is not inferred from context

// 3. Hooks can't express conditional computation
const user = useUser();  // Always runs
const posts = usePosts(user?.id);  // Must handle undefined
```

### 6.1 Native Type Safety

PureScript was designed with types from the ground up:

```purescript
-- Row polymorphism: structural typing done right
render :: forall r. { name :: String | r } -> HTML
render user = HH.text user.name
-- Works with any record containing `name :: String`

-- Type inference works everywhere
handleInput :: FormEvent -> Effect Unit
handleInput event = do
  value <- liftEffect $ targetValue event
  setValue value
  
-- Conditional computation is explicit
case user of
  Nothing -> pure unit
  Just u  -> fetchPosts u.id >>= setPosts
```

---

## 7. The Ecosystem Lock-In

React's dominance creates a self-reinforcing ecosystem:

1. Companies use React because developers know React
2. Developers learn React because companies use React
3. Libraries target React because of market share
4. Alternatives struggle despite technical superiority

This is not evidence of technical merit. It is evidence of network effects and
market dynamics. **Popularity is not a technical argument.**

### 7.1 The Counter-Argument

"But React has more libraries!"

True. React also has more:

- Security vulnerabilities in npm dependencies
- Breaking changes across major versions
- Abandoned packages
- Conflicting state management paradigms
- Configuration complexity (Webpack, Babel, etc.)

A smaller ecosystem with coherent design principles is preferable to a vast
ecosystem of incompatible solutions.

---

## 8. Exhibit A: Hydrogen

The Hydrogen framework demonstrates what becomes possible when starting from
sound foundations:

### 8.1 Query System

```purescript
-- Type-safe data fetching with automatic caching
state <- Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser config userId
  }

-- State is RemoteData + metadata
-- state :: { data :: RemoteData String User
--          , isStale :: Boolean
--          , isFetching :: Boolean }

-- Stale-while-revalidate is trivial
if state.isFetching && Q.hasData state
  then showWithSpinner (Q.getData state)
  else normalRender state.data
```

### 8.2 Route Metadata

```purescript
-- Define once, use everywhere
class RouteMetadata route where
  isProtected :: route -> Boolean
  isStaticRoute :: route -> Boolean
  routeTitle :: route -> String
  routeDescription :: route -> String
  routeOgImage :: route -> Maybe String

-- Same types for:
-- 1. Client-side SPA routing
-- 2. Server-side rendering
-- 3. Static site generation
-- 4. SEO metadata
```

### 8.3 SSG Integration

```purescript
-- "Write once, render anywhere" is automatic
renderRouteStatic :: forall route. 
  IsRoute route => RouteMetadata route => 
  DocConfig -> route -> HTML -> String

-- One route definition generates both static pages and SPA navigation
```

---

## 9. Conclusion

React is not obsolete in the market. It is obsolete **in principle**.

The evidence:

1. **Impossible states** are representable and common
2. **Hooks** require manual discipline the type system should enforce
3. **Routing** is stringly-typed by default
4. **Composition** lacks algebraic foundations
5. **Virtual DOM** imposes unavoidable runtime overhead
6. **TypeScript** is a retrofit, not native support
7. **Ecosystem** is vast but incoherent

React was a breakthrough in 2013. The ideas it pioneered—declarative UI,
unidirectional data flow, component composition—have been refined and surpassed.

The web development community remains on React not because it is the best tool,
but because:

- Migration costs are high
- Network effects favor incumbents
- Most developers learned React first
- Technical debt compounds

These are business and social constraints, not technical endorsements.

**For greenfield projects where correctness matters, React is the wrong
choice.**

---

## Appendix: The Laws

For reference, the algebraic laws that Hydrogen's `RemoteData` satisfies:

### Functor Laws

```
map id == id
map (f >>> g) == map f >>> map g
```

### Applicative Laws

```
pure id <*> v == v
pure (<<<) <*> u <*> v <*> w == u <*> (v <*> w)
pure f <*> pure x == pure (f x)
u <*> pure y == pure (\f -> f y) <*> u
```

### Monad Laws

```
pure a >>= f == f a
m >>= pure == m
(m >>= f) >>= g == m >>= (\x -> f x >>= g)
```

React cannot satisfy these laws because JavaScript lacks:

1. Parametric polymorphism (generics are erased)
2. Higher-kinded types
3. Typeclass constraints
4. Purity enforcement

---

*"The purpose of abstraction is not to be vague, but to create a new semantic
level in which one can be absolutely precise."*

— Edsger W. Dijkstra

---

**Document version**: 1.0  
**Framework reference**: Hydrogen 0.1.0  
**Date**: 2026-02-21
