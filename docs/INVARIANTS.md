-- FOUNDRY Dashboard Invariants
-- Mathematical and Logical Properties That Must Hold

-- Overview

This document defines ALL invariants that the FOUNDRY Dashboard must maintain.
These invariants are proven in Lean4 BEFORE any implementation begins.
Haskell and PureScript implementations must satisfy these invariants.


-- 1. Bounding Box Invariants (Foundry.Brand.Visual.Bounds)

INVARIANT: bounds_width_nonnegative
──────────────────────────────────
  forall bounds : BoundingBox.
    bounds.width >= 0

INVARIANT: bounds_height_nonnegative
───────────────────────────────────
  forall bounds : BoundingBox.
    bounds.height >= 0

INVARIANT: bounds_area_nonnegative
─────────────────────────────────
  forall bounds : BoundingBox.
    bounds.width * bounds.height >= 0

SMART CONSTRUCTOR: mkBoundingBox
────────────────────────────────
  mkBoundingBox : Float -> Float -> Float -> Float -> Maybe BoundingBox
  mkBoundingBox x y w h =
    if w >= 0 && h >= 0
    then Just { x, y, width: w, height: h }
    else Nothing

The constructor returns Nothing for invalid bounds, making invalid
states unrepresentable at construction time.


-- 2. Visual Element Invariants (Foundry.Brand.Visual.Element)

INVARIANT: element_has_valid_bounds
──────────────────────────────────
  forall element : VisualElement.
    element.bounds.width >= 0
    && element.bounds.height >= 0

INVARIANT: element_zindex_is_integer
───────────────────────────────────
  forall element : VisualElement.
    element.zIndex in Z  -- Z is the integers

INVARIANT: element_opacity_bounded
─────────────────────────────────
  forall element : VisualElement.
    0 <= element.opacity <= 100

INVARIANT: element_uuid5_deterministic
─────────────────────────────────────
  forall element : VisualElement.
    uuid5(namespace, contentHash(element)) = element.id

INVARIANT: element_uuid5_injective
─────────────────────────────────
  forall e1 e2 : VisualElement.
    e1.id = e2.id => contentHash(e1) = contentHash(e2)


-- 3. Color Invariants (Foundry.Core.Color)

INVARIANT: rgba_red_bounded
──────────────────────────
  forall color : RGBA.
    0 <= color.r <= 255

INVARIANT: rgba_green_bounded
────────────────────────────
  forall color : RGBA.
    0 <= color.g <= 255

INVARIANT: rgba_blue_bounded
───────────────────────────
  forall color : RGBA.
    0 <= color.b <= 255

INVARIANT: rgba_alpha_bounded
────────────────────────────
  forall color : RGBA.
    0 <= color.a <= 100

INVARIANT: rgba_equality_reflexive
─────────────────────────────────
  forall c : RGBA.
    c = c

INVARIANT: rgba_equality_symmetric
─────────────────────────────────
  forall c1 c2 : RGBA.
    c1 = c2 => c2 = c1


-- 4. Layer Invariants (Foundry.Brand.Visual.Layer)

INVARIANT: layer_elements_same_zindex
────────────────────────────────────
  forall layer : Layer.
    forall element in layer.elements.
      element.zIndex = layer.zIndex

INVARIANT: layer_elements_nonempty
─────────────────────────────────
  forall layer : Layer.
    length(layer.elements) > 0

INVARIANT: layers_zindex_unique
──────────────────────────────
  forall layers : Array Layer.
    forall i j. i != j =>
      layers[i].zIndex != layers[j].zIndex

INVARIANT: layers_sorted_ascending
─────────────────────────────────
  forall layers : Array Layer.
    forall i < j.
      layers[i].zIndex < layers[j].zIndex

This ensures painter's algorithm ordering: elements with lower z-index
render first (back to front).

INVARIANT: layers_z_monotonicity
───────────────────────────────
  forall layers : Array Layer.
    isSorted(map(.zIndex, layers))


-- 5. Scrape State Machine Invariants (Foundry.Pipeline.Scrape)

STATES:
  - Idle      : No scrape in progress
  - Loading   : Scrape in progress
  - Loaded    : Scrape completed successfully
  - Failed    : Scrape failed with error

INVARIANT: progress_bounded
──────────────────────────
  forall state : ScrapeState.
    state = Loading(progress) =>
      0.0 <= progress <= 1.0

INVARIANT: progress_monotonic
────────────────────────────
  forall state1 state2 : ScrapeState.
  forall transition : state1 -> state2.
    state1 = Loading(p1) && state2 = Loading(p2) =>
      p1 <= p2

Progress only increases; it never decreases during a scrape.

INVARIANT: valid_transitions
───────────────────────────
  The following are the ONLY valid state transitions:

  Idle    -> Loading(0.0)      -- Scrape initiated
  Loading -> Loading           -- Progress update
  Loading -> Loaded            -- Scrape succeeded
  Loading -> Failed            -- Scrape failed
  Loaded  -> Idle              -- Reset
  Failed  -> Idle              -- Reset

INVARIANT: loaded_has_result
───────────────────────────
  forall state : ScrapeState.
    state = Loaded =>
      exists result : ScrapeResult.
        state.result = Just(result)

INVARIANT: failed_has_error
──────────────────────────
  forall state : ScrapeState.
    state = Failed =>
      exists error : String.
        state.error = Just(error)
        && length(error) > 0


-- 6. Viewport Transform Invariants (Foundry.Viewport.Transform)

INVARIANT: zoom_bounded
──────────────────────
  forall viewport : ViewportState.
    0.25 <= viewport.zoom <= 4.0

Zoom is clamped to 25% minimum (0.25x) and 400% maximum (4.0x).

INVARIANT: transform_identity
────────────────────────────
  exists identity : Transform.
    forall t : Transform.
      compose(identity, t) = t
      && compose(t, identity) = t

INVARIANT: transform_inverse
───────────────────────────
  forall t : Transform.
    exists t_inv : Transform.
      compose(t, t_inv) = identity
      && compose(t_inv, t) = identity

INVARIANT: transform_associativity
─────────────────────────────────
  forall a b c : Transform.
    compose(compose(a, b), c) = compose(a, compose(b, c))

INVARIANT: scale_positive
────────────────────────
  forall t : Transform.
    t.scaleX > 0 && t.scaleY > 0

Scale factors must be positive (no flipping, no zero scale).

INVARIANT: zoom_in_increases
───────────────────────────
  forall viewport : ViewportState.
    let viewport' = applyZoomIn(viewport) in
      viewport'.zoom > viewport.zoom
      || viewport'.zoom = 4.0  -- at max

INVARIANT: zoom_out_decreases
────────────────────────────
  forall viewport : ViewportState.
    let viewport' = applyZoomOut(viewport) in
      viewport'.zoom < viewport.zoom
      || viewport'.zoom = 0.25  -- at min


-- 7. Clamp Invariants (Foundry.Viewport.Clamp)

INVARIANT: clamp_idempotent
──────────────────────────
  forall x min max : Float.
    clamp(clamp(x, min, max), min, max) = clamp(x, min, max)

INVARIANT: clamp_in_range
────────────────────────
  forall x min max : Float.
    min <= clamp(x, min, max) <= max

INVARIANT: clamp_preserves_valid
───────────────────────────────
  forall x min max : Float.
    min <= x <= max =>
      clamp(x, min, max) = x

INVARIANT: clamp_monotonic
─────────────────────────
  forall x1 x2 min max : Float.
    x1 <= x2 =>
      clamp(x1, min, max) <= clamp(x2, min, max)


-- 8. UUID5 Invariants (Foundry.Core.UUID5)

INVARIANT: uuid5_deterministic
─────────────────────────────
  forall namespace : UUID.
  forall name : String.
    uuid5(namespace, name) = uuid5(namespace, name)

Same inputs always produce same output.

INVARIANT: uuid5_namespace_sensitivity
─────────────────────────────────────
  forall ns1 ns2 : UUID.
  forall name : String.
    ns1 != ns2 =>
      uuid5(ns1, name) != uuid5(ns2, name)  -- with high probability

INVARIANT: uuid5_name_sensitivity
────────────────────────────────
  forall namespace : UUID.
  forall name1 name2 : String.
    name1 != name2 =>
      uuid5(namespace, name1) != uuid5(namespace, name2)  -- with high probability


-- 9. Coeffect Algebra Invariants (Foundry.Pipeline)

These are already proven in Foundry.Pipeline.lean but listed here for completeness.

INVARIANT: coeffect_idempotent
─────────────────────────────
  forall c : Coeffect.
    c `tensor` c = c  -- for deduplication

INVARIANT: coeffect_associativity
────────────────────────────────
  forall a b c : Coeffects.
    (a `tensor` b) `tensor` c = a `tensor` (b `tensor` c)

INVARIANT: coeffect_pure_identity
────────────────────────────────
  forall r : Coeffects.
    pure `tensor` r = r
    && r `tensor` pure = r


-- 10. Dashboard State Invariants (Dashboard.State)

INVARIANT: state_consistency
───────────────────────────
  forall state : DashboardState.
    state.scrapeStatus = Loaded =>
      isJust(state.scrapeResult)
      && isJust(state.screenshot)
      && length(state.layers) > 0

INVARIANT: selected_layer_valid
──────────────────────────────
  forall state : DashboardState.
    isJust(state.selectedLayer) =>
      state.selectedLayer < length(state.layers)

INVARIANT: url_valid_for_scrape
──────────────────────────────
  forall state : DashboardState.
    state.scrapeStatus = Loading =>
      isValidUrl(state.url)


-- 11. Reconstruction Invariants (Reconstruction)

INVARIANT: element_mapping_preserves_bounds
──────────────────────────────────────────
  forall element : VisualElement.
    let hydrogenElement = mapToHydrogen(element) in
      hydrogenElement.bounds = element.bounds

INVARIANT: layer_mapping_preserves_order
───────────────────────────────────────
  forall layers : Array Layer.
    let viewports = mapLayersToViewports(layers) in
      forall i j. i < j =>
        viewports[i].zIndex < viewports[j].zIndex

INVARIANT: color_mapping_exact
─────────────────────────────
  forall color : CSSColor.
    let rgba = parseColor(color) in
      toCSS(rgba) = normalizeCSS(color)

Parsing and serializing colors is lossless.


-- 12. Timestamp Invariants (Foundry.Timestamp)

INVARIANT: timestamp_ordered
───────────────────────────
  forall t1 t2 : Timestamp.
    t1.created_before(t2) => t1.nanos < t2.nanos

INVARIANT: timestamp_non_negative
────────────────────────────────
  forall t : Timestamp.
    t.nanos >= 0

INVARIANT: duration_non_negative
───────────────────────────────
  forall interval : TimeInterval.
    interval.start <= interval.end =>
      interval.duration >= 0


-- Summary Table

| Domain        | Invariant                    | Lean4 Module                    |
|---------------|------------------------------|---------------------------------|
| Bounds        | width >= 0, height >= 0      | Foundry.Brand.Visual.Bounds     |
| Element       | valid bounds, z in Z         | Foundry.Brand.Visual.Element    |
| Color         | r,g,b in [0,255], a in [0,100]| Foundry.Core.Color              |
| Layer         | z-monotonicity, sorted       | Foundry.Brand.Visual.Layer      |
| Scrape        | progress monotonic, valid tx | Foundry.Pipeline.Scrape         |
| Transform     | inverse identity, associative| Foundry.Viewport.Transform      |
| Clamp         | idempotent, monotonic        | Foundry.Viewport.Clamp          |
| UUID5         | deterministic, injective     | Foundry.Core.UUID5              |
| Coeffect      | associative, pure identity   | Foundry.Pipeline                |


-- Proof Strategy

Each invariant is proven using one of these strategies:

1. DEFINITIONAL
   The invariant holds by construction (smart constructors, bounded types)
   Example: mkBoundingBox rejects negative dimensions

2. INDUCTIVE
   Prove for base case, then prove preservation under all operations
   Example: Layer sorting preserved by insert operation

3. ALGEBRAIC
   Prove using algebraic laws (associativity, commutativity, identity)
   Example: Transform composition associativity

4. COMPUTATIONAL
   Use native_decide for decidable propositions on finite domains
   Example: Coeffect requiresNetwork on pipeline stages


-- Implementation Contract

Haskell and PureScript implementations MUST:

1. Use smart constructors that enforce invariants at construction time
2. Make invalid states unrepresentable (use types, not runtime checks)
3. Preserve invariants across all operations (proven by induction)
4. Never use escape hatches (undefined, unsafeCoerce, partial functions)
5. Have property-based tests that verify invariants hold


                                                      // foundry // invariants
                                                                     // 2026
