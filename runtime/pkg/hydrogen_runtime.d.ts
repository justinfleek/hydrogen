/* tslint:disable */
/* eslint-disable */

/**
 * State tracking all hidden elements for restoration.
 */
export class AriaHiderState {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Number of elements hidden.
     */
    readonly count: number;
}

/**
 * Breakpoint enumeration matching PureScript `Breakpoint` type.
 */
export enum Breakpoint {
    /**
     * < 768px
     */
    Mobile = 0,
    /**
     * >= 768px and < 1024px
     */
    Tablet = 1,
    /**
     * >= 1024px and < 1280px
     */
    Desktop = 2,
    /**
     * >= 1280px
     */
    LargeDesktop = 3,
}

/**
 * Handle for breakpoint change listener (multiple underlying listeners).
 */
export class BreakpointHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Standard breakpoint values in pixels (Tailwind conventions).
 *
 * Bounded: All values are positive integers within u16 range.
 */
export class Breakpoints {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * lg: 1024px
     */
    static lg(): number;
    /**
     * md: 768px
     */
    static md(): number;
    /**
     * sm: 640px
     */
    static sm(): number;
    /**
     * xl: 1280px
     */
    static xl(): number;
    /**
     * 2xl: 1536px
     */
    static xxl(): number;
}

/**
 * Complete visual state of a single DOM element.
 *
 * Mirrors `CapturedState` in PureScript.
 */
export class CapturedState {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    bg_a: number;
    bg_c: number;
    bg_h: number;
    bg_l: number;
    border_a: number;
    border_bottom_width: number;
    border_c: number;
    border_h: number;
    border_l: number;
    border_left_width: number;
    border_radius_bl: number;
    border_radius_br: number;
    border_radius_tl: number;
    border_radius_tr: number;
    border_right_width: number;
    border_top_width: number;
    depth: number;
    fg_a: number;
    fg_c: number;
    fg_h: number;
    fg_l: number;
    font_size: number;
    font_weight: number;
    height: number;
    index: number;
    letter_spacing: number;
    line_height: number;
    margin_bottom: number;
    margin_left: number;
    margin_right: number;
    margin_top: number;
    opacity: number;
    padding_bottom: number;
    padding_left: number;
    padding_right: number;
    padding_top: number;
    parent_index: number;
    transform_a: number;
    transform_b: number;
    transform_c: number;
    transform_d: number;
    transform_tx: number;
    transform_ty: number;
    width: number;
    x: number;
    y: number;
    z_index: number;
}

/**
 * Non-Copy fields stored separately
 */
export class CapturedStateStrings {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    readonly child_indices: Int32Array;
    readonly class_name: string;
    readonly element_id: string;
    readonly font_family: string;
    readonly tag_name: string;
}

/**
 * Chart padding (margins around the data area).
 */
export class ChartPadding {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Create new padding with all sides equal.
     */
    constructor(top: number, right: number, bottom: number, left: number);
    /**
     * Create uniform padding on all sides.
     */
    static uniform(value: number): ChartPadding;
    bottom: number;
    left: number;
    right: number;
    top: number;
}

/**
 * Debounced function state.
 */
export class Debouncer {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Call the debounced function.
     */
    call(args: any): void;
    /**
     * Cancel pending invocation.
     */
    cancel(): void;
    /**
     * Flush: invoke immediately if pending.
     */
    flush(): void;
    /**
     * Create a new debouncer.
     */
    constructor(wait_ms: number, leading: boolean, trailing: boolean, callback: Function);
}

/**
 * Geolocation error with code and message.
 */
export class GeoError {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    readonly code: GeoErrorCode;
    readonly message: string;
}

/**
 * Geolocation error codes.
 */
export enum GeoErrorCode {
    PermissionDenied = 1,
    PositionUnavailable = 2,
    Timeout = 3,
    Unknown = 0,
}

/**
 * Position options for requests.
 */
export class GeoOptions {
    free(): void;
    [Symbol.dispose](): void;
    constructor();
    with_high_accuracy(enabled: boolean): GeoOptions;
    with_maximum_age(ms: number): GeoOptions;
    with_timeout(ms: number): GeoOptions;
    enable_high_accuracy: boolean;
    maximum_age_ms: number;
    timeout_ms: number;
}

/**
 * Geographic position with bounded coordinates.
 */
export class GeoPosition {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    readonly accuracy: number;
    readonly altitude: number | undefined;
    readonly altitude_accuracy: number | undefined;
    readonly heading: number | undefined;
    readonly latitude: number;
    readonly longitude: number;
    readonly speed: number | undefined;
    readonly timestamp: number;
}

/**
 * Handle for an active position watch. Drop or call clear() to stop watching.
 */
export class GeoWatchHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Clear this watch (stop receiving position updates).
     */
    clear(): void;
    /**
     * Get the watch ID.
     */
    readonly watch_id: number;
}

/**
 * Geofence events.
 */
export enum GeofenceEvent {
    Enter = 0,
    Exit = 1,
    Dwell = 2,
}

/**
 * Handle for a geofence watch.
 */
export class GeofenceHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Clear the geofence watch.
     */
    clear(): void;
}

/**
 * Record of an element's original aria-hidden state.
 */
export class HiddenElement {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Intersection entry data (mirrors the JS structure).
 */
export class IntersectionEntry {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    bounding_bottom: number;
    bounding_height: number;
    bounding_left: number;
    bounding_right: number;
    bounding_top: number;
    bounding_width: number;
    intersection_ratio: number;
    is_intersecting: boolean;
    time: number;
}

/**
 * Handle for an intersection observer. Drop to disconnect.
 */
export class IntersectionHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Disconnect the observer.
     */
    disconnect(): void;
}

/**
 * Handle for crosshair cleanup. Drop to remove event listeners.
 */
export class LineCrosshairHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Clean up crosshair resources.
     */
    cleanup(): void;
    /**
     * Get the container ID this crosshair is attached to.
     */
    readonly container_id: string;
}

/**
 * Handle for link interceptor. Drop to stop intercepting.
 */
export class LinkInterceptHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Handle for a media query change listener. Drop to unsubscribe.
 */
export class MediaQueryHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Orientation enumeration.
 */
export enum Orientation {
    Portrait = 0,
    Landscape = 1,
}

/**
 * Handle for explode-on-click behavior.
 */
export class PieExplodeHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Handle for hover effects.
 */
export class PieHoverHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Pie slice data for tooltips.
 */
export class PieSliceData {
    free(): void;
    [Symbol.dispose](): void;
    constructor(label: string, value: number, percentage: number);
}

/**
 * Handle for tooltip behavior.
 */
export class PieTooltipHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Relative time units.
 */
export enum RelativeTimeUnit {
    Second = 0,
    Minute = 1,
    Hour = 2,
    Day = 3,
    Week = 4,
    Month = 5,
    Year = 6,
}

/**
 * Handle for route change listener. Drop to unsubscribe.
 */
export class RouteChangeHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * The main runtime interface exposed to JavaScript/PureScript.
 */
export class Runtime {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Create a new runtime attached to a canvas element.
     *
     * This is a factory method (not a constructor) because async constructors
     * produce invalid TypeScript definitions in wasm-bindgen.
     *
     * Usage from JavaScript:
     * ```js
     * const runtime = await Runtime.create(canvas);
     * ```
     */
    static create(canvas: HTMLCanvasElement): Promise<Runtime>;
    /**
     * Get the pick ID at screen coordinates.
     *
     * Returns 0 if no interactive element at that position.
     */
    pick(x: number, y: number): number;
    /**
     * Render a command buffer.
     *
     * Takes raw bytes from Hydrogen's Binary.serialize output.
     */
    render(bytes: Uint8Array): void;
    /**
     * Resize the renderer to match canvas size.
     */
    resize(width: number, height: number): void;
}

/**
 * Handle for a storage change listener. Drop to unsubscribe.
 */
export class StorageChangeHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * Throttled function state.
 */
export class Throttler {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Call the throttled function.
     */
    call(args: any): void;
    /**
     * Cancel pending invocation.
     */
    cancel(): void;
    /**
     * Flush: invoke immediately if pending.
     */
    flush(): void;
    /**
     * Create a new throttler.
     */
    constructor(wait_ms: number, leading: boolean, trailing: boolean, callback: Function);
}

/**
 * Tooltip position in screen coordinates.
 */
export class TooltipPosition {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Hidden tooltip.
     */
    static hidden(): TooltipPosition;
    /**
     * Create a new tooltip position.
     */
    constructor(x: number, y: number, visible: boolean);
    visible: boolean;
    x: number;
    y: number;
}

/**
 * A wrapped event with type identifier and payload.
 */
export class WrappedEvent {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Check if this event matches the expected type.
     */
    matches(expected_type_id: bigint): boolean;
    /**
     * Create a new wrapped event.
     */
    constructor(type_id: bigint, payload: any);
    /**
     * Unwrap the event if it matches the expected type.
     * Returns the payload if match, undefined otherwise.
     */
    unwrap_if_matches(expected_type_id: bigint): any;
    /**
     * Get the payload.
     */
    readonly payload: any;
    /**
     * Get the type ID.
     */
    readonly type_id: bigint;
}

/**
 * Handle for WebSocket event listeners. Drop to remove listeners.
 */
export class WsEventHandle {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
}

/**
 * High-resolution timestamp in milliseconds.
 * Uses performance.now() for sub-millisecond precision.
 */
export function animation_now(): number;

/**
 * Convert a number to a 32-bit integer by truncation toward zero.
 * Replaces the JS bitwise OR trick: `n | 0`
 */
export function animation_number_to_int(n: number): number;

/**
 * Hide all siblings of the given element from screen readers.
 * Walks up the DOM tree, hiding siblings at each level.
 */
export function aria_hider_hide_others(element: HTMLElement): AriaHiderState;

/**
 * Restore original aria-hidden values for all hidden elements.
 */
export function aria_hider_restore_others(state: AriaHiderState): void;

/**
 * Begin a compute pass.
 */
export function begin_compute_pass(encoder: GPUCommandEncoder): GPUComputePassEncoder;

/**
 * Begin a render pass.
 */
export function begin_render_pass(encoder: GPUCommandEncoder, desc: object): GPURenderPassEncoder;

/**
 * Capture state of all visible elements in the document.
 *
 * Returns a flat array of CapturedState with parent/child indices for tree reconstruction.
 */
export function capture_all_elements(): CapturedState[];

/**
 * Capture state of a single element by selector.
 */
export function capture_element(selector: string): CapturedState;

/**
 * Capture the string fields for an element (called separately to avoid Copy issues)
 */
export function capture_element_strings(selector: string): CapturedStateStrings;

/**
 * Configure a canvas for WebGPU rendering.
 * Returns the GPUCanvasContext.
 */
export function configure_canvas(device: GPUDevice, canvas: HTMLCanvasElement, format: string): GPUCanvasContext;

/**
 * Create a bind group.
 */
export function create_bind_group(device: GPUDevice, desc: object): any;

/**
 * Create a bind group layout.
 */
export function create_bind_group_layout(device: GPUDevice, desc: object): any;

/**
 * Create a GPU buffer.
 */
export function create_buffer(device: GPUDevice, desc: object): GPUBuffer;

/**
 * Create a command encoder.
 */
export function create_command_encoder(device: GPUDevice): GPUCommandEncoder;

/**
 * Create a compute pipeline.
 */
export function create_compute_pipeline(device: GPUDevice, desc: object): GPUComputePipeline;

/**
 * Create a pipeline layout.
 */
export function create_pipeline_layout(device: GPUDevice, desc: object): GPUPipelineLayout;

/**
 * Create a render pipeline.
 */
export function create_render_pipeline(device: GPUDevice, desc: object): GPURenderPipeline;

/**
 * Create a GPU sampler.
 */
export function create_sampler(device: GPUDevice, desc: object): GPUSampler;

/**
 * Create a shader module.
 */
export function create_shader_module(device: GPUDevice, desc: object): GPUShaderModule;

/**
 * Create a GPU texture.
 */
export function create_texture(device: GPUDevice, desc: object): GPUTexture;

/**
 * Create a texture view.
 */
export function create_texture_view(texture: GPUTexture, desc: object): GPUTextureView;

/**
 * Create a debounced function matching PureScript FFI signature.
 *
 * Returns a JS object with { call, cancel, flush } methods.
 *
 * PureScript signature:
 * ```purescript
 * foreign import debounceImpl
 *   :: forall a. Number -> Boolean -> Boolean -> (a -> Effect Unit)
 *   -> Effect { call :: a -> Effect Unit, cancel :: Effect Unit, flush :: Effect Unit }
 * ```
 */
export function debounceImpl(wait_ms: number, leading: boolean, trailing: boolean, callback: Function): any;

/**
 * Destroy a GPU buffer.
 */
export function destroy_buffer(buffer: GPUBuffer): void;

/**
 * Destroy a GPU texture.
 */
export function destroy_texture(texture: GPUTexture): void;

/**
 * Append a child node.
 */
export function dom_append_child(parent: Element, child: Node): void;

/**
 * Clear all children from an element.
 */
export function dom_clear_children(element: Element): void;

/**
 * Create an element with optional namespace.
 */
export function dom_create_element(tag_name: string, namespace?: string | null): Element;

/**
 * Create a text node.
 */
export function dom_create_text_node(text: string): Text;

/**
 * Get the 'checked' property from an input element.
 */
export function dom_get_input_checked(element: HTMLElement): boolean;

/**
 * Get the 'value' property from an input element.
 */
export function dom_get_input_value(element: HTMLElement): string;

/**
 * Get inner text content.
 */
export function dom_get_text_content(element: Element): string | undefined;

/**
 * Insert before a reference node.
 */
export function dom_insert_before(parent: Element, new_node: Node, reference_node?: Node | null): void;

/**
 * Remove a child node.
 */
export function dom_remove_child(parent: Element, child: Node): void;

/**
 * Remove a CSS style property from an element.
 */
export function dom_remove_style_property(element: HTMLElement, property: string): void;

/**
 * Replace a child node.
 */
export function dom_replace_child(parent: Element, new_child: Node, old_child: Node): void;

/**
 * Set a namespaced attribute on an element.
 * Used for SVG attributes like xlink:href.
 */
export function dom_set_attribute_ns(element: Element, namespace: string | null | undefined, name: string, value: string): void;

/**
 * Set the 'checked' property on an input element.
 */
export function dom_set_input_checked(element: HTMLElement, checked: boolean): void;

/**
 * Set the 'disabled' property on an input element.
 */
export function dom_set_input_disabled(element: HTMLElement, disabled: boolean): void;

/**
 * Set the 'value' property on an input element.
 * Uses typed HtmlInputElement API instead of reflection.
 */
export function dom_set_input_value(element: HTMLElement, value: string): void;

/**
 * Set a CSS style property on an element.
 */
export function dom_set_style_property(element: HTMLElement, property: string, value: string): void;

/**
 * Set inner text content (safe — no HTML parsing).
 */
export function dom_set_text_content(element: Element, text: string): void;

/**
 * Draw primitives.
 */
export function draw(pass: GPURenderPassEncoder, vertex_count: number, instance_count: number, first_vertex: number, first_instance: number): void;

/**
 * Draw indexed primitives.
 */
export function draw_indexed(pass: GPURenderPassEncoder, index_count: number, instance_count: number, first_index: number, base_vertex: number, first_instance: number): void;

/**
 * Draw indirect.
 */
export function draw_indirect(pass: GPURenderPassEncoder, buffer: GPUBuffer, offset: number): void;

/**
 * End a compute pass.
 */
export function end_compute_pass(pass: GPUComputePassEncoder): void;

/**
 * End a render pass.
 */
export function end_render_pass(pass: GPURenderPassEncoder): void;

/**
 * Generate a unique type ID for an event type.
 * This replaces JavaScript Symbols for runtime type safety.
 */
export function event_generate_type_id(): bigint;

/**
 * Log an event to console for debugging.
 */
export function event_log(bus_name: string | null | undefined, event: any): void;

/**
 * Unwrap an event if it matches the expected type.
 */
export function event_unwrap(wrapped: WrappedEvent, expected_type_id: bigint): any;

/**
 * Wrap an event with a type identifier.
 */
export function event_wrap(type_id: bigint, payload: any): WrappedEvent;

/**
 * Finish command encoder, returning command buffer.
 */
export function finish_command_encoder(encoder: GPUCommandEncoder): GPUCommandBuffer;

/**
 * Check if an element is visible (not display:none, visibility:hidden, or hidden attr).
 */
export function focus_trap_is_visible(element: HTMLElement): boolean;

/**
 * Convert a Node to HtmlElement if it is one.
 * Returns None if the node is not an HtmlElement.
 */
export function focus_trap_node_to_element(node: Node): HTMLElement | undefined;

/**
 * Referential equality check for DOM nodes.
 */
export function focus_trap_ref_eq(a: any, b: any): boolean;

/**
 * Clear a position watch by ID.
 */
export function geo_clear_watch(watch_id: number): void;

/**
 * Get current position (one-time).
 * Returns a Promise that resolves to GeoPosition or rejects with GeoError.
 */
export function geo_get_current_position(options: GeoOptions): Promise<GeoPosition>;

/**
 * Check if Geolocation API is supported.
 */
export function geo_is_supported(): boolean;

/**
 * Watch a circular geofence for enter/exit events.
 */
export function geo_watch_geofence(center_lat: number, center_lon: number, radius_meters: number, on_event: Function): GeofenceHandle;

/**
 * Watch position with continuous updates.
 * Returns a handle that can be used to clear the watch.
 */
export function geo_watch_position(options: GeoOptions, on_success: Function, on_error: Function): GeoWatchHandle;

/**
 * Get the current texture from canvas context.
 */
export function get_current_texture(ctx: GPUCanvasContext): GPUTexture;

/**
 * Get device features as array of strings.
 */
export function get_features(device: GPUDevice): Array<any>;

/**
 * Get device limits.
 */
export function get_limits(device: GPUDevice): GPUSupportedLimits;

/**
 * Get mapped range from buffer.
 */
export function get_mapped_range(buffer: GPUBuffer, offset: number, size: number): ArrayBuffer;

/**
 * Get preferred canvas format.
 */
export function get_preferred_canvas_format(): string;

/**
 * Get the command queue from a device.
 */
export function get_queue(device: GPUDevice): GPUQueue;

/**
 * Initialize panic hook for better error messages in browser console.
 * Returns error if logger initialization fails.
 */
export function init(): void;

/**
 * Observe an element for intersection changes.
 *
 * # Arguments
 * * `element` - The element to observe
 * * `threshold` - Visibility ratio (0.0 to 1.0) at which to trigger callback
 * * `root_margin` - Margin around the root (CSS margin syntax, e.g., "10px 20px")
 * * `root` - Optional root element to use as viewport (null = browser viewport)
 * * `callback` - Function called when intersection changes
 */
export function intersection_observe(element: Element, threshold: number, root_margin: string, root: Element | null | undefined, callback: Function): IntersectionHandle;

/**
 * Observe an element once (disconnect after first intersection).
 *
 * # Arguments
 * * `element` - The element to observe
 * * `threshold` - Visibility ratio (0.0 to 1.0) at which to trigger callback
 * * `root_margin` - Margin around the root (CSS margin syntax, e.g., "10px 20px")
 * * `root` - Optional root element to use as viewport (null = browser viewport)
 * * `callback` - Function called when element first intersects, then observer disconnects
 */
export function intersection_observe_once(element: Element, threshold: number, root_margin: string, root: Element | null | undefined, callback: Function): IntersectionHandle;

/**
 * Format a currency amount according to locale.
 *
 * # Arguments
 * * `locale` - BCP 47 language tag (e.g., "en-US", "de-DE")
 * * `amount` - Finite amount to format (bounded by Schema)
 * * `currency_symbol` - Currency symbol to prepend (e.g., "$", "€")
 *
 * # Returns
 * Formatted string (e.g., "$1,234.56" for en-US)
 *
 * # Note
 * For full ISO 4217 currency formatting, use the PureScript layer
 * which has complete currency code tables. This is a simplified version
 * that formats the number and prepends the symbol.
 */
export function intl_format_currency(locale: string, amount: number, currency_symbol: string): string;

/**
 * Format a decimal number according to locale.
 *
 * # Arguments
 * * `locale` - BCP 47 language tag (e.g., "en-US", "de-DE")
 * * `value` - Finite number to format (bounded by Schema)
 * * `decimal_places` - Number of decimal places to display
 *
 * # Returns
 * Formatted string (e.g., "1,234.56" for en-US)
 *
 * # Invariants
 * Input is guaranteed finite by Schema bounded types.
 */
export function intl_format_decimal(locale: string, value: number, decimal_places: number): string;

/**
 * Format an integer according to locale.
 *
 * # Arguments
 * * `locale` - BCP 47 language tag (e.g., "en-US", "de-DE")
 * * `value` - Integer to format
 *
 * # Returns
 * Formatted string (e.g., "1,234" for en-US)
 */
export function intl_format_integer(locale: string, value: bigint): string;

/**
 * Format a relative time value.
 *
 * # Arguments
 * * `value` - Numeric value (positive for future, negative for past)
 * * `unit` - Time unit
 * * `locale` - BCP 47 language tag
 *
 * # Returns
 * Formatted string in English (e.g., "in 2 days", "3 months ago")
 *
 * # Note
 * Full ICU4X RelativeTimeFormatter requires additional data loading.
 * This is a pure Rust implementation for common cases.
 */
export function intl_format_relative_time(value: number, unit: RelativeTimeUnit, _locale: string): string;

/**
 * Get the language subtag from a locale.
 * Returns empty string if invalid.
 */
export function intl_get_language(locale: string): string;

/**
 * Get the region subtag from a locale.
 * Returns empty string if not present or invalid.
 */
export function intl_get_region(locale: string): string;

/**
 * Check if a locale string is valid BCP 47.
 */
export function intl_is_valid_locale(locale: string): boolean;

/**
 * Check if WebGPU is supported.
 */
export function is_webgpu_supported(): boolean;

/**
 * Check if an input element is currently focused.
 * Returns true if focus is on input, textarea, select, or contenteditable.
 */
export function keyboard_is_input_focused(): boolean;

/**
 * Detect macOS/iOS platform for Cmd key handling.
 */
export function keyboard_is_mac_platform(): boolean;

/**
 * WASM-exported shortcut match check.
 * Takes flattened parameters for easy FFI.
 */
export function keyboard_shortcut_matches(input_key: string, input_code: string, input_ctrl: boolean, input_alt: boolean, input_shift: boolean, input_meta: boolean, def_key: string, def_ctrl: boolean, def_alt: boolean, def_shift: boolean, def_meta: boolean): boolean;

/**
 * Animate line drawing from start to end using stroke-dasharray.
 *
 * # Arguments
 * * `container_id` - Container element ID
 * * `duration_ms` - Animation duration in milliseconds
 * * `easing` - Easing function (uses CSS transition)
 */
export function line_animate(container_id: string, duration_ms: number): void;

/**
 * Clear all dot highlights.
 */
export function line_clear_dot_highlights(container_id: string, original_radius: number): void;

/**
 * Get total length of an SVG path.
 */
export function line_get_path_length(path_id: string): number;

/**
 * Get point at length along path.
 */
export function line_get_point_at_length(path_id: string, length: number): TooltipPosition;

/**
 * Hide tooltip.
 */
export function line_hide_tooltip(container_id: string): void;

/**
 * Highlight a data point dot.
 */
export function line_highlight_dot(container_id: string, index: number): void;

/**
 * Initialize crosshair for line chart.
 *
 * # Arguments
 * * `container_id` - Container element ID
 * * `padding` - Chart padding
 * * `on_move` - Callback with cursor position
 */
export function line_init_crosshair(container_id: string, padding: ChartPadding, on_move: Function): LineCrosshairHandle;

/**
 * Reset line animation to initial state.
 */
export function line_reset(container_id: string): void;

/**
 * Show tooltip at position.
 */
export function line_show_tooltip(container_id: string, x: number, y: number, content: string): void;

/**
 * Map a buffer asynchronously.
 */
export function map_buffer_async(buffer: GPUBuffer, mode: number, offset: number, size: number): any;

/**
 * Get the current breakpoint based on viewport width.
 */
export function mediaquery_current_breakpoint(): Breakpoint;

/**
 * Check if viewport is desktop (>= 1024px).
 */
export function mediaquery_is_desktop(): boolean;

/**
 * Check if display is high DPI (retina, >= 2x pixel ratio).
 */
export function mediaquery_is_high_dpi(): boolean;

/**
 * Check if device is in landscape orientation.
 */
export function mediaquery_is_landscape(): boolean;

/**
 * Check if viewport is large desktop (>= 1280px).
 */
export function mediaquery_is_large_desktop(): boolean;

/**
 * Check if viewport is mobile (< 768px).
 */
export function mediaquery_is_mobile(): boolean;

/**
 * Check if device is in portrait orientation.
 */
export function mediaquery_is_portrait(): boolean;

/**
 * Check if currently in print mode.
 */
export function mediaquery_is_print(): boolean;

/**
 * Check if viewport is tablet (>= 768px and < 1024px).
 */
export function mediaquery_is_tablet(): boolean;

/**
 * Check if device supports touch input.
 *
 * Uses hover:none + pointer:coarse heuristic.
 */
export function mediaquery_is_touch(): boolean;

/**
 * Check if a media query currently matches.
 *
 * Returns `false` if window or matchMedia is unavailable (SSR safety).
 */
export function mediaquery_matches(query: string): boolean;

/**
 * Subscribe to breakpoint changes.
 *
 * Callback receives the new Breakpoint value (0-3).
 */
export function mediaquery_on_breakpoint_change(callback: Function): BreakpointHandle;

/**
 * Subscribe to media query changes.
 *
 * Returns a handle that unsubscribes when dropped.
 * Callback receives `true` when query matches, `false` when it doesn't.
 */
export function mediaquery_on_change(query: string, callback: Function): MediaQueryHandle;

/**
 * Subscribe to color scheme changes.
 *
 * Callback receives `true` for dark mode, `false` for light mode.
 */
export function mediaquery_on_color_scheme_change(callback: Function): MediaQueryHandle;

/**
 * Subscribe to orientation changes.
 *
 * Callback receives `true` for portrait, `false` for landscape.
 */
export function mediaquery_on_orientation_change(callback: Function): MediaQueryHandle;

/**
 * Get current device orientation.
 */
export function mediaquery_orientation(): Orientation;

/**
 * Check if user prefers high contrast.
 */
export function mediaquery_prefers_contrast(): boolean;

/**
 * Check if user prefers dark color scheme.
 */
export function mediaquery_prefers_dark(): boolean;

/**
 * Check if user prefers light color scheme.
 */
export function mediaquery_prefers_light(): boolean;

/**
 * Check if user prefers reduced motion.
 *
 * Important for accessibility — disable animations when true.
 */
export function mediaquery_prefers_reduced_motion(): boolean;

/**
 * Check if user prefers reduced transparency.
 */
export function mediaquery_prefers_reduced_transparency(): boolean;

/**
 * Set a class on the body element.
 *
 * Useful for theme switching, modal open states, etc.
 */
export function meta_addBodyClass(class_name: string): void;

/**
 * Add a link tag.
 *
 * Corresponds to: `addLinkImpl` in `Hydrogen.Head.Meta`
 *
 * Parameters:
 * - rel: "preload", "prefetch", "preconnect", "dns-prefetch", "canonical", etc.
 * - href: URL or resource path
 * - as_type: For preload only ("script", "style", "image", "font", "fetch")
 */
export function meta_addLink(rel: string, href: string, as_type: string): void;

/**
 * Get a data attribute from the body.
 */
export function meta_getBodyData(key: string): string | undefined;

/**
 * Get meta tag content.
 *
 * Corresponds to: `getMetaImpl` in `Hydrogen.Head.Meta`
 *
 * Returns null if not found (PureScript handles as Nothing).
 */
export function meta_getMeta(name: string): string | undefined;

/**
 * Get current document title.
 *
 * Corresponds to: `getTitleImpl` in `Hydrogen.Head.Meta`
 */
export function meta_getTitle(): string;

/**
 * Check if body has a class.
 */
export function meta_hasBodyClass(class_name: string): boolean;

/**
 * Query a single element by CSS selector.
 *
 * Returns the first matching element, or None if not found.
 */
export function meta_querySelector(selector: string): Element | undefined;

/**
 * Remove an attribute from an element found by selector.
 */
export function meta_removeAttributeBySelector(selector: string, attr_name: string): boolean;

/**
 * Remove a class from the body element.
 */
export function meta_removeBodyClass(class_name: string): void;

/**
 * Remove a link tag by rel.
 *
 * Corresponds to: `removeLinkImpl` in `Hydrogen.Head.Meta`
 *
 * Removes ALL link tags with the given rel attribute.
 */
export function meta_removeLink(rel: string): void;

/**
 * Remove a meta tag.
 *
 * Corresponds to: `removeMetaImpl` in `Hydrogen.Head.Meta`
 */
export function meta_removeMeta(name: string): void;

/**
 * Set an attribute on an element found by selector.
 */
export function meta_setAttributeBySelector(selector: string, attr_name: string, attr_value: string): boolean;

/**
 * Set a data attribute on the body.
 *
 * Useful for storing state like theme, user preferences, etc.
 */
export function meta_setBodyData(key: string, value: string): void;

/**
 * Set favicon.
 *
 * Corresponds to: `setFaviconImpl` in `Hydrogen.Head.Meta`
 *
 * Removes existing favicon links and adds new one.
 */
export function meta_setFavicon(href: string): void;

/**
 * Set a meta tag (creates or updates).
 *
 * Corresponds to: `setMetaImpl` in `Hydrogen.Head.Meta`
 *
 * For Open Graph tags (og:*), uses property attribute.
 * For others, uses name attribute.
 */
export function meta_setMeta(name: string, content: string): void;

/**
 * Set document title.
 *
 * Corresponds to: `setTitleImpl` in `Hydrogen.Head.Meta`
 */
export function meta_setTitle(title: string): void;

/**
 * Toggle a class on the body element.
 */
export function meta_toggleBodyClass(class_name: string): boolean;

/**
 * Register callback for device lost.
 * Returns the promise for chaining.
 */
export function on_device_lost(device: GPUDevice, callback: Function): any;

/**
 * Register callback for uncaptured errors.
 * Returns error if event listener registration fails.
 */
export function on_uncaptured_error(device: GPUDevice, callback: Function): void;

/**
 * Animate slices with rotation effect.
 */
export function pie_animate_rotate(container_id: string, duration_ms: number): void;

/**
 * Animate pie slices appearing with scale effect.
 */
export function pie_animate_slices(container_id: string, duration_ms: number): void;

/**
 * Clear all slice highlights.
 */
export function pie_clear_highlights(container_id: string): void;

/**
 * Explode a slice outward from center.
 */
export function pie_explode_slice(container_id: string, index: number, distance: number): void;

/**
 * Calculate slice angle from mouse position (radians).
 */
export function pie_get_angle_from_mouse(container_id: string, mouse_x: number, mouse_y: number): number;

/**
 * Highlight a slice on hover.
 */
export function pie_highlight_slice(container_id: string, index: number): void;

/**
 * Initialize click-to-explode behavior.
 */
export function pie_init_explode_on_click(container_id: string, distance: number, on_click: Function): PieExplodeHandle;

/**
 * Initialize hover effects.
 */
export function pie_init_hover_effects(container_id: string): PieHoverHandle;

/**
 * Initialize tooltips for pie chart.
 */
export function pie_init_tooltips(container_id: string, data: PieSliceData[]): PieTooltipHandle;

/**
 * Reset all exploded slices.
 */
export function pie_reset_explode(container_id: string): void;

/**
 * Reset slice animation.
 */
export function pie_reset_slices(container_id: string): void;

/**
 * Request a GPU adapter.
 * Returns a Promise that resolves to GpuAdapter or rejects with error string.
 */
export function request_adapter(power_preference?: string | null): any;

/**
 * Request a GPU device from an adapter.
 * Returns a Promise that resolves to GpuDevice.
 */
export function request_device(adapter: GPUAdapter): any;

/**
 * Navigate back in history.
 * SIGIL opcode: 0xD4 (ROUTE_BACK)
 */
export function router_back(): void;

/**
 * Navigate forward in history.
 * SIGIL opcode: 0xD5 (ROUTE_FORWARD)
 */
export function router_forward(): void;

/**
 * Get the current hostname.
 */
export function router_get_hostname(): string;

/**
 * Get the current origin.
 */
export function router_get_origin(): string;

/**
 * Get the current pathname.
 */
export function router_get_pathname(): string;

/**
 * Intercept all internal link clicks for SPA navigation.
 */
export function router_intercept_links(callback: Function): LinkInterceptHandle;

/**
 * Subscribe to route changes (both popstate and programmatic).
 */
export function router_on_route_change(callback: Function): RouteChangeHandle;

/**
 * Push a new state to history.
 */
export function router_push_state(path: string): void;

/**
 * Replace the current state in history.
 */
export function router_replace_state(path: string): void;

/**
 * Set a bind group.
 */
export function set_bind_group(pass: GPURenderPassEncoder, index: number, bind_group: any): void;

/**
 * Set the index buffer.
 */
export function set_index_buffer(pass: GPURenderPassEncoder, buffer: GPUBuffer, format: string, offset: number, size: number): void;

/**
 * Set the render pipeline.
 */
export function set_pipeline(pass: GPURenderPassEncoder, pipeline: GPURenderPipeline): void;

/**
 * Set scissor rect.
 */
export function set_scissor_rect(pass: GPURenderPassEncoder, x: number, y: number, width: number, height: number): void;

/**
 * Set a vertex buffer.
 */
export function set_vertex_buffer(pass: GPURenderPassEncoder, slot: number, buffer: GPUBuffer, offset: number, size: number): void;

/**
 * Set viewport.
 */
export function set_viewport(pass: GPURenderPassEncoder, x: number, y: number, width: number, height: number, min_depth: number, max_depth: number): void;

/**
 * Add event listener for named events.
 */
export function sse_add_event_listener(source: EventSource, event_type: string, callback: Function): any;

/**
 * Close the EventSource connection.
 */
export function sse_close(source: EventSource): void;

/**
 * Create a new EventSource connection.
 */
export function sse_new(url: string, with_credentials: boolean): EventSource;

/**
 * Set onerror handler.
 */
export function sse_on_error(source: EventSource, callback: Function): any;

/**
 * Set onmessage handler (for unnamed events).
 */
export function sse_on_message(source: EventSource, callback: Function): any;

/**
 * Set onopen handler.
 */
export function sse_on_open(source: EventSource, callback: Function): any;

/**
 * Get ready state (0=CONNECTING, 1=OPEN, 2=CLOSED).
 */
export function sse_ready_state(source: EventSource): number;

/**
 * Get the URL.
 */
export function sse_url(source: EventSource): string;

/**
 * Clear all items from localStorage.
 */
export function storage_clear(): void;

/**
 * Get an item from localStorage. Returns empty string if not found or error.
 */
export function storage_get_item(key: string): string | undefined;

/**
 * Get all keys from localStorage.
 */
export function storage_keys(): string[];

/**
 * Get the number of items in localStorage.
 */
export function storage_length(): number;

/**
 * Subscribe to all storage changes.
 */
export function storage_on_any_change(callback: Function): StorageChangeHandle;

/**
 * Subscribe to storage changes for a specific key.
 * Returns a handle that unsubscribes when dropped.
 */
export function storage_on_change(key: string, callback: Function): StorageChangeHandle;

/**
 * Remove an item from localStorage.
 */
export function storage_remove_item(key: string): void;

/**
 * Set an item in localStorage.
 */
export function storage_set_item(key: string, value: string): void;

/**
 * Submit command buffers to the queue.
 */
export function submit(queue: GPUQueue, command_buffers: Array<any>): void;

/**
 * Create a throttled function matching PureScript FFI signature.
 *
 * Returns a JS object with { call, cancel, flush } methods.
 *
 * PureScript signature:
 * ```purescript
 * foreign import throttleImpl
 *   :: forall a. Number -> Boolean -> Boolean -> (a -> Effect Unit)
 *   -> Effect { call :: a -> Effect Unit, cancel :: Effect Unit, flush :: Effect Unit }
 * ```
 */
export function throttleImpl(wait_ms: number, leading: boolean, trailing: boolean, callback: Function): any;

/**
 * Unmap a buffer.
 */
export function unmap_buffer(buffer: GPUBuffer): void;

/**
 * Write data to a buffer via queue.
 */
export function write_buffer(queue: GPUQueue, buffer: GPUBuffer, buffer_offset: number, data: Uint8Array, data_offset: number, size: number): void;

/**
 * Write data to a texture via queue.
 */
export function write_texture(queue: GPUQueue, dest: object, data: Uint8Array, data_layout: object, size: object): void;

/**
 * Close the connection.
 */
export function ws_close(ws: WebSocket): void;

/**
 * Close with code and reason.
 */
export function ws_close_with_code(ws: WebSocket, code: number, reason: string): void;

/**
 * Create a new WebSocket connection.
 */
export function ws_new(url: string, protocols: string[]): WebSocket;

/**
 * Create a new WebSocket with a single protocol.
 */
export function ws_new_with_protocol(url: string, protocol: string): WebSocket;

/**
 * Set onclose handler.
 */
export function ws_on_close(ws: WebSocket, callback: Function): any;

/**
 * Set onerror handler.
 */
export function ws_on_error(ws: WebSocket, callback: Function): any;

/**
 * Set onmessage handler.
 */
export function ws_on_message(ws: WebSocket, callback: Function): any;

/**
 * Set onopen handler.
 */
export function ws_on_open(ws: WebSocket, callback: Function): any;

/**
 * Get ready state (0=CONNECTING, 1=OPEN, 2=CLOSING, 3=CLOSED).
 */
export function ws_ready_state(ws: WebSocket): number;

/**
 * Send a text message.
 */
export function ws_send(ws: WebSocket, data: string): void;

/**
 * Send binary data.
 */
export function ws_send_binary(ws: WebSocket, data: Uint8Array): void;

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly __wbg_debouncer_free: (a: number, b: number) => void;
    readonly __wbg_throttler_free: (a: number, b: number) => void;
    readonly debounceImpl: (a: number, b: number, c: number, d: any) => any;
    readonly debouncer_call: (a: number, b: any) => void;
    readonly debouncer_cancel: (a: number) => void;
    readonly debouncer_flush: (a: number) => void;
    readonly debouncer_new: (a: number, b: number, c: number, d: any) => number;
    readonly throttleImpl: (a: number, b: number, c: number, d: any) => any;
    readonly throttler_call: (a: number, b: any) => void;
    readonly throttler_cancel: (a: number) => void;
    readonly throttler_flush: (a: number) => void;
    readonly throttler_new: (a: number, b: number, c: number, d: any) => number;
    readonly __wbg_pieexplodehandle_free: (a: number, b: number) => void;
    readonly __wbg_piehoverhandle_free: (a: number, b: number) => void;
    readonly __wbg_pieslicedata_free: (a: number, b: number) => void;
    readonly __wbg_pietooltiphandle_free: (a: number, b: number) => void;
    readonly dom_append_child: (a: any, b: any) => [number, number];
    readonly dom_clear_children: (a: any) => void;
    readonly dom_create_element: (a: number, b: number, c: number, d: number) => [number, number, number];
    readonly dom_create_text_node: (a: number, b: number) => [number, number, number];
    readonly dom_get_input_checked: (a: any) => [number, number, number];
    readonly dom_get_input_value: (a: any) => [number, number, number, number];
    readonly dom_get_text_content: (a: any) => [number, number];
    readonly dom_insert_before: (a: any, b: any, c: number) => [number, number];
    readonly dom_remove_child: (a: any, b: any) => [number, number];
    readonly dom_remove_style_property: (a: any, b: number, c: number) => [number, number];
    readonly dom_replace_child: (a: any, b: any, c: any) => [number, number];
    readonly dom_set_attribute_ns: (a: any, b: number, c: number, d: number, e: number, f: number, g: number) => [number, number];
    readonly dom_set_input_checked: (a: any, b: number) => [number, number];
    readonly dom_set_input_disabled: (a: any, b: number) => [number, number];
    readonly dom_set_input_value: (a: any, b: number, c: number) => [number, number];
    readonly dom_set_style_property: (a: any, b: number, c: number, d: number, e: number) => [number, number];
    readonly dom_set_text_content: (a: any, b: number, c: number) => void;
    readonly pie_animate_rotate: (a: number, b: number, c: number) => [number, number];
    readonly pie_animate_slices: (a: number, b: number, c: number) => [number, number];
    readonly pie_clear_highlights: (a: number, b: number) => [number, number];
    readonly pie_explode_slice: (a: number, b: number, c: number, d: number) => [number, number];
    readonly pie_get_angle_from_mouse: (a: number, b: number, c: number, d: number) => number;
    readonly pie_highlight_slice: (a: number, b: number, c: number) => [number, number];
    readonly pie_init_explode_on_click: (a: number, b: number, c: number, d: any) => [number, number, number];
    readonly pie_init_hover_effects: (a: number, b: number) => [number, number, number];
    readonly pie_init_tooltips: (a: number, b: number, c: number, d: number) => [number, number, number];
    readonly pie_reset_explode: (a: number, b: number) => [number, number];
    readonly pie_reset_slices: (a: number, b: number) => [number, number];
    readonly pieslicedata_new: (a: number, b: number, c: number, d: number) => number;
    readonly __wbg_capturedstate_free: (a: number, b: number) => void;
    readonly __wbg_capturedstatestrings_free: (a: number, b: number) => void;
    readonly __wbg_chartpadding_free: (a: number, b: number) => void;
    readonly __wbg_get_capturedstate_bg_a: (a: number) => number;
    readonly __wbg_get_capturedstate_bg_c: (a: number) => number;
    readonly __wbg_get_capturedstate_bg_h: (a: number) => number;
    readonly __wbg_get_capturedstate_bg_l: (a: number) => number;
    readonly __wbg_get_capturedstate_border_a: (a: number) => number;
    readonly __wbg_get_capturedstate_border_bottom_width: (a: number) => number;
    readonly __wbg_get_capturedstate_border_c: (a: number) => number;
    readonly __wbg_get_capturedstate_border_h: (a: number) => number;
    readonly __wbg_get_capturedstate_border_l: (a: number) => number;
    readonly __wbg_get_capturedstate_border_left_width: (a: number) => number;
    readonly __wbg_get_capturedstate_border_radius_bl: (a: number) => number;
    readonly __wbg_get_capturedstate_border_radius_br: (a: number) => number;
    readonly __wbg_get_capturedstate_border_radius_tl: (a: number) => number;
    readonly __wbg_get_capturedstate_border_radius_tr: (a: number) => number;
    readonly __wbg_get_capturedstate_border_right_width: (a: number) => number;
    readonly __wbg_get_capturedstate_border_top_width: (a: number) => number;
    readonly __wbg_get_capturedstate_depth: (a: number) => number;
    readonly __wbg_get_capturedstate_fg_a: (a: number) => number;
    readonly __wbg_get_capturedstate_fg_c: (a: number) => number;
    readonly __wbg_get_capturedstate_fg_h: (a: number) => number;
    readonly __wbg_get_capturedstate_fg_l: (a: number) => number;
    readonly __wbg_get_capturedstate_font_size: (a: number) => number;
    readonly __wbg_get_capturedstate_font_weight: (a: number) => number;
    readonly __wbg_get_capturedstate_height: (a: number) => number;
    readonly __wbg_get_capturedstate_index: (a: number) => number;
    readonly __wbg_get_capturedstate_letter_spacing: (a: number) => number;
    readonly __wbg_get_capturedstate_line_height: (a: number) => number;
    readonly __wbg_get_capturedstate_margin_bottom: (a: number) => number;
    readonly __wbg_get_capturedstate_margin_left: (a: number) => number;
    readonly __wbg_get_capturedstate_margin_right: (a: number) => number;
    readonly __wbg_get_capturedstate_margin_top: (a: number) => number;
    readonly __wbg_get_capturedstate_opacity: (a: number) => number;
    readonly __wbg_get_capturedstate_padding_bottom: (a: number) => number;
    readonly __wbg_get_capturedstate_padding_left: (a: number) => number;
    readonly __wbg_get_capturedstate_padding_right: (a: number) => number;
    readonly __wbg_get_capturedstate_padding_top: (a: number) => number;
    readonly __wbg_get_capturedstate_parent_index: (a: number) => number;
    readonly __wbg_get_capturedstate_transform_a: (a: number) => number;
    readonly __wbg_get_capturedstate_transform_b: (a: number) => number;
    readonly __wbg_get_capturedstate_transform_c: (a: number) => number;
    readonly __wbg_get_capturedstate_transform_d: (a: number) => number;
    readonly __wbg_get_capturedstate_transform_tx: (a: number) => number;
    readonly __wbg_get_capturedstate_transform_ty: (a: number) => number;
    readonly __wbg_get_capturedstate_width: (a: number) => number;
    readonly __wbg_get_capturedstate_x: (a: number) => number;
    readonly __wbg_get_capturedstate_y: (a: number) => number;
    readonly __wbg_get_capturedstate_z_index: (a: number) => number;
    readonly __wbg_get_tooltipposition_visible: (a: number) => number;
    readonly __wbg_set_capturedstate_bg_a: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_bg_c: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_bg_h: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_bg_l: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_a: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_bottom_width: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_c: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_h: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_l: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_left_width: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_radius_bl: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_radius_br: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_radius_tl: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_radius_tr: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_right_width: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_border_top_width: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_depth: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_fg_a: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_fg_c: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_fg_h: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_fg_l: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_font_size: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_font_weight: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_height: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_index: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_letter_spacing: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_line_height: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_margin_bottom: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_margin_left: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_margin_right: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_margin_top: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_opacity: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_padding_bottom: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_padding_left: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_padding_right: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_padding_top: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_parent_index: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_transform_a: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_transform_b: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_transform_c: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_transform_d: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_transform_tx: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_transform_ty: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_width: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_x: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_y: (a: number, b: number) => void;
    readonly __wbg_set_capturedstate_z_index: (a: number, b: number) => void;
    readonly __wbg_set_tooltipposition_visible: (a: number, b: number) => void;
    readonly __wbg_tooltipposition_free: (a: number, b: number) => void;
    readonly capture_all_elements: () => [number, number, number, number];
    readonly capture_element: (a: number, b: number) => [number, number, number];
    readonly capture_element_strings: (a: number, b: number) => [number, number, number];
    readonly capturedstatestrings_child_indices: (a: number) => [number, number];
    readonly capturedstatestrings_class_name: (a: number) => [number, number];
    readonly capturedstatestrings_element_id: (a: number) => [number, number];
    readonly capturedstatestrings_font_family: (a: number) => [number, number];
    readonly capturedstatestrings_tag_name: (a: number) => [number, number];
    readonly chartpadding_new: (a: number, b: number, c: number, d: number) => number;
    readonly chartpadding_uniform: (a: number) => number;
    readonly tooltipposition_hidden: () => number;
    readonly tooltipposition_new: (a: number, b: number, c: number) => number;
    readonly __wbg_set_chartpadding_bottom: (a: number, b: number) => void;
    readonly __wbg_set_chartpadding_left: (a: number, b: number) => void;
    readonly __wbg_set_chartpadding_right: (a: number, b: number) => void;
    readonly __wbg_set_chartpadding_top: (a: number, b: number) => void;
    readonly __wbg_set_tooltipposition_x: (a: number, b: number) => void;
    readonly __wbg_set_tooltipposition_y: (a: number, b: number) => void;
    readonly __wbg_get_chartpadding_bottom: (a: number) => number;
    readonly __wbg_get_chartpadding_left: (a: number) => number;
    readonly __wbg_get_chartpadding_right: (a: number) => number;
    readonly __wbg_get_chartpadding_top: (a: number) => number;
    readonly __wbg_get_tooltipposition_x: (a: number) => number;
    readonly __wbg_get_tooltipposition_y: (a: number) => number;
    readonly __wbg_breakpointhandle_free: (a: number, b: number) => void;
    readonly __wbg_breakpoints_free: (a: number, b: number) => void;
    readonly __wbg_geoerror_free: (a: number, b: number) => void;
    readonly __wbg_geofencehandle_free: (a: number, b: number) => void;
    readonly __wbg_geooptions_free: (a: number, b: number) => void;
    readonly __wbg_geoposition_free: (a: number, b: number) => void;
    readonly __wbg_geowatchhandle_free: (a: number, b: number) => void;
    readonly __wbg_get_geooptions_enable_high_accuracy: (a: number) => number;
    readonly __wbg_get_geooptions_maximum_age_ms: (a: number) => number;
    readonly __wbg_get_geooptions_timeout_ms: (a: number) => number;
    readonly __wbg_get_intersectionentry_bounding_bottom: (a: number) => number;
    readonly __wbg_get_intersectionentry_bounding_height: (a: number) => number;
    readonly __wbg_get_intersectionentry_bounding_left: (a: number) => number;
    readonly __wbg_get_intersectionentry_bounding_right: (a: number) => number;
    readonly __wbg_get_intersectionentry_bounding_top: (a: number) => number;
    readonly __wbg_get_intersectionentry_bounding_width: (a: number) => number;
    readonly __wbg_get_intersectionentry_intersection_ratio: (a: number) => number;
    readonly __wbg_get_intersectionentry_is_intersecting: (a: number) => number;
    readonly __wbg_get_intersectionentry_time: (a: number) => number;
    readonly __wbg_intersectionentry_free: (a: number, b: number) => void;
    readonly __wbg_intersectionhandle_free: (a: number, b: number) => void;
    readonly __wbg_mediaqueryhandle_free: (a: number, b: number) => void;
    readonly __wbg_set_geooptions_enable_high_accuracy: (a: number, b: number) => void;
    readonly __wbg_set_geooptions_maximum_age_ms: (a: number, b: number) => void;
    readonly __wbg_set_geooptions_timeout_ms: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_bounding_bottom: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_bounding_height: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_bounding_left: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_bounding_right: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_bounding_top: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_bounding_width: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_intersection_ratio: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_is_intersecting: (a: number, b: number) => void;
    readonly __wbg_set_intersectionentry_time: (a: number, b: number) => void;
    readonly __wbg_wseventhandle_free: (a: number, b: number) => void;
    readonly breakpoints_lg: () => number;
    readonly breakpoints_md: () => number;
    readonly breakpoints_sm: () => number;
    readonly breakpoints_xl: () => number;
    readonly breakpoints_xxl: () => number;
    readonly geo_clear_watch: (a: number) => void;
    readonly geo_get_current_position: (a: number) => any;
    readonly geo_is_supported: () => number;
    readonly geo_watch_geofence: (a: number, b: number, c: number, d: any) => [number, number, number];
    readonly geo_watch_position: (a: number, b: any, c: any) => [number, number, number];
    readonly geoerror_code: (a: number) => number;
    readonly geoerror_message: (a: number) => [number, number];
    readonly geofencehandle_clear: (a: number) => void;
    readonly geooptions_new: () => number;
    readonly geooptions_with_high_accuracy: (a: number, b: number) => number;
    readonly geooptions_with_maximum_age: (a: number, b: number) => number;
    readonly geooptions_with_timeout: (a: number, b: number) => number;
    readonly geoposition_accuracy: (a: number) => number;
    readonly geoposition_altitude: (a: number) => [number, number];
    readonly geoposition_altitude_accuracy: (a: number) => [number, number];
    readonly geoposition_heading: (a: number) => [number, number];
    readonly geoposition_latitude: (a: number) => number;
    readonly geoposition_longitude: (a: number) => number;
    readonly geoposition_speed: (a: number) => [number, number];
    readonly geoposition_timestamp: (a: number) => number;
    readonly geowatchhandle_clear: (a: number) => void;
    readonly geowatchhandle_watch_id: (a: number) => number;
    readonly intersection_observe: (a: any, b: number, c: number, d: number, e: number, f: any) => [number, number, number];
    readonly intersection_observe_once: (a: any, b: number, c: number, d: number, e: number, f: any) => [number, number, number];
    readonly intersectionhandle_disconnect: (a: number) => void;
    readonly mediaquery_current_breakpoint: () => number;
    readonly mediaquery_is_desktop: () => number;
    readonly mediaquery_is_high_dpi: () => number;
    readonly mediaquery_is_landscape: () => number;
    readonly mediaquery_is_large_desktop: () => number;
    readonly mediaquery_is_mobile: () => number;
    readonly mediaquery_is_portrait: () => number;
    readonly mediaquery_is_print: () => number;
    readonly mediaquery_is_tablet: () => number;
    readonly mediaquery_is_touch: () => number;
    readonly mediaquery_matches: (a: number, b: number) => number;
    readonly mediaquery_on_breakpoint_change: (a: any) => [number, number, number];
    readonly mediaquery_on_change: (a: number, b: number, c: any) => [number, number, number];
    readonly mediaquery_on_color_scheme_change: (a: any) => [number, number, number];
    readonly mediaquery_on_orientation_change: (a: any) => [number, number, number];
    readonly mediaquery_orientation: () => number;
    readonly mediaquery_prefers_contrast: () => number;
    readonly mediaquery_prefers_dark: () => number;
    readonly mediaquery_prefers_light: () => number;
    readonly mediaquery_prefers_reduced_motion: () => number;
    readonly mediaquery_prefers_reduced_transparency: () => number;
    readonly sse_add_event_listener: (a: any, b: number, c: number, d: any) => [number, number, number];
    readonly sse_close: (a: any) => void;
    readonly sse_new: (a: number, b: number, c: number) => [number, number, number];
    readonly sse_on_error: (a: any, b: any) => any;
    readonly sse_on_message: (a: any, b: any) => any;
    readonly sse_on_open: (a: any, b: any) => any;
    readonly sse_ready_state: (a: any) => number;
    readonly sse_url: (a: any) => [number, number];
    readonly ws_close: (a: any) => [number, number];
    readonly ws_close_with_code: (a: any, b: number, c: number, d: number) => [number, number];
    readonly ws_new: (a: number, b: number, c: number, d: number) => [number, number, number];
    readonly ws_new_with_protocol: (a: number, b: number, c: number, d: number) => [number, number, number];
    readonly ws_on_close: (a: any, b: any) => any;
    readonly ws_on_error: (a: any, b: any) => any;
    readonly ws_on_message: (a: any, b: any) => any;
    readonly ws_on_open: (a: any, b: any) => any;
    readonly ws_ready_state: (a: any) => number;
    readonly ws_send: (a: any, b: number, c: number) => [number, number];
    readonly ws_send_binary: (a: any, b: number, c: number) => [number, number];
    readonly __wbg_ariahiderstate_free: (a: number, b: number) => void;
    readonly __wbg_hiddenelement_free: (a: number, b: number) => void;
    readonly aria_hider_hide_others: (a: any) => number;
    readonly aria_hider_restore_others: (a: number) => void;
    readonly ariahiderstate_count: (a: number) => number;
    readonly begin_compute_pass: (a: any) => any;
    readonly begin_render_pass: (a: any, b: any) => [number, number, number];
    readonly configure_canvas: (a: any, b: any, c: number, d: number) => [number, number, number];
    readonly create_bind_group: (a: any, b: any) => any;
    readonly create_bind_group_layout: (a: any, b: any) => [number, number, number];
    readonly create_buffer: (a: any, b: any) => [number, number, number];
    readonly create_command_encoder: (a: any) => any;
    readonly create_compute_pipeline: (a: any, b: any) => any;
    readonly create_pipeline_layout: (a: any, b: any) => any;
    readonly create_render_pipeline: (a: any, b: any) => [number, number, number];
    readonly create_sampler: (a: any, b: any) => any;
    readonly create_shader_module: (a: any, b: any) => any;
    readonly create_texture: (a: any, b: any) => [number, number, number];
    readonly create_texture_view: (a: any, b: any) => [number, number, number];
    readonly destroy_buffer: (a: any) => void;
    readonly destroy_texture: (a: any) => void;
    readonly draw: (a: any, b: number, c: number, d: number, e: number) => void;
    readonly draw_indexed: (a: any, b: number, c: number, d: number, e: number, f: number) => void;
    readonly draw_indirect: (a: any, b: any, c: number) => void;
    readonly end_compute_pass: (a: any) => void;
    readonly end_render_pass: (a: any) => void;
    readonly finish_command_encoder: (a: any) => any;
    readonly get_current_texture: (a: any) => [number, number, number];
    readonly get_features: (a: any) => any;
    readonly get_limits: (a: any) => any;
    readonly get_mapped_range: (a: any, b: number, c: number) => [number, number, number];
    readonly get_preferred_canvas_format: () => [number, number, number, number];
    readonly get_queue: (a: any) => any;
    readonly is_webgpu_supported: () => number;
    readonly map_buffer_async: (a: any, b: number, c: number, d: number) => any;
    readonly meta_addBodyClass: (a: number, b: number) => [number, number];
    readonly meta_addLink: (a: number, b: number, c: number, d: number, e: number, f: number) => [number, number];
    readonly meta_getBodyData: (a: number, b: number) => [number, number, number, number];
    readonly meta_getMeta: (a: number, b: number) => [number, number, number, number];
    readonly meta_getTitle: () => [number, number, number, number];
    readonly meta_hasBodyClass: (a: number, b: number) => [number, number, number];
    readonly meta_querySelector: (a: number, b: number) => [number, number, number];
    readonly meta_removeAttributeBySelector: (a: number, b: number, c: number, d: number) => [number, number, number];
    readonly meta_removeBodyClass: (a: number, b: number) => [number, number];
    readonly meta_removeLink: (a: number, b: number) => [number, number];
    readonly meta_removeMeta: (a: number, b: number) => [number, number];
    readonly meta_setAttributeBySelector: (a: number, b: number, c: number, d: number, e: number, f: number) => [number, number, number];
    readonly meta_setBodyData: (a: number, b: number, c: number, d: number) => [number, number];
    readonly meta_setFavicon: (a: number, b: number) => [number, number];
    readonly meta_setMeta: (a: number, b: number, c: number, d: number) => [number, number];
    readonly meta_setTitle: (a: number, b: number) => [number, number];
    readonly meta_toggleBodyClass: (a: number, b: number) => [number, number, number];
    readonly on_device_lost: (a: any, b: any) => any;
    readonly on_uncaptured_error: (a: any, b: any) => [number, number];
    readonly request_adapter: (a: number, b: number) => any;
    readonly request_device: (a: any) => any;
    readonly set_bind_group: (a: any, b: number, c: any) => void;
    readonly set_index_buffer: (a: any, b: any, c: number, d: number, e: number, f: number) => void;
    readonly set_pipeline: (a: any, b: any) => void;
    readonly set_scissor_rect: (a: any, b: number, c: number, d: number, e: number) => void;
    readonly set_vertex_buffer: (a: any, b: number, c: any, d: number, e: number) => void;
    readonly set_viewport: (a: any, b: number, c: number, d: number, e: number, f: number, g: number) => void;
    readonly submit: (a: any, b: any) => void;
    readonly unmap_buffer: (a: any) => void;
    readonly write_buffer: (a: any, b: any, c: number, d: any, e: number, f: number) => [number, number];
    readonly write_texture: (a: any, b: any, c: any, d: any, e: any) => [number, number];
    readonly __wbg_linkintercepthandle_free: (a: number, b: number) => void;
    readonly __wbg_routechangehandle_free: (a: number, b: number) => void;
    readonly __wbg_runtime_free: (a: number, b: number) => void;
    readonly __wbg_storagechangehandle_free: (a: number, b: number) => void;
    readonly init: () => void;
    readonly router_back: () => [number, number];
    readonly router_forward: () => [number, number];
    readonly router_get_hostname: () => [number, number];
    readonly router_get_origin: () => [number, number];
    readonly router_get_pathname: () => [number, number];
    readonly router_intercept_links: (a: any) => [number, number, number];
    readonly router_on_route_change: (a: any) => [number, number, number];
    readonly router_push_state: (a: number, b: number) => [number, number];
    readonly router_replace_state: (a: number, b: number) => [number, number];
    readonly runtime_create: (a: any) => any;
    readonly runtime_pick: (a: number, b: number, c: number) => number;
    readonly runtime_render: (a: number, b: number, c: number) => [number, number];
    readonly runtime_resize: (a: number, b: number, c: number) => void;
    readonly storage_clear: () => [number, number];
    readonly storage_get_item: (a: number, b: number) => [number, number];
    readonly storage_keys: () => [number, number];
    readonly storage_length: () => number;
    readonly storage_on_any_change: (a: any) => [number, number, number];
    readonly storage_on_change: (a: number, b: number, c: any) => [number, number, number];
    readonly storage_remove_item: (a: number, b: number) => [number, number];
    readonly storage_set_item: (a: number, b: number, c: number, d: number) => [number, number];
    readonly __wbg_linecrosshairhandle_free: (a: number, b: number) => void;
    readonly animation_now: () => number;
    readonly animation_number_to_int: (a: number) => number;
    readonly focus_trap_is_visible: (a: any) => number;
    readonly focus_trap_node_to_element: (a: any) => any;
    readonly focus_trap_ref_eq: (a: any, b: any) => number;
    readonly intl_format_currency: (a: number, b: number, c: number, d: number, e: number) => [number, number];
    readonly intl_format_decimal: (a: number, b: number, c: number, d: number) => [number, number];
    readonly intl_format_integer: (a: number, b: number, c: bigint) => [number, number];
    readonly intl_format_relative_time: (a: number, b: number, c: number, d: number) => [number, number];
    readonly intl_get_language: (a: number, b: number) => [number, number];
    readonly intl_get_region: (a: number, b: number) => [number, number];
    readonly intl_is_valid_locale: (a: number, b: number) => number;
    readonly keyboard_is_input_focused: () => number;
    readonly keyboard_is_mac_platform: () => number;
    readonly keyboard_shortcut_matches: (a: number, b: number, c: number, d: number, e: number, f: number, g: number, h: number, i: number, j: number, k: number, l: number, m: number, n: number) => number;
    readonly line_animate: (a: number, b: number, c: number) => [number, number];
    readonly line_clear_dot_highlights: (a: number, b: number, c: number) => [number, number];
    readonly line_get_path_length: (a: number, b: number) => number;
    readonly line_get_point_at_length: (a: number, b: number, c: number) => number;
    readonly line_hide_tooltip: (a: number, b: number) => [number, number];
    readonly line_highlight_dot: (a: number, b: number, c: number) => [number, number];
    readonly line_init_crosshair: (a: number, b: number, c: number, d: any) => [number, number, number];
    readonly line_reset: (a: number, b: number) => [number, number];
    readonly line_show_tooltip: (a: number, b: number, c: number, d: number, e: number, f: number) => [number, number];
    readonly linecrosshairhandle_cleanup: (a: number) => [number, number];
    readonly linecrosshairhandle_container_id: (a: number) => [number, number];
    readonly __wbg_wrappedevent_free: (a: number, b: number) => void;
    readonly event_generate_type_id: () => bigint;
    readonly event_log: (a: number, b: number, c: any) => void;
    readonly event_unwrap: (a: number, b: bigint) => any;
    readonly event_wrap: (a: bigint, b: any) => number;
    readonly wrappedevent_matches: (a: number, b: bigint) => number;
    readonly wrappedevent_payload: (a: number) => any;
    readonly wrappedevent_type_id: (a: number) => bigint;
    readonly wrappedevent_unwrap_if_matches: (a: number, b: bigint) => any;
    readonly wrappedevent_new: (a: bigint, b: any) => number;
    readonly wasm_bindgen__closure__destroy__h20c8283e70380080: (a: number, b: number) => void;
    readonly wasm_bindgen__closure__destroy__h74cdfa934dbd4e78: (a: number, b: number) => void;
    readonly wasm_bindgen__convert__closures_____invoke__ha7b5997a266ba3bb: (a: number, b: number, c: any, d: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e: (a: number, b: number, c: any) => [number, number];
    readonly wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e_17: (a: number, b: number, c: any) => [number, number];
    readonly wasm_bindgen__convert__closures_____invoke__h26c7a007d8dbb55a: (a: number, b: number, c: any) => [number, number];
    readonly wasm_bindgen__convert__closures_____invoke__h6c1eb3a335b0afa4: (a: number, b: number, c: any, d: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_2: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_3: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_4: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_5: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_8: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_9: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_10: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_11: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_12: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_13: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_14: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_15: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_16: (a: number, b: number, c: any) => void;
    readonly wasm_bindgen__convert__closures_____invoke__habd940842afd6a4b: (a: number, b: number) => void;
    readonly wasm_bindgen__convert__closures_____invoke__hb81663616f129ed0: (a: number, b: number) => void;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __externref_table_alloc: () => number;
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_exn_store: (a: number) => void;
    readonly __wbindgen_free: (a: number, b: number, c: number) => void;
    readonly __externref_table_dealloc: (a: number) => void;
    readonly __externref_drop_slice: (a: number, b: number) => void;
    readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
