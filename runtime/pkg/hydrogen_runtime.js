/* @ts-self-types="./hydrogen_runtime.d.ts" */

/**
 * State tracking all hidden elements for restoration.
 */
export class AriaHiderState {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(AriaHiderState.prototype);
        obj.__wbg_ptr = ptr;
        AriaHiderStateFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        AriaHiderStateFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_ariahiderstate_free(ptr, 0);
    }
    /**
     * Number of elements hidden.
     * @returns {number}
     */
    get count() {
        const ret = wasm.ariahiderstate_count(this.__wbg_ptr);
        return ret >>> 0;
    }
}
if (Symbol.dispose) AriaHiderState.prototype[Symbol.dispose] = AriaHiderState.prototype.free;

/**
 * Breakpoint enumeration matching PureScript `Breakpoint` type.
 * @enum {0 | 1 | 2 | 3}
 */
export const Breakpoint = Object.freeze({
    /**
     * < 768px
     */
    Mobile: 0, "0": "Mobile",
    /**
     * >= 768px and < 1024px
     */
    Tablet: 1, "1": "Tablet",
    /**
     * >= 1024px and < 1280px
     */
    Desktop: 2, "2": "Desktop",
    /**
     * >= 1280px
     */
    LargeDesktop: 3, "3": "LargeDesktop",
});

/**
 * Handle for breakpoint change listener (multiple underlying listeners).
 */
export class BreakpointHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(BreakpointHandle.prototype);
        obj.__wbg_ptr = ptr;
        BreakpointHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        BreakpointHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_breakpointhandle_free(ptr, 0);
    }
}
if (Symbol.dispose) BreakpointHandle.prototype[Symbol.dispose] = BreakpointHandle.prototype.free;

/**
 * Standard breakpoint values in pixels (Tailwind conventions).
 *
 * Bounded: All values are positive integers within u16 range.
 */
export class Breakpoints {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        BreakpointsFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_breakpoints_free(ptr, 0);
    }
    /**
     * lg: 1024px
     * @returns {number}
     */
    static lg() {
        const ret = wasm.breakpoints_lg();
        return ret;
    }
    /**
     * md: 768px
     * @returns {number}
     */
    static md() {
        const ret = wasm.breakpoints_md();
        return ret;
    }
    /**
     * sm: 640px
     * @returns {number}
     */
    static sm() {
        const ret = wasm.breakpoints_sm();
        return ret;
    }
    /**
     * xl: 1280px
     * @returns {number}
     */
    static xl() {
        const ret = wasm.breakpoints_xl();
        return ret;
    }
    /**
     * 2xl: 1536px
     * @returns {number}
     */
    static xxl() {
        const ret = wasm.breakpoints_xxl();
        return ret;
    }
}
if (Symbol.dispose) Breakpoints.prototype[Symbol.dispose] = Breakpoints.prototype.free;

/**
 * Complete visual state of a single DOM element.
 *
 * Mirrors `CapturedState` in PureScript.
 */
export class CapturedState {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(CapturedState.prototype);
        obj.__wbg_ptr = ptr;
        CapturedStateFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        CapturedStateFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_capturedstate_free(ptr, 0);
    }
    /**
     * @returns {number}
     */
    get bg_a() {
        const ret = wasm.__wbg_get_capturedstate_bg_a(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bg_c() {
        const ret = wasm.__wbg_get_capturedstate_bg_c(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bg_h() {
        const ret = wasm.__wbg_get_capturedstate_bg_h(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bg_l() {
        const ret = wasm.__wbg_get_capturedstate_bg_l(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_a() {
        const ret = wasm.__wbg_get_capturedstate_border_a(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_bottom_width() {
        const ret = wasm.__wbg_get_capturedstate_border_bottom_width(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_c() {
        const ret = wasm.__wbg_get_capturedstate_border_c(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_h() {
        const ret = wasm.__wbg_get_capturedstate_border_h(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_l() {
        const ret = wasm.__wbg_get_capturedstate_border_l(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_left_width() {
        const ret = wasm.__wbg_get_capturedstate_border_left_width(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_radius_bl() {
        const ret = wasm.__wbg_get_capturedstate_border_radius_bl(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_radius_br() {
        const ret = wasm.__wbg_get_capturedstate_border_radius_br(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_radius_tl() {
        const ret = wasm.__wbg_get_capturedstate_border_radius_tl(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_radius_tr() {
        const ret = wasm.__wbg_get_capturedstate_border_radius_tr(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_right_width() {
        const ret = wasm.__wbg_get_capturedstate_border_right_width(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get border_top_width() {
        const ret = wasm.__wbg_get_capturedstate_border_top_width(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get depth() {
        const ret = wasm.__wbg_get_capturedstate_depth(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get fg_a() {
        const ret = wasm.__wbg_get_capturedstate_fg_a(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get fg_c() {
        const ret = wasm.__wbg_get_capturedstate_fg_c(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get fg_h() {
        const ret = wasm.__wbg_get_capturedstate_fg_h(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get fg_l() {
        const ret = wasm.__wbg_get_capturedstate_fg_l(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get font_size() {
        const ret = wasm.__wbg_get_capturedstate_font_size(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get font_weight() {
        const ret = wasm.__wbg_get_capturedstate_font_weight(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get height() {
        const ret = wasm.__wbg_get_capturedstate_height(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get index() {
        const ret = wasm.__wbg_get_capturedstate_index(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get letter_spacing() {
        const ret = wasm.__wbg_get_capturedstate_letter_spacing(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get line_height() {
        const ret = wasm.__wbg_get_capturedstate_line_height(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get margin_bottom() {
        const ret = wasm.__wbg_get_capturedstate_margin_bottom(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get margin_left() {
        const ret = wasm.__wbg_get_capturedstate_margin_left(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get margin_right() {
        const ret = wasm.__wbg_get_capturedstate_margin_right(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get margin_top() {
        const ret = wasm.__wbg_get_capturedstate_margin_top(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get opacity() {
        const ret = wasm.__wbg_get_capturedstate_opacity(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get padding_bottom() {
        const ret = wasm.__wbg_get_capturedstate_padding_bottom(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get padding_left() {
        const ret = wasm.__wbg_get_capturedstate_padding_left(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get padding_right() {
        const ret = wasm.__wbg_get_capturedstate_padding_right(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get padding_top() {
        const ret = wasm.__wbg_get_capturedstate_padding_top(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get parent_index() {
        const ret = wasm.__wbg_get_capturedstate_parent_index(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get transform_a() {
        const ret = wasm.__wbg_get_capturedstate_transform_a(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get transform_b() {
        const ret = wasm.__wbg_get_capturedstate_transform_b(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get transform_c() {
        const ret = wasm.__wbg_get_capturedstate_transform_c(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get transform_d() {
        const ret = wasm.__wbg_get_capturedstate_transform_d(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get transform_tx() {
        const ret = wasm.__wbg_get_capturedstate_transform_tx(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get transform_ty() {
        const ret = wasm.__wbg_get_capturedstate_transform_ty(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get width() {
        const ret = wasm.__wbg_get_capturedstate_width(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get x() {
        const ret = wasm.__wbg_get_capturedstate_x(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get y() {
        const ret = wasm.__wbg_get_capturedstate_y(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get z_index() {
        const ret = wasm.__wbg_get_capturedstate_z_index(this.__wbg_ptr);
        return ret;
    }
    /**
     * @param {number} arg0
     */
    set bg_a(arg0) {
        wasm.__wbg_set_capturedstate_bg_a(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bg_c(arg0) {
        wasm.__wbg_set_capturedstate_bg_c(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bg_h(arg0) {
        wasm.__wbg_set_capturedstate_bg_h(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bg_l(arg0) {
        wasm.__wbg_set_capturedstate_bg_l(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_a(arg0) {
        wasm.__wbg_set_capturedstate_border_a(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_bottom_width(arg0) {
        wasm.__wbg_set_capturedstate_border_bottom_width(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_c(arg0) {
        wasm.__wbg_set_capturedstate_border_c(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_h(arg0) {
        wasm.__wbg_set_capturedstate_border_h(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_l(arg0) {
        wasm.__wbg_set_capturedstate_border_l(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_left_width(arg0) {
        wasm.__wbg_set_capturedstate_border_left_width(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_radius_bl(arg0) {
        wasm.__wbg_set_capturedstate_border_radius_bl(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_radius_br(arg0) {
        wasm.__wbg_set_capturedstate_border_radius_br(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_radius_tl(arg0) {
        wasm.__wbg_set_capturedstate_border_radius_tl(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_radius_tr(arg0) {
        wasm.__wbg_set_capturedstate_border_radius_tr(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_right_width(arg0) {
        wasm.__wbg_set_capturedstate_border_right_width(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set border_top_width(arg0) {
        wasm.__wbg_set_capturedstate_border_top_width(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set depth(arg0) {
        wasm.__wbg_set_capturedstate_depth(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set fg_a(arg0) {
        wasm.__wbg_set_capturedstate_fg_a(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set fg_c(arg0) {
        wasm.__wbg_set_capturedstate_fg_c(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set fg_h(arg0) {
        wasm.__wbg_set_capturedstate_fg_h(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set fg_l(arg0) {
        wasm.__wbg_set_capturedstate_fg_l(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set font_size(arg0) {
        wasm.__wbg_set_capturedstate_font_size(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set font_weight(arg0) {
        wasm.__wbg_set_capturedstate_font_weight(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set height(arg0) {
        wasm.__wbg_set_capturedstate_height(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set index(arg0) {
        wasm.__wbg_set_capturedstate_index(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set letter_spacing(arg0) {
        wasm.__wbg_set_capturedstate_letter_spacing(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set line_height(arg0) {
        wasm.__wbg_set_capturedstate_line_height(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set margin_bottom(arg0) {
        wasm.__wbg_set_capturedstate_margin_bottom(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set margin_left(arg0) {
        wasm.__wbg_set_capturedstate_margin_left(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set margin_right(arg0) {
        wasm.__wbg_set_capturedstate_margin_right(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set margin_top(arg0) {
        wasm.__wbg_set_capturedstate_margin_top(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set opacity(arg0) {
        wasm.__wbg_set_capturedstate_opacity(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set padding_bottom(arg0) {
        wasm.__wbg_set_capturedstate_padding_bottom(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set padding_left(arg0) {
        wasm.__wbg_set_capturedstate_padding_left(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set padding_right(arg0) {
        wasm.__wbg_set_capturedstate_padding_right(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set padding_top(arg0) {
        wasm.__wbg_set_capturedstate_padding_top(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set parent_index(arg0) {
        wasm.__wbg_set_capturedstate_parent_index(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set transform_a(arg0) {
        wasm.__wbg_set_capturedstate_transform_a(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set transform_b(arg0) {
        wasm.__wbg_set_capturedstate_transform_b(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set transform_c(arg0) {
        wasm.__wbg_set_capturedstate_transform_c(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set transform_d(arg0) {
        wasm.__wbg_set_capturedstate_transform_d(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set transform_tx(arg0) {
        wasm.__wbg_set_capturedstate_transform_tx(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set transform_ty(arg0) {
        wasm.__wbg_set_capturedstate_transform_ty(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set width(arg0) {
        wasm.__wbg_set_capturedstate_width(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set x(arg0) {
        wasm.__wbg_set_capturedstate_x(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set y(arg0) {
        wasm.__wbg_set_capturedstate_y(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set z_index(arg0) {
        wasm.__wbg_set_capturedstate_z_index(this.__wbg_ptr, arg0);
    }
}
if (Symbol.dispose) CapturedState.prototype[Symbol.dispose] = CapturedState.prototype.free;

/**
 * Non-Copy fields stored separately
 */
export class CapturedStateStrings {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(CapturedStateStrings.prototype);
        obj.__wbg_ptr = ptr;
        CapturedStateStringsFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        CapturedStateStringsFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_capturedstatestrings_free(ptr, 0);
    }
    /**
     * @returns {Int32Array}
     */
    get child_indices() {
        const ret = wasm.capturedstatestrings_child_indices(this.__wbg_ptr);
        var v1 = getArrayI32FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 4, 4);
        return v1;
    }
    /**
     * @returns {string}
     */
    get class_name() {
        let deferred1_0;
        let deferred1_1;
        try {
            const ret = wasm.capturedstatestrings_class_name(this.__wbg_ptr);
            deferred1_0 = ret[0];
            deferred1_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * @returns {string}
     */
    get element_id() {
        let deferred1_0;
        let deferred1_1;
        try {
            const ret = wasm.capturedstatestrings_element_id(this.__wbg_ptr);
            deferred1_0 = ret[0];
            deferred1_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * @returns {string}
     */
    get font_family() {
        let deferred1_0;
        let deferred1_1;
        try {
            const ret = wasm.capturedstatestrings_font_family(this.__wbg_ptr);
            deferred1_0 = ret[0];
            deferred1_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * @returns {string}
     */
    get tag_name() {
        let deferred1_0;
        let deferred1_1;
        try {
            const ret = wasm.capturedstatestrings_tag_name(this.__wbg_ptr);
            deferred1_0 = ret[0];
            deferred1_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
        }
    }
}
if (Symbol.dispose) CapturedStateStrings.prototype[Symbol.dispose] = CapturedStateStrings.prototype.free;

/**
 * Chart padding (margins around the data area).
 */
export class ChartPadding {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(ChartPadding.prototype);
        obj.__wbg_ptr = ptr;
        ChartPaddingFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        ChartPaddingFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_chartpadding_free(ptr, 0);
    }
    /**
     * Create new padding with all sides equal.
     * @param {number} top
     * @param {number} right
     * @param {number} bottom
     * @param {number} left
     */
    constructor(top, right, bottom, left) {
        const ret = wasm.chartpadding_new(top, right, bottom, left);
        this.__wbg_ptr = ret >>> 0;
        ChartPaddingFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
    /**
     * Create uniform padding on all sides.
     * @param {number} value
     * @returns {ChartPadding}
     */
    static uniform(value) {
        const ret = wasm.chartpadding_uniform(value);
        return ChartPadding.__wrap(ret);
    }
    /**
     * @returns {number}
     */
    get bottom() {
        const ret = wasm.__wbg_get_chartpadding_bottom(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get left() {
        const ret = wasm.__wbg_get_chartpadding_left(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get right() {
        const ret = wasm.__wbg_get_chartpadding_right(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get top() {
        const ret = wasm.__wbg_get_chartpadding_top(this.__wbg_ptr);
        return ret;
    }
    /**
     * @param {number} arg0
     */
    set bottom(arg0) {
        wasm.__wbg_set_chartpadding_bottom(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set left(arg0) {
        wasm.__wbg_set_chartpadding_left(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set right(arg0) {
        wasm.__wbg_set_chartpadding_right(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set top(arg0) {
        wasm.__wbg_set_chartpadding_top(this.__wbg_ptr, arg0);
    }
}
if (Symbol.dispose) ChartPadding.prototype[Symbol.dispose] = ChartPadding.prototype.free;

/**
 * Debounced function state.
 */
export class Debouncer {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        DebouncerFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_debouncer_free(ptr, 0);
    }
    /**
     * Call the debounced function.
     * @param {any} args
     */
    call(args) {
        wasm.debouncer_call(this.__wbg_ptr, args);
    }
    /**
     * Cancel pending invocation.
     */
    cancel() {
        wasm.debouncer_cancel(this.__wbg_ptr);
    }
    /**
     * Flush: invoke immediately if pending.
     */
    flush() {
        wasm.debouncer_flush(this.__wbg_ptr);
    }
    /**
     * Create a new debouncer.
     * @param {number} wait_ms
     * @param {boolean} leading
     * @param {boolean} trailing
     * @param {Function} callback
     */
    constructor(wait_ms, leading, trailing, callback) {
        const ret = wasm.debouncer_new(wait_ms, leading, trailing, callback);
        this.__wbg_ptr = ret >>> 0;
        DebouncerFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
}
if (Symbol.dispose) Debouncer.prototype[Symbol.dispose] = Debouncer.prototype.free;

/**
 * Geolocation error with code and message.
 */
export class GeoError {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        GeoErrorFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_geoerror_free(ptr, 0);
    }
    /**
     * @returns {GeoErrorCode}
     */
    get code() {
        const ret = wasm.geoerror_code(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {string}
     */
    get message() {
        let deferred1_0;
        let deferred1_1;
        try {
            const ret = wasm.geoerror_message(this.__wbg_ptr);
            deferred1_0 = ret[0];
            deferred1_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
        }
    }
}
if (Symbol.dispose) GeoError.prototype[Symbol.dispose] = GeoError.prototype.free;

/**
 * Geolocation error codes.
 * @enum {1 | 2 | 3 | 0}
 */
export const GeoErrorCode = Object.freeze({
    PermissionDenied: 1, "1": "PermissionDenied",
    PositionUnavailable: 2, "2": "PositionUnavailable",
    Timeout: 3, "3": "Timeout",
    Unknown: 0, "0": "Unknown",
});

/**
 * Position options for requests.
 */
export class GeoOptions {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(GeoOptions.prototype);
        obj.__wbg_ptr = ptr;
        GeoOptionsFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        GeoOptionsFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_geooptions_free(ptr, 0);
    }
    constructor() {
        const ret = wasm.geooptions_new();
        this.__wbg_ptr = ret >>> 0;
        GeoOptionsFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
    /**
     * @param {boolean} enabled
     * @returns {GeoOptions}
     */
    with_high_accuracy(enabled) {
        const ptr = this.__destroy_into_raw();
        const ret = wasm.geooptions_with_high_accuracy(ptr, enabled);
        return GeoOptions.__wrap(ret);
    }
    /**
     * @param {number} ms
     * @returns {GeoOptions}
     */
    with_maximum_age(ms) {
        const ptr = this.__destroy_into_raw();
        const ret = wasm.geooptions_with_maximum_age(ptr, ms);
        return GeoOptions.__wrap(ret);
    }
    /**
     * @param {number} ms
     * @returns {GeoOptions}
     */
    with_timeout(ms) {
        const ptr = this.__destroy_into_raw();
        const ret = wasm.geooptions_with_timeout(ptr, ms);
        return GeoOptions.__wrap(ret);
    }
    /**
     * @returns {boolean}
     */
    get enable_high_accuracy() {
        const ret = wasm.__wbg_get_geooptions_enable_high_accuracy(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * @returns {number}
     */
    get maximum_age_ms() {
        const ret = wasm.__wbg_get_geooptions_maximum_age_ms(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * @returns {number}
     */
    get timeout_ms() {
        const ret = wasm.__wbg_get_geooptions_timeout_ms(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * @param {boolean} arg0
     */
    set enable_high_accuracy(arg0) {
        wasm.__wbg_set_geooptions_enable_high_accuracy(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set maximum_age_ms(arg0) {
        wasm.__wbg_set_geooptions_maximum_age_ms(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set timeout_ms(arg0) {
        wasm.__wbg_set_geooptions_timeout_ms(this.__wbg_ptr, arg0);
    }
}
if (Symbol.dispose) GeoOptions.prototype[Symbol.dispose] = GeoOptions.prototype.free;

/**
 * Geographic position with bounded coordinates.
 */
export class GeoPosition {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(GeoPosition.prototype);
        obj.__wbg_ptr = ptr;
        GeoPositionFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        GeoPositionFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_geoposition_free(ptr, 0);
    }
    /**
     * @returns {number}
     */
    get accuracy() {
        const ret = wasm.geoposition_accuracy(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number | undefined}
     */
    get altitude() {
        const ret = wasm.geoposition_altitude(this.__wbg_ptr);
        return ret[0] === 0 ? undefined : ret[1];
    }
    /**
     * @returns {number | undefined}
     */
    get altitude_accuracy() {
        const ret = wasm.geoposition_altitude_accuracy(this.__wbg_ptr);
        return ret[0] === 0 ? undefined : ret[1];
    }
    /**
     * @returns {number | undefined}
     */
    get heading() {
        const ret = wasm.geoposition_heading(this.__wbg_ptr);
        return ret[0] === 0 ? undefined : ret[1];
    }
    /**
     * @returns {number}
     */
    get latitude() {
        const ret = wasm.geoposition_latitude(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get longitude() {
        const ret = wasm.geoposition_longitude(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number | undefined}
     */
    get speed() {
        const ret = wasm.geoposition_speed(this.__wbg_ptr);
        return ret[0] === 0 ? undefined : ret[1];
    }
    /**
     * @returns {number}
     */
    get timestamp() {
        const ret = wasm.geoposition_timestamp(this.__wbg_ptr);
        return ret;
    }
}
if (Symbol.dispose) GeoPosition.prototype[Symbol.dispose] = GeoPosition.prototype.free;

/**
 * Handle for an active position watch. Drop or call clear() to stop watching.
 */
export class GeoWatchHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(GeoWatchHandle.prototype);
        obj.__wbg_ptr = ptr;
        GeoWatchHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        GeoWatchHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_geowatchhandle_free(ptr, 0);
    }
    /**
     * Clear this watch (stop receiving position updates).
     */
    clear() {
        wasm.geowatchhandle_clear(this.__wbg_ptr);
    }
    /**
     * Get the watch ID.
     * @returns {number}
     */
    get watch_id() {
        const ret = wasm.geowatchhandle_watch_id(this.__wbg_ptr);
        return ret;
    }
}
if (Symbol.dispose) GeoWatchHandle.prototype[Symbol.dispose] = GeoWatchHandle.prototype.free;

/**
 * Geofence events.
 * @enum {0 | 1 | 2}
 */
export const GeofenceEvent = Object.freeze({
    Enter: 0, "0": "Enter",
    Exit: 1, "1": "Exit",
    Dwell: 2, "2": "Dwell",
});

/**
 * Handle for a geofence watch.
 */
export class GeofenceHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(GeofenceHandle.prototype);
        obj.__wbg_ptr = ptr;
        GeofenceHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        GeofenceHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_geofencehandle_free(ptr, 0);
    }
    /**
     * Clear the geofence watch.
     */
    clear() {
        wasm.geofencehandle_clear(this.__wbg_ptr);
    }
}
if (Symbol.dispose) GeofenceHandle.prototype[Symbol.dispose] = GeofenceHandle.prototype.free;

/**
 * Record of an element's original aria-hidden state.
 */
export class HiddenElement {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        HiddenElementFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_hiddenelement_free(ptr, 0);
    }
}
if (Symbol.dispose) HiddenElement.prototype[Symbol.dispose] = HiddenElement.prototype.free;

/**
 * Intersection entry data (mirrors the JS structure).
 */
export class IntersectionEntry {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        IntersectionEntryFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_intersectionentry_free(ptr, 0);
    }
    /**
     * @returns {number}
     */
    get bounding_bottom() {
        const ret = wasm.__wbg_get_intersectionentry_bounding_bottom(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bounding_height() {
        const ret = wasm.__wbg_get_intersectionentry_bounding_height(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bounding_left() {
        const ret = wasm.__wbg_get_intersectionentry_bounding_left(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bounding_right() {
        const ret = wasm.__wbg_get_intersectionentry_bounding_right(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bounding_top() {
        const ret = wasm.__wbg_get_intersectionentry_bounding_top(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get bounding_width() {
        const ret = wasm.__wbg_get_intersectionentry_bounding_width(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get intersection_ratio() {
        const ret = wasm.__wbg_get_intersectionentry_intersection_ratio(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {boolean}
     */
    get is_intersecting() {
        const ret = wasm.__wbg_get_intersectionentry_is_intersecting(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * @returns {number}
     */
    get time() {
        const ret = wasm.__wbg_get_intersectionentry_time(this.__wbg_ptr);
        return ret;
    }
    /**
     * @param {number} arg0
     */
    set bounding_bottom(arg0) {
        wasm.__wbg_set_intersectionentry_bounding_bottom(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bounding_height(arg0) {
        wasm.__wbg_set_intersectionentry_bounding_height(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bounding_left(arg0) {
        wasm.__wbg_set_intersectionentry_bounding_left(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bounding_right(arg0) {
        wasm.__wbg_set_intersectionentry_bounding_right(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bounding_top(arg0) {
        wasm.__wbg_set_intersectionentry_bounding_top(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set bounding_width(arg0) {
        wasm.__wbg_set_intersectionentry_bounding_width(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set intersection_ratio(arg0) {
        wasm.__wbg_set_intersectionentry_intersection_ratio(this.__wbg_ptr, arg0);
    }
    /**
     * @param {boolean} arg0
     */
    set is_intersecting(arg0) {
        wasm.__wbg_set_intersectionentry_is_intersecting(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set time(arg0) {
        wasm.__wbg_set_intersectionentry_time(this.__wbg_ptr, arg0);
    }
}
if (Symbol.dispose) IntersectionEntry.prototype[Symbol.dispose] = IntersectionEntry.prototype.free;

/**
 * Handle for an intersection observer. Drop to disconnect.
 */
export class IntersectionHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(IntersectionHandle.prototype);
        obj.__wbg_ptr = ptr;
        IntersectionHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        IntersectionHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_intersectionhandle_free(ptr, 0);
    }
    /**
     * Disconnect the observer.
     */
    disconnect() {
        wasm.intersectionhandle_disconnect(this.__wbg_ptr);
    }
}
if (Symbol.dispose) IntersectionHandle.prototype[Symbol.dispose] = IntersectionHandle.prototype.free;

/**
 * Handle for crosshair cleanup. Drop to remove event listeners.
 */
export class LineCrosshairHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(LineCrosshairHandle.prototype);
        obj.__wbg_ptr = ptr;
        LineCrosshairHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        LineCrosshairHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_linecrosshairhandle_free(ptr, 0);
    }
    /**
     * Clean up crosshair resources.
     */
    cleanup() {
        const ret = wasm.linecrosshairhandle_cleanup(this.__wbg_ptr);
        if (ret[1]) {
            throw takeFromExternrefTable0(ret[0]);
        }
    }
    /**
     * Get the container ID this crosshair is attached to.
     * @returns {string}
     */
    get container_id() {
        let deferred1_0;
        let deferred1_1;
        try {
            const ret = wasm.linecrosshairhandle_container_id(this.__wbg_ptr);
            deferred1_0 = ret[0];
            deferred1_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
        }
    }
}
if (Symbol.dispose) LineCrosshairHandle.prototype[Symbol.dispose] = LineCrosshairHandle.prototype.free;

/**
 * Handle for link interceptor. Drop to stop intercepting.
 */
export class LinkInterceptHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(LinkInterceptHandle.prototype);
        obj.__wbg_ptr = ptr;
        LinkInterceptHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        LinkInterceptHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_linkintercepthandle_free(ptr, 0);
    }
}
if (Symbol.dispose) LinkInterceptHandle.prototype[Symbol.dispose] = LinkInterceptHandle.prototype.free;

/**
 * Handle for a media query change listener. Drop to unsubscribe.
 */
export class MediaQueryHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(MediaQueryHandle.prototype);
        obj.__wbg_ptr = ptr;
        MediaQueryHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        MediaQueryHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_mediaqueryhandle_free(ptr, 0);
    }
}
if (Symbol.dispose) MediaQueryHandle.prototype[Symbol.dispose] = MediaQueryHandle.prototype.free;

/**
 * Orientation enumeration.
 * @enum {0 | 1}
 */
export const Orientation = Object.freeze({
    Portrait: 0, "0": "Portrait",
    Landscape: 1, "1": "Landscape",
});

/**
 * Handle for explode-on-click behavior.
 */
export class PieExplodeHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(PieExplodeHandle.prototype);
        obj.__wbg_ptr = ptr;
        PieExplodeHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        PieExplodeHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_pieexplodehandle_free(ptr, 0);
    }
}
if (Symbol.dispose) PieExplodeHandle.prototype[Symbol.dispose] = PieExplodeHandle.prototype.free;

/**
 * Handle for hover effects.
 */
export class PieHoverHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(PieHoverHandle.prototype);
        obj.__wbg_ptr = ptr;
        PieHoverHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        PieHoverHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_piehoverhandle_free(ptr, 0);
    }
}
if (Symbol.dispose) PieHoverHandle.prototype[Symbol.dispose] = PieHoverHandle.prototype.free;

/**
 * Pie slice data for tooltips.
 */
export class PieSliceData {
    static __unwrap(jsValue) {
        if (!(jsValue instanceof PieSliceData)) {
            return 0;
        }
        return jsValue.__destroy_into_raw();
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        PieSliceDataFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_pieslicedata_free(ptr, 0);
    }
    /**
     * @param {string} label
     * @param {number} value
     * @param {number} percentage
     */
    constructor(label, value, percentage) {
        const ptr0 = passStringToWasm0(label, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.pieslicedata_new(ptr0, len0, value, percentage);
        this.__wbg_ptr = ret >>> 0;
        PieSliceDataFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
}
if (Symbol.dispose) PieSliceData.prototype[Symbol.dispose] = PieSliceData.prototype.free;

/**
 * Handle for tooltip behavior.
 */
export class PieTooltipHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(PieTooltipHandle.prototype);
        obj.__wbg_ptr = ptr;
        PieTooltipHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        PieTooltipHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_pietooltiphandle_free(ptr, 0);
    }
}
if (Symbol.dispose) PieTooltipHandle.prototype[Symbol.dispose] = PieTooltipHandle.prototype.free;

/**
 * Relative time units.
 * @enum {0 | 1 | 2 | 3 | 4 | 5 | 6}
 */
export const RelativeTimeUnit = Object.freeze({
    Second: 0, "0": "Second",
    Minute: 1, "1": "Minute",
    Hour: 2, "2": "Hour",
    Day: 3, "3": "Day",
    Week: 4, "4": "Week",
    Month: 5, "5": "Month",
    Year: 6, "6": "Year",
});

/**
 * Handle for route change listener. Drop to unsubscribe.
 */
export class RouteChangeHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(RouteChangeHandle.prototype);
        obj.__wbg_ptr = ptr;
        RouteChangeHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        RouteChangeHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_routechangehandle_free(ptr, 0);
    }
}
if (Symbol.dispose) RouteChangeHandle.prototype[Symbol.dispose] = RouteChangeHandle.prototype.free;

/**
 * The main runtime interface exposed to JavaScript/PureScript.
 */
export class Runtime {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(Runtime.prototype);
        obj.__wbg_ptr = ptr;
        RuntimeFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        RuntimeFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_runtime_free(ptr, 0);
    }
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
     * @param {HTMLCanvasElement} canvas
     * @returns {Promise<Runtime>}
     */
    static create(canvas) {
        const ret = wasm.runtime_create(canvas);
        return ret;
    }
    /**
     * Get the pick ID at screen coordinates.
     *
     * Returns 0 if no interactive element at that position.
     * @param {number} x
     * @param {number} y
     * @returns {number}
     */
    pick(x, y) {
        const ret = wasm.runtime_pick(this.__wbg_ptr, x, y);
        return ret >>> 0;
    }
    /**
     * Render a command buffer.
     *
     * Takes raw bytes from Hydrogen's Binary.serialize output.
     * @param {Uint8Array} bytes
     */
    render(bytes) {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.runtime_render(this.__wbg_ptr, ptr0, len0);
        if (ret[1]) {
            throw takeFromExternrefTable0(ret[0]);
        }
    }
    /**
     * Resize the renderer to match canvas size.
     * @param {number} width
     * @param {number} height
     */
    resize(width, height) {
        wasm.runtime_resize(this.__wbg_ptr, width, height);
    }
}
if (Symbol.dispose) Runtime.prototype[Symbol.dispose] = Runtime.prototype.free;

/**
 * Handle for a storage change listener. Drop to unsubscribe.
 */
export class StorageChangeHandle {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(StorageChangeHandle.prototype);
        obj.__wbg_ptr = ptr;
        StorageChangeHandleFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        StorageChangeHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_storagechangehandle_free(ptr, 0);
    }
}
if (Symbol.dispose) StorageChangeHandle.prototype[Symbol.dispose] = StorageChangeHandle.prototype.free;

/**
 * Throttled function state.
 */
export class Throttler {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        ThrottlerFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_throttler_free(ptr, 0);
    }
    /**
     * Call the throttled function.
     * @param {any} args
     */
    call(args) {
        wasm.throttler_call(this.__wbg_ptr, args);
    }
    /**
     * Cancel pending invocation.
     */
    cancel() {
        wasm.throttler_cancel(this.__wbg_ptr);
    }
    /**
     * Flush: invoke immediately if pending.
     */
    flush() {
        wasm.throttler_flush(this.__wbg_ptr);
    }
    /**
     * Create a new throttler.
     * @param {number} wait_ms
     * @param {boolean} leading
     * @param {boolean} trailing
     * @param {Function} callback
     */
    constructor(wait_ms, leading, trailing, callback) {
        const ret = wasm.throttler_new(wait_ms, leading, trailing, callback);
        this.__wbg_ptr = ret >>> 0;
        ThrottlerFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
}
if (Symbol.dispose) Throttler.prototype[Symbol.dispose] = Throttler.prototype.free;

/**
 * Tooltip position in screen coordinates.
 */
export class TooltipPosition {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(TooltipPosition.prototype);
        obj.__wbg_ptr = ptr;
        TooltipPositionFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        TooltipPositionFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_tooltipposition_free(ptr, 0);
    }
    /**
     * @returns {boolean}
     */
    get visible() {
        const ret = wasm.__wbg_get_tooltipposition_visible(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * @returns {number}
     */
    get x() {
        const ret = wasm.__wbg_get_tooltipposition_x(this.__wbg_ptr);
        return ret;
    }
    /**
     * @returns {number}
     */
    get y() {
        const ret = wasm.__wbg_get_tooltipposition_y(this.__wbg_ptr);
        return ret;
    }
    /**
     * @param {boolean} arg0
     */
    set visible(arg0) {
        wasm.__wbg_set_tooltipposition_visible(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set x(arg0) {
        wasm.__wbg_set_tooltipposition_x(this.__wbg_ptr, arg0);
    }
    /**
     * @param {number} arg0
     */
    set y(arg0) {
        wasm.__wbg_set_tooltipposition_y(this.__wbg_ptr, arg0);
    }
    /**
     * Hidden tooltip.
     * @returns {TooltipPosition}
     */
    static hidden() {
        const ret = wasm.tooltipposition_hidden();
        return TooltipPosition.__wrap(ret);
    }
    /**
     * Create a new tooltip position.
     * @param {number} x
     * @param {number} y
     * @param {boolean} visible
     */
    constructor(x, y, visible) {
        const ret = wasm.tooltipposition_new(x, y, visible);
        this.__wbg_ptr = ret >>> 0;
        TooltipPositionFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
}
if (Symbol.dispose) TooltipPosition.prototype[Symbol.dispose] = TooltipPosition.prototype.free;

/**
 * A wrapped event with type identifier and payload.
 */
export class WrappedEvent {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(WrappedEvent.prototype);
        obj.__wbg_ptr = ptr;
        WrappedEventFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        WrappedEventFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_wrappedevent_free(ptr, 0);
    }
    /**
     * Check if this event matches the expected type.
     * @param {bigint} expected_type_id
     * @returns {boolean}
     */
    matches(expected_type_id) {
        const ret = wasm.wrappedevent_matches(this.__wbg_ptr, expected_type_id);
        return ret !== 0;
    }
    /**
     * Create a new wrapped event.
     * @param {bigint} type_id
     * @param {any} payload
     */
    constructor(type_id, payload) {
        const ret = wasm.wrappedevent_new(type_id, payload);
        this.__wbg_ptr = ret >>> 0;
        WrappedEventFinalization.register(this, this.__wbg_ptr, this);
        return this;
    }
    /**
     * Get the payload.
     * @returns {any}
     */
    get payload() {
        const ret = wasm.wrappedevent_payload(this.__wbg_ptr);
        return ret;
    }
    /**
     * Get the type ID.
     * @returns {bigint}
     */
    get type_id() {
        const ret = wasm.wrappedevent_type_id(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Unwrap the event if it matches the expected type.
     * Returns the payload if match, undefined otherwise.
     * @param {bigint} expected_type_id
     * @returns {any}
     */
    unwrap_if_matches(expected_type_id) {
        const ret = wasm.wrappedevent_unwrap_if_matches(this.__wbg_ptr, expected_type_id);
        return ret;
    }
}
if (Symbol.dispose) WrappedEvent.prototype[Symbol.dispose] = WrappedEvent.prototype.free;

/**
 * Handle for WebSocket event listeners. Drop to remove listeners.
 */
export class WsEventHandle {
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        WsEventHandleFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_wseventhandle_free(ptr, 0);
    }
}
if (Symbol.dispose) WsEventHandle.prototype[Symbol.dispose] = WsEventHandle.prototype.free;

/**
 * High-resolution timestamp in milliseconds.
 * Uses performance.now() for sub-millisecond precision.
 * @returns {number}
 */
export function animation_now() {
    const ret = wasm.animation_now();
    return ret;
}

/**
 * Convert a number to a 32-bit integer by truncation toward zero.
 * Replaces the JS bitwise OR trick: `n | 0`
 * @param {number} n
 * @returns {number}
 */
export function animation_number_to_int(n) {
    const ret = wasm.animation_number_to_int(n);
    return ret;
}

/**
 * Hide all siblings of the given element from screen readers.
 * Walks up the DOM tree, hiding siblings at each level.
 * @param {HTMLElement} element
 * @returns {AriaHiderState}
 */
export function aria_hider_hide_others(element) {
    const ret = wasm.aria_hider_hide_others(element);
    return AriaHiderState.__wrap(ret);
}

/**
 * Restore original aria-hidden values for all hidden elements.
 * @param {AriaHiderState} state
 */
export function aria_hider_restore_others(state) {
    _assertClass(state, AriaHiderState);
    var ptr0 = state.__destroy_into_raw();
    wasm.aria_hider_restore_others(ptr0);
}

/**
 * Begin a compute pass.
 * @param {GPUCommandEncoder} encoder
 * @returns {GPUComputePassEncoder}
 */
export function begin_compute_pass(encoder) {
    const ret = wasm.begin_compute_pass(encoder);
    return ret;
}

/**
 * Begin a render pass.
 * @param {GPUCommandEncoder} encoder
 * @param {object} desc
 * @returns {GPURenderPassEncoder}
 */
export function begin_render_pass(encoder, desc) {
    const ret = wasm.begin_render_pass(encoder, desc);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Capture state of all visible elements in the document.
 *
 * Returns a flat array of CapturedState with parent/child indices for tree reconstruction.
 * @returns {CapturedState[]}
 */
export function capture_all_elements() {
    const ret = wasm.capture_all_elements();
    if (ret[3]) {
        throw takeFromExternrefTable0(ret[2]);
    }
    var v1 = getArrayJsValueFromWasm0(ret[0], ret[1]).slice();
    wasm.__wbindgen_free(ret[0], ret[1] * 4, 4);
    return v1;
}

/**
 * Capture state of a single element by selector.
 * @param {string} selector
 * @returns {CapturedState}
 */
export function capture_element(selector) {
    const ptr0 = passStringToWasm0(selector, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.capture_element(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return CapturedState.__wrap(ret[0]);
}

/**
 * Capture the string fields for an element (called separately to avoid Copy issues)
 * @param {string} selector
 * @returns {CapturedStateStrings}
 */
export function capture_element_strings(selector) {
    const ptr0 = passStringToWasm0(selector, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.capture_element_strings(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return CapturedStateStrings.__wrap(ret[0]);
}

/**
 * Configure a canvas for WebGPU rendering.
 * Returns the GPUCanvasContext.
 * @param {GPUDevice} device
 * @param {HTMLCanvasElement} canvas
 * @param {string} format
 * @returns {GPUCanvasContext}
 */
export function configure_canvas(device, canvas, format) {
    const ptr0 = passStringToWasm0(format, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.configure_canvas(device, canvas, ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a bind group.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {any}
 */
export function create_bind_group(device, desc) {
    const ret = wasm.create_bind_group(device, desc);
    return ret;
}

/**
 * Create a bind group layout.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {any}
 */
export function create_bind_group_layout(device, desc) {
    const ret = wasm.create_bind_group_layout(device, desc);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a GPU buffer.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPUBuffer}
 */
export function create_buffer(device, desc) {
    const ret = wasm.create_buffer(device, desc);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a command encoder.
 * @param {GPUDevice} device
 * @returns {GPUCommandEncoder}
 */
export function create_command_encoder(device) {
    const ret = wasm.create_command_encoder(device);
    return ret;
}

/**
 * Create a compute pipeline.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPUComputePipeline}
 */
export function create_compute_pipeline(device, desc) {
    const ret = wasm.create_compute_pipeline(device, desc);
    return ret;
}

/**
 * Create a pipeline layout.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPUPipelineLayout}
 */
export function create_pipeline_layout(device, desc) {
    const ret = wasm.create_pipeline_layout(device, desc);
    return ret;
}

/**
 * Create a render pipeline.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPURenderPipeline}
 */
export function create_render_pipeline(device, desc) {
    const ret = wasm.create_render_pipeline(device, desc);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a GPU sampler.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPUSampler}
 */
export function create_sampler(device, desc) {
    const ret = wasm.create_sampler(device, desc);
    return ret;
}

/**
 * Create a shader module.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPUShaderModule}
 */
export function create_shader_module(device, desc) {
    const ret = wasm.create_shader_module(device, desc);
    return ret;
}

/**
 * Create a GPU texture.
 * @param {GPUDevice} device
 * @param {object} desc
 * @returns {GPUTexture}
 */
export function create_texture(device, desc) {
    const ret = wasm.create_texture(device, desc);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a texture view.
 * @param {GPUTexture} texture
 * @param {object} desc
 * @returns {GPUTextureView}
 */
export function create_texture_view(texture, desc) {
    const ret = wasm.create_texture_view(texture, desc);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

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
 * @param {number} wait_ms
 * @param {boolean} leading
 * @param {boolean} trailing
 * @param {Function} callback
 * @returns {any}
 */
export function debounceImpl(wait_ms, leading, trailing, callback) {
    const ret = wasm.debounceImpl(wait_ms, leading, trailing, callback);
    return ret;
}

/**
 * Destroy a GPU buffer.
 * @param {GPUBuffer} buffer
 */
export function destroy_buffer(buffer) {
    wasm.destroy_buffer(buffer);
}

/**
 * Destroy a GPU texture.
 * @param {GPUTexture} texture
 */
export function destroy_texture(texture) {
    wasm.destroy_texture(texture);
}

/**
 * Append a child node.
 * @param {Element} parent
 * @param {Node} child
 */
export function dom_append_child(parent, child) {
    const ret = wasm.dom_append_child(parent, child);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Clear all children from an element.
 * @param {Element} element
 */
export function dom_clear_children(element) {
    wasm.dom_clear_children(element);
}

/**
 * Create an element with optional namespace.
 * @param {string} tag_name
 * @param {string | null} [namespace]
 * @returns {Element}
 */
export function dom_create_element(tag_name, namespace) {
    const ptr0 = passStringToWasm0(tag_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    var ptr1 = isLikeNone(namespace) ? 0 : passStringToWasm0(namespace, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len1 = WASM_VECTOR_LEN;
    const ret = wasm.dom_create_element(ptr0, len0, ptr1, len1);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a text node.
 * @param {string} text
 * @returns {Text}
 */
export function dom_create_text_node(text) {
    const ptr0 = passStringToWasm0(text, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.dom_create_text_node(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Get the 'checked' property from an input element.
 * @param {HTMLElement} element
 * @returns {boolean}
 */
export function dom_get_input_checked(element) {
    const ret = wasm.dom_get_input_checked(element);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return ret[0] !== 0;
}

/**
 * Get the 'value' property from an input element.
 * @param {HTMLElement} element
 * @returns {string}
 */
export function dom_get_input_value(element) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ret = wasm.dom_get_input_value(element);
        var ptr1 = ret[0];
        var len1 = ret[1];
        if (ret[3]) {
            ptr1 = 0; len1 = 0;
            throw takeFromExternrefTable0(ret[2]);
        }
        deferred2_0 = ptr1;
        deferred2_1 = len1;
        return getStringFromWasm0(ptr1, len1);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Get inner text content.
 * @param {Element} element
 * @returns {string | undefined}
 */
export function dom_get_text_content(element) {
    const ret = wasm.dom_get_text_content(element);
    let v1;
    if (ret[0] !== 0) {
        v1 = getStringFromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
    }
    return v1;
}

/**
 * Insert before a reference node.
 * @param {Element} parent
 * @param {Node} new_node
 * @param {Node | null} [reference_node]
 */
export function dom_insert_before(parent, new_node, reference_node) {
    const ret = wasm.dom_insert_before(parent, new_node, isLikeNone(reference_node) ? 0 : addToExternrefTable0(reference_node));
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Remove a child node.
 * @param {Element} parent
 * @param {Node} child
 */
export function dom_remove_child(parent, child) {
    const ret = wasm.dom_remove_child(parent, child);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Remove a CSS style property from an element.
 * @param {HTMLElement} element
 * @param {string} property
 */
export function dom_remove_style_property(element, property) {
    const ptr0 = passStringToWasm0(property, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.dom_remove_style_property(element, ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Replace a child node.
 * @param {Element} parent
 * @param {Node} new_child
 * @param {Node} old_child
 */
export function dom_replace_child(parent, new_child, old_child) {
    const ret = wasm.dom_replace_child(parent, new_child, old_child);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set a namespaced attribute on an element.
 * Used for SVG attributes like xlink:href.
 * @param {Element} element
 * @param {string | null | undefined} namespace
 * @param {string} name
 * @param {string} value
 */
export function dom_set_attribute_ns(element, namespace, name, value) {
    var ptr0 = isLikeNone(namespace) ? 0 : passStringToWasm0(namespace, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ptr2 = passStringToWasm0(value, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len2 = WASM_VECTOR_LEN;
    const ret = wasm.dom_set_attribute_ns(element, ptr0, len0, ptr1, len1, ptr2, len2);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set the 'checked' property on an input element.
 * @param {HTMLElement} element
 * @param {boolean} checked
 */
export function dom_set_input_checked(element, checked) {
    const ret = wasm.dom_set_input_checked(element, checked);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set the 'disabled' property on an input element.
 * @param {HTMLElement} element
 * @param {boolean} disabled
 */
export function dom_set_input_disabled(element, disabled) {
    const ret = wasm.dom_set_input_disabled(element, disabled);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set the 'value' property on an input element.
 * Uses typed HtmlInputElement API instead of reflection.
 * @param {HTMLElement} element
 * @param {string} value
 */
export function dom_set_input_value(element, value) {
    const ptr0 = passStringToWasm0(value, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.dom_set_input_value(element, ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set a CSS style property on an element.
 * @param {HTMLElement} element
 * @param {string} property
 * @param {string} value
 */
export function dom_set_style_property(element, property, value) {
    const ptr0 = passStringToWasm0(property, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(value, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.dom_set_style_property(element, ptr0, len0, ptr1, len1);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set inner text content (safe — no HTML parsing).
 * @param {Element} element
 * @param {string} text
 */
export function dom_set_text_content(element, text) {
    const ptr0 = passStringToWasm0(text, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    wasm.dom_set_text_content(element, ptr0, len0);
}

/**
 * Draw primitives.
 * @param {GPURenderPassEncoder} pass
 * @param {number} vertex_count
 * @param {number} instance_count
 * @param {number} first_vertex
 * @param {number} first_instance
 */
export function draw(pass, vertex_count, instance_count, first_vertex, first_instance) {
    wasm.draw(pass, vertex_count, instance_count, first_vertex, first_instance);
}

/**
 * Draw indexed primitives.
 * @param {GPURenderPassEncoder} pass
 * @param {number} index_count
 * @param {number} instance_count
 * @param {number} first_index
 * @param {number} base_vertex
 * @param {number} first_instance
 */
export function draw_indexed(pass, index_count, instance_count, first_index, base_vertex, first_instance) {
    wasm.draw_indexed(pass, index_count, instance_count, first_index, base_vertex, first_instance);
}

/**
 * Draw indirect.
 * @param {GPURenderPassEncoder} pass
 * @param {GPUBuffer} buffer
 * @param {number} offset
 */
export function draw_indirect(pass, buffer, offset) {
    wasm.draw_indirect(pass, buffer, offset);
}

/**
 * End a compute pass.
 * @param {GPUComputePassEncoder} pass
 */
export function end_compute_pass(pass) {
    wasm.end_compute_pass(pass);
}

/**
 * End a render pass.
 * @param {GPURenderPassEncoder} pass
 */
export function end_render_pass(pass) {
    wasm.end_render_pass(pass);
}

/**
 * Generate a unique type ID for an event type.
 * This replaces JavaScript Symbols for runtime type safety.
 * @returns {bigint}
 */
export function event_generate_type_id() {
    const ret = wasm.event_generate_type_id();
    return BigInt.asUintN(64, ret);
}

/**
 * Log an event to console for debugging.
 * @param {string | null | undefined} bus_name
 * @param {any} event
 */
export function event_log(bus_name, event) {
    var ptr0 = isLikeNone(bus_name) ? 0 : passStringToWasm0(bus_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    wasm.event_log(ptr0, len0, event);
}

/**
 * Unwrap an event if it matches the expected type.
 * @param {WrappedEvent} wrapped
 * @param {bigint} expected_type_id
 * @returns {any}
 */
export function event_unwrap(wrapped, expected_type_id) {
    _assertClass(wrapped, WrappedEvent);
    const ret = wasm.event_unwrap(wrapped.__wbg_ptr, expected_type_id);
    return ret;
}

/**
 * Wrap an event with a type identifier.
 * @param {bigint} type_id
 * @param {any} payload
 * @returns {WrappedEvent}
 */
export function event_wrap(type_id, payload) {
    const ret = wasm.event_wrap(type_id, payload);
    return WrappedEvent.__wrap(ret);
}

/**
 * Finish command encoder, returning command buffer.
 * @param {GPUCommandEncoder} encoder
 * @returns {GPUCommandBuffer}
 */
export function finish_command_encoder(encoder) {
    const ret = wasm.finish_command_encoder(encoder);
    return ret;
}

/**
 * Check if an element is visible (not display:none, visibility:hidden, or hidden attr).
 * @param {HTMLElement} element
 * @returns {boolean}
 */
export function focus_trap_is_visible(element) {
    const ret = wasm.focus_trap_is_visible(element);
    return ret !== 0;
}

/**
 * Convert a Node to HtmlElement if it is one.
 * Returns None if the node is not an HtmlElement.
 * @param {Node} node
 * @returns {HTMLElement | undefined}
 */
export function focus_trap_node_to_element(node) {
    const ret = wasm.focus_trap_node_to_element(node);
    return ret;
}

/**
 * Referential equality check for DOM nodes.
 * @param {any} a
 * @param {any} b
 * @returns {boolean}
 */
export function focus_trap_ref_eq(a, b) {
    const ret = wasm.focus_trap_ref_eq(a, b);
    return ret !== 0;
}

/**
 * Clear a position watch by ID.
 * @param {number} watch_id
 */
export function geo_clear_watch(watch_id) {
    wasm.geo_clear_watch(watch_id);
}

/**
 * Get current position (one-time).
 * Returns a Promise that resolves to GeoPosition or rejects with GeoError.
 * @param {GeoOptions} options
 * @returns {Promise<GeoPosition>}
 */
export function geo_get_current_position(options) {
    _assertClass(options, GeoOptions);
    const ret = wasm.geo_get_current_position(options.__wbg_ptr);
    return ret;
}

/**
 * Check if Geolocation API is supported.
 * @returns {boolean}
 */
export function geo_is_supported() {
    const ret = wasm.geo_is_supported();
    return ret !== 0;
}

/**
 * Watch a circular geofence for enter/exit events.
 * @param {number} center_lat
 * @param {number} center_lon
 * @param {number} radius_meters
 * @param {Function} on_event
 * @returns {GeofenceHandle}
 */
export function geo_watch_geofence(center_lat, center_lon, radius_meters, on_event) {
    const ret = wasm.geo_watch_geofence(center_lat, center_lon, radius_meters, on_event);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return GeofenceHandle.__wrap(ret[0]);
}

/**
 * Watch position with continuous updates.
 * Returns a handle that can be used to clear the watch.
 * @param {GeoOptions} options
 * @param {Function} on_success
 * @param {Function} on_error
 * @returns {GeoWatchHandle}
 */
export function geo_watch_position(options, on_success, on_error) {
    _assertClass(options, GeoOptions);
    const ret = wasm.geo_watch_position(options.__wbg_ptr, on_success, on_error);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return GeoWatchHandle.__wrap(ret[0]);
}

/**
 * Get the current texture from canvas context.
 * @param {GPUCanvasContext} ctx
 * @returns {GPUTexture}
 */
export function get_current_texture(ctx) {
    const ret = wasm.get_current_texture(ctx);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Get device features as array of strings.
 * @param {GPUDevice} device
 * @returns {Array<any>}
 */
export function get_features(device) {
    const ret = wasm.get_features(device);
    return ret;
}

/**
 * Get device limits.
 * @param {GPUDevice} device
 * @returns {GPUSupportedLimits}
 */
export function get_limits(device) {
    const ret = wasm.get_limits(device);
    return ret;
}

/**
 * Get mapped range from buffer.
 * @param {GPUBuffer} buffer
 * @param {number} offset
 * @param {number} size
 * @returns {ArrayBuffer}
 */
export function get_mapped_range(buffer, offset, size) {
    const ret = wasm.get_mapped_range(buffer, offset, size);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Get preferred canvas format.
 * @returns {string}
 */
export function get_preferred_canvas_format() {
    let deferred2_0;
    let deferred2_1;
    try {
        const ret = wasm.get_preferred_canvas_format();
        var ptr1 = ret[0];
        var len1 = ret[1];
        if (ret[3]) {
            ptr1 = 0; len1 = 0;
            throw takeFromExternrefTable0(ret[2]);
        }
        deferred2_0 = ptr1;
        deferred2_1 = len1;
        return getStringFromWasm0(ptr1, len1);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Get the command queue from a device.
 * @param {GPUDevice} device
 * @returns {GPUQueue}
 */
export function get_queue(device) {
    const ret = wasm.get_queue(device);
    return ret;
}

/**
 * Initialize panic hook for better error messages in browser console.
 * Returns error if logger initialization fails.
 */
export function init() {
    wasm.init();
}

/**
 * Observe an element for intersection changes.
 *
 * # Arguments
 * * `element` - The element to observe
 * * `threshold` - Visibility ratio (0.0 to 1.0) at which to trigger callback
 * * `root_margin` - Margin around the root (CSS margin syntax, e.g., "10px 20px")
 * * `root` - Optional root element to use as viewport (null = browser viewport)
 * * `callback` - Function called when intersection changes
 * @param {Element} element
 * @param {number} threshold
 * @param {string} root_margin
 * @param {Element | null | undefined} root
 * @param {Function} callback
 * @returns {IntersectionHandle}
 */
export function intersection_observe(element, threshold, root_margin, root, callback) {
    const ptr0 = passStringToWasm0(root_margin, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.intersection_observe(element, threshold, ptr0, len0, isLikeNone(root) ? 0 : addToExternrefTable0(root), callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return IntersectionHandle.__wrap(ret[0]);
}

/**
 * Observe an element once (disconnect after first intersection).
 *
 * # Arguments
 * * `element` - The element to observe
 * * `threshold` - Visibility ratio (0.0 to 1.0) at which to trigger callback
 * * `root_margin` - Margin around the root (CSS margin syntax, e.g., "10px 20px")
 * * `root` - Optional root element to use as viewport (null = browser viewport)
 * * `callback` - Function called when element first intersects, then observer disconnects
 * @param {Element} element
 * @param {number} threshold
 * @param {string} root_margin
 * @param {Element | null | undefined} root
 * @param {Function} callback
 * @returns {IntersectionHandle}
 */
export function intersection_observe_once(element, threshold, root_margin, root, callback) {
    const ptr0 = passStringToWasm0(root_margin, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.intersection_observe_once(element, threshold, ptr0, len0, isLikeNone(root) ? 0 : addToExternrefTable0(root), callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return IntersectionHandle.__wrap(ret[0]);
}

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
 * @param {string} locale
 * @param {number} amount
 * @param {string} currency_symbol
 * @returns {string}
 */
export function intl_format_currency(locale, amount, currency_symbol) {
    let deferred3_0;
    let deferred3_1;
    try {
        const ptr0 = passStringToWasm0(locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(currency_symbol, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.intl_format_currency(ptr0, len0, amount, ptr1, len1);
        deferred3_0 = ret[0];
        deferred3_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
    }
}

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
 * @param {string} locale
 * @param {number} value
 * @param {number} decimal_places
 * @returns {string}
 */
export function intl_format_decimal(locale, value, decimal_places) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.intl_format_decimal(ptr0, len0, value, decimal_places);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Format an integer according to locale.
 *
 * # Arguments
 * * `locale` - BCP 47 language tag (e.g., "en-US", "de-DE")
 * * `value` - Integer to format
 *
 * # Returns
 * Formatted string (e.g., "1,234" for en-US)
 * @param {string} locale
 * @param {bigint} value
 * @returns {string}
 */
export function intl_format_integer(locale, value) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.intl_format_integer(ptr0, len0, value);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

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
 * @param {number} value
 * @param {RelativeTimeUnit} unit
 * @param {string} _locale
 * @returns {string}
 */
export function intl_format_relative_time(value, unit, _locale) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(_locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.intl_format_relative_time(value, unit, ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Get the language subtag from a locale.
 * Returns empty string if invalid.
 * @param {string} locale
 * @returns {string}
 */
export function intl_get_language(locale) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.intl_get_language(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Get the region subtag from a locale.
 * Returns empty string if not present or invalid.
 * @param {string} locale
 * @returns {string}
 */
export function intl_get_region(locale) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.intl_get_region(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Check if a locale string is valid BCP 47.
 * @param {string} locale
 * @returns {boolean}
 */
export function intl_is_valid_locale(locale) {
    const ptr0 = passStringToWasm0(locale, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.intl_is_valid_locale(ptr0, len0);
    return ret !== 0;
}

/**
 * Check if WebGPU is supported.
 * @returns {boolean}
 */
export function is_webgpu_supported() {
    const ret = wasm.is_webgpu_supported();
    return ret !== 0;
}

/**
 * Check if an input element is currently focused.
 * Returns true if focus is on input, textarea, select, or contenteditable.
 * @returns {boolean}
 */
export function keyboard_is_input_focused() {
    const ret = wasm.keyboard_is_input_focused();
    return ret !== 0;
}

/**
 * Detect macOS/iOS platform for Cmd key handling.
 * @returns {boolean}
 */
export function keyboard_is_mac_platform() {
    const ret = wasm.keyboard_is_mac_platform();
    return ret !== 0;
}

/**
 * WASM-exported shortcut match check.
 * Takes flattened parameters for easy FFI.
 * @param {string} input_key
 * @param {string} input_code
 * @param {boolean} input_ctrl
 * @param {boolean} input_alt
 * @param {boolean} input_shift
 * @param {boolean} input_meta
 * @param {string} def_key
 * @param {boolean} def_ctrl
 * @param {boolean} def_alt
 * @param {boolean} def_shift
 * @param {boolean} def_meta
 * @returns {boolean}
 */
export function keyboard_shortcut_matches(input_key, input_code, input_ctrl, input_alt, input_shift, input_meta, def_key, def_ctrl, def_alt, def_shift, def_meta) {
    const ptr0 = passStringToWasm0(input_key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(input_code, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ptr2 = passStringToWasm0(def_key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len2 = WASM_VECTOR_LEN;
    const ret = wasm.keyboard_shortcut_matches(ptr0, len0, ptr1, len1, input_ctrl, input_alt, input_shift, input_meta, ptr2, len2, def_ctrl, def_alt, def_shift, def_meta);
    return ret !== 0;
}

/**
 * Animate line drawing from start to end using stroke-dasharray.
 *
 * # Arguments
 * * `container_id` - Container element ID
 * * `duration_ms` - Animation duration in milliseconds
 * * `easing` - Easing function (uses CSS transition)
 * @param {string} container_id
 * @param {number} duration_ms
 */
export function line_animate(container_id, duration_ms) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_animate(ptr0, len0, duration_ms);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Clear all dot highlights.
 * @param {string} container_id
 * @param {number} original_radius
 */
export function line_clear_dot_highlights(container_id, original_radius) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_clear_dot_highlights(ptr0, len0, original_radius);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Get total length of an SVG path.
 * @param {string} path_id
 * @returns {number}
 */
export function line_get_path_length(path_id) {
    const ptr0 = passStringToWasm0(path_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_get_path_length(ptr0, len0);
    return ret;
}

/**
 * Get point at length along path.
 * @param {string} path_id
 * @param {number} length
 * @returns {TooltipPosition}
 */
export function line_get_point_at_length(path_id, length) {
    const ptr0 = passStringToWasm0(path_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_get_point_at_length(ptr0, len0, length);
    return TooltipPosition.__wrap(ret);
}

/**
 * Hide tooltip.
 * @param {string} container_id
 */
export function line_hide_tooltip(container_id) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_hide_tooltip(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Highlight a data point dot.
 * @param {string} container_id
 * @param {number} index
 */
export function line_highlight_dot(container_id, index) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_highlight_dot(ptr0, len0, index);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Initialize crosshair for line chart.
 *
 * # Arguments
 * * `container_id` - Container element ID
 * * `padding` - Chart padding
 * * `on_move` - Callback with cursor position
 * @param {string} container_id
 * @param {ChartPadding} padding
 * @param {Function} on_move
 * @returns {LineCrosshairHandle}
 */
export function line_init_crosshair(container_id, padding, on_move) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    _assertClass(padding, ChartPadding);
    const ret = wasm.line_init_crosshair(ptr0, len0, padding.__wbg_ptr, on_move);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return LineCrosshairHandle.__wrap(ret[0]);
}

/**
 * Reset line animation to initial state.
 * @param {string} container_id
 */
export function line_reset(container_id) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.line_reset(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Show tooltip at position.
 * @param {string} container_id
 * @param {number} x
 * @param {number} y
 * @param {string} content
 */
export function line_show_tooltip(container_id, x, y, content) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(content, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.line_show_tooltip(ptr0, len0, x, y, ptr1, len1);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Map a buffer asynchronously.
 * @param {GPUBuffer} buffer
 * @param {number} mode
 * @param {number} offset
 * @param {number} size
 * @returns {any}
 */
export function map_buffer_async(buffer, mode, offset, size) {
    const ret = wasm.map_buffer_async(buffer, mode, offset, size);
    return ret;
}

/**
 * Get the current breakpoint based on viewport width.
 * @returns {Breakpoint}
 */
export function mediaquery_current_breakpoint() {
    const ret = wasm.mediaquery_current_breakpoint();
    return ret;
}

/**
 * Check if viewport is desktop (>= 1024px).
 * @returns {boolean}
 */
export function mediaquery_is_desktop() {
    const ret = wasm.mediaquery_is_desktop();
    return ret !== 0;
}

/**
 * Check if display is high DPI (retina, >= 2x pixel ratio).
 * @returns {boolean}
 */
export function mediaquery_is_high_dpi() {
    const ret = wasm.mediaquery_is_high_dpi();
    return ret !== 0;
}

/**
 * Check if device is in landscape orientation.
 * @returns {boolean}
 */
export function mediaquery_is_landscape() {
    const ret = wasm.mediaquery_is_landscape();
    return ret !== 0;
}

/**
 * Check if viewport is large desktop (>= 1280px).
 * @returns {boolean}
 */
export function mediaquery_is_large_desktop() {
    const ret = wasm.mediaquery_is_large_desktop();
    return ret !== 0;
}

/**
 * Check if viewport is mobile (< 768px).
 * @returns {boolean}
 */
export function mediaquery_is_mobile() {
    const ret = wasm.mediaquery_is_mobile();
    return ret !== 0;
}

/**
 * Check if device is in portrait orientation.
 * @returns {boolean}
 */
export function mediaquery_is_portrait() {
    const ret = wasm.mediaquery_is_portrait();
    return ret !== 0;
}

/**
 * Check if currently in print mode.
 * @returns {boolean}
 */
export function mediaquery_is_print() {
    const ret = wasm.mediaquery_is_print();
    return ret !== 0;
}

/**
 * Check if viewport is tablet (>= 768px and < 1024px).
 * @returns {boolean}
 */
export function mediaquery_is_tablet() {
    const ret = wasm.mediaquery_is_tablet();
    return ret !== 0;
}

/**
 * Check if device supports touch input.
 *
 * Uses hover:none + pointer:coarse heuristic.
 * @returns {boolean}
 */
export function mediaquery_is_touch() {
    const ret = wasm.mediaquery_is_touch();
    return ret !== 0;
}

/**
 * Check if a media query currently matches.
 *
 * Returns `false` if window or matchMedia is unavailable (SSR safety).
 * @param {string} query
 * @returns {boolean}
 */
export function mediaquery_matches(query) {
    const ptr0 = passStringToWasm0(query, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.mediaquery_matches(ptr0, len0);
    return ret !== 0;
}

/**
 * Subscribe to breakpoint changes.
 *
 * Callback receives the new Breakpoint value (0-3).
 * @param {Function} callback
 * @returns {BreakpointHandle}
 */
export function mediaquery_on_breakpoint_change(callback) {
    const ret = wasm.mediaquery_on_breakpoint_change(callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return BreakpointHandle.__wrap(ret[0]);
}

/**
 * Subscribe to media query changes.
 *
 * Returns a handle that unsubscribes when dropped.
 * Callback receives `true` when query matches, `false` when it doesn't.
 * @param {string} query
 * @param {Function} callback
 * @returns {MediaQueryHandle}
 */
export function mediaquery_on_change(query, callback) {
    const ptr0 = passStringToWasm0(query, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.mediaquery_on_change(ptr0, len0, callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return MediaQueryHandle.__wrap(ret[0]);
}

/**
 * Subscribe to color scheme changes.
 *
 * Callback receives `true` for dark mode, `false` for light mode.
 * @param {Function} callback
 * @returns {MediaQueryHandle}
 */
export function mediaquery_on_color_scheme_change(callback) {
    const ret = wasm.mediaquery_on_color_scheme_change(callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return MediaQueryHandle.__wrap(ret[0]);
}

/**
 * Subscribe to orientation changes.
 *
 * Callback receives `true` for portrait, `false` for landscape.
 * @param {Function} callback
 * @returns {MediaQueryHandle}
 */
export function mediaquery_on_orientation_change(callback) {
    const ret = wasm.mediaquery_on_orientation_change(callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return MediaQueryHandle.__wrap(ret[0]);
}

/**
 * Get current device orientation.
 * @returns {Orientation}
 */
export function mediaquery_orientation() {
    const ret = wasm.mediaquery_orientation();
    return ret;
}

/**
 * Check if user prefers high contrast.
 * @returns {boolean}
 */
export function mediaquery_prefers_contrast() {
    const ret = wasm.mediaquery_prefers_contrast();
    return ret !== 0;
}

/**
 * Check if user prefers dark color scheme.
 * @returns {boolean}
 */
export function mediaquery_prefers_dark() {
    const ret = wasm.mediaquery_prefers_dark();
    return ret !== 0;
}

/**
 * Check if user prefers light color scheme.
 * @returns {boolean}
 */
export function mediaquery_prefers_light() {
    const ret = wasm.mediaquery_prefers_light();
    return ret !== 0;
}

/**
 * Check if user prefers reduced motion.
 *
 * Important for accessibility — disable animations when true.
 * @returns {boolean}
 */
export function mediaquery_prefers_reduced_motion() {
    const ret = wasm.mediaquery_prefers_reduced_motion();
    return ret !== 0;
}

/**
 * Check if user prefers reduced transparency.
 * @returns {boolean}
 */
export function mediaquery_prefers_reduced_transparency() {
    const ret = wasm.mediaquery_prefers_reduced_transparency();
    return ret !== 0;
}

/**
 * Set a class on the body element.
 *
 * Useful for theme switching, modal open states, etc.
 * @param {string} class_name
 */
export function meta_addBodyClass(class_name) {
    const ptr0 = passStringToWasm0(class_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_addBodyClass(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Add a link tag.
 *
 * Corresponds to: `addLinkImpl` in `Hydrogen.Head.Meta`
 *
 * Parameters:
 * - rel: "preload", "prefetch", "preconnect", "dns-prefetch", "canonical", etc.
 * - href: URL or resource path
 * - as_type: For preload only ("script", "style", "image", "font", "fetch")
 * @param {string} rel
 * @param {string} href
 * @param {string} as_type
 */
export function meta_addLink(rel, href, as_type) {
    const ptr0 = passStringToWasm0(rel, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(href, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ptr2 = passStringToWasm0(as_type, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len2 = WASM_VECTOR_LEN;
    const ret = wasm.meta_addLink(ptr0, len0, ptr1, len1, ptr2, len2);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Get a data attribute from the body.
 * @param {string} key
 * @returns {string | undefined}
 */
export function meta_getBodyData(key) {
    const ptr0 = passStringToWasm0(key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_getBodyData(ptr0, len0);
    if (ret[3]) {
        throw takeFromExternrefTable0(ret[2]);
    }
    let v2;
    if (ret[0] !== 0) {
        v2 = getStringFromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
    }
    return v2;
}

/**
 * Get meta tag content.
 *
 * Corresponds to: `getMetaImpl` in `Hydrogen.Head.Meta`
 *
 * Returns null if not found (PureScript handles as Nothing).
 * @param {string} name
 * @returns {string | undefined}
 */
export function meta_getMeta(name) {
    const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_getMeta(ptr0, len0);
    if (ret[3]) {
        throw takeFromExternrefTable0(ret[2]);
    }
    let v2;
    if (ret[0] !== 0) {
        v2 = getStringFromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
    }
    return v2;
}

/**
 * Get current document title.
 *
 * Corresponds to: `getTitleImpl` in `Hydrogen.Head.Meta`
 * @returns {string}
 */
export function meta_getTitle() {
    let deferred2_0;
    let deferred2_1;
    try {
        const ret = wasm.meta_getTitle();
        var ptr1 = ret[0];
        var len1 = ret[1];
        if (ret[3]) {
            ptr1 = 0; len1 = 0;
            throw takeFromExternrefTable0(ret[2]);
        }
        deferred2_0 = ptr1;
        deferred2_1 = len1;
        return getStringFromWasm0(ptr1, len1);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Check if body has a class.
 * @param {string} class_name
 * @returns {boolean}
 */
export function meta_hasBodyClass(class_name) {
    const ptr0 = passStringToWasm0(class_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_hasBodyClass(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return ret[0] !== 0;
}

/**
 * Query a single element by CSS selector.
 *
 * Returns the first matching element, or None if not found.
 * @param {string} selector
 * @returns {Element | undefined}
 */
export function meta_querySelector(selector) {
    const ptr0 = passStringToWasm0(selector, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_querySelector(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Remove an attribute from an element found by selector.
 * @param {string} selector
 * @param {string} attr_name
 * @returns {boolean}
 */
export function meta_removeAttributeBySelector(selector, attr_name) {
    const ptr0 = passStringToWasm0(selector, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(attr_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.meta_removeAttributeBySelector(ptr0, len0, ptr1, len1);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return ret[0] !== 0;
}

/**
 * Remove a class from the body element.
 * @param {string} class_name
 */
export function meta_removeBodyClass(class_name) {
    const ptr0 = passStringToWasm0(class_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_removeBodyClass(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Remove a link tag by rel.
 *
 * Corresponds to: `removeLinkImpl` in `Hydrogen.Head.Meta`
 *
 * Removes ALL link tags with the given rel attribute.
 * @param {string} rel
 */
export function meta_removeLink(rel) {
    const ptr0 = passStringToWasm0(rel, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_removeLink(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Remove a meta tag.
 *
 * Corresponds to: `removeMetaImpl` in `Hydrogen.Head.Meta`
 * @param {string} name
 */
export function meta_removeMeta(name) {
    const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_removeMeta(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set an attribute on an element found by selector.
 * @param {string} selector
 * @param {string} attr_name
 * @param {string} attr_value
 * @returns {boolean}
 */
export function meta_setAttributeBySelector(selector, attr_name, attr_value) {
    const ptr0 = passStringToWasm0(selector, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(attr_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ptr2 = passStringToWasm0(attr_value, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len2 = WASM_VECTOR_LEN;
    const ret = wasm.meta_setAttributeBySelector(ptr0, len0, ptr1, len1, ptr2, len2);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return ret[0] !== 0;
}

/**
 * Set a data attribute on the body.
 *
 * Useful for storing state like theme, user preferences, etc.
 * @param {string} key
 * @param {string} value
 */
export function meta_setBodyData(key, value) {
    const ptr0 = passStringToWasm0(key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(value, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.meta_setBodyData(ptr0, len0, ptr1, len1);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set favicon.
 *
 * Corresponds to: `setFaviconImpl` in `Hydrogen.Head.Meta`
 *
 * Removes existing favicon links and adds new one.
 * @param {string} href
 */
export function meta_setFavicon(href) {
    const ptr0 = passStringToWasm0(href, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_setFavicon(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set a meta tag (creates or updates).
 *
 * Corresponds to: `setMetaImpl` in `Hydrogen.Head.Meta`
 *
 * For Open Graph tags (og:*), uses property attribute.
 * For others, uses name attribute.
 * @param {string} name
 * @param {string} content
 */
export function meta_setMeta(name, content) {
    const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(content, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.meta_setMeta(ptr0, len0, ptr1, len1);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set document title.
 *
 * Corresponds to: `setTitleImpl` in `Hydrogen.Head.Meta`
 * @param {string} title
 */
export function meta_setTitle(title) {
    const ptr0 = passStringToWasm0(title, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_setTitle(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Toggle a class on the body element.
 * @param {string} class_name
 * @returns {boolean}
 */
export function meta_toggleBodyClass(class_name) {
    const ptr0 = passStringToWasm0(class_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.meta_toggleBodyClass(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return ret[0] !== 0;
}

/**
 * Register callback for device lost.
 * Returns the promise for chaining.
 * @param {GPUDevice} device
 * @param {Function} callback
 * @returns {any}
 */
export function on_device_lost(device, callback) {
    const ret = wasm.on_device_lost(device, callback);
    return ret;
}

/**
 * Register callback for uncaptured errors.
 * Returns error if event listener registration fails.
 * @param {GPUDevice} device
 * @param {Function} callback
 */
export function on_uncaptured_error(device, callback) {
    const ret = wasm.on_uncaptured_error(device, callback);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Animate slices with rotation effect.
 * @param {string} container_id
 * @param {number} duration_ms
 */
export function pie_animate_rotate(container_id, duration_ms) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_animate_rotate(ptr0, len0, duration_ms);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Animate pie slices appearing with scale effect.
 * @param {string} container_id
 * @param {number} duration_ms
 */
export function pie_animate_slices(container_id, duration_ms) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_animate_slices(ptr0, len0, duration_ms);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Clear all slice highlights.
 * @param {string} container_id
 */
export function pie_clear_highlights(container_id) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_clear_highlights(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Explode a slice outward from center.
 * @param {string} container_id
 * @param {number} index
 * @param {number} distance
 */
export function pie_explode_slice(container_id, index, distance) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_explode_slice(ptr0, len0, index, distance);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Calculate slice angle from mouse position (radians).
 * @param {string} container_id
 * @param {number} mouse_x
 * @param {number} mouse_y
 * @returns {number}
 */
export function pie_get_angle_from_mouse(container_id, mouse_x, mouse_y) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_get_angle_from_mouse(ptr0, len0, mouse_x, mouse_y);
    return ret;
}

/**
 * Highlight a slice on hover.
 * @param {string} container_id
 * @param {number} index
 */
export function pie_highlight_slice(container_id, index) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_highlight_slice(ptr0, len0, index);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Initialize click-to-explode behavior.
 * @param {string} container_id
 * @param {number} distance
 * @param {Function} on_click
 * @returns {PieExplodeHandle}
 */
export function pie_init_explode_on_click(container_id, distance, on_click) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_init_explode_on_click(ptr0, len0, distance, on_click);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return PieExplodeHandle.__wrap(ret[0]);
}

/**
 * Initialize hover effects.
 * @param {string} container_id
 * @returns {PieHoverHandle}
 */
export function pie_init_hover_effects(container_id) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_init_hover_effects(ptr0, len0);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return PieHoverHandle.__wrap(ret[0]);
}

/**
 * Initialize tooltips for pie chart.
 * @param {string} container_id
 * @param {PieSliceData[]} data
 * @returns {PieTooltipHandle}
 */
export function pie_init_tooltips(container_id, data) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passArrayJsValueToWasm0(data, wasm.__wbindgen_malloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.pie_init_tooltips(ptr0, len0, ptr1, len1);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return PieTooltipHandle.__wrap(ret[0]);
}

/**
 * Reset all exploded slices.
 * @param {string} container_id
 */
export function pie_reset_explode(container_id) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_reset_explode(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Reset slice animation.
 * @param {string} container_id
 */
export function pie_reset_slices(container_id) {
    const ptr0 = passStringToWasm0(container_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.pie_reset_slices(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Request a GPU adapter.
 * Returns a Promise that resolves to GpuAdapter or rejects with error string.
 * @param {string | null} [power_preference]
 * @returns {any}
 */
export function request_adapter(power_preference) {
    var ptr0 = isLikeNone(power_preference) ? 0 : passStringToWasm0(power_preference, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    const ret = wasm.request_adapter(ptr0, len0);
    return ret;
}

/**
 * Request a GPU device from an adapter.
 * Returns a Promise that resolves to GpuDevice.
 * @param {GPUAdapter} adapter
 * @returns {any}
 */
export function request_device(adapter) {
    const ret = wasm.request_device(adapter);
    return ret;
}

/**
 * Navigate back in history.
 * SIGIL opcode: 0xD4 (ROUTE_BACK)
 */
export function router_back() {
    const ret = wasm.router_back();
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Navigate forward in history.
 * SIGIL opcode: 0xD5 (ROUTE_FORWARD)
 */
export function router_forward() {
    const ret = wasm.router_forward();
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Get the current hostname.
 * @returns {string}
 */
export function router_get_hostname() {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.router_get_hostname();
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Get the current origin.
 * @returns {string}
 */
export function router_get_origin() {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.router_get_origin();
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Get the current pathname.
 * @returns {string}
 */
export function router_get_pathname() {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.router_get_pathname();
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Intercept all internal link clicks for SPA navigation.
 * @param {Function} callback
 * @returns {LinkInterceptHandle}
 */
export function router_intercept_links(callback) {
    const ret = wasm.router_intercept_links(callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return LinkInterceptHandle.__wrap(ret[0]);
}

/**
 * Subscribe to route changes (both popstate and programmatic).
 * @param {Function} callback
 * @returns {RouteChangeHandle}
 */
export function router_on_route_change(callback) {
    const ret = wasm.router_on_route_change(callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return RouteChangeHandle.__wrap(ret[0]);
}

/**
 * Push a new state to history.
 * @param {string} path
 */
export function router_push_state(path) {
    const ptr0 = passStringToWasm0(path, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.router_push_state(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Replace the current state in history.
 * @param {string} path
 */
export function router_replace_state(path) {
    const ptr0 = passStringToWasm0(path, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.router_replace_state(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set a bind group.
 * @param {GPURenderPassEncoder} pass
 * @param {number} index
 * @param {any} bind_group
 */
export function set_bind_group(pass, index, bind_group) {
    wasm.set_bind_group(pass, index, bind_group);
}

/**
 * Set the index buffer.
 * @param {GPURenderPassEncoder} pass
 * @param {GPUBuffer} buffer
 * @param {string} format
 * @param {number} offset
 * @param {number} size
 */
export function set_index_buffer(pass, buffer, format, offset, size) {
    const ptr0 = passStringToWasm0(format, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    wasm.set_index_buffer(pass, buffer, ptr0, len0, offset, size);
}

/**
 * Set the render pipeline.
 * @param {GPURenderPassEncoder} pass
 * @param {GPURenderPipeline} pipeline
 */
export function set_pipeline(pass, pipeline) {
    wasm.set_pipeline(pass, pipeline);
}

/**
 * Set scissor rect.
 * @param {GPURenderPassEncoder} pass
 * @param {number} x
 * @param {number} y
 * @param {number} width
 * @param {number} height
 */
export function set_scissor_rect(pass, x, y, width, height) {
    wasm.set_scissor_rect(pass, x, y, width, height);
}

/**
 * Set a vertex buffer.
 * @param {GPURenderPassEncoder} pass
 * @param {number} slot
 * @param {GPUBuffer} buffer
 * @param {number} offset
 * @param {number} size
 */
export function set_vertex_buffer(pass, slot, buffer, offset, size) {
    wasm.set_vertex_buffer(pass, slot, buffer, offset, size);
}

/**
 * Set viewport.
 * @param {GPURenderPassEncoder} pass
 * @param {number} x
 * @param {number} y
 * @param {number} width
 * @param {number} height
 * @param {number} min_depth
 * @param {number} max_depth
 */
export function set_viewport(pass, x, y, width, height, min_depth, max_depth) {
    wasm.set_viewport(pass, x, y, width, height, min_depth, max_depth);
}

/**
 * Add event listener for named events.
 * @param {EventSource} source
 * @param {string} event_type
 * @param {Function} callback
 * @returns {any}
 */
export function sse_add_event_listener(source, event_type, callback) {
    const ptr0 = passStringToWasm0(event_type, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.sse_add_event_listener(source, ptr0, len0, callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Close the EventSource connection.
 * @param {EventSource} source
 */
export function sse_close(source) {
    wasm.sse_close(source);
}

/**
 * Create a new EventSource connection.
 * @param {string} url
 * @param {boolean} with_credentials
 * @returns {EventSource}
 */
export function sse_new(url, with_credentials) {
    const ptr0 = passStringToWasm0(url, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.sse_new(ptr0, len0, with_credentials);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Set onerror handler.
 * @param {EventSource} source
 * @param {Function} callback
 * @returns {any}
 */
export function sse_on_error(source, callback) {
    const ret = wasm.sse_on_error(source, callback);
    return ret;
}

/**
 * Set onmessage handler (for unnamed events).
 * @param {EventSource} source
 * @param {Function} callback
 * @returns {any}
 */
export function sse_on_message(source, callback) {
    const ret = wasm.sse_on_message(source, callback);
    return ret;
}

/**
 * Set onopen handler.
 * @param {EventSource} source
 * @param {Function} callback
 * @returns {any}
 */
export function sse_on_open(source, callback) {
    const ret = wasm.sse_on_open(source, callback);
    return ret;
}

/**
 * Get ready state (0=CONNECTING, 1=OPEN, 2=CLOSED).
 * @param {EventSource} source
 * @returns {number}
 */
export function sse_ready_state(source) {
    const ret = wasm.sse_ready_state(source);
    return ret;
}

/**
 * Get the URL.
 * @param {EventSource} source
 * @returns {string}
 */
export function sse_url(source) {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.sse_url(source);
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Clear all items from localStorage.
 */
export function storage_clear() {
    const ret = wasm.storage_clear();
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Get an item from localStorage. Returns empty string if not found or error.
 * @param {string} key
 * @returns {string | undefined}
 */
export function storage_get_item(key) {
    const ptr0 = passStringToWasm0(key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.storage_get_item(ptr0, len0);
    let v2;
    if (ret[0] !== 0) {
        v2 = getStringFromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
    }
    return v2;
}

/**
 * Get all keys from localStorage.
 * @returns {string[]}
 */
export function storage_keys() {
    const ret = wasm.storage_keys();
    var v1 = getArrayJsValueFromWasm0(ret[0], ret[1]).slice();
    wasm.__wbindgen_free(ret[0], ret[1] * 4, 4);
    return v1;
}

/**
 * Get the number of items in localStorage.
 * @returns {number}
 */
export function storage_length() {
    const ret = wasm.storage_length();
    return ret >>> 0;
}

/**
 * Subscribe to all storage changes.
 * @param {Function} callback
 * @returns {StorageChangeHandle}
 */
export function storage_on_any_change(callback) {
    const ret = wasm.storage_on_any_change(callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return StorageChangeHandle.__wrap(ret[0]);
}

/**
 * Subscribe to storage changes for a specific key.
 * Returns a handle that unsubscribes when dropped.
 * @param {string} key
 * @param {Function} callback
 * @returns {StorageChangeHandle}
 */
export function storage_on_change(key, callback) {
    const ptr0 = passStringToWasm0(key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.storage_on_change(ptr0, len0, callback);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return StorageChangeHandle.__wrap(ret[0]);
}

/**
 * Remove an item from localStorage.
 * @param {string} key
 */
export function storage_remove_item(key) {
    const ptr0 = passStringToWasm0(key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.storage_remove_item(ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Set an item in localStorage.
 * @param {string} key
 * @param {string} value
 */
export function storage_set_item(key, value) {
    const ptr0 = passStringToWasm0(key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(value, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.storage_set_item(ptr0, len0, ptr1, len1);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Submit command buffers to the queue.
 * @param {GPUQueue} queue
 * @param {Array<any>} command_buffers
 */
export function submit(queue, command_buffers) {
    wasm.submit(queue, command_buffers);
}

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
 * @param {number} wait_ms
 * @param {boolean} leading
 * @param {boolean} trailing
 * @param {Function} callback
 * @returns {any}
 */
export function throttleImpl(wait_ms, leading, trailing, callback) {
    const ret = wasm.throttleImpl(wait_ms, leading, trailing, callback);
    return ret;
}

/**
 * Unmap a buffer.
 * @param {GPUBuffer} buffer
 */
export function unmap_buffer(buffer) {
    wasm.unmap_buffer(buffer);
}

/**
 * Write data to a buffer via queue.
 * @param {GPUQueue} queue
 * @param {GPUBuffer} buffer
 * @param {number} buffer_offset
 * @param {Uint8Array} data
 * @param {number} data_offset
 * @param {number} size
 */
export function write_buffer(queue, buffer, buffer_offset, data, data_offset, size) {
    const ret = wasm.write_buffer(queue, buffer, buffer_offset, data, data_offset, size);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Write data to a texture via queue.
 * @param {GPUQueue} queue
 * @param {object} dest
 * @param {Uint8Array} data
 * @param {object} data_layout
 * @param {object} size
 */
export function write_texture(queue, dest, data, data_layout, size) {
    const ret = wasm.write_texture(queue, dest, data, data_layout, size);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Close the connection.
 * @param {WebSocket} ws
 */
export function ws_close(ws) {
    const ret = wasm.ws_close(ws);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Close with code and reason.
 * @param {WebSocket} ws
 * @param {number} code
 * @param {string} reason
 */
export function ws_close_with_code(ws, code, reason) {
    const ptr0 = passStringToWasm0(reason, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.ws_close_with_code(ws, code, ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Create a new WebSocket connection.
 * @param {string} url
 * @param {string[]} protocols
 * @returns {WebSocket}
 */
export function ws_new(url, protocols) {
    const ptr0 = passStringToWasm0(url, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passArrayJsValueToWasm0(protocols, wasm.__wbindgen_malloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.ws_new(ptr0, len0, ptr1, len1);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Create a new WebSocket with a single protocol.
 * @param {string} url
 * @param {string} protocol
 * @returns {WebSocket}
 */
export function ws_new_with_protocol(url, protocol) {
    const ptr0 = passStringToWasm0(url, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ptr1 = passStringToWasm0(protocol, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len1 = WASM_VECTOR_LEN;
    const ret = wasm.ws_new_with_protocol(ptr0, len0, ptr1, len1);
    if (ret[2]) {
        throw takeFromExternrefTable0(ret[1]);
    }
    return takeFromExternrefTable0(ret[0]);
}

/**
 * Set onclose handler.
 * @param {WebSocket} ws
 * @param {Function} callback
 * @returns {any}
 */
export function ws_on_close(ws, callback) {
    const ret = wasm.ws_on_close(ws, callback);
    return ret;
}

/**
 * Set onerror handler.
 * @param {WebSocket} ws
 * @param {Function} callback
 * @returns {any}
 */
export function ws_on_error(ws, callback) {
    const ret = wasm.ws_on_error(ws, callback);
    return ret;
}

/**
 * Set onmessage handler.
 * @param {WebSocket} ws
 * @param {Function} callback
 * @returns {any}
 */
export function ws_on_message(ws, callback) {
    const ret = wasm.ws_on_message(ws, callback);
    return ret;
}

/**
 * Set onopen handler.
 * @param {WebSocket} ws
 * @param {Function} callback
 * @returns {any}
 */
export function ws_on_open(ws, callback) {
    const ret = wasm.ws_on_open(ws, callback);
    return ret;
}

/**
 * Get ready state (0=CONNECTING, 1=OPEN, 2=CLOSING, 3=CLOSED).
 * @param {WebSocket} ws
 * @returns {number}
 */
export function ws_ready_state(ws) {
    const ret = wasm.ws_ready_state(ws);
    return ret;
}

/**
 * Send a text message.
 * @param {WebSocket} ws
 * @param {string} data
 */
export function ws_send(ws, data) {
    const ptr0 = passStringToWasm0(data, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.ws_send(ws, ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

/**
 * Send binary data.
 * @param {WebSocket} ws
 * @param {Uint8Array} data
 */
export function ws_send_binary(ws, data) {
    const ptr0 = passArray8ToWasm0(data, wasm.__wbindgen_malloc);
    const len0 = WASM_VECTOR_LEN;
    const ret = wasm.ws_send_binary(ws, ptr0, len0);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

function __wbg_get_imports() {
    const import0 = {
        __proto__: null,
        __wbg___wbindgen_debug_string_5398f5bb970e0daa: function(arg0, arg1) {
            const ret = debugString(arg1);
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg___wbindgen_is_function_3c846841762788c1: function(arg0) {
            const ret = typeof(arg0) === 'function';
            return ret;
        },
        __wbg___wbindgen_is_null_0b605fc6b167c56f: function(arg0) {
            const ret = arg0 === null;
            return ret;
        },
        __wbg___wbindgen_is_undefined_52709e72fb9f179c: function(arg0) {
            const ret = arg0 === undefined;
            return ret;
        },
        __wbg___wbindgen_jsval_eq_ee31bfad3e536463: function(arg0, arg1) {
            const ret = arg0 === arg1;
            return ret;
        },
        __wbg___wbindgen_rethrow_5d3a9250cec92549: function(arg0) {
            throw arg0;
        },
        __wbg___wbindgen_string_get_395e606bd0ee4427: function(arg0, arg1) {
            const obj = arg1;
            const ret = typeof(obj) === 'string' ? obj : undefined;
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg___wbindgen_throw_6ddd609b62940d55: function(arg0, arg1) {
            throw new Error(getStringFromWasm0(arg0, arg1));
        },
        __wbg__wbg_cb_unref_6b5b6b8576d35cb1: function(arg0) {
            arg0._wbg_cb_unref();
        },
        __wbg_accuracy_f4208e1e65f1cf4e: function(arg0) {
            const ret = arg0.accuracy;
            return ret;
        },
        __wbg_activeElement_c2981ba623ac16d9: function(arg0) {
            const ret = arg0.activeElement;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_addEventListener_2d985aa8a656f6dc: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            arg0.addEventListener(getStringFromWasm0(arg1, arg2), arg3);
        }, arguments); },
        __wbg_addEventListener_97281b0177d72360: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            arg0.addEventListener(getStringFromWasm0(arg1, arg2), arg3, arg4);
        }, arguments); },
        __wbg_add_6c0a5a17e83d73e8: function() { return handleError(function (arg0, arg1, arg2) {
            arg0.add(getStringFromWasm0(arg1, arg2));
        }, arguments); },
        __wbg_altitudeAccuracy_ecb77410908264f9: function(arg0, arg1) {
            const ret = arg1.altitudeAccuracy;
            getDataViewMemory0().setFloat64(arg0 + 8 * 1, isLikeNone(ret) ? 0 : ret, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, !isLikeNone(ret), true);
        },
        __wbg_altitude_7cb71493bbdebfbd: function(arg0, arg1) {
            const ret = arg1.altitude;
            getDataViewMemory0().setFloat64(arg0 + 8 * 1, isLikeNone(ret) ? 0 : ret, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, !isLikeNone(ret), true);
        },
        __wbg_appendChild_8cb157b6ec5612a6: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.appendChild(arg1);
            return ret;
        }, arguments); },
        __wbg_back_8b9d6d6d5d076870: function() { return handleError(function (arg0) {
            arg0.back();
        }, arguments); },
        __wbg_baseVal_4591b09b2af7f432: function(arg0) {
            const ret = arg0.baseVal;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_beginComputePass_37a42f968e193dc4: function(arg0) {
            const ret = arg0.beginComputePass();
            return ret;
        },
        __wbg_beginRenderPass_672fd7fa8a642817: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.beginRenderPass(arg1);
            return ret;
        }, arguments); },
        __wbg_body_5eb99e7257e5ae34: function(arg0) {
            const ret = arg0.body;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_bottom_bfd7fcb3cf1632f0: function(arg0) {
            const ret = arg0.bottom;
            return ret;
        },
        __wbg_boundingClientRect_2327c787cbfa98ee: function(arg0) {
            const ret = arg0.boundingClientRect;
            return ret;
        },
        __wbg_buffer_60b8043cd926067d: function(arg0) {
            const ret = arg0.buffer;
            return ret;
        },
        __wbg_call_2d781c1f4d5c0ef8: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.call(arg1, arg2);
            return ret;
        }, arguments); },
        __wbg_call_dcc2662fa17a72cf: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = arg0.call(arg1, arg2, arg3);
            return ret;
        }, arguments); },
        __wbg_call_e133b57c9155d22c: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.call(arg1);
            return ret;
        }, arguments); },
        __wbg_capturedstate_new: function(arg0) {
            const ret = CapturedState.__wrap(arg0);
            return ret;
        },
        __wbg_checked_7b8b07c4341e3e6c: function(arg0) {
            const ret = arg0.checked;
            return ret;
        },
        __wbg_children_95c695034f7287c2: function(arg0) {
            const ret = arg0.children;
            return ret;
        },
        __wbg_classList_07fcb7252e322f6f: function(arg0) {
            const ret = arg0.classList;
            return ret;
        },
        __wbg_className_469dc424b1b0b858: function(arg0, arg1) {
            const ret = arg1.className;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_clearTimeout_113b1cde814ec762: function(arg0) {
            const ret = clearTimeout(arg0);
            return ret;
        },
        __wbg_clearWatch_cbb20a082f56bbe8: function(arg0, arg1) {
            arg0.clearWatch(arg1);
        },
        __wbg_clear_f0a9edc1f780da4e: function() { return handleError(function (arg0) {
            arg0.clear();
        }, arguments); },
        __wbg_clientX_51eb1976d50e9aa7: function(arg0) {
            const ret = arg0.clientX;
            return ret;
        },
        __wbg_clientY_bf90b5a826653c23: function(arg0) {
            const ret = arg0.clientY;
            return ret;
        },
        __wbg_close_9bf05dee8cc57aff: function(arg0) {
            arg0.close();
        },
        __wbg_close_a86fff250f8aa14f: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            arg0.close(arg1, getStringFromWasm0(arg2, arg3));
        }, arguments); },
        __wbg_close_af26905c832a88cb: function() { return handleError(function (arg0) {
            arg0.close();
        }, arguments); },
        __wbg_closest_ee628ba349731f6d: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.closest(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_code_21c62be11333bd1b: function(arg0) {
            const ret = arg0.code;
            return ret;
        },
        __wbg_code_aea376e2d265a64f: function(arg0) {
            const ret = arg0.code;
            return ret;
        },
        __wbg_configure_03c6d8b8f6b9b54f: function() { return handleError(function (arg0, arg1) {
            arg0.configure(arg1);
        }, arguments); },
        __wbg_contains_d1b71c766bb23709: function(arg0, arg1, arg2) {
            const ret = arg0.contains(getStringFromWasm0(arg1, arg2));
            return ret;
        },
        __wbg_content_4373268a6f34e443: function(arg0, arg1) {
            const ret = arg1.content;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_coords_1668fa31ef6650cb: function(arg0) {
            const ret = arg0.coords;
            return ret;
        },
        __wbg_createBindGroupLayout_7b4b530aa08cfed5: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.createBindGroupLayout(arg1);
            return ret;
        }, arguments); },
        __wbg_createBindGroup_28273deae4e32692: function(arg0, arg1) {
            const ret = arg0.createBindGroup(arg1);
            return ret;
        },
        __wbg_createBuffer_8bac0feca41a8825: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.createBuffer(arg1);
            return ret;
        }, arguments); },
        __wbg_createCommandEncoder_cd4f27624c068db1: function(arg0) {
            const ret = arg0.createCommandEncoder();
            return ret;
        },
        __wbg_createComputePipeline_a64220e0c3c0eead: function(arg0, arg1) {
            const ret = arg0.createComputePipeline(arg1);
            return ret;
        },
        __wbg_createElementNS_aac38e987dc3e061: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            const ret = arg0.createElementNS(arg1 === 0 ? undefined : getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
            return ret;
        }, arguments); },
        __wbg_createElement_9b0aab265c549ded: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.createElement(getStringFromWasm0(arg1, arg2));
            return ret;
        }, arguments); },
        __wbg_createPipelineLayout_918dc5ba3e71889a: function(arg0, arg1) {
            const ret = arg0.createPipelineLayout(arg1);
            return ret;
        },
        __wbg_createRenderPipeline_92147495a04e4535: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.createRenderPipeline(arg1);
            return ret;
        }, arguments); },
        __wbg_createSampler_b8a956e3d4d4bdd0: function(arg0, arg1) {
            const ret = arg0.createSampler(arg1);
            return ret;
        },
        __wbg_createShaderModule_8fbdf866a6e2d7a0: function(arg0, arg1) {
            const ret = arg0.createShaderModule(arg1);
            return ret;
        },
        __wbg_createTextNode_1997fd99f09c6afd: function(arg0, arg1, arg2) {
            const ret = arg0.createTextNode(getStringFromWasm0(arg1, arg2));
            return ret;
        },
        __wbg_createTexture_06c3f76db23c0f89: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.createTexture(arg1);
            return ret;
        }, arguments); },
        __wbg_createView_3438b27f2f07fec4: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.createView(arg1);
            return ret;
        }, arguments); },
        __wbg_createView_e70b60326d45fac5: function() { return handleError(function (arg0) {
            const ret = arg0.createView();
            return ret;
        }, arguments); },
        __wbg_data_a3d9ff9cdd801002: function(arg0) {
            const ret = arg0.data;
            return ret;
        },
        __wbg_debug_271c16e6de0bc226: function(arg0, arg1, arg2, arg3) {
            console.debug(arg0, arg1, arg2, arg3);
        },
        __wbg_destroy_a2f6f3c1f852f812: function(arg0) {
            arg0.destroy();
        },
        __wbg_destroy_fb16ec43ff2a1029: function(arg0) {
            arg0.destroy();
        },
        __wbg_detail_6061fd0cdb1cb16f: function(arg0) {
            const ret = arg0.detail;
            return ret;
        },
        __wbg_disconnect_21257e7fa524a113: function(arg0) {
            arg0.disconnect();
        },
        __wbg_dispatchEvent_29145a50abb697bc: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.dispatchEvent(arg1);
            return ret;
        }, arguments); },
        __wbg_document_c0320cd4183c6d9b: function(arg0) {
            const ret = arg0.document;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_done_08ce71ee07e3bd17: function(arg0) {
            const ret = arg0.done;
            return ret;
        },
        __wbg_drawIndexed_1e1d0fd512365540: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            arg0.drawIndexed(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4, arg5 >>> 0);
        },
        __wbg_drawIndirect_e10267a98b59d5e0: function(arg0, arg1, arg2) {
            arg0.drawIndirect(arg1, arg2);
        },
        __wbg_draw_0446cf41a3803b71: function(arg0, arg1) {
            arg0.draw(arg1 >>> 0);
        },
        __wbg_draw_5f6cf1afc7266a08: function(arg0, arg1, arg2, arg3, arg4) {
            arg0.draw(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_draw_9046fecc62880dc5: function(arg0, arg1, arg2) {
            arg0.draw(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_end_28d0ab4f47baa031: function(arg0) {
            arg0.end();
        },
        __wbg_end_c28e679c233fe3e2: function(arg0) {
            arg0.end();
        },
        __wbg_error_1eece6b0039034ce: function(arg0, arg1, arg2, arg3) {
            console.error(arg0, arg1, arg2, arg3);
        },
        __wbg_error_8d9a8e04cd1d3588: function(arg0) {
            console.error(arg0);
        },
        __wbg_error_a6fa202b58aa1cd3: function(arg0, arg1) {
            let deferred0_0;
            let deferred0_1;
            try {
                deferred0_0 = arg0;
                deferred0_1 = arg1;
                console.error(getStringFromWasm0(arg0, arg1));
            } finally {
                wasm.__wbindgen_free(deferred0_0, deferred0_1, 1);
            }
        },
        __wbg_features_e5ef65fb1f70f34b: function(arg0) {
            const ret = arg0.features;
            return ret;
        },
        __wbg_finish_a46ec2b3ba59dcb9: function(arg0) {
            const ret = arg0.finish();
            return ret;
        },
        __wbg_forward_67afd077eee51e0d: function() { return handleError(function (arg0) {
            arg0.forward();
        }, arguments); },
        __wbg_geolocation_9c32526430b2330b: function() { return handleError(function (arg0) {
            const ret = arg0.geolocation;
            return ret;
        }, arguments); },
        __wbg_geoposition_new: function(arg0) {
            const ret = GeoPosition.__wrap(arg0);
            return ret;
        },
        __wbg_getAttribute_cf830fef39b6ba0e: function(arg0, arg1, arg2, arg3) {
            const ret = arg1.getAttribute(getStringFromWasm0(arg2, arg3));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getBBox_2ba1f8315ebe1386: function() { return handleError(function (arg0) {
            const ret = arg0.getBBox();
            return ret;
        }, arguments); },
        __wbg_getBoundingClientRect_b236f2e393fd0e7a: function(arg0) {
            const ret = arg0.getBoundingClientRect();
            return ret;
        },
        __wbg_getComputedStyle_b12e52450a4be72c: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.getComputedStyle(arg1);
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_getContext_f04bf8f22dcb2d53: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.getContext(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_getCurrentPosition_b3b9b7ba09338bb3: function(arg0, arg1, arg2, arg3) {
            arg0.getCurrentPosition(arg1, arg2, arg3);
        },
        __wbg_getCurrentTexture_7fd853fe17849c85: function() { return handleError(function (arg0) {
            const ret = arg0.getCurrentTexture();
            return ret;
        }, arguments); },
        __wbg_getElementById_d1f25d287b19a833: function(arg0, arg1, arg2) {
            const ret = arg0.getElementById(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_getItem_a7cc1d4f154f2e6f: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = arg1.getItem(getStringFromWasm0(arg2, arg3));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_getMappedRange_06bcdc87c65f777e: function() { return handleError(function (arg0) {
            const ret = arg0.getMappedRange();
            return ret;
        }, arguments); },
        __wbg_getMappedRange_474821a7ec636dbb: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.getMappedRange(arg1, arg2);
            return ret;
        }, arguments); },
        __wbg_getPointAtLength_b4f588534eb673ab: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.getPointAtLength(arg1);
            return ret;
        }, arguments); },
        __wbg_getPreferredCanvasFormat_e571195270d6536f: function(arg0) {
            const ret = arg0.getPreferredCanvasFormat();
            return (__wbindgen_enum_GpuTextureFormat.indexOf(ret) + 1 || 102) - 1;
        },
        __wbg_getPropertyValue_d2181532557839cf: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = arg1.getPropertyValue(getStringFromWasm0(arg2, arg3));
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_getTotalLength_96eb62345a7220f4: function(arg0) {
            const ret = arg0.getTotalLength();
            return ret;
        },
        __wbg_get_3ef1eba1850ade27: function() { return handleError(function (arg0, arg1) {
            const ret = Reflect.get(arg0, arg1);
            return ret;
        }, arguments); },
        __wbg_get_a8ee5c45dabc1b3b: function(arg0, arg1) {
            const ret = arg0[arg1 >>> 0];
            return ret;
        },
        __wbg_get_c7546417fb0bec10: function(arg0, arg1) {
            const ret = arg0[arg1 >>> 0];
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_hasAttribute_924558041de5324b: function(arg0, arg1, arg2) {
            const ret = arg0.hasAttribute(getStringFromWasm0(arg1, arg2));
            return ret;
        },
        __wbg_hash_20f4358e910e29b8: function(arg0, arg1) {
            const ret = arg1.hash;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_head_3cb79209fe5c12b3: function(arg0) {
            const ret = arg0.head;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_heading_a587c7c7c1b50eb0: function(arg0, arg1) {
            const ret = arg1.heading;
            getDataViewMemory0().setFloat64(arg0 + 8 * 1, isLikeNone(ret) ? 0 : ret, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, !isLikeNone(ret), true);
        },
        __wbg_height_6568c4427c3b889d: function(arg0) {
            const ret = arg0.height;
            return ret;
        },
        __wbg_height_75b0d10baf97e535: function(arg0) {
            const ret = arg0.height;
            return ret;
        },
        __wbg_height_8c06cb597de53887: function(arg0) {
            const ret = arg0.height;
            return ret;
        },
        __wbg_height_fdf21c66d7f29f89: function(arg0) {
            const ret = arg0.height;
            return ret;
        },
        __wbg_hidden_696aedb715359e8c: function(arg0) {
            const ret = arg0.hidden;
            return ret;
        },
        __wbg_history_26b8c29b7753d0e8: function() { return handleError(function (arg0) {
            const ret = arg0.history;
            return ret;
        }, arguments); },
        __wbg_hostname_a30ece22df1c8b63: function() { return handleError(function (arg0, arg1) {
            const ret = arg1.hostname;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_id_491c6437a748ea9f: function(arg0, arg1) {
            const ret = arg1.id;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_info_0194681687b5ab04: function(arg0, arg1, arg2, arg3) {
            console.info(arg0, arg1, arg2, arg3);
        },
        __wbg_insertBefore_64157928ea5f5def: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.insertBefore(arg1, arg2);
            return ret;
        }, arguments); },
        __wbg_instanceof_Element_7f177ac0337279af: function(arg0) {
            let result;
            try {
                result = arg0 instanceof Element;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_GpuAdapter_a667e6a5c8e36404: function(arg0) {
            let result;
            try {
                result = arg0 instanceof GPUAdapter;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_GpuCanvasContext_f66125e000b2f9c3: function(arg0) {
            let result;
            try {
                result = arg0 instanceof GPUCanvasContext;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_GpuCommandBuffer_8457eea749adc442: function(arg0) {
            let result;
            try {
                result = arg0 instanceof GPUCommandBuffer;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_GpuDevice_93b30216a83e9dff: function(arg0) {
            let result;
            try {
                result = arg0 instanceof GPUDevice;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_Gpu_6933b978fff681c5: function(arg0) {
            let result;
            try {
                result = arg0 instanceof GPU;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_HtmlAnchorElement_085fbdab589de474: function(arg0) {
            let result;
            try {
                result = arg0 instanceof HTMLAnchorElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_HtmlElement_ef05df8222c2b81b: function(arg0) {
            let result;
            try {
                result = arg0 instanceof HTMLElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_HtmlInputElement_f6b9c8ea98b1980f: function(arg0) {
            let result;
            try {
                result = arg0 instanceof HTMLInputElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_HtmlLinkElement_57d0f18f76177395: function(arg0) {
            let result;
            try {
                result = arg0 instanceof HTMLLinkElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_HtmlMetaElement_07f78901e9785572: function(arg0) {
            let result;
            try {
                result = arg0 instanceof HTMLMetaElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_IntersectionObserverEntry_1f308400e360909f: function(arg0) {
            let result;
            try {
                result = arg0 instanceof IntersectionObserverEntry;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_SvgElement_5e8fc40a4330df8a: function(arg0) {
            let result;
            try {
                result = arg0 instanceof SVGElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_SvgGraphicsElement_7532cdeb60ef57a7: function(arg0) {
            let result;
            try {
                result = arg0 instanceof SVGGraphicsElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_SvgPathElement_59cb4cdf88b8c484: function(arg0) {
            let result;
            try {
                result = arg0 instanceof SVGPathElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_SvgsvgElement_952cae1fba5e81b1: function(arg0) {
            let result;
            try {
                result = arg0 instanceof SVGSVGElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_Window_23e677d2c6843922: function(arg0) {
            let result;
            try {
                result = arg0 instanceof Window;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_intersectionRatio_7b821bb4948eb8c1: function(arg0) {
            const ret = arg0.intersectionRatio;
            return ret;
        },
        __wbg_isContentEditable_5cefb711f7d1a768: function(arg0) {
            const ret = arg0.isContentEditable;
            return ret;
        },
        __wbg_isIntersecting_b3e74fb0cf75f7d1: function(arg0) {
            const ret = arg0.isIntersecting;
            return ret;
        },
        __wbg_is_a166b9958c2438ad: function(arg0, arg1) {
            const ret = Object.is(arg0, arg1);
            return ret;
        },
        __wbg_item_08587c228265a63e: function(arg0, arg1) {
            const ret = arg0.item(arg1 >>> 0);
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_key_84733a6ee7e4d63e: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg1.key(arg2 >>> 0);
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_key_85a141bbb3c7dd5a: function(arg0, arg1) {
            const ret = arg1.key;
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_latitude_6e3d9dd07dbf3d8d: function(arg0) {
            const ret = arg0.latitude;
            return ret;
        },
        __wbg_left_0050d4abe2736ee9: function(arg0) {
            const ret = arg0.left;
            return ret;
        },
        __wbg_length_6d31ca02e78204b5: function(arg0) {
            const ret = arg0.length;
            return ret;
        },
        __wbg_length_8632bd8b5ab30449: function() { return handleError(function (arg0) {
            const ret = arg0.length;
            return ret;
        }, arguments); },
        __wbg_length_8e55f95606d8e278: function(arg0) {
            const ret = arg0.length;
            return ret;
        },
        __wbg_length_b3416cf66a5452c8: function(arg0) {
            const ret = arg0.length;
            return ret;
        },
        __wbg_length_ea16607d7b61445b: function(arg0) {
            const ret = arg0.length;
            return ret;
        },
        __wbg_limits_aaba0948329a625f: function(arg0) {
            const ret = arg0.limits;
            return ret;
        },
        __wbg_localStorage_51c38b3b222e1ed2: function() { return handleError(function (arg0) {
            const ret = arg0.localStorage;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_location_fc8d47802682dd93: function(arg0) {
            const ret = arg0.location;
            return ret;
        },
        __wbg_log_70972330cfc941dd: function(arg0, arg1, arg2, arg3) {
            console.log(arg0, arg1, arg2, arg3);
        },
        __wbg_log_f9fd74320aa3c372: function(arg0, arg1) {
            console.log(arg0, arg1);
        },
        __wbg_longitude_26689131cfccdace: function(arg0) {
            const ret = arg0.longitude;
            return ret;
        },
        __wbg_lost_53a9adbb0de6e9a2: function(arg0) {
            const ret = arg0.lost;
            return ret;
        },
        __wbg_mapAsync_3eb761508b0cf2fd: function(arg0, arg1, arg2, arg3) {
            const ret = arg0.mapAsync(arg1 >>> 0, arg2, arg3);
            return ret;
        },
        __wbg_matchMedia_b27489ec503ba2a5: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.matchMedia(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_matches_d58caa45a0ef29a3: function(arg0) {
            const ret = arg0.matches;
            return ret;
        },
        __wbg_matches_f83fffb38a4551ad: function(arg0) {
            const ret = arg0.matches;
            return ret;
        },
        __wbg_message_67f6368dc2a526af: function(arg0, arg1) {
            const ret = arg1.message;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_message_87704339e07207af: function(arg0, arg1) {
            const ret = arg1.message;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_navigator_9cebf56f28aa719b: function(arg0) {
            const ret = arg0.navigator;
            return ret;
        },
        __wbg_newValue_aa1496183766bf05: function(arg0, arg1) {
            const ret = arg1.newValue;
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_new_227d7c05414eb861: function() {
            const ret = new Error();
            return ret;
        },
        __wbg_new_5f486cdf45a04d78: function(arg0) {
            const ret = new Uint8Array(arg0);
            return ret;
        },
        __wbg_new_a70fbab9066b301f: function() {
            const ret = new Array();
            return ret;
        },
        __wbg_new_ab79df5bd7c26067: function() {
            const ret = new Object();
            return ret;
        },
        __wbg_new_d098e265629cd10f: function(arg0, arg1) {
            try {
                var state0 = {a: arg0, b: arg1};
                var cb0 = (arg0, arg1) => {
                    const a = state0.a;
                    state0.a = 0;
                    try {
                        return wasm_bindgen__convert__closures_____invoke__h6c1eb3a335b0afa4(a, state0.b, arg0, arg1);
                    } finally {
                        state0.a = a;
                    }
                };
                const ret = new Promise(cb0);
                return ret;
            } finally {
                state0.a = state0.b = 0;
            }
        },
        __wbg_new_dd50bcc3f60ba434: function() { return handleError(function (arg0, arg1) {
            const ret = new WebSocket(getStringFromWasm0(arg0, arg1));
            return ret;
        }, arguments); },
        __wbg_new_from_slice_22da9388ac046e50: function(arg0, arg1) {
            const ret = new Uint8Array(getArrayU8FromWasm0(arg0, arg1));
            return ret;
        },
        __wbg_new_typed_aaaeaf29cf802876: function(arg0, arg1) {
            try {
                var state0 = {a: arg0, b: arg1};
                var cb0 = (arg0, arg1) => {
                    const a = state0.a;
                    state0.a = 0;
                    try {
                        return wasm_bindgen__convert__closures_____invoke__h6c1eb3a335b0afa4(a, state0.b, arg0, arg1);
                    } finally {
                        state0.a = a;
                    }
                };
                const ret = new Promise(cb0);
                return ret;
            } finally {
                state0.a = state0.b = 0;
            }
        },
        __wbg_new_with_base_d787868306e9ee82: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = new URL(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3));
            return ret;
        }, arguments); },
        __wbg_new_with_event_init_dict_590586ad0ea40ad7: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = new CustomEvent(getStringFromWasm0(arg0, arg1), arg2);
            return ret;
        }, arguments); },
        __wbg_new_with_event_source_init_dict_7952384d79ffd8d0: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = new EventSource(getStringFromWasm0(arg0, arg1), arg2);
            return ret;
        }, arguments); },
        __wbg_new_with_options_897716b4d74e6aa0: function() { return handleError(function (arg0, arg1) {
            const ret = new IntersectionObserver(arg0, arg1);
            return ret;
        }, arguments); },
        __wbg_new_with_str_299114bdb2430303: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = new WebSocket(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3));
            return ret;
        }, arguments); },
        __wbg_new_with_str_sequence_82c04ad794ead10e: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = new WebSocket(getStringFromWasm0(arg0, arg1), arg2);
            return ret;
        }, arguments); },
        __wbg_next_11b99ee6237339e3: function() { return handleError(function (arg0) {
            const ret = arg0.next();
            return ret;
        }, arguments); },
        __wbg_nodeType_17b68b25b25c1b52: function(arg0) {
            const ret = arg0.nodeType;
            return ret;
        },
        __wbg_now_16f0c993d5dd6c27: function() {
            const ret = Date.now();
            return ret;
        },
        __wbg_now_c6d7a7d35f74f6f1: function(arg0) {
            const ret = arg0.now();
            return ret;
        },
        __wbg_observe_a829ffd9907f84b1: function(arg0, arg1) {
            arg0.observe(arg1);
        },
        __wbg_offsetHeight_d67fa0a1c7a582f1: function(arg0) {
            const ret = arg0.offsetHeight;
            return ret;
        },
        __wbg_offsetWidth_2e99270f392b1f3e: function(arg0) {
            const ret = arg0.offsetWidth;
            return ret;
        },
        __wbg_origin_a482fc79aee4de43: function(arg0, arg1) {
            const ret = arg1.origin;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_origin_bac5c3119fe40a90: function() { return handleError(function (arg0, arg1) {
            const ret = arg1.origin;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_parentElement_6ea1a9ddfe78f22d: function(arg0) {
            const ret = arg0.parentElement;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_parentNode_f02c28ae3eec09bc: function(arg0) {
            const ret = arg0.parentNode;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_pathname_619d419072a14b21: function(arg0, arg1) {
            const ret = arg1.pathname;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_pathname_91da77877cfd2b76: function() { return handleError(function (arg0, arg1) {
            const ret = arg1.pathname;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_performance_28be169151161678: function(arg0) {
            const ret = arg0.performance;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_pieslicedata_unwrap: function(arg0) {
            const ret = PieSliceData.__unwrap(arg0);
            return ret;
        },
        __wbg_platform_89094136c8b1c14d: function() { return handleError(function (arg0, arg1) {
            const ret = arg1.platform;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_preventDefault_25a229bfe5c510f8: function(arg0) {
            arg0.preventDefault();
        },
        __wbg_pushState_5508821a88aaddd2: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5) {
            arg0.pushState(arg1, getStringFromWasm0(arg2, arg3), arg4 === 0 ? undefined : getStringFromWasm0(arg4, arg5));
        }, arguments); },
        __wbg_push_e87b0e732085a946: function(arg0, arg1) {
            const ret = arg0.push(arg1);
            return ret;
        },
        __wbg_querySelectorAll_22fb20807c17166d: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.querySelectorAll(getStringFromWasm0(arg1, arg2));
            return ret;
        }, arguments); },
        __wbg_querySelectorAll_ccbf0696a1c6fed8: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.querySelectorAll(getStringFromWasm0(arg1, arg2));
            return ret;
        }, arguments); },
        __wbg_querySelector_332d8dfa3e191085: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.querySelector(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_querySelector_46ff1b81410aebea: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.querySelector(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        }, arguments); },
        __wbg_queueMicrotask_0c399741342fb10f: function(arg0) {
            const ret = arg0.queueMicrotask;
            return ret;
        },
        __wbg_queueMicrotask_a082d78ce798393e: function(arg0) {
            queueMicrotask(arg0);
        },
        __wbg_queue_5b6ab754cbbb317a: function(arg0) {
            const ret = arg0.queue;
            return ret;
        },
        __wbg_readyState_1f1e7f1bdf9f4d42: function(arg0) {
            const ret = arg0.readyState;
            return ret;
        },
        __wbg_readyState_3a03f060e7fd4fe7: function(arg0) {
            const ret = arg0.readyState;
            return ret;
        },
        __wbg_reason_90bbeb9b3cd7c819: function(arg0) {
            const ret = arg0.reason;
            return (__wbindgen_enum_GpuDeviceLostReason.indexOf(ret) + 1 || 3) - 1;
        },
        __wbg_reason_cbcb9911796c4714: function(arg0, arg1) {
            const ret = arg1.reason;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_reject_452b6409a2fde3cd: function(arg0) {
            const ret = Promise.reject(arg0);
            return ret;
        },
        __wbg_removeAttribute_c0738b49de4ead0b: function() { return handleError(function (arg0, arg1, arg2) {
            arg0.removeAttribute(getStringFromWasm0(arg1, arg2));
        }, arguments); },
        __wbg_removeChild_dfd4207a6ece49c1: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.removeChild(arg1);
            return ret;
        }, arguments); },
        __wbg_removeEventListener_d27694700fc0df8b: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            arg0.removeEventListener(getStringFromWasm0(arg1, arg2), arg3);
        }, arguments); },
        __wbg_removeItem_95c258b9afdd7580: function() { return handleError(function (arg0, arg1, arg2) {
            arg0.removeItem(getStringFromWasm0(arg1, arg2));
        }, arguments); },
        __wbg_removeProperty_5b3523637b608633: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = arg1.removeProperty(getStringFromWasm0(arg2, arg3));
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        }, arguments); },
        __wbg_remove_83b6b382cbfb297b: function() { return handleError(function (arg0, arg1, arg2) {
            arg0.remove(getStringFromWasm0(arg1, arg2));
        }, arguments); },
        __wbg_replaceChild_9876b14e5b35a2a2: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.replaceChild(arg1, arg2);
            return ret;
        }, arguments); },
        __wbg_replaceState_2dd9c86c164b292e: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5) {
            arg0.replaceState(arg1, getStringFromWasm0(arg2, arg3), arg4 === 0 ? undefined : getStringFromWasm0(arg4, arg5));
        }, arguments); },
        __wbg_requestAdapter_24f34d50169a2b99: function(arg0) {
            const ret = arg0.requestAdapter();
            return ret;
        },
        __wbg_requestAdapter_e235af181fc37e67: function(arg0, arg1) {
            const ret = arg0.requestAdapter(arg1);
            return ret;
        },
        __wbg_requestAnimationFrame_206c97f410e7a383: function() { return handleError(function (arg0, arg1) {
            const ret = arg0.requestAnimationFrame(arg1);
            return ret;
        }, arguments); },
        __wbg_requestDevice_19593893e06c10f4: function(arg0) {
            const ret = arg0.requestDevice();
            return ret;
        },
        __wbg_resolve_ae8d83246e5bcc12: function(arg0) {
            const ret = Promise.resolve(arg0);
            return ret;
        },
        __wbg_right_ad93e95b5e30b7ff: function(arg0) {
            const ret = arg0.right;
            return ret;
        },
        __wbg_runtime_new: function(arg0) {
            const ret = Runtime.__wrap(arg0);
            return ret;
        },
        __wbg_search_35617fb7936183df: function(arg0, arg1) {
            const ret = arg1.search;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_send_4a1dc66e8653e5ed: function() { return handleError(function (arg0, arg1, arg2) {
            arg0.send(getStringFromWasm0(arg1, arg2));
        }, arguments); },
        __wbg_send_d31a693c975dea74: function() { return handleError(function (arg0, arg1, arg2) {
            arg0.send(getArrayU8FromWasm0(arg1, arg2));
        }, arguments); },
        __wbg_setAttributeNS_83830f885bc964f4: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            arg0.setAttributeNS(arg1 === 0 ? undefined : getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4), getStringFromWasm0(arg5, arg6));
        }, arguments); },
        __wbg_setAttribute_f20d3b966749ab64: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            arg0.setAttribute(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
        }, arguments); },
        __wbg_setBindGroup_f5a3bf4b9fa20cb9: function(arg0, arg1, arg2) {
            arg0.setBindGroup(arg1 >>> 0, arg2);
        },
        __wbg_setIndexBuffer_d361a7dd5100bf47: function(arg0, arg1, arg2, arg3) {
            arg0.setIndexBuffer(arg1, __wbindgen_enum_GpuIndexFormat[arg2], arg3);
        },
        __wbg_setIndexBuffer_ef8d81e60d4348ee: function(arg0, arg1, arg2, arg3, arg4) {
            arg0.setIndexBuffer(arg1, __wbindgen_enum_GpuIndexFormat[arg2], arg3, arg4);
        },
        __wbg_setItem_5f84aeef0d7f3c17: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            arg0.setItem(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
        }, arguments); },
        __wbg_setPipeline_51be59779ada984d: function(arg0, arg1) {
            arg0.setPipeline(arg1);
        },
        __wbg_setProperty_ef29d2aa64a04d2b: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            arg0.setProperty(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
        }, arguments); },
        __wbg_setScissorRect_9ce9b6ce9ce963b6: function(arg0, arg1, arg2, arg3, arg4) {
            arg0.setScissorRect(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_setTimeout_7f7035ad0b026458: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.setTimeout(arg1, arg2);
            return ret;
        }, arguments); },
        __wbg_setTimeout_ef24d2fc3ad97385: function() { return handleError(function (arg0, arg1) {
            const ret = setTimeout(arg0, arg1);
            return ret;
        }, arguments); },
        __wbg_setVertexBuffer_4b46972d6698f81d: function(arg0, arg1, arg2, arg3) {
            arg0.setVertexBuffer(arg1 >>> 0, arg2, arg3);
        },
        __wbg_setVertexBuffer_6dfe4dd8b7fd9f21: function(arg0, arg1, arg2) {
            arg0.setVertexBuffer(arg1 >>> 0, arg2);
        },
        __wbg_setVertexBuffer_cdd28d1611dce122: function(arg0, arg1, arg2, arg3, arg4) {
            arg0.setVertexBuffer(arg1 >>> 0, arg2, arg3, arg4);
        },
        __wbg_setViewport_fcbb65ff77b1e1bf: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            arg0.setViewport(arg1, arg2, arg3, arg4, arg5, arg6);
        },
        __wbg_set_6be42768c690e380: function(arg0, arg1, arg2) {
            arg0[arg1] = arg2;
        },
        __wbg_set_7eaa4f96924fd6b3: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = Reflect.set(arg0, arg1, arg2);
            return ret;
        }, arguments); },
        __wbg_set_8c0b3ffcf05d61c2: function(arg0, arg1, arg2) {
            arg0.set(getArrayU8FromWasm0(arg1, arg2));
        },
        __wbg_set_capture_271d6acb719615b3: function(arg0, arg1) {
            arg0.capture = arg1 !== 0;
        },
        __wbg_set_checked_682ea4d0bea94b97: function(arg0, arg1) {
            arg0.checked = arg1 !== 0;
        },
        __wbg_set_code_94473da68a33396c: function(arg0, arg1, arg2) {
            arg0.code = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_content_9097776e5b2da71c: function(arg0, arg1, arg2) {
            arg0.content = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_detail_5ef5904eae68e618: function(arg0, arg1) {
            arg0.detail = arg1;
        },
        __wbg_set_device_6a298571c1fab5ff: function(arg0, arg1) {
            arg0.device = arg1;
        },
        __wbg_set_disabled_16e4445551f0addb: function(arg0, arg1) {
            arg0.disabled = arg1 !== 0;
        },
        __wbg_set_enable_high_accuracy_47f66931ad3e3d7a: function(arg0, arg1) {
            arg0.enableHighAccuracy = arg1 !== 0;
        },
        __wbg_set_format_311e805183902f6b: function(arg0, arg1) {
            arg0.format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_href_9d0799c11e59855a: function(arg0, arg1, arg2) {
            arg0.href = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_id_2692cc8cc00cf4db: function(arg0, arg1, arg2) {
            arg0.id = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_innerHTML_97039584c4ab4c83: function(arg0, arg1, arg2) {
            arg0.innerHTML = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_mapped_at_creation_10545fa62507c04b: function(arg0, arg1) {
            arg0.mappedAtCreation = arg1 !== 0;
        },
        __wbg_set_maximum_age_37a47d4a9c0eccd9: function(arg0, arg1) {
            arg0.maximumAge = arg1 >>> 0;
        },
        __wbg_set_name_aaf0ea6c71aeb89f: function(arg0, arg1, arg2) {
            arg0.name = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_onclose_8da801226bdd7a7b: function(arg0, arg1) {
            arg0.onclose = arg1;
        },
        __wbg_set_onerror_18ee4e7660cdb555: function(arg0, arg1) {
            arg0.onerror = arg1;
        },
        __wbg_set_onerror_901ca711f94a5bbb: function(arg0, arg1) {
            arg0.onerror = arg1;
        },
        __wbg_set_onmessage_523dba0e73324d2f: function(arg0, arg1) {
            arg0.onmessage = arg1;
        },
        __wbg_set_onmessage_6f80ab771bf151aa: function(arg0, arg1) {
            arg0.onmessage = arg1;
        },
        __wbg_set_onopen_34e3e24cf9337ddd: function(arg0, arg1) {
            arg0.onopen = arg1;
        },
        __wbg_set_onopen_4dbbcf518a47f0f9: function(arg0, arg1) {
            arg0.onopen = arg1;
        },
        __wbg_set_power_preference_6a5cd351811b6b7e: function(arg0, arg1) {
            arg0.powerPreference = __wbindgen_enum_GpuPowerPreference[arg1];
        },
        __wbg_set_rel_7f9ccc09316f31ac: function(arg0, arg1, arg2) {
            arg0.rel = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_root_218154cb28e47c98: function(arg0, arg1) {
            arg0.root = arg1;
        },
        __wbg_set_root_margin_3b46537be72db527: function(arg0, arg1, arg2) {
            arg0.rootMargin = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_size_f64_43fbd919c7d5e6b5: function(arg0, arg1) {
            arg0.size = arg1;
        },
        __wbg_set_textContent_1e964492a2410e92: function(arg0, arg1, arg2) {
            arg0.textContent = arg1 === 0 ? undefined : getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_threshold_72d4541c0f23725b: function(arg0, arg1) {
            arg0.threshold = arg1;
        },
        __wbg_set_timeout_0d60f2fe14219c0d: function(arg0, arg1) {
            arg0.timeout = arg1 >>> 0;
        },
        __wbg_set_title_2160d10262f712f4: function(arg0, arg1, arg2) {
            arg0.title = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_usage_bec795879ec31852: function(arg0, arg1) {
            arg0.usage = arg1 >>> 0;
        },
        __wbg_set_value_0756834ee6cb3709: function(arg0, arg1, arg2) {
            arg0.value = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_with_credentials_101f725619b81958: function(arg0, arg1) {
            arg0.withCredentials = arg1 !== 0;
        },
        __wbg_speed_290049b34dcee115: function(arg0, arg1) {
            const ret = arg1.speed;
            getDataViewMemory0().setFloat64(arg0 + 8 * 1, isLikeNone(ret) ? 0 : ret, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, !isLikeNone(ret), true);
        },
        __wbg_stack_3b0d974bbf31e44f: function(arg0, arg1) {
            const ret = arg1.stack;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_static_accessor_GLOBAL_8adb955bd33fac2f: function() {
            const ret = typeof global === 'undefined' ? null : global;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_static_accessor_GLOBAL_THIS_ad356e0db91c7913: function() {
            const ret = typeof globalThis === 'undefined' ? null : globalThis;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_static_accessor_SELF_f207c857566db248: function() {
            const ret = typeof self === 'undefined' ? null : self;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_static_accessor_WINDOW_bb9f1ba69d61b386: function() {
            const ret = typeof window === 'undefined' ? null : window;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_style_0124c87588e99e28: function(arg0) {
            const ret = arg0.style;
            return ret;
        },
        __wbg_style_b01fc765f98b99ff: function(arg0) {
            const ret = arg0.style;
            return ret;
        },
        __wbg_submit_81404551b7462ef0: function(arg0, arg1, arg2) {
            arg0.submit(getArrayJsValueViewFromWasm0(arg1, arg2));
        },
        __wbg_tagName_3bd06789ca771c23: function(arg0, arg1) {
            const ret = arg1.tagName;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_target_7bc90f314634b37b: function(arg0) {
            const ret = arg0.target;
            return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
        },
        __wbg_target_9293709c76b077f8: function(arg0, arg1) {
            const ret = arg1.target;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_textContent_75b4506705c8c793: function(arg0, arg1) {
            const ret = arg1.textContent;
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_then_098abe61755d12f6: function(arg0, arg1) {
            const ret = arg0.then(arg1);
            return ret;
        },
        __wbg_then_1d7a5273811a5cea: function(arg0, arg1) {
            const ret = arg0.then(arg1);
            return ret;
        },
        __wbg_then_9e335f6dd892bc11: function(arg0, arg1, arg2) {
            const ret = arg0.then(arg1, arg2);
            return ret;
        },
        __wbg_time_c38f824eaf05b36a: function(arg0) {
            const ret = arg0.time;
            return ret;
        },
        __wbg_timestamp_dfdfda77f2136981: function(arg0) {
            const ret = arg0.timestamp;
            return ret;
        },
        __wbg_title_eb6d8b4a7c878501: function(arg0, arg1) {
            const ret = arg1.title;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_toggle_87cf598b224d0e80: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = arg0.toggle(getStringFromWasm0(arg1, arg2));
            return ret;
        }, arguments); },
        __wbg_top_378559f0b38a1038: function(arg0) {
            const ret = arg0.top;
            return ret;
        },
        __wbg_unmap_da0cf4403ff4f19e: function(arg0) {
            arg0.unmap();
        },
        __wbg_unobserve_ed74c2583d60061c: function(arg0, arg1) {
            arg0.unobserve(arg1);
        },
        __wbg_url_1adf4734cea15822: function(arg0, arg1) {
            const ret = arg1.url;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_value_21fc78aab0322612: function(arg0) {
            const ret = arg0.value;
            return ret;
        },
        __wbg_value_567d71719bef8eda: function(arg0, arg1) {
            const ret = arg1.value;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_values_513d4a7800e856a2: function(arg0) {
            const ret = arg0.values();
            return ret;
        },
        __wbg_viewBox_bcd5c26fab3d62e6: function(arg0) {
            const ret = arg0.viewBox;
            return ret;
        },
        __wbg_warn_69424c2d92a2fa73: function(arg0) {
            console.warn(arg0);
        },
        __wbg_warn_809cad1bfc2b3a42: function(arg0, arg1, arg2, arg3) {
            console.warn(arg0, arg1, arg2, arg3);
        },
        __wbg_watchPosition_fbc6545362fa8f22: function(arg0, arg1, arg2, arg3) {
            const ret = arg0.watchPosition(arg1, arg2, arg3);
            return ret;
        },
        __wbg_width_4d6fc7fecd877217: function(arg0) {
            const ret = arg0.width;
            return ret;
        },
        __wbg_width_8df4ba64e1cb1a60: function(arg0) {
            const ret = arg0.width;
            return ret;
        },
        __wbg_width_9824c1a2c17d3ebd: function(arg0) {
            const ret = arg0.width;
            return ret;
        },
        __wbg_width_f933723cb0daf368: function(arg0) {
            const ret = arg0.width;
            return ret;
        },
        __wbg_writeBuffer_60bb3be726c14747: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5) {
            arg0.writeBuffer(arg1, arg2, arg3, arg4, arg5);
        }, arguments); },
        __wbg_writeBuffer_b27f8bcb04ccf228: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            arg0.writeBuffer(arg1, arg2 >>> 0, arg3);
        }, arguments); },
        __wbg_writeTexture_bffa9b2232812bfb: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            arg0.writeTexture(arg1, arg2, arg3, arg4);
        }, arguments); },
        __wbg_x_62c3107ec67fb9f2: function(arg0) {
            const ret = arg0.x;
            return ret;
        },
        __wbg_x_663bdb24f78fdb4f: function(arg0) {
            const ret = arg0.x;
            return ret;
        },
        __wbg_x_a2b3b3a855175bf9: function(arg0) {
            const ret = arg0.x;
            return ret;
        },
        __wbg_y_0606499823d8a75d: function(arg0) {
            const ret = arg0.y;
            return ret;
        },
        __wbg_y_30a7c06266f44f65: function(arg0) {
            const ret = arg0.y;
            return ret;
        },
        __wbg_y_be1a4ec0966e3935: function(arg0) {
            const ret = arg0.y;
            return ret;
        },
        __wbindgen_cast_0000000000000001: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [Externref], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3);
            return ret;
        },
        __wbindgen_cast_0000000000000002: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("Array<any>"), NamedExternref("IntersectionObserver")], shim_idx: 157, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__ha7b5997a266ba3bb);
            return ret;
        },
        __wbindgen_cast_0000000000000003: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("CloseEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_2);
            return ret;
        },
        __wbindgen_cast_0000000000000004: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("CustomEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_3);
            return ret;
        },
        __wbindgen_cast_0000000000000005: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("ErrorEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_4);
            return ret;
        },
        __wbindgen_cast_0000000000000006: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("Event")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_5);
            return ret;
        },
        __wbindgen_cast_0000000000000007: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("Event")], shim_idx: 158, ret: Unit, inner_ret: Some(Unit) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38);
            return ret;
        },
        __wbindgen_cast_0000000000000008: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("GPUDevice")], shim_idx: 159, ret: Result(Unit), inner_ret: Some(Result(Unit)) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e);
            return ret;
        },
        __wbindgen_cast_0000000000000009: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("GPUDeviceLostInfo")], shim_idx: 158, ret: Unit, inner_ret: Some(Unit) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_8);
            return ret;
        },
        __wbindgen_cast_000000000000000a: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("GeolocationPosition")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_9);
            return ret;
        },
        __wbindgen_cast_000000000000000b: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("GeolocationPosition")], shim_idx: 158, ret: Unit, inner_ret: Some(Unit) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_10);
            return ret;
        },
        __wbindgen_cast_000000000000000c: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("GeolocationPositionError")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_11);
            return ret;
        },
        __wbindgen_cast_000000000000000d: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("GeolocationPositionError")], shim_idx: 158, ret: Unit, inner_ret: Some(Unit) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_12);
            return ret;
        },
        __wbindgen_cast_000000000000000e: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("MediaQueryListEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_13);
            return ret;
        },
        __wbindgen_cast_000000000000000f: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("MessageEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_14);
            return ret;
        },
        __wbindgen_cast_0000000000000010: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("MouseEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_15);
            return ret;
        },
        __wbindgen_cast_0000000000000011: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("StorageEvent")], shim_idx: 156, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_16);
            return ret;
        },
        __wbindgen_cast_0000000000000012: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [NamedExternref("any")], shim_idx: 159, ret: Result(Unit), inner_ret: Some(Result(Unit)) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e_17);
            return ret;
        },
        __wbindgen_cast_0000000000000013: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [], shim_idx: 154, ret: Unit, inner_ret: Some(Unit) }, mutable: false }) -> Externref`.
            const ret = makeClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__habd940842afd6a4b);
            return ret;
        },
        __wbindgen_cast_0000000000000014: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 1, function: Function { arguments: [], shim_idx: 155, ret: Unit, inner_ret: Some(Unit) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h20c8283e70380080, wasm_bindgen__convert__closures_____invoke__hb81663616f129ed0);
            return ret;
        },
        __wbindgen_cast_0000000000000015: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 197, function: Function { arguments: [Externref], shim_idx: 222, ret: Result(Unit), inner_ret: Some(Result(Unit)) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.wasm_bindgen__closure__destroy__h74cdfa934dbd4e78, wasm_bindgen__convert__closures_____invoke__h26c7a007d8dbb55a);
            return ret;
        },
        __wbindgen_cast_0000000000000016: function(arg0) {
            // Cast intrinsic for `F64 -> Externref`.
            const ret = arg0;
            return ret;
        },
        __wbindgen_cast_0000000000000017: function(arg0, arg1) {
            // Cast intrinsic for `Ref(String) -> Externref`.
            const ret = getStringFromWasm0(arg0, arg1);
            return ret;
        },
        __wbindgen_init_externref_table: function() {
            const table = wasm.__wbindgen_externrefs;
            const offset = table.grow(4);
            table.set(0, undefined);
            table.set(offset + 0, undefined);
            table.set(offset + 1, null);
            table.set(offset + 2, true);
            table.set(offset + 3, false);
        },
    };
    return {
        __proto__: null,
        "./hydrogen_runtime_bg.js": import0,
    };
}

function wasm_bindgen__convert__closures_____invoke__habd940842afd6a4b(arg0, arg1) {
    wasm.wasm_bindgen__convert__closures_____invoke__habd940842afd6a4b(arg0, arg1);
}

function wasm_bindgen__convert__closures_____invoke__hb81663616f129ed0(arg0, arg1) {
    wasm.wasm_bindgen__convert__closures_____invoke__hb81663616f129ed0(arg0, arg1);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_2(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_2(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_3(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_3(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_4(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_4(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_5(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_5(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_8(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_8(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_9(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_9(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_10(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_10(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_11(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_11(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_12(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h07e87e9984307d38_12(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_13(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_13(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_14(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_14(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_15(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_15(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_16(arg0, arg1, arg2) {
    wasm.wasm_bindgen__convert__closures_____invoke__h0f5a503c40d566e3_16(arg0, arg1, arg2);
}

function wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e(arg0, arg1, arg2) {
    const ret = wasm.wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e(arg0, arg1, arg2);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

function wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e_17(arg0, arg1, arg2) {
    const ret = wasm.wasm_bindgen__convert__closures_____invoke__hdde938f47fb8e60e_17(arg0, arg1, arg2);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

function wasm_bindgen__convert__closures_____invoke__h26c7a007d8dbb55a(arg0, arg1, arg2) {
    const ret = wasm.wasm_bindgen__convert__closures_____invoke__h26c7a007d8dbb55a(arg0, arg1, arg2);
    if (ret[1]) {
        throw takeFromExternrefTable0(ret[0]);
    }
}

function wasm_bindgen__convert__closures_____invoke__ha7b5997a266ba3bb(arg0, arg1, arg2, arg3) {
    wasm.wasm_bindgen__convert__closures_____invoke__ha7b5997a266ba3bb(arg0, arg1, arg2, arg3);
}

function wasm_bindgen__convert__closures_____invoke__h6c1eb3a335b0afa4(arg0, arg1, arg2, arg3) {
    wasm.wasm_bindgen__convert__closures_____invoke__h6c1eb3a335b0afa4(arg0, arg1, arg2, arg3);
}


const __wbindgen_enum_GpuDeviceLostReason = ["unknown", "destroyed"];


const __wbindgen_enum_GpuIndexFormat = ["uint16", "uint32"];


const __wbindgen_enum_GpuPowerPreference = ["low-power", "high-performance"];


const __wbindgen_enum_GpuTextureFormat = ["r8unorm", "r8snorm", "r8uint", "r8sint", "r16unorm", "r16snorm", "r16uint", "r16sint", "r16float", "rg8unorm", "rg8snorm", "rg8uint", "rg8sint", "r32uint", "r32sint", "r32float", "rg16unorm", "rg16snorm", "rg16uint", "rg16sint", "rg16float", "rgba8unorm", "rgba8unorm-srgb", "rgba8snorm", "rgba8uint", "rgba8sint", "bgra8unorm", "bgra8unorm-srgb", "rgb9e5ufloat", "rgb10a2uint", "rgb10a2unorm", "rg11b10ufloat", "rg32uint", "rg32sint", "rg32float", "rgba16unorm", "rgba16snorm", "rgba16uint", "rgba16sint", "rgba16float", "rgba32uint", "rgba32sint", "rgba32float", "stencil8", "depth16unorm", "depth24plus", "depth24plus-stencil8", "depth32float", "depth32float-stencil8", "bc1-rgba-unorm", "bc1-rgba-unorm-srgb", "bc2-rgba-unorm", "bc2-rgba-unorm-srgb", "bc3-rgba-unorm", "bc3-rgba-unorm-srgb", "bc4-r-unorm", "bc4-r-snorm", "bc5-rg-unorm", "bc5-rg-snorm", "bc6h-rgb-ufloat", "bc6h-rgb-float", "bc7-rgba-unorm", "bc7-rgba-unorm-srgb", "etc2-rgb8unorm", "etc2-rgb8unorm-srgb", "etc2-rgb8a1unorm", "etc2-rgb8a1unorm-srgb", "etc2-rgba8unorm", "etc2-rgba8unorm-srgb", "eac-r11unorm", "eac-r11snorm", "eac-rg11unorm", "eac-rg11snorm", "astc-4x4-unorm", "astc-4x4-unorm-srgb", "astc-5x4-unorm", "astc-5x4-unorm-srgb", "astc-5x5-unorm", "astc-5x5-unorm-srgb", "astc-6x5-unorm", "astc-6x5-unorm-srgb", "astc-6x6-unorm", "astc-6x6-unorm-srgb", "astc-8x5-unorm", "astc-8x5-unorm-srgb", "astc-8x6-unorm", "astc-8x6-unorm-srgb", "astc-8x8-unorm", "astc-8x8-unorm-srgb", "astc-10x5-unorm", "astc-10x5-unorm-srgb", "astc-10x6-unorm", "astc-10x6-unorm-srgb", "astc-10x8-unorm", "astc-10x8-unorm-srgb", "astc-10x10-unorm", "astc-10x10-unorm-srgb", "astc-12x10-unorm", "astc-12x10-unorm-srgb", "astc-12x12-unorm", "astc-12x12-unorm-srgb"];
const AriaHiderStateFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_ariahiderstate_free(ptr >>> 0, 1));
const BreakpointHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_breakpointhandle_free(ptr >>> 0, 1));
const BreakpointsFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_breakpoints_free(ptr >>> 0, 1));
const CapturedStateFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_capturedstate_free(ptr >>> 0, 1));
const CapturedStateStringsFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_capturedstatestrings_free(ptr >>> 0, 1));
const ChartPaddingFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_chartpadding_free(ptr >>> 0, 1));
const DebouncerFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_debouncer_free(ptr >>> 0, 1));
const GeoErrorFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_geoerror_free(ptr >>> 0, 1));
const GeoOptionsFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_geooptions_free(ptr >>> 0, 1));
const GeoPositionFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_geoposition_free(ptr >>> 0, 1));
const GeoWatchHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_geowatchhandle_free(ptr >>> 0, 1));
const GeofenceHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_geofencehandle_free(ptr >>> 0, 1));
const HiddenElementFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_hiddenelement_free(ptr >>> 0, 1));
const IntersectionEntryFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_intersectionentry_free(ptr >>> 0, 1));
const IntersectionHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_intersectionhandle_free(ptr >>> 0, 1));
const LineCrosshairHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_linecrosshairhandle_free(ptr >>> 0, 1));
const LinkInterceptHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_linkintercepthandle_free(ptr >>> 0, 1));
const MediaQueryHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_mediaqueryhandle_free(ptr >>> 0, 1));
const PieExplodeHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_pieexplodehandle_free(ptr >>> 0, 1));
const PieHoverHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_piehoverhandle_free(ptr >>> 0, 1));
const PieSliceDataFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_pieslicedata_free(ptr >>> 0, 1));
const PieTooltipHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_pietooltiphandle_free(ptr >>> 0, 1));
const RouteChangeHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_routechangehandle_free(ptr >>> 0, 1));
const RuntimeFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_runtime_free(ptr >>> 0, 1));
const StorageChangeHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_storagechangehandle_free(ptr >>> 0, 1));
const ThrottlerFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_throttler_free(ptr >>> 0, 1));
const TooltipPositionFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_tooltipposition_free(ptr >>> 0, 1));
const WrappedEventFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_wrappedevent_free(ptr >>> 0, 1));
const WsEventHandleFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_wseventhandle_free(ptr >>> 0, 1));

function addToExternrefTable0(obj) {
    const idx = wasm.__externref_table_alloc();
    wasm.__wbindgen_externrefs.set(idx, obj);
    return idx;
}

function _assertClass(instance, klass) {
    if (!(instance instanceof klass)) {
        throw new Error(`expected instance of ${klass.name}`);
    }
}

const CLOSURE_DTORS = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(state => state.dtor(state.a, state.b));

function debugString(val) {
    // primitive types
    const type = typeof val;
    if (type == 'number' || type == 'boolean' || val == null) {
        return  `${val}`;
    }
    if (type == 'string') {
        return `"${val}"`;
    }
    if (type == 'symbol') {
        const description = val.description;
        if (description == null) {
            return 'Symbol';
        } else {
            return `Symbol(${description})`;
        }
    }
    if (type == 'function') {
        const name = val.name;
        if (typeof name == 'string' && name.length > 0) {
            return `Function(${name})`;
        } else {
            return 'Function';
        }
    }
    // objects
    if (Array.isArray(val)) {
        const length = val.length;
        let debug = '[';
        if (length > 0) {
            debug += debugString(val[0]);
        }
        for(let i = 1; i < length; i++) {
            debug += ', ' + debugString(val[i]);
        }
        debug += ']';
        return debug;
    }
    // Test for built-in
    const builtInMatches = /\[object ([^\]]+)\]/.exec(toString.call(val));
    let className;
    if (builtInMatches && builtInMatches.length > 1) {
        className = builtInMatches[1];
    } else {
        // Failed to match the standard '[object ClassName]'
        return toString.call(val);
    }
    if (className == 'Object') {
        // we're a user defined class or Object
        // JSON.stringify avoids problems with cycles, and is generally much
        // easier than looping through ownProperties of `val`.
        try {
            return 'Object(' + JSON.stringify(val) + ')';
        } catch (_) {
            return 'Object';
        }
    }
    // errors
    if (val instanceof Error) {
        return `${val.name}: ${val.message}\n${val.stack}`;
    }
    // TODO we could test for more things here, like `Set`s and `Map`s.
    return className;
}

function getArrayI32FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getInt32ArrayMemory0().subarray(ptr / 4, ptr / 4 + len);
}

function getArrayJsValueFromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    const mem = getDataViewMemory0();
    const result = [];
    for (let i = ptr; i < ptr + 4 * len; i += 4) {
        result.push(wasm.__wbindgen_externrefs.get(mem.getUint32(i, true)));
    }
    wasm.__externref_drop_slice(ptr, len);
    return result;
}

function getArrayJsValueViewFromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    const mem = getDataViewMemory0();
    const result = [];
    for (let i = ptr; i < ptr + 4 * len; i += 4) {
        result.push(wasm.__wbindgen_externrefs.get(mem.getUint32(i, true)));
    }
    return result;
}

function getArrayU8FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
}

let cachedDataViewMemory0 = null;
function getDataViewMemory0() {
    if (cachedDataViewMemory0 === null || cachedDataViewMemory0.buffer.detached === true || (cachedDataViewMemory0.buffer.detached === undefined && cachedDataViewMemory0.buffer !== wasm.memory.buffer)) {
        cachedDataViewMemory0 = new DataView(wasm.memory.buffer);
    }
    return cachedDataViewMemory0;
}

let cachedInt32ArrayMemory0 = null;
function getInt32ArrayMemory0() {
    if (cachedInt32ArrayMemory0 === null || cachedInt32ArrayMemory0.byteLength === 0) {
        cachedInt32ArrayMemory0 = new Int32Array(wasm.memory.buffer);
    }
    return cachedInt32ArrayMemory0;
}

function getStringFromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return decodeText(ptr, len);
}

let cachedUint8ArrayMemory0 = null;
function getUint8ArrayMemory0() {
    if (cachedUint8ArrayMemory0 === null || cachedUint8ArrayMemory0.byteLength === 0) {
        cachedUint8ArrayMemory0 = new Uint8Array(wasm.memory.buffer);
    }
    return cachedUint8ArrayMemory0;
}

function handleError(f, args) {
    try {
        return f.apply(this, args);
    } catch (e) {
        const idx = addToExternrefTable0(e);
        wasm.__wbindgen_exn_store(idx);
    }
}

function isLikeNone(x) {
    return x === undefined || x === null;
}

function makeClosure(arg0, arg1, dtor, f) {
    const state = { a: arg0, b: arg1, cnt: 1, dtor };
    const real = (...args) => {

        // First up with a closure we increment the internal reference
        // count. This ensures that the Rust closure environment won't
        // be deallocated while we're invoking it.
        state.cnt++;
        try {
            return f(state.a, state.b, ...args);
        } finally {
            real._wbg_cb_unref();
        }
    };
    real._wbg_cb_unref = () => {
        if (--state.cnt === 0) {
            state.dtor(state.a, state.b);
            state.a = 0;
            CLOSURE_DTORS.unregister(state);
        }
    };
    CLOSURE_DTORS.register(real, state, state);
    return real;
}

function makeMutClosure(arg0, arg1, dtor, f) {
    const state = { a: arg0, b: arg1, cnt: 1, dtor };
    const real = (...args) => {

        // First up with a closure we increment the internal reference
        // count. This ensures that the Rust closure environment won't
        // be deallocated while we're invoking it.
        state.cnt++;
        const a = state.a;
        state.a = 0;
        try {
            return f(a, state.b, ...args);
        } finally {
            state.a = a;
            real._wbg_cb_unref();
        }
    };
    real._wbg_cb_unref = () => {
        if (--state.cnt === 0) {
            state.dtor(state.a, state.b);
            state.a = 0;
            CLOSURE_DTORS.unregister(state);
        }
    };
    CLOSURE_DTORS.register(real, state, state);
    return real;
}

function passArray8ToWasm0(arg, malloc) {
    const ptr = malloc(arg.length * 1, 1) >>> 0;
    getUint8ArrayMemory0().set(arg, ptr / 1);
    WASM_VECTOR_LEN = arg.length;
    return ptr;
}

function passArrayJsValueToWasm0(array, malloc) {
    const ptr = malloc(array.length * 4, 4) >>> 0;
    for (let i = 0; i < array.length; i++) {
        const add = addToExternrefTable0(array[i]);
        getDataViewMemory0().setUint32(ptr + 4 * i, add, true);
    }
    WASM_VECTOR_LEN = array.length;
    return ptr;
}

function passStringToWasm0(arg, malloc, realloc) {
    if (realloc === undefined) {
        const buf = cachedTextEncoder.encode(arg);
        const ptr = malloc(buf.length, 1) >>> 0;
        getUint8ArrayMemory0().subarray(ptr, ptr + buf.length).set(buf);
        WASM_VECTOR_LEN = buf.length;
        return ptr;
    }

    let len = arg.length;
    let ptr = malloc(len, 1) >>> 0;

    const mem = getUint8ArrayMemory0();

    let offset = 0;

    for (; offset < len; offset++) {
        const code = arg.charCodeAt(offset);
        if (code > 0x7F) break;
        mem[ptr + offset] = code;
    }
    if (offset !== len) {
        if (offset !== 0) {
            arg = arg.slice(offset);
        }
        ptr = realloc(ptr, len, len = offset + arg.length * 3, 1) >>> 0;
        const view = getUint8ArrayMemory0().subarray(ptr + offset, ptr + len);
        const ret = cachedTextEncoder.encodeInto(arg, view);

        offset += ret.written;
        ptr = realloc(ptr, len, offset, 1) >>> 0;
    }

    WASM_VECTOR_LEN = offset;
    return ptr;
}

function takeFromExternrefTable0(idx) {
    const value = wasm.__wbindgen_externrefs.get(idx);
    wasm.__externref_table_dealloc(idx);
    return value;
}

let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
cachedTextDecoder.decode();
const MAX_SAFARI_DECODE_BYTES = 2146435072;
let numBytesDecoded = 0;
function decodeText(ptr, len) {
    numBytesDecoded += len;
    if (numBytesDecoded >= MAX_SAFARI_DECODE_BYTES) {
        cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
        cachedTextDecoder.decode();
        numBytesDecoded = len;
    }
    return cachedTextDecoder.decode(getUint8ArrayMemory0().subarray(ptr, ptr + len));
}

const cachedTextEncoder = new TextEncoder();

if (!('encodeInto' in cachedTextEncoder)) {
    cachedTextEncoder.encodeInto = function (arg, view) {
        const buf = cachedTextEncoder.encode(arg);
        view.set(buf);
        return {
            read: arg.length,
            written: buf.length
        };
    };
}

let WASM_VECTOR_LEN = 0;

let wasmModule, wasm;
function __wbg_finalize_init(instance, module) {
    wasm = instance.exports;
    wasmModule = module;
    cachedDataViewMemory0 = null;
    cachedInt32ArrayMemory0 = null;
    cachedUint8ArrayMemory0 = null;
    wasm.__wbindgen_start();
    return wasm;
}

async function __wbg_load(module, imports) {
    if (typeof Response === 'function' && module instanceof Response) {
        if (typeof WebAssembly.instantiateStreaming === 'function') {
            try {
                return await WebAssembly.instantiateStreaming(module, imports);
            } catch (e) {
                const validResponse = module.ok && expectedResponseType(module.type);

                if (validResponse && module.headers.get('Content-Type') !== 'application/wasm') {
                    console.warn("`WebAssembly.instantiateStreaming` failed because your server does not serve Wasm with `application/wasm` MIME type. Falling back to `WebAssembly.instantiate` which is slower. Original error:\n", e);

                } else { throw e; }
            }
        }

        const bytes = await module.arrayBuffer();
        return await WebAssembly.instantiate(bytes, imports);
    } else {
        const instance = await WebAssembly.instantiate(module, imports);

        if (instance instanceof WebAssembly.Instance) {
            return { instance, module };
        } else {
            return instance;
        }
    }

    function expectedResponseType(type) {
        switch (type) {
            case 'basic': case 'cors': case 'default': return true;
        }
        return false;
    }
}

function initSync(module) {
    if (wasm !== undefined) return wasm;


    if (module !== undefined) {
        if (Object.getPrototypeOf(module) === Object.prototype) {
            ({module} = module)
        } else {
            console.warn('using deprecated parameters for `initSync()`; pass a single object instead')
        }
    }

    const imports = __wbg_get_imports();
    if (!(module instanceof WebAssembly.Module)) {
        module = new WebAssembly.Module(module);
    }
    const instance = new WebAssembly.Instance(module, imports);
    return __wbg_finalize_init(instance, module);
}

async function __wbg_init(module_or_path) {
    if (wasm !== undefined) return wasm;


    if (module_or_path !== undefined) {
        if (Object.getPrototypeOf(module_or_path) === Object.prototype) {
            ({module_or_path} = module_or_path)
        } else {
            console.warn('using deprecated parameters for the initialization function; pass a single object instead')
        }
    }

    if (module_or_path === undefined) {
        module_or_path = new URL('hydrogen_runtime_bg.wasm', import.meta.url);
    }
    const imports = __wbg_get_imports();

    if (typeof module_or_path === 'string' || (typeof Request === 'function' && module_or_path instanceof Request) || (typeof URL === 'function' && module_or_path instanceof URL)) {
        module_or_path = fetch(module_or_path);
    }

    const { instance, module } = await __wbg_load(await module_or_path, imports);

    return __wbg_finalize_init(instance, module);
}

export { initSync, __wbg_init as default };
