// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // color picker
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | ColorPicker component
// |
// | Interactive color selection with multiple input methods:
// | - HSL sliders (Hue 0-359, Saturation 0-100, Lightness 0-100)
// | - RGB sliders (Red 0-255, Green 0-255, Blue 0-255)
// | - Hex color input (#RRGGBB)
// | - Visual color wheel/square (future enhancement)
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.ColorPicker as ColorPicker
// | import Hydrogen.Schema.Color.HSL (hsl)
// |
// | ColorPicker.colorPicker
// |   [ ColorPicker.initialColor (hsl 210 80 50)
// |   , ColorPicker.onChange HandleColorChange
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_Component_Slider from "../Hydrogen.Component.Slider/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Color picker input mode
var ModeHSL = /* #__PURE__ */ (function () {
    function ModeHSL() {

    };
    ModeHSL.value = new ModeHSL();
    return ModeHSL;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Color picker input mode
var ModeRGB = /* #__PURE__ */ (function () {
    function ModeRGB() {

    };
    ModeRGB.value = new ModeRGB();
    return ModeRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Color picker input mode
var ModeHex = /* #__PURE__ */ (function () {
    function ModeHex() {

    };
    ModeHex.value = new ModeHex();
    return ModeHex;
})();

// | Render a readonly labeled slider
var renderSliderReadonly = function (label) {
    return function (minVal) {
        return function (maxVal) {
            return function (value) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-1" ]) ])([ Halogen_HTML_Elements.label([ Hydrogen_UI_Core.cls([ "text-sm font-medium" ]) ])([ Halogen_HTML_Core.text(label + (": " + show(value))) ]), Hydrogen_Component_Slider.slider([ Hydrogen_Component_Slider.value(Data_Int.toNumber(value)), Hydrogen_Component_Slider.min(Data_Int.toNumber(minVal)), Hydrogen_Component_Slider.max(Data_Int.toNumber(maxVal)), Hydrogen_Component_Slider.disabled(true) ]) ]);
            };
        };
    };
};

// | Render a labeled slider
var renderSlider = function (label) {
    return function (minVal) {
        return function (maxVal) {
            return function (value) {
                return function (handler) {
                    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-1" ]) ])([ Halogen_HTML_Elements.label([ Hydrogen_UI_Core.cls([ "text-sm font-medium" ]) ])([ Halogen_HTML_Core.text(label + (": " + show(value))) ]), Hydrogen_Component_Slider.slider([ Hydrogen_Component_Slider.value(Data_Int.toNumber(value)), Hydrogen_Component_Slider.min(Data_Int.toNumber(minVal)), Hydrogen_Component_Slider.max(Data_Int.toNumber(maxVal)), Hydrogen_Component_Slider.onChange(function (v) {
                        return handler(Data_Int.round(v));
                    }) ]) ]);
                };
            };
        };
    };
};

// | Set change handler
var onChange = function (handler) {
    return function (props) {
        return {
            color: props.color,
            mode: props.mode,
            className: props.className,
            onChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set color mode
var mode = function (m) {
    return function (props) {
        return {
            color: props.color,
            className: props.className,
            onChange: props.onChange,
            mode: m
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set initial color
var initialColor = function (c) {
    return function (props) {
        return {
            mode: props.mode,
            className: props.className,
            onChange: props.onChange,
            color: c
        };
    };
};
var eqColorMode = {
    eq: function (x) {
        return function (y) {
            if (x instanceof ModeHSL && y instanceof ModeHSL) {
                return true;
            };
            if (x instanceof ModeRGB && y instanceof ModeRGB) {
                return true;
            };
            if (x instanceof ModeHex && y instanceof ModeHex) {
                return true;
            };
            return false;
        };
    }
};

// | Default color picker properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        color: Hydrogen_Schema_Color_HSL.hsl(0)(0)(50),
        mode: ModeHSL.value,
        className: "",
        onChange: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // component
// ═══════════════════════════════════════════════════════════════════════════════
// | Render a color picker
var colorPicker = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var hslRec = Hydrogen_Schema_Color_HSL.hslToRecord(props.color);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "color-picker space-y-4 p-4 border border-white/20 rounded-lg", props.className ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "color-preview w-full h-16 rounded border border-white/20" ]), Halogen_HTML_Properties.style("background-color: " + Hydrogen_Schema_Color_HSL.toCss(props.color)) ])([  ]), (function () {
        if (props.onChange instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-2" ]) ])([ renderSliderReadonly("Hue")(0)(359)(hslRec.h), renderSliderReadonly("Saturation")(0)(100)(hslRec.s), renderSliderReadonly("Lightness")(0)(100)(hslRec.l) ]);
        };
        if (props.onChange instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-2" ]) ])([ renderSlider("Hue")(0)(359)(hslRec.h)(function (v) {
                return props.onChange.value0(Hydrogen_Schema_Color_HSL.hsl(v)(hslRec.s)(hslRec.l));
            }), renderSlider("Saturation")(0)(100)(hslRec.s)(function (v) {
                return props.onChange.value0(Hydrogen_Schema_Color_HSL.hsl(hslRec.h)(v)(hslRec.l));
            }), renderSlider("Lightness")(0)(100)(hslRec.l)(function (v) {
                return props.onChange.value0(Hydrogen_Schema_Color_HSL.hsl(hslRec.h)(hslRec.s)(v));
            }) ]);
        };
        throw new Error("Failed pattern match at Hydrogen.Component.ColorPicker (line 136, column 11 - line 146, column 16): " + [ props.onChange.constructor.name ]);
    })() ]);
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            color: props.color,
            mode: props.mode,
            onChange: props.onChange,
            className: props.className + (" " + c)
        };
    };
};
export {
    colorPicker,
    defaultProps,
    initialColor,
    onChange,
    mode,
    className,
    ModeHSL,
    ModeRGB,
    ModeHex,
    eqColorMode
};
