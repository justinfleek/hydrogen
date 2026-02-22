// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                // hydrogen // schema // color // white balance
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | WhiteBalance - temperature and tint correction for color grading.
// |
// | **PROFESSIONAL COLOR CORRECTION:**
// | White balance adjusts the color temperature and tint of an image to
// | compensate for lighting conditions. Essential for:
// | - Video color grading (LATTICE)
// | - Photo processing (COMPASS)
// | - Consistent color across different lighting
// | - Correcting color cast
// |
// | **Two-axis control:**
// | - **Temperature** - Blue ↔ Orange (measured in Kelvin shift)
// | - **Tint** - Green ↔ Magenta (corrects fluorescent/mixed lighting)
// |
// | **Common scenarios:**
// | - Shot under tungsten (3200K), needs daylight correction → +2300K shift
// | - Fluorescent green cast → +20 tint (toward magenta)
// | - Shade has blue cast → -500K shift (toward warm)
// |
// | **Standard presets:**
// | - Daylight: 5500K, 0 tint
// | - Tungsten: 3200K, 0 tint
// | - Fluorescent: 4000K, +10 tint (magenta to counter green)
// | - Flash: 5500K, 0 tint
// | - Cloudy: 6500K, 0 tint
// | - Shade: 7500K, +10 tint
// |
// | **Integration:**
// | Part of the ColorGrading compound - applied before ColorWheels and Curves.
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var AsShot = /* #__PURE__ */ (function () {
    function AsShot() {

    };
    AsShot.value = new AsShot();
    return AsShot;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Auto = /* #__PURE__ */ (function () {
    function Auto() {

    };
    Auto.value = new Auto();
    return Auto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Daylight = /* #__PURE__ */ (function () {
    function Daylight() {

    };
    Daylight.value = new Daylight();
    return Daylight;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Cloudy = /* #__PURE__ */ (function () {
    function Cloudy() {

    };
    Cloudy.value = new Cloudy();
    return Cloudy;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Shade = /* #__PURE__ */ (function () {
    function Shade() {

    };
    Shade.value = new Shade();
    return Shade;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Tungsten = /* #__PURE__ */ (function () {
    function Tungsten() {

    };
    Tungsten.value = new Tungsten();
    return Tungsten;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Fluorescent = /* #__PURE__ */ (function () {
    function Fluorescent() {

    };
    Fluorescent.value = new Fluorescent();
    return Fluorescent;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Flash = /* #__PURE__ */ (function () {
    function Flash() {

    };
    Flash.value = new Flash();
    return Flash;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard white balance presets
var Custom = /* #__PURE__ */ (function () {
    function Custom(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Custom.create = function (value0) {
        return function (value1) {
            return new Custom(value0, value1);
        };
    };
    return Custom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create white balance adjustment
// |
// | ```purescript
// | whiteBalance 500 10   -- +500K warmer, +10 magenta tint
// | whiteBalance (-200) 0 -- -200K cooler, neutral tint
// | ```
var whiteBalance = function (temp) {
    return function (tintVal) {
        var clampTint = function (t) {
            if (t < (-100 | 0)) {
                return -100 | 0;
            };
            if (t > 100) {
                return 100;
            };
            if (Data_Boolean.otherwise) {
                return t;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.WhiteBalance (line 117, column 5 - line 120, column 22): " + [ t.constructor.name ]);
        };
        var clampTemp = function (t) {
            if (t < (-5000 | 0)) {
                return -5000 | 0;
            };
            if (t > 5000) {
                return 5000;
            };
            if (Data_Boolean.otherwise) {
                return t;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.WhiteBalance (line 112, column 5 - line 115, column 22): " + [ t.constructor.name ]);
        };
        return {
            temperature: clampTemp(temp),
            tint: clampTint(tintVal)
        };
    };
};

// | Update temperature
var withTemperature = function (newTemp) {
    return function (wb) {
        return whiteBalance(newTemp)(wb.tint);
    };
};

// | Update tint
var withTint = function (newTint) {
    return function (wb) {
        return whiteBalance(wb.temperature)(newTint);
    };
};

// | Get tint correction
var tint = function (wb) {
    return wb.tint;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Get temperature shift
var temperature = function (wb) {
    return wb.temperature;
};
var showPreset = {
    show: function (v) {
        if (v instanceof AsShot) {
            return "As Shot";
        };
        if (v instanceof Auto) {
            return "Auto";
        };
        if (v instanceof Daylight) {
            return "Daylight";
        };
        if (v instanceof Cloudy) {
            return "Cloudy";
        };
        if (v instanceof Shade) {
            return "Shade";
        };
        if (v instanceof Tungsten) {
            return "Tungsten";
        };
        if (v instanceof Fluorescent) {
            return "Fluorescent";
        };
        if (v instanceof Flash) {
            return "Flash";
        };
        if (v instanceof Custom) {
            return "Custom (" + (show(v.value0) + ("K, " + (show(v.value1) + " tint)")));
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.WhiteBalance (line 85, column 10 - line 94, column 70): " + [ v.constructor.name ]);
    }
};

// | Create from preset
// |
// | ```purescript
// | fromPreset Daylight      -- 5500K
// | fromPreset Tungsten      -- 3200K
// | fromPreset (Custom 6000 5) -- Custom values
// | ```
var fromPreset = function (v) {
    if (v instanceof AsShot) {
        return whiteBalance(0)(0);
    };
    if (v instanceof Auto) {
        return whiteBalance(0)(0);
    };
    if (v instanceof Daylight) {
        return whiteBalance(0)(0);
    };
    if (v instanceof Cloudy) {
        return whiteBalance(1000)(0);
    };
    if (v instanceof Shade) {
        return whiteBalance(2000)(10);
    };
    if (v instanceof Tungsten) {
        return whiteBalance(-2300 | 0)(0);
    };
    if (v instanceof Fluorescent) {
        return whiteBalance(-1500 | 0)(10);
    };
    if (v instanceof Flash) {
        return whiteBalance(0)(0);
    };
    if (v instanceof Custom) {
        return whiteBalance(v.value0)(v.value1);
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.WhiteBalance (line 130, column 14 - line 139, column 33): " + [ v.constructor.name ]);
};
var eqPreset = {
    eq: function (x) {
        return function (y) {
            if (x instanceof AsShot && y instanceof AsShot) {
                return true;
            };
            if (x instanceof Auto && y instanceof Auto) {
                return true;
            };
            if (x instanceof Daylight && y instanceof Daylight) {
                return true;
            };
            if (x instanceof Cloudy && y instanceof Cloudy) {
                return true;
            };
            if (x instanceof Shade && y instanceof Shade) {
                return true;
            };
            if (x instanceof Tungsten && y instanceof Tungsten) {
                return true;
            };
            if (x instanceof Fluorescent && y instanceof Fluorescent) {
                return true;
            };
            if (x instanceof Flash && y instanceof Flash) {
                return true;
            };
            if (x instanceof Custom && y instanceof Custom) {
                return x.value0 === y.value0 && x.value1 === y.value1;
            };
            return false;
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Apply white balance to RGB color
// |
// | Algorithm:
// | 1. Apply temperature shift (blue-orange axis)
// | 2. Apply tint correction (green-magenta axis)
// | 3. Normalize to maintain overall brightness
// |
// | ```purescript
// | applyToRgb (whiteBalance 500 10) rgbColor
// | ```
var applyToRgb = function (wb) {
    return function (rgb) {
        var clamp = function (min$prime) {
            return function (max$prime) {
                return function (val) {
                    if (val < min$prime) {
                        return min$prime;
                    };
                    if (val > max$prime) {
                        return max$prime;
                    };
                    if (Data_Boolean.otherwise) {
                        return val;
                    };
                    throw new Error("Failed pattern match at Hydrogen.Schema.Color.WhiteBalance (line 196, column 5 - line 199, column 24): " + [ min$prime.constructor.name, max$prime.constructor.name, val.constructor.name ]);
                };
            };
        };
        
        // Tint adjustment (green-magenta axis)
        // Positive tint = more magenta (more red+blue, less green)
        // Negative tint = more green
var tintFactor = Data_Int.toNumber(wb.tint) / 100.0;
        
        // Temperature adjustment (Kelvin shift affects blue-orange)
        // Positive temp = warmer (more red/orange, less blue)
        // Negative temp = cooler (less red, more blue)
var tempFactor = Data_Int.toNumber(wb.temperature) / 5000.0;
        var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb)));
        var rTemp = r + tempFactor * 50.0;
        var rTint = rTemp + tintFactor * 20.0;
        
        // Clamp to valid range
var rFinal = Data_Int.round(clamp(0.0)(255.0)(rTint));
        var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb)));
        var gTint = g - tintFactor * 40.0;
        var gFinal = Data_Int.round(clamp(0.0)(255.0)(gTint));
        var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb)));
        var bTemp = b - tempFactor * 50.0;
        var bTint = bTemp + tintFactor * 20.0;
        var bFinal = Data_Int.round(clamp(0.0)(255.0)(bTint));
        return Hydrogen_Schema_Color_RGB.rgb(rFinal)(gFinal)(bFinal);
    };
};
export {
    AsShot,
    Auto,
    Daylight,
    Cloudy,
    Shade,
    Tungsten,
    Fluorescent,
    Flash,
    Custom,
    whiteBalance,
    fromPreset,
    temperature,
    tint,
    applyToRgb,
    withTemperature,
    withTint,
    eqPreset,
    showPreset
};
