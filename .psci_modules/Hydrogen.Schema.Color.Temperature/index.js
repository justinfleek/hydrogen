// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                    // hydrogen // schema // color // temperature
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color temperature - warm/cool/neutral classification.
// |
// | Temperature affects emotional perception:
// | - **Warm**: Reds, oranges, yellows - energizing, inviting
// | - **Cool**: Blues, greens, purples - calming, professional
// | - **Neutral**: Balanced colors, low saturation grays
// |
// | Also provides Kelvin-based temperature for light sources.
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color temperature
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived color temperature
var VeryCool = /* #__PURE__ */ (function () {
    function VeryCool() {

    };
    VeryCool.value = new VeryCool();
    return VeryCool;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color temperature
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived color temperature
var Cool = /* #__PURE__ */ (function () {
    function Cool() {

    };
    Cool.value = new Cool();
    return Cool;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color temperature
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived color temperature
var Neutral = /* #__PURE__ */ (function () {
    function Neutral() {

    };
    Neutral.value = new Neutral();
    return Neutral;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color temperature
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived color temperature
var Warm = /* #__PURE__ */ (function () {
    function Warm() {

    };
    Warm.value = new Warm();
    return Warm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color temperature
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived color temperature
var VeryWarm = /* #__PURE__ */ (function () {
    function VeryWarm() {

    };
    VeryWarm.value = new VeryWarm();
    return VeryWarm;
})();

// | Determine the perceived temperature of an HSL color
var temperatureFromHSL = function (color) {
    var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
    var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(color));
    var $8 = s < 10;
    if ($8) {
        return Neutral.value;
    };
    var $9 = h >= 0 && h < 30;
    if ($9) {
        return VeryWarm.value;
    };
    var $10 = h >= 30 && h < 90;
    if ($10) {
        return Warm.value;
    };
    var $11 = h >= 90 && h < 150;
    if ($11) {
        return Neutral.value;
    };
    var $12 = h >= 150 && h < 210;
    if ($12) {
        return Cool.value;
    };
    var $13 = h >= 210 && h < 270;
    if ($13) {
        return VeryCool.value;
    };
    var $14 = h >= 270 && h < 330;
    if ($14) {
        return Cool.value;
    };
    return VeryWarm.value;
};
var showTemperature = {
    show: function (v) {
        if (v instanceof VeryCool) {
            return "Very Cool";
        };
        if (v instanceof Cool) {
            return "Cool";
        };
        if (v instanceof Neutral) {
            return "Neutral";
        };
        if (v instanceof Warm) {
            return "Warm";
        };
        if (v instanceof VeryWarm) {
            return "Very Warm";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Temperature (line 42, column 10 - line 47, column 28): " + [ v.constructor.name ]);
    }
};

// | Color temperature in Kelvin (for light sources)
// |
// | Reference points:
// | - 1000K = candlelight
// | - 2700K = incandescent bulb
// | - 3000K = warm white LED
// | - 4000K = neutral white
// | - 5500K = daylight
// | - 6500K = overcast sky
// | - 10000K = blue sky
var kelvin = function (k) {
    if (k < 3000) {
        return VeryWarm.value;
    };
    if (k < 4000) {
        return Warm.value;
    };
    if (k < 5500) {
        return Neutral.value;
    };
    if (k < 7000) {
        return Cool.value;
    };
    if (Data_Boolean.otherwise) {
        return VeryCool.value;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Temperature (line 74, column 1 - line 74, column 29): " + [ k.constructor.name ]);
};
var eqTemperature = {
    eq: function (x) {
        return function (y) {
            if (x instanceof VeryCool && y instanceof VeryCool) {
                return true;
            };
            if (x instanceof Cool && y instanceof Cool) {
                return true;
            };
            if (x instanceof Neutral && y instanceof Neutral) {
                return true;
            };
            if (x instanceof Warm && y instanceof Warm) {
                return true;
            };
            if (x instanceof VeryWarm && y instanceof VeryWarm) {
                return true;
            };
            return false;
        };
    }
};
var ordTemperature = {
    compare: function (x) {
        return function (y) {
            if (x instanceof VeryCool && y instanceof VeryCool) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof VeryCool) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof VeryCool) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Cool && y instanceof Cool) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Cool) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Cool) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Neutral && y instanceof Neutral) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Neutral) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Neutral) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Warm && y instanceof Warm) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Warm) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Warm) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof VeryWarm && y instanceof VeryWarm) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.Temperature (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqTemperature;
    }
};
export {
    VeryCool,
    Cool,
    Neutral,
    Warm,
    VeryWarm,
    temperatureFromHSL,
    kelvin,
    eqTemperature,
    ordTemperature,
    showTemperature
};
