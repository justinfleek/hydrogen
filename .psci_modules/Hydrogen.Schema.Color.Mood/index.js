// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // hydrogen // schema // color // mood
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color psychology - emotional associations.
// |
// | Colors evoke psychological responses:
// | - **Energetic**: Bright, warm, saturated - excitement, urgency
// | - **Calm**: Cool, desaturated, light - relaxation, trust
// | - **Professional**: Neutral, balanced - competence, reliability
// | - **Luxurious**: Deep, rich, dark - elegance, exclusivity
import * as Data_Eq from "../Data.Eq/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";
import * as Hydrogen_Schema_Color_Temperature from "../Hydrogen.Schema.Color.Temperature/index.js";
var eq = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Temperature.eqTemperature);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Energetic = /* #__PURE__ */ (function () {
    function Energetic() {

    };
    Energetic.value = new Energetic();
    return Energetic;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Calm = /* #__PURE__ */ (function () {
    function Calm() {

    };
    Calm.value = new Calm();
    return Calm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Professional = /* #__PURE__ */ (function () {
    function Professional() {

    };
    Professional.value = new Professional();
    return Professional;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Playful = /* #__PURE__ */ (function () {
    function Playful() {

    };
    Playful.value = new Playful();
    return Playful;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Luxurious = /* #__PURE__ */ (function () {
    function Luxurious() {

    };
    Luxurious.value = new Luxurious();
    return Luxurious;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Natural = /* #__PURE__ */ (function () {
    function Natural() {

    };
    Natural.value = new Natural();
    return Natural;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Dramatic = /* #__PURE__ */ (function () {
    function Dramatic() {

    };
    Dramatic.value = new Dramatic();
    return Dramatic;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color psychology
// ═══════════════════════════════════════════════════════════════════════════════
// | Psychological/emotional associations
var Soft = /* #__PURE__ */ (function () {
    function Soft() {

    };
    Soft.value = new Soft();
    return Soft;
})();
var showMood = {
    show: function (v) {
        if (v instanceof Energetic) {
            return "Energetic";
        };
        if (v instanceof Calm) {
            return "Calm";
        };
        if (v instanceof Professional) {
            return "Professional";
        };
        if (v instanceof Playful) {
            return "Playful";
        };
        if (v instanceof Luxurious) {
            return "Luxurious";
        };
        if (v instanceof Natural) {
            return "Natural";
        };
        if (v instanceof Dramatic) {
            return "Dramatic";
        };
        if (v instanceof Soft) {
            return "Soft";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Mood (line 45, column 10 - line 53, column 19): " + [ v.constructor.name ]);
    }
};

// | Infer mood from an HSL color
// |
// | This is a heuristic based on color properties:
// | - Temperature (warm/cool)
// | - Saturation (vivid/muted)
// | - Lightness (light/dark)
var moodFromHSL = function (color) {
    var temp = Hydrogen_Schema_Color_Temperature.temperatureFromHSL(color);
    var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
    var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(color));
    var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(color));
    var $12 = s < 20;
    if ($12) {
        return Professional.value;
    };
    var $13 = l > 80 && s < 50;
    if ($13) {
        return Soft.value;
    };
    var $14 = l < 30;
    if ($14) {
        return Luxurious.value;
    };
    var $15 = eq(temp)(Hydrogen_Schema_Color_Temperature.Warm.value) || eq(temp)(Hydrogen_Schema_Color_Temperature.VeryWarm.value);
    if ($15) {
        var $16 = s > 70;
        if ($16) {
            return Energetic.value;
        };
        return Playful.value;
    };
    var $17 = eq(temp)(Hydrogen_Schema_Color_Temperature.Cool.value) || eq(temp)(Hydrogen_Schema_Color_Temperature.VeryCool.value);
    if ($17) {
        var $18 = s < 50;
        if ($18) {
            return Calm.value;
        };
        return Dramatic.value;
    };
    var $19 = h >= 60 && h <= 180;
    if ($19) {
        return Natural.value;
    };
    return Professional.value;
};

// | Describe the mood for UI/documentation
var moodDescription = function (v) {
    if (v instanceof Energetic) {
        return "Exciting, urgent, attention-grabbing";
    };
    if (v instanceof Calm) {
        return "Relaxing, trustworthy, serene";
    };
    if (v instanceof Professional) {
        return "Competent, reliable, corporate";
    };
    if (v instanceof Playful) {
        return "Fun, youthful, creative";
    };
    if (v instanceof Luxurious) {
        return "Elegant, exclusive, premium";
    };
    if (v instanceof Natural) {
        return "Organic, earthy, sustainable";
    };
    if (v instanceof Dramatic) {
        return "Bold, powerful, impactful";
    };
    if (v instanceof Soft) {
        return "Gentle, delicate, approachable";
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Mood (line 57, column 19 - line 65, column 43): " + [ v.constructor.name ]);
};
var eqMood = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Energetic && y instanceof Energetic) {
                return true;
            };
            if (x instanceof Calm && y instanceof Calm) {
                return true;
            };
            if (x instanceof Professional && y instanceof Professional) {
                return true;
            };
            if (x instanceof Playful && y instanceof Playful) {
                return true;
            };
            if (x instanceof Luxurious && y instanceof Luxurious) {
                return true;
            };
            if (x instanceof Natural && y instanceof Natural) {
                return true;
            };
            if (x instanceof Dramatic && y instanceof Dramatic) {
                return true;
            };
            if (x instanceof Soft && y instanceof Soft) {
                return true;
            };
            return false;
        };
    }
};
export {
    Energetic,
    Calm,
    Professional,
    Playful,
    Luxurious,
    Natural,
    Dramatic,
    Soft,
    moodFromHSL,
    moodDescription,
    eqMood,
    showMood
};
