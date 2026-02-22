// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // channel
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Channel - a single RGB color channel.
// |
// | An 8-bit unsigned value from 0 to 255:
// | - **0**: No contribution from this channel
// | - **128**: Half intensity
// | - **255**: Full intensity
// |
// | RGB colors are composed of three channels: red, green, and blue.
// | Each channel contributes light to the final perceived color.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // channel
// ═══════════════════════════════════════════════════════════════════════════════
// | RGB channel value (0-255)
// |
// | Represents the intensity of a single color component (red, green, or blue)
// | in the standard 8-bit per channel color model.
var Channel = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a channel without clamping
// |
// | Use only when you know the value is valid.
var unsafeChannel = Channel;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 255.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showChannel = {
    show: function (v) {
        return show(v);
    }
};

// | Invert channel (255 - value)
var invert = function (v) {
    return 255 - v | 0;
};
var eqChannel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordChannel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqChannel;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a channel, clamping to 0-255
var channel = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(255)(n);
};

// | Create a channel from unit interval (0.0-1.0)
var fromUnitInterval = function (n) {
    return channel(Data_Int.round(Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(n) * 255.0));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale channel by a factor
var scale = function (factor) {
    return function (v) {
        return channel(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(255)("channel")("8-bit color channel intensity");

// | Blend two channels with weight (0.0 = all first, 1.0 = all second)
var blend = function (weight) {
    return function (v) {
        return function (v1) {
            var w = Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(weight);
            var result = Data_Int.toNumber(v) * (1.0 - w) + Data_Int.toNumber(v1) * w;
            return channel(Data_Int.round(result));
        };
    };
};

// | Add two channels (clamped)
var add = function (v) {
    return function (v1) {
        return channel(v + v1 | 0);
    };
};
export {
    channel,
    unsafeChannel,
    unwrap,
    scale,
    invert,
    add,
    blend,
    bounds,
    toNumber,
    toUnitInterval,
    fromUnitInterval,
    eqChannel,
    ordChannel,
    showChannel
};
