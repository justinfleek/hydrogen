// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                              // hydrogen // schema // bounded
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Bounded numeric primitives - the foundation of the ontology.
// |
// | Every value in the design system has semantic meaning AND valid bounds.
// | A hue is 0-359. A saturation is 0-100. A channel is 0-255. These are
// | not interchangeable, and the type system enforces this.
// |
// | ## Design Philosophy
// |
// | We do NOT use phantom types or type-level naturals here. Instead:
// | - Each domain gets its own newtype (Hue, Saturation, Channel, etc.)
// | - Smart constructors clamp or validate at construction time
// | - The `Bounds` record documents valid ranges for serialization/UI
// |
// | This keeps the types simple, serializable, and comprehensible to both
// | humans and AI agents consuming the schema.
import * as Data_Boolean from "../Data.Boolean/index.js";

// | Check if a number is within bounds
var inBoundsNumber = function (minVal) {
    return function (maxVal) {
        return function (n) {
            return n >= minVal && n <= maxVal;
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // validation
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if an integer is within bounds
var inBoundsInt = function (minVal) {
    return function (maxVal) {
        return function (n) {
            return n >= minVal && n <= maxVal;
        };
    };
};

// | Clamp a number to bounds
var clampNumber = function (minVal) {
    return function (maxVal) {
        return function (n) {
            if (n < minVal) {
                return minVal;
            };
            if (n > maxVal) {
                return maxVal;
            };
            if (Data_Boolean.otherwise) {
                return n;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Bounded (line 101, column 1 - line 101, column 52): " + [ minVal.constructor.name, maxVal.constructor.name, n.constructor.name ]);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // clamping
// ═══════════════════════════════════════════════════════════════════════════════
// | Clamp an integer to bounds
var clampInt = function (minVal) {
    return function (maxVal) {
        return function (n) {
            if (n < minVal) {
                return minVal;
            };
            if (n > maxVal) {
                return maxVal;
            };
            if (Data_Boolean.otherwise) {
                return n;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Bounded (line 94, column 1 - line 94, column 37): " + [ minVal.constructor.name, maxVal.constructor.name, n.constructor.name ]);
        };
    };
};

// | Create bounds documentation
var bounds = function (min$prime) {
    return function (max$prime) {
        return function (name$prime) {
            return function (desc) {
                return {
                    min: min$prime,
                    max: max$prime,
                    name: name$prime,
                    description: desc
                };
            };
        };
    };
};

// | Create integer bounds
var intBounds = bounds;

// | Byte bounds (0-255)
var $$byte = /* #__PURE__ */ intBounds(0)(255)("byte")("8-bit unsigned integer from 0 to 255");

// | Degree bounds (0-359)
// | Note: 360 wraps to 0, so valid range is 0-359
var degrees = /* #__PURE__ */ intBounds(0)(359)("degrees")("Angle in degrees from 0 to 359");

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // common bounds
// ═══════════════════════════════════════════════════════════════════════════════
// | Percentage bounds (0-100)
var percent = /* #__PURE__ */ intBounds(0)(100)("percent")("Integer percentage from 0 to 100");

// | Create number bounds
var numberBounds = bounds;

// | Normalized bounds (0.0-1.0)
// | Alias for unit, more descriptive in some contexts
var normalized = /* #__PURE__ */ numberBounds(0.0)(1.0)("normalized")("Normalized value from 0.0 to 1.0");

// | Unit interval bounds (0.0-1.0)
var unit = /* #__PURE__ */ numberBounds(0.0)(1.0)("unit")("Normalized value from 0.0 to 1.0");
export {
    bounds,
    intBounds,
    numberBounds,
    clampInt,
    clampNumber,
    inBoundsInt,
    inBoundsNumber,
    percent,
    unit,
    $$byte as byte,
    degrees,
    normalized
};
