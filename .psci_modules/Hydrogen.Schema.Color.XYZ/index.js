// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // xyz
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | XYZ - CIE 1931 XYZ color space (device-independent).
// |
// | **FOUNDATION OF COLOR SCIENCE:**
// | XYZ is THE fundamental color space in professional color management.
// | Created by the International Commission on Illumination (CIE) in 1931,
// | it's based on how human cone cells actually respond to light.
// |
// | **Why XYZ exists:**
// | RGB is device-dependent - same RGB values look different on different screens.
// | XYZ is device-independent - same XYZ values produce the same perceived color
// | on any calibrated device. This is why every ICC color profile uses XYZ.
// |
// | **Components (Tristimulus values):**
// | - **X**: Roughly corresponds to red-green (0.0-0.95047 for D65 white)
// | - **Y**: Luminance/brightness (0.0-1.0, where 1.0 = perfect white)
// | - **Z**: Roughly corresponds to blue-yellow (0.0-1.08883 for D65 white)
// |
// | **White point:**
// | This module uses D65 illuminant (standard for sRGB displays):
// | - X = 0.95047
// | - Y = 1.00000
// | - Z = 1.08883
// |
// | **The conversion bridge:**
// | You CANNOT convert RGB ↔ LAB directly. The path is:
// | ```
// | RGB → XYZ → LAB → LCH
// | LCH → LAB → XYZ → RGB
// | ```
// |
// | **Use cases:**
// | - ICC color profile conversions
// | - Cross-device color matching
// | - Professional color management
// | - Scientific color measurements
// | - Accurate color space transformations
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// | Z component (tristimulus value): 0.0-1.08883 (D65 white)
// | Roughly corresponds to blue-yellow axis
var ZComponent = function (x) {
    return x;
};

// | Y component (tristimulus value): 0.0-1.0
// | Represents luminance (brightness). Y=1.0 is perfect white.
var YComponent = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // atoms
// ═══════════════════════════════════════════════════════════════════════════════
// | X component (tristimulus value): 0.0-0.95047 (D65 white)
// | Roughly corresponds to red-green axis
var XComponent = function (x) {
    return x;
};

// | Create Z value (clamped 0.0-1.3 for safety, though D65 white is 1.08883)
var zValue = function (n) {
    if (n < 0.0) {
        return 0.0;
    };
    if (n > 1.3) {
        return 1.3;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.XYZ (line 121, column 1 - line 121, column 31): " + [ n.constructor.name ]);
};

// | Get Z component
var zComponent = function (color) {
    return color.z;
};

// | Create Y value (clamped 0.0-1.0)
var yValue = function (n) {
    if (n < 0.0) {
        return 0.0;
    };
    if (n > 1.0) {
        return 1.0;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.XYZ (line 101, column 1 - line 101, column 31): " + [ n.constructor.name ]);
};

// | Get Y component (luminance)
var yComponent = function (color) {
    return color.y;
};

// | Create X value (clamped 0.0-1.2 for safety, though D65 white is 0.95047)
var xValue = function (n) {
    if (n < 0.0) {
        return 0.0;
    };
    if (n > 1.2) {
        return 1.2;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.XYZ (line 81, column 1 - line 81, column 31): " + [ n.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create XYZ color from tristimulus values
// |
// | ```purescript
// | xyz 0.95047 1.0 1.08883  -- D65 white point
// | xyz 0.0 0.0 0.0          -- Black
// | xyz 0.41246 0.21267 0.01933  -- Pure sRGB red
// | ```
var xyz = function (x) {
    return function (y) {
        return function (z) {
            return {
                x: xValue(x),
                y: yValue(y),
                z: zValue(z)
            };
        };
    };
};

// | Create from record
var xyzFromRecord = function (v) {
    return xyz(v.x)(v.y)(v.z);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Get X component
var xComponent = function (color) {
    return color.x;
};
var unwrapZ = function (v) {
    return v;
};
var unwrapY = function (v) {
    return v;
};
var unwrapX = function (v) {
    return v;
};

// | Convert to record - explicitly named for backend persistence
var xyzToRecord = function (color) {
    return {
        x: unwrapX(color.x),
        y: unwrapY(color.y),
        z: unwrapZ(color.z)
    };
};

// | Generic alias for xyzToRecord
var toRecord = xyzToRecord;
var showZComponent = {
    show: function (v) {
        return "Z " + show(v);
    }
};
var showYComponent = {
    show: function (v) {
        return "Y " + show(v);
    }
};
var showXComponent = {
    show: function (v) {
        return "X " + show(v);
    }
};
var eqZComponent = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordZComponent = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqZComponent;
    }
};
var eqYComponent = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordYComponent = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqYComponent;
    }
};
var eqXComponent = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordXComponent = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqXComponent;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // white point
// ═══════════════════════════════════════════════════════════════════════════════
// | D65 white point (standard daylight illuminant for sRGB)
// |
// | Used as reference white for RGB ↔ XYZ ↔ LAB conversions.
// | These are the XYZ values that correspond to pure white (RGB 255, 255, 255).
// |
// | ```purescript
// | d65White  -- { x: 0.95047, y: 1.0, z: 1.08883 }
// | ```
var d65White = /* #__PURE__ */ xyz(0.95047)(1.0)(1.08883);
export {
    xyz,
    xyzFromRecord,
    xComponent,
    yComponent,
    zComponent,
    xyzToRecord,
    toRecord,
    d65White,
    eqXComponent,
    ordXComponent,
    showXComponent,
    eqYComponent,
    ordYComponent,
    showYComponent,
    eqZComponent,
    ordZComponent,
    showZComponent
};
