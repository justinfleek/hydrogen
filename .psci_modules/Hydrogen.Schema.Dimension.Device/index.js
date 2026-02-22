// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                   // hydrogen // schema // dimension // device
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Device-dependent units - measurements that depend on display hardware.
// |
// | A pixel has no inherent physical size. A "1920px" image could be:
// | - 20 inches wide on a 96 PPI monitor
// | - 13 inches wide on a 144 PPI laptop
// | - 200 inches wide on a projector
// |
// | ## Unit Distinctions
// |
// | - **DevicePixel**: Actual hardware pixels on the display
// | - **CSSPixel**: Reference pixel at 96 PPI (CSS spec)
// | - **Pixel**: Generic discrete pixel (context determines meaning)
// |
// | ## Conversion Requires Context
// |
// | To convert between device units and physical units, you need:
// | - PPI (pixels per inch) of the display
// | - Device pixel ratio (for HiDPI/Retina displays)
// |
// | See `Dimension.Context` for conversion functions.
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// | Scaled pixel (Android sp)
// | Like dp, but also scales with user's font size preference
// | Used for text to respect accessibility settings
var ScaledPixel = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // display properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Pixels per inch - the density of a display
// | This is what bridges device pixels to physical inches
// | Also known as DPI (dots per inch) in print contexts
var PixelsPerInch = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // pixel types
// ═══════════════════════════════════════════════════════════════════════════════
// | Generic pixel - a discrete unit on some display
// | The physical size depends entirely on the display's PPI
var Pixel = function (x) {
    return x;
};

// | Device pixel ratio - ratio of device pixels to CSS pixels
// | Standard displays: 1.0
// | Retina displays: 2.0
// | Retina HD: 3.0
// | Some Android devices: 1.5, 2.5, etc.
var DevicePixelRatio = function (x) {
    return x;
};

// | Device pixel - actual hardware pixel on the display
// | On a Retina display, 1 CSS pixel = 2 device pixels
var DevicePixel = function (x) {
    return x;
};

// | Density-independent pixel (Android dp)
// | 1 dp = 1 pixel at 160 PPI (mdpi baseline)
// | Scales proportionally: at 320 PPI (xhdpi), 1 dp = 2 pixels
var DensityIndependentPixel = function (x) {
    return x;
};

// | CSS pixel - reference pixel defined at 96 PPI
// | This is what web browsers use by default
// | 1 CSS inch = 96 CSS pixels (regardless of actual display)
var CSSPixel = function (x) {
    return x;
};

// | Extract the raw Number from a ScaledPixel
var unwrapSp = function (v) {
    return v;
};

// | Extract the raw Number from a PixelsPerInch
var unwrapPpi = function (v) {
    return v;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Number from a Pixel
var unwrapPixel = function (v) {
    return v;
};

// | Extract the raw Number from a DevicePixelRatio
var unwrapDpr = function (v) {
    return v;
};

// | Extract the raw Number from a DensityIndependentPixel
var unwrapDp = function (v) {
    return v;
};

// | Extract the raw Number from a DevicePixel
var unwrapDevicePixel = function (v) {
    return v;
};

// | Extract the raw Number from a CSSPixel
var unwrapCSSPixel = function (v) {
    return v;
};

// | Subtract two Pixel values
var subtractPx = function (v) {
    return function (v1) {
        return v - v1;
    };
};

// | Create a ScaledPixel value
var sp = ScaledPixel;
var showScaledPixel = {
    show: function (v) {
        return show(v) + "sp";
    }
};
var showPixelsPerInch = {
    show: function (v) {
        return show(v) + " PPI";
    }
};
var showPixel = {
    show: function (v) {
        return show(v) + "px";
    }
};
var showDevicePixelRatio = {
    show: function (v) {
        return show(v) + "x";
    }
};
var showDevicePixel = {
    show: function (v) {
        return show(v) + "dpx";
    }
};
var showDensityIndependentPixel = {
    show: function (v) {
        return show(v) + "dp";
    }
};
var showCSSPixel = {
    show: function (v) {
        return show(v) + "px (CSS)";
    }
};
var semiringPixel = {
    add: function (v) {
        return function (v1) {
            return v + v1;
        };
    },
    zero: 0.0,
    mul: function (v) {
        return function (v1) {
            return v * v1;
        };
    },
    one: 1.0
};

// | Scale a Pixel value by a dimensionless factor
var scalePx = function (factor) {
    return function (v) {
        return v * factor;
    };
};
var ringPixel = {
    sub: function (v) {
        return function (v1) {
            return v - v1;
        };
    },
    Semiring0: function () {
        return semiringPixel;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a Pixel value
var px = Pixel;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // common display densities
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard desktop monitor (96 PPI)
// | This is the CSS reference density
var ppiStandard = 96.0;

// | Apple Retina HD display (~326-458 PPI)
// | iPhone Plus/Max models
var ppiRetinaHD = 326.0;

// | Apple Retina display (~220-230 PPI)
// | iPhone 4 was 326 PPI, MacBook Pro is ~220 PPI
var ppiRetina = 220.0;

// | High quality print at 600 DPI
var ppiPrint600 = 600.0;

// | Print quality at 300 DPI
var ppiPrint300 = 300.0;

// | 4K UHD at typical monitor sizes (~163-185 PPI)
var ppi4K = 163.0;

// | Create a PixelsPerInch value
var ppi = PixelsPerInch;

// | Negate a Pixel value
var negatePx = function (v) {
    return -v;
};
var eqScaledPixel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordScaledPixel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqScaledPixel;
    }
};
var eqPixelsPerInch = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordPixelsPerInch = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqPixelsPerInch;
    }
};
var eqPixel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordPixel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqPixel;
    }
};
var eqDevicePixelRatio = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordDevicePixelRatio = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqDevicePixelRatio;
    }
};
var eqDevicePixel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordDevicePixel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqDevicePixel;
    }
};
var eqDensityIndependentPixel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordDensityIndependentPixel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqDensityIndependentPixel;
    }
};
var eqCSSPixel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordCSSPixel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqCSSPixel;
    }
};

// | Create a DevicePixelRatio value
var dpr = DevicePixelRatio;

// | Create a DensityIndependentPixel value
var dp = DensityIndependentPixel;

// | Create a DevicePixel value
var devicePx = DevicePixel;

// | Create a CSSPixel value
var cssPx = CSSPixel;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Add two Pixel values
var addPx = function (v) {
    return function (v1) {
        return v + v1;
    };
};

// | Absolute value of a Pixel
var absPx = function (v) {
    return Hydrogen_Math_Core.abs(v);
};
export {
    Pixel,
    DevicePixel,
    CSSPixel,
    DensityIndependentPixel,
    ScaledPixel,
    PixelsPerInch,
    DevicePixelRatio,
    px,
    devicePx,
    cssPx,
    dp,
    sp,
    ppi,
    dpr,
    addPx,
    subtractPx,
    scalePx,
    negatePx,
    absPx,
    ppiStandard,
    ppiRetina,
    ppiRetinaHD,
    ppi4K,
    ppiPrint300,
    ppiPrint600,
    unwrapPixel,
    unwrapDevicePixel,
    unwrapCSSPixel,
    unwrapDp,
    unwrapSp,
    unwrapPpi,
    unwrapDpr,
    eqPixel,
    ordPixel,
    showPixel,
    semiringPixel,
    ringPixel,
    eqDevicePixel,
    ordDevicePixel,
    showDevicePixel,
    eqCSSPixel,
    ordCSSPixel,
    showCSSPixel,
    eqDensityIndependentPixel,
    ordDensityIndependentPixel,
    showDensityIndependentPixel,
    eqScaledPixel,
    ordScaledPixel,
    showScaledPixel,
    eqPixelsPerInch,
    ordPixelsPerInch,
    showPixelsPerInch,
    eqDevicePixelRatio,
    ordDevicePixelRatio,
    showDevicePixelRatio
};
