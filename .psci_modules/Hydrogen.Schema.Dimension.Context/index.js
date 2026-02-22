// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // hydrogen // schema // dimension // context
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Display context - the bridge between physical and device units.
// |
// | A pixel has no inherent physical size. To convert between pixels and
// | inches, you need to know the display's characteristics:
// |
// | - **PPI**: Pixels per inch (physical density)
// | - **DPR**: Device pixel ratio (CSS pixels to device pixels)
// | - **Viewing distance**: Affects perceived size
// | - **Font scale**: User accessibility preference
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Schema.Dimension.Context as Ctx
// | import Hydrogen.Schema.Dimension.Physical as Phys
// | import Hydrogen.Schema.Dimension.Device as Dev
// |
// | -- Define display context
// | myDisplay :: Ctx.DisplayContext
// | myDisplay = Ctx.displayContext
// |   { ppi: Dev.ppi 220.0
// |   , devicePixelRatio: Dev.dpr 2.0
// |   , fontScale: 1.0
// |   }
// |
// | -- Convert 1 inch to pixels on this display
// | pixelCount :: Dev.Pixel
// | pixelCount = Ctx.inchToPixels myDisplay (Phys.inch 1.0)
// | -- Result: 220 pixels
// | ```
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Dimension_Physical from "../Hydrogen.Schema.Dimension.Physical/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var eq = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Dimension_Physical.eqMeter);
var compare = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Dimension_Physical.ordMeter);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // viewing distance
// ═══════════════════════════════════════════════════════════════════════════════
// | Viewing distance from display to eye
// | Affects perceived angular size of elements
var ViewingDistance = function (x) {
    return x;
};

// | Typical tablet viewing distance (~40 cm / 16 inches)
var typicalTablet = 0.4;

// | Typical TV viewing distance (~3 m / 10 feet)
var typicalTV = 3.0;

// | Typical phone viewing distance (~30 cm / 12 inches)
var typicalPhone = 0.3;

// | Typical desktop viewing distance (~60 cm / 24 inches)
var typicalDesktop = 0.6;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // sp <-> pixel conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert scaled pixels to device pixels
// | Respects user font scale preference
var spToPixels = function (ctx) {
    return function (v) {
        return v * (ctx.ppi / 160.0) * ctx.fontScale;
    };
};
var showViewingDistance = {
    show: function (v) {
        return show(v) + " m viewing distance";
    }
};

// | Convert device pixels to scaled pixels
var pixelsToSp = function (ctx) {
    return function (v) {
        return (v * (160.0 / ctx.ppi)) / ctx.fontScale;
    };
};

// | Convert device pixels to physical meters
var pixelsToMeter = function (ctx) {
    return function (v) {
        var inches$prime = v / ctx.ppi;
        return inches$prime / 39.3701;
    };
};

// | Convert device pixels to physical inches
var pixelsToInch = function (ctx) {
    return function (v) {
        return v / ctx.ppi;
    };
};

// | Convert device pixels to density-independent pixels
var pixelsToDp = function (ctx) {
    return function (v) {
        return v * (160.0 / ctx.ppi);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // angular size
// ═══════════════════════════════════════════════════════════════════════════════
// | Calculate angular size of a pixel in arcminutes
// | This is what the human eye actually perceives
// | 1 arcminute ≈ limit of human visual acuity
var pixelToArcminutes = function (ctx) {
    return function (v) {
        
        // Size of one pixel in meters
var pixelSizeMeters = 2.54e-2 / ctx.ppi;
        
        // Angular size in radians: arctan(size / distance)
        // For small angles: angle ≈ size / distance
var angleRadians = pixelSizeMeters / v;
        
        // Convert to arcminutes (1 radian = 3437.75 arcminutes)
var arcminutes = angleRadians * 3437.75;
        return arcminutes;
    };
};

// | Convert physical meters to device pixels
var meterToPixels = function (ctx) {
    return function (v) {
        
        // 1 meter = 39.3701 inches
var inches$prime = v * 39.3701;
        return inches$prime * ctx.ppi;
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                  // physical <-> device conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert physical inches to device pixels
var inchToPixels = function (ctx) {
    return function (v) {
        return v * ctx.ppi;
    };
};
var eqViewingDistance = {
    eq: function (x) {
        return function (y) {
            return eq(x)(y);
        };
    }
};
var ordViewingDistance = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqViewingDistance;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // dp <-> pixel conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert density-independent pixels to device pixels
// | Android formula: pixels = dp * (ppi / 160)
var dpToPixels = function (ctx) {
    return function (v) {
        return v * (ctx.ppi / 160.0);
    };
};

// | Create a display context
var displayContext = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);

// | Convert device pixels to CSS pixels
var devicePixelToCssPixel = function (ctx) {
    return function (v) {
        return v / ctx.devicePixelRatio;
    };
};

// | Default display context (96 PPI, 1x DPR, normal font)
// | This matches CSS reference pixel (1 CSS inch = 96 CSS pixels)
var defaultDisplayContext = {
    ppi: 96.0,
    devicePixelRatio: 1.0,
    fontScale: 1.0
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // css <-> device conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert CSS pixels to device pixels
var cssPixelToDevicePixel = function (ctx) {
    return function (v) {
        return v * ctx.devicePixelRatio;
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // context properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Get PPI from context
var contextPpi = function (ctx) {
    return ctx.ppi;
};

// | Get font scale from context
var contextFontScale = function (ctx) {
    return ctx.fontScale;
};

// | Get device pixel ratio from context
var contextDpr = function (ctx) {
    return ctx.devicePixelRatio;
};

// | Calculate required pixel size for a given angular resolution
// | Useful for determining appropriate PPI at a viewing distance
var arcminutesToPixel = function (v) {
    return function (arcminutes) {
        
        // Convert arcminutes to radians
var angleRadians = arcminutes / 3437.75;
        
        // Required pixel size in meters
var pixelSizeMeters = angleRadians * v;
        
        // Convert to PPI
var ppiVal = 2.54e-2 / pixelSizeMeters;
        return ppiVal;
    };
};
export {
    displayContext,
    defaultDisplayContext,
    contextPpi,
    contextDpr,
    contextFontScale,
    inchToPixels,
    pixelsToInch,
    meterToPixels,
    pixelsToMeter,
    cssPixelToDevicePixel,
    devicePixelToCssPixel,
    dpToPixels,
    pixelsToDp,
    spToPixels,
    pixelsToSp,
    ViewingDistance,
    typicalPhone,
    typicalTablet,
    typicalDesktop,
    typicalTV,
    pixelToArcminutes,
    arcminutesToPixel,
    eqViewingDistance,
    ordViewingDistance,
    showViewingDistance
};
