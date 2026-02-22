// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // yuv
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | YUV - Video color space (PAL/SECAM analog).
// |
// | **VIDEO BROADCAST STANDARD:**
// | YUV separates brightness (luma) from color (chroma):
// | - **Y**: Luma (brightness), 0.0-1.0
// | - **U**: Blue-difference chroma, -0.5 to +0.5
// | - **V**: Red-difference chroma, -0.5 to +0.5
// |
// | **Why separate luma and chroma?**
// | - Backward compatibility with B&W TVs (they only need Y)
// | - Chroma can be lower resolution (human vision less sensitive)
// | - Efficient video compression
// |
// | **Variants:**
// | - YUV: Analog (PAL/SECAM)
// | - YCbCr: Digital (JPEG, MPEG, H.264)
// | - YIQ: NTSC (North America analog TV)
// |
// | **Note:** Digital video typically uses YCbCr, but YUV is often used generically
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // atoms
// ═══════════════════════════════════════════════════════════════════════════════
// | Luma (Y) - brightness component: 0.0-1.0
var Luma = function (x) {
    return x;
};

// | Chroma V - red-difference: -0.5 to +0.5
var ChromaV = function (x) {
    return x;
};

// | Chroma U - blue-difference: -0.5 to +0.5
var ChromaU = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // molecule
// ═══════════════════════════════════════════════════════════════════════════════
// | YUV color - composition of Luma and two Chroma components
var YUV = function (x) {
    return x;
};
var unwrapV = function (v) {
    return v;
};
var unwrapU = function (v) {
    return v;
};
var unwrapLuma = function (v) {
    return v;
};

// | Convert to record
var yuvToRecord = function (v) {
    return {
        y: unwrapLuma(v.y),
        u: unwrapU(v.u),
        v: unwrapV(v.v)
    };
};

// | Alias for yuvToRecord
var toRecord = yuvToRecord;
var showYUV = {
    show: function (v) {
        return "yuv(" + (show(unwrapLuma(v.y)) + (", " + (show(unwrapU(v.u)) + (", " + (show(unwrapV(v.v)) + ")")))));
    }
};
var showLuma = {
    show: function (v) {
        return "Luma " + show(v);
    }
};
var showChromaV = {
    show: function (v) {
        return "ChromaV " + show(v);
    }
};
var showChromaU = {
    show: function (v) {
        return "ChromaU " + show(v);
    }
};

// | Create luma value (clamped 0.0-1.0)
var luma = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(n);
};

// | Extract V chroma
var getV = function (v) {
    return v.v;
};

// | Extract U chroma
var getU = function (v) {
    return v.u;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract luma
var getLuma = function (v) {
    return v.y;
};
var eqLuma = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq1 = /* #__PURE__ */ Data_Eq.eq(eqLuma);
var ordLuma = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLuma;
    }
};
var compare1 = /* #__PURE__ */ Data_Ord.compare(ordLuma);
var eqChromaV = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(eqChromaV);
var ordChromaV = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqChromaV;
    }
};
var compare2 = /* #__PURE__ */ Data_Ord.compare(ordChromaV);
var eqChromaU = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(eqChromaU);
var eqYUV = {
    eq: function (x) {
        return function (y) {
            return eq3(x.u)(y.u) && eq2(x.v)(y.v) && eq1(x.y)(y.y);
        };
    }
};
var ordChromaU = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqChromaU;
    }
};
var compare3 = /* #__PURE__ */ Data_Ord.compare(ordChromaU);
var ordYUV = {
    compare: function (x) {
        return function (y) {
            var v = compare3(x.u)(y.u);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare2(x.v)(y.v);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare1(x.y)(y.y);
        };
    },
    Eq0: function () {
        return eqYUV;
    }
};

// | Create V chroma value (clamped -0.5 to +0.5)
var chromaV = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(-0.5)(0.5)(n);
};

// | Create U chroma value (clamped -0.5 to +0.5)
var chromaU = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(-0.5)(0.5)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create YUV color
var yuv = function (y) {
    return function (u) {
        return function (v) {
            return {
                y: luma(y),
                u: chromaU(u),
                v: chromaV(v)
            };
        };
    };
};

// | Create from record
var yuvFromRecord = function (v) {
    return yuv(v.y)(v.u)(v.v);
};
export {
    yuv,
    yuvFromRecord,
    luma,
    chromaU,
    chromaV,
    getLuma,
    getU,
    getV,
    unwrapLuma,
    unwrapU,
    unwrapV,
    yuvToRecord,
    toRecord,
    eqLuma,
    ordLuma,
    showLuma,
    eqChromaU,
    ordChromaU,
    showChromaU,
    eqChromaV,
    ordChromaV,
    showChromaV,
    eqYUV,
    ordYUV,
    showYUV
};
