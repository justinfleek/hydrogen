// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // space
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color spaces for professional color management.
// |
// | This module provides types for various color spaces used in:
// | - **Web**: sRGB (standard), Display P3 (wide gamut)
// | - **Print**: CMYK, Pantone references
// | - **Film/Video**: ACES, Rec.709, Rec.2020, DCI-P3
// | - **Perceptual**: LAB, OKLAB, LCH, OKLCH
// | - **3D/PBR**: Linear RGB for physically-based rendering
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";

// | Transfer function (gamma curve)
var Linear = /* #__PURE__ */ (function () {
    function Linear() {

    };
    Linear.value = new Linear();
    return Linear;
})();

// | Transfer function (gamma curve)
var Gamma22 = /* #__PURE__ */ (function () {
    function Gamma22() {

    };
    Gamma22.value = new Gamma22();
    return Gamma22;
})();

// | Transfer function (gamma curve)
var Gamma24 = /* #__PURE__ */ (function () {
    function Gamma24() {

    };
    Gamma24.value = new Gamma24();
    return Gamma24;
})();

// | Transfer function (gamma curve)
var Gamma26 = /* #__PURE__ */ (function () {
    function Gamma26() {

    };
    Gamma26.value = new Gamma26();
    return Gamma26;
})();

// | Transfer function (gamma curve)
var SRGBTransfer = /* #__PURE__ */ (function () {
    function SRGBTransfer() {

    };
    SRGBTransfer.value = new SRGBTransfer();
    return SRGBTransfer;
})();

// | Transfer function (gamma curve)
var PQTransfer = /* #__PURE__ */ (function () {
    function PQTransfer() {

    };
    PQTransfer.value = new PQTransfer();
    return PQTransfer;
})();

// | Transfer function (gamma curve)
var HLGTransfer = /* #__PURE__ */ (function () {
    function HLGTransfer() {

    };
    HLGTransfer.value = new HLGTransfer();
    return HLGTransfer;
})();

// | Transfer function (gamma curve)
var ACEScct = /* #__PURE__ */ (function () {
    function ACEScct() {

    };
    ACEScct.value = new ACEScct();
    return ACEScct;
})();

// | Transfer function (gamma curve)
var ACEScc = /* #__PURE__ */ (function () {
    function ACEScc() {

    };
    ACEScc.value = new ACEScc();
    return ACEScc;
})();

// | Standard illuminants (white points)
var D50 = /* #__PURE__ */ (function () {
    function D50() {

    };
    D50.value = new D50();
    return D50;
})();

// | Standard illuminants (white points)
var D55 = /* #__PURE__ */ (function () {
    function D55() {

    };
    D55.value = new D55();
    return D55;
})();

// | Standard illuminants (white points)
var D65 = /* #__PURE__ */ (function () {
    function D65() {

    };
    D65.value = new D65();
    return D65;
})();

// | Standard illuminants (white points)
var D75 = /* #__PURE__ */ (function () {
    function D75() {

    };
    D75.value = new D75();
    return D75;
})();

// | Standard illuminants (white points)
var DCI = /* #__PURE__ */ (function () {
    function DCI() {

    };
    DCI.value = new DCI();
    return DCI;
})();

// | Standard illuminants (white points)
var ACES = /* #__PURE__ */ (function () {
    function ACES() {

    };
    ACES.value = new ACES();
    return ACES;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // gamut mapping
// ═══════════════════════════════════════════════════════════════════════════════
// | Strategy for handling out-of-gamut colors
var Clip = /* #__PURE__ */ (function () {
    function Clip() {

    };
    Clip.value = new Clip();
    return Clip;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // gamut mapping
// ═══════════════════════════════════════════════════════════════════════════════
// | Strategy for handling out-of-gamut colors
var Compress = /* #__PURE__ */ (function () {
    function Compress() {

    };
    Compress.value = new Compress();
    return Compress;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // gamut mapping
// ═══════════════════════════════════════════════════════════════════════════════
// | Strategy for handling out-of-gamut colors
var ProjectToSurface = /* #__PURE__ */ (function () {
    function ProjectToSurface() {

    };
    ProjectToSurface.value = new ProjectToSurface();
    return ProjectToSurface;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // gamut mapping
// ═══════════════════════════════════════════════════════════════════════════════
// | Strategy for handling out-of-gamut colors
var PreserveLightness = /* #__PURE__ */ (function () {
    function PreserveLightness() {

    };
    PreserveLightness.value = new PreserveLightness();
    return PreserveLightness;
})();

// | Gamut describes the range of colors a space can represent
var GamutSRGB = /* #__PURE__ */ (function () {
    function GamutSRGB() {

    };
    GamutSRGB.value = new GamutSRGB();
    return GamutSRGB;
})();

// | Gamut describes the range of colors a space can represent
var GamutP3 = /* #__PURE__ */ (function () {
    function GamutP3() {

    };
    GamutP3.value = new GamutP3();
    return GamutP3;
})();

// | Gamut describes the range of colors a space can represent
var GamutRec2020 = /* #__PURE__ */ (function () {
    function GamutRec2020() {

    };
    GamutRec2020.value = new GamutRec2020();
    return GamutRec2020;
})();

// | Gamut describes the range of colors a space can represent
var GamutAP0 = /* #__PURE__ */ (function () {
    function GamutAP0() {

    };
    GamutAP0.value = new GamutAP0();
    return GamutAP0;
})();

// | Gamut describes the range of colors a space can represent
var GamutProPhoto = /* #__PURE__ */ (function () {
    function GamutProPhoto() {

    };
    GamutProPhoto.value = new GamutProPhoto();
    return GamutProPhoto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var SRGB = /* #__PURE__ */ (function () {
    function SRGB() {

    };
    SRGB.value = new SRGB();
    return SRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var LinearSRGB = /* #__PURE__ */ (function () {
    function LinearSRGB() {

    };
    LinearSRGB.value = new LinearSRGB();
    return LinearSRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var DisplayP3 = /* #__PURE__ */ (function () {
    function DisplayP3() {

    };
    DisplayP3.value = new DisplayP3();
    return DisplayP3;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var AdobeRGB = /* #__PURE__ */ (function () {
    function AdobeRGB() {

    };
    AdobeRGB.value = new AdobeRGB();
    return AdobeRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var ProPhotoRGB = /* #__PURE__ */ (function () {
    function ProPhotoRGB() {

    };
    ProPhotoRGB.value = new ProPhotoRGB();
    return ProPhotoRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var Rec709 = /* #__PURE__ */ (function () {
    function Rec709() {

    };
    Rec709.value = new Rec709();
    return Rec709;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var Rec2020 = /* #__PURE__ */ (function () {
    function Rec2020() {

    };
    Rec2020.value = new Rec2020();
    return Rec2020;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var DCIP3 = /* #__PURE__ */ (function () {
    function DCIP3() {

    };
    DCIP3.value = new DCIP3();
    return DCIP3;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var ACES_AP0 = /* #__PURE__ */ (function () {
    function ACES_AP0() {

    };
    ACES_AP0.value = new ACES_AP0();
    return ACES_AP0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var ACES_AP1 = /* #__PURE__ */ (function () {
    function ACES_AP1() {

    };
    ACES_AP1.value = new ACES_AP1();
    return ACES_AP1;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var CIE_XYZ = /* #__PURE__ */ (function () {
    function CIE_XYZ() {

    };
    CIE_XYZ.value = new CIE_XYZ();
    return CIE_XYZ;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var CIE_LAB = /* #__PURE__ */ (function () {
    function CIE_LAB() {

    };
    CIE_LAB.value = new CIE_LAB();
    return CIE_LAB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var CIE_LCH = /* #__PURE__ */ (function () {
    function CIE_LCH() {

    };
    CIE_LCH.value = new CIE_LCH();
    return CIE_LCH;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var OKLab = /* #__PURE__ */ (function () {
    function OKLab() {

    };
    OKLab.value = new OKLab();
    return OKLab;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var OKLCH = /* #__PURE__ */ (function () {
    function OKLCH() {

    };
    OKLCH.value = new OKLCH();
    return OKLCH;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var CMYK_FOGRA39 = /* #__PURE__ */ (function () {
    function CMYK_FOGRA39() {

    };
    CMYK_FOGRA39.value = new CMYK_FOGRA39();
    return CMYK_FOGRA39;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // color space types
// ═══════════════════════════════════════════════════════════════════════════════
// | Identifies a color space by its characteristics
var CMYK_GRACoL = /* #__PURE__ */ (function () {
    function CMYK_GRACoL() {

    };
    CMYK_GRACoL.value = new CMYK_GRACoL();
    return CMYK_GRACoL;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InSRGB = /* #__PURE__ */ (function () {
    function InSRGB(value0) {
        this.value0 = value0;
    };
    InSRGB.create = function (value0) {
        return new InSRGB(value0);
    };
    return InSRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InLinearRGB = /* #__PURE__ */ (function () {
    function InLinearRGB(value0) {
        this.value0 = value0;
    };
    InLinearRGB.create = function (value0) {
        return new InLinearRGB(value0);
    };
    return InLinearRGB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InDisplayP3 = /* #__PURE__ */ (function () {
    function InDisplayP3(value0) {
        this.value0 = value0;
    };
    InDisplayP3.create = function (value0) {
        return new InDisplayP3(value0);
    };
    return InDisplayP3;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InXYZ = /* #__PURE__ */ (function () {
    function InXYZ(value0) {
        this.value0 = value0;
    };
    InXYZ.create = function (value0) {
        return new InXYZ(value0);
    };
    return InXYZ;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InLAB = /* #__PURE__ */ (function () {
    function InLAB(value0) {
        this.value0 = value0;
    };
    InLAB.create = function (value0) {
        return new InLAB(value0);
    };
    return InLAB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InOKLAB = /* #__PURE__ */ (function () {
    function InOKLAB(value0) {
        this.value0 = value0;
    };
    InOKLAB.create = function (value0) {
        return new InOKLAB(value0);
    };
    return InOKLAB;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InLCH = /* #__PURE__ */ (function () {
    function InLCH(value0) {
        this.value0 = value0;
    };
    InLCH.create = function (value0) {
        return new InLCH(value0);
    };
    return InLCH;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InOKLCH = /* #__PURE__ */ (function () {
    function InOKLCH(value0) {
        this.value0 = value0;
    };
    InOKLCH.create = function (value0) {
        return new InOKLCH(value0);
    };
    return InOKLCH;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // color value in space
// ═══════════════════════════════════════════════════════════════════════════════
// | A color value tagged with its color space
var InCMYK = /* #__PURE__ */ (function () {
    function InCMYK(value0) {
        this.value0 = value0;
    };
    InCMYK.create = function (value0) {
        return new InCMYK(value0);
    };
    return InCMYK;
})();

// | Create a CIE XYZ color
var xyz = function (x) {
    return function (y) {
        return function (z) {
            return new InXYZ({
                x: x,
                y: y,
                z: z
            });
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | sRGB gamma to linear conversion for single channel
var srgbToLinearChannel = function (c) {
    var $45 = c <= 4.045e-2;
    if ($45) {
        return c / 12.92;
    };
    return Hydrogen_Math_Core.pow((c + 5.5e-2) / 1.055)(2.4);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert sRGB to Linear RGB (remove gamma)
var toLinear = function (v) {
    if (v instanceof InSRGB) {
        return new InLinearRGB({
            r: srgbToLinearChannel(v.value0.r),
            g: srgbToLinearChannel(v.value0.g),
            b: srgbToLinearChannel(v.value0.b)
        });
    };
    return v;
};

// | Convert to CIE XYZ (reference space)
var toXYZ = function ($copy_v) {
    var $tco_done = false;
    var $tco_result;
    function $tco_loop(v) {
        if (v instanceof InLinearRGB) {
            var z = 1.93339e-2 * v.value0.r + 0.119192 * v.value0.g + 0.9503041 * v.value0.b;
            var y = 0.2126729 * v.value0.r + 0.7151522 * v.value0.g + 7.2175e-2 * v.value0.b;
            var x = 0.4124564 * v.value0.r + 0.3575761 * v.value0.g + 0.1804375 * v.value0.b;
            $tco_done = true;
            return new InXYZ({
                x: x,
                y: y,
                z: z
            });
        };
        if (v instanceof InSRGB) {
            $copy_v = toLinear(new InSRGB({
                r: 0.0,
                g: 0.0,
                b: 0.0
            }));
            return;
        };
        $tco_done = true;
        return v;
    };
    while (!$tco_done) {
        $tco_result = $tco_loop($copy_v);
    };
    return $tco_result;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an sRGB color (values 0.0-1.0)
var srgb = function (r) {
    return function (g) {
        return function (b) {
            return new InSRGB({
                r: r,
                g: g,
                b: b
            });
        };
    };
};
var showColorSpace = {
    show: function (v) {
        if (v instanceof SRGB) {
            return "sRGB";
        };
        if (v instanceof LinearSRGB) {
            return "Linear sRGB";
        };
        if (v instanceof DisplayP3) {
            return "Display P3";
        };
        if (v instanceof AdobeRGB) {
            return "Adobe RGB";
        };
        if (v instanceof ProPhotoRGB) {
            return "ProPhoto RGB";
        };
        if (v instanceof Rec709) {
            return "Rec.709";
        };
        if (v instanceof Rec2020) {
            return "Rec.2020";
        };
        if (v instanceof DCIP3) {
            return "DCI-P3";
        };
        if (v instanceof ACES_AP0) {
            return "ACES AP0";
        };
        if (v instanceof ACES_AP1) {
            return "ACES AP1";
        };
        if (v instanceof CIE_XYZ) {
            return "CIE XYZ";
        };
        if (v instanceof CIE_LAB) {
            return "CIE L*a*b*";
        };
        if (v instanceof CIE_LCH) {
            return "CIE LCH";
        };
        if (v instanceof OKLab) {
            return "Oklab";
        };
        if (v instanceof OKLCH) {
            return "OKLCH";
        };
        if (v instanceof CMYK_FOGRA39) {
            return "CMYK (FOGRA39)";
        };
        if (v instanceof CMYK_GRACoL) {
            return "CMYK (GRACoL)";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Space (line 93, column 10 - line 110, column 35): " + [ v.constructor.name ]);
    }
};

// | Rec.709 (HDTV standard)
var rec709 = /* #__PURE__ */ (function () {
    return {
        name: "Rec.709",
        gamut: GamutSRGB.value,
        transfer: Gamma24.value,
        whitePoint: D65.value
    };
})();

// | Rec.2020 (UHDTV standard)
var rec2020 = /* #__PURE__ */ (function () {
    return {
        name: "Rec.2020",
        gamut: GamutRec2020.value,
        transfer: PQTransfer.value,
        whitePoint: D65.value
    };
})();

// | Create an OKLCH color
var oklch = function (l) {
    return function (c) {
        return function (h) {
            return new InOKLCH({
                l: l,
                c: c,
                h: h
            });
        };
    };
};

// | Create an Oklab color
var oklab = function (l) {
    return function (a) {
        return function (b) {
            return new InOKLAB({
                l: l,
                a: a,
                b: b
            });
        };
    };
};

// | Linear to sRGB gamma conversion for single channel
var linearToSrgbChannel = function (c) {
    var $58 = c <= 3.1308e-3;
    if ($58) {
        return c * 12.92;
    };
    return 1.055 * Hydrogen_Math_Core.pow(c)(1.0 / 2.4) - 5.5e-2;
};

// | Create a linear RGB color (values 0.0-1.0, can exceed for HDR)
var linearRgb = function (r) {
    return function (g) {
        return function (b) {
            return new InLinearRGB({
                r: r,
                g: g,
                b: b
            });
        };
    };
};

// | Create a CIE LCH color
var lch = function (l) {
    return function (c) {
        return function (h) {
            return new InLCH({
                l: l,
                c: c,
                h: h
            });
        };
    };
};

// | Create a CIE L*a*b* color
var lab = function (l) {
    return function (a) {
        return function (b) {
            return new InLAB({
                l: l,
                a: a,
                b: b
            });
        };
    };
};

// | Check if a color is within the sRGB gamut
var isInGamut = /* #__PURE__ */ (function () {
    var inRange = function (n) {
        return n >= 0.0 && n <= 1.0;
    };
    return function (v) {
        if (v instanceof InSRGB) {
            return inRange(v.value0.r) && (inRange(v.value0.g) && inRange(v.value0.b));
        };
        if (v instanceof InLinearRGB) {
            return inRange(v.value0.r) && (inRange(v.value0.g) && inRange(v.value0.b));
        };
        return true;
    };
})();

// | Convert from CIE XYZ to Linear RGB
var fromXYZ = function (v) {
    if (v instanceof InXYZ) {
        var r = 3.2404542 * v.value0.x - 1.5371385 * v.value0.y - 0.4985314 * v.value0.z;
        var g = -0.969266 * v.value0.x + 1.8760108 * v.value0.y + 4.1556e-2 * v.value0.z;
        var b = (5.56434e-2 * v.value0.x - 0.2040259 * v.value0.y) + 1.0572252 * v.value0.z;
        return new InLinearRGB({
            r: r,
            g: g,
            b: b
        });
    };
    return v;
};

// | Convert Linear RGB to sRGB (apply gamma)
var fromLinear = function (v) {
    if (v instanceof InLinearRGB) {
        return new InSRGB({
            r: linearToSrgbChannel(v.value0.r),
            g: linearToSrgbChannel(v.value0.g),
            b: linearToSrgbChannel(v.value0.b)
        });
    };
    return v;
};
var eqTransferFunction = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Linear && y instanceof Linear) {
                return true;
            };
            if (x instanceof Gamma22 && y instanceof Gamma22) {
                return true;
            };
            if (x instanceof Gamma24 && y instanceof Gamma24) {
                return true;
            };
            if (x instanceof Gamma26 && y instanceof Gamma26) {
                return true;
            };
            if (x instanceof SRGBTransfer && y instanceof SRGBTransfer) {
                return true;
            };
            if (x instanceof PQTransfer && y instanceof PQTransfer) {
                return true;
            };
            if (x instanceof HLGTransfer && y instanceof HLGTransfer) {
                return true;
            };
            if (x instanceof ACEScct && y instanceof ACEScct) {
                return true;
            };
            if (x instanceof ACEScc && y instanceof ACEScc) {
                return true;
            };
            return false;
        };
    }
};
var eqIlluminant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof D50 && y instanceof D50) {
                return true;
            };
            if (x instanceof D55 && y instanceof D55) {
                return true;
            };
            if (x instanceof D65 && y instanceof D65) {
                return true;
            };
            if (x instanceof D75 && y instanceof D75) {
                return true;
            };
            if (x instanceof DCI && y instanceof DCI) {
                return true;
            };
            if (x instanceof ACES && y instanceof ACES) {
                return true;
            };
            return false;
        };
    }
};
var eqGamutMapping = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Clip && y instanceof Clip) {
                return true;
            };
            if (x instanceof Compress && y instanceof Compress) {
                return true;
            };
            if (x instanceof ProjectToSurface && y instanceof ProjectToSurface) {
                return true;
            };
            if (x instanceof PreserveLightness && y instanceof PreserveLightness) {
                return true;
            };
            return false;
        };
    }
};
var eqGamut = {
    eq: function (x) {
        return function (y) {
            if (x instanceof GamutSRGB && y instanceof GamutSRGB) {
                return true;
            };
            if (x instanceof GamutP3 && y instanceof GamutP3) {
                return true;
            };
            if (x instanceof GamutRec2020 && y instanceof GamutRec2020) {
                return true;
            };
            if (x instanceof GamutAP0 && y instanceof GamutAP0) {
                return true;
            };
            if (x instanceof GamutProPhoto && y instanceof GamutProPhoto) {
                return true;
            };
            return false;
        };
    }
};
var eqColorSpace = {
    eq: function (x) {
        return function (y) {
            if (x instanceof SRGB && y instanceof SRGB) {
                return true;
            };
            if (x instanceof LinearSRGB && y instanceof LinearSRGB) {
                return true;
            };
            if (x instanceof DisplayP3 && y instanceof DisplayP3) {
                return true;
            };
            if (x instanceof AdobeRGB && y instanceof AdobeRGB) {
                return true;
            };
            if (x instanceof ProPhotoRGB && y instanceof ProPhotoRGB) {
                return true;
            };
            if (x instanceof Rec709 && y instanceof Rec709) {
                return true;
            };
            if (x instanceof Rec2020 && y instanceof Rec2020) {
                return true;
            };
            if (x instanceof DCIP3 && y instanceof DCIP3) {
                return true;
            };
            if (x instanceof ACES_AP0 && y instanceof ACES_AP0) {
                return true;
            };
            if (x instanceof ACES_AP1 && y instanceof ACES_AP1) {
                return true;
            };
            if (x instanceof CIE_XYZ && y instanceof CIE_XYZ) {
                return true;
            };
            if (x instanceof CIE_LAB && y instanceof CIE_LAB) {
                return true;
            };
            if (x instanceof CIE_LCH && y instanceof CIE_LCH) {
                return true;
            };
            if (x instanceof OKLab && y instanceof OKLab) {
                return true;
            };
            if (x instanceof OKLCH && y instanceof OKLCH) {
                return true;
            };
            if (x instanceof CMYK_FOGRA39 && y instanceof CMYK_FOGRA39) {
                return true;
            };
            if (x instanceof CMYK_GRACoL && y instanceof CMYK_GRACoL) {
                return true;
            };
            return false;
        };
    }
};
var eqColorInSpace = {
    eq: function (x) {
        return function (y) {
            if (x instanceof InSRGB && y instanceof InSRGB) {
                return x.value0.b === y.value0.b && x.value0.g === y.value0.g && x.value0.r === y.value0.r;
            };
            if (x instanceof InLinearRGB && y instanceof InLinearRGB) {
                return x.value0.b === y.value0.b && x.value0.g === y.value0.g && x.value0.r === y.value0.r;
            };
            if (x instanceof InDisplayP3 && y instanceof InDisplayP3) {
                return x.value0.b === y.value0.b && x.value0.g === y.value0.g && x.value0.r === y.value0.r;
            };
            if (x instanceof InXYZ && y instanceof InXYZ) {
                return x.value0.x === y.value0.x && x.value0.y === y.value0.y && x.value0.z === y.value0.z;
            };
            if (x instanceof InLAB && y instanceof InLAB) {
                return x.value0.a === y.value0.a && x.value0.b === y.value0.b && x.value0.l === y.value0.l;
            };
            if (x instanceof InOKLAB && y instanceof InOKLAB) {
                return x.value0.a === y.value0.a && x.value0.b === y.value0.b && x.value0.l === y.value0.l;
            };
            if (x instanceof InLCH && y instanceof InLCH) {
                return x.value0.c === y.value0.c && x.value0.h === y.value0.h && x.value0.l === y.value0.l;
            };
            if (x instanceof InOKLCH && y instanceof InOKLCH) {
                return x.value0.c === y.value0.c && x.value0.h === y.value0.h && x.value0.l === y.value0.l;
            };
            if (x instanceof InCMYK && y instanceof InCMYK) {
                return x.value0.c === y.value0.c && x.value0.k === y.value0.k && x.value0.m === y.value0.m && x.value0.y === y.value0.y;
            };
            return false;
        };
    }
};

// | Create a Display P3 color
var displayP3 = function (r) {
    return function (g) {
        return function (b) {
            return new InDisplayP3({
                r: r,
                g: g,
                b: b
            });
        };
    };
};

// | DCI-P3 (digital cinema)
var dciP3 = /* #__PURE__ */ (function () {
    return {
        name: "DCI-P3",
        gamut: GamutP3.value,
        transfer: Gamma26.value,
        whitePoint: DCI.value
    };
})();

// | Create a CMYK color
var cmyk = function (c) {
    return function (m) {
        return function (y) {
            return function (k) {
                return new InCMYK({
                    c: c,
                    m: m,
                    y: y,
                    k: k
                });
            };
        };
    };
};

// | ACES AP1 (working space for ACES pipeline)
var acesAP1 = /* #__PURE__ */ (function () {
    return {
        name: "ACES AP1",
        gamut: GamutRec2020.value,
        transfer: ACEScct.value,
        whitePoint: ACES.value
    };
})();

// | ACES AP0 (Academy Color Encoding System, archival)
var acesAP0 = /* #__PURE__ */ (function () {
    return {
        name: "ACES AP0",
        gamut: GamutAP0.value,
        transfer: Linear.value,
        whitePoint: ACES.value
    };
})();
export {
    SRGB,
    LinearSRGB,
    DisplayP3,
    AdobeRGB,
    ProPhotoRGB,
    Rec709,
    Rec2020,
    DCIP3,
    ACES_AP0,
    ACES_AP1,
    CIE_XYZ,
    CIE_LAB,
    CIE_LCH,
    OKLab,
    OKLCH,
    CMYK_FOGRA39,
    CMYK_GRACoL,
    GamutSRGB,
    GamutP3,
    GamutRec2020,
    GamutAP0,
    GamutProPhoto,
    Linear,
    Gamma22,
    Gamma24,
    Gamma26,
    SRGBTransfer,
    PQTransfer,
    HLGTransfer,
    ACEScct,
    ACEScc,
    D50,
    D55,
    D65,
    D75,
    DCI,
    ACES,
    InSRGB,
    InLinearRGB,
    InDisplayP3,
    InXYZ,
    InLAB,
    InOKLAB,
    InLCH,
    InOKLCH,
    InCMYK,
    srgb,
    linearRgb,
    displayP3,
    lab,
    oklab,
    lch,
    oklch,
    cmyk,
    xyz,
    toLinear,
    fromLinear,
    toXYZ,
    fromXYZ,
    acesAP0,
    acesAP1,
    rec709,
    rec2020,
    dciP3,
    Clip,
    Compress,
    ProjectToSurface,
    PreserveLightness,
    isInGamut,
    eqColorSpace,
    showColorSpace,
    eqGamut,
    eqTransferFunction,
    eqIlluminant,
    eqColorInSpace,
    eqGamutMapping
};
