// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // token
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Design tokens as types
// |
// | This module provides type-safe design tokens for:
// | - Spacing (padding, margin, gap)
// | - Border radius
// | - Shadows
// | - Z-index layers
// |
// | All tokens map to Tailwind CSS classes for zero-runtime styling.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Style.Token as Token
// |
// | -- Type-safe spacing
// | padding Token.P4        -- "p-4"
// | margin Token.M2         -- "m-2"
// | gap Token.Gap4          -- "gap-4"
// |
// | -- Border radius
// | radius Token.RoundedLg  -- "rounded-lg"
// |
// | -- Shadows
// | shadow Token.ShadowMd   -- "shadow-md"
// | ```
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var Z0 = /* #__PURE__ */ (function () {
    function Z0() {

    };
    Z0.value = new Z0();
    return Z0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var Z10 = /* #__PURE__ */ (function () {
    function Z10() {

    };
    Z10.value = new Z10();
    return Z10;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var Z20 = /* #__PURE__ */ (function () {
    function Z20() {

    };
    Z20.value = new Z20();
    return Z20;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var Z30 = /* #__PURE__ */ (function () {
    function Z30() {

    };
    Z30.value = new Z30();
    return Z30;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var Z40 = /* #__PURE__ */ (function () {
    function Z40() {

    };
    Z40.value = new Z40();
    return Z40;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var Z50 = /* #__PURE__ */ (function () {
    function Z50() {

    };
    Z50.value = new Z50();
    return Z50;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // z-index
// ═══════════════════════════════════════════════════════════════════════════════
// | Z-index layers
var ZAuto = /* #__PURE__ */ (function () {
    function ZAuto() {

    };
    ZAuto.value = new ZAuto();
    return ZAuto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S0 = /* #__PURE__ */ (function () {
    function S0() {

    };
    S0.value = new S0();
    return S0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S0_5 = /* #__PURE__ */ (function () {
    function S0_5() {

    };
    S0_5.value = new S0_5();
    return S0_5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S1 = /* #__PURE__ */ (function () {
    function S1() {

    };
    S1.value = new S1();
    return S1;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S1_5 = /* #__PURE__ */ (function () {
    function S1_5() {

    };
    S1_5.value = new S1_5();
    return S1_5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S2 = /* #__PURE__ */ (function () {
    function S2() {

    };
    S2.value = new S2();
    return S2;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S2_5 = /* #__PURE__ */ (function () {
    function S2_5() {

    };
    S2_5.value = new S2_5();
    return S2_5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S3 = /* #__PURE__ */ (function () {
    function S3() {

    };
    S3.value = new S3();
    return S3;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S3_5 = /* #__PURE__ */ (function () {
    function S3_5() {

    };
    S3_5.value = new S3_5();
    return S3_5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S4 = /* #__PURE__ */ (function () {
    function S4() {

    };
    S4.value = new S4();
    return S4;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S5 = /* #__PURE__ */ (function () {
    function S5() {

    };
    S5.value = new S5();
    return S5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S6 = /* #__PURE__ */ (function () {
    function S6() {

    };
    S6.value = new S6();
    return S6;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S7 = /* #__PURE__ */ (function () {
    function S7() {

    };
    S7.value = new S7();
    return S7;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S8 = /* #__PURE__ */ (function () {
    function S8() {

    };
    S8.value = new S8();
    return S8;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S9 = /* #__PURE__ */ (function () {
    function S9() {

    };
    S9.value = new S9();
    return S9;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S10 = /* #__PURE__ */ (function () {
    function S10() {

    };
    S10.value = new S10();
    return S10;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S11 = /* #__PURE__ */ (function () {
    function S11() {

    };
    S11.value = new S11();
    return S11;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S12 = /* #__PURE__ */ (function () {
    function S12() {

    };
    S12.value = new S12();
    return S12;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S14 = /* #__PURE__ */ (function () {
    function S14() {

    };
    S14.value = new S14();
    return S14;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S16 = /* #__PURE__ */ (function () {
    function S16() {

    };
    S16.value = new S16();
    return S16;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S20 = /* #__PURE__ */ (function () {
    function S20() {

    };
    S20.value = new S20();
    return S20;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S24 = /* #__PURE__ */ (function () {
    function S24() {

    };
    S24.value = new S24();
    return S24;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S28 = /* #__PURE__ */ (function () {
    function S28() {

    };
    S28.value = new S28();
    return S28;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S32 = /* #__PURE__ */ (function () {
    function S32() {

    };
    S32.value = new S32();
    return S32;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S36 = /* #__PURE__ */ (function () {
    function S36() {

    };
    S36.value = new S36();
    return S36;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S40 = /* #__PURE__ */ (function () {
    function S40() {

    };
    S40.value = new S40();
    return S40;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S44 = /* #__PURE__ */ (function () {
    function S44() {

    };
    S44.value = new S44();
    return S44;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S48 = /* #__PURE__ */ (function () {
    function S48() {

    };
    S48.value = new S48();
    return S48;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S52 = /* #__PURE__ */ (function () {
    function S52() {

    };
    S52.value = new S52();
    return S52;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S56 = /* #__PURE__ */ (function () {
    function S56() {

    };
    S56.value = new S56();
    return S56;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S60 = /* #__PURE__ */ (function () {
    function S60() {

    };
    S60.value = new S60();
    return S60;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S64 = /* #__PURE__ */ (function () {
    function S64() {

    };
    S64.value = new S64();
    return S64;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S72 = /* #__PURE__ */ (function () {
    function S72() {

    };
    S72.value = new S72();
    return S72;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S80 = /* #__PURE__ */ (function () {
    function S80() {

    };
    S80.value = new S80();
    return S80;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var S96 = /* #__PURE__ */ (function () {
    function S96() {

    };
    S96.value = new S96();
    return S96;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing scale (maps to Tailwind's spacing scale)
// |
// | Each step is 0.25rem (4px at default font size)
var SAuto = /* #__PURE__ */ (function () {
    function SAuto() {

    };
    SAuto.value = new SAuto();
    return SAuto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeSpacing = /* #__PURE__ */ (function () {
    function SizeSpacing(value0) {
        this.value0 = value0;
    };
    SizeSpacing.create = function (value0) {
        return new SizeSpacing(value0);
    };
    return SizeSpacing;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeFull = /* #__PURE__ */ (function () {
    function SizeFull() {

    };
    SizeFull.value = new SizeFull();
    return SizeFull;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeScreen = /* #__PURE__ */ (function () {
    function SizeScreen() {

    };
    SizeScreen.value = new SizeScreen();
    return SizeScreen;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeMin = /* #__PURE__ */ (function () {
    function SizeMin() {

    };
    SizeMin.value = new SizeMin();
    return SizeMin;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeMax = /* #__PURE__ */ (function () {
    function SizeMax() {

    };
    SizeMax.value = new SizeMax();
    return SizeMax;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeFit = /* #__PURE__ */ (function () {
    function SizeFit() {

    };
    SizeFit.value = new SizeFit();
    return SizeFit;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeAuto = /* #__PURE__ */ (function () {
    function SizeAuto() {

    };
    SizeAuto.value = new SizeAuto();
    return SizeAuto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizeFraction = /* #__PURE__ */ (function () {
    function SizeFraction(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    SizeFraction.create = function (value0) {
        return function (value1) {
            return new SizeFraction(value0, value1);
        };
    };
    return SizeFraction;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Size values (for width/height)
var SizePx = /* #__PURE__ */ (function () {
    function SizePx(value0) {
        this.value0 = value0;
    };
    SizePx.create = function (value0) {
        return new SizePx(value0);
    };
    return SizePx;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var ShadowNone = /* #__PURE__ */ (function () {
    function ShadowNone() {

    };
    ShadowNone.value = new ShadowNone();
    return ShadowNone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var ShadowSm = /* #__PURE__ */ (function () {
    function ShadowSm() {

    };
    ShadowSm.value = new ShadowSm();
    return ShadowSm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var Shadow = /* #__PURE__ */ (function () {
    function Shadow() {

    };
    Shadow.value = new Shadow();
    return Shadow;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var ShadowMd = /* #__PURE__ */ (function () {
    function ShadowMd() {

    };
    ShadowMd.value = new ShadowMd();
    return ShadowMd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var ShadowLg = /* #__PURE__ */ (function () {
    function ShadowLg() {

    };
    ShadowLg.value = new ShadowLg();
    return ShadowLg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var ShadowXl = /* #__PURE__ */ (function () {
    function ShadowXl() {

    };
    ShadowXl.value = new ShadowXl();
    return ShadowXl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var Shadow2xl = /* #__PURE__ */ (function () {
    function Shadow2xl() {

    };
    Shadow2xl.value = new Shadow2xl();
    return Shadow2xl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // shadow
// ═══════════════════════════════════════════════════════════════════════════════
// | Shadow scale
var ShadowInner = /* #__PURE__ */ (function () {
    function ShadowInner() {

    };
    ShadowInner.value = new ShadowInner();
    return ShadowInner;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var RoundedNone = /* #__PURE__ */ (function () {
    function RoundedNone() {

    };
    RoundedNone.value = new RoundedNone();
    return RoundedNone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var RoundedSm = /* #__PURE__ */ (function () {
    function RoundedSm() {

    };
    RoundedSm.value = new RoundedSm();
    return RoundedSm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var Rounded = /* #__PURE__ */ (function () {
    function Rounded() {

    };
    Rounded.value = new Rounded();
    return Rounded;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var RoundedMd = /* #__PURE__ */ (function () {
    function RoundedMd() {

    };
    RoundedMd.value = new RoundedMd();
    return RoundedMd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var RoundedLg = /* #__PURE__ */ (function () {
    function RoundedLg() {

    };
    RoundedLg.value = new RoundedLg();
    return RoundedLg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var RoundedXl = /* #__PURE__ */ (function () {
    function RoundedXl() {

    };
    RoundedXl.value = new RoundedXl();
    return RoundedXl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var Rounded2xl = /* #__PURE__ */ (function () {
    function Rounded2xl() {

    };
    Rounded2xl.value = new Rounded2xl();
    return Rounded2xl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var Rounded3xl = /* #__PURE__ */ (function () {
    function Rounded3xl() {

    };
    Rounded3xl.value = new Rounded3xl();
    return Rounded3xl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // border radius
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius scale
var RoundedFull = /* #__PURE__ */ (function () {
    function RoundedFull() {

    };
    RoundedFull.value = new RoundedFull();
    return RoundedFull;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // padding
// ═══════════════════════════════════════════════════════════════════════════════
// | Padding values
var Padding = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // margin
// ═══════════════════════════════════════════════════════════════════════════════
// | Margin values
var Margin = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap values (for flex/grid)
var Gap = function (x) {
    return x;
};

// | Convert z-index to Tailwind class
var zIndex = function (v) {
    if (v instanceof Z0) {
        return "z-0";
    };
    if (v instanceof Z10) {
        return "z-10";
    };
    if (v instanceof Z20) {
        return "z-20";
    };
    if (v instanceof Z30) {
        return "z-30";
    };
    if (v instanceof Z40) {
        return "z-40";
    };
    if (v instanceof Z50) {
        return "z-50";
    };
    if (v instanceof ZAuto) {
        return "z-auto";
    };
    throw new Error("Failed pattern match at Hydrogen.Style.Token (line 385, column 10 - line 392, column 20): " + [ v.constructor.name ]);
};

// | Get spacing in pixels (at 16px base)
var spacingPx = function (v) {
    if (v instanceof S0) {
        return 0;
    };
    if (v instanceof S0_5) {
        return 2;
    };
    if (v instanceof S1) {
        return 4;
    };
    if (v instanceof S1_5) {
        return 6;
    };
    if (v instanceof S2) {
        return 8;
    };
    if (v instanceof S2_5) {
        return 10;
    };
    if (v instanceof S3) {
        return 12;
    };
    if (v instanceof S3_5) {
        return 14;
    };
    if (v instanceof S4) {
        return 16;
    };
    if (v instanceof S5) {
        return 20;
    };
    if (v instanceof S6) {
        return 24;
    };
    if (v instanceof S7) {
        return 28;
    };
    if (v instanceof S8) {
        return 32;
    };
    if (v instanceof S9) {
        return 36;
    };
    if (v instanceof S10) {
        return 40;
    };
    if (v instanceof S11) {
        return 44;
    };
    if (v instanceof S12) {
        return 48;
    };
    if (v instanceof S14) {
        return 56;
    };
    if (v instanceof S16) {
        return 64;
    };
    if (v instanceof S20) {
        return 80;
    };
    if (v instanceof S24) {
        return 96;
    };
    if (v instanceof S28) {
        return 112;
    };
    if (v instanceof S32) {
        return 128;
    };
    if (v instanceof S36) {
        return 144;
    };
    if (v instanceof S40) {
        return 160;
    };
    if (v instanceof S44) {
        return 176;
    };
    if (v instanceof S48) {
        return 192;
    };
    if (v instanceof S52) {
        return 208;
    };
    if (v instanceof S56) {
        return 224;
    };
    if (v instanceof S60) {
        return 240;
    };
    if (v instanceof S64) {
        return 256;
    };
    if (v instanceof S72) {
        return 288;
    };
    if (v instanceof S80) {
        return 320;
    };
    if (v instanceof S96) {
        return 384;
    };
    if (v instanceof SAuto) {
        return 0;
    };
    throw new Error("Failed pattern match at Hydrogen.Style.Token (line 169, column 13 - line 204, column 13): " + [ v.constructor.name ]);
};

// | Convert spacing to Tailwind class suffix
var spacing = function (v) {
    if (v instanceof S0) {
        return "0";
    };
    if (v instanceof S0_5) {
        return "0.5";
    };
    if (v instanceof S1) {
        return "1";
    };
    if (v instanceof S1_5) {
        return "1.5";
    };
    if (v instanceof S2) {
        return "2";
    };
    if (v instanceof S2_5) {
        return "2.5";
    };
    if (v instanceof S3) {
        return "3";
    };
    if (v instanceof S3_5) {
        return "3.5";
    };
    if (v instanceof S4) {
        return "4";
    };
    if (v instanceof S5) {
        return "5";
    };
    if (v instanceof S6) {
        return "6";
    };
    if (v instanceof S7) {
        return "7";
    };
    if (v instanceof S8) {
        return "8";
    };
    if (v instanceof S9) {
        return "9";
    };
    if (v instanceof S10) {
        return "10";
    };
    if (v instanceof S11) {
        return "11";
    };
    if (v instanceof S12) {
        return "12";
    };
    if (v instanceof S14) {
        return "14";
    };
    if (v instanceof S16) {
        return "16";
    };
    if (v instanceof S20) {
        return "20";
    };
    if (v instanceof S24) {
        return "24";
    };
    if (v instanceof S28) {
        return "28";
    };
    if (v instanceof S32) {
        return "32";
    };
    if (v instanceof S36) {
        return "36";
    };
    if (v instanceof S40) {
        return "40";
    };
    if (v instanceof S44) {
        return "44";
    };
    if (v instanceof S48) {
        return "48";
    };
    if (v instanceof S52) {
        return "52";
    };
    if (v instanceof S56) {
        return "56";
    };
    if (v instanceof S60) {
        return "60";
    };
    if (v instanceof S64) {
        return "64";
    };
    if (v instanceof S72) {
        return "72";
    };
    if (v instanceof S80) {
        return "80";
    };
    if (v instanceof S96) {
        return "96";
    };
    if (v instanceof SAuto) {
        return "auto";
    };
    throw new Error("Failed pattern match at Hydrogen.Style.Token (line 130, column 11 - line 165, column 18): " + [ v.constructor.name ]);
};
var sizeClass = function (prefix) {
    return function (v) {
        if (v instanceof SizeSpacing) {
            return prefix + ("-" + spacing(v.value0));
        };
        if (v instanceof SizeFull) {
            return prefix + "-full";
        };
        if (v instanceof SizeScreen) {
            return prefix + "-screen";
        };
        if (v instanceof SizeMin) {
            return prefix + "-min";
        };
        if (v instanceof SizeMax) {
            return prefix + "-max";
        };
        if (v instanceof SizeFit) {
            return prefix + "-fit";
        };
        if (v instanceof SizeAuto) {
            return prefix + "-auto";
        };
        if (v instanceof SizeFraction) {
            return prefix + ("-" + (show(v.value0) + ("/" + show(v.value1))));
        };
        if (v instanceof SizePx) {
            return prefix + ("-[" + (show(v.value0) + "px]"));
        };
        throw new Error("Failed pattern match at Hydrogen.Style.Token (line 441, column 20 - line 450, column 50): " + [ v.constructor.name ]);
    };
};

// | Width class
var width = /* #__PURE__ */ sizeClass("w");

// | Convert shadow to Tailwind class
var shadow = function (v) {
    if (v instanceof ShadowNone) {
        return "shadow-none";
    };
    if (v instanceof ShadowSm) {
        return "shadow-sm";
    };
    if (v instanceof Shadow) {
        return "shadow";
    };
    if (v instanceof ShadowMd) {
        return "shadow-md";
    };
    if (v instanceof ShadowLg) {
        return "shadow-lg";
    };
    if (v instanceof ShadowXl) {
        return "shadow-xl";
    };
    if (v instanceof Shadow2xl) {
        return "shadow-2xl";
    };
    if (v instanceof ShadowInner) {
        return "shadow-inner";
    };
    throw new Error("Failed pattern match at Hydrogen.Style.Token (line 356, column 10 - line 364, column 32): " + [ v.constructor.name ]);
};

// | Convert radius to Tailwind class
var radius = function (v) {
    if (v instanceof RoundedNone) {
        return "rounded-none";
    };
    if (v instanceof RoundedSm) {
        return "rounded-sm";
    };
    if (v instanceof Rounded) {
        return "rounded";
    };
    if (v instanceof RoundedMd) {
        return "rounded-md";
    };
    if (v instanceof RoundedLg) {
        return "rounded-lg";
    };
    if (v instanceof RoundedXl) {
        return "rounded-xl";
    };
    if (v instanceof Rounded2xl) {
        return "rounded-2xl";
    };
    if (v instanceof Rounded3xl) {
        return "rounded-3xl";
    };
    if (v instanceof RoundedFull) {
        return "rounded-full";
    };
    throw new Error("Failed pattern match at Hydrogen.Style.Token (line 325, column 10 - line 334, column 32): " + [ v.constructor.name ]);
};

// | Vertical padding (top and bottom)
var paddingY = function (s) {
    return "py-" + spacing(s);
};

// | Horizontal padding (left and right)
var paddingX = function (s) {
    return "px-" + spacing(s);
};

// | Top padding
var paddingT = function (s) {
    return "pt-" + spacing(s);
};

// | Right padding
var paddingR = function (s) {
    return "pr-" + spacing(s);
};

// | Left padding
var paddingL = function (s) {
    return "pl-" + spacing(s);
};

// | Bottom padding
var paddingB = function (s) {
    return "pb-" + spacing(s);
};

// | All sides padding
var padding = function (s) {
    return "p-" + spacing(s);
};

// | Min-width class
var minWidth = /* #__PURE__ */ sizeClass("min-w");

// | Min-height class
var minHeight = /* #__PURE__ */ sizeClass("min-h");

// | Max-width class
var maxWidth = /* #__PURE__ */ sizeClass("max-w");

// | Max-height class
var maxHeight = /* #__PURE__ */ sizeClass("max-h");

// | Vertical margin (top and bottom)
var marginY = function (s) {
    return "my-" + spacing(s);
};

// | Horizontal margin (left and right)
var marginX = function (s) {
    return "mx-" + spacing(s);
};

// | Top margin
var marginT = function (s) {
    return "mt-" + spacing(s);
};

// | Right margin
var marginR = function (s) {
    return "mr-" + spacing(s);
};

// | Left margin
var marginL = function (s) {
    return "ml-" + spacing(s);
};

// | Bottom margin
var marginB = function (s) {
    return "mb-" + spacing(s);
};

// | All sides margin
var margin = function (s) {
    return "m-" + spacing(s);
};

// | Height class
var height = /* #__PURE__ */ sizeClass("h");

// | Both width and height (square)
var size = function (s) {
    return width(s) + (" " + height(s));
};

// | Vertical gap
var gapY = function (s) {
    return "gap-y-" + spacing(s);
};

// | Horizontal gap
var gapX = function (s) {
    return "gap-x-" + spacing(s);
};

// | Gap (both directions)
var gap = function (s) {
    return "gap-" + spacing(s);
};
var eqZIndex = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Z0 && y instanceof Z0) {
                return true;
            };
            if (x instanceof Z10 && y instanceof Z10) {
                return true;
            };
            if (x instanceof Z20 && y instanceof Z20) {
                return true;
            };
            if (x instanceof Z30 && y instanceof Z30) {
                return true;
            };
            if (x instanceof Z40 && y instanceof Z40) {
                return true;
            };
            if (x instanceof Z50 && y instanceof Z50) {
                return true;
            };
            if (x instanceof ZAuto && y instanceof ZAuto) {
                return true;
            };
            return false;
        };
    }
};
var ordZIndex = {
    compare: function (x) {
        return function (y) {
            if (x instanceof Z0 && y instanceof Z0) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Z0) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Z0) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Z10 && y instanceof Z10) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Z10) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Z10) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Z20 && y instanceof Z20) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Z20) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Z20) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Z30 && y instanceof Z30) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Z30) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Z30) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Z40 && y instanceof Z40) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Z40) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Z40) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Z50 && y instanceof Z50) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Z50) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Z50) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof ZAuto && y instanceof ZAuto) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Style.Token (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqZIndex;
    }
};
var eqSpacing = {
    eq: function (x) {
        return function (y) {
            if (x instanceof S0 && y instanceof S0) {
                return true;
            };
            if (x instanceof S0_5 && y instanceof S0_5) {
                return true;
            };
            if (x instanceof S1 && y instanceof S1) {
                return true;
            };
            if (x instanceof S1_5 && y instanceof S1_5) {
                return true;
            };
            if (x instanceof S2 && y instanceof S2) {
                return true;
            };
            if (x instanceof S2_5 && y instanceof S2_5) {
                return true;
            };
            if (x instanceof S3 && y instanceof S3) {
                return true;
            };
            if (x instanceof S3_5 && y instanceof S3_5) {
                return true;
            };
            if (x instanceof S4 && y instanceof S4) {
                return true;
            };
            if (x instanceof S5 && y instanceof S5) {
                return true;
            };
            if (x instanceof S6 && y instanceof S6) {
                return true;
            };
            if (x instanceof S7 && y instanceof S7) {
                return true;
            };
            if (x instanceof S8 && y instanceof S8) {
                return true;
            };
            if (x instanceof S9 && y instanceof S9) {
                return true;
            };
            if (x instanceof S10 && y instanceof S10) {
                return true;
            };
            if (x instanceof S11 && y instanceof S11) {
                return true;
            };
            if (x instanceof S12 && y instanceof S12) {
                return true;
            };
            if (x instanceof S14 && y instanceof S14) {
                return true;
            };
            if (x instanceof S16 && y instanceof S16) {
                return true;
            };
            if (x instanceof S20 && y instanceof S20) {
                return true;
            };
            if (x instanceof S24 && y instanceof S24) {
                return true;
            };
            if (x instanceof S28 && y instanceof S28) {
                return true;
            };
            if (x instanceof S32 && y instanceof S32) {
                return true;
            };
            if (x instanceof S36 && y instanceof S36) {
                return true;
            };
            if (x instanceof S40 && y instanceof S40) {
                return true;
            };
            if (x instanceof S44 && y instanceof S44) {
                return true;
            };
            if (x instanceof S48 && y instanceof S48) {
                return true;
            };
            if (x instanceof S52 && y instanceof S52) {
                return true;
            };
            if (x instanceof S56 && y instanceof S56) {
                return true;
            };
            if (x instanceof S60 && y instanceof S60) {
                return true;
            };
            if (x instanceof S64 && y instanceof S64) {
                return true;
            };
            if (x instanceof S72 && y instanceof S72) {
                return true;
            };
            if (x instanceof S80 && y instanceof S80) {
                return true;
            };
            if (x instanceof S96 && y instanceof S96) {
                return true;
            };
            if (x instanceof SAuto && y instanceof SAuto) {
                return true;
            };
            return false;
        };
    }
};
var eq1 = /* #__PURE__ */ Data_Eq.eq(eqSpacing);
var ordSpacing = {
    compare: function (x) {
        return function (y) {
            if (x instanceof S0 && y instanceof S0) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S0) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S0) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S0_5 && y instanceof S0_5) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S0_5) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S0_5) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S1 && y instanceof S1) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S1) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S1) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S1_5 && y instanceof S1_5) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S1_5) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S1_5) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S2 && y instanceof S2) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S2) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S2) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S2_5 && y instanceof S2_5) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S2_5) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S2_5) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S3 && y instanceof S3) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S3) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S3) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S3_5 && y instanceof S3_5) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S3_5) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S3_5) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S4 && y instanceof S4) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S4) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S4) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S5 && y instanceof S5) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S5) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S5) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S6 && y instanceof S6) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S6) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S6) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S7 && y instanceof S7) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S7) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S7) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S8 && y instanceof S8) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S8) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S8) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S9 && y instanceof S9) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S9) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S9) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S10 && y instanceof S10) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S10) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S10) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S11 && y instanceof S11) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S11) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S11) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S12 && y instanceof S12) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S12) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S12) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S14 && y instanceof S14) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S14) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S14) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S16 && y instanceof S16) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S16) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S16) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S20 && y instanceof S20) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S20) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S20) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S24 && y instanceof S24) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S24) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S24) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S28 && y instanceof S28) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S28) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S28) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S32 && y instanceof S32) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S32) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S32) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S36 && y instanceof S36) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S36) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S36) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S40 && y instanceof S40) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S40) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S40) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S44 && y instanceof S44) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S44) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S44) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S48 && y instanceof S48) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S48) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S48) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S52 && y instanceof S52) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S52) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S52) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S56 && y instanceof S56) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S56) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S56) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S60 && y instanceof S60) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S60) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S60) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S64 && y instanceof S64) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S64) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S64) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S72 && y instanceof S72) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S72) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S72) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S80 && y instanceof S80) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S80) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S80) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof S96 && y instanceof S96) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof S96) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof S96) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof SAuto && y instanceof SAuto) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Style.Token (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqSpacing;
    }
};
var ordGap = ordSpacing;
var ordMargin = ordSpacing;
var ordPadding = ordSpacing;
var eqSize = {
    eq: function (x) {
        return function (y) {
            if (x instanceof SizeSpacing && y instanceof SizeSpacing) {
                return eq1(x.value0)(y.value0);
            };
            if (x instanceof SizeFull && y instanceof SizeFull) {
                return true;
            };
            if (x instanceof SizeScreen && y instanceof SizeScreen) {
                return true;
            };
            if (x instanceof SizeMin && y instanceof SizeMin) {
                return true;
            };
            if (x instanceof SizeMax && y instanceof SizeMax) {
                return true;
            };
            if (x instanceof SizeFit && y instanceof SizeFit) {
                return true;
            };
            if (x instanceof SizeAuto && y instanceof SizeAuto) {
                return true;
            };
            if (x instanceof SizeFraction && y instanceof SizeFraction) {
                return x.value0 === y.value0 && x.value1 === y.value1;
            };
            if (x instanceof SizePx && y instanceof SizePx) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eqShadow = {
    eq: function (x) {
        return function (y) {
            if (x instanceof ShadowNone && y instanceof ShadowNone) {
                return true;
            };
            if (x instanceof ShadowSm && y instanceof ShadowSm) {
                return true;
            };
            if (x instanceof Shadow && y instanceof Shadow) {
                return true;
            };
            if (x instanceof ShadowMd && y instanceof ShadowMd) {
                return true;
            };
            if (x instanceof ShadowLg && y instanceof ShadowLg) {
                return true;
            };
            if (x instanceof ShadowXl && y instanceof ShadowXl) {
                return true;
            };
            if (x instanceof Shadow2xl && y instanceof Shadow2xl) {
                return true;
            };
            if (x instanceof ShadowInner && y instanceof ShadowInner) {
                return true;
            };
            return false;
        };
    }
};
var ordShadow = {
    compare: function (x) {
        return function (y) {
            if (x instanceof ShadowNone && y instanceof ShadowNone) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof ShadowNone) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof ShadowNone) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof ShadowSm && y instanceof ShadowSm) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof ShadowSm) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof ShadowSm) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Shadow && y instanceof Shadow) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Shadow) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Shadow) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof ShadowMd && y instanceof ShadowMd) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof ShadowMd) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof ShadowMd) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof ShadowLg && y instanceof ShadowLg) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof ShadowLg) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof ShadowLg) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof ShadowXl && y instanceof ShadowXl) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof ShadowXl) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof ShadowXl) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Shadow2xl && y instanceof Shadow2xl) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Shadow2xl) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Shadow2xl) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof ShadowInner && y instanceof ShadowInner) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Style.Token (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqShadow;
    }
};
var eqRadius = {
    eq: function (x) {
        return function (y) {
            if (x instanceof RoundedNone && y instanceof RoundedNone) {
                return true;
            };
            if (x instanceof RoundedSm && y instanceof RoundedSm) {
                return true;
            };
            if (x instanceof Rounded && y instanceof Rounded) {
                return true;
            };
            if (x instanceof RoundedMd && y instanceof RoundedMd) {
                return true;
            };
            if (x instanceof RoundedLg && y instanceof RoundedLg) {
                return true;
            };
            if (x instanceof RoundedXl && y instanceof RoundedXl) {
                return true;
            };
            if (x instanceof Rounded2xl && y instanceof Rounded2xl) {
                return true;
            };
            if (x instanceof Rounded3xl && y instanceof Rounded3xl) {
                return true;
            };
            if (x instanceof RoundedFull && y instanceof RoundedFull) {
                return true;
            };
            return false;
        };
    }
};
var ordRadius = {
    compare: function (x) {
        return function (y) {
            if (x instanceof RoundedNone && y instanceof RoundedNone) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof RoundedNone) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof RoundedNone) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof RoundedSm && y instanceof RoundedSm) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof RoundedSm) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof RoundedSm) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Rounded && y instanceof Rounded) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Rounded) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Rounded) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof RoundedMd && y instanceof RoundedMd) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof RoundedMd) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof RoundedMd) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof RoundedLg && y instanceof RoundedLg) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof RoundedLg) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof RoundedLg) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof RoundedXl && y instanceof RoundedXl) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof RoundedXl) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof RoundedXl) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Rounded2xl && y instanceof Rounded2xl) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Rounded2xl) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Rounded2xl) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Rounded3xl && y instanceof Rounded3xl) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Rounded3xl) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Rounded3xl) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof RoundedFull && y instanceof RoundedFull) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Style.Token (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqRadius;
    }
};
var eqPadding = {
    eq: function (x) {
        return function (y) {
            return eq1(x)(y);
        };
    }
};
var eqMargin = {
    eq: function (x) {
        return function (y) {
            return eq1(x)(y);
        };
    }
};
var eqGap = {
    eq: function (x) {
        return function (y) {
            return eq1(x)(y);
        };
    }
};
export {
    S0,
    S0_5,
    S1,
    S1_5,
    S2,
    S2_5,
    S3,
    S3_5,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    S12,
    S14,
    S16,
    S20,
    S24,
    S28,
    S32,
    S36,
    S40,
    S44,
    S48,
    S52,
    S56,
    S60,
    S64,
    S72,
    S80,
    S96,
    SAuto,
    spacing,
    spacingPx,
    Padding,
    padding,
    paddingX,
    paddingY,
    paddingT,
    paddingB,
    paddingL,
    paddingR,
    Margin,
    margin,
    marginX,
    marginY,
    marginT,
    marginB,
    marginL,
    marginR,
    Gap,
    gap,
    gapX,
    gapY,
    RoundedNone,
    RoundedSm,
    Rounded,
    RoundedMd,
    RoundedLg,
    RoundedXl,
    Rounded2xl,
    Rounded3xl,
    RoundedFull,
    radius,
    ShadowNone,
    ShadowSm,
    Shadow,
    ShadowMd,
    ShadowLg,
    ShadowXl,
    Shadow2xl,
    ShadowInner,
    shadow,
    Z0,
    Z10,
    Z20,
    Z30,
    Z40,
    Z50,
    ZAuto,
    zIndex,
    SizeSpacing,
    SizeFull,
    SizeScreen,
    SizeMin,
    SizeMax,
    SizeFit,
    SizeAuto,
    SizeFraction,
    SizePx,
    width,
    height,
    size,
    minWidth,
    maxWidth,
    minHeight,
    maxHeight,
    eqSpacing,
    ordSpacing,
    eqPadding,
    ordPadding,
    eqMargin,
    ordMargin,
    eqGap,
    ordGap,
    eqRadius,
    ordRadius,
    eqShadow,
    ordShadow,
    eqZIndex,
    ordZIndex,
    eqSize
};
