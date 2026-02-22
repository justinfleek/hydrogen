// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // icon // 3d
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Base 3D icon component and utilities
// |
// | This module provides the foundation for rendering 3D icons using Three.js:
// | - Icon3DProps for consistent icon configuration
// | - Helper functions for creating 3D icon components
// | - Size, color, and material utilities
// | - Composable primitives for building complex icons
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Icon.Icon3D as Icon3D
// | import Hydrogen.Icon.Icons3D as Icons3D
// |
// | -- Render a 3D icon with default settings
// | Icons3D.check []
// |
// | -- With custom size
// | Icons3D.check [ Icon3D.size Icon3D.Lg ]
// |
// | -- With custom material
// | Icons3D.check [ Icon3D.material Icon3D.metallic ]
// |
// | -- With animation
// | Icons3D.check [ Icon3D.animate Icon3D.Rotate ]
// |
// | -- Interactive
// | Icons3D.check [ Icon3D.onClick HandleClick ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var eq2 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Maybe.eqMaybe(Data_Eq.eqString));
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // material variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Material variant for icon parts — determines surface treatment
var MatteVariant = /* #__PURE__ */ (function () {
    function MatteVariant() {

    };
    MatteVariant.value = new MatteVariant();
    return MatteVariant;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // material variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Material variant for icon parts — determines surface treatment
var GlossyVariant = /* #__PURE__ */ (function () {
    function GlossyVariant() {

    };
    GlossyVariant.value = new GlossyVariant();
    return GlossyVariant;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // material variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Material variant for icon parts — determines surface treatment
var ChromeVariant = /* #__PURE__ */ (function () {
    function ChromeVariant() {

    };
    ChromeVariant.value = new ChromeVariant();
    return ChromeVariant;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // material variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Material variant for icon parts — determines surface treatment
var MetallicVariant = /* #__PURE__ */ (function () {
    function MetallicVariant() {

    };
    MetallicVariant.value = new MetallicVariant();
    return MetallicVariant;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // material variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Material variant for icon parts — determines surface treatment
var SoftVariant = /* #__PURE__ */ (function () {
    function SoftVariant() {

    };
    SoftVariant.value = new SoftVariant();
    return SoftVariant;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon styles
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon style presets for consistent theming
var DarkChrome = /* #__PURE__ */ (function () {
    function DarkChrome() {

    };
    DarkChrome.value = new DarkChrome();
    return DarkChrome;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon styles
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon style presets for consistent theming
var DarkOrange = /* #__PURE__ */ (function () {
    function DarkOrange() {

    };
    DarkOrange.value = new DarkOrange();
    return DarkOrange;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon styles
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon style presets for consistent theming
var BlueMetal = /* #__PURE__ */ (function () {
    function BlueMetal() {

    };
    BlueMetal.value = new BlueMetal();
    return BlueMetal;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon styles
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon style presets for consistent theming
var Isometric = /* #__PURE__ */ (function () {
    function Isometric() {

    };
    Isometric.value = new Isometric();
    return Isometric;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon styles
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon style presets for consistent theming
var Bold = /* #__PURE__ */ (function () {
    function Bold() {

    };
    Bold.value = new Bold();
    return Bold;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Xs = /* #__PURE__ */ (function () {
    function Xs() {

    };
    Xs.value = new Xs();
    return Xs;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Sm = /* #__PURE__ */ (function () {
    function Sm() {

    };
    Sm.value = new Sm();
    return Sm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Md = /* #__PURE__ */ (function () {
    function Md() {

    };
    Md.value = new Md();
    return Md;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Lg = /* #__PURE__ */ (function () {
    function Lg() {

    };
    Lg.value = new Lg();
    return Lg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Xl = /* #__PURE__ */ (function () {
    function Xl() {

    };
    Xl.value = new Xl();
    return Xl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Xxl = /* #__PURE__ */ (function () {
    function Xxl() {

    };
    Xxl.value = new Xxl();
    return Xxl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard 3D icon sizes (in scene units)
var Custom = /* #__PURE__ */ (function () {
    function Custom(value0) {
        this.value0 = value0;
    };
    Custom.create = function (value0) {
        return new Custom(value0);
    };
    return Custom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Rotate = /* #__PURE__ */ (function () {
    function Rotate() {

    };
    Rotate.value = new Rotate();
    return Rotate;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var RotateX = /* #__PURE__ */ (function () {
    function RotateX() {

    };
    RotateX.value = new RotateX();
    return RotateX;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var RotateZ = /* #__PURE__ */ (function () {
    function RotateZ() {

    };
    RotateZ.value = new RotateZ();
    return RotateZ;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Bounce = /* #__PURE__ */ (function () {
    function Bounce() {

    };
    Bounce.value = new Bounce();
    return Bounce;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Pulse = /* #__PURE__ */ (function () {
    function Pulse() {

    };
    Pulse.value = new Pulse();
    return Pulse;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Float = /* #__PURE__ */ (function () {
    function Float() {

    };
    Float.value = new Float();
    return Float;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Spin = /* #__PURE__ */ (function () {
    function Spin() {

    };
    Spin.value = new Spin();
    return Spin;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Wobble = /* #__PURE__ */ (function () {
    function Wobble() {

    };
    Wobble.value = new Wobble();
    return Wobble;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var Flip = /* #__PURE__ */ (function () {
    function Flip() {

    };
    Flip.value = new Flip();
    return Flip;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // animations
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D icon animations
var CustomAnimation = /* #__PURE__ */ (function () {
    function CustomAnimation(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    CustomAnimation.create = function (value0) {
        return function (value1) {
            return new CustomAnimation(value0, value1);
        };
    };
    return CustomAnimation;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveBox = /* #__PURE__ */ (function () {
    function PrimitiveBox(value0) {
        this.value0 = value0;
    };
    PrimitiveBox.create = function (value0) {
        return new PrimitiveBox(value0);
    };
    return PrimitiveBox;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveRoundedBox = /* #__PURE__ */ (function () {
    function PrimitiveRoundedBox(value0) {
        this.value0 = value0;
    };
    PrimitiveRoundedBox.create = function (value0) {
        return new PrimitiveRoundedBox(value0);
    };
    return PrimitiveRoundedBox;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveSphere = /* #__PURE__ */ (function () {
    function PrimitiveSphere(value0) {
        this.value0 = value0;
    };
    PrimitiveSphere.create = function (value0) {
        return new PrimitiveSphere(value0);
    };
    return PrimitiveSphere;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveCylinder = /* #__PURE__ */ (function () {
    function PrimitiveCylinder(value0) {
        this.value0 = value0;
    };
    PrimitiveCylinder.create = function (value0) {
        return new PrimitiveCylinder(value0);
    };
    return PrimitiveCylinder;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveCapsule = /* #__PURE__ */ (function () {
    function PrimitiveCapsule(value0) {
        this.value0 = value0;
    };
    PrimitiveCapsule.create = function (value0) {
        return new PrimitiveCapsule(value0);
    };
    return PrimitiveCapsule;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveCone = /* #__PURE__ */ (function () {
    function PrimitiveCone(value0) {
        this.value0 = value0;
    };
    PrimitiveCone.create = function (value0) {
        return new PrimitiveCone(value0);
    };
    return PrimitiveCone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveTorus = /* #__PURE__ */ (function () {
    function PrimitiveTorus(value0) {
        this.value0 = value0;
    };
    PrimitiveTorus.create = function (value0) {
        return new PrimitiveTorus(value0);
    };
    return PrimitiveTorus;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitivePlane = /* #__PURE__ */ (function () {
    function PrimitivePlane(value0) {
        this.value0 = value0;
    };
    PrimitivePlane.create = function (value0) {
        return new PrimitivePlane(value0);
    };
    return PrimitivePlane;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // primitives
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon primitive types for building 3D icons
var PrimitiveGroup = /* #__PURE__ */ (function () {
    function PrimitiveGroup(value0) {
        this.value0 = value0;
    };
    PrimitiveGroup.create = function (value0) {
        return new PrimitiveGroup(value0);
    };
    return PrimitiveGroup;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // brand palette
// ═══════════════════════════════════════════════════════════════════════════════
// | Brand color slot — which brand color to use for an icon part
var Primary = /* #__PURE__ */ (function () {
    function Primary() {

    };
    Primary.value = new Primary();
    return Primary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // brand palette
// ═══════════════════════════════════════════════════════════════════════════════
// | Brand color slot — which brand color to use for an icon part
var Secondary = /* #__PURE__ */ (function () {
    function Secondary() {

    };
    Secondary.value = new Secondary();
    return Secondary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // brand palette
// ═══════════════════════════════════════════════════════════════════════════════
// | Brand color slot — which brand color to use for an icon part
var Accent = /* #__PURE__ */ (function () {
    function Accent() {

    };
    Accent.value = new Accent();
    return Accent;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // brand palette
// ═══════════════════════════════════════════════════════════════════════════════
// | Brand color slot — which brand color to use for an icon part
var Neutral = /* #__PURE__ */ (function () {
    function Neutral() {

    };
    Neutral.value = new Neutral();
    return Neutral;
})();

// | Zero vector
var zero3 = {
    x: 0.0,
    y: 0.0,
    z: 0.0
};

// | Set wireframe mode
var wireframe = function (b) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            wireframe: b
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // internal
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert Vector3 to string
var vector3ToString = function (v) {
    return show(v.x) + ("," + (show(v.y) + ("," + show(v.z))));
};

// | Create a vector
var vec3 = function (x) {
    return function (y) {
        return function (z) {
            return {
                x: x,
                y: y,
                z: z
            };
        };
    };
};

// | Get default palette for a style
var stylePalette = function (v) {
    if (v instanceof DarkChrome) {
        return {
            primary: "#374151",
            secondary: "#1f2937",
            accent: "#e5e7eb",
            neutral: "#4b5563"
        };
    };
    if (v instanceof DarkOrange) {
        return {
            primary: "#1f2937",
            secondary: "#374151",
            accent: "#f97316",
            neutral: "#4b5563"
        };
    };
    if (v instanceof BlueMetal) {
        return {
            primary: "#3b82f6",
            secondary: "#1e40af",
            accent: "#93c5fd",
            neutral: "#64748b"
        };
    };
    if (v instanceof Isometric) {
        return {
            primary: "#8b5cf6",
            secondary: "#a78bfa",
            accent: "#fbbf24",
            neutral: "#e2e8f0"
        };
    };
    if (v instanceof Bold) {
        return {
            primary: "#ef4444",
            secondary: "#1f2937",
            accent: "#fbbf24",
            neutral: "#f3f4f6"
        };
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 211, column 16 - line 241, column 6): " + [ v.constructor.name ]);
};

// | Soft plastic material — toy-like, friendly appearance
// | Higher clearcoat for that plastic sheen
var softPlastic = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.35,
        metalness: 5.0e-2,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.6,
        clearcoatRoughness: 0.2
    };
})();

// | Soft pastel material — dreamy, light appearance
// | Slight transparency and emissive for ethereal quality
var softPastel = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.55,
        metalness: 8.0e-2,
        opacity: 0.95,
        transparent: true,
        emissive: new Data_Maybe.Just("#ffffff"),
        emissiveIntensity: 0.15,
        clearcoat: 0.2,
        clearcoatRoughness: 0.6
    };
})();

// | Soft gradient material — subtle emissive glow for depth
// | Pairs well with gradient-colored icons
var softGradient = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.45,
        metalness: 0.15,
        opacity: 1.0,
        transparent: false,
        emissive: new Data_Maybe.Just("#ffffff"),
        emissiveIntensity: 0.1,
        clearcoat: 0.25,
        clearcoatRoughness: 0.5
    };
})();

// | Soft clay material — matte, organic feel
// | No clearcoat, higher roughness for that sculpted look
var softClay = /* #__PURE__ */ (function () {
    return {
        materialType: "standard",
        roughness: 0.7,
        metalness: 0.0,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.0,
        clearcoatRoughness: 0.0
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // soft / isometric materials
// ═══════════════════════════════════════════════════════════════════════════════
// | Soft material — the default isometric SaaS style
// | Low metalness, medium roughness, subtle clearcoat for that soft shine
var soft = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.5,
        metalness: 0.1,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.3,
        clearcoatRoughness: 0.4
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set icon size
var size = function (s) {
    return function (props) {
        return {
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            size: s
        };
    };
};

// | Set icon rotation
var rotation = function (r) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            rotation: r
        };
    };
};

// | Resolve brand slot to actual color
var resolveSlot = function (pal) {
    return function (v) {
        if (v instanceof Primary) {
            return pal.primary;
        };
        if (v instanceof Secondary) {
            return pal.secondary;
        };
        if (v instanceof Accent) {
            return pal.accent;
        };
        if (v instanceof Neutral) {
            return pal.neutral;
        };
        throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 189, column 19 - line 193, column 25): " + [ v.constructor.name ]);
    };
};

// | Set receive shadow
var receiveShadow = function (b) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            receiveShadow: b
        };
    };
};

// | Create a torus primitive
var primitiveTorus = function (radius) {
    return function (tube) {
        return function (p) {
            return function (r) {
                return new PrimitiveTorus({
                    radius: radius,
                    tube: tube,
                    position: p,
                    rotation: r
                });
            };
        };
    };
};

// | Create a sphere primitive
var primitiveSphere = function (radius) {
    return function (p) {
        return new PrimitiveSphere({
            radius: radius,
            position: p
        });
    };
};

// | Create a rounded box primitive (beveled corners)
var primitiveRoundedBox = function (s) {
    return function (rad) {
        return function (p) {
            return function (r) {
                return new PrimitiveRoundedBox({
                    size: s,
                    radius: rad,
                    position: p,
                    rotation: r
                });
            };
        };
    };
};

// | Create a plane primitive
var primitivePlane = function (w) {
    return function (h) {
        return function (p) {
            return function (r) {
                return new PrimitivePlane({
                    width: w,
                    height: h,
                    position: p,
                    rotation: r
                });
            };
        };
    };
};

// | Group primitives together
var primitiveGroup = /* #__PURE__ */ (function () {
    return PrimitiveGroup.create;
})();

// | Create a cylinder primitive
var primitiveCylinder = function (rTop) {
    return function (rBot) {
        return function (h) {
            return function (p) {
                return function (r) {
                    return new PrimitiveCylinder({
                        radiusTop: rTop,
                        radiusBottom: rBot,
                        height: h,
                        position: p,
                        rotation: r
                    });
                };
            };
        };
    };
};

// | Create a cone primitive
var primitiveCone = function (radius) {
    return function (h) {
        return function (p) {
            return function (r) {
                return new PrimitiveCone({
                    radius: radius,
                    height: h,
                    position: p,
                    rotation: r
                });
            };
        };
    };
};

// | Create a capsule primitive (cylinder with hemispherical caps)
var primitiveCapsule = function (rad) {
    return function (len) {
        return function (p) {
            return function (r) {
                return new PrimitiveCapsule({
                    radius: rad,
                    length: len,
                    position: p,
                    rotation: r
                });
            };
        };
    };
};

// | Create a box primitive
var primitiveBox = function (s) {
    return function (p) {
        return function (r) {
            return new PrimitiveBox({
                size: s,
                position: p,
                rotation: r
            });
        };
    };
};

// | Set icon position
var position = function (p) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            position: p
        };
    };
};

// | Set brand palette
var palette = function (p) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            iconStyle: props.iconStyle,
            brandPalette: p
        };
    };
};

// | Unit vector
var one3 = {
    x: 1.0,
    y: 1.0,
    z: 1.0
};

// | Set hover handler
var onHover = function (handler) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            onHover: new Data_Maybe.Just(handler)
        };
    };
};

// | Set click handler
var onClick = function (handler) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            onClick: new Data_Maybe.Just(handler)
        };
    };
};

// | Neon material (glowing)
var neon = /* #__PURE__ */ (function () {
    return {
        materialType: "standard",
        roughness: 0.3,
        metalness: 0.0,
        opacity: 1.0,
        transparent: false,
        emissive: new Data_Maybe.Just("#ffffff"),
        emissiveIntensity: 0.8,
        clearcoat: 0.0,
        clearcoatRoughness: 0.0
    };
})();

// | Metallic material (chrome-like)
var metallic = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.1,
        metalness: 0.9,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.5,
        clearcoatRoughness: 0.1
    };
})();

// | Matte material (flat, no shine)
var matte = /* #__PURE__ */ (function () {
    return {
        materialType: "standard",
        roughness: 1.0,
        metalness: 0.0,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.0,
        clearcoatRoughness: 0.0
    };
})();

// | Convert material to string
var materialToString = function (m) {
    var emissiveStr = function (v) {
        if (v instanceof Data_Maybe.Just) {
            return ";emissive=" + v.value0;
        };
        if (v instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 1057, column 3 - line 1057, column 43): " + [ v.constructor.name ]);
    };
    return "type=" + (m.materialType + (";roughness=" + (show(m.roughness) + (";metalness=" + (show(m.metalness) + (";opacity=" + (show(m.opacity) + (";transparent=" + (show1(m.transparent) + (emissiveStr(m.emissive) + (";emissiveIntensity=" + (show(m.emissiveIntensity) + (";clearcoat=" + (show(m.clearcoat) + (";clearcoatRoughness=" + show(m.clearcoatRoughness))))))))))))))));
};

// | Set icon material
var material = function (m) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            material: m
        };
    };
};

// | Get scale factor for icon size
var iconSizeScale = function (v) {
    if (v instanceof Xs) {
        return 0.5;
    };
    if (v instanceof Sm) {
        return 0.75;
    };
    if (v instanceof Md) {
        return 1.0;
    };
    if (v instanceof Lg) {
        return 1.5;
    };
    if (v instanceof Xl) {
        return 2.0;
    };
    if (v instanceof Xxl) {
        return 3.0;
    };
    if (v instanceof Custom) {
        return v.value0;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 401, column 17 - line 408, column 16): " + [ v.constructor.name ]);
};

// | Create an icon part
var iconPart = function (slot) {
    return function (variant) {
        return function (prim) {
            return {
                primitive: prim,
                brandSlot: slot,
                materialVariant: variant
            };
        };
    };
};

// | Glass material (transparent, refractive)
var glass = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.0,
        metalness: 0.0,
        opacity: 0.3,
        transparent: true,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 1.0,
        clearcoatRoughness: 0.0
    };
})();

// | Convert Euler to string
var eulerToString = function (e) {
    return show(e.x) + ("," + (show(e.y) + ("," + show(e.z))));
};

// | Convert primitive to HTML representation (for JS to parse)
var primitiveToHtml = function (v) {
    if (v instanceof PrimitiveBox) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("box"), Halogen_HTML_Properties.attr("data-size")(vector3ToString(v.value0.size)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveRoundedBox) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("rounded-box"), Halogen_HTML_Properties.attr("data-size")(vector3ToString(v.value0.size)), Halogen_HTML_Properties.attr("data-radius")(show(v.value0.radius)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveSphere) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("sphere"), Halogen_HTML_Properties.attr("data-radius")(show(v.value0.radius)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveCylinder) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("cylinder"), Halogen_HTML_Properties.attr("data-radius-top")(show(v.value0.radiusTop)), Halogen_HTML_Properties.attr("data-radius-bottom")(show(v.value0.radiusBottom)), Halogen_HTML_Properties.attr("data-height")(show(v.value0.height)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveCapsule) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("capsule"), Halogen_HTML_Properties.attr("data-radius")(show(v.value0.radius)), Halogen_HTML_Properties.attr("data-length")(show(v.value0.length)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveCone) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("cone"), Halogen_HTML_Properties.attr("data-radius")(show(v.value0.radius)), Halogen_HTML_Properties.attr("data-height")(show(v.value0.height)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveTorus) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("torus"), Halogen_HTML_Properties.attr("data-radius")(show(v.value0.radius)), Halogen_HTML_Properties.attr("data-tube")(show(v.value0.tube)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitivePlane) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("plane"), Halogen_HTML_Properties.attr("data-width")(show(v.value0.width)), Halogen_HTML_Properties.attr("data-height")(show(v.value0.height)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(v.value0.position)), Halogen_HTML_Properties.attr("data-rotation")(eulerToString(v.value0.rotation)), Halogen_HTML_Properties.style("display: none") ])([  ]);
    };
    if (v instanceof PrimitiveGroup) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("group"), Halogen_HTML_Properties.style("display: none") ])(map(primitiveToHtml)(v.value0));
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 938, column 19 - line 1030, column 37): " + [ v.constructor.name ]);
};

// | Create euler angles
var euler = function (x) {
    return function (y) {
        return function (z) {
            return {
                x: x,
                y: y,
                z: z
            };
        };
    };
};
var eqMaterialVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof MatteVariant && y instanceof MatteVariant) {
                return true;
            };
            if (x instanceof GlossyVariant && y instanceof GlossyVariant) {
                return true;
            };
            if (x instanceof ChromeVariant && y instanceof ChromeVariant) {
                return true;
            };
            if (x instanceof MetallicVariant && y instanceof MetallicVariant) {
                return true;
            };
            if (x instanceof SoftVariant && y instanceof SoftVariant) {
                return true;
            };
            return false;
        };
    }
};
var eqIconStyle = {
    eq: function (x) {
        return function (y) {
            if (x instanceof DarkChrome && y instanceof DarkChrome) {
                return true;
            };
            if (x instanceof DarkOrange && y instanceof DarkOrange) {
                return true;
            };
            if (x instanceof BlueMetal && y instanceof BlueMetal) {
                return true;
            };
            if (x instanceof Isometric && y instanceof Isometric) {
                return true;
            };
            if (x instanceof Bold && y instanceof Bold) {
                return true;
            };
            return false;
        };
    }
};
var eqIcon3DSize = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Xs && y instanceof Xs) {
                return true;
            };
            if (x instanceof Sm && y instanceof Sm) {
                return true;
            };
            if (x instanceof Md && y instanceof Md) {
                return true;
            };
            if (x instanceof Lg && y instanceof Lg) {
                return true;
            };
            if (x instanceof Xl && y instanceof Xl) {
                return true;
            };
            if (x instanceof Xxl && y instanceof Xxl) {
                return true;
            };
            if (x instanceof Custom && y instanceof Custom) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eqIcon3DAnimation = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Rotate && y instanceof Rotate) {
                return true;
            };
            if (x instanceof RotateX && y instanceof RotateX) {
                return true;
            };
            if (x instanceof RotateZ && y instanceof RotateZ) {
                return true;
            };
            if (x instanceof Bounce && y instanceof Bounce) {
                return true;
            };
            if (x instanceof Pulse && y instanceof Pulse) {
                return true;
            };
            if (x instanceof Float && y instanceof Float) {
                return true;
            };
            if (x instanceof Spin && y instanceof Spin) {
                return true;
            };
            if (x instanceof Wobble && y instanceof Wobble) {
                return true;
            };
            if (x instanceof Flip && y instanceof Flip) {
                return true;
            };
            if (x instanceof CustomAnimation && y instanceof CustomAnimation) {
                return x.value0 === y.value0 && x.value1 === y.value1;
            };
            return false;
        };
    }
};
var eqBrandSlot = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Primary && y instanceof Primary) {
                return true;
            };
            if (x instanceof Secondary && y instanceof Secondary) {
                return true;
            };
            if (x instanceof Accent && y instanceof Accent) {
                return true;
            };
            if (x instanceof Neutral && y instanceof Neutral) {
                return true;
            };
            return false;
        };
    }
};

// | Default brand palette (blue theme)
var defaultPalette = {
    primary: "#3b82f6",
    secondary: "#1e293b",
    accent: "#f97316",
    neutral: "#64748b"
};

// | Default material (standard PBR)
var defaultMaterial = /* #__PURE__ */ (function () {
    return {
        materialType: "standard",
        roughness: 0.4,
        metalness: 0.1,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.0,
        clearcoatRoughness: 0.0
    };
})();

// | Default icon properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        size: Md.value,
        color: "#3b82f6",
        material: defaultMaterial,
        position: zero3,
        rotation: zero3,
        animation: Data_Maybe.Nothing.value,
        castShadow: true,
        receiveShadow: true,
        wireframe: false,
        onClick: Data_Maybe.Nothing.value,
        onHover: Data_Maybe.Nothing.value,
        className: "",
        brandPalette: defaultPalette,
        iconStyle: Data_Maybe.Nothing.value
    };
})();

// | Dark chrome accent — brighter chrome for highlights and details
var darkChromeAccent = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.1,
        metalness: 0.95,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.9,
        clearcoatRoughness: 5.0e-2
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // premium 3d materials
// ═══════════════════════════════════════════════════════════════════════════════
// | Dark chrome material — gunmetal finish with subtle reflections
var darkChrome = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.25,
        metalness: 0.85,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.7,
        clearcoatRoughness: 0.15
    };
})();

// | Custom material builder
var customMaterial = function (config) {
    return {
        materialType: (function () {
            var $114 = config.metalness > 0.5;
            if ($114) {
                return "physical";
            };
            return "standard";
        })(),
        roughness: config.roughness,
        metalness: config.metalness,
        opacity: config.opacity,
        transparent: config.opacity < 1.0,
        emissive: config.emissive,
        emissiveIntensity: (function () {
            var $115 = eq2(config.emissive)(Data_Maybe.Nothing.value);
            if ($115) {
                return 0.0;
            };
            return 0.5;
        })(),
        clearcoat: 0.0,
        clearcoatRoughness: 0.0
    };
};

// | Set icon color
var color = function (c) {
    return function (props) {
        return {
            size: props.size,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            color: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            className: props.className + (" " + c)
        };
    };
};

// | Set cast shadow
var castShadow = function (b) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            castShadow: b
        };
    };
};

// | Convert brand slot to string
var brandSlotToString = function (v) {
    if (v instanceof Primary) {
        return "primary";
    };
    if (v instanceof Secondary) {
        return "secondary";
    };
    if (v instanceof Accent) {
        return "accent";
    };
    if (v instanceof Neutral) {
        return "neutral";
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 892, column 21 - line 896, column 23): " + [ v.constructor.name ]);
};

// | Bold matte material — flat plastic finish
var boldMatte = /* #__PURE__ */ (function () {
    return {
        materialType: "standard",
        roughness: 0.8,
        metalness: 0.0,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.0,
        clearcoatRoughness: 0.0
    };
})();

// | Bold glossy material — shiny plastic accents
var boldGlossy = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.2,
        metalness: 5.0e-2,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.9,
        clearcoatRoughness: 0.1
    };
})();

// | Blue metal chrome — bright chrome accents
var blueMetalChrome = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.15,
        metalness: 0.9,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.8,
        clearcoatRoughness: 0.1
    };
})();

// | Blue metal material — satin blue finish
var blueMetal = /* #__PURE__ */ (function () {
    return {
        materialType: "physical",
        roughness: 0.35,
        metalness: 0.75,
        opacity: 1.0,
        transparent: false,
        emissive: Data_Maybe.Nothing.value,
        emissiveIntensity: 0.0,
        clearcoat: 0.5,
        clearcoatRoughness: 0.2
    };
})();

// | Get primary material for a style
var styleMaterial = function (v) {
    if (v instanceof DarkChrome) {
        return darkChrome;
    };
    if (v instanceof DarkOrange) {
        return darkChrome;
    };
    if (v instanceof BlueMetal) {
        return blueMetal;
    };
    if (v instanceof Isometric) {
        return soft;
    };
    if (v instanceof Bold) {
        return boldMatte;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 245, column 17 - line 250, column 20): " + [ v.constructor.name ]);
};

// | Set icon style (applies preset palette and materials)
var style = function (s) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            position: props.position,
            rotation: props.rotation,
            animation: props.animation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            iconStyle: new Data_Maybe.Just(s),
            brandPalette: stylePalette(s),
            material: styleMaterial(s)
        };
    };
};

// | Convert variant to material
var variantToMaterial = function (v) {
    if (v instanceof MatteVariant) {
        return matte;
    };
    if (v instanceof GlossyVariant) {
        return softPlastic;
    };
    if (v instanceof ChromeVariant) {
        return metallic;
    };
    if (v instanceof MetallicVariant) {
        return blueMetal;
    };
    if (v instanceof SoftVariant) {
        return soft;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 268, column 21 - line 273, column 22): " + [ v.constructor.name ]);
};

// | Convert icon part to HTML
var partToHtml = function (pal) {
    return function (part) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-icon3d-part")("true"), Halogen_HTML_Properties.attr("data-part-color")(resolveSlot(pal)(part.brandSlot)), Halogen_HTML_Properties.attr("data-part-slot")(brandSlotToString(part.brandSlot)), Halogen_HTML_Properties.attr("data-part-material")(materialToString(variantToMaterial(part.materialVariant))), Halogen_HTML_Properties.style("display: none") ])([ primitiveToHtml(part.primitive) ]);
    };
};

// | Convert animation to data attributes
var animationToString = function (v) {
    if (v instanceof Rotate) {
        return "rotate-y";
    };
    if (v instanceof RotateX) {
        return "rotate-x";
    };
    if (v instanceof RotateZ) {
        return "rotate-z";
    };
    if (v instanceof Bounce) {
        return "bounce";
    };
    if (v instanceof Pulse) {
        return "pulse";
    };
    if (v instanceof Float) {
        return "float";
    };
    if (v instanceof Spin) {
        return "spin";
    };
    if (v instanceof Wobble) {
        return "wobble";
    };
    if (v instanceof Flip) {
        return "flip";
    };
    if (v instanceof CustomAnimation) {
        return v.value0;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 705, column 21 - line 715, column 33): " + [ v.constructor.name ]);
};
var animationDuration = function (v) {
    if (v instanceof Rotate) {
        return 4.0;
    };
    if (v instanceof RotateX) {
        return 4.0;
    };
    if (v instanceof RotateZ) {
        return 4.0;
    };
    if (v instanceof Bounce) {
        return 1.0;
    };
    if (v instanceof Pulse) {
        return 1.5;
    };
    if (v instanceof Float) {
        return 3.0;
    };
    if (v instanceof Spin) {
        return 1.0;
    };
    if (v instanceof Wobble) {
        return 0.5;
    };
    if (v instanceof Flip) {
        return 0.6;
    };
    if (v instanceof CustomAnimation) {
        return v.value1;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 718, column 21 - line 728, column 27): " + [ v.constructor.name ]);
};

// | Create a 3D icon from multiple primitives
var icon3DWith = function (propMods) {
    return function (primitives) {
        var animationAttr = function (p) {
            if (p.animation instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-icon3d-animation")(animationToString(p.animation.value0)), Halogen_HTML_Properties.attr("data-icon3d-animation-duration")(show(animationDuration(p.animation.value0))), Halogen_HTML_Properties.style("display: none") ])([  ]) ];
            };
            if (p.animation instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 925, column 21 - line 934, column 18): " + [ p.animation.constructor.name ]);
        };
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var scale = iconSizeScale(props.size);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "inline-block", props.className ]), Halogen_HTML_Properties.attr("data-icon3d")("true"), Halogen_HTML_Properties.attr("data-icon3d-scale")(show(scale)), Halogen_HTML_Properties.attr("data-icon3d-color")(props.color), Halogen_HTML_Properties.attr("data-icon3d-material")(materialToString(props.material)), Halogen_HTML_Properties.attr("data-icon3d-position")(vector3ToString(props.position)), Halogen_HTML_Properties.attr("data-icon3d-rotation")(eulerToString(props.rotation)), Halogen_HTML_Properties.attr("data-icon3d-cast-shadow")(show1(props.castShadow)), Halogen_HTML_Properties.attr("data-icon3d-receive-shadow")(show1(props.receiveShadow)), Halogen_HTML_Properties.attr("data-icon3d-wireframe")(show1(props.wireframe)) ])(append1(map(primitiveToHtml)(primitives))(animationAttr(props)));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // icon rendering
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a 3D icon from a single primitive
var icon3D = function (propMods) {
    return function (primitive) {
        return icon3DWith(propMods)([ primitive ]);
    };
};

// | Render a multi-part icon with brand colors
var iconMulti = function (propMods) {
    return function (parts) {
        var animationAttrMulti = function (p) {
            if (p.animation instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-icon3d-animation")(animationToString(p.animation.value0)), Halogen_HTML_Properties.attr("data-icon3d-animation-duration")(show(animationDuration(p.animation.value0))), Halogen_HTML_Properties.style("display: none") ])([  ]) ];
            };
            if (p.animation instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Icon.Icon3D (line 867, column 26 - line 876, column 18): " + [ p.animation.constructor.name ]);
        };
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var scale = iconSizeScale(props.size);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "inline-block", props.className ]), Halogen_HTML_Properties.attr("data-icon3d")("true"), Halogen_HTML_Properties.attr("data-icon3d-scale")(show(scale)), Halogen_HTML_Properties.attr("data-icon3d-multicolor")("true"), Halogen_HTML_Properties.attr("data-icon3d-palette-primary")(props.brandPalette.primary), Halogen_HTML_Properties.attr("data-icon3d-palette-secondary")(props.brandPalette.secondary), Halogen_HTML_Properties.attr("data-icon3d-palette-accent")(props.brandPalette.accent), Halogen_HTML_Properties.attr("data-icon3d-palette-neutral")(props.brandPalette.neutral), Halogen_HTML_Properties.attr("data-icon3d-position")(vector3ToString(props.position)), Halogen_HTML_Properties.attr("data-icon3d-rotation")(eulerToString(props.rotation)), Halogen_HTML_Properties.attr("data-icon3d-cast-shadow")(show1(props.castShadow)), Halogen_HTML_Properties.attr("data-icon3d-receive-shadow")(show1(props.receiveShadow)) ])(append1(map(partToHtml(props.brandPalette))(parts))(animationAttrMulti(props)));
    };
};

// | Set animation
var animate = function (a) {
    return function (props) {
        return {
            size: props.size,
            color: props.color,
            material: props.material,
            position: props.position,
            rotation: props.rotation,
            castShadow: props.castShadow,
            receiveShadow: props.receiveShadow,
            wireframe: props.wireframe,
            onClick: props.onClick,
            onHover: props.onHover,
            className: props.className,
            brandPalette: props.brandPalette,
            iconStyle: props.iconStyle,
            animation: new Data_Maybe.Just(a)
        };
    };
};
export {
    defaultProps,
    size,
    color,
    material,
    position,
    rotation,
    animate,
    onClick,
    onHover,
    castShadow,
    receiveShadow,
    wireframe,
    className,
    palette,
    defaultPalette,
    Primary,
    Secondary,
    Accent,
    Neutral,
    DarkChrome,
    DarkOrange,
    BlueMetal,
    Isometric,
    Bold,
    style,
    Xs,
    Sm,
    Md,
    Lg,
    Xl,
    Xxl,
    Custom,
    iconSizeScale,
    MatteVariant,
    GlossyVariant,
    ChromeVariant,
    MetallicVariant,
    SoftVariant,
    defaultMaterial,
    metallic,
    glass,
    neon,
    matte,
    customMaterial,
    darkChrome,
    darkChromeAccent,
    blueMetal,
    blueMetalChrome,
    boldMatte,
    boldGlossy,
    soft,
    softGradient,
    softPlastic,
    softClay,
    softPastel,
    Rotate,
    RotateX,
    RotateZ,
    Bounce,
    Pulse,
    Float,
    Spin,
    Wobble,
    Flip,
    CustomAnimation,
    icon3D,
    icon3DWith,
    iconPart,
    iconMulti,
    PrimitiveBox,
    PrimitiveRoundedBox,
    PrimitiveSphere,
    PrimitiveCylinder,
    PrimitiveCapsule,
    PrimitiveCone,
    PrimitiveTorus,
    PrimitivePlane,
    PrimitiveGroup,
    primitiveBox,
    primitiveRoundedBox,
    primitiveSphere,
    primitiveCylinder,
    primitiveCapsule,
    primitiveCone,
    primitiveTorus,
    primitivePlane,
    primitiveGroup,
    zero3,
    one3,
    vec3,
    euler,
    eqBrandSlot,
    eqIconStyle,
    eqMaterialVariant,
    eqIcon3DSize,
    eqIcon3DAnimation
};
