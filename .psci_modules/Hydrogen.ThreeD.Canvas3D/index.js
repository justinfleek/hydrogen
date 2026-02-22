// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // canvas3d
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Simple 3D Canvas Component
// |
// | A simplified API for basic 3D rendering, ideal for product viewers,
// | logos, interactive demos, and simple 3D visualizations.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.ThreeD.Canvas3D as Canvas3D
// |
// | -- Simple rotating cube
// | Canvas3D.canvas3D
// |   { width: 400
// |   , height: 300
// |   }
// |   [ Canvas3D.cube
// |       { size: 1.0
// |       , color: "#3b82f6"
// |       , autoRotate: true
// |       }
// |   ]
// |
// | -- Product viewer with model
// | Canvas3D.canvas3DWithProps
// |   Canvas3D.defaultCanvasProps
// |     { background = "#f8fafc"
// |     , cameraDistance = 5.0
// |     , enableZoom = true
// |     , enablePan = false
// |     }
// |   [ Canvas3D.modelUrl "/models/product.glb"
// |   ]
// |
// | -- Interactive sphere
// | Canvas3D.canvas3D
// |   { width: 200, height: 200 }
// |   [ Canvas3D.sphere
// |       { radius: 0.8
// |       , color: "#10b981"
// |       , metalness: 0.9
// |       , roughness: 0.1
// |       , onClick: Just HandleClick
// |       }
// |   ]
// |
// | -- Multiple primitives
// | Canvas3D.canvas3D
// |   { width: 600, height: 400 }
// |   [ Canvas3D.cube { size: 0.5, color: "#ef4444", position: { x: -1.0, y: 0.0, z: 0.0 } }
// |   , Canvas3D.sphere { radius: 0.4, color: "#3b82f6", position: { x: 0.0, y: 0.0, z: 0.0 } }
// |   , Canvas3D.cone { radius: 0.3, height: 0.8, color: "#10b981", position: { x: 1.0, y: 0.0, z: 0.0 } }
// |   ]
// |
// | -- With environment lighting
// | Canvas3D.canvas3DWithProps
// |   Canvas3D.defaultCanvasProps
// |     { environment = Canvas3D.Studio
// |     , showFloor = true
// |     , floorColor = "#e5e7eb"
// |     }
// |   objects
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML from "../Halogen.HTML/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var show2 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var Studio = /* #__PURE__ */ (function () {
    function Studio() {

    };
    Studio.value = new Studio();
    return Studio;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var Sunset = /* #__PURE__ */ (function () {
    function Sunset() {

    };
    Sunset.value = new Sunset();
    return Sunset;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var Dawn = /* #__PURE__ */ (function () {
    function Dawn() {

    };
    Dawn.value = new Dawn();
    return Dawn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var Night = /* #__PURE__ */ (function () {
    function Night() {

    };
    Night.value = new Night();
    return Night;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var Forest = /* #__PURE__ */ (function () {
    function Forest() {

    };
    Forest.value = new Forest();
    return Forest;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var City = /* #__PURE__ */ (function () {
    function City() {

    };
    City.value = new City();
    return City;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var Warehouse = /* #__PURE__ */ (function () {
    function Warehouse() {

    };
    Warehouse.value = new Warehouse();
    return Warehouse;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // environment
// ═══════════════════════════════════════════════════════════════════════════════
// | Environment lighting presets
var None = /* #__PURE__ */ (function () {
    function None() {

    };
    None.value = new None();
    return None;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // internal
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert Vector3 to string
var vector3ToString = function (v) {
    return show(v.x) + ("," + (show(v.y) + ("," + show(v.z))));
};

// | Torus (donut) primitive
var torus = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("torus"), Halogen_HTML_Properties.attr("data-radius")(show(config.radius)), Halogen_HTML_Properties.attr("data-tube")(show(config.tube)), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-rotation")(vector3ToString(config.rotation)), Halogen_HTML_Properties.attr("data-metalness")(show(config.metalness)), Halogen_HTML_Properties.attr("data-roughness")(show(config.roughness)), Halogen_HTML_Properties.attr("data-auto-rotate")(show1(config.autoRotate)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};

// | Spotlight
var spotlight = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-light")("spot"), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-intensity")(show(config.intensity)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-target")(vector3ToString(config.target)), Halogen_HTML_Properties.attr("data-cast-shadow")(show1(config.castShadow)) ])([  ]);
};

// | Sphere primitive
var sphere = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("sphere"), Halogen_HTML_Properties.attr("data-radius")(show(config.radius)), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-metalness")(show(config.metalness)), Halogen_HTML_Properties.attr("data-roughness")(show(config.roughness)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};
var setAutoRotate = $foreign.setAutoRotateImpl;

// | Ring primitive
var ring = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("ring"), Halogen_HTML_Properties.attr("data-inner-radius")(show(config.innerRadius)), Halogen_HTML_Properties.attr("data-outer-radius")(show(config.outerRadius)), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-rotation")(vector3ToString(config.rotation)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};
var resetCamera = $foreign.resetCameraImpl;
var removePrimitive = $foreign.removePrimitiveImpl;

// | Handler for hover events
var onHover = function (v) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-event")("hover"), Halogen_HTML_Properties.style("display: none") ])([  ]);
};

// | Handler for drag events
var onDrag = function (v) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-event")("drag"), Halogen_HTML_Properties.style("display: none") ])([  ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // events
// ═══════════════════════════════════════════════════════════════════════════════
// | Handler for click events
var onClick = function (v) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-event")("click"), Halogen_HTML_Properties.style("display: none") ])([  ]);
};

// | Load model from URL
var modelUrl = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-model-url")(config.url), Halogen_HTML_Properties.attr("data-scale")(show(config.scale)), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-rotation")(vector3ToString(config.rotation)), Halogen_HTML_Properties.attr("data-auto-rotate")(show1(config.autoRotate)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};
var getCanvasRef = $foreign.getCanvasRefImpl;
var eqEnvironment = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Studio && y instanceof Studio) {
                return true;
            };
            if (x instanceof Sunset && y instanceof Sunset) {
                return true;
            };
            if (x instanceof Dawn && y instanceof Dawn) {
                return true;
            };
            if (x instanceof Night && y instanceof Night) {
                return true;
            };
            if (x instanceof Forest && y instanceof Forest) {
                return true;
            };
            if (x instanceof City && y instanceof City) {
                return true;
            };
            if (x instanceof Warehouse && y instanceof Warehouse) {
                return true;
            };
            if (x instanceof None && y instanceof None) {
                return true;
            };
            return false;
        };
    }
};
var environmentToString = function (v) {
    if (v instanceof Studio) {
        return "studio";
    };
    if (v instanceof Sunset) {
        return "sunset";
    };
    if (v instanceof Dawn) {
        return "dawn";
    };
    if (v instanceof Night) {
        return "night";
    };
    if (v instanceof Forest) {
        return "forest";
    };
    if (v instanceof City) {
        return "city";
    };
    if (v instanceof Warehouse) {
        return "warehouse";
    };
    if (v instanceof None) {
        return "none";
    };
    throw new Error("Failed pattern match at Hydrogen.ThreeD.Canvas3D (line 160, column 1 - line 160, column 45): " + [ v.constructor.name ]);
};

// | Default cube config
var defaultCubeConfig = /* #__PURE__ */ (function () {
    return {
        size: 1.0,
        color: "#3b82f6",
        position: {
            x: 0.0,
            y: 0.0,
            z: 0.0
        },
        rotation: {
            x: 0.0,
            y: 0.0,
            z: 0.0
        },
        metalness: 0.3,
        roughness: 0.5,
        autoRotate: false,
        autoRotateSpeed: 1.0,
        onClick: Data_Maybe.Nothing.value,
        id: ""
    };
})();

// | Default canvas properties
var defaultCanvasProps = /* #__PURE__ */ (function () {
    return {
        width: 400,
        height: 300,
        background: "#f8fafc",
        transparent: false,
        environment: Studio.value,
        cameraDistance: 4.0,
        cameraFov: 45.0,
        autoRotate: false,
        autoRotateSpeed: 1.0,
        enableZoom: true,
        enablePan: false,
        enableRotate: true,
        minDistance: 1.0,
        maxDistance: 20.0,
        showFloor: false,
        floorColor: "#e5e7eb",
        floorSize: 10.0,
        shadows: true,
        responsive: true,
        pixelRatio: Data_Maybe.Nothing.value,
        onClick: Data_Maybe.Nothing.value,
        onHover: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// | Cylinder primitive
var cylinder = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("cylinder"), Halogen_HTML_Properties.attr("data-radius")(show(config.radius)), Halogen_HTML_Properties.attr("data-height")(show(config.height)), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-rotation")(vector3ToString(config.rotation)), Halogen_HTML_Properties.attr("data-metalness")(show(config.metalness)), Halogen_HTML_Properties.attr("data-roughness")(show(config.roughness)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};

// | Cube primitive
var cube = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("cube"), Halogen_HTML_Properties.attr("data-size")(show(config.size)), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-rotation")(vector3ToString(config.rotation)), Halogen_HTML_Properties.attr("data-metalness")(show(config.metalness)), Halogen_HTML_Properties.attr("data-roughness")(show(config.roughness)), Halogen_HTML_Properties.attr("data-auto-rotate")(show1(config.autoRotate)), Halogen_HTML_Properties.attr("data-auto-rotate-speed")(show(config.autoRotateSpeed)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};

// | Cone primitive
var cone = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-primitive")("cone"), Halogen_HTML_Properties.attr("data-radius")(show(config.radius)), Halogen_HTML_Properties.attr("data-height")(show(config.height)), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-position")(vector3ToString(config.position)), Halogen_HTML_Properties.attr("data-rotation")(vector3ToString(config.rotation)), Halogen_HTML_Properties.attr("data-metalness")(show(config.metalness)), Halogen_HTML_Properties.attr("data-roughness")(show(config.roughness)), Halogen_HTML_Properties.attr("data-id")(config.id) ])([  ]);
};

// | Canvas with full props
var canvas3DWithProps = function (props) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative overflow-hidden rounded-lg", (function () {
            if (props.responsive) {
                return "w-full h-full";
            };
            return "";
        })(), props.className ]), Halogen_HTML_Properties.attr("data-canvas3d")("true"), Halogen_HTML_Properties.attr("data-canvas-width")(show2(props.width)), Halogen_HTML_Properties.attr("data-canvas-height")(show2(props.height)), Halogen_HTML_Properties.attr("data-background")(props.background), Halogen_HTML_Properties.attr("data-transparent")(show1(props.transparent)), Halogen_HTML_Properties.attr("data-environment")(environmentToString(props.environment)), Halogen_HTML_Properties.attr("data-camera-distance")(show(props.cameraDistance)), Halogen_HTML_Properties.attr("data-camera-fov")(show(props.cameraFov)), Halogen_HTML_Properties.attr("data-auto-rotate")(show1(props.autoRotate)), Halogen_HTML_Properties.attr("data-auto-rotate-speed")(show(props.autoRotateSpeed)), Halogen_HTML_Properties.attr("data-enable-zoom")(show1(props.enableZoom)), Halogen_HTML_Properties.attr("data-enable-pan")(show1(props.enablePan)), Halogen_HTML_Properties.attr("data-enable-rotate")(show1(props.enableRotate)), Halogen_HTML_Properties.attr("data-min-distance")(show(props.minDistance)), Halogen_HTML_Properties.attr("data-max-distance")(show(props.maxDistance)), Halogen_HTML_Properties.attr("data-show-floor")(show1(props.showFloor)), Halogen_HTML_Properties.attr("data-floor-color")(props.floorColor), Halogen_HTML_Properties.attr("data-floor-size")(show(props.floorSize)), Halogen_HTML_Properties.attr("data-shadows")(show1(props.shadows)), Halogen_HTML_Properties.attr("data-responsive")(show1(props.responsive)) ])([ Halogen_HTML_Elements.canvas([ Hydrogen_UI_Core.cls([ "block w-full h-full" ]), Halogen_HTML_Properties.attr("data-canvas3d-element")("true") ]), Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-canvas3d-children")("true"), Halogen_HTML_Properties.style("display: none") ])(map(Halogen_HTML.fromPlainHTML)(children)) ]);
    };
};

// | Simple 3D canvas with basic config
var canvas3D = function (config) {
    return function (children) {
        return canvas3DWithProps({
            background: defaultCanvasProps.background,
            transparent: defaultCanvasProps.transparent,
            environment: defaultCanvasProps.environment,
            cameraDistance: defaultCanvasProps.cameraDistance,
            cameraFov: defaultCanvasProps.cameraFov,
            autoRotate: defaultCanvasProps.autoRotate,
            autoRotateSpeed: defaultCanvasProps.autoRotateSpeed,
            enableZoom: defaultCanvasProps.enableZoom,
            enablePan: defaultCanvasProps.enablePan,
            enableRotate: defaultCanvasProps.enableRotate,
            minDistance: defaultCanvasProps.minDistance,
            maxDistance: defaultCanvasProps.maxDistance,
            showFloor: defaultCanvasProps.showFloor,
            floorColor: defaultCanvasProps.floorColor,
            floorSize: defaultCanvasProps.floorSize,
            shadows: defaultCanvasProps.shadows,
            responsive: defaultCanvasProps.responsive,
            pixelRatio: defaultCanvasProps.pixelRatio,
            onClick: defaultCanvasProps.onClick,
            onHover: defaultCanvasProps.onHover,
            className: defaultCanvasProps.className,
            width: config.width,
            height: config.height
        })(children);
    };
};

// | Ambient light
var ambientLight = function (config) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-light")("ambient"), Halogen_HTML_Properties.attr("data-color")(config.color), Halogen_HTML_Properties.attr("data-intensity")(show(config.intensity)) ])([  ]);
};
var addPrimitive = $foreign.addPrimitiveImpl;
export {
    canvas3D,
    canvas3DWithProps,
    defaultCanvasProps,
    Studio,
    Sunset,
    Dawn,
    Night,
    Forest,
    City,
    Warehouse,
    None,
    cube,
    sphere,
    cylinder,
    cone,
    torus,
    ring,
    modelUrl,
    ambientLight,
    spotlight,
    onClick,
    onHover,
    onDrag,
    getCanvasRef,
    addPrimitive,
    removePrimitive,
    resetCamera,
    setAutoRotate,
    eqEnvironment
};
