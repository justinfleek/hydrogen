// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // hydrogen // mesh gradient renderer
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | MeshGradientRenderer component
// |
// | Renders mesh gradients as a simple preview using CSS gradients approximation.
// | True mesh gradient rendering requires SVG or Canvas with FFI.
// |
// | This component provides a fallback visualization by sampling the mesh
// | at the 4 corners and creating a rough approximation.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.MeshGradientRenderer as MeshRenderer
// | import Hydrogen.Schema.Color.Gradient (meshGradient)
// | import Hydrogen.Schema.Color.RGB (rgb)
// |
// | MeshRenderer.meshGradientPreview
// |   [ MeshRenderer.mesh (meshGradient
// |       (rgb 255 0 0)   -- top left
// |       (rgb 0 255 0)   -- top right
// |       (rgb 0 0 255)   -- bottom left
// |       (rgb 255 255 0) -- bottom right
// |     )
// |   ]
// | ```
// |
// | For production use, implement proper mesh rendering with:
// | - SVG with gradient meshes (requires halogen-svg package)
// | - Canvas 2D with FFI for pixel manipulation
// | - WebGL for GPU-accelerated rendering
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_Schema_Color_Gradient from "../Hydrogen.Schema.Color.Gradient/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// | Set width in pixels
var width = function (w) {
    return function (props) {
        return {
            gradient: props.gradient,
            height: props.height,
            className: props.className,
            width: w
        };
    };
};

// | Render a color swatch
var renderSwatch = function (color) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.style("background-color: " + Hydrogen_Schema_Color_RGB.rgbToCss(color)), Hydrogen_UI_Core.cls([ "w-full h-full" ]) ])([  ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set mesh gradient
var mesh = function (g) {
    return function (props) {
        return {
            width: props.width,
            height: props.height,
            className: props.className,
            gradient: g
        };
    };
};

// | Set height in pixels
var height = function (h) {
    return function (props) {
        return {
            gradient: props.gradient,
            width: props.width,
            className: props.className,
            height: h
        };
    };
};

// | Default mesh preview properties
var defaultProps = {
    gradient: /* #__PURE__ */ Hydrogen_Schema_Color_Gradient.meshGradient(/* #__PURE__ */ Hydrogen_Schema_Color_RGB.rgb(255)(0)(0))(/* #__PURE__ */ Hydrogen_Schema_Color_RGB.rgb(0)(255)(0))(/* #__PURE__ */ Hydrogen_Schema_Color_RGB.rgb(0)(0)(255))(/* #__PURE__ */ Hydrogen_Schema_Color_RGB.rgb(255)(255)(0)),
    width: 400,
    height: 300,
    className: ""
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // component
// ═══════════════════════════════════════════════════════════════════════════════
// | Render a simplified mesh gradient preview
// | Shows the 4 corner colors with a note that true mesh rendering requires SVG/Canvas
var meshGradientPreview = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    
    // Sample colors at corners
var topLeft = Hydrogen_Schema_Color_Gradient.sampleMeshAt(0.0)(0.0)(props.gradient);
    var topRight = Hydrogen_Schema_Color_Gradient.sampleMeshAt(1.0)(0.0)(props.gradient);
    var center = Hydrogen_Schema_Color_Gradient.sampleMeshAt(0.5)(0.5)(props.gradient);
    var bottomRight = Hydrogen_Schema_Color_Gradient.sampleMeshAt(1.0)(1.0)(props.gradient);
    var bottomLeft = Hydrogen_Schema_Color_Gradient.sampleMeshAt(0.0)(1.0)(props.gradient);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "mesh-gradient-preview border border-white/20 rounded", props.className ]), Halogen_HTML_Properties.style("width: " + (show(props.width) + ("px; height: " + (show(props.height) + "px;")))) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "grid grid-cols-3 grid-rows-3 h-full" ]) ])([ renderSwatch(topLeft), Halogen_HTML_Elements.div([  ])([  ]), renderSwatch(topRight), Halogen_HTML_Elements.div([  ])([  ]), renderSwatch(center), Halogen_HTML_Elements.div([  ])([  ]), renderSwatch(bottomLeft), Halogen_HTML_Elements.div([  ])([  ]), renderSwatch(bottomRight) ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute inset-0 flex items-center justify-center bg-black/50 text-white text-sm p-4 text-center" ]) ])([ Halogen_HTML_Core.text("Mesh gradient preview. Full rendering requires SVG or Canvas.") ]) ]);
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            gradient: props.gradient,
            width: props.width,
            height: props.height,
            className: props.className + (" " + c)
        };
    };
};
export {
    meshGradientPreview,
    defaultProps,
    mesh,
    width,
    height,
    className
};
