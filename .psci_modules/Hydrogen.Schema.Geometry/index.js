// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                            // hydrogen // schema // geometry
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Geometry pillar - shapes, paths, and spatial primitives.
// |
// | Covers:
// | - **Radius**: Border radius and corner definitions
// | - **Shape**: Primitive shapes (rectangle, circle, polygon)
// | - **Path**: Bezier paths and curves
// | - **Transform**: 2D/3D transforms (translate, rotate, scale, skew)
// |
// | ## Usage
// |
// | Always use qualified imports to avoid naming conflicts:
// |
// | ```purescript
// | import Hydrogen.Schema.Geometry as Geometry
// |
// | cardRadius :: Geometry.Corners
// | cardRadius = Geometry.cornersAll Geometry.md
// | ```
// |
// | Re-exports all Geometry submodules.
import * as Hydrogen_Schema_Geometry_Radius from "../Hydrogen.Schema.Geometry.Radius/index.js";

export {
    RadiusFull,
    RadiusNone,
    RadiusPercent,
    RadiusPx,
    RadiusRem,
    corners,
    cornersAll,
    cornersBottom,
    cornersBottomLeft,
    cornersBottomRight,
    cornersLeft,
    cornersRight,
    cornersToCss,
    cornersTop,
    cornersTopLeft,
    cornersTopRight,
    double,
    full,
    half,
    lg,
    md,
    none,
    percent,
    px,
    rem,
    scale,
    sm,
    toCss,
    xl,
    xl2,
    xs
} from "../Hydrogen.Schema.Geometry.Radius/index.js";
