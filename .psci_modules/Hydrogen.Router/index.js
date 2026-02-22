// | Client-side routing infrastructure
// |
// | This module provides a typeclass-based routing system that allows
// | applications to define their own route ADTs while using shared
// | routing infrastructure.
// |
// | ## Usage
// |
// | 1. Define your route type:
// | ```purescript
// | data Route = Home | About | Dashboard | NotFound
// | ```
// |
// | 2. Implement the Route class:
// | ```purescript
// | instance routeMyRoute :: Route Route where
// |   parseRoute "/" = Home
// |   parseRoute "/about" = About
// |   parseRoute "/dashboard" = Dashboard
// |   parseRoute _ = NotFound
// |   
// |   routeToPath Home = "/"
// |   routeToPath About = "/about"
// |   routeToPath Dashboard = "/dashboard"
// |   routeToPath NotFound = "/"
// | ```
// |
// | 3. Use the routing helpers:
// | ```purescript
// | handleAction Initialize = do
// |   path <- liftEffect getPathname
// |   let route = parseRoute path
// |   ...
// | ```
import * as $foreign from "./foreign.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";

// | Convert a route back to a URL path
var routeToPath = function (dict) {
    return dict.routeToPath;
};

// | Page title for the route (used in <title> and og:title)
var routeTitle = function (dict) {
    return dict.routeTitle;
};

// | Optional OpenGraph image URL for the route
var routeOgImage = function (dict) {
    return dict.routeOgImage;
};

// | Meta description for the route (used in description and og:description)
var routeDescription = function (dict) {
    return dict.routeDescription;
};

// | Parse a URL path into a route
var parseRoute = function (dict) {
    return dict.parseRoute;
};

// ============================================================
// UTILITIES
// ============================================================
// | Normalize paths by removing trailing slashes (except for root)
// |
// | ```purescript
// | normalizeTrailingSlash "/" == "/"
// | normalizeTrailingSlash "/about/" == "/about"
// | normalizeTrailingSlash "/about" == "/about"
// | ```
var normalizeTrailingSlash = function (v) {
    if (v === "/") {
        return "/";
    };
    var $10 = Data_String_CodeUnits.takeRight(1)(v) === "/";
    if ($10) {
        return Data_String_CodeUnits.dropRight(1)(v);
    };
    return v;
};

// | Navigate to a route programmatically
// |
// | This pushes the new path to browser history and can trigger
// | your app's routing logic.
var navigate = function (dictIsRoute) {
    var routeToPath1 = routeToPath(dictIsRoute);
    return function (route) {
        return $foreign.pushState(routeToPath1(route));
    };
};

// | Whether the route should be statically generated (SSG)
// | Returns true for public pages, false for SPA-only routes
var isStaticRoute = function (dict) {
    return dict.isStaticRoute;
};

// | Whether the route requires authentication
var isProtected = function (dict) {
    return dict.isProtected;
};
export {
    getPathname,
    getHostname,
    getOrigin,
    pushState,
    replaceState,
    onPopState,
    interceptLinks
} from "./foreign.js";
export {
    parseRoute,
    routeToPath,
    isProtected,
    isStaticRoute,
    routeTitle,
    routeDescription,
    routeOgImage,
    navigate,
    normalizeTrailingSlash
};
