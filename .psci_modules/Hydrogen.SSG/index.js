// | Static Site Generation utilities
// |
// | This module provides utilities for building static sites with Halogen:
// | - HTML document generation
// | - Meta tag helpers (SEO, OpenGraph, Twitter)
// | - Page shell generation
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.SSG as SSG
// | import Halogen.HTML.Renderer as Renderer
// |
// | myPage :: PageMeta
// | myPage =
// |   { title: "My Page"
// |   , description: "A great page"
// |   , path: "/my-page"
// |   , ogImage: Nothing
// |   }
// |
// | html :: String
// | html = SSG.renderPage defaultDocConfig myPage pageContent
// | ```
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_HTML_Renderer from "../Hydrogen.HTML.Renderer/index.js";
import * as Hydrogen_Router from "../Hydrogen.Router/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var twitterMeta = function (name) {
    return function (contentVal) {
        return Halogen_HTML_Elements.meta([ Halogen_HTML_Properties.attr("name")(name), Halogen_HTML_Properties.attr("content")(contentVal) ]);
    };
};

// | Generate Twitter Card meta tags
var twitterTags = function (meta) {
    var image = (function () {
        if (meta.ogImage instanceof Data_Maybe.Just) {
            return [ twitterMeta("twitter:image")(meta.ogImage.value0) ];
        };
        if (meta.ogImage instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.SSG (line 174, column 11 - line 176, column 18): " + [ meta.ogImage.constructor.name ]);
    })();
    return append([ twitterMeta("twitter:card")("summary_large_image"), twitterMeta("twitter:title")(meta.title), twitterMeta("twitter:description")(meta.description) ])(image);
};
var themeColorMeta = function (config) {
    if (config.themeColor instanceof Data_Maybe.Just) {
        return [ Halogen_HTML_Elements.meta([ Halogen_HTML_Properties.attr("name")("theme-color"), Halogen_HTML_Properties.attr("content")(config.themeColor.value0) ]) ];
    };
    if (config.themeColor instanceof Data_Maybe.Nothing) {
        return [  ];
    };
    throw new Error("Failed pattern match at Hydrogen.SSG (line 215, column 25 - line 222, column 16): " + [ config.themeColor.constructor.name ]);
};
var stylesheetLinks = function (config) {
    return map(function (href) {
        return Halogen_HTML_Elements.link([ Halogen_HTML_Properties.rel("stylesheet"), Halogen_HTML_Properties.href(href) ]);
    })(config.stylesheets);
};
var scriptTags = function (config) {
    return map(function (src) {
        return Halogen_HTML_Elements.script([ Halogen_HTML_Properties.src(src) ])([  ]);
    })(config.scripts);
};

// ============================================================
// ROUTE INTEGRATION
// ============================================================
// | Generate PageMeta from a route using the RouteMetadata typeclass
// |
// | This is the key to the "write once, SSG or dynamic" pattern:
// | define your route metadata once in the typeclass, then use it
// | for both static generation and runtime rendering.
// |
// | ```purescript
// | import Hydrogen.SSG as SSG
// | import MyApp.Router (Route(..), homeRoute)
// |
// | -- Generate static page
// | homeMeta :: PageMeta
// | homeMeta = pageMetaFromRoute homeRoute
// |
// | html :: String
// | html = SSG.renderPage docConfig homeMeta content
// | ```
var pageMetaFromRoute = function (dictIsRoute) {
    var routeToPath = Hydrogen_Router.routeToPath(dictIsRoute);
    return function (dictRouteMetadata) {
        var routeTitle = Hydrogen_Router.routeTitle(dictRouteMetadata);
        var routeDescription = Hydrogen_Router.routeDescription(dictRouteMetadata);
        var routeOgImage = Hydrogen_Router.routeOgImage(dictRouteMetadata);
        return function (route) {
            return {
                title: routeTitle(route),
                description: routeDescription(route),
                path: routeToPath(route),
                ogImage: routeOgImage(route),
                canonicalUrl: Data_Maybe.Nothing.value
            };
        };
    };
};

// ============================================================
// HELPERS
// ============================================================
var ogMeta = function (property) {
    return function (contentVal) {
        return Halogen_HTML_Elements.meta([ Halogen_HTML_Properties.attr("property")(property), Halogen_HTML_Properties.attr("content")(contentVal) ]);
    };
};

// | Generate OpenGraph meta tags
var ogTags = function (config) {
    return function (meta) {
        var siteName = (function () {
            if (config.siteName === "") {
                return [  ];
            };
            return [ ogMeta("og:site_name")(config.siteName) ];
        })();
        var image = (function () {
            if (meta.ogImage instanceof Data_Maybe.Just) {
                return [ ogMeta("og:image")(meta.ogImage.value0) ];
            };
            if (meta.ogImage instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.SSG (line 161, column 11 - line 163, column 18): " + [ meta.ogImage.constructor.name ]);
        })();
        return append([ ogMeta("og:type")("website"), ogMeta("og:title")(meta.title), ogMeta("og:description")(meta.description), ogMeta("og:url")(meta.path) ])(append(siteName)(image));
    };
};

// ============================================================
// META TAGS
// ============================================================
// | Generate standard meta tags
var metaTags = function (_config) {
    return function (meta) {
        if (meta.canonicalUrl instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Elements.link([ Halogen_HTML_Properties.rel("canonical"), Halogen_HTML_Properties.href(meta.canonicalUrl.value0) ]) ];
        };
        if (meta.canonicalUrl instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.SSG (line 143, column 3 - line 145, column 18): " + [ meta.canonicalUrl.constructor.name ]);
    };
};
var manifestLink = function (config) {
    if (config.manifest instanceof Data_Maybe.Just) {
        return [ Halogen_HTML_Elements.link([ Halogen_HTML_Properties.rel("manifest"), Halogen_HTML_Properties.href(config.manifest.value0) ]) ];
    };
    if (config.manifest instanceof Data_Maybe.Nothing) {
        return [  ];
    };
    throw new Error("Failed pattern match at Hydrogen.SSG (line 210, column 23 - line 212, column 16): " + [ config.manifest.constructor.name ]);
};
var faviconLink = function (config) {
    if (config.favicon instanceof Data_Maybe.Just) {
        return [ Halogen_HTML_Elements.link([ Halogen_HTML_Properties.rel("icon"), Halogen_HTML_Properties.href(config.favicon.value0) ]) ];
    };
    if (config.favicon instanceof Data_Maybe.Nothing) {
        return [  ];
    };
    throw new Error("Failed pattern match at Hydrogen.SSG (line 205, column 22 - line 207, column 16): " + [ config.favicon.constructor.name ]);
};

// | Render the HTML document (without DOCTYPE)
var renderDocument = function (config) {
    return function (meta) {
        return function (content) {
            return Hydrogen_HTML_Renderer.render(Halogen_HTML_Elements.html([ Halogen_HTML_Properties.attr("lang")(config.lang) ])([ Halogen_HTML_Elements.head_(append([ Halogen_HTML_Elements.meta([ Halogen_HTML_Properties.attr("charset")(config.charset) ]), Halogen_HTML_Elements.meta([ Halogen_HTML_Properties.attr("name")("viewport"), Halogen_HTML_Properties.attr("content")(config.viewport) ]), Halogen_HTML_Elements.title_([ Halogen_HTML_Core.text(meta.title) ]), Halogen_HTML_Elements.meta([ Halogen_HTML_Properties.attr("name")("description"), Halogen_HTML_Properties.attr("content")(meta.description) ]) ])(append(metaTags(config)(meta))(append(ogTags(config)(meta))(append(twitterTags(meta))(append(stylesheetLinks(config))(append(faviconLink(config))(append(manifestLink(config))(themeColorMeta(config))))))))), Halogen_HTML_Elements.body_(append([ content ])(scriptTags(config))) ]));
        };
    };
};

// ============================================================
// RENDERING
// ============================================================
// | Render a complete HTML page
// |
// | Combines document config, page meta, and body content into
// | a complete HTML document string.
var renderPage = function (config) {
    return function (meta) {
        return function (content) {
            return "<!DOCTYPE html>" + renderDocument(config)(meta)(content);
        };
    };
};

// | Render a route to a complete HTML page
// |
// | Combines pageMetaFromRoute with renderPage for a one-liner:
// |
// | ```purescript
// | html :: String
// | html = renderRouteStatic docConfig homeRoute homeContent
// | ```
var renderRouteStatic = function (dictIsRoute) {
    var pageMetaFromRoute1 = pageMetaFromRoute(dictIsRoute);
    return function (dictRouteMetadata) {
        var pageMetaFromRoute2 = pageMetaFromRoute1(dictRouteMetadata);
        return function (config) {
            return function (route) {
                return function (content) {
                    return renderPage(config)(pageMetaFromRoute2(route))(content);
                };
            };
        };
    };
};

// | Default document configuration
var defaultDocConfig = /* #__PURE__ */ (function () {
    return {
        lang: "en",
        charset: "utf-8",
        viewport: "width=device-width, initial-scale=1",
        siteName: "",
        themeColor: Data_Maybe.Nothing.value,
        favicon: Data_Maybe.Nothing.value,
        manifest: Data_Maybe.Nothing.value,
        stylesheets: [  ],
        scripts: [  ]
    };
})();
export {
    defaultDocConfig,
    renderPage,
    renderDocument,
    pageMetaFromRoute,
    renderRouteStatic,
    metaTags,
    ogTags,
    twitterTags
};
