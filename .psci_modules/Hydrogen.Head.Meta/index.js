// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // meta
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Dynamic document head management
// |
// | Manage title, meta tags, links, and structured data.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Head.Meta as Meta
// |
// | -- Set page title
// | Meta.setTitle "My Page - My App"
// |
// | -- Update meta tags
// | Meta.setMeta "description" "Page description here"
// | Meta.setMeta "og:title" "Share Title"
// |
// | -- Add structured data (JSON-LD)
// | Meta.setJsonLd
// |   { "@context": "https://schema.org"
// |   , "@type": "Article"
// |   , "headline": "Article Title"
// |   }
// |
// | -- Preload resources
// | Meta.preload "/api/data" "fetch"
// | Meta.prefetch "/next-page"
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Argonaut_Core from "../Data.Argonaut.Core/index.js";
import * as Data_Argonaut_Encode_Class from "../Data.Argonaut.Encode.Class/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Unit from "../Data.Unit/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // title
// ═══════════════════════════════════════════════════════════════════════════════
// | Set document title
var setTitle = $foreign.setTitleImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // meta tags
// ═══════════════════════════════════════════════════════════════════════════════
// | Set a meta tag (creates or updates)
var setMeta = $foreign.setMetaImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // open graph
// ═══════════════════════════════════════════════════════════════════════════════
// | Set Open Graph tags
var setOgTags = function (tags) {
    return function __do() {
        setMeta("og:title")(tags.title)();
        setMeta("og:description")(tags.description)();
        (function () {
            if (tags.image instanceof Data_Maybe.Just) {
                return setMeta("og:image")(tags.image.value0)();
            };
            if (tags.image instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 144, column 3 - line 146, column 25): " + [ tags.image.constructor.name ]);
        })();
        (function () {
            if (tags.url instanceof Data_Maybe.Just) {
                return setMeta("og:url")(tags.url.value0)();
            };
            if (tags.url instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 147, column 3 - line 149, column 25): " + [ tags.url.constructor.name ]);
        })();
        (function () {
            if (tags.type_ instanceof Data_Maybe.Just) {
                return setMeta("og:type")(tags.type_.value0)();
            };
            if (tags.type_ instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 150, column 3 - line 152, column 25): " + [ tags.type_.constructor.name ]);
        })();
        if (tags.siteName instanceof Data_Maybe.Just) {
            return setMeta("og:site_name")(tags.siteName.value0)();
        };
        if (tags.siteName instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 153, column 3 - line 155, column 25): " + [ tags.siteName.constructor.name ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // twitter cards
// ═══════════════════════════════════════════════════════════════════════════════
// | Set Twitter Card tags
var setTwitterCard = function (card) {
    return function __do() {
        setMeta("twitter:card")(card.card)();
        setMeta("twitter:title")(card.title)();
        setMeta("twitter:description")(card.description)();
        (function () {
            if (card.image instanceof Data_Maybe.Just) {
                return setMeta("twitter:image")(card.image.value0)();
            };
            if (card.image instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 167, column 3 - line 169, column 25): " + [ card.image.constructor.name ]);
        })();
        (function () {
            if (card.site instanceof Data_Maybe.Just) {
                return setMeta("twitter:site")(card.site.value0)();
            };
            if (card.site instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 170, column 3 - line 172, column 25): " + [ card.site.constructor.name ]);
        })();
        if (card.creator instanceof Data_Maybe.Just) {
            return setMeta("twitter:creator")(card.creator.value0)();
        };
        if (card.creator instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Head.Meta (line 173, column 3 - line 175, column 25): " + [ card.creator.constructor.name ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // structured data
// ═══════════════════════════════════════════════════════════════════════════════
// | Set JSON-LD structured data
var setJsonLd = function (dictEncodeJson) {
    var encodeJson = Data_Argonaut_Encode_Class.encodeJson(dictEncodeJson);
    return function (data$prime) {
        return $foreign.setJsonLdImpl(Data_Argonaut_Core.stringify(encodeJson(data$prime)));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // favicon
// ═══════════════════════════════════════════════════════════════════════════════
// | Set favicon
var setFavicon = $foreign.setFaviconImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // links
// ═══════════════════════════════════════════════════════════════════════════════
// | Set canonical URL
var setCanonical = function (url) {
    return $foreign.addLinkImpl("canonical")(url)("");
};

// | Remove a meta tag
var removeMeta = $foreign.removeMetaImpl;

// | Remove a link tag by rel
var removeLink = $foreign.removeLinkImpl;

// | Remove JSON-LD structured data
var removeJsonLd = $foreign.removeJsonLdImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // resource hints
// ═══════════════════════════════════════════════════════════════════════════════
// | Preload a resource
// | as: "script", "style", "image", "font", "fetch"
var preload = function (href) {
    return function (as_) {
        return $foreign.addLinkImpl("preload")(href)(as_);
    };
};

// | Prefetch a resource for future navigation
var prefetch = function (href) {
    return $foreign.addLinkImpl("prefetch")(href)("");
};

// | Preconnect to an origin
var preconnect = function (origin) {
    return $foreign.addLinkImpl("preconnect")(origin)("");
};

// | Get current document title
var getTitle = $foreign.getTitleImpl;

// | Get meta tag value
var getMeta = $foreign.getMetaImpl;

// | DNS prefetch for an origin
var dnsPrefetch = function (origin) {
    return $foreign.addLinkImpl("dns-prefetch")(origin)("");
};

// | Add a link tag
var addLink = function (rel) {
    return function (href) {
        return $foreign.addLinkImpl(rel)(href)("");
    };
};
export {
    setTitle,
    getTitle,
    setMeta,
    removeMeta,
    getMeta,
    setOgTags,
    setTwitterCard,
    setJsonLd,
    removeJsonLd,
    preload,
    prefetch,
    preconnect,
    dnsPrefetch,
    setCanonical,
    addLink,
    removeLink,
    setFavicon
};
