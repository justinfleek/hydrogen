// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // locale
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Internationalization (i18n) support
// |
// | Type-safe translations with pluralization, interpolation, and locale management.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.I18n.Locale as I18n
// |
// | -- Create i18n instance
// | i18n <- I18n.create
// |   { defaultLocale: "en"
// |   , fallbackLocale: "en"
// |   , translations: 
// |       { en: { greeting: "Hello", items: { one: "1 item", other: "{count} items" } }
// |       , es: { greeting: "Hola", items: { one: "1 artículo", other: "{count} artículos" } }
// |       }
// |   }
// |
// | -- Translate
// | greeting <- I18n.t i18n "greeting"  -- "Hello"
// |
// | -- With interpolation
// | message <- I18n.t' i18n "welcome" { name: "Alice" }  -- "Welcome, Alice!"
// |
// | -- Pluralization
// | items <- I18n.plural i18n "items" 5  -- "5 items"
// |
// | -- Change locale
// | I18n.setLocale i18n "es"
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Map from "../Data.Map/index.js";
import * as Data_Map_Internal from "../Data.Map.Internal/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Set from "../Data.Set/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Foreign_Object from "../Foreign.Object/index.js";
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);
var foldM = /* #__PURE__ */ Data_Array.foldM(Effect.monadEffect);
var bind1 = /* #__PURE__ */ Control_Bind.bind(Data_Maybe.bindMaybe);
var lookup = /* #__PURE__ */ Data_Map_Internal.lookup(Data_Ord.ordString);
var elem = /* #__PURE__ */ Data_Array.elem(Data_Eq.eqString);
var foldMap = /* #__PURE__ */ Foreign_Object.foldMap(/* #__PURE__ */ Data_Monoid.monoidFn(Data_Monoid.monoidString));
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var fromFoldable = /* #__PURE__ */ Data_Array.fromFoldable(Data_Set.foldableSet);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | I18n instance
var I18n = function (x) {
    return x;
};

// | Set current locale
var setLocale = function (v) {
    return function (newLocale) {
        var for_ = function (arr) {
            return function (f) {
                return $$void(foldM(function (v1) {
                    return function (x) {
                        return f(x);
                    };
                })(Data_Unit.unit)(arr));
            };
        };
        return function __do() {
            Effect_Ref.write(newLocale)(v.locale)();
            var subs = Effect_Ref.read(v.listeners)();
            return for_(subs)(function (listener) {
                return listener.callback(newLocale);
            })();
        };
    };
};

// | Determine plural form (simplified English rules)
var pluralForm = function (n) {
    if (n === 0) {
        return "zero";
    };
    if (n === 1) {
        return "one";
    };
    if (n === 2) {
        return "two";
    };
    if (n < 5) {
        return "few";
    };
    if (Data_Boolean.otherwise) {
        return "other";
    };
    throw new Error("Failed pattern match at Hydrogen.I18n.Locale (line 194, column 1 - line 194, column 28): " + [ n.constructor.name ]);
};

// | Subscribe to locale changes
var onLocaleChange = function (v) {
    return function (callback) {
        return function __do() {
            var subs = Effect_Ref.read(v.listeners)();
            var nextId = (function () {
                var v1 = Data_Array.last(subs);
                if (v1 instanceof Data_Maybe.Nothing) {
                    return 0;
                };
                if (v1 instanceof Data_Maybe.Just) {
                    return v1.value0.id + 1 | 0;
                };
                throw new Error("Failed pattern match at Hydrogen.I18n.Locale (line 241, column 16 - line 243, column 27): " + [ v1.constructor.name ]);
            })();
            var sub = {
                id: nextId,
                callback: callback
            };
            Effect_Ref.modify_(Data_Function.flip(Data_Array.snoc)(sub))(v.listeners)();
            return Effect_Ref.modify_(Data_Array.filter(function (s) {
                return s.id !== nextId;
            }))(v.listeners);
        };
    };
};

// | Lookup translation in nested structure
var lookupTranslation = function (translations) {
    return function (loc) {
        return function (key) {
            return bind1(lookup(loc)(translations))(function (localeMap) {
                return lookup(key)(localeMap);
            });
        };
    };
};

// | Try to translate, returning Maybe
var tMaybe = function (v) {
    return function (key) {
        return function __do() {
            var currentLocale = Effect_Ref.read(v.locale)();
            var trans = Effect_Ref.read(v.translations)();
            var result = lookupTranslation(trans)(currentLocale)(key);
            if (result instanceof Data_Maybe.Just) {
                return result;
            };
            if (result instanceof Data_Maybe.Nothing) {
                return lookupTranslation(trans)(v.config.fallbackLocale)(key);
            };
            throw new Error("Failed pattern match at Hydrogen.I18n.Locale (line 172, column 3 - line 174, column 72): " + [ result.constructor.name ]);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // translation
// ═══════════════════════════════════════════════════════════════════════════════
// | Translate a key
var t = function (i18n) {
    return function (key) {
        return function __do() {
            var result = tMaybe(i18n)(key)();
            return Data_Maybe.fromMaybe(key)(result);
        };
    };
};

// | RTL locale check
var isRTLLocale = function (locale) {
    var lang = Data_String_CodePoints.take(2)(locale);
    return elem(lang)([ "ar", "he", "fa", "ur" ]);
};

// | Interpolate values into a string
var interpolate = function (prefix) {
    return function (suffix) {
        return function (template) {
            return function (values) {
                var replaceOne = function (pattern) {
                    return function (replacement) {
                        return function (str) {
                            return Data_String_Common.replaceAll(pattern)(replacement)(str);
                        };
                    };
                };
                return foldMap(function (k) {
                    return function (v) {
                        return replaceOne(prefix + (k + suffix))(v);
                    };
                })(values)(template);
            };
        };
    };
};

// | Translate with interpolation values
var t$prime = function (v) {
    return function (key) {
        return function (values) {
            return function __do() {
                var translation = t(v)(key)();
                return interpolate(v.config.interpolationPrefix)(v.config.interpolationSuffix)(translation)(values);
            };
        };
    };
};

// | Pluralize with additional interpolation
var pluralWith = function (i18n) {
    return function (baseKey) {
        return function (count) {
            return function (values) {
                var pluralKey = baseKey + ("." + pluralForm(count));
                var valuesWithCount = Foreign_Object.insert("count")(show(count))(values);
                return t$prime(i18n)(pluralKey)(valuesWithCount);
            };
        };
    };
};

// | Pluralize a translation
var plural = function (i18n) {
    return function (key) {
        return function (count) {
            return pluralWith(i18n)(key)(count)(Foreign_Object.empty);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if a translation exists
var hasTranslation = function (i18n) {
    return function (key) {
        return function __do() {
            var result = tMaybe(i18n)(key)();
            if (result instanceof Data_Maybe.Just) {
                return true;
            };
            if (result instanceof Data_Maybe.Nothing) {
                return false;
            };
            throw new Error("Failed pattern match at Hydrogen.I18n.Locale (line 290, column 10 - line 292, column 21): " + [ result.constructor.name ]);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // locale management
// ═══════════════════════════════════════════════════════════════════════════════
// | Get current locale
var getLocale = function (v) {
    return Effect_Ref.read(v.locale);
};

// | Check if current locale is RTL
var isRTL = function (i18n) {
    return function __do() {
        var locale = getLocale(i18n)();
        return isRTLLocale(locale);
    };
};

// | Get text direction for current locale
var getDirection = function (i18n) {
    return function __do() {
        var locale = getLocale(i18n)();
        var $51 = isRTLLocale(locale);
        if ($51) {
            return "rtl";
        };
        return "ltr";
    };
};

// | Get all available locales
var getAvailableLocales = function (v) {
    return function __do() {
        var trans = Effect_Ref.read(v.translations)();
        return fromFoldable(Data_Map.keys(trans));
    };
};

// | Format relative time (e.g., "3 days ago")
var formatRelativeTime = function (i18n) {
    return function (value) {
        return function (unit) {
            return function __do() {
                var locale = getLocale(i18n)();
                return $foreign.formatRelativeTimeImpl(locale)(value)(unit);
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // formatting
// ═══════════════════════════════════════════════════════════════════════════════
// | Format a number according to locale
var formatNumber = function (i18n) {
    return function (n) {
        return function __do() {
            var locale = getLocale(i18n)();
            return $foreign.formatNumberImpl(locale)(n);
        };
    };
};

// | Format a date
var formatDate = function (i18n) {
    return function (dateStr) {
        return function (format) {
            return function __do() {
                var locale = getLocale(i18n)();
                return $foreign.formatDateImpl(locale)(dateStr)(format);
            };
        };
    };
};

// | Format currency
var formatCurrency = function (i18n) {
    return function (amount) {
        return function (currency) {
            return function __do() {
                var locale = getLocale(i18n)();
                return $foreign.formatCurrencyImpl(locale)(amount)(currency);
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // initialization
// ═══════════════════════════════════════════════════════════════════════════════
// | Default configuration
var defaultConfig = {
    defaultLocale: "en",
    fallbackLocale: "en",
    interpolationPrefix: "{",
    interpolationSuffix: "}"
};

// | Create an I18n instance with inline translations
var create = function (config) {
    return function (translations) {
        return function __do() {
            var localeRef = Effect_Ref["new"](config.defaultLocale)();
            var translationsRef = Effect_Ref["new"](translations)();
            var listenersRef = Effect_Ref["new"]([  ])();
            return {
                locale: localeRef,
                config: config,
                translations: translationsRef,
                listeners: listenersRef
            };
        };
    };
};

// | Create with async translation loader
var createWithLoader = function (config) {
    return function (_loader) {
        return create(config)(Data_Map_Internal.empty);
    };
};
export {
    create,
    createWithLoader,
    t,
    t$prime,
    tMaybe,
    plural,
    pluralWith,
    getLocale,
    setLocale,
    getAvailableLocales,
    onLocaleChange,
    formatNumber,
    formatCurrency,
    formatDate,
    formatRelativeTime,
    hasTranslation,
    getDirection,
    isRTL
};
