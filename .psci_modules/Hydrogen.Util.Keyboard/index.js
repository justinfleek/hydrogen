// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // keyboard
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Global keyboard shortcut management
// |
// | Register keyboard shortcuts with modifier keys, scopes, and sequences.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Util.Keyboard as Keyboard
// |
// | -- Simple shortcut
// | unregister <- Keyboard.registerShortcut
// |   (Keyboard.parseShortcut "Ctrl+K")
// |   (Console.log "Ctrl+K pressed!")
// |
// | -- With scope (only active in certain contexts)
// | unregister <- Keyboard.registerScopedShortcut "editor"
// |   (Keyboard.parseShortcut "Ctrl+S")
// |   saveDocument
// |
// | -- Key sequence (vim-style)
// | unregister <- Keyboard.registerSequence ["g", "i"]
// |   (Console.log "Go to inbox!")
// |
// | -- Prevent default
// | unregister <- Keyboard.registerShortcut
// |   (Keyboard.parseShortcut "Ctrl+S" # Keyboard.preventDefault)
// |   saveDocument
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var elem = /* #__PURE__ */ Data_Array.elem(Data_Eq.eqString);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordString);

// | Scope for scoped shortcuts
var Scope = function (x) {
    return x;
};

// | Keyboard modifiers
var Ctrl = /* #__PURE__ */ (function () {
    function Ctrl() {

    };
    Ctrl.value = new Ctrl();
    return Ctrl;
})();

// | Keyboard modifiers
var Alt = /* #__PURE__ */ (function () {
    function Alt() {

    };
    Alt.value = new Alt();
    return Alt;
})();

// | Keyboard modifiers
var Shift = /* #__PURE__ */ (function () {
    function Shift() {

    };
    Shift.value = new Shift();
    return Shift;
})();

// | Keyboard modifiers
var Meta = /* #__PURE__ */ (function () {
    function Meta() {

    };
    Meta.value = new Meta();
    return Meta;
})();

// | Add modifiers to a shortcut
var withModifiers = function (mods) {
    return function (s) {
        return {
            key: s.key,
            config: s.config,
            modifiers: append(s.modifiers)(mods)
        };
    };
};

// Local when helper
var when = function (v) {
    return function (v1) {
        if (v) {
            return v1;
        };
        if (!v) {
            return pure(Data_Unit.unit);
        };
        throw new Error("Failed pattern match at Hydrogen.Util.Keyboard (line 453, column 1 - line 453, column 46): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | Unregister all shortcuts
var unregisterAll = $foreign.clearShortcutRegistry;

// | Set stopPropagation
var stopPropagation = function (s) {
    return {
        key: s.key,
        modifiers: s.modifiers,
        config: {
            preventDefault: s.config.preventDefault,
            ignoreInputs: s.config.ignoreInputs,
            description: s.config.description,
            stopPropagation: true
        }
    };
};
var showScope = {
    show: function (v) {
        return "Scope(" + (v + ")");
    }
};
var showModifier = {
    show: function (v) {
        if (v instanceof Ctrl) {
            return "Ctrl";
        };
        if (v instanceof Alt) {
            return "Alt";
        };
        if (v instanceof Shift) {
            return "Shift";
        };
        if (v instanceof Meta) {
            return "Meta";
        };
        throw new Error("Failed pattern match at Hydrogen.Util.Keyboard (line 113, column 1 - line 117, column 21): " + [ v.constructor.name ]);
    }
};
var show = /* #__PURE__ */ Data_Show.show(showModifier);

// | Add Shift modifier
var shift = function (s) {
    return {
        key: s.key,
        config: s.config,
        modifiers: append(s.modifiers)([ Shift.value ])
    };
};

// | Set custom sequence timeout
var sequenceTimeout = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);

// | Set preventDefault
var preventDefault = function (s) {
    return {
        key: s.key,
        modifiers: s.modifiers,
        config: {
            stopPropagation: s.config.stopPropagation,
            ignoreInputs: s.config.ignoreInputs,
            description: s.config.description,
            preventDefault: true
        }
    };
};

// | Add Meta modifier (Cmd on Mac)
var meta = function (s) {
    return {
        key: s.key,
        config: s.config,
        modifiers: append(s.modifiers)([ Meta.value ])
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if an input element is focused
var isInputFocused = $foreign.isInputFocusedImpl;

// | Check if shortcut should be ignored
// |
// | Returns true if an input is focused and shortcut should respect that.
var shouldIgnore = function (s) {
    if (s.config.ignoreInputs) {
        return isInputFocused;
    };
    return pure(false);
};

// | Check if a scope is active
var isActiveScope = function (v) {
    var $57 = v === "global";
    if ($57) {
        return pure(true);
    };
    return function __do() {
        var ref = $foreign.activeScopesRef();
        var scopes = Effect_Ref.read(ref)();
        return elem(v)(scopes);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // scope management
// ═══════════════════════════════════════════════════════════════════════════════
// | Global scope (always active)
var globalScope = "global";

// | Format shortcut for display
var formatShortcut = function (s) {
    var modStrs = map(show)(s.modifiers);
    var parts = append(modStrs)([ s.key ]);
    return Data_String_Common.joinWith("+")(parts);
};

// | Format shortcut for current platform
// |
// | Uses Cmd symbol on Mac, Ctrl on others.
var formatForPlatform = function (s) {
    return function __do() {
        var isMac = $foreign.isMacPlatformImpl();
        var formatMod = function (v) {
            if (v instanceof Meta) {
                if (isMac) {
                    return "\u2318";
                };
                return "Ctrl";
            };
            if (v instanceof Ctrl) {
                if (isMac) {
                    return "\u2303";
                };
                return "Ctrl";
            };
            if (v instanceof Alt) {
                if (isMac) {
                    return "\u2325";
                };
                return "Alt";
            };
            if (v instanceof Shift) {
                if (isMac) {
                    return "\u21e7";
                };
                return "Shift";
            };
            throw new Error("Failed pattern match at Hydrogen.Util.Keyboard (line 426, column 17 - line 430, column 51): " + [ v.constructor.name ]);
        };
        var modStrs = map(formatMod)(s.modifiers);
        var parts = append(modStrs)([ s.key ]);
        return Data_String_Common.joinWith((function () {
            if (isMac) {
                return "";
            };
            return "+";
        })())(parts);
    };
};
var eqScope = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordScope = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqScope;
    }
};
var eqModifier = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Ctrl && y instanceof Ctrl) {
                return true;
            };
            if (x instanceof Alt && y instanceof Alt) {
                return true;
            };
            if (x instanceof Shift && y instanceof Shift) {
                return true;
            };
            if (x instanceof Meta && y instanceof Meta) {
                return true;
            };
            return false;
        };
    }
};
var elem1 = /* #__PURE__ */ Data_Array.elem(eqModifier);
var ordModifier = {
    compare: function (x) {
        return function (y) {
            if (x instanceof Ctrl && y instanceof Ctrl) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Ctrl) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Ctrl) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Alt && y instanceof Alt) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Alt) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Alt) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Shift && y instanceof Shift) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Shift) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Shift) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Meta && y instanceof Meta) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Util.Keyboard (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqModifier;
    }
};

// | Register a scoped shortcut
// |
// | Only active when the scope is active.
var registerScopedShortcut = function (v) {
    return function (s) {
        return function (callback) {
            return function __do() {
                $foreign.addToShortcutRegistry({
                    key: formatShortcut(s),
                    scope: v,
                    description: s.config.description
                })();
                return $foreign.registerShortcutImpl({
                    key: s.key,
                    ctrl: elem1(Ctrl.value)(s.modifiers),
                    alt: elem1(Alt.value)(s.modifiers),
                    shift: elem1(Shift.value)(s.modifiers),
                    meta: elem1(Meta.value)(s.modifiers),
                    preventDefault: s.config.preventDefault,
                    stopPropagation: s.config.stopPropagation,
                    ignoreInputs: s.config.ignoreInputs
                })(function __do() {
                    var active = isActiveScope(v)();
                    return when(active)(callback)();
                })();
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // registration
// ═══════════════════════════════════════════════════════════════════════════════
// | Register a global keyboard shortcut
// |
// | Returns an unregister function.
var registerShortcut = function (s) {
    return function (callback) {
        return function __do() {
            $foreign.addToShortcutRegistry({
                key: formatShortcut(s),
                scope: "global",
                description: s.config.description
            })();
            return $foreign.registerShortcutImpl({
                key: s.key,
                ctrl: elem1(Ctrl.value)(s.modifiers),
                alt: elem1(Alt.value)(s.modifiers),
                shift: elem1(Shift.value)(s.modifiers),
                meta: elem1(Meta.value)(s.modifiers),
                preventDefault: s.config.preventDefault,
                stopPropagation: s.config.stopPropagation,
                ignoreInputs: s.config.ignoreInputs
            })(callback)();
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // key sequences
// ═══════════════════════════════════════════════════════════════════════════════
// | Default sequence timeout (1000ms)
var defaultSequenceTimeout = 1000;

// | Register a scoped key sequence
var registerScopedSequence = function (scope) {
    return function (keys) {
        return function (callback) {
            return $foreign.registerSequenceImpl(keys)(defaultSequenceTimeout)(function __do() {
                var active = isActiveScope(scope)();
                return when(active)(callback)();
            });
        };
    };
};

// | Register a key sequence (vim-style)
// |
// | ```purescript
// | registerSequence ["g", "i"] (Console.log "Go to inbox")
// | ```
var registerSequence = function (keys) {
    return function (callback) {
        return $foreign.registerSequenceImpl(keys)(defaultSequenceTimeout)(callback);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // shortcut creation
// ═══════════════════════════════════════════════════════════════════════════════
// | Default shortcut config
var defaultConfig = {
    preventDefault: true,
    stopPropagation: false,
    ignoreInputs: true,
    description: ""
};

// | Parse a shortcut string
// |
// | Supports formats like:
// | - "Ctrl+K", "Cmd+Shift+P", "Alt+1"
// | - Uses "Cmd" as alias for Meta (platform-aware)
// |
// | ```purescript
// | parseShortcut "Ctrl+K"       -- Ctrl + K
// | parseShortcut "Ctrl+Shift+P" -- Ctrl + Shift + P
// | parseShortcut "Escape"       -- Escape (no modifiers)
// | ```
var parseShortcut = function (str) {
    var unsafeFromJust = function ($copy_v) {
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(v) {
            if (v instanceof Data_Maybe.Just) {
                $tco_done = true;
                return v.value0;
            };
            if (v instanceof Data_Maybe.Nothing) {
                $copy_v = Data_Maybe.Nothing.value;
                return;
            };
            throw new Error("Failed pattern match at Hydrogen.Util.Keyboard (line 241, column 3 - line 241, column 43): " + [ v.constructor.name ]);
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($copy_v);
        };
        return $tco_result;
    };
    var parseModifier = function (s) {
        var v = Data_String_Common.toLower(s);
        if (v === "ctrl") {
            return new Data_Maybe.Just(Ctrl.value);
        };
        if (v === "alt") {
            return new Data_Maybe.Just(Alt.value);
        };
        if (v === "shift") {
            return new Data_Maybe.Just(Shift.value);
        };
        if (v === "meta") {
            return new Data_Maybe.Just(Meta.value);
        };
        if (v === "cmd") {
            return new Data_Maybe.Just(Meta.value);
        };
        return Data_Maybe.Nothing.value;
    };
    var isModifier = function (s) {
        return elem(Data_String_Common.toLower(s))([ "ctrl", "alt", "shift", "meta", "cmd" ]);
    };
    var isJust = function (v) {
        if (v instanceof Data_Maybe.Just) {
            return true;
        };
        if (v instanceof Data_Maybe.Nothing) {
            return false;
        };
        throw new Error("Failed pattern match at Hydrogen.Util.Keyboard (line 237, column 3 - line 237, column 41): " + [ v.constructor.name ]);
    };
    var parseModifiers = (function () {
        var $85 = map(unsafeFromJust);
        var $86 = Data_Array.filter(isJust);
        var $87 = map(parseModifier);
        return function ($88) {
            return $85($86($87($88)));
        };
    })();
    var parts = Data_String_Common.split("+")(str);
    var mods = Data_Array.filter(isModifier)(parts);
    var keys = Data_Array.filter(function ($89) {
        return !isModifier($89);
    })(parts);
    var key = (function () {
        if (keys.length === 1) {
            return keys[0];
        };
        return "";
    })();
    return {
        key: key,
        modifiers: parseModifiers(mods),
        config: defaultConfig
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // help integration
// ═══════════════════════════════════════════════════════════════════════════════
// | Get all registered shortcuts
var getRegisteredShortcuts = /* #__PURE__ */ (function () {
    var toShortcutInfo = function (r) {
        return {
            shortcut: parseShortcut(r.key),
            scope: r.scope,
            description: r.description
        };
    };
    return function __do() {
        var registry = $foreign.getShortcutRegistry();
        return map(toShortcutInfo)(registry);
    };
})();

// | Create a shortcut from a key
var shortcut = function (key) {
    return {
        key: key,
        modifiers: [  ],
        config: defaultConfig
    };
};

// | Deactivate a scope
var deactivateScope = function (v) {
    return function __do() {
        var ref = $foreign.activeScopesRef();
        return Effect_Ref.modify_(Data_Array.filter(function (v1) {
            return v1 !== v;
        }))(ref)();
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // shortcut modifiers
// ═══════════════════════════════════════════════════════════════════════════════
// | Add Ctrl modifier
var ctrl = function (s) {
    return {
        key: s.key,
        config: s.config,
        modifiers: append(s.modifiers)([ Ctrl.value ])
    };
};

// | Create a new scope
var createScope = Scope;

// | Add Alt modifier
var alt = function (s) {
    return {
        key: s.key,
        config: s.config,
        modifiers: append(s.modifiers)([ Alt.value ])
    };
};

// | Activate a scope
var activateScope = function (v) {
    return function __do() {
        var ref = $foreign.activeScopesRef();
        return Effect_Ref.modify_(function (scopes) {
            var $84 = elem(v)(scopes);
            if ($84) {
                return scopes;
            };
            return append(scopes)([ v ]);
        })(ref)();
    };
};
export {
    Ctrl,
    Alt,
    Shift,
    Meta,
    shortcut,
    parseShortcut,
    withModifiers,
    ctrl,
    alt,
    shift,
    meta,
    preventDefault,
    stopPropagation,
    registerShortcut,
    registerScopedShortcut,
    unregisterAll,
    createScope,
    activateScope,
    deactivateScope,
    isActiveScope,
    globalScope,
    registerSequence,
    registerScopedSequence,
    sequenceTimeout,
    getRegisteredShortcuts,
    formatShortcut,
    formatForPlatform,
    isInputFocused,
    shouldIgnore,
    eqModifier,
    ordModifier,
    showModifier,
    eqScope,
    ordScope,
    showScope
};
