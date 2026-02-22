// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // localstorage
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Type-safe localStorage utilities
// |
// | Provides type-safe access to localStorage with JSON encoding/decoding.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Util.LocalStorage as LS
// |
// | -- Store a value (any type with EncodeJson)
// | LS.setItem "user" { name: "Alice", age: 30 }
// |
// | -- Retrieve a value (any type with DecodeJson)
// | maybeUser :: Maybe User <- LS.getItem "user"
// |
// | -- Remove a value
// | LS.removeItem "user"
// |
// | -- Clear all storage
// | LS.clear
// |
// | -- Listen for changes
// | unsubscribe <- LS.onChange "user" \maybeValue ->
// |   Console.log $ "User changed: " <> show maybeValue
// |
// | -- With namespacing
// | ns <- LS.namespace "myapp"
// | ns.setItem "setting" true
// | ns.getItem "setting"  -- Stored as "myapp:setting"
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Argonaut_Core from "../Data.Argonaut.Core/index.js";
import * as Data_Argonaut_Decode_Class from "../Data.Argonaut.Decode.Class/index.js";
import * as Data_Argonaut_Decode_Parser from "../Data.Argonaut.Decode.Parser/index.js";
import * as Data_Argonaut_Encode_Class from "../Data.Argonaut.Encode.Class/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var bind1 = /* #__PURE__ */ Control_Bind.bind(Data_Maybe.bindMaybe);

// Local void helper
var $$void = function (action) {
    return function __do() {
        action();
        return Data_Unit.unit;
    };
};

// | Set a raw string in localStorage (no JSON encoding)
var setItemRaw = $foreign.setItemImpl;

// | Set an item in localStorage with JSON encoding
// |
// | ```purescript
// | setItem "settings" { theme: "dark", fontSize: 14 }
// | ```
var setItem = function (dictEncodeJson) {
    var encodeJson = Data_Argonaut_Encode_Class.encodeJson(dictEncodeJson);
    return function (key) {
        return function (value) {
            return $foreign.setItemImpl(key)(Data_Argonaut_Core.stringify(encodeJson(value)));
        };
    };
};

// | Set a prefixed item with type safety
var setItemPrefixed = function (dictEncodeJson) {
    var setItem1 = setItem(dictEncodeJson);
    return function (prefix) {
        return function (key) {
            return function (value) {
                return setItem1(prefix + (":" + key))(value);
            };
        };
    };
};

// | Remove an item from localStorage
var removeItem = $foreign.removeItemImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // change listening
// ═══════════════════════════════════════════════════════════════════════════════
// | Listen for changes to a specific key
// |
// | Fires when the key is changed from another tab/window.
// | Note: Does not fire for changes in the same tab.
// |
// | ```purescript
// | unsubscribe <- onChange "user" \maybeValue ->
// |   case maybeValue of
// |     Nothing -> Console.log "User removed"
// |     Just value -> Console.log $ "User updated: " <> value
// | ```
var onChange = $foreign.onChangeImpl;

// | Listen for any storage changes
// |
// | Callback receives the key and new value.
var onAnyChange = $foreign.onAnyChangeImpl;

// | Get the number of items in localStorage
var length = $foreign.lengthImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Get all keys in localStorage
var keys = $foreign.keysImpl;

// | Check if a key exists in localStorage
var has = function (key) {
    return map(Data_Maybe.isJust)($foreign.getItemImpl(key));
};

// | Get all keys with a given prefix
var getNamespaceKeys = function (prefix) {
    var startsWith = function (p) {
        return function (str) {
            return $foreign.take($foreign.strLength(p))(str) === p;
        };
    };
    return function __do() {
        var allKeys = $foreign.keysImpl();
        return $foreign.filterImpl(startsWith(prefix + ":"))(allKeys);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // string operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Get a raw string from localStorage (no JSON decoding)
var getItemRaw = $foreign.getItemImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // core operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Get an item from localStorage with JSON decoding
// |
// | Returns `Nothing` if the key doesn't exist or decoding fails.
// |
// | ```purescript
// | maybeUser :: Maybe User <- getItem "user"
// | ```
var getItem = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    return function (key) {
        return function __do() {
            var maybeStr = $foreign.getItemImpl(key)();
            if (maybeStr instanceof Data_Maybe.Nothing) {
                return Data_Maybe.Nothing.value;
            };
            if (maybeStr instanceof Data_Maybe.Just) {
                return bind1(Data_Either.hush(Data_Argonaut_Decode_Parser.parseJson(maybeStr.value0)))(function ($17) {
                    return Data_Either.hush(decodeJson($17));
                });
            };
            throw new Error("Failed pattern match at Hydrogen.Util.LocalStorage (line 119, column 10 - line 121, column 61): " + [ maybeStr.constructor.name ]);
        };
    };
};

// | Get a prefixed item with type safety
var getItemPrefixed = function (dictDecodeJson) {
    var getItem1 = getItem(dictDecodeJson);
    return function (prefix) {
        return function (key) {
            return getItem1(prefix + (":" + key));
        };
    };
};

// | Clear all keys with a given prefix
var clearNamespace = function (prefix) {
    var traverse_ = function (f) {
        return function (arr) {
            return $$void($foreign.traverseImpl(f)(arr));
        };
    };
    var startsWith = function (p) {
        return function (str) {
            return $foreign.take($foreign.strLength(p))(str) === p;
        };
    };
    var filterPrefix = function (p) {
        return function (arr) {
            return $foreign.filterImpl(startsWith(p))(arr);
        };
    };
    return function __do() {
        var allKeys = $foreign.keysImpl();
        var prefixedKeys = filterPrefix(prefix + ":")(allKeys);
        return traverse_(removeItem)(prefixedKeys)();
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // namespacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a namespaced storage interface
// |
// | All keys are prefixed with the namespace.
// |
// | ```purescript
// | ns <- namespace "myapp"
// | ns.setItemRaw "theme" "dark"  -- Stored as "myapp:theme"
// | maybeTheme <- ns.getItemRaw "theme"
// | ns.clear  -- Only clears "myapp:*" keys
// |
// | -- For typed access, use the prefix:
// | setItem (ns.prefix <> ":setting") myValue
// | ```
var namespace = function (prefix) {
    return pure({
        getItemRaw: function (key) {
            return getItemRaw(prefix + (":" + key));
        },
        setItemRaw: function (key) {
            return function (value) {
                return setItemRaw(prefix + (":" + key))(value);
            };
        },
        removeItem: function (key) {
            return removeItem(prefix + (":" + key));
        },
        clear: clearNamespace(prefix),
        keys: getNamespaceKeys(prefix),
        prefix: prefix
    });
};

// | Clear all items from localStorage
var clear = $foreign.clearImpl;
export {
    getItem,
    setItem,
    removeItem,
    clear,
    getItemRaw,
    setItemRaw,
    onChange,
    onAnyChange,
    namespace,
    getItemPrefixed,
    setItemPrefixed,
    keys,
    length,
    has
};
