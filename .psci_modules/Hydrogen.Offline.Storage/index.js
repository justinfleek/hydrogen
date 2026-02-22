// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // storage
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Offline storage with IndexedDB
// |
// | Type-safe wrapper around IndexedDB for offline-first applications.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Offline.Storage as Storage
// |
// | -- Open a database
// | db <- Storage.open "myapp" 1
// |   [ Storage.store "users" { keyPath: "id" }
// |   , Storage.store "posts" { keyPath: "id", autoIncrement: true }
// |   ]
// |
// | -- Store data
// | Storage.put db "users" user
// |
// | -- Get data
// | maybeUser <- Storage.get db "users" "user-123"
// |
// | -- Query all
// | users <- Storage.getAll db "users"
// |
// | -- Delete
// | Storage.delete db "users" "user-123"
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Argonaut_Decode_Class from "../Data.Argonaut.Decode.Class/index.js";
import * as Data_Argonaut_Encode_Class from "../Data.Argonaut.Encode.Class/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Aff from "../Effect.Aff/index.js";
var bind = /* #__PURE__ */ Control_Bind.bind(Effect_Aff.bindAff);
var pure1 = /* #__PURE__ */ Control_Applicative.pure(Effect_Aff.applicativeAff);

// | Transaction mode
var ReadOnly = /* #__PURE__ */ (function () {
    function ReadOnly() {

    };
    ReadOnly.value = new ReadOnly();
    return ReadOnly;
})();

// | Transaction mode
var ReadWrite = /* #__PURE__ */ (function () {
    function ReadWrite() {

    };
    ReadWrite.value = new ReadWrite();
    return ReadWrite;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // transactions
// ═══════════════════════════════════════════════════════════════════════════════
// | Execute operations in a transaction
var transaction = function (_db) {
    return function (_stores) {
        return function (_mode) {
            return function (action) {
                return action;
            };
        };
    };
};

// | Create a store with indexes
var storeWithIndex = function (name) {
    return function (config) {
        return function (indexes) {
            return {
                name: name,
                config: config,
                indexes: indexes
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // database operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a store configuration
var store = function (name) {
    return function (config) {
        return {
            name: name,
            config: config,
            indexes: [  ]
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // crud operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Put (insert or update) a value
var put = function (dictEncodeJson) {
    var encodeJson = Data_Argonaut_Encode_Class.encodeJson(dictEncodeJson);
    return function (db) {
        return function (storeName) {
            return function (value) {
                return Effect_Aff.makeAff(function (callback) {
                    return function __do() {
                        $foreign.putImpl(db)(storeName)(encodeJson(value))(function (err) {
                            return callback(new Data_Either.Left(err));
                        })(callback(new Data_Either.Right(Data_Unit.unit)))();
                        return Effect_Aff.nonCanceler;
                    };
                });
            };
        };
    };
};

// | Open or create a database
var open = function (name) {
    return function (version) {
        return function (stores) {
            return Effect_Aff.makeAff(function (callback) {
                return function __do() {
                    $foreign.openImpl(name)(version)(stores)(function (err) {
                        return callback(new Data_Either.Left(err));
                    })(function (db) {
                        return callback(new Data_Either.Right(db));
                    })();
                    return Effect_Aff.nonCanceler;
                };
            });
        };
    };
};

// | Get all keys from a store
var keys = function (db) {
    return function (storeName) {
        return Effect_Aff.makeAff(function (callback) {
            return function __do() {
                $foreign.keysImpl(db)(storeName)(function (err) {
                    return callback(new Data_Either.Left(err));
                })(function (ks) {
                    return callback(new Data_Either.Right(ks));
                })();
                return Effect_Aff.nonCanceler;
            };
        });
    };
};

// | Get all values matching an index
var getAllByIndex = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    return function (db) {
        return function (storeName) {
            return function (indexName) {
                return function (value) {
                    return Effect_Aff.makeAff(function (callback) {
                        return function __do() {
                            $foreign.getAllByIndexImpl(db)(storeName)(indexName)(value)(function (err) {
                                return callback(new Data_Either.Left(err));
                            })(function (jsons) {
                                return callback(new Data_Either.Right(Data_Array.mapMaybe(function ($17) {
                                    return Data_Either.hush(decodeJson($17));
                                })(jsons)));
                            })();
                            return Effect_Aff.nonCanceler;
                        };
                    });
                };
            };
        };
    };
};

// | Get all values from a store
var getAll = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    return function (db) {
        return function (storeName) {
            return Effect_Aff.makeAff(function (callback) {
                return function __do() {
                    $foreign.getAllImpl(db)(storeName)(function (err) {
                        return callback(new Data_Either.Left(err));
                    })(function (jsons) {
                        return callback(new Data_Either.Right(Data_Array.mapMaybe(function ($18) {
                            return Data_Either.hush(decodeJson($18));
                        })(jsons)));
                    })();
                    return Effect_Aff.nonCanceler;
                };
            });
        };
    };
};

// | Get a value by key
var get = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    return function (db) {
        return function (storeName) {
            return function (key) {
                return Effect_Aff.makeAff(function (callback) {
                    return function __do() {
                        $foreign.getImpl(db)(storeName)(key)(function (err) {
                            return callback(new Data_Either.Left(err));
                        })(function (json) {
                            return callback(new Data_Either.Right(Data_Either.hush(decodeJson(json))));
                        })(callback(new Data_Either.Right(Data_Maybe.Nothing.value)))();
                        return Effect_Aff.nonCanceler;
                    };
                });
            };
        };
    };
};
var get1 = /* #__PURE__ */ get(Data_Argonaut_Decode_Class.decodeJsonJson);

// | Check if a key exists
var exists = function (db) {
    return function (storeName) {
        return function (key) {
            return bind(get1(db)(storeName)(key))(function (result) {
                return pure1((function () {
                    if (result instanceof Data_Maybe.Just) {
                        return true;
                    };
                    if (result instanceof Data_Maybe.Nothing) {
                        return false;
                    };
                    throw new Error("Failed pattern match at Hydrogen.Offline.Storage (line 304, column 10 - line 306, column 21): " + [ result.constructor.name ]);
                })());
            });
        };
    };
};

// | Delete entire database
var deleteDatabase = function (name) {
    return Effect_Aff.makeAff(function (callback) {
        return function __do() {
            $foreign.deleteDatabaseImpl(name)(function (err) {
                return callback(new Data_Either.Left(err));
            })(callback(new Data_Either.Right(Data_Unit.unit)))();
            return Effect_Aff.nonCanceler;
        };
    });
};

// | Delete a value by key
var $$delete = function (db) {
    return function (storeName) {
        return function (key) {
            return Effect_Aff.makeAff(function (callback) {
                return function __do() {
                    $foreign.deleteImpl(db)(storeName)(key)(function (err) {
                        return callback(new Data_Either.Left(err));
                    })(callback(new Data_Either.Right(Data_Unit.unit)))();
                    return Effect_Aff.nonCanceler;
                };
            });
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Count entries in a store
var count = function (db) {
    return function (storeName) {
        return Effect_Aff.makeAff(function (callback) {
            return function __do() {
                $foreign.countImpl(db)(storeName)(function (err) {
                    return callback(new Data_Either.Left(err));
                })(function (n) {
                    return callback(new Data_Either.Right(n));
                })();
                return Effect_Aff.nonCanceler;
            };
        });
    };
};

// | Close database connection
var close = $foreign.closeImpl;

// | Clear all values from a store
var clear = function (db) {
    return function (storeName) {
        return Effect_Aff.makeAff(function (callback) {
            return function __do() {
                $foreign.clearImpl(db)(storeName)(function (err) {
                    return callback(new Data_Either.Left(err));
                })(callback(new Data_Either.Right(Data_Unit.unit)))();
                return Effect_Aff.nonCanceler;
            };
        });
    };
};
export {
    open,
    close,
    deleteDatabase,
    store,
    storeWithIndex,
    put,
    get,
    getAll,
    getAllByIndex,
    $$delete as delete,
    clear,
    transaction,
    ReadOnly,
    ReadWrite,
    count,
    keys,
    exists
};
