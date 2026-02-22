// | Data fetching with caching, deduplication, and automatic refetch.
// |
// | Inspired by TanStack Query, designed to work with zeitschrift-generated clients.
// |
// | ## Design
// |
// | Query state is split into two concerns:
// |
// | 1. **RemoteData e a** - The core data state (NotAsked, Loading, Failure, Success)
// |    This is a lawful Monad, so you can use `do` notation and all standard combinators.
// |
// | 2. **QueryState e a** - Record with metadata:
// |    ```purescript
// |    { data :: RemoteData e a
// |    , isStale :: Boolean      -- Data exists but may be outdated
// |    , isFetching :: Boolean   -- Currently fetching (initial or refetch)
// |    }
// |    ```
// |
// | This design mirrors TanStack Query where `data` and `isFetching` are separate.
// | You can show stale data while a background refetch is in progress.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Query as Q
// | import Hydrogen.Data.RemoteData as RD
// | 
// | -- Create a query client (typically in your main)
// | client <- Q.newClient Q.defaultClientOptions
// | 
// | -- Fetch data with caching
// | state <- Q.query client
// |   { key: ["user", userId]
// |   , fetch: Api.getUser config userId
// |   }
// | 
// | -- Use the RemoteData for rendering
// | case state.data of
// |   RD.NotAsked -> HH.text "Not loaded"
// |   RD.Loading -> spinner
// |   RD.Failure e -> errorCard e
// |   RD.Success user -> userCard user
// |
// | -- Or use fold
// | Q.foldData state
// |   { notAsked: HH.text "Click to load"
// |   , loading: spinner
// |   , failure: \e -> errorCard e
// |   , success: \user -> userCard user
// |   }
// |
// | -- Show stale data with loading indicator
// | if state.isFetching && Q.hasData state
// |   then showWithSpinner (Q.getData state)
// |   else normalRender state.data
// | 
// | -- Invalidate cache after mutation
// | Q.invalidate client ["user", userId]
// | ```
// |
// | ## Combining Queries with RemoteData
// |
// | Because RemoteData is a lawful Monad, you can combine queries naturally:
// |
// | ```purescript
// | -- Using ado syntax (Applicative - parallel semantics)
// | let combined = ado
// |       user <- userState.data
// |       posts <- postsState.data
// |       in { user, posts }
// |
// | -- Using do syntax (Monad - sequential semantics)
// | let dependent = do
// |       user <- userState.data
// |       posts <- postsState.data
// |       pure $ renderUserWithPosts user posts
// | ```
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Argonaut_Decode_Class from "../Data.Argonaut.Decode.Class/index.js";
import * as Data_Argonaut_Decode_Error from "../Data.Argonaut.Decode.Error/index.js";
import * as Data_Argonaut_Encode_Class from "../Data.Argonaut.Encode.Class/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_DateTime_Instant from "../Data.DateTime.Instant/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Map_Internal from "../Data.Map.Internal/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Newtype from "../Data.Newtype/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Aff from "../Effect.Aff/index.js";
import * as Effect_Class from "../Effect.Class/index.js";
import * as Effect_Now from "../Effect.Now/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Hydrogen_Data_RemoteData from "../Hydrogen.Data.RemoteData/index.js";
var bind = /* #__PURE__ */ Control_Bind.bind(Effect_Aff.bindAff);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect_Aff.applicativeAff);
var notEq = /* #__PURE__ */ Data_Eq.notEq(/* #__PURE__ */ Data_Maybe.eqMaybe(Data_Eq.eqString));
var $$delete = /* #__PURE__ */ Data_Map_Internal["delete"](Data_Ord.ordString);
var unwrap = /* #__PURE__ */ Data_Newtype.unwrap();
var update = /* #__PURE__ */ Data_Map_Internal.update(Data_Ord.ordString);
var map = /* #__PURE__ */ Data_Functor.map(Data_Map_Internal.functorMap);
var mapMaybeWithKey = /* #__PURE__ */ Data_Map_Internal.mapMaybeWithKey(Data_Ord.ordString);
var map1 = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var lookup = /* #__PURE__ */ Data_Map_Internal.lookup(Data_Ord.ordString);
var bind2 = /* #__PURE__ */ Control_Bind.bind(Data_Maybe.bindMaybe);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit)(Effect_Aff.bindAff);
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var liftEffect = /* #__PURE__ */ Effect_Class.liftEffect(Effect_Aff.monadEffectAff);
var insert = /* #__PURE__ */ Data_Map_Internal.insert(Data_Ord.ordString);
var show = /* #__PURE__ */ Data_Show.show(Data_Argonaut_Decode_Error.showJsonDecodeError);
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect_Aff.functorAff);

// =============================================================================
//                                                                     // client
// =============================================================================
// | Opaque query client that manages cache and in-flight requests.
var QueryClient = function (x) {
    return x;
};

// | Batcher for DataLoader-style request coalescing.
var Batcher = function (x) {
    return x;
};

// | Get success value or fall back to default.
var withDefaultData = function (def) {
    return function (state) {
        if (state.data instanceof Hydrogen_Data_RemoteData.Success) {
            return state.data.value0;
        };
        return def;
    };
};

// | Execute a paginated query.
var queryPaged = function (dictDecodeJson) {
    return function (dictEncodeJson) {
        return function (_client) {
            return function (opts) {
                return bind(opts.fetch(Data_Maybe.Nothing.value))(function (result) {
                    return pure((function () {
                        if (result instanceof Data_Either.Left) {
                            return {
                                data: new Hydrogen_Data_RemoteData.Failure(result.value0),
                                pages: [  ],
                                hasNextPage: false,
                                isFetching: false,
                                isFetchingNextPage: false
                            };
                        };
                        if (result instanceof Data_Either.Right) {
                            return {
                                data: new Hydrogen_Data_RemoteData.Success([ result.value0 ]),
                                pages: [ result.value0 ],
                                hasNextPage: notEq(opts.getNextPageParam(result.value0))(Data_Maybe.Nothing.value),
                                isFetching: false,
                                isFetchingNextPage: false
                            };
                        };
                        throw new Error("Failed pattern match at Hydrogen.Query (line 549, column 10 - line 563, column 8): " + [ result.constructor.name ]);
                    })());
                });
            };
        };
    };
};

// | Create a new query client with custom options.
var newClientWith = function (options) {
    return function __do() {
        var cache = Effect_Ref["new"](Data_Map_Internal.empty)();
        var inFlight = Effect_Ref["new"](Data_Map_Internal.empty)();
        return {
            cache: cache,
            inFlight: inFlight,
            options: options
        };
    };
};

// | Create a new batcher.
var newBatcher = function (options) {
    return function __do() {
        var queue = Effect_Ref["new"]([  ])();
        var scheduled = Effect_Ref["new"](false)();
        return {
            queue: queue,
            scheduled: scheduled,
            options: options
        };
    };
};

// | Load multiple values in a single batch.
var loadMany = function (dictOrd) {
    var fromFoldable = Data_Map_Internal.fromFoldable(dictOrd)(Data_Foldable.foldableArray);
    return function (v) {
        return function (keys) {
            return bind(v.options.batchFn(keys))(function (results) {
                return pure(fromFoldable(results));
            });
        };
    };
};

// | Load a single value, batching with concurrent requests.
var load = function (dictOrd) {
    var loadMany1 = loadMany(dictOrd);
    var lookup1 = Data_Map_Internal.lookup(dictOrd);
    return function (batcher) {
        return function (key) {
            return bind(loadMany1(batcher)([ key ]))(function (results) {
                return pure(Data_Maybe.fromMaybe(new Data_Either.Left("Key not found in batch result"))(lookup1(key)(results)));
            });
        };
    };
};
var keyToString = /* #__PURE__ */ Data_String_Common.joinWith(":");

// | Remove a query from the cache entirely.
var removeQuery = function (v) {
    return function (key) {
        return Effect_Ref.modify_($$delete(keyToString(key)))(v.cache);
    };
};
var isEntryStale = function (entry) {
    return function (currentTime) {
        var toMs = function (instant) {
            return unwrap(Data_DateTime_Instant.unInstant(instant));
        };
        return toMs(currentTime) > toMs(entry.staleAt);
    };
};

// | Invalidate a query with an exact key match.
var invalidateExact = function (v) {
    return function (key) {
        return function __do() {
            var currentTime = Effect_Now.now();
            return Effect_Ref.modify_(update(function (e) {
                return new Data_Maybe.Just({
                    json: e.json,
                    updatedAt: e.updatedAt,
                    staleAt: currentTime
                });
            })(keyToString(key)))(v.cache)();
        };
    };
};

// | Invalidate all queries in the cache.
var invalidateAll = function (v) {
    return function __do() {
        var currentTime = Effect_Now.now();
        return Effect_Ref.modify_(map(function (e) {
            return {
                json: e.json,
                updatedAt: e.updatedAt,
                staleAt: currentTime
            };
        }))(v.cache)();
    };
};

// =============================================================================
//                                                          // cache invalidation
// =============================================================================
// | Invalidate all queries matching a key prefix.
// |
// | ```purescript
// | -- Invalidate all user queries
// | Q.invalidate client ["user"]
// | 
// | -- Invalidate specific user
// | Q.invalidate client ["user", "123"]
// | ```
var invalidate = function (v) {
    return function (prefix) {
        var markStaleIfMatches = function (prefixStr) {
            return function (currentTime) {
                return function (key) {
                    return function (entry) {
                        if (Data_String_CodeUnits.contains(prefixStr)(key)) {
                            return new Data_Maybe.Just({
                                json: entry.json,
                                updatedAt: entry.updatedAt,
                                staleAt: currentTime
                            });
                        };
                        if (Data_Boolean.otherwise) {
                            return new Data_Maybe.Just(entry);
                        };
                        throw new Error("Failed pattern match at Hydrogen.Query (line 484, column 3 - line 487, column 29): " + [ prefixStr.constructor.name, currentTime.constructor.name, key.constructor.name, entry.constructor.name ]);
                    };
                };
            };
        };
        var prefixStr = keyToString(prefix);
        return function __do() {
            var currentTime = Effect_Now.now();
            return Effect_Ref.modify_(mapMaybeWithKey(markStaleIfMatches(prefixStr)(currentTime)))(v.cache)();
        };
    };
};

// | Initial query state (not asked, not fetching).
var initialQueryState = /* #__PURE__ */ (function () {
    return {
        data: Hydrogen_Data_RemoteData.NotAsked.value,
        isStale: false,
        isFetching: false
    };
})();

// | Initial paged state.
var initialPagedState = /* #__PURE__ */ (function () {
    return {
        data: Hydrogen_Data_RemoteData.NotAsked.value,
        pages: [  ],
        hasNextPage: false,
        isFetching: false,
        isFetchingNextPage: false
    };
})();

// | Get cached data for a query (if available).
var getQueryData = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    return function (v) {
        return function (key) {
            return function __do() {
                var entry = map1(lookup(keyToString(key)))(Effect_Ref.read(v.cache))();
                return bind2(entry)(function (e) {
                    return Data_Either.hush(decodeJson(e.json));
                });
            };
        };
    };
};

// | Get the error from a QueryState if in failure state.
var getError = function (state) {
    if (state.data instanceof Hydrogen_Data_RemoteData.Failure) {
        return new Data_Maybe.Just(state.data.value0);
    };
    return Data_Maybe.Nothing.value;
};

// =============================================================================
//                                                          // QueryState helpers
// =============================================================================
// | Get the data from a QueryState if available.
var getData = function (state) {
    if (state.data instanceof Hydrogen_Data_RemoteData.Success) {
        return new Data_Maybe.Just(state.data.value0);
    };
    return Data_Maybe.Nothing.value;
};

// | Check if QueryState has data (Success or stale data preserved).
var hasData = function (state) {
    return Data_Maybe.isJust(getData(state));
};

// | Fold over the RemoteData in a QueryState.
// |
// | ```purescript
// | Q.foldData state
// |   { notAsked: HH.text "Click to load"
// |   , loading: spinner
// |   , failure: \e -> errorCard e
// |   , success: \user -> userCard user
// |   }
// | ```
var foldData = function (handlers) {
    return function (state) {
        if (state.data instanceof Hydrogen_Data_RemoteData.NotAsked) {
            return handlers.notAsked;
        };
        if (state.data instanceof Hydrogen_Data_RemoteData.Loading) {
            return handlers.loading;
        };
        if (state.data instanceof Hydrogen_Data_RemoteData.Failure) {
            return handlers.failure(state.data.value0);
        };
        if (state.data instanceof Hydrogen_Data_RemoteData.Success) {
            return handlers.success(state.data.value0);
        };
        throw new Error("Failed pattern match at Hydrogen.Query (line 684, column 27 - line 688, column 34): " + [ state.data.constructor.name ]);
    };
};

// | Fetch with retry logic.
var fetchWithRetry = function (dictEncodeJson) {
    var encodeJson = Data_Argonaut_Encode_Class.encodeJson(dictEncodeJson);
    return function (fetch) {
        return function (retriesLeft) {
            return function (retryDelay) {
                return bind(fetch)(function (result) {
                    if (result instanceof Data_Either.Right) {
                        return pure(new Data_Either.Right(encodeJson(result.value0)));
                    };
                    if (result instanceof Data_Either.Left && retriesLeft > 0) {
                        return discard(Effect_Aff.delay(retryDelay))(function () {
                            return fetchWithRetry(dictEncodeJson)(fetch)(retriesLeft - 1 | 0)(retryDelay);
                        });
                    };
                    if (result instanceof Data_Either.Left) {
                        return pure(new Data_Either.Left(result.value0));
                    };
                    throw new Error("Failed pattern match at Hydrogen.Query (line 410, column 3 - line 415, column 32): " + [ result.constructor.name ]);
                });
            };
        };
    };
};

// | Fetch the next page.
var fetchNextPage = function (dictDecodeJson) {
    return function (dictEncodeJson) {
        return function (_client) {
            return function (opts) {
                return function (state) {
                    var lastPage = Data_Array.last(state.pages);
                    var nextCursor = bind2(lastPage)(opts.getNextPageParam);
                    if (nextCursor instanceof Data_Maybe.Nothing) {
                        return pure({
                            data: state.data,
                            isFetching: state.isFetching,
                            isFetchingNextPage: state.isFetchingNextPage,
                            pages: state.pages,
                            hasNextPage: false
                        });
                    };
                    if (nextCursor instanceof Data_Maybe.Just) {
                        return bind(opts.fetch(new Data_Maybe.Just(nextCursor.value0)))(function (result) {
                            return pure((function () {
                                if (result instanceof Data_Either.Left) {
                                    return {
                                        hasNextPage: state.hasNextPage,
                                        isFetching: state.isFetching,
                                        pages: state.pages,
                                        data: new Hydrogen_Data_RemoteData.Failure(result.value0),
                                        isFetchingNextPage: false
                                    };
                                };
                                if (result instanceof Data_Either.Right) {
                                    var newPages = append(state.pages)([ result.value0 ]);
                                    return {
                                        isFetching: state.isFetching,
                                        data: new Hydrogen_Data_RemoteData.Success(newPages),
                                        pages: newPages,
                                        hasNextPage: notEq(opts.getNextPageParam(result.value0))(Data_Maybe.Nothing.value),
                                        isFetchingNextPage: false
                                    };
                                };
                                throw new Error("Failed pattern match at Hydrogen.Query (line 581, column 14 - line 591, column 14): " + [ result.constructor.name ]);
                            })());
                        });
                    };
                    throw new Error("Failed pattern match at Hydrogen.Query (line 577, column 3 - line 591, column 14): " + [ nextCursor.constructor.name ]);
                };
            };
        };
    };
};

// | Default query options (just provide key and fetch).
var defaultQueryOptions = function (key) {
    return function (fetch) {
        return {
            key: key,
            fetch: fetch,
            staleTime: Data_Maybe.Nothing.value,
            retry: 0,
            retryDelay: 1000.0
        };
    };
};

// | Default client options.
// | 
// | - staleTime: 0 (always refetch)
// | - cacheTime: 5 minutes
var defaultClientOptions = {
    staleTime: 0.0,
    cacheTime: 300000.0
};

// | Create a new query client with default options.
var newClient = /* #__PURE__ */ newClientWith(defaultClientOptions);

// =============================================================================
//                                                                    // helpers
// =============================================================================
// | Add milliseconds to an instant.
// | Falls back to original instant if result would be invalid.
var addMs = function (inst) {
    return function (v) {
        var v1 = Data_DateTime_Instant.unInstant(inst);
        var newMs = v1 + v;
        return Data_Maybe.fromMaybe(inst)(Data_DateTime_Instant.instant(newMs));
    };
};

// | Fetch fresh data, handling deduplication and retries.
var fetchFresh = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    return function (dictEncodeJson) {
        var fetchWithRetry1 = fetchWithRetry(dictEncodeJson);
        return function (v) {
            return function (opts) {
                return function (staleData) {
                    var cacheKey = keyToString(opts.key);
                    return bind(liftEffect(map1(lookup(cacheKey))(Effect_Ref.read(v.inFlight))))(function (inFlightFiber) {
                        return bind((function () {
                            if (inFlightFiber instanceof Data_Maybe.Just) {
                                return Effect_Aff.joinFiber(inFlightFiber.value0);
                            };
                            if (inFlightFiber instanceof Data_Maybe.Nothing) {
                                var doFetch = fetchWithRetry1(opts.fetch)(opts.retry)(opts.retryDelay);
                                return bind(Effect_Aff.forkAff(doFetch))(function (fiber) {
                                    return discard(liftEffect(Effect_Ref.modify_(insert(cacheKey)(fiber))(v.inFlight)))(function () {
                                        return bind(Effect_Aff.joinFiber(fiber))(function (result) {
                                            return discard(liftEffect(Effect_Ref.modify_($$delete(cacheKey))(v.inFlight)))(function () {
                                                return discard((function () {
                                                    if (result instanceof Data_Either.Right) {
                                                        return bind(liftEffect(Effect_Now.now))(function (updateTime) {
                                                            var staleTime = Data_Maybe.fromMaybe(v.options.staleTime)(opts.staleTime);
                                                            var staleAt = addMs(updateTime)(staleTime);
                                                            var entry = {
                                                                json: result.value0,
                                                                updatedAt: updateTime,
                                                                staleAt: staleAt
                                                            };
                                                            return liftEffect(Effect_Ref.modify_(insert(cacheKey)(entry))(v.cache));
                                                        });
                                                    };
                                                    if (result instanceof Data_Either.Left) {
                                                        return pure(Data_Unit.unit);
                                                    };
                                                    throw new Error("Failed pattern match at Hydrogen.Query (line 359, column 7 - line 366, column 28): " + [ result.constructor.name ]);
                                                })())(function () {
                                                    return pure(result);
                                                });
                                            });
                                        });
                                    });
                                });
                            };
                            throw new Error("Failed pattern match at Hydrogen.Query (line 346, column 17 - line 368, column 18): " + [ inFlightFiber.constructor.name ]);
                        })())(function (jsonResult) {
                            return pure((function () {
                                if (jsonResult instanceof Data_Either.Left) {
                                    if (staleData instanceof Data_Maybe.Just) {
                                        return {
                                            data: new Hydrogen_Data_RemoteData.Success(staleData.value0),
                                            isStale: true,
                                            isFetching: false
                                        };
                                    };
                                    if (staleData instanceof Data_Maybe.Nothing) {
                                        return {
                                            data: new Hydrogen_Data_RemoteData.Failure(jsonResult.value0),
                                            isStale: false,
                                            isFetching: false
                                        };
                                    };
                                    throw new Error("Failed pattern match at Hydrogen.Query (line 374, column 7 - line 386, column 12): " + [ staleData.constructor.name ]);
                                };
                                if (jsonResult instanceof Data_Either.Right) {
                                    var v1 = decodeJson(jsonResult.value0);
                                    if (v1 instanceof Data_Either.Left) {
                                        return {
                                            data: new Hydrogen_Data_RemoteData.Failure(show(v1.value0)),
                                            isStale: false,
                                            isFetching: false
                                        };
                                    };
                                    if (v1 instanceof Data_Either.Right) {
                                        return {
                                            data: new Hydrogen_Data_RemoteData.Success(v1.value0),
                                            isStale: false,
                                            isFetching: false
                                        };
                                    };
                                    throw new Error("Failed pattern match at Hydrogen.Query (line 388, column 7 - line 398, column 12): " + [ v1.constructor.name ]);
                                };
                                throw new Error("Failed pattern match at Hydrogen.Query (line 371, column 10 - line 398, column 12): " + [ jsonResult.constructor.name ]);
                            })());
                        });
                    });
                };
            };
        };
    };
};

// | Execute a query with an enabled flag.
// |
// | Useful for conditional fetching:
// | ```purescript
// | state <- Q.queryWith client opts { enabled: userId /= "" }
// | ```
var queryWith = function (dictDecodeJson) {
    var decodeJson = Data_Argonaut_Decode_Class.decodeJson(dictDecodeJson);
    var fetchFresh1 = fetchFresh(dictDecodeJson);
    return function (dictEncodeJson) {
        var fetchFresh2 = fetchFresh1(dictEncodeJson);
        return function (v) {
            return function (v1) {
                return function (v2) {
                    if (!v2.enabled) {
                        return pure(initialQueryState);
                    };
                    var cacheKey = keyToString(v1.key);
                    return bind(liftEffect(Effect_Now.now))(function (currentTime) {
                        return bind(liftEffect(map1(lookup(cacheKey))(Effect_Ref.read(v.cache))))(function (cachedEntry) {
                            if (cachedEntry instanceof Data_Maybe.Just && !isEntryStale(cachedEntry.value0)(currentTime)) {
                                var v3 = decodeJson(cachedEntry.value0.json);
                                if (v3 instanceof Data_Either.Right) {
                                    return pure({
                                        data: new Hydrogen_Data_RemoteData.Success(v3.value0),
                                        isStale: false,
                                        isFetching: false
                                    });
                                };
                                if (v3 instanceof Data_Either.Left) {
                                    return fetchFresh2(v)(v1)(Data_Maybe.Nothing.value);
                                };
                                throw new Error("Failed pattern match at Hydrogen.Query (line 315, column 7 - line 321, column 49): " + [ v3.constructor.name ]);
                            };
                            if (cachedEntry instanceof Data_Maybe.Just) {
                                var staleData = Data_Either.hush(decodeJson(cachedEntry.value0.json));
                                return fetchFresh2(v)(v1)(staleData);
                            };
                            if (cachedEntry instanceof Data_Maybe.Nothing) {
                                return fetchFresh2(v)(v1)(Data_Maybe.Nothing.value);
                            };
                            throw new Error("Failed pattern match at Hydrogen.Query (line 312, column 3 - line 329, column 46): " + [ cachedEntry.constructor.name ]);
                        });
                    });
                };
            };
        };
    };
};

// =============================================================================
//                                                            // query operations
// =============================================================================
// | Execute a query with caching and deduplication.
// |
// | - Returns cached data immediately if fresh
// | - Deduplicates concurrent requests to the same key
// | - Refetches in background if stale
var query = function (dictDecodeJson) {
    var queryWith1 = queryWith(dictDecodeJson);
    return function (dictEncodeJson) {
        var queryWith2 = queryWith1(dictEncodeJson);
        return function (client) {
            return function (opts) {
                return queryWith2(client)(opts)({
                    enabled: true
                });
            };
        };
    };
};

// | Prefetch a query without waiting for the result.
var prefetch = function (dictDecodeJson) {
    var query1 = query(dictDecodeJson);
    return function (dictEncodeJson) {
        var query2 = query1(dictEncodeJson);
        return function (client) {
            return function (opts) {
                return $$void(query2(client)(opts));
            };
        };
    };
};

// | Manually set cached data for a query.
// |
// | Useful for optimistic updates:
// | ```purescript
// | -- Optimistically update
// | Q.setQueryData client ["user", id] updatedUser
// | 
// | -- If mutation fails, invalidate to refetch
// | Q.invalidate client ["user", id]
// | ```
var setQueryData = function (dictEncodeJson) {
    var encodeJson = Data_Argonaut_Encode_Class.encodeJson(dictEncodeJson);
    return function (v) {
        return function (key) {
            return function (value) {
                return function __do() {
                    var currentTime = Effect_Now.now();
                    var staleAt = addMs(currentTime)(v.options.staleTime);
                    var entry = {
                        json: encodeJson(value),
                        updatedAt: currentTime,
                        staleAt: staleAt
                    };
                    return Effect_Ref.modify_(insert(keyToString(key))(entry))(v.cache)();
                };
            };
        };
    };
};
export {
    defaultClientOptions,
    newClient,
    newClientWith,
    defaultQueryOptions,
    initialQueryState,
    query,
    queryWith,
    prefetch,
    getQueryData,
    setQueryData,
    invalidate,
    invalidateExact,
    invalidateAll,
    removeQuery,
    initialPagedState,
    queryPaged,
    fetchNextPage,
    newBatcher,
    load,
    loadMany,
    getData,
    getError,
    hasData,
    foldData,
    withDefaultData
};
export {
    Failure,
    Loading,
    NotAsked,
    Success,
    fromEither,
    isFailure,
    isLoading,
    isNotAsked,
    isSuccess,
    map2,
    map3,
    map4,
    mapError,
    toMaybe
} from "../Hydrogen.Data.RemoteData/index.js";
