// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // infinite-scroll
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Infinite scroll - load more content as user scrolls
// |
// | Intersection Observer-based infinite loading with bi-directional
// | support, error states, and VirtualScroll integration.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Interaction.InfiniteScroll as InfiniteScroll
// |
// | -- Basic infinite scroll
// | InfiniteScroll.infiniteScroll
// |   [ InfiniteScroll.onLoadMore LoadMoreItems
// |   , InfiniteScroll.threshold 0.8
// |   , InfiniteScroll.loading state.isLoading
// |   , InfiniteScroll.hasMore state.hasMore
// |   ]
// |   [ HH.div_ (map renderItem state.items)
// |   ]
// |
// | -- Bi-directional (chat-like)
// | InfiniteScroll.biDirectional
// |   [ InfiniteScroll.onLoadNewer LoadNewerMessages
// |   , InfiniteScroll.onLoadOlder LoadOlderMessages
// |   , InfiniteScroll.hasNewer state.hasNewer
// |   , InfiniteScroll.hasOlder state.hasOlder
// |   ]
// |   [ HH.div_ (map renderMessage state.messages)
// |   ]
// |
// | -- With VirtualScroll
// | InfiniteScroll.virtualInfiniteScroll
// |   { infiniteProps: [ InfiniteScroll.onLoadMore LoadMore ]
// |   , virtualProps: [ VirtualScroll.itemHeight (VirtualScroll.Fixed 48) ]
// |   , itemCount: Array.length state.items
// |   , renderItem: \i -> renderItem (state.items !! i)
// |   , scrollOffset: state.scrollOffset
// |   }
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_Interaction_VirtualScroll from "../Hydrogen.Interaction.VirtualScroll/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction for loading more content
var LoadDown = /* #__PURE__ */ (function () {
    function LoadDown() {

    };
    LoadDown.value = new LoadDown();
    return LoadDown;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction for loading more content
var LoadUp = /* #__PURE__ */ (function () {
    function LoadUp() {

    };
    LoadUp.value = new LoadUp();
    return LoadUp;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction for loading more content
var LoadBoth = /* #__PURE__ */ (function () {
    function LoadBoth() {

    };
    LoadBoth.value = new LoadBoth();
    return LoadBoth;
})();

// | State of infinite scroll
var Idle = /* #__PURE__ */ (function () {
    function Idle() {

    };
    Idle.value = new Idle();
    return Idle;
})();

// | State of infinite scroll
var Loading = /* #__PURE__ */ (function () {
    function Loading() {

    };
    Loading.value = new Loading();
    return Loading;
})();

// | State of infinite scroll
var $$Error = /* #__PURE__ */ (function () {
    function $$Error(value0) {
        this.value0 = value0;
    };
    $$Error.create = function (value0) {
        return new $$Error(value0);
    };
    return $$Error;
})();

// | State of infinite scroll
var EndReached = /* #__PURE__ */ (function () {
    function EndReached() {

    };
    EndReached.value = new EndReached();
    return EndReached;
})();

// | Reference to infinite scroll for imperative operations
var InfiniteScrollRef = function (x) {
    return x;
};

// | Programmatically trigger load more
var triggerLoadMore = function (v) {
    return Effect_Ref.write(Loading.value)(v.state);
};

// | Set intersection threshold (0-1)
var threshold = function (t) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            threshold: t
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // sub-components
// ═══════════════════════════════════════════════════════════════════════════════
// | Sentinel element that triggers loading when visible
var sentinel = function (opts) {
    if (opts.visible) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "infinite-scroll-sentinel h-1 w-full" ]), Halogen_HTML_Properties.attr("data-sentinel")("true"), Halogen_HTML_Properties.attr("aria-hidden")("true") ])([  ]);
    };
    return Halogen_HTML_Core.text("");
};

// | Scroll to top
var scrollToTop = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            return $foreign.scrollToTopImpl(maybeContainer.value0)();
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.InfiniteScroll (line 540, column 3 - line 542, column 25): " + [ maybeContainer.constructor.name ]);
    };
};

// | Scroll to bottom (useful after loading newer content)
var scrollToBottom = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            return $foreign.scrollToBottomImpl(maybeContainer.value0)();
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.InfiniteScroll (line 532, column 3 - line 534, column 25): " + [ maybeContainer.constructor.name ]);
    };
};

// | Save current scroll position
var saveScrollPosition = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            var pos = $foreign.saveScrollPositionImpl(maybeContainer.value0)();
            Effect_Ref.write(new Data_Maybe.Just(pos))(v.savedPosition)();
            return new Data_Maybe.Just(pos);
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return Data_Maybe.Nothing.value;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.InfiniteScroll (line 487, column 3 - line 492, column 28): " + [ maybeContainer.constructor.name ]);
    };
};

// | Set root margin for intersection observer
var rootMargin = function (m) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            rootMargin: m
        };
    };
};

// | Restore saved scroll position
var restoreScrollPosition = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        var maybePosition = Effect_Ref.read(v.savedPosition)();
        if (maybeContainer instanceof Data_Maybe.Just && maybePosition instanceof Data_Maybe.Just) {
            return $foreign.restoreScrollPositionImpl(maybeContainer.value0)(maybePosition.value0)();
        };
        return Data_Unit.unit;
    };
};

// | Reset scroll position to top
var resetScroll = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            return $foreign.scrollToTopImpl(maybeContainer.value0)();
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.InfiniteScroll (line 524, column 3 - line 526, column 25): " + [ maybeContainer.constructor.name ]);
    };
};

// | Handler for loading older content (top)
var onLoadOlder = function (handler) {
    return function (props) {
        return {
            onLoadNewer: props.onLoadNewer,
            hasNewer: props.hasNewer,
            hasOlder: props.hasOlder,
            loadingNewer: props.loadingNewer,
            loadingOlder: props.loadingOlder,
            threshold: props.threshold,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            className: props.className,
            onLoadOlder: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for loading newer content (bottom)
var onLoadNewer = function (handler) {
    return function (props) {
        return {
            onLoadOlder: props.onLoadOlder,
            hasNewer: props.hasNewer,
            hasOlder: props.hasOlder,
            loadingNewer: props.loadingNewer,
            loadingOlder: props.loadingOlder,
            threshold: props.threshold,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            className: props.className,
            onLoadNewer: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler when more content should be loaded
var onLoadMore = function (handler) {
    return function (props) {
        return {
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            onLoadMore: new Data_Maybe.Just(handler)
        };
    };
};

// | Set loading state for older content
var loadingOlder = function (l) {
    return function (props) {
        return {
            onLoadNewer: props.onLoadNewer,
            onLoadOlder: props.onLoadOlder,
            hasNewer: props.hasNewer,
            hasOlder: props.hasOlder,
            loadingNewer: props.loadingNewer,
            threshold: props.threshold,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            className: props.className,
            loadingOlder: l
        };
    };
};

// | Set loading state for newer content
var loadingNewer = function (l) {
    return function (props) {
        return {
            onLoadNewer: props.onLoadNewer,
            onLoadOlder: props.onLoadOlder,
            hasNewer: props.hasNewer,
            hasOlder: props.hasOlder,
            loadingOlder: props.loadingOlder,
            threshold: props.threshold,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            className: props.className,
            loadingNewer: l
        };
    };
};

// | Loading indicator
var loadingIndicator = function (customContent) {
    var defaultLoading = Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2 text-muted-foreground" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-4 h-4 border-2 border-current border-t-transparent rounded-full animate-spin" ]) ])([  ]), Halogen_HTML_Elements.span_([ Halogen_HTML_Core.text("Loading...") ]) ]);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "infinite-scroll-loading flex items-center justify-center py-4" ]) ])([ Data_Maybe.fromMaybe(defaultLoading)(customContent) ]);
};

// | Custom loading indicator
var loadingContent = function (content) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            loadingContent: new Data_Maybe.Just(content)
        };
    };
};

// | Set loading state
var loading = function (l) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            loading: l
        };
    };
};

// | Set whether older content exists
var hasOlder = function (h) {
    return function (props) {
        return {
            onLoadNewer: props.onLoadNewer,
            onLoadOlder: props.onLoadOlder,
            hasNewer: props.hasNewer,
            loadingNewer: props.loadingNewer,
            loadingOlder: props.loadingOlder,
            threshold: props.threshold,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            className: props.className,
            hasOlder: h
        };
    };
};

// | Set whether newer content exists
var hasNewer = function (h) {
    return function (props) {
        return {
            onLoadNewer: props.onLoadNewer,
            onLoadOlder: props.onLoadOlder,
            hasOlder: props.hasOlder,
            loadingNewer: props.loadingNewer,
            loadingOlder: props.loadingOlder,
            threshold: props.threshold,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            className: props.className,
            hasNewer: h
        };
    };
};

// | Set whether more content exists
var hasMore = function (h) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            hasMore: h
        };
    };
};

// | Error state with retry
var errorState = function (opts) {
    var defaultError = Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center gap-2 text-destructive" ]) ])([ Halogen_HTML_Elements.span_([ Halogen_HTML_Core.text("Error: " + opts.message) ]), (function () {
        if (opts.onRetry instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "px-4 py-2 text-sm bg-secondary hover:bg-secondary/80 rounded-md" ]) ])([ Halogen_HTML_Core.text("Retry") ]);
        };
        if (opts.onRetry instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.InfiniteScroll (line 465, column 9 - line 470, column 32): " + [ opts.onRetry.constructor.name ]);
    })() ]);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "infinite-scroll-error flex flex-col items-center justify-center py-4 gap-2" ]) ])([ (function () {
        if (opts.customContent instanceof Data_Maybe.Just) {
            return opts.customContent.value0(opts.message);
        };
        if (opts.customContent instanceof Data_Maybe.Nothing) {
            return defaultError;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.InfiniteScroll (line 456, column 7 - line 458, column 32): " + [ opts.customContent.constructor.name ]);
    })() ]);
};

// | Custom error content (receives error message)
var errorContent = function (render) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            errorContent: new Data_Maybe.Just(render)
        };
    };
};
var eqLoadDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof LoadDown && y instanceof LoadDown) {
                return true;
            };
            if (x instanceof LoadUp && y instanceof LoadUp) {
                return true;
            };
            if (x instanceof LoadBoth && y instanceof LoadBoth) {
                return true;
            };
            return false;
        };
    }
};
var eqInfiniteScrollState = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Idle && y instanceof Idle) {
                return true;
            };
            if (x instanceof Loading && y instanceof Loading) {
                return true;
            };
            if (x instanceof $$Error && y instanceof $$Error) {
                return x.value0 === y.value0;
            };
            if (x instanceof EndReached && y instanceof EndReached) {
                return true;
            };
            return false;
        };
    }
};

// | End of list indicator
var endOfList = function (customContent) {
    var defaultEnd = Halogen_HTML_Elements.span_([ Halogen_HTML_Core.text("You've reached the end") ]);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "infinite-scroll-end flex items-center justify-center py-4 text-muted-foreground" ]) ])([ Data_Maybe.fromMaybe(defaultEnd)(customContent) ]);
};

// | Custom end of list indicator
var endContent = function (content) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            endContent: new Data_Maybe.Just(content)
        };
    };
};

// | Disable loading
var disabled = function (d) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className,
            disabled: d
        };
    };
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        onLoadMore: Data_Maybe.Nothing.value,
        threshold: 0.8,
        loading: false,
        hasMore: true,
        disabled: false,
        rootMargin: "0px 0px 200px 0px",
        loadingContent: Data_Maybe.Nothing.value,
        endContent: Data_Maybe.Nothing.value,
        errorContent: Data_Maybe.Nothing.value,
        onError: Data_Maybe.Nothing.value,
        onRetry: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Infinite scroll container
// |
// | Wraps content and adds a sentinel element that triggers loading
// | when it becomes visible in the viewport.
var infiniteScroll = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var sentinelEl = sentinel({
            visible: props.hasMore && (!props.loading && !props.disabled),
            onIntersect: props.onLoadMore
        });
        var loadingEl = (function () {
            if (props.loading) {
                return loadingIndicator(props.loadingContent);
            };
            return Halogen_HTML_Core.text("");
        })();
        var endEl = (function () {
            var $68 = !props.hasMore;
            if ($68) {
                return endOfList(props.endContent);
            };
            return Halogen_HTML_Core.text("");
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "infinite-scroll-container relative", props.className ]), Halogen_HTML_Properties.attr("data-root-margin")(props.rootMargin), Halogen_HTML_Properties.attr("data-threshold")(show(props.threshold)) ])(append1(children)([ sentinelEl, loadingEl, endEl ]));
    };
};

// | Infinite scroll with virtual scrolling
// |
// | Combines infinite loading with virtual scrolling for
// | maximum performance with large datasets.
var virtualInfiniteScroll = function (opts) {
    var virtualList = Hydrogen_Interaction_VirtualScroll.virtualList(opts.virtualProps)(opts.renderItem)(opts.scrollOffset);
    var infinitePropsApplied = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(opts.infiniteProps);
    var loadingEl = (function () {
        if (infinitePropsApplied.loading) {
            return loadingIndicator(infinitePropsApplied.loadingContent);
        };
        return Halogen_HTML_Core.text("");
    })();
    var sentinelEl = sentinel({
        visible: infinitePropsApplied.hasMore && !infinitePropsApplied.loading,
        onIntersect: infinitePropsApplied.onLoadMore
    });
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "virtual-infinite-scroll-container", infinitePropsApplied.className ]) ])([ virtualList, sentinelEl, loadingEl ]);
};
var defaultBiProps = /* #__PURE__ */ (function () {
    return {
        onLoadNewer: Data_Maybe.Nothing.value,
        onLoadOlder: Data_Maybe.Nothing.value,
        hasNewer: true,
        hasOlder: true,
        loadingNewer: false,
        loadingOlder: false,
        threshold: 0.8,
        rootMargin: "100px",
        loadingContent: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // imperative api
// ═══════════════════════════════════════════════════════════════════════════════
// | Create infinite scroll ref
var createInfiniteScrollRef = function __do() {
    var containerRef = Effect_Ref["new"](Data_Maybe.Nothing.value)();
    var state = Effect_Ref["new"](Idle.value)();
    var savedPosition = Effect_Ref["new"](Data_Maybe.Nothing.value)();
    return {
        containerRef: containerRef,
        state: state,
        savedPosition: savedPosition
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            onLoadMore: props.onLoadMore,
            threshold: props.threshold,
            loading: props.loading,
            hasMore: props.hasMore,
            disabled: props.disabled,
            rootMargin: props.rootMargin,
            loadingContent: props.loadingContent,
            endContent: props.endContent,
            errorContent: props.errorContent,
            onError: props.onError,
            onRetry: props.onRetry,
            className: props.className + (" " + c)
        };
    };
};

// | Bi-directional infinite scroll
// |
// | Loads content in both directions - useful for chat interfaces,
// | timelines, and other bi-directional content.
var biDirectional = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultBiProps)(propMods);
        var topLoading = (function () {
            if (props.loadingOlder) {
                return loadingIndicator(props.loadingContent);
            };
            return Halogen_HTML_Core.text("");
        })();
        var topSentinel = sentinel({
            visible: props.hasOlder && !props.loadingOlder,
            onIntersect: props.onLoadOlder
        });
        var bottomSentinel = sentinel({
            visible: props.hasNewer && !props.loadingNewer,
            onIntersect: props.onLoadNewer
        });
        var bottomLoading = (function () {
            if (props.loadingNewer) {
                return loadingIndicator(props.loadingContent);
            };
            return Halogen_HTML_Core.text("");
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "bi-directional-scroll-container relative", props.className ]) ])(append1([ topSentinel, topLoading ])(append1(children)([ bottomLoading, bottomSentinel ])));
    };
};
export {
    infiniteScroll,
    biDirectional,
    virtualInfiniteScroll,
    sentinel,
    loadingIndicator,
    endOfList,
    errorState,
    LoadDown,
    LoadUp,
    LoadBoth,
    Idle,
    Loading,
    $$Error as Error,
    EndReached,
    onLoadMore,
    threshold,
    loading,
    hasMore,
    disabled,
    rootMargin,
    loadingContent,
    endContent,
    errorContent,
    className,
    onLoadNewer,
    onLoadOlder,
    hasNewer,
    hasOlder,
    loadingNewer,
    loadingOlder,
    saveScrollPosition,
    restoreScrollPosition,
    createInfiniteScrollRef,
    triggerLoadMore,
    resetScroll,
    scrollToBottom,
    scrollToTop,
    eqLoadDirection,
    eqInfiniteScrollState
};
