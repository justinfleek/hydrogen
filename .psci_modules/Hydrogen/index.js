// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                   // hydrogen
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Hydrogen Web Framework
// |
// | A PureScript/Halogen web framework for building robust web applications
// | with type-safe routing, API clients, SSG support, and accessible UI components.
// |
// | ## Quick Start
// |
// | ```purescript
// | import Hydrogen.Router (class IsRoute, parseRoute, routeToPath)
// | import Hydrogen.API.Client (get, post, withAuth)
// | import Hydrogen.UI.Core (cls, row, column)
// | import Hydrogen.UI.Loading (loadingState, spinnerMd)
// | import Hydrogen.UI.Error (errorState, emptyState)
// | import Hydrogen.Data.Format (formatBytes, formatDuration)
// | import Hydrogen.Data.RemoteData (RemoteData(..))
// | import Hydrogen.Query as Q
// | import Hydrogen.State.Atom as Atom
// | import Hydrogen.State.Store as Store
// | import Hydrogen.Realtime.WebSocket as WS
// | import Hydrogen.Auth.Session as Session
// | import Hydrogen.I18n.Locale as I18n
// | import Hydrogen.Feature.Flags as Flags
// | import Hydrogen.Analytics.Tracker as Analytics
// | ```
// |
// | ## Modules
// |
// | ### Core
// | - **Hydrogen.Router** - Type-safe client-side routing
// | - **Hydrogen.API.Client** - HTTP client with JSON encoding
// | - **Hydrogen.Query** - Data fetching with caching, deduplication, and QueryState
// | - **Hydrogen.SSG** - Static site generation
// | - **Hydrogen.HTML.Renderer** - Render Halogen HTML to strings
// |
// | ### State Management
// | - **Hydrogen.State.Atom** - Jotai/Recoil-style atomic state
// | - **Hydrogen.State.Store** - Redux-style store with middleware
// |
// | ### Realtime
// | - **Hydrogen.Realtime.WebSocket** - WebSocket client with reconnection
// | - **Hydrogen.Realtime.SSE** - Server-Sent Events client
// |
// | ### Auth
// | - **Hydrogen.Auth.Session** - Session/token management
// | - **Hydrogen.Auth.Guard** - Route guards and role-based access
// |
// | ### Internationalization
// | - **Hydrogen.I18n.Locale** - I18n with pluralization and interpolation
// |
// | ### Offline/PWA
// | - **Hydrogen.Offline.Storage** - IndexedDB wrapper
// | - **Hydrogen.Offline.ServiceWorker** - Service worker registration
// |
// | ### Error Handling
// | - **Hydrogen.Error.Boundary** - Error boundaries, retry, recovery
// |
// | ### Infrastructure
// | - **Hydrogen.Head.Meta** - Dynamic document head, OG tags, JSON-LD
// | - **Hydrogen.Portal.Layer** - Modal portals, stacking context
// | - **Hydrogen.Event.Bus** - Typed pub/sub channels
// | - **Hydrogen.Feature.Flags** - Feature flags, A/B testing
// | - **Hydrogen.Analytics.Tracker** - Page views, events, Core Web Vitals
// |
// | ### UI
// | - **Hydrogen.UI.Core** - Layout and class utilities
// | - **Hydrogen.UI.Loading** - Loading states and skeletons
// | - **Hydrogen.UI.Error** - Error and empty states
// | - **Hydrogen.Data.Format** - Number/byte/duration formatting
// | - **Hydrogen.Data.RemoteData** - RemoteData type for async state
import * as Hydrogen_API_Client from "../Hydrogen.API.Client/index.js";
import * as Hydrogen_Data_Format from "../Hydrogen.Data.Format/index.js";
import * as Hydrogen_Data_RemoteData from "../Hydrogen.Data.RemoteData/index.js";
import * as Hydrogen_HTML_Renderer from "../Hydrogen.HTML.Renderer/index.js";
import * as Hydrogen_Router from "../Hydrogen.Router/index.js";
import * as Hydrogen_SSG from "../Hydrogen.SSG/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
import * as Hydrogen_UI_Error from "../Hydrogen.UI.Error/index.js";
import * as Hydrogen_UI_Loading from "../Hydrogen.UI.Loading/index.js";

export {
    defaultConfig,
    delete,
    get,
    patch,
    post,
    put,
    withAuth,
    withLogging
} from "../Hydrogen.API.Client/index.js";
export {
    formatBytes,
    formatBytesCompact,
    formatCount,
    formatDuration,
    formatDurationCompact,
    formatDurationMs,
    formatNum,
    formatNumCompact,
    formatPercent,
    gb,
    kb,
    mb,
    parseBytes,
    percentage,
    rate,
    ratio,
    tb
} from "../Hydrogen.Data.Format/index.js";
export {
    Failure,
    Loading,
    NotAsked,
    Success,
    fold,
    fromEither,
    fromMaybe,
    isFailure,
    isLoading,
    isNotAsked,
    isSuccess,
    map2,
    map3,
    map4,
    mapError,
    sequence,
    toEither,
    toMaybe,
    traverse,
    withDefault
} from "../Hydrogen.Data.RemoteData/index.js";
export {
    defaultOptions,
    render,
    renderWith
} from "../Hydrogen.HTML.Renderer/index.js";
export {
    getHostname,
    getOrigin,
    getPathname,
    interceptLinks,
    isProtected,
    isStaticRoute,
    navigate,
    normalizeTrailingSlash,
    onPopState,
    parseRoute,
    pushState,
    replaceState,
    routeDescription,
    routeOgImage,
    routeTitle,
    routeToPath
} from "../Hydrogen.Router/index.js";
export {
    defaultDocConfig,
    metaTags,
    ogTags,
    pageMetaFromRoute,
    renderDocument,
    renderPage,
    renderRouteStatic,
    twitterTags
} from "../Hydrogen.SSG/index.js";
export {
    box,
    classes,
    cls,
    column,
    container,
    flex,
    row,
    section,
    svgCls,
    svgNS
} from "../Hydrogen.UI.Core/index.js";
export {
    emptyState,
    errorBadge,
    errorCard,
    errorInline,
    errorState
} from "../Hydrogen.UI.Error/index.js";
export {
    loadingCard,
    loadingCardLarge,
    loadingInline,
    loadingState,
    skeletonRow,
    skeletonText,
    spinner,
    spinnerLg,
    spinnerMd,
    spinnerSm
} from "../Hydrogen.UI.Loading/index.js";
