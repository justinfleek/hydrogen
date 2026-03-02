-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                   // hydrogen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Web Framework
-- |
-- | The purest web design language ever created.
-- |
-- | Hydrogen is a pure rendering abstraction — UI as data, not framework-specific
-- | code. Built on lawful abstractions with Schema atoms composing into Elements.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Haskell (Business Logic)
-- |     ↓ generates
-- | PureScript Element (Pure Data)
-- |     ↓ interprets
-- | WebGPU Runtime (Rendering)
-- | ```
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Router (class IsRoute, parseRoute, routeToPath)
-- | import Hydrogen.UI.Core (cls, row, column)
-- | import Hydrogen.UI.Loading (loadingState, spinnerMd)
-- | import Hydrogen.UI.Error (errorState, emptyState)
-- | import Hydrogen.UI.Dialog as Dialog
-- | import Hydrogen.UI.Tabs as Tabs
-- | import Hydrogen.Data.Format (formatBytes, formatDuration)
-- | import Hydrogen.Data.RemoteData (RemoteData(..))
-- | import Hydrogen.Element.Compound.Skeleton as Skeleton
-- | import Hydrogen.Element.Compound.Alert as Alert
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- | ```
-- |
-- | ## Modules
-- |
-- | ### Core
-- | - **Hydrogen.Router** - Type-safe client-side routing
-- | - **Hydrogen.SSG** - Static site generation
-- | - **Hydrogen.HTML.Renderer** - Render Element to HTML strings
-- |
-- | ### Schema (Atomic Design Primitives)
-- | - **Hydrogen.Schema.Color** - Color spaces, atoms, conversions
-- | - **Hydrogen.Schema.Dimension** - Pixel, spacing, viewport atoms
-- | - **Hydrogen.Schema.Geometry** - Radius, corners, transforms
-- | - **Hydrogen.Schema.Typography** - Font size, weight, line height
-- | - **Hydrogen.Schema.Motion** - Easing, duration, spring physics
-- | - **Hydrogen.Schema.Elevation** - Shadow, z-index
-- |
-- | ### Element (Pure UI as Data)
-- | - **Hydrogen.Element.Compound** - Schema-native components
-- | - **Hydrogen.Element.Layout** - Container, Grid, Stack, etc.
-- |
-- | ### Auth
-- | - **Hydrogen.Auth.Session** - Session/token management
-- | - **Hydrogen.Auth.Guard** - Route guards and role-based access
-- |
-- | ### Internationalization
-- | - **Hydrogen.I18n.Locale** - I18n with pluralization and interpolation
-- |
-- | ### Offline/PWA
-- | - **Hydrogen.Offline.Storage** - IndexedDB wrapper
-- | - **Hydrogen.Offline.ServiceWorker** - Service worker registration
-- |
-- | ### Error Handling
-- | - **Hydrogen.Error.Boundary** - Error boundaries, retry, recovery
-- |
-- | ### Infrastructure
-- | - **Hydrogen.Head.Meta** - Dynamic document head, OG tags, JSON-LD
-- | - **Hydrogen.Portal.Layer** - Modal portals, stacking context
-- | - **Hydrogen.Event.Bus** - Typed pub/sub channels
-- | - **Hydrogen.Feature.Flags** - Feature flags, A/B testing
-- | - **Hydrogen.Analytics.Tracker** - Page views, events, Core Web Vitals
-- |
-- | ### UI
-- | - **Hydrogen.UI.Core** - Layout and class utilities
-- | - **Hydrogen.UI.Loading** - Loading states and skeletons
-- | - **Hydrogen.UI.Error** - Error and empty states
-- | - **Hydrogen.UI.Dialog** - Accessible modal dialog with focus trapping
-- | - **Hydrogen.UI.Tabs** - Accessible tabs with keyboard navigation
-- | - **Hydrogen.UI.FocusTrap** - Focus management utilities
-- | - **Hydrogen.UI.AriaHider** - Screen reader isolation utilities
-- | - **Hydrogen.UI.Id** - Unique ID generation for accessibility
-- |
-- | ### Data
-- | - **Hydrogen.Data.Format** - Number/byte/duration formatting
-- | - **Hydrogen.Data.RemoteData** - RemoteData type for async state
module Hydrogen
  ( -- * Core
    module Hydrogen.Router
  , module Hydrogen.SSG
  , module Hydrogen.HTML.Renderer
    -- * UI
  , module Hydrogen.UI.Core
  , module Hydrogen.UI.Loading
  , module Hydrogen.UI.Error
  , module Hydrogen.UI.FocusTrap
  , module Hydrogen.UI.AriaHider
  , module Hydrogen.UI.Id
    -- * Data
  , module Hydrogen.Data.Format
  , module Hydrogen.Data.RemoteData
  ) where

import Hydrogen.Router (class IsRoute, class RouteMetadata, parseRoute, routeToPath, isProtected, isStaticRoute, routeTitle, routeDescription, routeOgImage, getPathname, getHostname, getOrigin, pushState, replaceState, onPopState, interceptLinks, navigate, normalizeTrailingSlash)
import Hydrogen.UI.Core (classes, cls, svgCls, flex, row, column, box, container, section, svgNS)
import Hydrogen.UI.Loading (spinner, spinnerSm, spinnerMd, spinnerLg, loadingState, loadingInline, loadingCard, loadingCardLarge, skeletonText, skeletonRow)
import Hydrogen.UI.Error (errorState, errorCard, errorBadge, errorInline, emptyState)
import Hydrogen.UI.FocusTrap (FocusScope, createFocusScope, destroyFocusScope, trapFocus, releaseFocus, handleTabKey, focusFirst, focusLast, getTabbableElements)
import Hydrogen.UI.AriaHider (AriaHiderState, hideOthers, restoreOthers)
import Hydrogen.UI.Id (IdGenerator, createIdGenerator, nextId, useId)
import Hydrogen.Data.Format (formatBytes, formatBytesCompact, parseBytes, kb, mb, gb, tb, formatNum, formatNumCompact, formatPercent, formatCount, formatDuration, formatDurationCompact, formatDurationMs, percentage, rate, ratio)
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Loading, Failure, Success), fromEither, fromMaybe, toEither, toMaybe, fold, withDefault, isNotAsked, isLoading, isFailure, isSuccess, mapError, map2, map3, map4, sequence, traverse)
import Hydrogen.SSG (DocConfig, defaultDocConfig, PageMeta, renderPage, renderDocument, pageMetaFromRoute, renderRouteStatic, metaTags, ogTags, twitterTags)
import Hydrogen.HTML.Renderer (render, renderWith, RenderOptions, defaultOptions)
