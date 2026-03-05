-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // router
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Client-side Routing Infrastructure
-- |
-- | This module provides a typeclass-based routing system that allows
-- | applications to define their own route ADTs while using shared
-- | routing infrastructure.
-- |
-- | ## Design Philosophy
-- |
-- | Navigation commands are **pure data** (Cmd values) instead of direct
-- | effects. The Rust/WASM runtime interprets these commands and executes
-- | the actual History API manipulation.
-- |
-- | At billion-agent scale, commands are encoded as SIGIL frames:
-- |   - `PushUrl` → opcode 0xD2 (ROUTE_PUSH)
-- |   - `ReplaceUrl` → opcode 0xD3 (ROUTE_REPLACE)
-- |   - `Back` → opcode 0xD4 (ROUTE_BACK)
-- |   - `Forward` → opcode 0xD5 (ROUTE_FORWARD)
-- |
-- | straylight-llm consumes these frames via ZMQ4 at 10,000 tokens/second.
-- |
-- | ## Usage
-- |
-- | 1. Define your route type:
-- | ```purescript
-- | data Route = Home | About | Dashboard | NotFound
-- | ```
-- |
-- | 2. Implement the IsRoute class:
-- | ```purescript
-- | instance isRouteMyRoute :: IsRoute Route where
-- |   parseRoute "/" = Home
-- |   parseRoute "/about" = About
-- |   parseRoute "/dashboard" = Dashboard
-- |   parseRoute _ = NotFound
-- |   
-- |   routeToPath Home = "/"
-- |   routeToPath About = "/about"
-- |   routeToPath Dashboard = "/dashboard"
-- |   routeToPath NotFound = "/"
-- | ```
-- |
-- | 3. Use navigation commands in your update function:
-- | ```purescript
-- | import Hydrogen.Router (navigate)
-- | import Hydrogen.Runtime.Cmd (pushUrl, back)
-- |
-- | update :: Msg -> State -> Transition State Msg
-- | update msg state = case msg of
-- |   GoToAbout ->
-- |     transition state (navigate About)
-- |   
-- |   GoBack ->
-- |     transition state back
-- | ```
-- |
-- | ## Initial Route
-- |
-- | For the initial route, pass it as part of your application's flags:
-- |
-- | ```purescript
-- | type Flags = { initialPath :: String }
-- |
-- | init :: Flags -> Transition State Msg
-- | init flags =
-- |   let route = parseRoute flags.initialPath
-- |   in noCmd { currentRoute: route, ... }
-- | ```
-- |
-- | The runtime provides the initial path when starting the application.

module Hydrogen.Router
  ( -- * Route typeclass
    class IsRoute
  , parseRoute
  , routeToPath
  
  -- * Route metadata
  , class RouteMetadata
  , isProtected
  , isStaticRoute
  , routeTitle
  , routeDescription
  , routeOgImage
  
  -- * Navigation commands (re-exported from Cmd)
  -- | Use these in your update functions
  , module CmdReExports
  
  -- * Route-typed navigation
  , navigate
  , navigateReplace
  
  -- * Utilities
  , normalizeTrailingSlash
  
  -- * SIGIL Frame Encoding (advanced)
  , encodeRoutePushFrame
  , encodeRouteReplaceFrame
  , encodeRouteBackFrame
  , encodeRouteForwardFrame
  
  -- * Effect-based browser operations
  , getPathname
  , getHostname
  , getOrigin
  , pushState
  , replaceState
  , onPopState
  , interceptLinks
  ) where

import Prelude
  ( class Eq
  , Unit
  , ($)
  , (==)
  )

import Effect (Effect)
import Data.Maybe (Maybe)
import Data.String.CodeUnits as SCU

import Hydrogen.Runtime.Cmd 
  ( Cmd
  , pushUrl
  , replaceUrl
  , back
  , forward
  ) as CmdReExports

import Hydrogen.Runtime.Cmd (Cmd, pushUrl, replaceUrl)
import Hydrogen.Scraper.Wire.Types (Frame)
import Hydrogen.Scraper.Wire.Encode 
  ( encodeRoutePush
  , encodeRouteReplace
  , encodeRouteBack
  , encodeRouteForward
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // route typeclass
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Typeclass for route types that can be parsed from and serialized to paths.
-- |
-- | Laws:
-- | - `parseRoute (routeToPath r) == r` for all valid routes
-- | - `routeToPath` should produce paths starting with "/"
-- |
-- | This typeclass enables type-safe routing where the compiler ensures
-- | all routes are handled and navigation uses valid paths.
class IsRoute route where
  -- | Parse a URL path into a route.
  -- |
  -- | The parser should handle all possible paths, including invalid ones.
  -- | A common pattern is to return a `NotFound` route for unrecognized paths.
  parseRoute :: String -> route
  
  -- | Convert a route back to a URL path.
  -- |
  -- | The resulting path should always start with "/" and be valid for
  -- | use with the History API.
  routeToPath :: route -> String

-- | Optional metadata for routes.
-- |
-- | Implement this typeclass if your routes have protection or SSG semantics.
-- | This enables the "write once, SSG or dynamic" pattern where route metadata
-- | is defined once and used for both static generation and runtime rendering.
class RouteMetadata route where
  -- | Whether the route requires authentication.
  -- |
  -- | Protected routes should redirect to login if the user is not authenticated.
  isProtected :: route -> Boolean
  
  -- | Whether the route should be statically generated (SSG).
  -- |
  -- | Returns true for public pages that benefit from static generation,
  -- | false for SPA-only routes that require client-side data.
  isStaticRoute :: route -> Boolean
  
  -- | Page title for the route.
  -- |
  -- | Used in `<title>` tag and OpenGraph `og:title` meta tag.
  routeTitle :: route -> String
  
  -- | Meta description for the route.
  -- |
  -- | Used in description meta tag and OpenGraph `og:description`.
  routeDescription :: route -> String
  
  -- | Optional OpenGraph image URL for the route.
  -- |
  -- | Used in `og:image` meta tag for social media previews.
  routeOgImage :: route -> Maybe String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // navigation commands
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Navigate to a route programmatically (push to history).
-- |
-- | This is a type-safe wrapper around `pushUrl` that uses your route type.
-- |
-- | ```purescript
-- | update GoToAbout state =
-- |   transition state (navigate About)
-- | ```
-- |
-- | SIGIL opcode: 0xD2 (ROUTE_PUSH)
navigate :: forall route msg. IsRoute route => route -> Cmd msg
navigate route = pushUrl (routeToPath route)

-- | Navigate to a route by replacing current history entry.
-- |
-- | Use this for redirects that shouldn't appear in browser history.
-- |
-- | ```purescript
-- | update (AuthSuccess user) state =
-- |   transition state { user = Just user } (navigateReplace Dashboard)
-- | ```
-- |
-- | SIGIL opcode: 0xD3 (ROUTE_REPLACE)
navigateReplace :: forall route msg. IsRoute route => route -> Cmd msg
navigateReplace route = replaceUrl (routeToPath route)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Normalize paths by removing trailing slashes (except for root).
-- |
-- | ```purescript
-- | normalizeTrailingSlash "/" == "/"
-- | normalizeTrailingSlash "/about/" == "/about"
-- | normalizeTrailingSlash "/about" == "/about"
-- | ```
-- |
-- | Use this in your `parseRoute` implementation for consistent path handling.
normalizeTrailingSlash :: String -> String
normalizeTrailingSlash "/" = "/"
normalizeTrailingSlash path =
  if SCU.takeRight 1 path == "/" 
    then SCU.dropRight 1 path
    else path

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // sigil frame encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode a route push command as a SIGIL frame.
-- |
-- | SIGIL opcode: 0xD2 (ROUTE_PUSH)
-- | Payload: varint-prefixed UTF-8 URL
-- |
-- | For advanced usage (testing, custom transport). Normal apps use `navigate`.
encodeRoutePushFrame :: String -> Frame
encodeRoutePushFrame = encodeRoutePush

-- | Encode a route replace command as a SIGIL frame.
-- |
-- | SIGIL opcode: 0xD3 (ROUTE_REPLACE)
-- | Payload: varint-prefixed UTF-8 URL
encodeRouteReplaceFrame :: String -> Frame
encodeRouteReplaceFrame = encodeRouteReplace

-- | Encode a back navigation command as a SIGIL frame.
-- |
-- | SIGIL opcode: 0xD4 (ROUTE_BACK)
-- | Payload: none
encodeRouteBackFrame :: Frame
encodeRouteBackFrame = encodeRouteBack

-- | Encode a forward navigation command as a SIGIL frame.
-- |
-- | SIGIL opcode: 0xD5 (ROUTE_FORWARD)
-- | Payload: none
encodeRouteForwardFrame :: Frame
encodeRouteForwardFrame = encodeRouteForward

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // effect-based browser api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the current pathname from the browser location.
-- |
-- | Effect-based operation for reading browser state directly.
-- | For Elm-architecture apps, prefer using subscriptions for location changes.
foreign import getPathname :: Effect String

-- | Get the current hostname from the browser location.
foreign import getHostname :: Effect String

-- | Get the current origin from the browser location.
foreign import getOrigin :: Effect String

-- | Push a state onto the browser history.
-- |
-- | Effect-based operation. For Elm-architecture apps, use `pushUrl` Cmd instead.
foreign import pushState :: String -> Effect Unit

-- | Replace the current browser history entry.
-- |
-- | Effect-based operation. For Elm-architecture apps, use `replaceUrl` Cmd instead.
foreign import replaceState :: String -> Effect Unit

-- | Subscribe to popstate events (browser back/forward).
-- |
-- | Returns an unsubscribe function.
foreign import onPopState :: (String -> Effect Unit) -> Effect (Effect Unit)

-- | Intercept link clicks for SPA routing.
-- |
-- | Intercepts clicks on anchor elements with relative hrefs and calls
-- | the provided handler with the path. Returns an unsubscribe function.
foreign import interceptLinks :: (String -> Effect Unit) -> Effect (Effect Unit)
