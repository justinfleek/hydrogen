-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // reactive // viewport // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Viewport type, constructors, accessors, controls, and state.
-- |
-- | This module provides the main Viewport record type and functions
-- | for creating, accessing, and manipulating viewports.

module Hydrogen.Schema.Reactive.Viewport.Core
  ( -- * Viewport Identity
    viewportId
  , viewportNamespace
  
  -- * Viewport Core
  , Viewport
  , viewport
  , viewportWithId
  
  -- * Viewport Accessors
  , getId
  , getWidth
  , getHeight
  , getBreakpoint
  , getOrientation
  , getDeviceClass
  , getDimensions
  
  -- * Viewport Controls
  , defaultControls
  , addControl
  , removeControl
  , hasControl
  
  -- * Viewport State
  , ViewportState
  , initialState
  , withZoom
  , withScroll
  , withFullscreen
  ) where

import Prelude
  ( class Eq
  , not
  , (==)
  , (<>)
  , ($)
  )

import Data.Array as Array

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Reactive.ScrollState (ScrollPosition, originScroll)
import Hydrogen.Schema.Reactive.Viewport.Types
  ( ViewportId(ViewportId)
  , Breakpoint
  , Orientation
  , DeviceClass
  , ViewportControl(Scroll, Zoom, Fullscreen)
  , ViewportControls
  , ZoomLevel
  , zoom100
  )
import Hydrogen.Schema.Reactive.Viewport.Breakpoints
  ( breakpointFromWidth
  , orientationFromDimensions
  , deviceClassFromBreakpoint
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | UUID5 namespace for viewport identities.
viewportNamespace :: String
viewportNamespace = "viewport.hydrogen.schema"

-- | Create viewport ID from namespace and name.
-- |
-- | ```purescript
-- | viewportId "acme-corp" "main-dashboard"
-- | -- => ViewportId "a3f8c2d1-..." (deterministic)
-- | ```
viewportId :: String -> String -> ViewportId
viewportId ns name =
  let uuid = UUID5.uuid5 UUID5.nsElement (viewportNamespace <> ":" <> ns <> ":" <> name)
  in ViewportId (UUID5.toString uuid)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // viewport core
-- ═════════════════════════════════════════════════════════════════════════════

-- | A viewport — a bounded viewing region with identity and state.
-- |
-- | Viewports are first-class containers that can display any content.
-- | They have deterministic identity, dimensions, controls, and settings.
type Viewport =
  { id :: ViewportId
  , width :: Int
  , height :: Int
  , breakpoint :: Breakpoint
  , orientation :: Orientation
  , deviceClass :: DeviceClass
  , controls :: ViewportControls
  , state :: ViewportState
  }

-- | Create a viewport with auto-generated ID.
-- |
-- | ID is derived from namespace + name via UUID5.
viewport 
  :: { namespace :: String
     , name :: String
     , width :: Int
     , height :: Int
     }
  -> Viewport
viewport cfg =
  let
    bp = breakpointFromWidth cfg.width
    orient = orientationFromDimensions cfg.width cfg.height
  in
    { id: viewportId cfg.namespace cfg.name
    , width: cfg.width
    , height: cfg.height
    , breakpoint: bp
    , orientation: orient
    , deviceClass: deviceClassFromBreakpoint bp
    , controls: defaultControls
    , state: initialState
    }

-- | Create a viewport with explicit ID.
viewportWithId
  :: { id :: ViewportId
     , width :: Int
     , height :: Int
     }
  -> Viewport
viewportWithId cfg =
  let
    bp = breakpointFromWidth cfg.width
    orient = orientationFromDimensions cfg.width cfg.height
  in
    { id: cfg.id
    , width: cfg.width
    , height: cfg.height
    , breakpoint: bp
    , orientation: orient
    , deviceClass: deviceClassFromBreakpoint bp
    , controls: defaultControls
    , state: initialState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get viewport ID.
getId :: Viewport -> ViewportId
getId vp = vp.id

-- | Get viewport width.
getWidth :: Viewport -> Int
getWidth vp = vp.width

-- | Get viewport height.
getHeight :: Viewport -> Int
getHeight vp = vp.height

-- | Get current breakpoint.
getBreakpoint :: Viewport -> Breakpoint
getBreakpoint vp = vp.breakpoint

-- | Get current orientation.
getOrientation :: Viewport -> Orientation
getOrientation vp = vp.orientation

-- | Get device class.
getDeviceClass :: Viewport -> DeviceClass
getDeviceClass vp = vp.deviceClass

-- | Get dimensions as record.
getDimensions :: Viewport -> { width :: Int, height :: Int }
getDimensions vp = { width: vp.width, height: vp.height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport controls
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default controls for most viewports.
defaultControls :: ViewportControls
defaultControls = [Scroll, Zoom, Fullscreen]

-- | Add a control to viewport controls.
addControl :: ViewportControl -> ViewportControls -> ViewportControls
addControl ctrl ctrls =
  if Array.elem ctrl ctrls
    then ctrls
    else Array.snoc ctrls ctrl

-- | Remove a control from viewport controls.
removeControl :: ViewportControl -> ViewportControls -> ViewportControls
removeControl ctrl ctrls = Array.filter (\c -> not (c == ctrl)) ctrls

-- | Check if viewport has a control.
hasControl :: ViewportControl -> ViewportControls -> Boolean
hasControl ctrl ctrls = Array.elem ctrl ctrls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mutable state of a viewport.
type ViewportState =
  { zoom :: ZoomLevel
  , scroll :: ScrollPosition
  , isFullscreen :: Boolean
  }

-- | Initial viewport state.
initialState :: ViewportState
initialState =
  { zoom: zoom100
  , scroll: originScroll
  , isFullscreen: false
  }

-- | Set zoom level.
withZoom :: ZoomLevel -> ViewportState -> ViewportState
withZoom z state = state { zoom = z }

-- | Set scroll position.
withScroll :: ScrollPosition -> ViewportState -> ViewportState
withScroll pos state = state { scroll = pos }

-- | Set fullscreen state.
withFullscreen :: Boolean -> ViewportState -> ViewportState
withFullscreen fs state = state { isFullscreen = fs }
