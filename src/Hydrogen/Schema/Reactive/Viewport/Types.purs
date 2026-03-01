-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // reactive // viewport // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for Viewport module.
-- |
-- | This module contains all fundamental types used throughout the Viewport
-- | system: identifiers, breakpoints, orientation, device class, controls,
-- | and zoom levels.

module Hydrogen.Schema.Reactive.Viewport.Types
  ( -- * Viewport Identity
    ViewportId(ViewportId)
  , viewportIdFromString
  , unwrapViewportId
  , viewportIdToString
  
  -- * Breakpoint Type
  , Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  , allBreakpoints
  
  -- * Orientation
  , Orientation(Portrait, Landscape, Square)
  
  -- * Device Class
  , DeviceClass(Phone, Tablet, Desktop, LargeDesktop)
  
  -- * Viewport Controls
  , ViewportControl(Zoom, Pan, Scroll, Fullscreen, Refresh, Close)
  , ViewportControls
  
  -- * Zoom Level
  , ZoomLevel(ZoomLevel)
  , zoomLevel
  , zoomFit
  , zoomFill
  , zoom100
  , zoom50
  , zoom200
  , unwrapZoom
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , Ordering(LT, EQ, GT)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deterministic identifier for a viewport.
-- |
-- | Generated via UUID5 from namespace + name, ensuring the same viewport
-- | configuration always produces the same ID across sessions and systems.
newtype ViewportId = ViewportId String

derive instance eqViewportId :: Eq ViewportId
derive instance ordViewportId :: Ord ViewportId

instance showViewportId :: Show ViewportId where
  show (ViewportId id) = "ViewportId:" <> id

-- | Create viewport ID from raw string (for deserialization).
viewportIdFromString :: String -> ViewportId
viewportIdFromString = ViewportId

-- | Unwrap viewport ID to String.
unwrapViewportId :: ViewportId -> String
unwrapViewportId (ViewportId id) = id

-- | Convert to string (for serialization).
viewportIdToString :: ViewportId -> String
viewportIdToString = unwrapViewportId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // breakpoint type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard breakpoint tiers.
-- |
-- | Aligned with Tailwind CSS breakpoints for ecosystem compatibility.
-- | These are semantic size tiers, not arbitrary pixel values.
data Breakpoint
  = Xs   -- ^ Extra small: 0-639px (mobile portrait)
  | Sm   -- ^ Small: 640-767px (mobile landscape)
  | Md   -- ^ Medium: 768-1023px (tablet portrait)
  | Lg   -- ^ Large: 1024-1279px (tablet landscape / small desktop)
  | Xl   -- ^ Extra large: 1280-1535px (desktop)
  | Xxl  -- ^ 2x Extra large: 1536px+ (large desktop)

derive instance eqBreakpoint :: Eq Breakpoint

instance ordBreakpoint :: Ord Breakpoint where
  compare Xs Xs = EQ
  compare Xs _ = LT
  compare Sm Xs = GT
  compare Sm Sm = EQ
  compare Sm _ = LT
  compare Md Xs = GT
  compare Md Sm = GT
  compare Md Md = EQ
  compare Md _ = LT
  compare Lg Xs = GT
  compare Lg Sm = GT
  compare Lg Md = GT
  compare Lg Lg = EQ
  compare Lg _ = LT
  compare Xl Xxl = LT
  compare Xl Xl = EQ
  compare Xl _ = GT
  compare Xxl Xxl = EQ
  compare Xxl _ = GT

instance showBreakpoint :: Show Breakpoint where
  show Xs = "xs"
  show Sm = "sm"
  show Md = "md"
  show Lg = "lg"
  show Xl = "xl"
  show Xxl = "2xl"

-- | All breakpoints in order from smallest to largest.
allBreakpoints :: Array Breakpoint
allBreakpoints = [Xs, Sm, Md, Lg, Xl, Xxl]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen/viewport orientation.
data Orientation
  = Portrait   -- ^ Height > Width
  | Landscape  -- ^ Width > Height
  | Square     -- ^ Width == Height

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Portrait = "portrait"
  show Landscape = "landscape"
  show Square = "square"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // device class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic device classification.
-- |
-- | Higher-level than breakpoints — describes device capabilities,
-- | not just screen size.
data DeviceClass
  = Phone        -- ^ Xs, Sm — handheld, touch-primary
  | Tablet       -- ^ Md, Lg — portable, touch or stylus
  | Desktop      -- ^ Xl — stationary, mouse/keyboard primary
  | LargeDesktop -- ^ Xxl — multi-monitor, ultrawide

derive instance eqDeviceClass :: Eq DeviceClass

instance showDeviceClass :: Show DeviceClass where
  show Phone = "phone"
  show Tablet = "tablet"
  show Desktop = "desktop"
  show LargeDesktop = "large-desktop"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport controls
-- ═════════════════════════════════════════════════════════════════════════════

-- | Available viewport controls.
-- |
-- | Not all viewports support all controls — a document viewer might
-- | support Zoom and Scroll, while a video player supports Fullscreen.
data ViewportControl
  = Zoom       -- ^ Zoom in/out
  | Pan        -- ^ Pan/drag content
  | Scroll     -- ^ Scroll content
  | Fullscreen -- ^ Enter/exit fullscreen
  | Refresh    -- ^ Refresh/reload content
  | Close      -- ^ Close viewport

derive instance eqViewportControl :: Eq ViewportControl

instance showViewportControl :: Show ViewportControl where
  show Zoom = "zoom"
  show Pan = "pan"
  show Scroll = "scroll"
  show Fullscreen = "fullscreen"
  show Refresh = "refresh"
  show Close = "close"

-- | Set of available controls for a viewport.
type ViewportControls = Array ViewportControl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // zoom level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom level for viewport content.
-- |
-- | 1.0 = 100% (fit to viewport)
-- | 2.0 = 200% (zoomed in)
-- | 0.5 = 50% (zoomed out)
newtype ZoomLevel = ZoomLevel Number

derive instance eqZoomLevel :: Eq ZoomLevel
derive instance ordZoomLevel :: Ord ZoomLevel

instance showZoomLevel :: Show ZoomLevel where
  show (ZoomLevel z) = show z <> "x"

-- | Create zoom level from number.
zoomLevel :: Number -> ZoomLevel
zoomLevel = ZoomLevel

-- | Zoom to fit content in viewport.
zoomFit :: ZoomLevel
zoomFit = ZoomLevel 1.0

-- | Zoom to fill viewport (may crop).
zoomFill :: ZoomLevel
zoomFill = ZoomLevel 1.0

-- | 100% zoom.
zoom100 :: ZoomLevel
zoom100 = ZoomLevel 1.0

-- | 50% zoom.
zoom50 :: ZoomLevel
zoom50 = ZoomLevel 0.5

-- | 200% zoom.
zoom200 :: ZoomLevel
zoom200 = ZoomLevel 2.0

-- | Unwrap zoom level to Number.
unwrapZoom :: ZoomLevel -> Number
unwrapZoom (ZoomLevel z) = z
