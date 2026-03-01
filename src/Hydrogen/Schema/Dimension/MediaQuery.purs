-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // dimension // media-query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MediaQuery — Type-safe CSS media query representation.
-- |
-- | **WHY MEDIAQUERY?**
-- | Media queries in CSS are stringly typed and error-prone. This module
-- | provides a type-safe ADT for media queries, eliminating JavaScript FFI
-- | for media query matching and construction.
-- |
-- | **Supported Features:**
-- | - Width constraints (min-width, max-width)
-- | - Height constraints (min-height, max-height)
-- | - Orientation (portrait, landscape)
-- | - User preferences (color scheme, reduced motion)
-- | - Display characteristics (resolution, color depth)
-- | - Pointer capabilities (coarse, fine, none)
-- | - Combinators (and, or, not)
-- |
-- | **Use Cases:**
-- | - Responsive design breakpoints
-- | - Dark mode detection
-- | - Accessibility preferences
-- | - Device capability detection
-- | - Print styling
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Dimension.Device (Pixel, PixelsPerInch)
-- |
-- | ## Dependents
-- | - Hydrogen.Schema.Dimension.Breakpoint
-- | - Component.ThemeProvider
-- | - Hook.UseMediaQuery

module Hydrogen.Schema.Dimension.MediaQuery
  ( -- * Media Query Type
    MediaQuery(..)
  
  -- * Screen Orientation
  , ScreenOrientation(Portrait, Landscape)
  
  -- * Color Scheme
  , ColorScheme(Light, Dark, NoPreference)
  
  -- * Pointer Type
  , PointerType(PointerNone, PointerCoarse, PointerFine)
  
  -- * Hover Capability
  , HoverCapability(HoverNone, HoverOnDemand, Hover)
  
  -- * Display Mode
  , DisplayMode(Fullscreen, Standalone, MinimalUI, Browser)
  
  -- * Media Type
  , MediaType(Screen, Print, All)
  
  -- * Constructors
  , minWidth
  , maxWidth
  , minHeight
  , maxHeight
  , orientation
  , prefersColorScheme
  , prefersReducedMotion
  , prefersReducedTransparency
  , prefersContrast
  , pointer
  , anyPointer
  , hover
  , anyHover
  , displayMode
  , resolution
  , minResolution
  , colorGamut
  , mediaType
  
  -- * Combinators
  , and
  , or
  , not
  
  -- * Common Queries
  , isMobile
  , isTablet
  , isDesktop
  , isDarkMode
  , isLightMode
  , prefersReducedMotionQuery
  , isTouchDevice
  , isHighResolution
  , isPrint
  
  -- * Serialization
  , toCSS
  
  -- * Evaluation
  , matches
  , MediaEnvironment
  , defaultMediaEnvironment
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )
import Prelude (not) as P

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), unwrapPixel, PixelsPerInch(PixelsPerInch), unwrapPpi)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // screen orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen orientation values.
data ScreenOrientation
  = Portrait   -- ^ Height > width
  | Landscape  -- ^ Width >= height

derive instance eqScreenOrientation :: Eq ScreenOrientation
derive instance ordScreenOrientation :: Ord ScreenOrientation

instance showScreenOrientation :: Show ScreenOrientation where
  show Portrait = "portrait"
  show Landscape = "landscape"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // color scheme
-- ═════════════════════════════════════════════════════════════════════════════

-- | User's preferred color scheme.
data ColorScheme
  = Light         -- ^ Light mode preference
  | Dark          -- ^ Dark mode preference
  | NoPreference  -- ^ No explicit preference

derive instance eqColorScheme :: Eq ColorScheme
derive instance ordColorScheme :: Ord ColorScheme

instance showColorScheme :: Show ColorScheme where
  show Light = "light"
  show Dark = "dark"
  show NoPreference = "no-preference"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pointer type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Primary pointing device capability.
data PointerType
  = PointerNone    -- ^ No pointing device
  | PointerCoarse  -- ^ Imprecise (touch, stylus)
  | PointerFine    -- ^ Precise (mouse, trackpad)

derive instance eqPointerType :: Eq PointerType
derive instance ordPointerType :: Ord PointerType

instance showPointerType :: Show PointerType where
  show PointerNone = "none"
  show PointerCoarse = "coarse"
  show PointerFine = "fine"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // hover capability
-- ═════════════════════════════════════════════════════════════════════════════

-- | Device hover capability.
data HoverCapability
  = HoverNone      -- ^ Cannot hover (touch devices)
  | HoverOnDemand  -- ^ Can hover but with effort
  | Hover          -- ^ Full hover support (mouse)

derive instance eqHoverCapability :: Eq HoverCapability
derive instance ordHoverCapability :: Ord HoverCapability

instance showHoverCapability :: Show HoverCapability where
  show HoverNone = "none"
  show HoverOnDemand = "on-demand"
  show Hover = "hover"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // display mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | PWA display mode.
data DisplayMode
  = Fullscreen  -- ^ Full screen, no browser UI
  | Standalone  -- ^ App-like, minimal browser UI
  | MinimalUI   -- ^ Minimal browser UI elements
  | Browser     -- ^ Normal browser tab

derive instance eqDisplayMode :: Eq DisplayMode
derive instance ordDisplayMode :: Ord DisplayMode

instance showDisplayMode :: Show DisplayMode where
  show Fullscreen = "fullscreen"
  show Standalone = "standalone"
  show MinimalUI = "minimal-ui"
  show Browser = "browser"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // media type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media type for output targeting.
data MediaType
  = Screen  -- ^ Screen display
  | Print   -- ^ Print output
  | All     -- ^ All media types

derive instance eqMediaType :: Eq MediaType
derive instance ordMediaType :: Ord MediaType

instance showMediaType :: Show MediaType where
  show Screen = "screen"
  show Print = "print"
  show All = "all"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // media query type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type-safe media query representation.
-- |
-- | Represents all standard CSS media features as an ADT.
-- | Can be combined using And, Or, and Not constructors.
data MediaQuery
  = MinWidth Pixel
    -- ^ @media (min-width: Xpx)
  | MaxWidth Pixel
    -- ^ @media (max-width: Xpx)
  | MinHeight Pixel
    -- ^ @media (min-height: Xpx)
  | MaxHeight Pixel
    -- ^ @media (max-height: Xpx)
  | Orientation ScreenOrientation
    -- ^ @media (orientation: portrait|landscape)
  | PrefersColorScheme ColorScheme
    -- ^ @media (prefers-color-scheme: light|dark)
  | PrefersReducedMotion Boolean
    -- ^ @media (prefers-reduced-motion: reduce|no-preference)
  | PrefersReducedTransparency Boolean
    -- ^ @media (prefers-reduced-transparency: reduce|no-preference)
  | PrefersContrast Boolean
    -- ^ @media (prefers-contrast: more|no-preference)
  | Pointer PointerType
    -- ^ @media (pointer: none|coarse|fine)
  | AnyPointer PointerType
    -- ^ @media (any-pointer: none|coarse|fine)
  | HoverMedia HoverCapability
    -- ^ @media (hover: none|hover)
  | AnyHover HoverCapability
    -- ^ @media (any-hover: none|hover)
  | DisplayModeQuery DisplayMode
    -- ^ @media (display-mode: fullscreen|standalone|minimal-ui|browser)
  | Resolution PixelsPerInch
    -- ^ @media (resolution: Xdpi)
  | MinResolution PixelsPerInch
    -- ^ @media (min-resolution: Xdpi)
  | ColorGamut String
    -- ^ @media (color-gamut: srgb|p3|rec2020)
  | Type MediaType
    -- ^ @media screen|print|all
  | And MediaQuery MediaQuery
    -- ^ Logical AND of two queries
  | Or MediaQuery MediaQuery
    -- ^ Logical OR of two queries
  | Not MediaQuery
    -- ^ Logical NOT of a query

derive instance eqMediaQuery :: Eq MediaQuery
derive instance ordMediaQuery :: Ord MediaQuery

instance showMediaQuery :: Show MediaQuery where
  show q = "MediaQuery(" <> toCSS q <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a min-width query.
minWidth :: Pixel -> MediaQuery
minWidth = MinWidth

-- | Create a max-width query.
maxWidth :: Pixel -> MediaQuery
maxWidth = MaxWidth

-- | Create a min-height query.
minHeight :: Pixel -> MediaQuery
minHeight = MinHeight

-- | Create a max-height query.
maxHeight :: Pixel -> MediaQuery
maxHeight = MaxHeight

-- | Create an orientation query.
orientation :: ScreenOrientation -> MediaQuery
orientation = Orientation

-- | Create a prefers-color-scheme query.
prefersColorScheme :: ColorScheme -> MediaQuery
prefersColorScheme = PrefersColorScheme

-- | Create a prefers-reduced-motion query.
prefersReducedMotion :: Boolean -> MediaQuery
prefersReducedMotion = PrefersReducedMotion

-- | Create a prefers-reduced-transparency query.
prefersReducedTransparency :: Boolean -> MediaQuery
prefersReducedTransparency = PrefersReducedTransparency

-- | Create a prefers-contrast query.
prefersContrast :: Boolean -> MediaQuery
prefersContrast = PrefersContrast

-- | Create a pointer query.
pointer :: PointerType -> MediaQuery
pointer = Pointer

-- | Create an any-pointer query.
anyPointer :: PointerType -> MediaQuery
anyPointer = AnyPointer

-- | Create a hover query.
hover :: HoverCapability -> MediaQuery
hover = HoverMedia

-- | Create an any-hover query.
anyHover :: HoverCapability -> MediaQuery
anyHover = AnyHover

-- | Create a display-mode query.
displayMode :: DisplayMode -> MediaQuery
displayMode = DisplayModeQuery

-- | Create a resolution query.
resolution :: PixelsPerInch -> MediaQuery
resolution = Resolution

-- | Create a min-resolution query.
minResolution :: PixelsPerInch -> MediaQuery
minResolution = MinResolution

-- | Create a color-gamut query.
colorGamut :: String -> MediaQuery
colorGamut = ColorGamut

-- | Create a media type query.
mediaType :: MediaType -> MediaQuery
mediaType = Type

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // combinators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two queries with AND.
and :: MediaQuery -> MediaQuery -> MediaQuery
and = And

-- | Combine two queries with OR.
or :: MediaQuery -> MediaQuery -> MediaQuery
or = Or

-- | Negate a query.
not :: MediaQuery -> MediaQuery
not = Not

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mobile devices (max-width: 767px).
isMobile :: MediaQuery
isMobile = MaxWidth (Pixel 767.0)

-- | Tablet devices (768px - 1023px).
isTablet :: MediaQuery
isTablet = And (MinWidth (Pixel 768.0)) (MaxWidth (Pixel 1023.0))

-- | Desktop devices (min-width: 1024px).
isDesktop :: MediaQuery
isDesktop = MinWidth (Pixel 1024.0)

-- | Dark mode preference.
isDarkMode :: MediaQuery
isDarkMode = PrefersColorScheme Dark

-- | Light mode preference.
isLightMode :: MediaQuery
isLightMode = PrefersColorScheme Light

-- | User prefers reduced motion.
prefersReducedMotionQuery :: MediaQuery
prefersReducedMotionQuery = PrefersReducedMotion true

-- | Touch device (coarse pointer).
isTouchDevice :: MediaQuery
isTouchDevice = Pointer PointerCoarse

-- | High resolution display (min 2x).
isHighResolution :: MediaQuery
isHighResolution = MinResolution (PixelsPerInch 192.0)

-- | Print media.
isPrint :: MediaQuery
isPrint = Type Print

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert MediaQuery to CSS string.
-- |
-- | ```purescript
-- | toCSS (MinWidth (Pixel 768.0))
-- | -- "(min-width: 768px)"
-- |
-- | toCSS (And (MinWidth (Pixel 768.0)) (MaxWidth (Pixel 1023.0)))
-- | -- "(min-width: 768px) and (max-width: 1023px)"
-- | ```
toCSS :: MediaQuery -> String
toCSS (MinWidth p) = "(min-width: " <> showPx p <> ")"
toCSS (MaxWidth p) = "(max-width: " <> showPx p <> ")"
toCSS (MinHeight p) = "(min-height: " <> showPx p <> ")"
toCSS (MaxHeight p) = "(max-height: " <> showPx p <> ")"
toCSS (Orientation o) = "(orientation: " <> show o <> ")"
toCSS (PrefersColorScheme cs) = "(prefers-color-scheme: " <> show cs <> ")"
toCSS (PrefersReducedMotion true) = "(prefers-reduced-motion: reduce)"
toCSS (PrefersReducedMotion false) = "(prefers-reduced-motion: no-preference)"
toCSS (PrefersReducedTransparency true) = "(prefers-reduced-transparency: reduce)"
toCSS (PrefersReducedTransparency false) = "(prefers-reduced-transparency: no-preference)"
toCSS (PrefersContrast true) = "(prefers-contrast: more)"
toCSS (PrefersContrast false) = "(prefers-contrast: no-preference)"
toCSS (Pointer pt) = "(pointer: " <> show pt <> ")"
toCSS (AnyPointer pt) = "(any-pointer: " <> show pt <> ")"
toCSS (HoverMedia hc) = "(hover: " <> hoverToCSS hc <> ")"
toCSS (AnyHover hc) = "(any-hover: " <> hoverToCSS hc <> ")"
toCSS (DisplayModeQuery dm) = "(display-mode: " <> show dm <> ")"
toCSS (Resolution ppi) = "(resolution: " <> showDpi ppi <> ")"
toCSS (MinResolution ppi) = "(min-resolution: " <> showDpi ppi <> ")"
toCSS (ColorGamut g) = "(color-gamut: " <> g <> ")"
toCSS (Type mt) = show mt
toCSS (And q1 q2) = toCSS q1 <> " and " <> toCSS q2
toCSS (Or q1 q2) = toCSS q1 <> ", " <> toCSS q2
toCSS (Not q) = "not " <> toCSS q

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media environment for evaluating queries.
-- |
-- | Represents the current state of the user's environment.
type MediaEnvironment =
  { width :: Pixel
  , height :: Pixel
  , orientation :: ScreenOrientation
  , colorScheme :: ColorScheme
  , reducedMotion :: Boolean
  , reducedTransparency :: Boolean
  , highContrast :: Boolean
  , pointer :: PointerType
  , hover :: HoverCapability
  , displayMode :: DisplayMode
  , resolution :: PixelsPerInch
  , colorGamut :: String
  , mediaType :: MediaType
  }

-- | Default media environment (desktop, light mode).
defaultMediaEnvironment :: MediaEnvironment
defaultMediaEnvironment =
  { width: Pixel 1920.0
  , height: Pixel 1080.0
  , orientation: Landscape
  , colorScheme: Light
  , reducedMotion: false
  , reducedTransparency: false
  , highContrast: false
  , pointer: PointerFine
  , hover: Hover
  , displayMode: Browser
  , resolution: PixelsPerInch 96.0
  , colorGamut: "srgb"
  , mediaType: Screen
  }

-- | Evaluate a media query against an environment.
-- |
-- | Returns true if the query matches the environment.
matches :: MediaEnvironment -> MediaQuery -> Boolean
matches env (MinWidth p) = unwrapPixel env.width >= unwrapPixel p
matches env (MaxWidth p) = unwrapPixel env.width <= unwrapPixel p
matches env (MinHeight p) = unwrapPixel env.height >= unwrapPixel p
matches env (MaxHeight p) = unwrapPixel env.height <= unwrapPixel p
matches env (Orientation o) = env.orientation == o
matches env (PrefersColorScheme cs) = env.colorScheme == cs
matches env (PrefersReducedMotion b) = env.reducedMotion == b
matches env (PrefersReducedTransparency b) = env.reducedTransparency == b
matches env (PrefersContrast b) = env.highContrast == b
matches env (Pointer pt) = env.pointer == pt
matches env (AnyPointer pt) = env.pointer == pt
matches env (HoverMedia hc) = env.hover == hc
matches env (AnyHover hc) = env.hover == hc
matches env (DisplayModeQuery dm) = env.displayMode == dm
matches env (Resolution ppi) = unwrapPpi env.resolution == unwrapPpi ppi
matches env (MinResolution ppi) = unwrapPpi env.resolution >= unwrapPpi ppi
matches env (ColorGamut g) = env.colorGamut == g
matches env (Type mt) = env.mediaType == mt || mt == All
matches env (And q1 q2) = matches env q1 && matches env q2
matches env (Or q1 q2) = matches env q1 || matches env q2
matches env (Not q) = P.not (matches env q)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format Pixel for CSS output.
showPx :: Pixel -> String
showPx (Pixel n) = show n <> "px"

-- | Format PixelsPerInch for CSS output.
showDpi :: PixelsPerInch -> String
showDpi (PixelsPerInch n) = show n <> "dpi"

-- | Convert HoverCapability to CSS value.
hoverToCSS :: HoverCapability -> String
hoverToCSS HoverNone = "none"
hoverToCSS HoverOnDemand = "none"
hoverToCSS Hover = "hover"
