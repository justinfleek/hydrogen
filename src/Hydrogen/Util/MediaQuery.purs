-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // util // media-query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media query types.
-- |
-- | Type-safe media query representation and composition.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.MediaQuery as MQ
-- |
-- | tabletUp :: MediaQuery
-- | tabletUp = MQ.minWidth (Pixel 768.0)
-- |
-- | darkMode :: MediaQuery
-- | darkMode = MQ.isDarkMode
-- |
-- | darkTablet :: MediaQuery
-- | darkTablet = MQ.and tabletUp darkMode
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Dimension.MediaQuery
-- |
-- | ## Dependents
-- | - Responsive components
-- | - Theme switching
-- | - Accessibility preferences

module Hydrogen.Util.MediaQuery
  ( module SchemaMediaQuery
  ) where

import Hydrogen.Schema.Dimension.MediaQuery
  ( MediaQuery(MinWidth, MaxWidth, MinHeight, MaxHeight, Orientation, PrefersColorScheme, PrefersReducedMotion, PrefersReducedTransparency, PrefersContrast, Pointer, AnyPointer, HoverMedia, AnyHover, DisplayModeQuery, Resolution, MinResolution, ColorGamut, Type, And, Or, Not)
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
  , and
  , or
  , not
  , isMobile
  , isTablet
  , isDesktop
  , isDarkMode
  , isLightMode
  , prefersReducedMotionQuery
  , isTouchDevice
  , isHighResolution
  , isPrint
  , matches
  , ScreenOrientation(Portrait, Landscape)
  , ColorScheme(Light, Dark, NoPreference)
  , PointerType(PointerNone, PointerCoarse, PointerFine)
  , HoverCapability(HoverNone, HoverOnDemand, Hover)
  , DisplayMode(Fullscreen, Standalone, MinimalUI, Browser)
  , MediaType(Screen, Print, All)
  , MediaEnvironment
  , Pixel(Pixel)
  , PixelsPerInch(PixelsPerInch)
  ) as SchemaMediaQuery
