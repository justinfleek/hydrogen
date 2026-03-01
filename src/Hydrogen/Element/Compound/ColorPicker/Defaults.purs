-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // color picker // defaults
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker Defaults — Default styling values.
-- |
-- | This module provides sensible default values for all ColorPicker styling
-- | properties, following a dark theme aesthetic.

module Hydrogen.Element.Compound.ColorPicker.Defaults
  ( -- * Color Defaults
    defaultBackgroundColor
  , defaultBorderColor
  , defaultLabelColor
  , defaultPrimaryColor
  , defaultSliderTrackColor
  
  -- * Geometry Defaults
  , defaultPreviewRadius
  , defaultPanelRadius
  
  -- * Dimension Defaults
  , defaultPadding
  , defaultGap
  , defaultBorderWidth
  , defaultPreviewHeight
  
  -- * Typography Defaults
  , defaultLabelFontSize
  , defaultLabelFontWeight
  , defaultHeaderFontSize
  , defaultHeaderFontWeight
  
  -- * Resolved Config Type
  , ResolvedConfig
  
  -- * Resolver Functions
  , getColor
  , getRadius
  , getPixel
  , getFontSize
  , getFontWeight
  ) where

import Data.Maybe (Maybe, maybe)

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default background color (dark surface)
defaultBackgroundColor :: Color.RGB
defaultBackgroundColor = Color.rgb 30 30 30

-- | Default border color (subtle)
defaultBorderColor :: Color.RGB
defaultBorderColor = Color.rgb 64 64 64

-- | Default label color (muted white)
defaultLabelColor :: Color.RGB
defaultLabelColor = Color.rgb 156 163 175

-- | Default primary color (blue)
defaultPrimaryColor :: Color.RGB
defaultPrimaryColor = Color.rgb 59 130 246

-- | Default slider track color (dark gray)
defaultSliderTrackColor :: Color.RGB
defaultSliderTrackColor = Color.rgb 64 64 64

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // geometry defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default preview border radius
defaultPreviewRadius :: Geometry.Radius
defaultPreviewRadius = Geometry.px 4.0

-- | Default panel border radius
defaultPanelRadius :: Geometry.Radius
defaultPanelRadius = Geometry.px 8.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dimension defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default padding
defaultPadding :: Device.Pixel
defaultPadding = Device.px 16.0

-- | Default gap
defaultGap :: Device.Pixel
defaultGap = Device.px 16.0

-- | Default border width
defaultBorderWidth :: Device.Pixel
defaultBorderWidth = Device.px 1.0

-- | Default preview height
defaultPreviewHeight :: Device.Pixel
defaultPreviewHeight = Device.px 64.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // typography defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default label font size (11px)
defaultLabelFontSize :: FontSize.FontSize
defaultLabelFontSize = FontSize.fontSize 11.0

-- | Default label font weight (500 = medium)
defaultLabelFontWeight :: FontWeight.FontWeight
defaultLabelFontWeight = FontWeight.medium

-- | Default header font size (12px)
defaultHeaderFontSize :: FontSize.FontSize
defaultHeaderFontSize = FontSize.fontSize 12.0

-- | Default header font weight (700 = bold)
defaultHeaderFontWeight :: FontWeight.FontWeight
defaultHeaderFontWeight = FontWeight.bold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // resolved config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resolved styling configuration (passed to render functions)
type ResolvedConfig =
  { lblColor :: Color.RGB
  , primColor :: Color.RGB
  , trkColor :: Color.RGB
  , lblFontSize :: FontSize.FontSize
  , lblFontWeight :: FontWeight.FontWeight
  , hdrFontSize :: FontSize.FontSize
  , hdrFontWeight :: FontWeight.FontWeight
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // resolver functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get effective color value with fallback
getColor :: Maybe Color.RGB -> Color.RGB -> Color.RGB
getColor maybeC fallback = maybe fallback (\c -> c) maybeC

-- | Get effective radius value with fallback
getRadius :: Maybe Geometry.Radius -> Geometry.Radius -> Geometry.Radius
getRadius maybeR fallback = maybe fallback (\r -> r) maybeR

-- | Get effective pixel value with fallback
getPixel :: Maybe Device.Pixel -> Device.Pixel -> Device.Pixel
getPixel maybeP fallback = maybe fallback (\p -> p) maybeP

-- | Get effective font size value with fallback
getFontSize :: Maybe FontSize.FontSize -> FontSize.FontSize -> FontSize.FontSize
getFontSize maybeS fallback = maybe fallback (\s -> s) maybeS

-- | Get effective font weight value with fallback
getFontWeight :: Maybe FontWeight.FontWeight -> FontWeight.FontWeight -> FontWeight.FontWeight
getFontWeight maybeW fallback = maybe fallback (\w -> w) maybeW
