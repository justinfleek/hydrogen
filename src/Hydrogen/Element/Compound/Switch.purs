-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // switch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Switch — Pure Element.Core rendering for toggle switch components.
-- |
-- | ## Design Philosophy
-- |
-- | This module emits **pure Element data**, not HTML/CSS.
-- | No strings. No CSS properties. Just bounded Schema atoms
-- | composed into Element.Core shapes (Rectangle, Ellipse, Group).
-- |
-- | ## Architecture
-- |
-- | ```
-- | SwitchConfig (Schema atoms)
-- |    ↓
-- | This module (render functions)
-- |    ↓
-- | Element.Core (Rectangle, Ellipse, Group)
-- |    ↓
-- | Flatten → DrawCommand → Binary → GPU
-- | ```
-- |
-- | ## Compositor Model
-- |
-- | A switch renders as:
-- | - Track: Rectangle with pill shape (full corner radius)
-- | - Thumb: Ellipse (circle) positioned left or right based on state
-- |
-- | Composed in a Group with the track as background, thumb on top.

module Hydrogen.Element.Compound.Switch
  ( -- * Main Render Function
    renderSwitch
  
  -- * Configuration
  , SwitchConfig
  , defaultConfig
  
  -- * Config Builders
  , withChecked
  , withDisabled
  , withTrackColorOn
  , withTrackColorOff
  , withThumbColor
  , withWidth
  , withHeight
  , withThumbSize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (-)
  , (/)
  , (*) 
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Element.Core — pure data shapes
import Hydrogen.Element.Core
  ( Element
  , rectangle
  , ellipse
  , group
  )

-- Schema atoms: Geometry — Rectangle and Ellipse
import Hydrogen.Schema.Geometry.Shape.Primitives
  ( RectangleShape
  , rectangleShape
  , EllipseShape
  , circleShape
  )
import Hydrogen.Schema.Geometry.Shape.Types
  ( PixelPoint2D
  , pixelPoint2D
  )
import Hydrogen.Schema.Geometry.Radius
  ( Radius
  , cornersAll
  , full
  )

-- Schema atoms: Dimension
import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )

-- Schema atoms: Surface
import Hydrogen.Schema.Surface.Fill
  ( fillSolid
  )

-- Schema atoms: Color
import Hydrogen.Schema.Color.RGB
  ( RGB
  , rgb
  )
import Hydrogen.Schema.Color.Opacity
  ( Opacity
  , opacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // config type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for rendering a switch toggle.
-- |
-- | All fields use bounded Schema atoms. No strings. No CSS.
type SwitchConfig =
  { -- State
    checked :: Boolean
  , disabled :: Boolean
  
  -- Colors
  , trackColorOn :: RGB        -- Track fill when ON
  , trackColorOff :: RGB       -- Track fill when OFF
  , thumbColor :: RGB          -- Thumb fill
  
  -- Geometry
  , width :: Pixel             -- Track width
  , height :: Pixel            -- Track height
  , thumbSize :: Pixel         -- Thumb diameter
  
  -- Position (center-based for the track)
  , center :: PixelPoint2D
  }

-- | Default switch configuration.
-- |
-- | Uses common defaults:
-- | - 44px × 24px track
-- | - 20px thumb
-- | - Blue ON color
-- | - Gray OFF color
-- | - White thumb
defaultConfig :: SwitchConfig
defaultConfig =
  { checked: false
  , disabled: false
  , trackColorOn: rgb 59 130 246    -- Blue
  , trackColorOff: rgb 203 213 225  -- Gray
  , thumbColor: rgb 255 255 255     -- White
  , width: Pixel 44.0
  , height: Pixel 24.0
  , thumbSize: Pixel 20.0
  , center: pixelPoint2D (Pixel 0.0) (Pixel 0.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state
withChecked :: Boolean -> SwitchConfig -> SwitchConfig
withChecked c cfg = cfg { checked = c }

-- | Set disabled state
withDisabled :: Boolean -> SwitchConfig -> SwitchConfig
withDisabled d cfg = cfg { disabled = d }

-- | Set track color when ON
withTrackColorOn :: RGB -> SwitchConfig -> SwitchConfig
withTrackColorOn color cfg = cfg { trackColorOn = color }

-- | Set track color when OFF
withTrackColorOff :: RGB -> SwitchConfig -> SwitchConfig
withTrackColorOff color cfg = cfg { trackColorOff = color }

-- | Set thumb color
withThumbColor :: RGB -> SwitchConfig -> SwitchConfig
withThumbColor color cfg = cfg { thumbColor = color }

-- | Set track width
withWidth :: Pixel -> SwitchConfig -> SwitchConfig
withWidth w cfg = cfg { width = w }

-- | Set track height
withHeight :: Pixel -> SwitchConfig -> SwitchConfig
withHeight h cfg = cfg { height = h }

-- | Set thumb size (diameter)
withThumbSize :: Pixel -> SwitchConfig -> SwitchConfig
withThumbSize s cfg = cfg { thumbSize = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a switch as pure Element.Core data.
-- |
-- | Returns a Group containing:
-- | - Track (rounded rectangle / pill shape)
-- | - Thumb (circle positioned based on checked state)
-- |
-- | ## Opacity
-- |
-- | When disabled, opacity is reduced to 50%.
-- | Otherwise full opacity (100%).
renderSwitch :: SwitchConfig -> Element
renderSwitch cfg =
  let
    -- Track color based on state
    trackColor = if cfg.checked
      then cfg.trackColorOn
      else cfg.trackColorOff
    
    -- Overall opacity (reduced when disabled)
    switchOpacity :: Opacity
    switchOpacity = if cfg.disabled
      then opacity 50
      else opacity 100
    
    -- Track element
    trackElement :: Element
    trackElement = renderTrack cfg trackColor switchOpacity
    
    -- Thumb element
    thumbElement :: Element
    thumbElement = renderThumb cfg switchOpacity
  in
    group [ trackElement, thumbElement ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // track
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the track (pill-shaped rectangle).
renderTrack :: SwitchConfig -> RGB -> Opacity -> Element
renderTrack cfg trackColor trackOpacity =
  let
    -- Track shape (pill = full corner radius)
    trackShape :: RectangleShape
    trackShape = rectangleShape
      cfg.center
      cfg.width
      cfg.height
      (cornersAll full)
  in
    rectangle
      { shape: trackShape
      , fill: fillSolid trackColor
      , stroke: Nothing
      , opacity: trackOpacity
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // thumb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the thumb (circle).
-- |
-- | Thumb position:
-- | - OFF: left side of track
-- | - ON: right side of track
-- |
-- | The thumb has a small padding from the track edges.
renderThumb :: SwitchConfig -> Opacity -> Element
renderThumb cfg thumbOpacity =
  let
    -- Extract dimensions
    (Pixel trackW) = cfg.width
    (Pixel trackH) = cfg.height
    (Pixel thumbD) = cfg.thumbSize
    
    -- Center of track
    (Pixel cx) = case cfg.center of
      { x: Pixel px_, y: _ } -> Pixel px_
    (Pixel cy) = case cfg.center of
      { x: _, y: Pixel py } -> Pixel py
    
    -- Thumb radius
    thumbRadius = Pixel (thumbD / 2.0)
    
    -- Padding from track edge
    padding = (trackH - thumbD) / 2.0
    
    -- Calculate thumb center X based on state
    -- OFF: left edge + padding + radius
    -- ON: right edge - padding - radius
    thumbCenterX = if cfg.checked
      then cx + (trackW / 2.0) - padding - (thumbD / 2.0)
      else cx - (trackW / 2.0) + padding + (thumbD / 2.0)
    
    -- Thumb center point
    thumbCenter = pixelPoint2D (Pixel thumbCenterX) (Pixel cy)
    
    -- Thumb shape (circle)
    thumbShape :: EllipseShape
    thumbShape = circleShape thumbCenter thumbRadius
  in
    ellipse
      { shape: thumbShape
      , fill: fillSolid cfg.thumbColor
      , stroke: Nothing
      , opacity: thumbOpacity
      }
