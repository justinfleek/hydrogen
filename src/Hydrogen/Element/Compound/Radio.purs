-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // radio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radio — Pure Element.Core rendering for radio button components.
-- |
-- | ## Design Philosophy
-- |
-- | This module emits **pure Element data**, not HTML/CSS.
-- | No strings. No CSS properties. Just bounded Schema atoms
-- | composed into Element.Core shapes (Ellipse, Group).
-- |
-- | ## Architecture
-- |
-- | ```
-- | RadioConfig (Schema atoms)
-- |    ↓
-- | This module (render functions)
-- |    ↓
-- | Element.Core (Ellipse, Group)
-- |    ↓
-- | Flatten → DrawCommand → Binary → GPU
-- | ```
-- |
-- | ## Compositor Model
-- |
-- | A radio button renders as:
-- | - Outer ring: Ellipse with stroke (circle)
-- | - Inner dot: Ellipse with fill (only when checked)
-- |
-- | Composed in a Group with the ring as background, dot on top.

module Hydrogen.Element.Compound.Radio
  ( -- * Main Render Function
    renderRadio
  
  -- * Configuration
  , RadioConfig
  , defaultConfig
  
  -- * Config Builders
  , withChecked
  , withDisabled
  , withSelectedColor
  , withBorderColor
  , withSize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (*)
  , (/)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Element.Core — pure data shapes
import Hydrogen.Element.Core
  ( Element
  , ellipse
  , group
  , empty
  )

-- Schema atoms: Geometry — Ellipse
import Hydrogen.Schema.Geometry.Shape.Primitives
  ( EllipseShape
  , circleShape
  )
import Hydrogen.Schema.Geometry.Shape.Types
  ( PixelPoint2D
  , pixelPoint2D
  )

-- Schema atoms: Dimension
import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )
import Hydrogen.Schema.Dimension.Stroke
  ( StrokeWidth
  , strokeWidth
  )

-- Schema atoms: Surface
import Hydrogen.Schema.Surface.Fill
  ( Fill
  , fillSolid
  , fillNone
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

-- Element.Core stroke
import Hydrogen.Element.Core.Stroke
  ( StrokeSpec
  , stroke
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // config type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for rendering a radio button.
-- |
-- | All fields use bounded Schema atoms. No strings. No CSS.
type RadioConfig =
  { -- State
    checked :: Boolean
  , disabled :: Boolean
  
  -- Colors
  , selectedColor :: RGB       -- Fill color when selected
  , borderColor :: RGB         -- Border/stroke color
  
  -- Geometry
  , size :: Pixel              -- Diameter of the radio button
  , borderWidth :: StrokeWidth -- Border thickness
  
  -- Position (center-based)
  , center :: PixelPoint2D
  }

-- | Default radio configuration.
-- |
-- | Uses common defaults:
-- | - 18px diameter
-- | - 2px border
-- | - Blue selected color
-- | - Gray border
defaultConfig :: RadioConfig
defaultConfig =
  { checked: false
  , disabled: false
  , selectedColor: rgb 59 130 246    -- Blue
  , borderColor: rgb 203 213 225     -- Gray
  , size: Pixel 18.0
  , borderWidth: strokeWidth 2.0
  , center: pixelPoint2D (Pixel 0.0) (Pixel 0.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state
withChecked :: Boolean -> RadioConfig -> RadioConfig
withChecked c cfg = cfg { checked = c }

-- | Set disabled state
withDisabled :: Boolean -> RadioConfig -> RadioConfig
withDisabled d cfg = cfg { disabled = d }

-- | Set selected/fill color
withSelectedColor :: RGB -> RadioConfig -> RadioConfig
withSelectedColor color cfg = cfg { selectedColor = color }

-- | Set border color
withBorderColor :: RGB -> RadioConfig -> RadioConfig
withBorderColor color cfg = cfg { borderColor = color }

-- | Set radio size (diameter)
withSize :: Pixel -> RadioConfig -> RadioConfig
withSize s cfg = cfg { size = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a radio button as pure Element.Core data.
-- |
-- | Returns a Group containing:
-- | - Outer circle (ring) with stroke
-- | - Inner dot (only when checked)
-- |
-- | ## Opacity
-- |
-- | When disabled, opacity is reduced to 50%.
-- | Otherwise full opacity (100%).
renderRadio :: RadioConfig -> Element
renderRadio cfg =
  let
    -- Calculate radius from diameter
    (Pixel diameter) = cfg.size
    radius = Pixel (diameter / 2.0)
    
    -- Border color changes when checked
    strokeColor = if cfg.checked
      then cfg.selectedColor
      else cfg.borderColor
    
    -- Outer ring shape (circle)
    ringShape :: EllipseShape
    ringShape = circleShape cfg.center radius
    
    -- Ring stroke
    ringStroke :: StrokeSpec
    ringStroke = stroke cfg.borderWidth (fillSolid strokeColor)
    
    -- Overall opacity (reduced when disabled)
    ringOpacity :: Opacity
    ringOpacity = if cfg.disabled
      then opacity 50
      else opacity 100
    
    -- Outer ring element (transparent fill, colored stroke)
    ringElement :: Element
    ringElement = ellipse
      { shape: ringShape
      , fill: fillNone
      , stroke: Just ringStroke
      , opacity: ringOpacity
      }
    
    -- Inner dot element (only when checked)
    dotElement :: Element
    dotElement = if cfg.checked
      then renderDot cfg
      else empty
  in
    group [ ringElement, dotElement ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // inner dot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the inner dot (for checked state).
-- |
-- | The dot is a smaller filled circle centered within the radio.
-- | Approximately 55% of the outer diameter.
renderDot :: RadioConfig -> Element
renderDot cfg =
  let
    -- Inner dot is ~55% of outer diameter
    (Pixel diameter) = cfg.size
    dotRadius = Pixel (diameter * 0.275)
    
    -- Dot shape (circle at same center)
    dotShape :: EllipseShape
    dotShape = circleShape cfg.center dotRadius
    
    -- Dot fill
    dotFill :: Fill
    dotFill = fillSolid cfg.selectedColor
    
    -- Opacity (reduced when disabled)
    dotOpacity :: Opacity
    dotOpacity = if cfg.disabled
      then opacity 50
      else opacity 100
  in
    ellipse
      { shape: dotShape
      , fill: dotFill
      , stroke: Nothing
      , opacity: dotOpacity
      }
