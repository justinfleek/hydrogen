-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // check-box
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Checkbox — Pure Element.Core rendering for checkbox components.
-- |
-- | ## Design Philosophy
-- |
-- | This module emits **pure Element data**, not HTML/CSS.
-- | No strings. No CSS properties. Just bounded Schema atoms
-- | composed into Element.Core shapes (Rectangle, Path, Group).
-- |
-- | ## Architecture
-- |
-- | ```
-- | CheckboxConfig (Schema atoms)
-- |    ↓
-- | This module (render functions)
-- |    ↓
-- | Element.Core (Rectangle, Path, Group)
-- |    ↓
-- | Flatten → DrawCommand → Binary → GPU
-- | ```
-- |
-- | ## Compositor Model
-- |
-- | A checkbox renders as:
-- | - Box: Rectangle with fill (varies by checked state) and stroke
-- | - Checkmark: Path (only when checked)
-- |
-- | Composed in a Group with the box as background, checkmark on top.

module Hydrogen.Element.Compound.Checkbox
  ( -- * Main Render Function
    renderCheckbox
  
  -- * Configuration
  , CheckboxConfig
  , defaultConfig
  
  -- * Config Builders
  , withChecked
  , withDisabled
  , withBackgroundColor
  , withBorderColor
  , withCheckColor
  , withSize
  , withBorderRadius
  , withBorderWidth
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
  , path
  , group
  , empty
  )

-- Schema atoms: Geometry — Path
import Hydrogen.Schema.Geometry.Shape
  ( PathShape
  , openPath
  )
import Hydrogen.Schema.Geometry.Shape.Types
  ( PixelPoint2D
  , pixelPoint2D
  , PathCommand(MoveTo, LineTo)
  )
import Hydrogen.Schema.Geometry.Shape.Primitives
  ( RectangleShape
  , rectangleShape
  )
import Hydrogen.Schema.Geometry.Radius
  ( Corners
  , Radius
  , cornersAll
  , px
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

-- | Configuration for rendering a checkbox.
-- |
-- | All fields use bounded Schema atoms. No strings. No CSS.
type CheckboxConfig =
  { -- State
    checked :: Boolean
  , disabled :: Boolean
  
  -- Colors
  , backgroundColor :: RGB      -- Fill when checked
  , uncheckedColor :: RGB       -- Fill when unchecked
  , borderColor :: RGB          -- Border color
  , checkColor :: RGB           -- Checkmark color
  
  -- Geometry
  , size :: Pixel               -- Width and height
  , borderRadius :: Radius      -- Corner radius (applied to all corners)
  , borderWidth :: StrokeWidth  -- Border thickness
  
  -- Position (center-based)
  , center :: PixelPoint2D
  }

-- | Default checkbox configuration.
-- |
-- | Uses common defaults:
-- | - 18px size
-- | - 4px border radius
-- | - 2px border
-- | - Blue checked background
-- | - Gray border
-- | - White checkmark
defaultConfig :: CheckboxConfig
defaultConfig =
  { checked: false
  , disabled: false
  , backgroundColor: rgb 59 130 246    -- Blue
  , uncheckedColor: rgb 255 255 255    -- White
  , borderColor: rgb 203 213 225       -- Gray
  , checkColor: rgb 255 255 255        -- White
  , size: Pixel 18.0
  , borderRadius: px 4.0
  , borderWidth: strokeWidth 2.0
  , center: pixelPoint2D (Pixel 0.0) (Pixel 0.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state
withChecked :: Boolean -> CheckboxConfig -> CheckboxConfig
withChecked c cfg = cfg { checked = c }

-- | Set disabled state
withDisabled :: Boolean -> CheckboxConfig -> CheckboxConfig
withDisabled d cfg = cfg { disabled = d }

-- | Set background color (when checked)
withBackgroundColor :: RGB -> CheckboxConfig -> CheckboxConfig
withBackgroundColor color cfg = cfg { backgroundColor = color }

-- | Set border color
withBorderColor :: RGB -> CheckboxConfig -> CheckboxConfig
withBorderColor color cfg = cfg { borderColor = color }

-- | Set checkmark color
withCheckColor :: RGB -> CheckboxConfig -> CheckboxConfig
withCheckColor color cfg = cfg { checkColor = color }

-- | Set checkbox size
withSize :: Pixel -> CheckboxConfig -> CheckboxConfig
withSize s cfg = cfg { size = s }

-- | Set border radius
withBorderRadius :: Radius -> CheckboxConfig -> CheckboxConfig
withBorderRadius r cfg = cfg { borderRadius = r }

-- | Set border width
withBorderWidth :: StrokeWidth -> CheckboxConfig -> CheckboxConfig
withBorderWidth w cfg = cfg { borderWidth = w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a checkbox as pure Element.Core data.
-- |
-- | Returns a Group containing:
-- | - Background rectangle with fill and stroke
-- | - Checkmark path (only when checked)
-- |
-- | ## Opacity
-- |
-- | When disabled, opacity is reduced to 50%.
-- | Otherwise full opacity (100%).
renderCheckbox :: CheckboxConfig -> Element
renderCheckbox cfg =
  let
    -- Determine fill based on checked state
    boxFill = if cfg.checked
      then fillSolid cfg.backgroundColor
      else fillSolid cfg.uncheckedColor
    
    -- Border color changes when checked
    strokeColor = if cfg.checked
      then cfg.backgroundColor
      else cfg.borderColor
    
    -- Build box shape (convert single Radius to Corners)
    boxShape :: RectangleShape
    boxShape = rectangleShape
      cfg.center
      cfg.size
      cfg.size
      (cornersAll cfg.borderRadius)
    
    -- Build stroke spec
    boxStroke :: StrokeSpec
    boxStroke = stroke cfg.borderWidth (fillSolid strokeColor)
    
    -- Overall opacity (reduced when disabled)
    boxOpacity :: Opacity
    boxOpacity = if cfg.disabled
      then opacity 50
      else opacity 100
    
    -- Background rectangle
    boxElement :: Element
    boxElement = rectangle
      { shape: boxShape
      , fill: boxFill
      , stroke: Just boxStroke
      , opacity: boxOpacity
      }
    
    -- Checkmark element (only when checked)
    checkElement :: Element
    checkElement = if cfg.checked
      then renderCheckmark cfg
      else empty
  in
    group [ boxElement, checkElement ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // checkmark
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the checkmark path.
-- |
-- | The checkmark is a simple "✓" shape scaled to fit within the box.
-- | Rendered as a Path with two line segments.
renderCheckmark :: CheckboxConfig -> Element
renderCheckmark cfg =
  let
    -- Extract size for calculations
    (Pixel sizeN) = cfg.size
    
    -- Checkmark is inset from edges
    inset = sizeN * 0.2
    innerSize = sizeN - (inset * 2.0)
    
    -- Center offset
    (Pixel cx) = case cfg.center of
      p -> case p of
        { x: Pixel px_, y: _ } -> Pixel px_
    (Pixel cy) = case cfg.center of
      p -> case p of
        { x: _, y: Pixel py } -> Pixel py
    
    -- Calculate checkmark points relative to center
    -- The checkmark "✓" has 3 points:
    -- - Start: left-middle
    -- - Middle: bottom-center (the "V" bottom)
    -- - End: top-right
    startX = cx - (innerSize * 0.3)
    startY = cy
    
    midX = cx - (innerSize * 0.05)
    midY = cy + (innerSize * 0.25)
    
    endX = cx + (innerSize * 0.35)
    endY = cy - (innerSize * 0.25)
    
    -- Build points
    p1 = pixelPoint2D (Pixel startX) (Pixel startY)
    p2 = pixelPoint2D (Pixel midX) (Pixel midY)
    p3 = pixelPoint2D (Pixel endX) (Pixel endY)
    
    -- Path commands
    pathCommands = 
      [ MoveTo p1
      , LineTo p2
      , LineTo p3
      ]
    
    -- Build open path (not closed)
    checkPath :: PathShape
    checkPath = openPath pathCommands
    
    -- Stroke for the checkmark
    checkStroke :: StrokeSpec
    checkStroke = stroke 
      (strokeWidth 2.0) 
      (fillSolid cfg.checkColor)
    
    -- Opacity (reduced when disabled)
    checkOpacity :: Opacity
    checkOpacity = if cfg.disabled
      then opacity 50
      else opacity 100
  in
    path
      { shape: checkPath
      , fill: fillNone
      , stroke: Just checkStroke
      , opacity: checkOpacity
      }
