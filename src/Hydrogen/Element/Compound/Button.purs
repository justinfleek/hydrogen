-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button — Pure GPU drawable button component.
-- |
-- | ## Design Philosophy
-- |
-- | This component emits **DrawCommand** arrays, NOT Element trees.
-- | No CSS. No strings. Pure bounded Schema atoms → GPU commands.
-- |
-- | The button is rendered as:
-- | - DrawRect for the background (with corner radius, fill color)
-- | - DrawWord for the label text
-- |
-- | ## Schema Atoms
-- |
-- | All visual properties are Schema atoms that flow directly to GPU:
-- | - Color.RGBA → DrawRect.fill
-- | - Geometry.Corners → DrawRect.cornerRadius  
-- | - Device.Pixel → DrawRect dimensions
-- |
-- | ## Architecture
-- |
-- | ```
-- | ButtonProps → button → Array (DrawCommand msg)
-- |                              ↓
-- |                         GPU interpreter
-- |                              ↓
-- |                         Pick buffer → msg dispatch
-- | ```

module Hydrogen.Element.Compound.Button
  ( -- * Main Component
    button
  
  -- * Types
  , ButtonProps
  , ButtonProp
  , defaultProps
  
  -- * Behavior Props
  , disabled
  , loading
  , onClick
  
  -- * Position/Size Props (required for GPU rendering)
  , x
  , y
  , width
  , height
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Typography Atoms
  , fontSize
  , fontId
  
  -- * Label
  , label
  ) where

import Prelude
  ( (<>)
  , (||)
  , (==)
  , (/)
  , (*)
  , (+)
  , (-)
  )

import Data.Array (foldl)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.String.CodeUnits (length) as String

import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.DrawCommand.Types (DrawCommand, CommandBuffer)
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.GPU.Text as Text
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button properties — pure Schema atoms for GPU rendering.
-- |
-- | Position (x, y) and size (width, height) are REQUIRED for GPU rendering.
-- | There is no layout engine — coordinates must be explicit.
type ButtonProps msg =
  { -- Behavior
    disabled :: Boolean
  , loading :: Boolean
  , onClick :: Maybe msg
  
  -- Position (required)
  , x :: Number
  , y :: Number
  
  -- Size (required)
  , width :: Number
  , height :: Number
  
  -- Color atoms
  , backgroundColor :: RGB.RGBA
  , textColor :: RGB.RGBA
  , borderColor :: Maybe RGB.RGBA
  
  -- Geometry atoms
  , borderRadius :: Radius.Corners
  , borderWidth :: Device.Pixel
  
  -- Typography atoms
  , fontSize :: Number
  , fontId :: Int
  
  -- Content
  , label :: String
  }

-- | Property modifier
type ButtonProp msg = ButtonProps msg -> ButtonProps msg

-- | Default properties with sensible fallbacks.
-- |
-- | Position defaults to origin. Size defaults to typical button dimensions.
-- | Colors default to blue button with white text.
defaultProps :: forall msg. ButtonProps msg
defaultProps =
  { disabled: false
  , loading: false
  , onClick: Nothing
  -- Position
  , x: 0.0
  , y: 0.0
  -- Size
  , width: 120.0
  , height: 40.0
  -- Colors (blue primary button)
  , backgroundColor: RGB.rgba 59 130 246 100   -- Blue
  , textColor: RGB.rgba 255 255 255 100        -- White
  , borderColor: Nothing
  -- Geometry
  , borderRadius: Radius.cornersAll (Radius.px 6.0)
  , borderWidth: Device.px 0.0
  -- Typography
  , fontSize: 14.0
  , fontId: 0
  -- Content
  , label: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set disabled state
disabled :: forall msg. Boolean -> ButtonProp msg
disabled d props = props { disabled = d }

-- | Set loading state (also disables the button)
loading :: forall msg. Boolean -> ButtonProp msg
loading l props = props { loading = l }

-- | Set click handler
onClick :: forall msg. msg -> ButtonProp msg
onClick handler props = props { onClick = Just handler }

-- | Set X position
x :: forall msg. Number -> ButtonProp msg
x val props = props { x = val }

-- | Set Y position  
y :: forall msg. Number -> ButtonProp msg
y val props = props { y = val }

-- | Set width
width :: forall msg. Number -> ButtonProp msg
width val props = props { width = val }

-- | Set height
height :: forall msg. Number -> ButtonProp msg
height val props = props { height = val }

-- | Set background color (RGBA atom)
backgroundColor :: forall msg. RGB.RGBA -> ButtonProp msg
backgroundColor c props = props { backgroundColor = c }

-- | Set text color (RGBA atom)
textColor :: forall msg. RGB.RGBA -> ButtonProp msg
textColor c props = props { textColor = c }

-- | Set border color (RGBA atom)
borderColor :: forall msg. RGB.RGBA -> ButtonProp msg
borderColor c props = props { borderColor = Just c }

-- | Set corner radius (Corners atom)
borderRadius :: forall msg. Radius.Corners -> ButtonProp msg
borderRadius r props = props { borderRadius = r }

-- | Set border width (Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ButtonProp msg
borderWidth w props = props { borderWidth = w }

-- | Set font size in pixels
fontSize :: forall msg. Number -> ButtonProp msg
fontSize s props = props { fontSize = s }

-- | Set font ID (references loaded font atlas)
fontId :: forall msg. Int -> ButtonProp msg
fontId id props = props { fontId = id }

-- | Set button label text
label :: forall msg. String -> ButtonProp msg
label txt props = props { label = txt }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a button as GPU draw commands.
-- |
-- | Returns an array of DrawCommands ready for the GPU interpreter:
-- | - DrawRect for the background
-- | - Text commands for the label
-- |
-- | The button is interactive via pick buffer when onClick is set.
button :: forall msg. Array (ButtonProp msg) -> CommandBuffer msg
button propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isDisabled = props.disabled || props.loading
    
    -- Adjust fill opacity if disabled
    fillColor = 
      if isDisabled
        then applyDisabledOpacity props.backgroundColor
        else props.backgroundColor
    
    -- Background rectangle
    bgRect = DC.drawRect
      { x: Coord.screenX props.x
      , y: Coord.screenY props.y
      , width: Coord.pixelWidth props.width
      , height: Coord.pixelHeight props.height
      , fill: fillColor
      , cornerRadius: props.borderRadius
      , depth: Coord.depthValue 0.0
      , pickId: Nothing  -- Assigned by runtime if onClick present
      , onClick: if isDisabled then Nothing else props.onClick
      }
    
    -- Text label (centered in button)
    labelCommands = 
      if props.label == ""
        then []
        else buildLabelCommands props
  in
    [ bgRect ] <> labelCommands

-- | Build text commands for the button label.
-- |
-- | Centers text within the button bounds.
buildLabelCommands :: forall msg. ButtonProps msg -> CommandBuffer msg
buildLabelCommands props =
  let
    -- Simple centering: offset from button position
    -- Real centering requires text measurement from font atlas
    textX = props.x + props.width / 2.0 - (textWidth / 2.0)
    textY = props.y + props.height / 2.0 + (props.fontSize / 3.0)  -- Baseline adjust
    
    -- Approximate text width (proper measurement needs font metrics)
    textWidth = props.fontSize * 0.6 * Int.toNumber (String.length props.label)
    
    fontConfig = Text.fontConfig props.fontId props.fontSize
  in
    Text.textToCommands fontConfig Text.emptyAtlas textX textY props.label

-- | Apply 50% opacity for disabled state.
applyDisabledOpacity :: RGB.RGBA -> RGB.RGBA
applyDisabledOpacity color =
  let rec = RGB.rgbaToRecord color
  in RGB.rgba rec.r rec.g rec.b (rec.a / 2)
