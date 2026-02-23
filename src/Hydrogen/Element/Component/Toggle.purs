-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // element // toggle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toggle — Schema-native toggle button component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Toggle buttons are used for binary or multi-selection states.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background (unpressed)  |
-- | | pressedBackgroundColor| Color      | Color.RGB                 | background (pressed)    |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | pressedTextColor      | Color      | Color.RGB                 | color (pressed)         |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.Toggle as Toggle
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Single toggle button
-- | Toggle.toggle
-- |   [ Toggle.pressed state.isBold
-- |   , Toggle.onPressedChange ToggleBold
-- |   ]
-- |   [ E.text "Bold" ]
-- |
-- | -- With brand atoms
-- | Toggle.toggle
-- |   [ Toggle.pressed state.isActive
-- |   , Toggle.pressedBackgroundColor brand.primaryColor
-- |   , Toggle.pressedTextColor brand.onPrimaryColor
-- |   ]
-- |   [ E.text "Active" ]
-- |
-- | -- Toggle group
-- | Toggle.toggleGroup [ Toggle.gap (Device.px 4.0) ]
-- |   [ Toggle.toggle [ Toggle.pressed (state.align == "left") ] [ E.text "Left" ]
-- |   , Toggle.toggle [ Toggle.pressed (state.align == "center") ] [ E.text "Center" ]
-- |   , Toggle.toggle [ Toggle.pressed (state.align == "right") ] [ E.text "Right" ]
-- |   ]
-- | ```

module Hydrogen.Element.Component.Toggle
  ( -- * Main Components
    toggle
  , toggleGroup
  
  -- * Props
  , ToggleProps
  , ToggleProp
  , GroupProps
  , GroupProp
  , defaultProps
  , defaultGroupProps
  
  -- * State Props
  , pressed
  , isDisabled
  
  -- * Color Atoms
  , backgroundColor
  , pressedBackgroundColor
  , textColor
  , pressedTextColor
  , borderColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , gap
  
  -- * Typography Atoms
  , fontSize
  , fontWeight
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onPressedChange
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // toggle props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toggle button properties
type ToggleProps msg =
  { -- State
    pressed :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , pressedBackgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , pressedTextColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onPressedChange :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ToggleProp msg = ToggleProps msg -> ToggleProps msg

-- | Default properties
defaultProps :: forall msg. ToggleProps msg
defaultProps =
  { pressed: false
  , disabled: false
  , backgroundColor: Nothing
  , pressedBackgroundColor: Nothing
  , textColor: Nothing
  , pressedTextColor: Nothing
  , borderColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , transitionDuration: Nothing
  , onPressedChange: Nothing
  , extraAttributes: []
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // group props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toggle group properties
type GroupProps msg =
  { -- Dimension atoms
    gap :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Group property modifier
type GroupProp msg = GroupProps msg -> GroupProps msg

-- | Default group properties
defaultGroupProps :: forall msg. GroupProps msg
defaultGroupProps =
  { gap: Nothing
  , extraAttributes: []
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // prop builders: state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set pressed state
pressed :: forall msg. Boolean -> ToggleProp msg
pressed p props = props { pressed = p }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> ToggleProp msg
isDisabled d props = props { disabled = d }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // prop builders: color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set background color when not pressed (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ToggleProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set background color when pressed (Color.RGB atom)
pressedBackgroundColor :: forall msg. Color.RGB -> ToggleProp msg
pressedBackgroundColor c props = props { pressedBackgroundColor = Just c }

-- | Set text color when not pressed (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ToggleProp msg
textColor c props = props { textColor = Just c }

-- | Set text color when pressed (Color.RGB atom)
pressedTextColor :: forall msg. Color.RGB -> ToggleProp msg
pressedTextColor c props = props { pressedTextColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ToggleProp msg
borderColor c props = props { borderColor = Just c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> ToggleProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ToggleProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: dimension
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set toggle height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> ToggleProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> ToggleProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> ToggleProp msg
paddingY p props = props { paddingY = Just p }

-- | Set gap between group items (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> GroupProp msg
gap g props = props { gap = Just g }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: typography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> ToggleProp msg
fontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
fontWeight :: forall msg. FontWeight.FontWeight -> ToggleProp msg
fontWeight w props = props { fontWeight = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // prop builders: motion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> ToggleProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set press change handler
onPressedChange :: forall msg. msg -> ToggleProp msg
onPressedChange handler props = props { onPressedChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: escape hatch
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ToggleProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // main component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a toggle button
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
toggle :: forall msg. Array (ToggleProp msg) -> Array (E.Element msg) -> E.Element msg
toggle propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.button_
      (buildToggleAttrs props)
      children

-- | Build toggle button attributes
buildToggleAttrs :: forall msg. ToggleProps msg -> Array (E.Attribute msg)
buildToggleAttrs props =
  let
    -- Default colors
    defaultBgColor = Color.rgb 255 255 255        -- White
    defaultPressedBgColor = Color.rgb 226 232 240  -- Light gray
    defaultTextColor = Color.rgb 71 85 105        -- Dark gray
    
    -- Current colors based on pressed state
    currentBgColor = if props.pressed
      then maybe defaultPressedBgColor (\c -> c) props.pressedBackgroundColor
      else maybe defaultBgColor (\c -> c) props.backgroundColor
    
    currentTextColor = if props.pressed
      then maybe defaultTextColor (\c -> c) props.pressedTextColor
      else maybe defaultTextColor (\c -> c) props.textColor
    
    -- Border
    borderStyle = case props.borderColor of
      Nothing -> [ E.style "border" "1px solid rgba(0, 0, 0, 0.1)" ]
      Just bc ->
        let bw = maybe "1px" show props.borderWidth
        in [ E.style "border-style" "solid"
           , E.style "border-width" bw
           , E.style "border-color" (Color.toLegacyCss bc)
           ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "6px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Height
    heightStyle = case props.height of
      Nothing -> [ E.style "height" "36px" ]
      Just h -> [ E.style "height" (show h) ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "12px" show props.paddingX
        py = maybe "6px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Transition
    transitionValue = maybe "150ms" show props.transitionDuration
    
    -- Core styles
    coreStyles =
      [ E.type_ "button"
      , E.attr "aria-pressed" (if props.pressed then "true" else "false")
      , E.disabled props.disabled
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "white-space" "nowrap"
      , E.style "background-color" (Color.toLegacyCss currentBgColor)
      , E.style "color" (Color.toLegacyCss currentTextColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> transitionValue <> " ease-out")
      , E.style "outline" "none"
      , E.style "user-select" "none"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onPressedChange of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
  in
    coreStyles 
    <> borderStyle 
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> disabledStyle 
    <> clickHandler 
    <> props.extraAttributes

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // toggle group
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a toggle group
-- |
-- | Container for multiple toggle buttons.
toggleGroup :: forall msg. Array (GroupProp msg) -> Array (E.Element msg) -> E.Element msg
toggleGroup propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    
    -- Gap
    gapValue = maybe "4px" show props.gap
  in
    E.div_
      ( [ E.role "group"
        , E.style "display" "inline-flex"
        , E.style "gap" gapValue
        ]
        <> props.extraAttributes
      )
      children
