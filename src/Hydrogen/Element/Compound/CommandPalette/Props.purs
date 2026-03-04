-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // command-palette // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CommandPalette Props — Property builder functions for CommandPalette.
-- |
-- | Each function takes a Schema atom and returns a property modifier.
-- | This allows composable configuration via the builder pattern.

module Hydrogen.Element.Compound.CommandPalette.Props
  ( -- * Content Props
    commands
  , groups
  , placeholder
  , emptyMessage
  , paletteOpen
  , paletteQuery
  , paletteHighlightedIndex
  
  -- * Accessibility Props
  , paletteAriaLabel
  
  -- * Overlay Atoms
  , overlayColor
  , overlayOpacity
  
  -- * Panel Atoms
  , backgroundColor
  , borderColor
  
  -- * Input Atoms
  , inputBackgroundColor
  , inputTextColor
  , inputPlaceholderColor
  , inputBorderColor
  
  -- * Item Atoms
  , itemTextColor
  , itemDescriptionColor
  , itemShortcutColor
  , itemHighlightedBackgroundColor
  , itemHighlightedTextColor
  , itemDisabledColor
  
  -- * Group Atoms
  , groupHeaderColor
  , groupBorderColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  , panelWidth
  , panelMaxHeight
  , itemHeight
  , itemPaddingX
  , itemPaddingY
  , inputHeight
  , inputPaddingX
  
  -- * Typography Atoms
  , inputFontSize
  , itemFontSize
  , descriptionFontSize
  , shortcutFontSize
  , groupHeaderFontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onQueryChange
  , onSelect
  , onClose
  , onHighlightChange
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude ((<>))

import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.CommandPalette.Types
  ( CommandPaletteProp
  , CommandItem
  , CommandGroup
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the list of commands
commands :: forall msg. Array (CommandItem msg) -> CommandPaletteProp msg
commands cs props = props { commands = cs }

-- | Set the command groups
groups :: forall msg. Array (CommandGroup msg) -> CommandPaletteProp msg
groups gs props = props { groups = gs }

-- | Set placeholder text for search input
placeholder :: forall msg. String -> CommandPaletteProp msg
placeholder p props = props { placeholder = p }

-- | Set message shown when no commands match
emptyMessage :: forall msg. String -> CommandPaletteProp msg
emptyMessage m props = props { emptyMessage = m }

-- | Set whether the palette is open
paletteOpen :: forall msg. Boolean -> CommandPaletteProp msg
paletteOpen o props = props { isOpen = o }

-- | Set current search query
paletteQuery :: forall msg. String -> CommandPaletteProp msg
paletteQuery q props = props { query = q }

-- | Set currently highlighted item index
paletteHighlightedIndex :: forall msg. Int -> CommandPaletteProp msg
paletteHighlightedIndex i props = props { highlightedIndex = i }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set aria-label for the palette
paletteAriaLabel :: forall msg. String -> CommandPaletteProp msg
paletteAriaLabel l props = props { ariaLabel = Just l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set overlay background color (Color.RGB atom)
overlayColor :: forall msg. Color.RGB -> CommandPaletteProp msg
overlayColor c props = props { overlayColor = Just c }

-- | Set overlay opacity (0.0 to 1.0)
overlayOpacity :: forall msg. Number -> CommandPaletteProp msg
overlayOpacity o props = props { overlayOpacity = Just o }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: panel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set panel background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> CommandPaletteProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set panel border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> CommandPaletteProp msg
borderColor c props = props { borderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: input
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input background color (Color.RGB atom)
inputBackgroundColor :: forall msg. Color.RGB -> CommandPaletteProp msg
inputBackgroundColor c props = props { inputBackgroundColor = Just c }

-- | Set input text color (Color.RGB atom)
inputTextColor :: forall msg. Color.RGB -> CommandPaletteProp msg
inputTextColor c props = props { inputTextColor = Just c }

-- | Set input placeholder color (Color.RGB atom)
inputPlaceholderColor :: forall msg. Color.RGB -> CommandPaletteProp msg
inputPlaceholderColor c props = props { inputPlaceholderColor = Just c }

-- | Set input border color (Color.RGB atom)
inputBorderColor :: forall msg. Color.RGB -> CommandPaletteProp msg
inputBorderColor c props = props { inputBorderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // prop builders: item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set item text color (Color.RGB atom)
itemTextColor :: forall msg. Color.RGB -> CommandPaletteProp msg
itemTextColor c props = props { itemTextColor = Just c }

-- | Set item description color (Color.RGB atom)
itemDescriptionColor :: forall msg. Color.RGB -> CommandPaletteProp msg
itemDescriptionColor c props = props { itemDescriptionColor = Just c }

-- | Set item keyboard shortcut color (Color.RGB atom)
itemShortcutColor :: forall msg. Color.RGB -> CommandPaletteProp msg
itemShortcutColor c props = props { itemShortcutColor = Just c }

-- | Set highlighted item background color (Color.RGB atom)
itemHighlightedBackgroundColor :: forall msg. Color.RGB -> CommandPaletteProp msg
itemHighlightedBackgroundColor c props = props { itemHighlightedBackgroundColor = Just c }

-- | Set highlighted item text color (Color.RGB atom)
itemHighlightedTextColor :: forall msg. Color.RGB -> CommandPaletteProp msg
itemHighlightedTextColor c props = props { itemHighlightedTextColor = Just c }

-- | Set disabled item color (Color.RGB atom)
itemDisabledColor :: forall msg. Color.RGB -> CommandPaletteProp msg
itemDisabledColor c props = props { itemDisabledColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set group header text color (Color.RGB atom)
groupHeaderColor :: forall msg. Color.RGB -> CommandPaletteProp msg
groupHeaderColor c props = props { groupHeaderColor = Just c }

-- | Set group separator border color (Color.RGB atom)
groupBorderColor :: forall msg. Color.RGB -> CommandPaletteProp msg
groupBorderColor c props = props { groupBorderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set panel border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> CommandPaletteProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set panel border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> CommandPaletteProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set panel width (Device.Pixel atom)
panelWidth :: forall msg. Device.Pixel -> CommandPaletteProp msg
panelWidth w props = props { panelWidth = Just w }

-- | Set panel max height (Device.Pixel atom)
panelMaxHeight :: forall msg. Device.Pixel -> CommandPaletteProp msg
panelMaxHeight h props = props { panelMaxHeight = Just h }

-- | Set item height (Device.Pixel atom)
itemHeight :: forall msg. Device.Pixel -> CommandPaletteProp msg
itemHeight h props = props { itemHeight = Just h }

-- | Set item horizontal padding (Device.Pixel atom)
itemPaddingX :: forall msg. Device.Pixel -> CommandPaletteProp msg
itemPaddingX p props = props { itemPaddingX = Just p }

-- | Set item vertical padding (Device.Pixel atom)
itemPaddingY :: forall msg. Device.Pixel -> CommandPaletteProp msg
itemPaddingY p props = props { itemPaddingY = Just p }

-- | Set input height (Device.Pixel atom)
inputHeight :: forall msg. Device.Pixel -> CommandPaletteProp msg
inputHeight h props = props { inputHeight = Just h }

-- | Set input horizontal padding (Device.Pixel atom)
inputPaddingX :: forall msg. Device.Pixel -> CommandPaletteProp msg
inputPaddingX p props = props { inputPaddingX = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input font size (FontSize atom)
inputFontSize :: forall msg. FontSize.FontSize -> CommandPaletteProp msg
inputFontSize s props = props { inputFontSize = Just s }

-- | Set item font size (FontSize atom)
itemFontSize :: forall msg. FontSize.FontSize -> CommandPaletteProp msg
itemFontSize s props = props { itemFontSize = Just s }

-- | Set description font size (FontSize atom)
descriptionFontSize :: forall msg. FontSize.FontSize -> CommandPaletteProp msg
descriptionFontSize s props = props { descriptionFontSize = Just s }

-- | Set keyboard shortcut font size (FontSize atom)
shortcutFontSize :: forall msg. FontSize.FontSize -> CommandPaletteProp msg
shortcutFontSize s props = props { shortcutFontSize = Just s }

-- | Set group header font size (FontSize atom)
groupHeaderFontSize :: forall msg. FontSize.FontSize -> CommandPaletteProp msg
groupHeaderFontSize s props = props { groupHeaderFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> CommandPaletteProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set query change handler
-- |
-- | Called when the search input value changes.
onQueryChange :: forall msg. (String -> msg) -> CommandPaletteProp msg
onQueryChange handler props = props { onQueryChange = Just handler }

-- | Set selection handler
-- |
-- | Called when a command is selected (via click or Enter).
onSelect :: forall msg. (CommandItem msg -> msg) -> CommandPaletteProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set close handler
-- |
-- | Called when the palette should close (Escape key or overlay click).
onClose :: forall msg. msg -> CommandPaletteProp msg
onClose handler props = props { onClose = Just handler }

-- | Set highlight change handler
-- |
-- | Called when keyboard navigation changes the highlighted item.
onHighlightChange :: forall msg. (Int -> msg) -> CommandPaletteProp msg
onHighlightChange handler props = props { onHighlightChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> CommandPaletteProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
