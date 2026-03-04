-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // command-palette // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CommandPalette Types — Core type definitions for the command palette.
-- |
-- | The command palette is a searchable list of commands that can be triggered
-- | by keyboard shortcuts or selection. It follows the same design philosophy
-- | as all Hydrogen compounds:
-- |
-- | - All visual properties accept concrete Schema atoms
-- | - `Maybe` indicates optional — `Nothing` means inherit from context
-- | - No hardcoded CSS values
-- | - Pure data — renders through any target (DOM, WebGPU, Static)

module Hydrogen.Element.Compound.CommandPalette.Types
  ( -- * Command Types
    CommandId
  , CommandItem
  , CommandGroup
  
  -- * State Types
  , CommandPaletteState
  , initialState
  
  -- * Props Types
  , CommandPaletteProps
  , CommandPaletteProp
  
  -- * Defaults
  , defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Gestural.Input.Shortcut (Shortcut)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // command types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a command
-- |
-- | Used for selection tracking and keyboard navigation.
type CommandId = String

-- | A single command item in the palette
-- |
-- | Commands can have:
-- | - A label displayed to the user
-- | - An optional description for additional context
-- | - An optional keyboard shortcut displayed alongside
-- | - An optional icon (as Element)
-- | - An optional group for categorization
-- | - A disabled state
type CommandItem msg =
  { id :: CommandId
  , label :: String
  , description :: Maybe String
  , shortcut :: Maybe Shortcut
  , icon :: Maybe (E.Element msg)
  , group :: Maybe String
  , disabled :: Boolean
  , action :: msg
  }

-- | A group of related commands
-- |
-- | Groups are displayed with a header and contain multiple commands.
-- | The `priority` field controls display order (lower = higher priority).
type CommandGroup msg =
  { id :: String
  , label :: String
  , commands :: Array (CommandItem msg)
  , priority :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // state types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Internal state for the command palette
-- |
-- | This state is managed by the component and tracks:
-- | - Whether the palette is open
-- | - The current search query
-- | - Which item is highlighted (for keyboard navigation)
type CommandPaletteState =
  { isOpen :: Boolean
  , query :: String
  , highlightedIndex :: Int
  }

-- | Initial state with palette closed
initialState :: CommandPaletteState
initialState =
  { isOpen: false
  , query: ""
  , highlightedIndex: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // props type
-- ═════════════════════════════════════════════════════════════════════════════

-- | CommandPalette properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type CommandPaletteProps msg =
  { -- Content
    commands :: Array (CommandItem msg)
  , groups :: Array (CommandGroup msg)
  , placeholder :: String
  , emptyMessage :: String
  , isOpen :: Boolean
  , query :: String
  , highlightedIndex :: Int
  
  -- Accessibility
  , ariaLabel :: Maybe String
  
  -- Overlay colors
  , overlayColor :: Maybe Color.RGB
  , overlayOpacity :: Maybe Number
  
  -- Panel colors
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  
  -- Input colors
  , inputBackgroundColor :: Maybe Color.RGB
  , inputTextColor :: Maybe Color.RGB
  , inputPlaceholderColor :: Maybe Color.RGB
  , inputBorderColor :: Maybe Color.RGB
  
  -- Item colors
  , itemTextColor :: Maybe Color.RGB
  , itemDescriptionColor :: Maybe Color.RGB
  , itemShortcutColor :: Maybe Color.RGB
  , itemHighlightedBackgroundColor :: Maybe Color.RGB
  , itemHighlightedTextColor :: Maybe Color.RGB
  , itemDisabledColor :: Maybe Color.RGB
  
  -- Group header colors
  , groupHeaderColor :: Maybe Color.RGB
  , groupBorderColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  , panelWidth :: Maybe Device.Pixel
  , panelMaxHeight :: Maybe Device.Pixel
  , itemHeight :: Maybe Device.Pixel
  , itemPaddingX :: Maybe Device.Pixel
  , itemPaddingY :: Maybe Device.Pixel
  , inputHeight :: Maybe Device.Pixel
  , inputPaddingX :: Maybe Device.Pixel
  
  -- Typography atoms
  , inputFontSize :: Maybe FontSize.FontSize
  , itemFontSize :: Maybe FontSize.FontSize
  , descriptionFontSize :: Maybe FontSize.FontSize
  , shortcutFontSize :: Maybe FontSize.FontSize
  , groupHeaderFontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onQueryChange :: Maybe (String -> msg)
  , onSelect :: Maybe (CommandItem msg -> msg)
  , onClose :: Maybe msg
  , onHighlightChange :: Maybe (Int -> msg)
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type CommandPaletteProp msg = CommandPaletteProps msg -> CommandPaletteProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. CommandPaletteProps msg
defaultProps =
  { -- Content
    commands: []
  , groups: []
  , placeholder: "Type a command or search..."
  , emptyMessage: "No commands found"
  , isOpen: false
  , query: ""
  , highlightedIndex: 0
  
  -- Accessibility
  , ariaLabel: Nothing
  
  -- Overlay colors
  , overlayColor: Nothing
  , overlayOpacity: Nothing
  
  -- Panel colors
  , backgroundColor: Nothing
  , borderColor: Nothing
  
  -- Input colors
  , inputBackgroundColor: Nothing
  , inputTextColor: Nothing
  , inputPlaceholderColor: Nothing
  , inputBorderColor: Nothing
  
  -- Item colors
  , itemTextColor: Nothing
  , itemDescriptionColor: Nothing
  , itemShortcutColor: Nothing
  , itemHighlightedBackgroundColor: Nothing
  , itemHighlightedTextColor: Nothing
  , itemDisabledColor: Nothing
  
  -- Group header colors
  , groupHeaderColor: Nothing
  , groupBorderColor: Nothing
  
  -- Geometry atoms
  , borderRadius: Nothing
  , borderWidth: Nothing
  , panelWidth: Nothing
  , panelMaxHeight: Nothing
  , itemHeight: Nothing
  , itemPaddingX: Nothing
  , itemPaddingY: Nothing
  , inputHeight: Nothing
  , inputPaddingX: Nothing
  
  -- Typography atoms
  , inputFontSize: Nothing
  , itemFontSize: Nothing
  , descriptionFontSize: Nothing
  , shortcutFontSize: Nothing
  , groupHeaderFontSize: Nothing
  
  -- Motion atoms
  , transitionDuration: Nothing
  
  -- Behavior
  , onQueryChange: Nothing
  , onSelect: Nothing
  , onClose: Nothing
  , onHighlightChange: Nothing
  
  -- Escape hatch
  , extraAttributes: []
  }
