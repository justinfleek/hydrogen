-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // command-palette
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CommandPalette — Schema-native command palette for keyboard-driven actions.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the Schema pillars.
-- | When an atom is `Nothing`, no style is emitted — the element inherits
-- | from its parent or browser defaults.
-- |
-- | **No hardcoded CSS values.** The BrandSchema provides all visual atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property                      | Pillar     | Type                |
-- | |-------------------------------|------------|---------------------|
-- | | overlayColor                  | Color      | Color.RGB           |
-- | | backgroundColor               | Color      | Color.RGB           |
-- | | borderColor                   | Color      | Color.RGB           |
-- | | inputBackgroundColor          | Color      | Color.RGB           |
-- | | inputTextColor                | Color      | Color.RGB           |
-- | | itemTextColor                 | Color      | Color.RGB           |
-- | | itemHighlightedBackgroundColor| Color      | Color.RGB           |
-- | | groupHeaderColor              | Color      | Color.RGB           |
-- | | borderRadius                  | Geometry   | Geometry.Corners    |
-- | | borderWidth                   | Dimension  | Device.Pixel        |
-- | | panelWidth                    | Dimension  | Device.Pixel        |
-- | | panelMaxHeight                | Dimension  | Device.Pixel        |
-- | | inputFontSize                 | Typography | FontSize.FontSize   |
-- | | transitionDuration            | Motion     | Temporal.Milliseconds|
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.CommandPalette as CP
-- |
-- | -- Basic command palette
-- | CP.commandPalette
-- |   [ CP.paletteOpen state.isCommandPaletteOpen
-- |   , CP.commands myCommands
-- |   , CP.paletteQuery state.searchQuery
-- |   , CP.onQueryChange UpdateSearch
-- |   , CP.onSelect ExecuteCommand
-- |   , CP.onClose CloseCommandPalette
-- |   ]
-- |
-- | -- With brand atoms
-- | CP.commandPalette
-- |   [ CP.paletteOpen state.isOpen
-- |   , CP.commands myCommands
-- |   , CP.backgroundColor brand.panelBackground
-- |   , CP.itemHighlightedBackgroundColor brand.accent
-- |   , CP.borderRadius brand.radiusLg
-- |   , CP.onSelect ExecuteCommand
-- |   ]
-- | ```
-- |
-- | ## Creating Commands
-- |
-- | ```purescript
-- | import Hydrogen.Util.Keyboard as Keyboard
-- |
-- | myCommands :: Array (CP.CommandItem Msg)
-- | myCommands =
-- |   [ { id: "save"
-- |     , label: "Save Document"
-- |     , description: Just "Save the current document to disk"
-- |     , shortcut: Just (Keyboard.parseShortcut "Ctrl+S")
-- |     , icon: Nothing
-- |     , group: Just "File"
-- |     , disabled: false
-- |     , action: SaveDocument
-- |     }
-- |   , { id: "open"
-- |     , label: "Open File"
-- |     , description: Nothing
-- |     , shortcut: Just (Keyboard.parseShortcut "Ctrl+O")
-- |     , icon: Nothing
-- |     , group: Just "File"
-- |     , disabled: false
-- |     , action: OpenFilePicker
-- |     }
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `CommandPalette.Types` — Core type definitions
-- | - `CommandPalette.Props` — Property builder functions
-- | - `CommandPalette.Render` — Internal rendering functions

module Hydrogen.Element.Compound.CommandPalette
  ( -- * CommandPalette Component
    commandPalette
  
  -- * Command Filtering
  , filterCommands
  
  -- * Types (re-exported from Types)
  , module Types
  
  -- * Props (re-exported from Props)
  , module Props
  ) where

import Prelude
  ( (<>)
  , (==)
  , ($)
  , not
  , map
  , (&&)
  , (||)
  )

import Data.Array (filter, foldl, concat, sortBy, length, mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering)
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.CommandPalette.Types
  ( CommandId
  , CommandItem
  , CommandGroup
  , CommandPaletteState
  , initialState
  , CommandPaletteProps
  , CommandPaletteProp
  , defaultProps
  ) as Types

import Hydrogen.Element.Compound.CommandPalette.Props
  ( commands
  , groups
  , placeholder
  , emptyMessage
  , paletteOpen
  , paletteQuery
  , paletteHighlightedIndex
  , paletteAriaLabel
  , overlayColor
  , overlayOpacity
  , backgroundColor
  , borderColor
  , inputBackgroundColor
  , inputTextColor
  , inputPlaceholderColor
  , inputBorderColor
  , itemTextColor
  , itemDescriptionColor
  , itemShortcutColor
  , itemHighlightedBackgroundColor
  , itemHighlightedTextColor
  , itemDisabledColor
  , groupHeaderColor
  , groupBorderColor
  , borderRadius
  , borderWidth
  , panelWidth
  , panelMaxHeight
  , itemHeight
  , itemPaddingX
  , itemPaddingY
  , inputHeight
  , inputPaddingX
  , inputFontSize
  , itemFontSize
  , descriptionFontSize
  , shortcutFontSize
  , groupHeaderFontSize
  , transitionDuration
  , onQueryChange
  , onSelect
  , onClose
  , onHighlightChange
  , extraAttributes
  ) as Props

import Hydrogen.Element.Compound.CommandPalette.Render
  ( renderOverlay
  , renderPanel
  , renderSearchInput
  , renderCommandList
  , renderCommandItem
  , renderGroupHeader
  , renderEmptyState
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a command palette
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
-- |
-- | The command palette consists of:
-- | - A semi-transparent overlay backdrop
-- | - A centered panel with search input
-- | - A scrollable list of commands
-- | - Keyboard navigation (Arrow keys, Enter, Escape)
commandPalette :: forall msg. Array (Types.CommandPaletteProp msg) -> E.Element msg
commandPalette propMods =
  let
    props = foldl (\p f -> f p) Types.defaultProps propMods
  in
    if not props.isOpen
      then E.empty
      else
        E.div_
          [ E.style "position" "fixed"
          , E.style "inset" "0"
          , E.style "z-index" "50"
          ]
          [ -- Backdrop overlay
            renderOverlay props
          -- Main panel (positioned over overlay)
          , E.div_
              [ E.style "position" "fixed"
              , E.style "inset" "0"
              , E.style "display" "flex"
              , E.style "align-items" "flex-start"
              , E.style "justify-content" "center"
              , E.style "padding-top" "20vh"
              , E.style "pointer-events" "none"
              ]
              [ E.div_
                  [ E.style "pointer-events" "auto" ]
                  [ renderPanel props
                      [ renderSearchInput props
                      , renderCommandListWithItems props
                      ]
                  ]
              ]
          ]

-- | Internal: Render the command list with filtered items
renderCommandListWithItems :: forall msg. Types.CommandPaletteProps msg -> E.Element msg
renderCommandListWithItems props =
  let
    filteredCommands = filterCommands props.query props.commands
    
    -- If groups are provided, organize by group
    -- Otherwise, show flat list
    content =
      if length props.groups == 0
        then renderFlatList props filteredCommands
        else renderGroupedList props filteredCommands
  in
    renderCommandList props content

-- | Render a flat list of commands (no groups)
renderFlatList
  :: forall msg
   . Types.CommandPaletteProps msg
  -> Array (Types.CommandItem msg)
  -> Array (E.Element msg)
renderFlatList props commands_ =
  if length commands_ == 0
    then [ renderEmptyState props ]
    else mapWithIndex (renderCommandItem props) commands_

-- | Render commands organized by group
renderGroupedList
  :: forall msg
   . Types.CommandPaletteProps msg
  -> Array (Types.CommandItem msg)
  -> Array (E.Element msg)
renderGroupedList props commands_ =
  if length commands_ == 0
    then [ renderEmptyState props ]
    else
      let
        -- Sort groups by priority
        sortedGroups = sortBy compareGroupPriority props.groups
        
        -- Render each group with its commands
        groupElements = map (renderGroupWithCommands props commands_) sortedGroups
        
        -- Commands without a group (ungrouped)
        ungroupedCommands = filter hasNoGroup commands_
        ungroupedElements =
          if length ungroupedCommands == 0
            then []
            else mapWithIndex (renderCommandItem props) ungroupedCommands
      in
        concat groupElements <> ungroupedElements
  where
    compareGroupPriority :: Types.CommandGroup msg -> Types.CommandGroup msg -> Ordering
    compareGroupPriority g1 g2 = compare g1.priority g2.priority
    
    hasNoGroup :: Types.CommandItem msg -> Boolean
    hasNoGroup item = case item.group of
      Nothing -> true
      Just _ -> false

-- | Render a single group with its commands
renderGroupWithCommands
  :: forall msg
   . Types.CommandPaletteProps msg
  -> Array (Types.CommandItem msg)
  -> Types.CommandGroup msg
  -> Array (E.Element msg)
renderGroupWithCommands props allCommands group =
  let
    groupCommands = filter (belongsToGroup group.id) allCommands
  in
    if length groupCommands == 0
      then []
      else
        [ renderGroupHeader props group.label ]
        <> mapWithIndex (renderCommandItem props) groupCommands
  where
    belongsToGroup :: String -> Types.CommandItem msg -> Boolean
    belongsToGroup groupId item = case item.group of
      Just g -> g == groupId
      Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // command filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter commands by search query
-- |
-- | Matches against:
-- | - Command label (case-insensitive)
-- | - Command description (if present, case-insensitive)
-- | - Group name (if present, case-insensitive)
filterCommands
  :: forall msg
   . String
  -> Array (Types.CommandItem msg)
  -> Array (Types.CommandItem msg)
filterCommands query commands_ =
  if String.length query == 0
    then commands_
    else filter (matchesQuery (String.toLower query)) commands_
  where
    matchesQuery :: String -> Types.CommandItem msg -> Boolean
    matchesQuery q item =
      let
        labelMatch = String.contains (Pattern q) (String.toLower item.label)
        
        descMatch = case item.description of
          Just desc -> String.contains (Pattern q) (String.toLower desc)
          Nothing -> false
        
        groupMatch = case item.group of
          Just g -> String.contains (Pattern q) (String.toLower g)
          Nothing -> false
      in
        labelMatch || descMatch || groupMatch


