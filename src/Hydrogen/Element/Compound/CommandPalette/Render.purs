-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // command-palette // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CommandPalette Render — Pure rendering functions for the command palette.
-- |
-- | These functions convert props into Element trees. They are pure functions
-- | with no side effects — all state comes through props.

module Hydrogen.Element.Compound.CommandPalette.Render
  ( -- * Rendering
    renderOverlay
  , renderPanel
  , renderSearchInput
  , renderCommandList
  , renderCommandItem
  , renderGroupHeader
  , renderEmptyState
  , renderShortcut
  ) where

import Prelude
  ( show
  , (<>)
  , (==)
  , (&&)
  , not
  , map
  , ($)
  )

import Data.Array (mapWithIndex, length)
import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Gestural.Input.Shortcut (Shortcut)
import Hydrogen.Schema.Gestural.Input.Shortcut as Shortcut

import Hydrogen.Element.Compound.CommandPalette.Types
  ( CommandPaletteProps
  , CommandItem
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // render overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the backdrop overlay
-- |
-- | Clicking the overlay closes the palette.
renderOverlay :: forall msg. CommandPaletteProps msg -> E.Element msg
renderOverlay props =
  let
    baseAttrs =
      [ E.style "position" "fixed"
      , E.style "inset" "0"
      , E.style "z-index" "50"
      , E.style "display" "flex"
      , E.style "align-items" "flex-start"
      , E.style "justify-content" "center"
      , E.style "padding-top" "20vh"
      ]
    
    colorAttr = case props.overlayColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> [ E.style "background-color" "rgba(0, 0, 0, 0.5)" ]
    
    opacityAttr = case props.overlayOpacity of
      Just o -> [ E.style "opacity" (show o) ]
      Nothing -> []
    
    clickHandler = case props.onClose of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.div_ (baseAttrs <> colorAttr <> opacityAttr <> clickHandler) []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // render panel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the main panel container
-- |
-- | Contains the search input and command list.
renderPanel :: forall msg. CommandPaletteProps msg -> Array (E.Element msg) -> E.Element msg
renderPanel props children =
  let
    baseAttrs =
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "overflow" "hidden"
      , E.role "dialog"
      , E.attr "aria-modal" "true"
      ]
    
    ariaAttrs = case props.ariaLabel of
      Just l -> [ E.attr "aria-label" l ]
      Nothing -> [ E.attr "aria-label" "Command palette" ]
    
    bgAttr = case props.backgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    borderColorAttr = case props.borderColor of
      Just c -> [ E.style "border-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    borderWidthAttr = case props.borderWidth of
      Just w -> [ E.style "border-width" (show w)
                , E.style "border-style" "solid"
                ]
      Nothing -> []
    
    radiusAttr = case props.borderRadius of
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
      Nothing -> []
    
    widthAttr = case props.panelWidth of
      Just w -> [ E.style "width" (show w) ]
      Nothing -> [ E.style "width" "640px" ]
    
    maxHeightAttr = case props.panelMaxHeight of
      Just h -> [ E.style "max-height" (show h) ]
      Nothing -> [ E.style "max-height" "400px" ]
    
    -- Prevent click propagation to overlay
    stopPropagation =
      [ E.attr "onclick" "event.stopPropagation()" ]
  in
    E.div_
      ( baseAttrs
      <> ariaAttrs
      <> bgAttr
      <> borderColorAttr
      <> borderWidthAttr
      <> radiusAttr
      <> widthAttr
      <> maxHeightAttr
      <> stopPropagation
      <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // render search input
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the search input field
renderSearchInput :: forall msg. CommandPaletteProps msg -> E.Element msg
renderSearchInput props =
  let
    containerAttrs =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "border-bottom" "1px solid"
      ]
    
    containerBorderAttr = case props.inputBorderColor of
      Just c -> [ E.style "border-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    inputBaseAttrs =
      [ E.attr "type" "text"
      , E.attr "placeholder" props.placeholder
      , E.attr "value" props.query
      , E.style "flex" "1"
      , E.style "border" "none"
      , E.style "outline" "none"
      , E.attr "autofocus" "true"
      ]
    
    inputBgAttr = case props.inputBackgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> [ E.style "background-color" "transparent" ]
    
    inputTextAttr = case props.inputTextColor of
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    inputHeightAttr = case props.inputHeight of
      Just h -> [ E.style "height" (show h) ]
      Nothing -> [ E.style "height" "48px" ]
    
    inputPaddingAttr = case props.inputPaddingX of
      Just p -> [ E.style "padding-left" (show p)
                , E.style "padding-right" (show p)
                ]
      Nothing -> [ E.style "padding-left" "16px"
                 , E.style "padding-right" "16px"
                 ]
    
    inputFontAttr = case props.inputFontSize of
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
      Nothing -> []
    
    inputHandler = case props.onQueryChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    -- Search icon
    searchIcon = E.span_
      [ E.style "padding-left" "16px"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      ]
      [ E.text "\x1F50D" ]  -- Magnifying glass emoji as placeholder
  in
    E.div_ (containerAttrs <> containerBorderAttr)
      [ searchIcon
      , E.input_
          ( inputBaseAttrs
          <> inputBgAttr
          <> inputTextAttr
          <> inputHeightAttr
          <> inputPaddingAttr
          <> inputFontAttr
          <> inputHandler
          )
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // render command list
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the scrollable command list
renderCommandList :: forall msg. CommandPaletteProps msg -> Array (E.Element msg) -> E.Element msg
renderCommandList props children =
  let
    baseAttrs =
      [ E.style "flex" "1"
      , E.style "overflow-y" "auto"
      , E.role "listbox"
      ]
  in
    E.div_ baseAttrs children

-- | Render a single command item
-- |
-- | The `index` is used for highlight state and accessibility.
renderCommandItem
  :: forall msg
   . CommandPaletteProps msg
  -> Int
  -> CommandItem msg
  -> E.Element msg
renderCommandItem props index item =
  let
    isHighlighted = index == props.highlightedIndex
    isDisabled = item.disabled
    
    baseAttrs =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "space-between"
      , E.style "cursor" (if isDisabled then "not-allowed" else "pointer")
      , E.role "option"
      , E.attr "aria-selected" (if isHighlighted then "true" else "false")
      , E.attr "aria-disabled" (if isDisabled then "true" else "false")
      ]
    
    bgAttr = 
      if isHighlighted
        then case props.itemHighlightedBackgroundColor of
          Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
          Nothing -> []
        else []
    
    textColorAttr =
      if isDisabled
        then case props.itemDisabledColor of
          Just c -> [ E.style "color" (Color.toLegacyCss c) ]
          Nothing -> [ E.style "opacity" "0.5" ]
        else if isHighlighted
          then case props.itemHighlightedTextColor of
            Just c -> [ E.style "color" (Color.toLegacyCss c) ]
            Nothing -> []
          else case props.itemTextColor of
            Just c -> [ E.style "color" (Color.toLegacyCss c) ]
            Nothing -> []
    
    heightAttr = case props.itemHeight of
      Just h -> [ E.style "height" (show h) ]
      Nothing -> []
    
    paddingXAttr = case props.itemPaddingX of
      Just p -> [ E.style "padding-left" (show p)
                , E.style "padding-right" (show p)
                ]
      Nothing -> [ E.style "padding-left" "16px"
                 , E.style "padding-right" "16px"
                 ]
    
    paddingYAttr = case props.itemPaddingY of
      Just p -> [ E.style "padding-top" (show p)
                , E.style "padding-bottom" (show p)
                ]
      Nothing -> [ E.style "padding-top" "8px"
                 , E.style "padding-bottom" "8px"
                 ]
    
    fontAttr = case props.itemFontSize of
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
      Nothing -> []
    
    clickHandler =
      if isDisabled
        then []
        else case props.onSelect of
          Just handler -> [ E.onClick (handler item) ]
          Nothing -> []
    
    -- Left side: icon + label + description
    leftContent =
      [ E.div_
          [ E.style "display" "flex"
          , E.style "flex-direction" "column"
          , E.style "gap" "2px"
          ]
          [ -- Label
            E.span_ [] [ E.text item.label ]
            -- Description (if present)
          , case item.description of
              Just desc ->
                let
                  descColorAttr = case props.itemDescriptionColor of
                    Just c -> [ E.style "color" (Color.toLegacyCss c) ]
                    Nothing -> [ E.style "opacity" "0.7" ]
                  descFontAttr = case props.descriptionFontSize of
                    Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
                    Nothing -> [ E.style "font-size" "0.875em" ]
                in
                  E.span_ (descColorAttr <> descFontAttr) [ E.text desc ]
              Nothing -> E.empty
          ]
      ]
    
    -- Right side: keyboard shortcut
    rightContent = case item.shortcut of
      Just s -> [ renderShortcut props s ]
      Nothing -> []
    
    -- Icon (if present)
    iconContent = case item.icon of
      Just iconEl ->
        [ E.span_
            [ E.style "margin-right" "12px"
            , E.style "display" "flex"
            , E.style "align-items" "center"
            ]
            [ iconEl ]
        ]
      Nothing -> []
  in
    E.div_
      ( baseAttrs
      <> bgAttr
      <> textColorAttr
      <> heightAttr
      <> paddingXAttr
      <> paddingYAttr
      <> fontAttr
      <> clickHandler
      )
      ( iconContent <> leftContent <> rightContent )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // render group header
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a group header
renderGroupHeader :: forall msg. CommandPaletteProps msg -> String -> E.Element msg
renderGroupHeader props label =
  let
    baseAttrs =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "padding" "8px 16px"
      , E.style "font-weight" "600"
      , E.style "text-transform" "uppercase"
      , E.style "letter-spacing" "0.05em"
      ]
    
    colorAttr = case props.groupHeaderColor of
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
      Nothing -> [ E.style "opacity" "0.6" ]
    
    fontAttr = case props.groupHeaderFontSize of
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
      Nothing -> [ E.style "font-size" "0.75em" ]
    
    borderAttr = case props.groupBorderColor of
      Just c -> [ E.style "border-top" ("1px solid " <> Color.toLegacyCss c) ]
      Nothing -> []
  in
    E.div_ (baseAttrs <> colorAttr <> fontAttr <> borderAttr)
      [ E.text label ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // render empty state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the empty state when no commands match
renderEmptyState :: forall msg. CommandPaletteProps msg -> E.Element msg
renderEmptyState props =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "padding" "32px"
    , E.style "opacity" "0.5"
    ]
    [ E.text props.emptyMessage ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // render shortcut
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a keyboard shortcut badge
renderShortcut :: forall msg. CommandPaletteProps msg -> Shortcut -> E.Element msg
renderShortcut props sc =
  let
    formatted = Shortcut.toDisplayString sc
    
    baseAttrs =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
    
    keyAttrs =
      [ E.style "padding" "2px 6px"
      , E.style "border-radius" "4px"
      , E.style "background-color" "rgba(0, 0, 0, 0.1)"
      , E.style "font-family" "monospace"
      ]
    
    colorAttr = case props.itemShortcutColor of
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    fontAttr = case props.shortcutFontSize of
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
      Nothing -> [ E.style "font-size" "0.75em" ]
    
    -- Split the formatted shortcut by + and render each key
    keys = String.split (String.Pattern "+") formatted
    keyElements = map (\k -> E.span_ keyAttrs [ E.text k ]) keys
  in
    E.span_ (baseAttrs <> colorAttr <> fontAttr) keyElements
