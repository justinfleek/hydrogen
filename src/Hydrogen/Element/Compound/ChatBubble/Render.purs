-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // chat-bubble // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble Rendering Logic
-- |
-- | Core rendering functions for chat bubble components.
-- | Transforms props into Element structures with proper styling.

module Hydrogen.Element.Compound.ChatBubble.Render
  ( -- * Wrapper Building
    wrapperAttrs
  , wrapperChildren
  ) where

import Prelude
  ( show
  , (<>)
  , not
  )

import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Glow as Glow
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow

import Hydrogen.Element.Compound.ChatBubble.Types
  ( ChatBubbleProps
  )
import Hydrogen.Element.Compound.ChatBubble.Icons (statusToIcon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // wrapper rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wrapper attributes (alignment)
-- |
-- | Sets up flex container with proper alignment based on direction.
wrapperAttrs :: forall msg. Boolean -> ChatBubbleProps msg -> Array (E.Attribute msg)
wrapperAttrs isSent props =
  let
    alignStyle = if isSent then "flex-end" else "flex-start"
    gapStyle = maybe "8px" show props.gap
  in
    [ E.style "display" "flex"
    , E.style "justify-content" alignStyle
    , E.style "align-items" "flex-end"
    , E.style "gap" gapStyle
    , E.style "margin-bottom" "8px"
    ]

-- | Wrapper children (avatar + bubble column)
-- |
-- | Sent messages show only the bubble.
-- | Received messages may include avatar before bubble.
wrapperChildren :: forall msg. Boolean -> ChatBubbleProps msg -> Array (E.Element msg)
wrapperChildren isSent props =
  let
    avatarEl = renderAvatar props
    bubbleColumn = renderBubbleColumn isSent props
  in
    if isSent
      then [ bubbleColumn ]
      else case props.avatarUrl of
        Just _ -> [ avatarEl, bubbleColumn ]
        Nothing -> [ bubbleColumn ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // avatar rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render avatar image
-- |
-- | Circular avatar with configurable size.
renderAvatar :: forall msg. ChatBubbleProps msg -> E.Element msg
renderAvatar props =
  let
    size = maybe "32px" show props.avatarSize
    url = maybe "" (\u -> u) props.avatarUrl
    altText = maybe "Avatar" (\s -> s) props.sender
  in
    E.img_
      [ E.src url
      , E.alt altText
      , E.style "width" size
      , E.style "height" size
      , E.style "border-radius" "50%"
      , E.style "object-fit" "cover"
      , E.style "flex-shrink" "0"
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // bubble column rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render bubble column (sender + bubble + metadata)
-- |
-- | Vertical stack containing sender name (if received),
-- | the bubble itself, and metadata.
renderBubbleColumn :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderBubbleColumn isSent props =
  let
    alignItems = if isSent then "flex-end" else "flex-start"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "align-items" alignItems
      ]
      [ renderSenderName isSent props
      , renderBubble isSent props
      ]

-- | Render sender name (for received messages)
-- |
-- | Only displays for received messages with a sender set.
renderSenderName :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderSenderName isSent props =
  if isSent
    then E.empty
    else case props.sender of
      Nothing -> E.empty
      Just name ->
        let
          colorStyle = maybe "inherit" Color.toLegacyCss props.senderTextColor
        in
          E.span_
            [ E.style "font-size" "12px"
            , E.style "font-weight" "500"
            , E.style "color" colorStyle
            , E.style "margin-bottom" "4px"
            ]
            [ E.text name ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bubble rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the bubble itself
-- |
-- | Main bubble element with background, border radius,
-- | shadow, and glow effects from Schema atoms.
renderBubble :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderBubble isSent props =
  let
    bubbleStyles = buildBubbleStyles isSent props
    
    clickAttr = case props.onClick of
      Just handler -> [ E.onClick handler, E.style "cursor" "pointer" ]
      Nothing -> []
    
    allAttrs = bubbleStyles <> clickAttr <> props.extraAttributes
  in
    E.div_
      allAttrs
      [ renderMessageText props
      , renderMetadata isSent props
      ]

-- | Build bubble style attributes from Schema atoms
-- |
-- | Applies color, geometry, and elevation atoms to create
-- | the visual appearance of the bubble.
buildBubbleStyles :: forall msg. Boolean -> ChatBubbleProps msg -> Array (E.Attribute msg)
buildBubbleStyles isSent props =
  let
    -- Default colors based on direction (fallbacks if no atom provided)
    defaultBgColor = if isSent 
      then Color.rgb 59 130 246
      else Color.rgb 241 245 249
    
    defaultTextColor = if isSent
      then Color.rgb 255 255 255
      else Color.rgb 15 23 42
    
    -- Apply atoms or defaults
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    txtColor = maybe defaultTextColor (\c -> c) props.textColor
    
    -- Border radius (default: 16px with tail adjustment)
    defaultRadius = if isSent
      then Geometry.corners 
             (Geometry.px 16.0) 
             (Geometry.px 16.0) 
             (Geometry.px 4.0)
             (Geometry.px 16.0)
      else Geometry.corners 
             (Geometry.px 16.0) 
             (Geometry.px 16.0) 
             (Geometry.px 16.0) 
             (Geometry.px 4.0)
    
    radiusValue = maybe defaultRadius (\r -> r) props.borderRadius
    
    -- Padding (default: 12px 16px)
    paddingValue = maybe "12px 16px" (\p -> show p) props.padding
    
    -- Max width (default: 75%)
    maxWidthValue = maybe "75%" (\w -> show w) props.maxWidth
    
    -- Core styles
    coreStyles =
      [ E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss txtColor)
      , E.style "border-radius" (Geometry.cornersToLegacyCss radiusValue)
      , E.style "padding" paddingValue
      , E.style "max-width" maxWidthValue
      , E.style "word-wrap" "break-word"
      , E.style "position" "relative"
      ]
    
    -- Shadow (if provided)
    shadowStyle = case props.shadow of
      Nothing -> []
      Just s -> 
        if Shadow.isNoShadow s
          then []
          else [ E.style "box-shadow" (Shadow.layeredToLegacyCss s) ]
    
    -- Glow (if provided, and not "off")
    glowStyle = case props.glow of
      Nothing -> []
      Just g -> 
        if Glow.isOff g
          then []
          else [ E.style "filter" (Glow.glowToCss g) ]
    
    -- Transition for hover effects
    transitionStyle =
      [ E.style "transition" "transform 0.15s ease-out, filter 0.15s ease-out, box-shadow 0.15s ease-out"
      ]
  in
    coreStyles <> shadowStyle <> glowStyle <> transitionStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // content rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render message text
-- |
-- | Preserves whitespace for multi-line messages.
renderMessageText :: forall msg. ChatBubbleProps msg -> E.Element msg
renderMessageText props =
  E.p_
    [ E.style "margin" "0"
    , E.style "white-space" "pre-wrap"
    ]
    [ E.text props.message ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // metadata rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render metadata row (timestamp + status)
-- |
-- | Only displays if timestamp is set. Shows delivery status
-- | icon for sent messages.
renderMetadata :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderMetadata isSent props =
  case props.timestamp of
    Nothing -> E.empty
    Just ts ->
      let
        colorStyle = maybe "inherit" Color.toLegacyCss props.timestampTextColor
        defaultOpacity = "0.7"
      in
        E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "justify-content" "flex-end"
          , E.style "gap" "4px"
          , E.style "margin-top" "4px"
          , E.style "font-size" "11px"
          , E.style "color" colorStyle
          , E.style "opacity" defaultOpacity
          ]
          [ E.span_ [] [ E.text ts ]
          , renderStatusIcon isSent props
          ]

-- | Render status icon (for sent messages)
-- |
-- | Only displays for sent messages with a status set.
renderStatusIcon :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderStatusIcon isSent props =
  if not isSent
    then E.empty
    else case props.status of
      Nothing -> E.empty
      Just st -> statusToIcon st
