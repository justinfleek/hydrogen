-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // chat-bubble
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble — Schema-native chat message component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars:
-- |
-- | - **Color**: Background, text, glow
-- | - **Geometry**: Border radius
-- | - **Elevation**: Shadow, z-index
-- | - **Dimension**: Padding, max width
-- | - **Typography**: Font styling (via TypeStyle)
-- |
-- | The **BrandSchema** defines what these atoms are for a given brand.
-- | This component just renders them faithfully.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property        | Pillar     | Type                    | CSS Output              |
-- | |-----------------|------------|-------------------------|-------------------------|
-- | | backgroundColor | Color      | Color.RGB               | background-color        |
-- | | textColor       | Color      | Color.RGB               | color                   |
-- | | borderRadius    | Geometry   | Geometry.Corners        | border-radius           |
-- | | shadow          | Elevation  | Shadow.LayeredShadow    | box-shadow              |
-- | | glow            | Color      | Color.Glow              | filter: drop-shadow     |
-- | | padding         | Dimension  | Device.Pixel            | padding                 |
-- | | maxWidth        | Dimension  | Device.Pixel            | max-width               |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.ChatBubble as ChatBubble
-- | import Hydrogen.Schema.Color as Color
-- | import Hydrogen.Schema.Geometry as Geometry
-- | import Hydrogen.Schema.Elevation.Shadow as Shadow
-- |
-- | -- Minimal usage
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "Hello, world!"
-- |   , ChatBubble.direction ChatBubble.Sent
-- |   ]
-- |
-- | -- With brand atoms
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "Hello!"
-- |   , ChatBubble.direction ChatBubble.Sent
-- |   , ChatBubble.backgroundColor brand.primary
-- |   , ChatBubble.textColor brand.onPrimary
-- |   , ChatBubble.borderRadius brand.bubbleRadius
-- |   , ChatBubble.shadow brand.bubbleShadow
-- |   , ChatBubble.glow brand.accentGlow
-- |   ]
-- |
-- | -- With status and metadata
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "Did you see the update?"
-- |   , ChatBubble.direction ChatBubble.Sent
-- |   , ChatBubble.timestamp "10:42 AM"
-- |   , ChatBubble.status ChatBubble.Delivered
-- |   ]
-- |
-- | -- Received message with avatar
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "I'm doing great, thanks!"
-- |   , ChatBubble.direction ChatBubble.Received
-- |   , ChatBubble.sender "Alice"
-- |   , ChatBubble.avatarUrl "https://..."
-- |   , ChatBubble.backgroundColor (Color.rgb 241 245 249)
-- |   , ChatBubble.textColor (Color.rgb 15 23 42)
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `ChatBubble.Types`: Direction, Status, Props, prop builders
-- | - `ChatBubble.Render`: Internal rendering functions
-- | - `ChatBubble.Companion`: chatContainer, typingIndicator, dateDivider
-- | - `ChatBubble.Icons`: SVG status icons

module Hydrogen.Element.Compound.ChatBubble
  ( -- * Main Component
    chatBubble
  
  -- * Companion Components (re-exported from Companion)
  , module Companion
  
  -- * Types (re-exported from Types)
  , module Types
  
  -- * Icons (re-exported from Icons)
  , module Icons
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  )

import Data.Array (foldl)

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.ChatBubble.Types
  ( Direction(Sent, Received)
  , Status(Sending, SentStatus, Delivered, Read, Failed)
  , ChatBubbleProps
  , ChatBubbleProp
  , defaultProps
  , message
  , direction
  , sender
  , avatarUrl
  , timestamp
  , status
  , backgroundColor
  , textColor
  , senderTextColor
  , timestampTextColor
  , glow
  , borderRadius
  , shadow
  , padding
  , maxWidth
  , avatarSize
  , gap
  , showTail
  , onClick
  , extraAttributes
  ) as Types

import Hydrogen.Element.Compound.ChatBubble.Render as Render

import Hydrogen.Element.Compound.ChatBubble.Companion
  ( chatContainer
  , typingIndicator
  , dateDivider
  ) as Companion

import Hydrogen.Element.Compound.ChatBubble.Icons
  ( statusToIcon
  , clockIcon
  , singleCheckIcon
  , doubleCheckIcon
  , doubleCheckReadIcon
  , errorIcon
  ) as Icons

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a chat bubble
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- |
-- | ```purescript
-- | chatBubble
-- |   [ message "Hello, world!"
-- |   , direction Sent
-- |   , backgroundColor (Color.rgb 59 130 246)
-- |   ]
-- | ```
chatBubble :: forall msg. Array (Types.ChatBubbleProp msg) -> E.Element msg
chatBubble propMods =
  let
    props = foldl (\p f -> f p) Types.defaultProps propMods
    isSent = props.direction == Types.Sent
  in
    E.div_
      (Render.wrapperAttrs isSent props)
      (Render.wrapperChildren isSent props)
