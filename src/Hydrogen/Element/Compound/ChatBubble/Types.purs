-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // chat-bubble // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble Types and Props
-- |
-- | Core types for chat bubble components:
-- | - Direction: Sent vs Received message alignment
-- | - Status: Message delivery status indicators
-- | - Props: Full property record with Schema atoms
-- | - Prop builders: Functions to modify props

module Hydrogen.Element.Compound.ChatBubble.Types
  ( -- * Direction Type
    Direction(Sent, Received)
  
  -- * Status Type
  , Status(Sending, SentStatus, Delivered, Read, Failed)
  
  -- * Props
  , ChatBubbleProps
  , ChatBubbleProp
  , defaultProps
  
  -- * Content Props
  , message
  , direction
  , sender
  , avatarUrl
  , timestamp
  , status
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , senderTextColor
  , timestampTextColor
  , glow
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Elevation Atoms
  , shadow
  
  -- * Dimension Atoms
  , padding
  , maxWidth
  , avatarSize
  , gap
  
  -- * Behavior Props
  , showTail
  , onClick
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Glow as Glow
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Message direction
-- |
-- | Determines alignment and default styling:
-- | - `Sent`: Right-aligned, typically brand primary color
-- | - `Received`: Left-aligned, typically neutral/muted color
data Direction
  = Sent
  | Received

derive instance eqDirection :: Eq Direction

instance showDirection :: Show Direction where
  show Sent = "sent"
  show Received = "received"

-- | Message delivery status (for sent messages)
-- |
-- | Visual indicator of message state:
-- | - `Sending`: Clock icon, message in transit
-- | - `SentStatus`: Single check, reached server
-- | - `Delivered`: Double check, reached recipient device
-- | - `Read`: Double check (colored), recipient viewed
-- | - `Failed`: Error indicator, delivery failed
data Status
  = Sending
  | SentStatus
  | Delivered
  | Read
  | Failed

derive instance eqStatus :: Eq Status

instance showStatus :: Show Status where
  show Sending = "sending"
  show SentStatus = "sent"
  show Delivered = "delivered"
  show Read = "read"
  show Failed = "failed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | ChatBubble properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type ChatBubbleProps msg =
  { -- Content
    message :: String
  , direction :: Direction
  , sender :: Maybe String
  , avatarUrl :: Maybe String
  , timestamp :: Maybe String
  , status :: Maybe Status
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , senderTextColor :: Maybe Color.RGB
  , timestampTextColor :: Maybe Color.RGB
  , glow :: Maybe Glow.Glow
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Elevation atoms
  , shadow :: Maybe Shadow.LayeredShadow
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , maxWidth :: Maybe Device.Pixel
  , avatarSize :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Behavior
  , showTail :: Boolean
  , onClick :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ChatBubbleProp msg = ChatBubbleProps msg -> ChatBubbleProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (inherit from context/brand).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. ChatBubbleProps msg
defaultProps =
  { message: ""
  , direction: Received
  , sender: Nothing
  , avatarUrl: Nothing
  , timestamp: Nothing
  , status: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , senderTextColor: Nothing
  , timestampTextColor: Nothing
  , glow: Nothing
  , borderRadius: Nothing
  , shadow: Nothing
  , padding: Nothing
  , maxWidth: Nothing
  , avatarSize: Nothing
  , gap: Nothing
  , showTail: true
  , onClick: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set message text
message :: forall msg. String -> ChatBubbleProp msg
message m props = props { message = m }

-- | Set message direction (Sent or Received)
direction :: forall msg. Direction -> ChatBubbleProp msg
direction d props = props { direction = d }

-- | Set sender name (for received messages)
sender :: forall msg. String -> ChatBubbleProp msg
sender s props = props { sender = Just s }

-- | Set avatar URL
avatarUrl :: forall msg. String -> ChatBubbleProp msg
avatarUrl url props = props { avatarUrl = Just url }

-- | Set timestamp text
timestamp :: forall msg. String -> ChatBubbleProp msg
timestamp t props = props { timestamp = Just t }

-- | Set delivery status (for sent messages)
status :: forall msg. Status -> ChatBubbleProp msg
status s props = props { status = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bubble background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ChatBubbleProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set message text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ChatBubbleProp msg
textColor c props = props { textColor = Just c }

-- | Set sender name text color (Color.RGB atom)
senderTextColor :: forall msg. Color.RGB -> ChatBubbleProp msg
senderTextColor c props = props { senderTextColor = Just c }

-- | Set timestamp text color (Color.RGB atom)
timestampTextColor :: forall msg. Color.RGB -> ChatBubbleProp msg
timestampTextColor c props = props { timestampTextColor = Just c }

-- | Set glow effect (Color.Glow atom)
-- |
-- | Renders as CSS `filter: drop-shadow(...)`.
glow :: forall msg. Glow.Glow -> ChatBubbleProp msg
glow g props = props { glow = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
-- |
-- | Supports per-corner radius for chat bubble tail effects.
borderRadius :: forall msg. Geometry.Corners -> ChatBubbleProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set box shadow (Shadow.LayeredShadow atom)
-- |
-- | Supports multiple shadow layers for depth effects.
shadow :: forall msg. Shadow.LayeredShadow -> ChatBubbleProp msg
shadow s props = props { shadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bubble padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ChatBubbleProp msg
padding p props = props { padding = Just p }

-- | Set maximum bubble width (Device.Pixel atom)
maxWidth :: forall msg. Device.Pixel -> ChatBubbleProp msg
maxWidth w props = props { maxWidth = Just w }

-- | Set avatar size (Device.Pixel atom)
avatarSize :: forall msg. Device.Pixel -> ChatBubbleProp msg
avatarSize s props = props { avatarSize = Just s }

-- | Set gap between avatar and bubble (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ChatBubbleProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show bubble tail pointer
showTail :: forall msg. Boolean -> ChatBubbleProp msg
showTail t props = props { showTail = t }

-- | Set click handler
onClick :: forall msg. msg -> ChatBubbleProp msg
onClick handler props = props { onClick = Just handler }

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ChatBubbleProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
