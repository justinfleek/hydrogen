-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // qrcode // content // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Content Types — Structured data that QR codes can encode.
-- |
-- | ## Design Philosophy
-- |
-- | QR codes aren't just "strings encoded as squares." They encode **actions**:
-- | - Opening a URL
-- | - Sending an email
-- | - Connecting to WiFi
-- | - Adding a contact
-- | - Triggering a webhook
-- | - Starting a Slack conversation
-- |
-- | This module defines the ADT for all supported content types, each with
-- | its own structured configuration and encoding format.
-- |
-- | ## Encoding Formats
-- |
-- | Different content types encode to different URI schemes:
-- | - URL: https://example.com
-- | - Email: mailto:user@example.com?subject=Hello&body=...
-- | - Phone: tel:+1234567890
-- | - SMS: sms:+1234567890?body=...
-- | - WiFi: WIFI:T:WPA;S:NetworkName;P:password;;
-- | - vCard: BEGIN:VCARD\nVERSION:3.0\n...
-- | - vEvent: BEGIN:VCALENDAR\n...
-- | - Geo: geo:40.7128,-74.0060
-- | - Bitcoin: bitcoin:address?amount=...
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)
-- | - Schema.Scheduling (for calendar events)

module Hydrogen.Element.Component.QRCode.Content.Types
  ( -- * Main Content ADT
    QRContent(..)
  , contentToString
  
  -- * URL Content
  , URLContent
  , urlContent
  , urlWithLabel
  
  -- * Email Content
  , EmailContent
  , emailContent
  , emailWithSubject
  , emailWithBody
  , emailFull
  
  -- * Phone Content
  , PhoneContent
  , phoneContent
  
  -- * SMS Content
  , SMSContent
  , smsContent
  , smsWithBody
  
  -- * WiFi Content
  , WiFiContent
  , WiFiSecurity(WEP, WPA, WPA2, WPA3, NoPassword)
  , wifiContent
  , wifiHidden
  
  -- * vCard Contact
  , VCardContent
  , vCardContent
  , vCardFull
  
  -- * Calendar Event
  , CalendarContent
  , calendarContent
  
  -- * Geo Location
  , GeoContent
  , geoContent
  , geoWithAltitude
  , geoWithQuery
  
  -- * Bitcoin/Crypto
  , BitcoinContent
  , bitcoinContent
  , bitcoinWithAmount
  , bitcoinFull
  
  -- * Slack
  , SlackContent
  , SlackAction(SlackOpenChannel, SlackComposeMessage, SlackTriggerWorkflow)
  , slackChannel
  , slackUser
  , slackCompose
  
  -- * Webhook
  , WebhookContent
  , HTTPMethod(GET, POST, PUT, DELETE, PATCH)
  , webhookGet
  , webhookPost
  
  -- * Deep Link
  , DeepLinkContent
  , deepLink
  , deepLinkWithFallback
  
  -- * Plain Text
  , textContent
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , map
  , otherwise
  , Ordering(LT, EQ, GT)
  , compare
  )

import Data.Array (intercalate, filter, length)
import Data.Maybe (Maybe(Just, Nothing), maybe, isJust)
import Data.String (joinWith, replaceAll, Pattern(Pattern), Replacement(Replacement))
import Data.Tuple (Tuple(Tuple))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // main content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All supported QR code content types.
-- |
-- | Each variant encodes to a specific URI scheme or data format.
data QRContent
  = ContentURL URLContent           -- ^ Web URL (https://, http://)
  | ContentEmail EmailContent       -- ^ Email (mailto:)
  | ContentPhone PhoneContent       -- ^ Phone call (tel:)
  | ContentSMS SMSContent           -- ^ SMS message (sms:)
  | ContentWiFi WiFiContent         -- ^ WiFi network config
  | ContentVCard VCardContent       -- ^ Contact card (vCard)
  | ContentCalendar CalendarContent -- ^ Calendar event (vEvent)
  | ContentGeo GeoContent           -- ^ Geographic location (geo:)
  | ContentBitcoin BitcoinContent   -- ^ Bitcoin payment (bitcoin:)
  | ContentSlack SlackContent       -- ^ Slack deep link
  | ContentWebhook WebhookContent   -- ^ Webhook trigger URL
  | ContentDeepLink DeepLinkContent -- ^ App deep link
  | ContentText String              -- ^ Plain text

derive instance eqQRContent :: Eq QRContent

instance showQRContent :: Show QRContent where
  show (ContentURL _) = "URL"
  show (ContentEmail _) = "Email"
  show (ContentPhone _) = "Phone"
  show (ContentSMS _) = "SMS"
  show (ContentWiFi _) = "WiFi"
  show (ContentVCard _) = "vCard"
  show (ContentCalendar _) = "Calendar"
  show (ContentGeo _) = "Geo"
  show (ContentBitcoin _) = "Bitcoin"
  show (ContentSlack _) = "Slack"
  show (ContentWebhook _) = "Webhook"
  show (ContentDeepLink _) = "DeepLink"
  show (ContentText _) = "Text"

-- | Convert content to encoded string for QR generation.
-- |
-- | This is the string that gets encoded into the QR matrix.
contentToString :: QRContent -> String
contentToString = case _ of
  ContentURL c -> encodeURL c
  ContentEmail c -> encodeEmail c
  ContentPhone c -> encodePhone c
  ContentSMS c -> encodeSMS c
  ContentWiFi c -> encodeWiFi c
  ContentVCard c -> encodeVCard c
  ContentCalendar c -> encodeCalendar c
  ContentGeo c -> encodeGeo c
  ContentBitcoin c -> encodeBitcoin c
  ContentSlack c -> encodeSlack c
  ContentWebhook c -> encodeWebhook c
  ContentDeepLink c -> encodeDeepLink c
  ContentText t -> t

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // url content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | URL content configuration.
type URLContent =
  { url :: String
  , label :: Maybe String  -- ^ Optional human-readable label
  }

-- | Create URL content
urlContent :: String -> QRContent
urlContent url = ContentURL { url, label: Nothing }

-- | Create URL content with label
urlWithLabel :: String -> String -> QRContent
urlWithLabel url label = ContentURL { url, label: Just label }

-- | Encode URL to string
encodeURL :: URLContent -> String
encodeURL c = c.url

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // email content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Email content configuration.
type EmailContent =
  { to :: Array String      -- ^ Primary recipients
  , cc :: Array String      -- ^ CC recipients
  , bcc :: Array String     -- ^ BCC recipients
  , subject :: Maybe String -- ^ Email subject
  , body :: Maybe String    -- ^ Email body
  }

-- | Create simple email content
emailContent :: String -> QRContent
emailContent to = ContentEmail
  { to: [to]
  , cc: []
  , bcc: []
  , subject: Nothing
  , body: Nothing
  }

-- | Create email with subject
emailWithSubject :: String -> String -> QRContent
emailWithSubject to subject = ContentEmail
  { to: [to]
  , cc: []
  , bcc: []
  , subject: Just subject
  , body: Nothing
  }

-- | Create email with body
emailWithBody :: String -> String -> String -> QRContent
emailWithBody to subject body = ContentEmail
  { to: [to]
  , cc: []
  , bcc: []
  , subject: Just subject
  , body: Just body
  }

-- | Create full email configuration
emailFull :: Array String -> Array String -> Array String -> Maybe String -> Maybe String -> QRContent
emailFull to cc bcc subject body = ContentEmail { to, cc, bcc, subject, body }

-- | Encode email to mailto: URI
encodeEmail :: EmailContent -> String
encodeEmail c =
  let
    recipients = joinWith "," c.to
    params = filter (\(Tuple _ v) -> v /= "")
      [ Tuple "cc" (joinWith "," c.cc)
      , Tuple "bcc" (joinWith "," c.bcc)
      , Tuple "subject" (maybe "" encodeURIComponent c.subject)
      , Tuple "body" (maybe "" encodeURIComponent c.body)
      ]
    paramStr = if length params == 0
      then ""
      else "?" <> joinWith "&" (map (\(Tuple k v) -> k <> "=" <> v) params)
  in
    "mailto:" <> recipients <> paramStr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // phone content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Phone content configuration.
type PhoneContent =
  { number :: String  -- ^ Phone number (with country code)
  }

-- | Create phone content
phoneContent :: String -> QRContent
phoneContent number = ContentPhone { number }

-- | Encode phone to tel: URI
encodePhone :: PhoneContent -> String
encodePhone c = "tel:" <> c.number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // sms content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SMS content configuration.
type SMSContent =
  { number :: String       -- ^ Phone number
  , body :: Maybe String   -- ^ Pre-filled message
  }

-- | Create SMS content
smsContent :: String -> QRContent
smsContent number = ContentSMS { number, body: Nothing }

-- | Create SMS with pre-filled body
smsWithBody :: String -> String -> QRContent
smsWithBody number body = ContentSMS { number, body: Just body }

-- | Encode SMS to sms: URI
encodeSMS :: SMSContent -> String
encodeSMS c =
  let
    base = "sms:" <> c.number
    bodyParam = maybe "" (\b -> "?body=" <> encodeURIComponent b) c.body
  in
    base <> bodyParam

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // wifi content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | WiFi security type.
data WiFiSecurity
  = WEP
  | WPA
  | WPA2
  | WPA3
  | NoPassword

derive instance eqWiFiSecurity :: Eq WiFiSecurity

instance showWiFiSecurity :: Show WiFiSecurity where
  show WEP = "WEP"
  show WPA = "WPA"
  show WPA2 = "WPA2"
  show WPA3 = "WPA3"
  show NoPassword = "nopass"

-- | WiFi content configuration.
type WiFiContent =
  { ssid :: String            -- ^ Network name
  , password :: Maybe String  -- ^ Network password
  , security :: WiFiSecurity  -- ^ Security type
  , hidden :: Boolean         -- ^ Is network hidden?
  }

-- | Create WiFi content
wifiContent :: String -> String -> WiFiSecurity -> QRContent
wifiContent ssid password security = ContentWiFi
  { ssid
  , password: Just password
  , security
  , hidden: false
  }

-- | Create hidden WiFi content
wifiHidden :: String -> String -> WiFiSecurity -> QRContent
wifiHidden ssid password security = ContentWiFi
  { ssid
  , password: Just password
  , security
  , hidden: true
  }

-- | Encode WiFi to WIFI: format
-- |
-- | Format: WIFI:T:WPA;S:NetworkName;P:password;H:true;;
encodeWiFi :: WiFiContent -> String
encodeWiFi c =
  let
    secType = case c.security of
      WEP -> "WEP"
      WPA -> "WPA"
      WPA2 -> "WPA"  -- WPA2 uses same tag as WPA
      WPA3 -> "WPA"  -- WPA3 uses same tag
      NoPassword -> "nopass"
    escapedSSID = escapeWiFiSpecial c.ssid
    escapedPass = maybe "" escapeWiFiSpecial c.password
    hiddenStr = if c.hidden then "H:true;" else ""
  in
    "WIFI:T:" <> secType <> ";S:" <> escapedSSID <> ";P:" <> escapedPass <> ";" <> hiddenStr <> ";"

-- | Escape special characters in WiFi strings
escapeWiFiSpecial :: String -> String
escapeWiFiSpecial s =
  replaceAll (Pattern "\\") (Replacement "\\\\")
    (replaceAll (Pattern ";") (Replacement "\\;")
      (replaceAll (Pattern ",") (Replacement "\\,")
        (replaceAll (Pattern "\"") (Replacement "\\\"")
          (replaceAll (Pattern ":") (Replacement "\\:") s))))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // vcard content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | vCard content configuration.
type VCardContent =
  { firstName :: String
  , lastName :: String
  , organization :: Maybe String
  , title :: Maybe String
  , email :: Maybe String
  , phone :: Maybe String
  , mobile :: Maybe String
  , address :: Maybe String
  , website :: Maybe String
  , note :: Maybe String
  }

-- | Create simple vCard
vCardContent :: String -> String -> QRContent
vCardContent firstName lastName = ContentVCard
  { firstName
  , lastName
  , organization: Nothing
  , title: Nothing
  , email: Nothing
  , phone: Nothing
  , mobile: Nothing
  , address: Nothing
  , website: Nothing
  , note: Nothing
  }

-- | Create full vCard
vCardFull :: String -> String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> QRContent
vCardFull firstName lastName organization title email phone mobile address website note = ContentVCard
  { firstName, lastName, organization, title, email, phone, mobile, address, website, note }

-- | Encode vCard to vCard 3.0 format
encodeVCard :: VCardContent -> String
encodeVCard c =
  let
    lines =
      [ "BEGIN:VCARD"
      , "VERSION:3.0"
      , "N:" <> c.lastName <> ";" <> c.firstName <> ";;;"
      , "FN:" <> c.firstName <> " " <> c.lastName
      ] <>
      maybe [] (\o -> ["ORG:" <> o]) c.organization <>
      maybe [] (\t -> ["TITLE:" <> t]) c.title <>
      maybe [] (\e -> ["EMAIL:" <> e]) c.email <>
      maybe [] (\p -> ["TEL;TYPE=WORK:" <> p]) c.phone <>
      maybe [] (\m -> ["TEL;TYPE=CELL:" <> m]) c.mobile <>
      maybe [] (\a -> ["ADR;TYPE=WORK:;;" <> a]) c.address <>
      maybe [] (\w -> ["URL:" <> w]) c.website <>
      maybe [] (\n -> ["NOTE:" <> n]) c.note <>
      [ "END:VCARD" ]
  in
    joinWith "\n" lines

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // calendar content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calendar event content configuration.
-- |
-- | For full calendar integration, use Schema.Scheduling.Event
-- | This is a simplified version for QR encoding.
type CalendarContent =
  { title :: String
  , description :: Maybe String
  , location :: Maybe String
  , startDate :: String         -- ^ ISO 8601 format: 20260224T150000Z
  , endDate :: String           -- ^ ISO 8601 format
  , allDay :: Boolean
  }

-- | Create calendar event content
calendarContent :: String -> String -> String -> QRContent
calendarContent title startDate endDate = ContentCalendar
  { title
  , description: Nothing
  , location: Nothing
  , startDate
  , endDate
  , allDay: false
  }

-- | Encode calendar to vEvent format
encodeCalendar :: CalendarContent -> String
encodeCalendar c =
  let
    lines =
      [ "BEGIN:VCALENDAR"
      , "VERSION:2.0"
      , "BEGIN:VEVENT"
      , "SUMMARY:" <> c.title
      , "DTSTART:" <> c.startDate
      , "DTEND:" <> c.endDate
      ] <>
      maybe [] (\d -> ["DESCRIPTION:" <> d]) c.description <>
      maybe [] (\l -> ["LOCATION:" <> l]) c.location <>
      [ "END:VEVENT"
      , "END:VCALENDAR"
      ]
  in
    joinWith "\n" lines

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // geo content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geographic location content.
type GeoContent =
  { latitude :: Number
  , longitude :: Number
  , altitude :: Maybe Number
  , query :: Maybe String      -- ^ Search query / place name
  }

-- | Create geo content
geoContent :: Number -> Number -> QRContent
geoContent latitude longitude = ContentGeo
  { latitude, longitude, altitude: Nothing, query: Nothing }

-- | Create geo content with altitude
geoWithAltitude :: Number -> Number -> Number -> QRContent
geoWithAltitude latitude longitude altitude = ContentGeo
  { latitude, longitude, altitude: Just altitude, query: Nothing }

-- | Create geo content with query
geoWithQuery :: Number -> Number -> String -> QRContent
geoWithQuery latitude longitude query = ContentGeo
  { latitude, longitude, altitude: Nothing, query: Just query }

-- | Encode geo to geo: URI
encodeGeo :: GeoContent -> String
encodeGeo c =
  let
    base = "geo:" <> show c.latitude <> "," <> show c.longitude
    altStr = maybe "" (\a -> "," <> show a) c.altitude
    queryStr = maybe "" (\q -> "?q=" <> encodeURIComponent q) c.query
  in
    base <> altStr <> queryStr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // bitcoin content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bitcoin payment content.
type BitcoinContent =
  { address :: String
  , amount :: Maybe Number     -- ^ Amount in BTC
  , label :: Maybe String      -- ^ Recipient label
  , message :: Maybe String    -- ^ Payment message
  }

-- | Create bitcoin content
bitcoinContent :: String -> QRContent
bitcoinContent address = ContentBitcoin
  { address, amount: Nothing, label: Nothing, message: Nothing }

-- | Create bitcoin with amount
bitcoinWithAmount :: String -> Number -> QRContent
bitcoinWithAmount address amount = ContentBitcoin
  { address, amount: Just amount, label: Nothing, message: Nothing }

-- | Create full bitcoin content
bitcoinFull :: String -> Maybe Number -> Maybe String -> Maybe String -> QRContent
bitcoinFull address amount label message = ContentBitcoin
  { address, amount, label, message }

-- | Encode bitcoin to bitcoin: URI
encodeBitcoin :: BitcoinContent -> String
encodeBitcoin c =
  let
    params = filter (\(Tuple _ v) -> v /= "")
      [ Tuple "amount" (maybe "" show c.amount)
      , Tuple "label" (maybe "" encodeURIComponent c.label)
      , Tuple "message" (maybe "" encodeURIComponent c.message)
      ]
    paramStr = if length params == 0
      then ""
      else "?" <> joinWith "&" (map (\(Tuple k v) -> k <> "=" <> v) params)
  in
    "bitcoin:" <> c.address <> paramStr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // slack content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Slack action type.
data SlackAction
  = SlackOpenChannel         -- ^ Just open the channel
  | SlackComposeMessage      -- ^ Open composer
  | SlackTriggerWorkflow     -- ^ Trigger a workflow

derive instance eqSlackAction :: Eq SlackAction

instance showSlackAction :: Show SlackAction where
  show SlackOpenChannel = "open"
  show SlackComposeMessage = "compose"
  show SlackTriggerWorkflow = "workflow"

-- | Slack deep link content.
type SlackContent =
  { workspace :: String        -- ^ Workspace ID or name
  , channel :: Maybe String    -- ^ Channel name (without #)
  , user :: Maybe String       -- ^ User ID for DM
  , message :: Maybe String    -- ^ Pre-filled message
  , action :: SlackAction
  }

-- | Create Slack channel link
slackChannel :: String -> String -> QRContent
slackChannel workspace channel = ContentSlack
  { workspace
  , channel: Just channel
  , user: Nothing
  , message: Nothing
  , action: SlackOpenChannel
  }

-- | Create Slack DM link
slackUser :: String -> String -> QRContent
slackUser workspace user = ContentSlack
  { workspace
  , channel: Nothing
  , user: Just user
  , message: Nothing
  , action: SlackOpenChannel
  }

-- | Create Slack compose link
slackCompose :: String -> String -> String -> QRContent
slackCompose workspace channel message = ContentSlack
  { workspace
  , channel: Just channel
  , user: Nothing
  , message: Just message
  , action: SlackComposeMessage
  }

-- | Encode Slack to slack:// URI
encodeSlack :: SlackContent -> String
encodeSlack c =
  let
    base = "slack://channel?team=" <> c.workspace
    channelPart = maybe "" (\ch -> "&id=" <> ch) c.channel
    userPart = maybe "" (\u -> "&id=" <> u) c.user
    -- Note: Slack deep links have limited support for pre-filled messages
    -- This is a best-effort encoding
  in
    base <> channelPart <> userPart

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // webhook content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HTTP method for webhooks.
data HTTPMethod
  = GET
  | POST
  | PUT
  | DELETE
  | PATCH

derive instance eqHTTPMethod :: Eq HTTPMethod

instance showHTTPMethod :: Show HTTPMethod where
  show GET = "GET"
  show POST = "POST"
  show PUT = "PUT"
  show DELETE = "DELETE"
  show PATCH = "PATCH"

-- | Webhook trigger content.
-- |
-- | Note: QR codes can only encode URLs. The actual webhook triggering
-- | happens when the user opens the URL, which should point to a service
-- | that performs the webhook call (e.g., a serverless function).
type WebhookContent =
  { url :: String
  , method :: HTTPMethod
  , description :: String      -- ^ Human-readable description of what happens
  }

-- | Create GET webhook
webhookGet :: String -> String -> QRContent
webhookGet url description = ContentWebhook
  { url, method: GET, description }

-- | Create POST webhook
webhookPost :: String -> String -> QRContent
webhookPost url description = ContentWebhook
  { url, method: POST, description }

-- | Encode webhook to URL
-- |
-- | The URL should be a trigger endpoint that performs the actual webhook.
encodeWebhook :: WebhookContent -> String
encodeWebhook c = c.url

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // deep link content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | App deep link content.
type DeepLinkContent =
  { scheme :: String           -- ^ App URL scheme (e.g., "myapp://")
  , path :: String             -- ^ Path within the app
  , params :: Array (Tuple String String)  -- ^ Query parameters
  , fallbackURL :: Maybe String  -- ^ Web fallback if app not installed
  }

-- | Create simple deep link
deepLink :: String -> String -> QRContent
deepLink scheme path = ContentDeepLink
  { scheme, path, params: [], fallbackURL: Nothing }

-- | Create deep link with fallback
deepLinkWithFallback :: String -> String -> String -> QRContent
deepLinkWithFallback scheme path fallback = ContentDeepLink
  { scheme, path, params: [], fallbackURL: Just fallback }

-- | Encode deep link to URI
encodeDeepLink :: DeepLinkContent -> String
encodeDeepLink c =
  let
    base = c.scheme <> c.path
    paramStr = if length c.params == 0
      then ""
      else "?" <> joinWith "&" (map (\(Tuple k v) -> k <> "=" <> encodeURIComponent v) c.params)
  in
    base <> paramStr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // text content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create plain text content
textContent :: String -> QRContent
textContent = ContentText

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | URI encode a string component.
-- |
-- | This is a pure PureScript implementation of URI encoding.
-- | Encodes all characters except: A-Z a-z 0-9 - _ . ~
encodeURIComponent :: String -> String
encodeURIComponent s =
  -- For now, a simplified encoding that handles common special characters
  -- A full implementation would handle all non-unreserved characters
  replaceAll (Pattern " ") (Replacement "%20")
    (replaceAll (Pattern "&") (Replacement "%26")
      (replaceAll (Pattern "=") (Replacement "%3D")
        (replaceAll (Pattern "?") (Replacement "%3F")
          (replaceAll (Pattern "#") (Replacement "%23")
            (replaceAll (Pattern "+") (Replacement "%2B")
              (replaceAll (Pattern "\n") (Replacement "%0A")
                (replaceAll (Pattern "\r") (Replacement "%0D") s)))))))
