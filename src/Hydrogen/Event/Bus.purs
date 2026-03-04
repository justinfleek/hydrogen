-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // event // bus
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Type-safe event bus for pub/sub communication
-- |
-- | The event bus provides a decoupled communication mechanism between
-- | components. Events are typed and can carry arbitrary payloads.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Event.Bus as Bus
-- |
-- | -- Define your events
-- | data AppEvent
-- |   = UserLoggedIn User
-- |   | CartUpdated Cart
-- |   | ThemeChanged Theme
-- |
-- | -- Create an event bus
-- | bus <- Bus.create
-- |
-- | -- Subscribe to events
-- | unsubscribe <- Bus.subscribe bus \event -> case event of
-- |   UserLoggedIn user -> Console.log $ "Welcome " <> user.name
-- |   CartUpdated cart -> updateCartUI cart
-- |   ThemeChanged theme -> applyTheme theme
-- |
-- | -- Emit events
-- | Bus.emit bus (UserLoggedIn { name: "Alice" })
-- |
-- | -- Clean up
-- | unsubscribe
-- | ```
module Hydrogen.Event.Bus
  ( -- * Event Bus
    EventBus
  , Subscriber
  , create
  , createNamed
  , createWithDebug
    -- * Subscriptions
  , subscribe
  , subscribeOnce
  , subscribeWithFilter
  , unsubscribeAll
    -- * Emitting
  , emit
  , emitAsync
  , emitDelayed
    -- * Server Sync (Query Integration)
  , emitToServer
  , subscribeFromServer
  , loadEventHistory
  , invalidateEventCache
    -- * Channels
  , Channel
  , channel
  , channelNamed
  , onChannel
  , emitToChannel
    -- * History
  , History
  , withHistory
  , withHistoryAndDebug
  , getHistory
  , clearHistory
  , replay
    -- * Debugging
  , getSubscriberCount
  ) where

import Prelude 
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , bind
  , discard
  , flip
  , not
  , pure
  , show
  , unit
  , void
  , ($)
  , (<$>)
  , (<>)
  , (+)
  , (==)
  , (/=)
  , (>)
  )

import Control.Monad (unless, when)
import Data.Argonaut.Decode (class DecodeJson)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Array as Array
import Data.DateTime.Instant (unInstant) as Instant
import Data.Either (Either)
import Data.Functor (map) as Functor
import Data.Maybe (Maybe(Just, Nothing))
import Data.Time.Duration (Milliseconds(Milliseconds)) as Duration
import Data.Traversable (traverse) as Traversable
import Effect (Effect)
import Effect.Aff (Aff, Milliseconds(Milliseconds), delay)
import Effect.Class (liftEffect)
import Effect.Console as Console
import Effect.Now (now) as Now
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Hydrogen.API.Client as Api
import Hydrogen.Data.RemoteData (RemoteData(Success))
import Hydrogen.Query as Q

-- ═════════════════════════════════════════════════════════════════════════════
-- Event Bus Core
-- ═════════════════════════════════════════════════════════════════════════════

-- | An event bus for type-safe pub/sub
-- |
-- | The debugHandler field enables structured debug output following
-- | SHOW_DEBUG_CONVENTION. When set, every emitted event is logged
-- | in format: `(EventBus:name event:value)`
type EventBus a =
  { name :: Maybe String
  , subscribers :: Ref (Array (Subscriber a))
  , nextId :: Ref Int
  , history :: Maybe (History a)
  , debugHandler :: Maybe (a -> Effect Unit)
  , queryClient :: Q.QueryClient
  }

-- | A subscriber with metadata
type Subscriber a =
  { id :: Int
  , handler :: a -> Effect Unit
  , once :: Boolean
  , filter :: Maybe (a -> Boolean)
  }

-- | Create a new event bus
create :: forall a. Effect (EventBus a)
create = do
  subscribers <- Ref.new []
  nextId <- Ref.new 0
  queryClient <- Q.newClient
  pure
    { name: Nothing
    , subscribers
    , nextId
    , history: Nothing
    , debugHandler: Nothing
    , queryClient
    }

-- | Create a named event bus (useful for debugging)
createNamed :: forall a. String -> Effect (EventBus a)
createNamed busName = do
  bus <- create
  pure bus { name = Just busName }

-- | Create a named event bus with debug logging enabled
-- |
-- | Requires Show constraint because debug output follows SHOW_DEBUG_CONVENTION:
-- | `(EventBus:busName event:eventValue)`
-- |
-- | ## Example
-- |
-- | ```purescript
-- | bus <- Bus.createWithDebug "user-events"
-- | Bus.emit bus (UserLoggedIn { name: "Alice" })
-- | -- Console: (EventBus:user-events event:(UserLoggedIn {name:"Alice"}))
-- | ```
createWithDebug :: forall a. Show a => String -> Effect (EventBus a)
createWithDebug busName = do
  bus <- create
  pure bus 
    { name = Just busName
    , debugHandler = Just (logEventDebug busName)
    }

-- | Pure debug logger following SHOW_DEBUG_CONVENTION
-- |
-- | Format: `(EventBus:busName event:eventValue)`
logEventDebug :: forall a. Show a => String -> a -> Effect Unit
logEventDebug busName event =
  Console.log $ "(EventBus:" <> busName <> " event:" <> show event <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
-- Subscriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subscribe to events on the bus
-- | Returns an unsubscribe function
subscribe :: forall a. EventBus a -> (a -> Effect Unit) -> Effect (Effect Unit)
subscribe bus handler = do
  id <- Ref.read bus.nextId
  Ref.write (id + 1) bus.nextId
  
  let subscriber = { id, handler, once: false, filter: Nothing }
  Ref.modify_ (flip Array.snoc subscriber) bus.subscribers
  
  -- Return unsubscribe function
  pure $ unsubscribe bus id

-- | Subscribe to a single event, then automatically unsubscribe
subscribeOnce :: forall a. EventBus a -> (a -> Effect Unit) -> Effect (Effect Unit)
subscribeOnce bus handler = do
  id <- Ref.read bus.nextId
  Ref.write (id + 1) bus.nextId
  
  let subscriber = { id, handler, once: true, filter: Nothing }
  Ref.modify_ (flip Array.snoc subscriber) bus.subscribers
  
  pure $ unsubscribe bus id

-- | Subscribe with a filter predicate
-- | Handler only called when filter returns true
subscribeWithFilter
  :: forall a
   . EventBus a
  -> (a -> Boolean)
  -> (a -> Effect Unit)
  -> Effect (Effect Unit)
subscribeWithFilter bus predicate handler = do
  id <- Ref.read bus.nextId
  Ref.write (id + 1) bus.nextId
  
  let subscriber = { id, handler, once: false, filter: Just predicate }
  Ref.modify_ (flip Array.snoc subscriber) bus.subscribers
  
  pure $ unsubscribe bus id

-- | Internal unsubscribe by ID
unsubscribe :: forall a. EventBus a -> Int -> Effect Unit
unsubscribe bus id = do
  Ref.modify_ (Array.filter (\s -> s.id /= id)) bus.subscribers

-- | Remove all subscribers
unsubscribeAll :: forall a. EventBus a -> Effect Unit
unsubscribeAll bus = Ref.write [] bus.subscribers

-- ═════════════════════════════════════════════════════════════════════════════
-- Emitting Events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emit an event to all subscribers
emit :: forall a. EventBus a -> a -> Effect Unit
emit bus event = do
  -- Record in history if enabled
  case bus.history of
    Just h -> recordEvent h event
    Nothing -> pure unit
  
  -- Debug logging (pure, uses Show constraint captured at bus creation)
  case bus.debugHandler of
    Just handler -> handler event
    Nothing -> pure unit
  
  -- Get current subscribers
  subs <- Ref.read bus.subscribers
  
  -- Call matching handlers
  let 
    matchingSubs = Array.filter (shouldHandle event) subs
    onceSubs = Array.filter _.once matchingSubs
  
  -- Remove one-time subscribers
  unless (Array.null onceSubs) do
    let onceIds = map _.id onceSubs
    Ref.modify_ (Array.filter (\s -> not (Array.elem s.id onceIds))) bus.subscribers
  
  -- Invoke handlers
  for_ matchingSubs \sub -> sub.handler event
  where
  shouldHandle :: a -> Subscriber a -> Boolean
  shouldHandle e sub = case sub.filter of
    Nothing -> true
    Just f -> f e
  
  for_ :: forall b. Array b -> (b -> Effect Unit) -> Effect Unit
  for_ arr f = void $ traverse f arr
  
  traverse :: forall b c. (b -> Effect c) -> Array b -> Effect (Array c)
  traverse = Traversable.traverse

-- | Emit an event asynchronously (non-blocking)
emitAsync :: forall a. EventBus a -> a -> Aff Unit
emitAsync bus event = liftEffect $ emit bus event

-- | Emit an event after a delay
emitDelayed :: forall a. EventBus a -> Milliseconds -> a -> Aff Unit
emitDelayed bus (Milliseconds ms) event = do
  delay (Milliseconds ms)
  liftEffect $ emit bus event

-- ═════════════════════════════════════════════════════════════════════════════
-- Channels (Namespaced Events)
-- ═════════════════════════════════════════════════════════════════════════════

-- | A named channel for organizing events
newtype Channel = Channel String

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

instance showChannel :: Show Channel where
  show (Channel name) = "Channel(" <> name <> ")"

-- | Create a channel
channel :: String -> Channel
channel = Channel

-- | Create a named channel (alias)
channelNamed :: String -> Channel
channelNamed = Channel

-- | Channeled event wrapper
type ChanneledEvent a =
  { channel :: Channel
  , payload :: a
  }

-- | Subscribe to a specific channel
onChannel
  :: forall a
   . EventBus (ChanneledEvent a)
  -> Channel
  -> (a -> Effect Unit)
  -> Effect (Effect Unit)
onChannel bus ch handler =
  subscribeWithFilter bus
    (\e -> e.channel == ch)
    (\e -> handler e.payload)

-- | Emit to a specific channel
emitToChannel :: forall a. EventBus (ChanneledEvent a) -> Channel -> a -> Effect Unit
emitToChannel bus ch payload =
  emit bus { channel: ch, payload }

-- ═════════════════════════════════════════════════════════════════════════════
-- History
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event history for replay/debugging
type History a =
  { events :: Ref (Array { event :: a, timestamp :: Number })
  , maxSize :: Int
  }

-- | Create a bus with history tracking
withHistory :: forall a. Int -> Effect (EventBus a)
withHistory maxSize = do
  bus <- create
  events <- Ref.new []
  pure bus { history = Just { events, maxSize } }

-- | Create a bus with history tracking and debug logging
-- |
-- | Combines history tracking with SHOW_DEBUG_CONVENTION output.
-- | Useful for debugging event sequences over time.
withHistoryAndDebug :: forall a. Show a => String -> Int -> Effect (EventBus a)
withHistoryAndDebug busName maxSize = do
  bus <- createWithDebug busName
  events <- Ref.new []
  pure bus { history = Just { events, maxSize } }

-- | Record an event in history
recordEvent :: forall a. History a -> a -> Effect Unit
recordEvent history event = do
  timestamp <- nowImpl
  Ref.modify_ (\arr ->
    let newArr = Array.snoc arr { event, timestamp }
    in if Array.length newArr > history.maxSize
       then Array.drop 1 newArr
       else newArr
  ) history.events

-- | Get current timestamp in milliseconds (pure implementation)
nowImpl :: Effect Number
nowImpl = do
  instant <- Now.now
  let Duration.Milliseconds ms = Instant.unInstant instant
  pure ms

-- | Get the event history
getHistory :: forall a. EventBus a -> Effect (Array { event :: a, timestamp :: Number })
getHistory bus = case bus.history of
  Just h -> Ref.read h.events
  Nothing -> pure []

-- | Clear the event history
clearHistory :: forall a. EventBus a -> Effect Unit
clearHistory bus = case bus.history of
  Just h -> Ref.write [] h.events
  Nothing -> pure unit

-- | Replay all events in history to a handler
replay :: forall a. EventBus a -> (a -> Effect Unit) -> Effect Unit
replay bus handler = do
  events <- getHistory bus
  for_ events \{ event } -> handler event
  where
  for_ :: forall b. Array b -> (b -> Effect Unit) -> Effect Unit
  for_ arr f = void $ Traversable.traverse f arr

-- ═════════════════════════════════════════════════════════════════════════════
-- Debugging
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the number of active subscribers
getSubscriberCount :: forall a. EventBus a -> Effect Int
getSubscriberCount bus = Array.length <$> Ref.read bus.subscribers

-- ═════════════════════════════════════════════════════════════════════════════
-- Server Sync (Query Integration)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emit an event to the server with Query caching
-- |
-- | ```purescript
-- | result <- Bus.emitToServer bus apiConfig "/api/events/room123" event
-- | case result of
-- |   Right _ -> Console.log "Event sent to server"
-- |   Left err -> Console.error err
-- | ```
emitToServer 
  :: forall a
   . EncodeJson a
  => DecodeJson a
  => EventBus a 
  -> Api.ApiConfig 
  -> String 
  -> a 
  -> Aff (Either String a)
emitToServer bus apiConfig path event = do
  -- Emit locally first
  liftEffect $ emit bus event
  -- Send to server
  Api.post apiConfig path event

-- | Subscribe to events from a server endpoint (via polling)
-- |
-- | ```purescript
-- | unsub <- Bus.subscribeFromServer bus apiConfig "/api/events/room123" 5000
-- | ```
subscribeFromServer 
  :: forall a
   . DecodeJson a
  => EncodeJson a
  => EventBus a 
  -> Api.ApiConfig 
  -> String 
  -> Duration.Milliseconds
  -> Aff (Effect Unit)
subscribeFromServer bus apiConfig path pollInterval = do
  -- Initial fetch
  result <- Q.query bus.queryClient
    { key: ["event", "bus", path]
    , fetch: Api.get apiConfig path
    , staleTime: Just pollInterval
    , retry: 1
    , retryDelay: Duration.Milliseconds 1000.0
    }
  
  -- Process fetched events
  case result.data of
    Success events -> liftEffect $ emitFetchedEvents bus events
    _ -> pure unit
  
  -- Return invalidation function (caller can use for cleanup)
  pure $ Q.invalidate bus.queryClient ["event", "bus", path]

-- | Helper to emit fetched events locally
emitFetchedEvents :: forall a. EventBus a -> Array a -> Effect Unit
emitFetchedEvents bus events = 
  for_ events \event -> emit bus event
  where
  for_ arr f = void $ Traversable.traverse f arr

-- | Load event history from server with Query caching
-- |
-- | ```purescript
-- | state <- Bus.loadEventHistory bus apiConfig "/api/events/room123/history"
-- | case state.data of
-- |   Success history -> Console.log $ "Loaded " <> show (Array.length history) <> " events"
-- |   Failure e -> Console.error e
-- |   _ -> pure unit
-- | ```
loadEventHistory 
  :: forall a
   . DecodeJson (Array a)
  => EncodeJson (Array a)
  => EventBus a 
  -> Api.ApiConfig 
  -> String 
  -> Aff (Q.QueryState String (Array a))
loadEventHistory bus apiConfig path = 
  Q.query bus.queryClient
    { key: ["event", "history", path]
    , fetch: Api.get apiConfig path
    , staleTime: Nothing
    , retry: 1
    , retryDelay: Duration.Milliseconds 1000.0
    }

-- | Invalidate cached event history (forces fresh fetch on next load)
invalidateEventCache :: forall a. EventBus a -> String -> Effect Unit
invalidateEventCache bus path = 
  Q.invalidate bus.queryClient ["event", "history", path]

-- ═════════════════════════════════════════════════════════════════════════════
-- Utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- Note: Using Control.Monad.when and Control.Monad.unless from standard library

-- | Map function for arrays (pure implementation)
map :: forall a b. (a -> b) -> Array a -> Array b
map = Functor.map
