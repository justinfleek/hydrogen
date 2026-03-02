-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // navigation // history
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navigation History — Back/forward stack for browser-like navigation.
-- |
-- | ## Design Philosophy
-- |
-- | Navigation history is fundamental to user experience. Users expect:
-- | - Back button always works (unless at start)
-- | - Forward button works after going back
-- | - Navigation to new location clears forward stack
-- | - History has bounded depth (prevent memory exhaustion)
-- |
-- | ## Bounded History
-- |
-- | Unbounded history is a memory exhaustion attack vector. A malicious
-- | entity could navigate rapidly to exhaust memory. We bound:
-- | - Back stack: max 100 entries (configurable)
-- | - Forward stack: max 100 entries
-- | - When exceeded, oldest entries are dropped
-- |
-- | ## Deterministic Identity
-- |
-- | Each history entry has a UUID5 derived from:
-- | - Entry content (location data)
-- | - Timestamp (for ordering)
-- | - Parent entry ID (for chain integrity)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Array (stack operations)
-- | - Data.Maybe (optional navigation)
-- | - Hydrogen.Schema.Bounded (clampInt)
-- |
-- | ## Dependents
-- |
-- | - Router (browser history integration)
-- | - Navigation.Index (position in history)
-- | - WorldModel (entity navigation state)

module Hydrogen.Schema.Navigation.History
  ( -- * History Entry
    HistoryEntry
  , historyEntry
  , entryId
  , entryLocation
  , entryTimestamp
  , entryTitle
  
  -- * History Stack Depth
  , HistoryDepth(HistoryDepth)
  , historyDepth
  , unwrapHistoryDepth
  , historyDepthBounds
  , defaultHistoryDepth
  , minHistoryDepth
  , maxHistoryDepth
  
  -- * Navigation History (Compound)
  , NavigationHistory
  , emptyHistory
  , historyWithDepth
  
  -- * Navigation State
  , currentEntry
  , canGoBack
  , canGoForward
  , backStackSize
  , forwardStackSize
  , totalHistorySize
  
  -- * Navigation Operations
  , navigateTo
  , goBack
  , goForward
  , goBackN
  , goForwardN
  
  -- * Stack Access
  , peekBack
  , peekForward
  , backStack
  , forwardStack
  
  -- * History Management
  , clearHistory
  , clearForward
  , truncateHistory
  , replaceCurrentEntry
  
  -- * Queries
  , findInHistory
  , historyContains
  , historyIndex
  
  -- * Transformations
  , mapHistory
  , mapEntries
  , filterHistory
  , filterByTimestamp
  , entriesInRange
  
  -- * Predicates
  , isEmpty
  , isFull
  , hasForwardHistory
  , isAtStart
  , isAtEnd
  
  -- * Comparisons
  , newerThan
  , olderThan
  , sameLocation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , pure
  , map
  , otherwise
  , (==)
  , (/=)
  , (<>)
  , (-)
  , (+)
  , (>)
  , (>=)
  , (<=)
  , (<)
  , (&&)
  , ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps)) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // history entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single entry in navigation history.
-- |
-- | Each entry represents a visited location with metadata.
-- | The ID is derived from content for deterministic identity.
type HistoryEntry =
  { id :: Int           -- Sequential ID within this history (for ordering)
  , location :: String  -- Location identifier (URL, route, etc.)
  , timestamp :: Int    -- Unix timestamp of visit
  , title :: String     -- Human-readable title
  }

-- | Create a history entry.
historyEntry :: Int -> String -> Int -> String -> HistoryEntry
historyEntry id location timestamp title =
  { id
  , location
  , timestamp
  , title
  }

-- | Get entry ID.
entryId :: HistoryEntry -> Int
entryId e = e.id

-- | Get entry location.
entryLocation :: HistoryEntry -> String
entryLocation e = e.location

-- | Get entry timestamp.
entryTimestamp :: HistoryEntry -> Int
entryTimestamp e = e.timestamp

-- | Get entry title.
entryTitle :: HistoryEntry -> String
entryTitle e = e.title

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // history depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum history stack depth [10, 1000].
-- |
-- | Controls how many entries are kept in back/forward stacks.
-- | Lower values save memory, higher values allow deeper navigation.
newtype HistoryDepth = HistoryDepth Int

derive instance eqHistoryDepth :: Eq HistoryDepth
derive instance ordHistoryDepth :: Ord HistoryDepth

instance showHistoryDepth :: Show HistoryDepth where
  show (HistoryDepth n) = "depth " <> show n

-- | Create history depth (clamps to [10, 1000]).
historyDepth :: Int -> HistoryDepth
historyDepth n = HistoryDepth (Bounded.clampInt 10 1000 n)

-- | Unwrap history depth.
unwrapHistoryDepth :: HistoryDepth -> Int
unwrapHistoryDepth (HistoryDepth n) = n

-- | Bounds for HistoryDepth.
historyDepthBounds :: Bounded.IntBounds
historyDepthBounds = Bounded.intBounds 10 1000 Bounded.Clamps
  "historyDepth"
  "Maximum navigation history depth (10-1000)"

-- | Default history depth: 100 entries.
defaultHistoryDepth :: HistoryDepth
defaultHistoryDepth = HistoryDepth 100

-- | Minimum history depth: 10 entries.
minHistoryDepth :: HistoryDepth
minHistoryDepth = HistoryDepth 10

-- | Maximum history depth: 1000 entries.
maxHistoryDepth :: HistoryDepth
maxHistoryDepth = HistoryDepth 1000

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // navigation history
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete navigation history state (Compound).
-- |
-- | Contains:
-- | - Current entry (where user is now)
-- | - Back stack (entries behind current)
-- | - Forward stack (entries ahead, after going back)
-- | - Maximum depth configuration
-- | - Next ID for new entries
type NavigationHistory =
  { current :: Maybe HistoryEntry  -- Current location (Nothing = fresh start)
  , back :: Array HistoryEntry     -- Back stack (newest first)
  , forward :: Array HistoryEntry  -- Forward stack (nearest first)
  , maxDepth :: HistoryDepth       -- Maximum stack depth
  , nextId :: Int                  -- Next entry ID
  }

-- | Create empty history with default depth.
emptyHistory :: NavigationHistory
emptyHistory = historyWithDepth defaultHistoryDepth

-- | Create empty history with specified depth.
historyWithDepth :: HistoryDepth -> NavigationHistory
historyWithDepth depth =
  { current: Nothing
  , back: []
  , forward: []
  , maxDepth: depth
  , nextId: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // navigation state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current entry (if any).
currentEntry :: NavigationHistory -> Maybe HistoryEntry
currentEntry h = h.current

-- | Can navigate back?
canGoBack :: NavigationHistory -> Boolean
canGoBack h = Array.length h.back > 0

-- | Can navigate forward?
canGoForward :: NavigationHistory -> Boolean
canGoForward h = Array.length h.forward > 0

-- | Number of entries in back stack.
backStackSize :: NavigationHistory -> Int
backStackSize h = Array.length h.back

-- | Number of entries in forward stack.
forwardStackSize :: NavigationHistory -> Int
forwardStackSize h = Array.length h.forward

-- | Total entries in history (including current).
totalHistorySize :: NavigationHistory -> Int
totalHistorySize h =
  let currentCount = case h.current of
        Nothing -> 0
        Just _ -> 1
  in currentCount + backStackSize h + forwardStackSize h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // navigation operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigate to a new location.
-- |
-- | - Current entry is pushed to back stack
-- | - Forward stack is cleared (navigating to new location discards forward history)
-- | - New entry becomes current
-- | - Back stack is truncated if exceeding max depth
navigateTo :: String -> Int -> String -> NavigationHistory -> NavigationHistory
navigateTo location timestamp title h =
  let
    -- Create new entry
    newEntry = historyEntry h.nextId location timestamp title
    
    -- Push current to back stack (if exists)
    newBack = case h.current of
      Nothing -> h.back
      Just curr -> Array.cons curr h.back
    
    -- Truncate back stack to max depth
    maxD = unwrapHistoryDepth h.maxDepth
    truncatedBack = Array.take maxD newBack
  in
    h { current = Just newEntry
      , back = truncatedBack
      , forward = []  -- Clear forward on new navigation
      , nextId = h.nextId + 1
      }

-- | Go back one entry.
-- |
-- | - Current moves to forward stack
-- | - First back entry becomes current
-- | - Returns unchanged if back stack is empty
goBack :: NavigationHistory -> NavigationHistory
goBack h = case Array.uncons h.back of
  Nothing -> h  -- Can't go back
  Just { head: prev, tail: restBack } ->
    let
      -- Push current to forward (if exists)
      newForward = case h.current of
        Nothing -> h.forward
        Just curr -> Array.cons curr h.forward
      
      -- Truncate forward stack
      maxD = unwrapHistoryDepth h.maxDepth
      truncatedForward = Array.take maxD newForward
    in
      h { current = Just prev
        , back = restBack
        , forward = truncatedForward
        }

-- | Go forward one entry.
-- |
-- | - Current moves to back stack
-- | - First forward entry becomes current
-- | - Returns unchanged if forward stack is empty
goForward :: NavigationHistory -> NavigationHistory
goForward h = case Array.uncons h.forward of
  Nothing -> h  -- Can't go forward
  Just { head: next, tail: restForward } ->
    let
      -- Push current to back (if exists)
      newBack = case h.current of
        Nothing -> h.back
        Just curr -> Array.cons curr h.back
      
      -- Truncate back stack
      maxD = unwrapHistoryDepth h.maxDepth
      truncatedBack = Array.take maxD newBack
    in
      h { current = Just next
        , back = truncatedBack
        , forward = restForward
        }

-- | Go back N entries.
-- |
-- | Stops at beginning of history if N exceeds back stack size.
goBackN :: Int -> NavigationHistory -> NavigationHistory
goBackN n h
  | n <= 0 = h
  | otherwise = goBackN (n - 1) (goBack h)

-- | Go forward N entries.
-- |
-- | Stops at end of forward stack if N exceeds size.
goForwardN :: Int -> NavigationHistory -> NavigationHistory
goForwardN n h
  | n <= 0 = h
  | otherwise = goForwardN (n - 1) (goForward h)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // stack access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Peek at next back entry without navigating.
peekBack :: NavigationHistory -> Maybe HistoryEntry
peekBack h = Array.head h.back

-- | Peek at next forward entry without navigating.
peekForward :: NavigationHistory -> Maybe HistoryEntry
peekForward h = Array.head h.forward

-- | Get entire back stack (newest first).
backStack :: NavigationHistory -> Array HistoryEntry
backStack h = h.back

-- | Get entire forward stack (nearest first).
forwardStack :: NavigationHistory -> Array HistoryEntry
forwardStack h = h.forward

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // history management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear all history (back and forward), keep current.
clearHistory :: NavigationHistory -> NavigationHistory
clearHistory h = h { back = [], forward = [] }

-- | Clear only forward stack.
clearForward :: NavigationHistory -> NavigationHistory
clearForward h = h { forward = [] }

-- | Truncate history to new depth.
-- |
-- | Useful if reducing maxDepth after configuration change.
truncateHistory :: HistoryDepth -> NavigationHistory -> NavigationHistory
truncateHistory newDepth h =
  let
    maxD = unwrapHistoryDepth newDepth
    newBack = Array.take maxD h.back
    newForward = Array.take maxD h.forward
  in
    h { maxDepth = newDepth
      , back = newBack
      , forward = newForward
      }

-- | Replace current entry without affecting stacks.
-- |
-- | Useful for URL updates that shouldn't create new history entry
-- | (e.g., query parameter changes, hash changes).
replaceCurrentEntry :: String -> Int -> String -> NavigationHistory -> NavigationHistory
replaceCurrentEntry location timestamp title h =
  let
    newId = case h.current of
      Nothing -> h.nextId
      Just curr -> curr.id
    newEntry = historyEntry newId location timestamp title
  in
    h { current = Just newEntry }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find an entry in history by location.
-- |
-- | Searches current, then back, then forward.
findInHistory :: String -> NavigationHistory -> Maybe HistoryEntry
findInHistory location h =
  case h.current of
    Just curr | curr.location == location -> Just curr
    _ -> case Array.find (\e -> e.location == location) h.back of
      Just e -> Just e
      Nothing -> Array.find (\e -> e.location == location) h.forward

-- | Check if history contains a location.
historyContains :: String -> NavigationHistory -> Boolean
historyContains location h = isJust (findInHistory location h)

-- | Get index of location in combined history.
-- |
-- | Returns position where 0 = oldest in back stack,
-- | backStackSize = current, backStackSize + 1 = first forward, etc.
-- | Returns Nothing if not found.
historyIndex :: String -> NavigationHistory -> Maybe Int
historyIndex location h =
  let
    backSize = backStackSize h
    -- Back stack is newest-first, so reverse for index calculation
    reversedBack = Array.reverse h.back
  in
    case Array.findIndex (\e -> e.location == location) reversedBack of
      Just i -> Just i
      Nothing -> 
        case h.current of
          Just curr | curr.location == location -> Just backSize
          _ -> case Array.findIndex (\e -> e.location == location) h.forward of
            Just i -> Just (backSize + 1 + i)
            Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over the current entry (if present).
-- |
-- | Useful for updating entry metadata without changing navigation state.
mapHistory :: (HistoryEntry -> HistoryEntry) -> NavigationHistory -> NavigationHistory
mapHistory f h = h { current = map f h.current }

-- | Map a function over ALL entries (current, back, forward).
-- |
-- | Useful for bulk updates like normalizing URLs or updating titles.
mapEntries :: (HistoryEntry -> HistoryEntry) -> NavigationHistory -> NavigationHistory
mapEntries f h =
  h { current = map f h.current
    , back = map f h.back
    , forward = map f h.forward
    }

-- | Filter history entries, keeping only those matching predicate.
-- |
-- | Current entry is kept if it matches, otherwise cleared.
-- | This is useful for removing entries matching certain criteria
-- | (e.g., removing all entries from a specific domain).
filterHistory :: (HistoryEntry -> Boolean) -> NavigationHistory -> NavigationHistory
filterHistory predicate h =
  let
    newCurrent = case h.current of
      Just curr | predicate curr -> Just curr
      _ -> Nothing
    newBack = Array.filter predicate h.back
    newForward = Array.filter predicate h.forward
  in
    h { current = newCurrent
      , back = newBack
      , forward = newForward
      }

-- | Filter entries by timestamp range.
-- |
-- | Keeps entries where: minTime <= timestamp <= maxTime
filterByTimestamp :: Int -> Int -> NavigationHistory -> NavigationHistory
filterByTimestamp minTime maxTime h =
  filterHistory (\e -> e.timestamp >= minTime && e.timestamp <= maxTime) h

-- | Get all entries in a timestamp range (across all stacks).
-- |
-- | Returns entries ordered by timestamp (oldest first).
entriesInRange :: Int -> Int -> NavigationHistory -> Array HistoryEntry
entriesInRange minTime maxTime h =
  let
    inRange e = e.timestamp >= minTime && e.timestamp <= maxTime
    currentEntries = case h.current of
      Just curr | inRange curr -> [curr]
      _ -> []
    backEntries = Array.filter inRange h.back
    forwardEntries = Array.filter inRange h.forward
    allEntries = backEntries <> currentEntries <> forwardEntries
  in
    -- Sort by timestamp ascending (oldest first)
    -- Using sortBy with custom comparator
    sortByTimestamp allEntries

-- | Sort entries by timestamp (oldest first).
sortByTimestamp :: Array HistoryEntry -> Array HistoryEntry
sortByTimestamp entries = Array.sortWith entryTimestamp entries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is history completely empty (no current, no back, no forward)?
isEmpty :: NavigationHistory -> Boolean
isEmpty h = case h.current of
  Nothing -> Array.length h.back == 0 && Array.length h.forward == 0
  Just _ -> false

-- | Is history at maximum capacity?
-- |
-- | True when both back and forward stacks are at max depth.
isFull :: NavigationHistory -> Boolean
isFull h =
  let maxD = unwrapHistoryDepth h.maxDepth
  in Array.length h.back >= maxD && Array.length h.forward >= maxD

-- | Does history have forward entries available?
hasForwardHistory :: NavigationHistory -> Boolean
hasForwardHistory = canGoForward

-- | Is current position at the start of history (nothing behind)?
isAtStart :: NavigationHistory -> Boolean
isAtStart h = Array.length h.back == 0

-- | Is current position at the end of history (nothing ahead)?
isAtEnd :: NavigationHistory -> Boolean
isAtEnd h = Array.length h.forward == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is entry A newer than entry B (higher timestamp)?
newerThan :: HistoryEntry -> HistoryEntry -> Boolean
newerThan a b = a.timestamp > b.timestamp

-- | Is entry A older than entry B (lower timestamp)?
olderThan :: HistoryEntry -> HistoryEntry -> Boolean
olderThan a b = a.timestamp < b.timestamp

-- | Do two entries refer to the same location?
-- |
-- | Useful for detecting duplicate navigation attempts.
sameLocation :: HistoryEntry -> HistoryEntry -> Boolean
sameLocation a b = a.location == b.location


