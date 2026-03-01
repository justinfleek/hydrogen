-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // query // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QueryState helper functions.
-- |
-- | This module provides convenience functions for working with QueryState:
-- | - getData: Extract success data as Maybe
-- | - getError: Extract error as Maybe
-- | - hasData: Check if data is available
-- | - foldData: Pattern match on the RemoteData
-- | - withDefaultData: Get data or fall back to default
module Hydrogen.Query.Helpers
  ( -- * QueryState helpers
    getData
  , getError
  , hasData
  , foldData
  , withDefaultData
  ) where

import Data.Maybe (Maybe(Nothing, Just), isJust)
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Hydrogen.Query.Types (QueryState)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // QueryState helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the data from a QueryState if available.
getData :: forall e a. QueryState e a -> Maybe a
getData state = case state.data of
  Success a -> Just a
  _ -> Nothing

-- | Get the error from a QueryState if in failure state.
getError :: forall e a. QueryState e a -> Maybe e
getError state = case state.data of
  Failure e -> Just e
  _ -> Nothing

-- | Check if QueryState has data (Success or stale data preserved).
hasData :: forall e a. QueryState e a -> Boolean
hasData state = isJust (getData state)

-- | Fold over the RemoteData in a QueryState.
-- |
-- | ```purescript
-- | Q.foldData state
-- |   { notAsked: HH.text "Click to load"
-- |   , loading: spinner
-- |   , failure: \e -> errorCard e
-- |   , success: \user -> userCard user
-- |   }
-- | ```
foldData
  :: forall e a r
   . { notAsked :: r
     , loading :: r
     , failure :: e -> r
     , success :: a -> r
     }
  -> QueryState e a
  -> r
foldData handlers state = case state.data of
  NotAsked -> handlers.notAsked
  Loading -> handlers.loading
  Failure e -> handlers.failure e
  Success a -> handlers.success a

-- | Get success value or fall back to default.
withDefaultData :: forall e a. a -> QueryState e a -> a
withDefaultData def state = case state.data of
  Success a -> a
  _ -> def
