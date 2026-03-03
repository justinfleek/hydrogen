{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // Foundry.Core.Effects.Graded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Graded monad for Foundry operations, built on Orchard & Petricek's
-- effect-monad library (Control.Effect).
--
-- The grade parameter is a type-level sorted set of GradeLabel atoms
-- from Foundry.Core.Effects.Grade. Composition unions the sets:
--
--     f : FoundryM '[Net] a
--     g : FoundryM '[Auth] b
--     f >>= \_ -> g : FoundryM '[Net, Auth] b    -- via Union
--
-- Runtime tracking (latency, tokens, provenance, coeffects) is still
-- accumulated at the value level — the type-level grade is a *static
-- upper bound* on what effects are permitted.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Foundry.Core.Effects.Graded
  ( -- * Re-export grade types
    module Foundry.Core.Effects.Grade

    -- * Value-level cost tracking
  , GatewayGrade (..)
  , emptyGrade
  , combineGrades
  , gradeFromLatency

    -- * CoEffect tracking
  , GatewayCoEffect (..)
  , emptyCoEffect
  , HttpAccess (..)
  , AuthUsage (..)
  , ConfigAccess (..)

    -- * Provenance
  , GatewayProvenance (..)
  , emptyProvenance

    -- * Graded Monad (type-level indexed)
  , FoundryM (..)
  , runFoundryM
  , runFoundryMPure

    -- * Primitive lift points
  , liftPure
  , liftNet
  , liftAuth
  , liftConfig
  , liftLog
  , liftCrypto
  , liftIO'

    -- * Cost tracking combinators
  , withCacheHit
  , withCacheMiss
  , withLatency
  , withLatencyTimed
  , withTokens
  , withRetry

    -- * CoEffect recording
  , recordHttpAccess
  , recordAuthUsage
  , recordConfigAccess

    -- * Provenance recording
  , recordProvider
  , recordModel
  , recordRequestId

    -- * Grade inspection
  , getGrade
  , getCoEffect
  , getProvenance
  , shouldCacheResponse
  ) where

import Control.DeepSeq (NFData (rnf))
import Control.Effect (Effect (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Time (UTCTime, getCurrentTime, diffUTCTime)
import GHC.Generics (Generic)

import Foundry.Core.Effects.Grade


-- ════════════════════════════════════════════════════════════════════════════
--                                                           // gateway grade
-- ════════════════════════════════════════════════════════════════════════════

-- | Value-level cost accumulator. Tracks what actually happened at runtime.
-- This is orthogonal to the type-level grade — the grade says what's
-- *permitted*, this records what *occurred*.
data GatewayGrade = GatewayGrade
  { ggLatencyMs     :: !Int
  , ggInputTokens   :: !Int
  , ggOutputTokens  :: !Int
  , ggProviderCalls :: !Int
  , ggRetries       :: !Int
  , ggCacheHits     :: !Int
  , ggCacheMisses   :: !Int
  }
  deriving stock (Show, Eq, Generic)

instance NFData GatewayGrade where
  rnf GatewayGrade {..} =
    rnf ggLatencyMs `seq` rnf ggInputTokens `seq`
    rnf ggOutputTokens `seq` rnf ggProviderCalls `seq`
    rnf ggRetries `seq` rnf ggCacheHits `seq` rnf ggCacheMisses

instance Semigroup GatewayGrade where
  g1 <> g2 = GatewayGrade
    { ggLatencyMs     = ggLatencyMs g1     + ggLatencyMs g2
    , ggInputTokens   = ggInputTokens g1   + ggInputTokens g2
    , ggOutputTokens  = ggOutputTokens g1  + ggOutputTokens g2
    , ggProviderCalls = ggProviderCalls g1 + ggProviderCalls g2
    , ggRetries       = ggRetries g1       + ggRetries g2
    , ggCacheHits     = ggCacheHits g1     + ggCacheHits g2
    , ggCacheMisses   = ggCacheMisses g1   + ggCacheMisses g2
    }

instance Monoid GatewayGrade where
  mempty = emptyGrade

emptyGrade :: GatewayGrade
emptyGrade = GatewayGrade 0 0 0 0 0 0 0

combineGrades :: GatewayGrade -> GatewayGrade -> GatewayGrade
combineGrades = (<>)

gradeFromLatency :: Int -> GatewayGrade
gradeFromLatency ms = emptyGrade { ggLatencyMs = ms, ggProviderCalls = 1 }


-- ════════════════════════════════════════════════════════════════════════════
--                                                        // gateway co-effect
-- ════════════════════════════════════════════════════════════════════════════

data HttpAccess = HttpAccess
  { haUrl        :: !Text
  , haMethod     :: !Text
  , haTimestamp  :: !UTCTime
  , haStatusCode :: !(Maybe Int)
  }
  deriving stock (Show, Eq, Ord, Generic)

instance NFData HttpAccess where
  rnf HttpAccess {..} =
    rnf haUrl `seq` rnf haMethod `seq` rnf haTimestamp `seq` rnf haStatusCode

data AuthUsage = AuthUsage
  { auProvider  :: !Text
  , auScope     :: !Text
  , auTimestamp :: !UTCTime
  }
  deriving stock (Show, Eq, Ord, Generic)

instance NFData AuthUsage where
  rnf AuthUsage {..} = rnf auProvider `seq` rnf auScope `seq` rnf auTimestamp

data ConfigAccess = ConfigAccess
  { caKey       :: !Text
  , caTimestamp :: !UTCTime
  }
  deriving stock (Show, Eq, Ord, Generic)

instance NFData ConfigAccess where
  rnf ConfigAccess {..} = rnf caKey `seq` rnf caTimestamp

data GatewayCoEffect = GatewayCoEffect
  { gceHttpAccess   :: !(Set HttpAccess)
  , gceAuthUsage    :: !(Set AuthUsage)
  , gceConfigAccess :: !(Set ConfigAccess)
  }
  deriving stock (Show, Eq, Generic)

instance NFData GatewayCoEffect where
  rnf GatewayCoEffect {..} =
    rnf gceHttpAccess `seq` rnf gceAuthUsage `seq` rnf gceConfigAccess

instance Semigroup GatewayCoEffect where
  ce1 <> ce2 = GatewayCoEffect
    { gceHttpAccess   = gceHttpAccess ce1   <> gceHttpAccess ce2
    , gceAuthUsage    = gceAuthUsage ce1    <> gceAuthUsage ce2
    , gceConfigAccess = gceConfigAccess ce1 <> gceConfigAccess ce2
    }

instance Monoid GatewayCoEffect where
  mempty = emptyCoEffect

emptyCoEffect :: GatewayCoEffect
emptyCoEffect = GatewayCoEffect Set.empty Set.empty Set.empty


-- ════════════════════════════════════════════════════════════════════════════
--                                                       // gateway provenance
-- ════════════════════════════════════════════════════════════════════════════

data GatewayProvenance = GatewayProvenance
  { gpRequestId     :: !(Maybe Text)
  , gpProvidersUsed :: ![Text]
  , gpModelsUsed    :: ![Text]
  , gpTimestamp     :: !(Maybe UTCTime)
  , gpClientIp      :: !(Maybe Text)
  }
  deriving stock (Show, Eq, Generic)

instance NFData GatewayProvenance where
  rnf GatewayProvenance {..} =
    rnf gpRequestId `seq` rnf gpProvidersUsed `seq`
    rnf gpModelsUsed `seq` rnf gpTimestamp `seq` rnf gpClientIp

emptyProvenance :: GatewayProvenance
emptyProvenance = GatewayProvenance Nothing [] [] Nothing Nothing

combineProvenance :: GatewayProvenance -> GatewayProvenance -> GatewayProvenance
combineProvenance p1 p2 = GatewayProvenance
  { gpRequestId     = gpRequestId p2     <|> gpRequestId p1
  , gpProvidersUsed = gpProvidersUsed p1  ++ gpProvidersUsed p2
  , gpModelsUsed    = gpModelsUsed p1     ++ gpModelsUsed p2
  , gpTimestamp     = gpTimestamp p1      <|> gpTimestamp p2
  , gpClientIp      = gpClientIp p1       <|> gpClientIp p2
  }
  where
    Nothing <|> y = y
    x       <|> _ = x


-- ════════════════════════════════════════════════════════════════════════════
--                                               // graded monad (the core)
-- ════════════════════════════════════════════════════════════════════════════

-- | The Foundry graded monad.
--
-- @FoundryM es a@ is a computation that:
--   - May perform effects in the set @es@ (type-level, checked at compile time)
--   - Produces a value of type @a@
--   - Accumulates runtime cost data in GatewayGrade, GatewayProvenance,
--     and GatewayCoEffect (value-level, available at runtime)
--
-- The phantom type parameter @es :: [GradeLabel]@ is the grade.
newtype FoundryM (es :: [GradeLabel]) a = FoundryM
  { unFoundryM :: IO (a, GatewayGrade, GatewayProvenance, GatewayCoEffect)
  }

-- | FoundryM is an Orchard & Petricek graded monad (Effect from effect-monad).
instance Effect FoundryM where
  type Unit FoundryM = Pure
  type Plus FoundryM f g = Union f g
  type Inv  FoundryM f g = ()

  return a = FoundryM $ pure (a, emptyGrade, emptyProvenance, emptyCoEffect)

  (FoundryM m) >>= f = FoundryM $ do
    (a, g1, p1, ce1) <- m
    (b, g2, p2, ce2) <- unFoundryM (f a)
    pure (b, g1 <> g2, combineProvenance p1 p2, ce1 <> ce2)

-- | Run a graded computation.
runFoundryM :: FoundryM es a -> IO (a, GatewayGrade, GatewayProvenance, GatewayCoEffect)
runFoundryM = unFoundryM

-- | Run discarding tracking data.
runFoundryMPure :: FoundryM es a -> IO a
runFoundryMPure m = (\(a, _, _, _) -> a) <$> runFoundryM m


-- ════════════════════════════════════════════════════════════════════════════
--                                                    // primitive lift points
-- ════════════════════════════════════════════════════════════════════════════

liftPure :: a -> FoundryM Pure a
liftPure a = FoundryM $ pure (a, emptyGrade, emptyProvenance, emptyCoEffect)

liftNet :: IO a -> FoundryM '[ 'Net ] a
liftNet action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

liftAuth :: IO a -> FoundryM '[ 'Auth ] a
liftAuth action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

liftConfig :: IO a -> FoundryM '[ 'Config ] a
liftConfig action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

liftLog :: IO a -> FoundryM '[ 'Log ] a
liftLog action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

liftCrypto :: IO a -> FoundryM '[ 'Crypto ] a
liftCrypto action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

liftIO' :: IO a -> FoundryM Full a
liftIO' action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)


-- ════════════════════════════════════════════════════════════════════════════
--                                                  // cost tracking combinators
-- ════════════════════════════════════════════════════════════════════════════

-- | Mark a computation as having used the cache (hit).
withCacheHit :: FoundryM es a -> FoundryM es a
withCacheHit (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  let g' = g { ggCacheHits = ggCacheHits g + 1 }
  pure (a, g', p, ce)

-- | Mark a computation as having missed the cache.
withCacheMiss :: FoundryM es a -> FoundryM es a
withCacheMiss (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  let g' = g { ggCacheMisses = ggCacheMisses g + 1 }
  pure (a, g', p, ce)

-- | Add latency cost to a computation.
withLatency :: Int -> FoundryM es a -> FoundryM es a
withLatency ms (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  let g' = g { ggLatencyMs = ggLatencyMs g + ms }
  pure (a, g', p, ce)

-- | Add token costs to a computation.
withTokens :: Int -> Int -> FoundryM es a -> FoundryM es a
withTokens input output (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  let g' = g { ggInputTokens = ggInputTokens g + input
             , ggOutputTokens = ggOutputTokens g + output
             }
  pure (a, g', p, ce)

-- | Record retry. Grade-preserving.
withRetry :: FoundryM es a -> FoundryM es a
withRetry (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  pure (a, g { ggRetries = ggRetries g + 1 }, p, ce)

-- | Measure latency of a network operation.
-- Note: this is tagged '[Net] because measuring latency implies network I/O.
withLatencyTimed :: IO a -> FoundryM '[ 'Net ] a
withLatencyTimed action = FoundryM $ do
  start  <- getCurrentTime
  result <- action
  end    <- getCurrentTime
  let ms = round (diffUTCTime end start * 1000)
  pure (result, gradeFromLatency ms, emptyProvenance, emptyCoEffect)


-- ════════════════════════════════════════════════════════════════════════════
--                                           // co-effect recording (value)
-- ════════════════════════════════════════════════════════════════════════════

-- | Record HTTP access. Introduces 'Net into the grade.
recordHttpAccess :: Text -> Text -> Maybe Int -> FoundryM '[ 'Net ] ()
recordHttpAccess url method status = FoundryM $ do
  now <- getCurrentTime
  let access = HttpAccess url method now status
      ce = emptyCoEffect { gceHttpAccess = Set.singleton access }
  pure ((), emptyGrade, emptyProvenance, ce)

-- | Record auth usage. Introduces 'Auth into the grade.
recordAuthUsage :: Text -> Text -> FoundryM '[ 'Auth ] ()
recordAuthUsage provider scope = FoundryM $ do
  now <- getCurrentTime
  let usage = AuthUsage provider scope now
      ce = emptyCoEffect { gceAuthUsage = Set.singleton usage }
  pure ((), emptyGrade, emptyProvenance, ce)

-- | Record config access. Introduces 'Config into the grade.
recordConfigAccess :: Text -> FoundryM '[ 'Config ] ()
recordConfigAccess key = FoundryM $ do
  now <- getCurrentTime
  let access = ConfigAccess key now
      ce = emptyCoEffect { gceConfigAccess = Set.singleton access }
  pure ((), emptyGrade, emptyProvenance, ce)


-- ════════════════════════════════════════════════════════════════════════════
--                                           // provenance recording (value)
-- ════════════════════════════════════════════════════════════════════════════

-- | Record provider used. Pure — provenance is bookkeeping, not an effect.
recordProvider :: Text -> FoundryM Pure ()
recordProvider provider = FoundryM $
  pure ((), emptyGrade, emptyProvenance { gpProvidersUsed = [provider] }, emptyCoEffect)

-- | Record model used. Pure.
recordModel :: Text -> FoundryM Pure ()
recordModel model = FoundryM $
  pure ((), emptyGrade, emptyProvenance { gpModelsUsed = [model] }, emptyCoEffect)

-- | Record request ID. Pure.
recordRequestId :: Text -> FoundryM Pure ()
recordRequestId reqId = FoundryM $ do
  now <- getCurrentTime
  let p = emptyProvenance { gpRequestId = Just reqId, gpTimestamp = Just now }
  pure ((), emptyGrade, p, emptyCoEffect)


-- ════════════════════════════════════════════════════════════════════════════
--                                                       // grade inspection
-- ════════════════════════════════════════════════════════════════════════════

-- | Inspect accumulated grade. Pure.
getGrade :: FoundryM Pure GatewayGrade
getGrade = FoundryM $ pure (emptyGrade, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Inspect accumulated co-effect. Pure.
getCoEffect :: FoundryM Pure GatewayCoEffect
getCoEffect = FoundryM $ pure (emptyCoEffect, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Inspect accumulated provenance. Pure.
getProvenance :: FoundryM Pure GatewayProvenance
getProvenance = FoundryM $ pure (emptyProvenance, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Should this response be cached? Based on cost heuristics.
shouldCacheResponse :: GatewayGrade -> Bool
shouldCacheResponse g =
  ggLatencyMs g > 100 || ggRetries g > 0 || ggCacheMisses g > 0
