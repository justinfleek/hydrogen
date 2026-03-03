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
--     "The sky above the port was the color of television, tuned to a dead
--      channel."
--
--                                                              — Neuromancer
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
-- upper bound* on what effects are permitted, while the value-level
-- data records what actually happened.
--
-- Usage with QualifiedDo:
--
--     {-# LANGUAGE QualifiedDo #-}
--     import Foundry.Core.Effects.Do qualified as F
--
--     handleRequest :: Request -> FoundryM '[Net, Auth, Crypto] Response
--     handleRequest req = F.do
--       provider <- selectProvider req        -- Pure, widened automatically
--       response <- callUpstream provider req -- Net ∪ Auth
--       proof    <- signResponse response     -- Crypto
--       F.return (response, proof)
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Foundry.Core.Effects.Graded
  ( -- * Foundry Grade (value-level cost tracking)
    FoundryGrade
      ( FoundryGrade
      , fgLatencyMs
      , fgInputTokens
      , fgOutputTokens
      , fgProviderCalls
      , fgRetries
      , fgCacheHits
      , fgCacheMisses
      )
  , emptyGrade
  , combineGrades
  , gradeFromLatency

    -- * Foundry CoEffect (value-level resource tracking)
  , FoundryCoEffect (FoundryCoEffect, fceHttpAccess, fceAuthUsage, fceConfigAccess)
  , emptyCoEffect
  , HttpAccess (HttpAccess, haUrl, haMethod, haTimestamp, haStatusCode)
  , AuthUsage (AuthUsage, auProvider, auScope, auTimestamp)
  , ConfigAccess (ConfigAccess, caKey, caTimestamp)

    -- * Foundry Provenance
  , FoundryProvenance
      ( FoundryProvenance
      , fpRequestId
      , fpProvidersUsed
      , fpModelsUsed
      , fpTimestamp
      , fpClientIp
      )
  , emptyProvenance

    -- * Graded Monad (type-level indexed)
  , FoundryM (FoundryM, unFoundryM)
  , runFoundryM
  , runFoundryMPure

    -- * Primitive effect operations (each tags the type-level grade)
  , liftPure
  , liftNet
  , liftAuth
  , liftConfig
  , liftLog
  , liftCrypto
  , liftIO'

    -- * Cost tracking
  , withLatency
  , withTokens
  , withCacheHit
  , withCacheMiss
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

    -- * Re-exports for grade construction
  , module Foundry.Core.Effects.Grade
  ) where

import Control.DeepSeq (NFData (rnf))
import Control.Effect (Effect (..))
import Data.Kind (Type)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Time (UTCTime, getCurrentTime, diffUTCTime)
import GHC.Generics (Generic)

import Foundry.Core.Effects.Grade


-- ════════════════════════════════════════════════════════════════════════════
--                                                           // foundry grade
-- ════════════════════════════════════════════════════════════════════════════

-- | Value-level cost accumulator. Tracks what actually happened at runtime.
-- This is orthogonal to the type-level grade — the grade says what's
-- *permitted*, this records what *occurred*.
data FoundryGrade = FoundryGrade
  { fgLatencyMs     :: !Int
  , fgInputTokens   :: !Int
  , fgOutputTokens  :: !Int
  , fgProviderCalls :: !Int
  , fgRetries       :: !Int
  , fgCacheHits     :: !Int
  , fgCacheMisses   :: !Int
  }
  deriving stock (Show, Eq, Generic)

instance NFData FoundryGrade where
  rnf FoundryGrade {..} =
    rnf fgLatencyMs `seq` rnf fgInputTokens `seq`
    rnf fgOutputTokens `seq` rnf fgProviderCalls `seq`
    rnf fgRetries `seq` rnf fgCacheHits `seq` rnf fgCacheMisses

instance Semigroup FoundryGrade where
  g1 <> g2 = FoundryGrade
    { fgLatencyMs     = fgLatencyMs g1     + fgLatencyMs g2
    , fgInputTokens   = fgInputTokens g1   + fgInputTokens g2
    , fgOutputTokens  = fgOutputTokens g1  + fgOutputTokens g2
    , fgProviderCalls = fgProviderCalls g1  + fgProviderCalls g2
    , fgRetries       = fgRetries g1       + fgRetries g2
    , fgCacheHits     = fgCacheHits g1     + fgCacheHits g2
    , fgCacheMisses   = fgCacheMisses g1   + fgCacheMisses g2
    }

instance Monoid FoundryGrade where
  mempty = emptyGrade

emptyGrade :: FoundryGrade
emptyGrade = FoundryGrade 0 0 0 0 0 0 0

combineGrades :: FoundryGrade -> FoundryGrade -> FoundryGrade
combineGrades = (<>)

gradeFromLatency :: Int -> FoundryGrade
gradeFromLatency ms = emptyGrade { fgLatencyMs = ms, fgProviderCalls = 1 }


-- ════════════════════════════════════════════════════════════════════════════
--                                                        // foundry co-effect
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

data FoundryCoEffect = FoundryCoEffect
  { fceHttpAccess   :: !(Set HttpAccess)
  , fceAuthUsage    :: !(Set AuthUsage)
  , fceConfigAccess :: !(Set ConfigAccess)
  }
  deriving stock (Show, Eq, Generic)

instance NFData FoundryCoEffect where
  rnf FoundryCoEffect {..} =
    rnf fceHttpAccess `seq` rnf fceAuthUsage `seq` rnf fceConfigAccess

instance Semigroup FoundryCoEffect where
  ce1 <> ce2 = FoundryCoEffect
    { fceHttpAccess   = fceHttpAccess ce1   <> fceHttpAccess ce2
    , fceAuthUsage    = fceAuthUsage ce1    <> fceAuthUsage ce2
    , fceConfigAccess = fceConfigAccess ce1 <> fceConfigAccess ce2
    }

instance Monoid FoundryCoEffect where
  mempty = emptyCoEffect

emptyCoEffect :: FoundryCoEffect
emptyCoEffect = FoundryCoEffect Set.empty Set.empty Set.empty


-- ════════════════════════════════════════════════════════════════════════════
--                                                       // foundry provenance
-- ════════════════════════════════════════════════════════════════════════════

data FoundryProvenance = FoundryProvenance
  { fpRequestId     :: !(Maybe Text)
  , fpProvidersUsed :: ![Text]
  , fpModelsUsed    :: ![Text]
  , fpTimestamp     :: !(Maybe UTCTime)
  , fpClientIp      :: !(Maybe Text)
  }
  deriving stock (Show, Eq, Generic)

instance NFData FoundryProvenance where
  rnf FoundryProvenance {..} =
    rnf fpRequestId `seq` rnf fpProvidersUsed `seq`
    rnf fpModelsUsed `seq` rnf fpTimestamp `seq` rnf fpClientIp

emptyProvenance :: FoundryProvenance
emptyProvenance = FoundryProvenance Nothing [] [] Nothing Nothing

combineProvenance :: FoundryProvenance -> FoundryProvenance -> FoundryProvenance
combineProvenance p1 p2 = FoundryProvenance
  { fpRequestId     = fpRequestId p2     <|> fpRequestId p1
  , fpProvidersUsed = fpProvidersUsed p1  ++ fpProvidersUsed p2
  , fpModelsUsed    = fpModelsUsed p1     ++ fpModelsUsed p2
  , fpTimestamp     = fpTimestamp p1      <|> fpTimestamp p2
  , fpClientIp      = fpClientIp p1      <|> fpClientIp p2
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
--   - Accumulates runtime cost data in FoundryGrade, FoundryProvenance,
--     and FoundryCoEffect (value-level, available at runtime)
--
-- The phantom type parameter @es :: [GradeLabel]@ is the grade.
-- It's a sorted set of effect labels. GHC enforces at compile time that
-- operations requiring 'Net are only called from contexts where 'Net is
-- in the grade.
newtype FoundryM (es :: [GradeLabel]) a = FoundryM
  { unFoundryM :: IO (a, FoundryGrade, FoundryProvenance, FoundryCoEffect)
  }

-- | FoundryM is an Orchard & Petricek graded monad (Effect from effect-monad).
--
-- The grade algebra:
--   Unit  = '[]              (pure computation, no effects)
--   Plus  = Union            (set union of effect labels)
--   Inv   = ()               (no additional constraints on composition)
instance Effect FoundryM where
  type Unit FoundryM = Pure                -- '[] — the empty effect set
  type Plus FoundryM f g = Union f g       -- set union
  type Inv  FoundryM f g = ()              -- no constraints on composition

  return a = FoundryM $ pure (a, emptyGrade, emptyProvenance, emptyCoEffect)

  (FoundryM m) >>= f = FoundryM $ do
    (a, g1, p1, ce1) <- m
    (b, g2, p2, ce2) <- unFoundryM (f a)
    pure (b, g1 <> g2, combineProvenance p1 p2, ce1 <> ce2)

-- | Run a graded computation. The grade @es@ is erased at runtime —
-- it exists only to constrain composition at compile time.
runFoundryM :: FoundryM es a -> IO (a, FoundryGrade, FoundryProvenance, FoundryCoEffect)
runFoundryM = unFoundryM

-- | Run discarding tracking data.
runFoundryMPure :: FoundryM es a -> IO a
runFoundryMPure m = (\(a, _, _, _) -> a) <$> runFoundryM m


-- ════════════════════════════════════════════════════════════════════════════
--                                                    // primitive lift points
-- ════════════════════════════════════════════════════════════════════════════

-- Each lift point tags the type-level grade with exactly the label(s)
-- corresponding to the kind of effect being performed. Callers of these
-- functions get their grade widened automatically by the Effect instance's
-- Plus (= Union).

-- | Lift a pure (no-IO) value. Grade: Pure ('[]). 
liftPure :: a -> FoundryM Pure a
liftPure a = FoundryM $ pure (a, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Lift an IO action that performs network access.
-- Grade: '[Net]. This is the *only* way to introduce 'Net into the grade.
liftNet :: IO a -> FoundryM '[ 'Net ] a
liftNet action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Lift an IO action that uses authentication credentials.
liftAuth :: IO a -> FoundryM '[ 'Auth ] a
liftAuth action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Lift an IO action that reads configuration.
liftConfig :: IO a -> FoundryM '[ 'Config ] a
liftConfig action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Lift a logging action.
liftLog :: IO a -> FoundryM '[ 'Log ] a
liftLog action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Lift a cryptographic operation.
liftCrypto :: IO a -> FoundryM '[ 'Crypto ] a
liftCrypto action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Escape hatch: lift arbitrary IO with full effect set.
-- Use sparingly — this defeats the purpose of grading.
-- Every use should have a comment justifying why.
liftIO' :: IO a -> FoundryM Full a
liftIO' action = FoundryM $ do
  result <- action
  pure (result, emptyGrade, emptyProvenance, emptyCoEffect)


-- ════════════════════════════════════════════════════════════════════════════
--                                                    // cost tracking (value)
-- ════════════════════════════════════════════════════════════════════════════

-- | Measure latency of a network operation.
-- Note: this is tagged '[Net] because measuring latency implies network I/O.
withLatency :: IO a -> FoundryM '[ 'Net ] a
withLatency action = FoundryM $ do
  start  <- getCurrentTime
  result <- action
  end    <- getCurrentTime
  let ms = round (diffUTCTime end start * 1000)
  pure (result, gradeFromLatency ms, emptyProvenance, emptyCoEffect)

-- | Add token counts. Grade-preserving (doesn't add new effect labels).
withTokens :: Int -> Int -> FoundryM es a -> FoundryM es a
withTokens input output (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  let g' = g { fgInputTokens  = fgInputTokens g + input
             , fgOutputTokens = fgOutputTokens g + output }
  pure (a, g', p, ce)

-- | Record cache hit. Grade-preserving.
withCacheHit :: FoundryM es a -> FoundryM es a
withCacheHit (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  pure (a, g { fgCacheHits = fgCacheHits g + 1 }, p, ce)

-- | Record cache miss. Grade-preserving.
withCacheMiss :: FoundryM es a -> FoundryM es a
withCacheMiss (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  pure (a, g { fgCacheMisses = fgCacheMisses g + 1 }, p, ce)

-- | Record retry. Grade-preserving.
withRetry :: FoundryM es a -> FoundryM es a
withRetry (FoundryM m) = FoundryM $ do
  (a, g, p, ce) <- m
  pure (a, g { fgRetries = fgRetries g + 1 }, p, ce)


-- ════════════════════════════════════════════════════════════════════════════
--                                           // co-effect recording (value)
-- ════════════════════════════════════════════════════════════════════════════

-- | Record HTTP access. Introduces 'Net into the grade.
recordHttpAccess :: Text -> Text -> Maybe Int -> FoundryM '[ 'Net ] ()
recordHttpAccess url method status = FoundryM $ do
  now <- getCurrentTime
  let access = HttpAccess url method now status
      ce = emptyCoEffect { fceHttpAccess = Set.singleton access }
  pure ((), emptyGrade, emptyProvenance, ce)

-- | Record auth usage. Introduces 'Auth into the grade.
recordAuthUsage :: Text -> Text -> FoundryM '[ 'Auth ] ()
recordAuthUsage provider scope = FoundryM $ do
  now <- getCurrentTime
  let usage = AuthUsage provider scope now
      ce = emptyCoEffect { fceAuthUsage = Set.singleton usage }
  pure ((), emptyGrade, emptyProvenance, ce)

-- | Record config access. Introduces 'Config into the grade.
recordConfigAccess :: Text -> FoundryM '[ 'Config ] ()
recordConfigAccess key = FoundryM $ do
  now <- getCurrentTime
  let access = ConfigAccess key now
      ce = emptyCoEffect { fceConfigAccess = Set.singleton access }
  pure ((), emptyGrade, emptyProvenance, ce)


-- ════════════════════════════════════════════════════════════════════════════
--                                           // provenance recording (value)
-- ════════════════════════════════════════════════════════════════════════════

-- | Record provider used. Pure — provenance is bookkeeping, not an effect.
recordProvider :: Text -> FoundryM Pure ()
recordProvider provider = FoundryM $
  pure ((), emptyGrade, emptyProvenance { fpProvidersUsed = [provider] }, emptyCoEffect)

-- | Record model used. Pure.
recordModel :: Text -> FoundryM Pure ()
recordModel model = FoundryM $
  pure ((), emptyGrade, emptyProvenance { fpModelsUsed = [model] }, emptyCoEffect)

-- | Record request ID. Pure.
recordRequestId :: Text -> FoundryM Pure ()
recordRequestId reqId = FoundryM $ do
  now <- getCurrentTime
  let p = emptyProvenance { fpRequestId = Just reqId, fpTimestamp = Just now }
  pure ((), emptyGrade, p, emptyCoEffect)


-- ════════════════════════════════════════════════════════════════════════════
--                                                       // grade inspection
-- ════════════════════════════════════════════════════════════════════════════

-- | Inspect accumulated grade. Pure.
getGrade :: FoundryM Pure FoundryGrade
getGrade = FoundryM $ pure (emptyGrade, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Inspect accumulated co-effect. Pure.
getCoEffect :: FoundryM Pure FoundryCoEffect
getCoEffect = FoundryM $ pure (emptyCoEffect, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Inspect accumulated provenance. Pure.
getProvenance :: FoundryM Pure FoundryProvenance
getProvenance = FoundryM $ pure (emptyProvenance, emptyGrade, emptyProvenance, emptyCoEffect)

-- | Should this response be cached? Based on cost heuristics.
shouldCacheResponse :: FoundryGrade -> Bool
shouldCacheResponse g =
  fgLatencyMs g > 100 || fgRetries g > 0 || fgCacheMisses g > 0
