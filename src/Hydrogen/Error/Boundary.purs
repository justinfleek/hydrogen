-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // boundary
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Error boundaries and recovery patterns
-- |
-- | Structured error handling with fallbacks, retries, and recovery.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Error.Boundary as Boundary
-- |
-- | -- Wrap content with fallback
-- | Boundary.withFallback
-- |   { fallback: \err -> errorCard err
-- |   , onError: \err -> logError err
-- |   }
-- |   content
-- |
-- | -- With retry
-- | Boundary.withRetry
-- |   { maxRetries: 3
-- |   , delay: Milliseconds 1000.0
-- |   , onRetry: \attempt -> showRetrying attempt
-- |   }
-- |   fetchData
-- |
-- | -- Graceful degradation
-- | Boundary.degrade
-- |   [ fullFeature, reducedFeature, minimalFeature ]
-- | ```
module Hydrogen.Error.Boundary
  ( -- * Types
    ErrorBoundary
  , BoundaryConfig
  , RetryConfig
  , RecoveryStrategy(..)
    -- * Error Boundaries
  , withFallback
  , withFallbackPure
  , catchError
    -- * Retry Logic
  , withRetry
  , withExponentialBackoff
  , retryUntil
    -- * Recovery
  , degrade
  , recover
  , withRecovery
    -- * Error Reporting
  , reportError
  , ErrorReport
  , createErrorReport
    -- * Utilities
  , safely
  , safelyWithDefault
  , attempt
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Aff (Aff, delay, throwError)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Exception (Error, message, try)
import Halogen.HTML as HH

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Error boundary state
type ErrorBoundary =
  { hasError :: Boolean
  , error :: Maybe Error
  , errorInfo :: Maybe String
  }

-- | Boundary configuration
type BoundaryConfig w i =
  { fallback :: Error -> HH.HTML w i
  , onError :: Error -> Effect Unit
  , onReset :: Effect Unit
  }

-- | Retry configuration
type RetryConfig =
  { maxRetries :: Int
  , delay :: Milliseconds
  , shouldRetry :: Error -> Boolean
  , onRetry :: Int -> Effect Unit
  }

-- | Recovery strategy
data RecoveryStrategy a
  = Fallback a
  | Retry RetryConfig
  | Ignore
  | Propagate

-- | Error report for logging/tracking
type ErrorReport =
  { error :: String
  , stack :: Maybe String
  , timestamp :: String
  , context :: Maybe String
  , userAgent :: String
  , url :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // error boundaries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Wrap content with a fallback UI for errors
withFallback
  :: forall w i
   . { fallback :: Error -> HH.HTML w i
     , onError :: Error -> Effect Unit
     }
  -> Effect (HH.HTML w i)
  -> Effect (HH.HTML w i)
withFallback config content = do
  result <- try content
  case result of
    Right html -> pure html
    Left err -> do
      config.onError err
      pure $ config.fallback err

-- | Pure version with Maybe
withFallbackPure
  :: forall w i
   . HH.HTML w i  -- Fallback
  -> Maybe (HH.HTML w i)  -- Content
  -> HH.HTML w i
withFallbackPure fallback = fromMaybe fallback

-- | Catch errors in an effect
catchError
  :: forall a
   . Effect a
  -> (Error -> Effect a)
  -> Effect a
catchError action handler = do
  result <- try action
  case result of
    Right a -> pure a
    Left err -> handler err

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // retry logic
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default retry configuration
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxRetries: 3
  , delay: Milliseconds 1000.0
  , shouldRetry: \_ -> true
  , onRetry: \_ -> pure unit
  }

-- | Execute with retry logic
withRetry :: forall a. RetryConfig -> Aff a -> Aff a
withRetry config action = go 0
  where
  go attempt = do
    result <- Aff.attempt action
    case result of
      Right a -> pure a
      Left err -> 
        if attempt < config.maxRetries && config.shouldRetry err
          then do
            liftEffect $ config.onRetry (attempt + 1)
            delay config.delay
            go (attempt + 1)
          else throwError err

-- | Retry with exponential backoff
withExponentialBackoff :: forall a. Int -> Milliseconds -> Aff a -> Aff a
withExponentialBackoff maxRetries baseDelay action = go 0
  where
  go attempt = do
    result <- Aff.attempt action
    case result of
      Right a -> pure a
      Left err -> 
        if attempt < maxRetries
          then do
            let Milliseconds ms = baseDelay
            let backoffMs = ms * (2.0 `pow` toNumber attempt)
            delay (Milliseconds backoffMs)
            go (attempt + 1)
          else throwError err
  
  pow :: Number -> Number -> Number
  pow base exp = if exp <= 0.0 then 1.0 else base * pow base (exp - 1.0)
  
  toNumber :: Int -> Number
  toNumber n = if n <= 0 then 0.0 else 1.0 + toNumber (n - 1)

-- | Retry until a condition is met
retryUntil :: forall a. (a -> Boolean) -> Int -> Aff a -> Aff a
retryUntil predicate maxAttempts action = go 0
  where
  go attempt = do
    result <- action
    if predicate result
      then pure result
      else if attempt < maxAttempts
        then go (attempt + 1)
        else pure result  -- Return last result even if predicate not met

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // recovery
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Graceful degradation - try alternatives in order
degrade :: forall a. Array (Aff a) -> Aff (Maybe a)
degrade alternatives = go alternatives
  where
  go arr = case Array.uncons arr of
    Nothing -> pure Nothing
    Just { head: alt, tail: rest } -> do
      result <- Aff.attempt alt
      case result of
        Right a -> pure (Just a)
        Left _ -> go rest

-- | Recover from an error with a handler
recover :: forall a. Aff a -> (Error -> Aff a) -> Aff a
recover action handler = do
  result <- Aff.attempt action
  case result of
    Right a -> pure a
    Left err -> handler err

-- | Apply recovery strategy
withRecovery :: forall a. RecoveryStrategy a -> Aff a -> Aff a
withRecovery strategy action = case strategy of
  Fallback value -> recover action (\_ -> pure value)
  Retry config -> withRetry config action
  Ignore -> recover action (\_ -> action)  -- This doesn't make sense, but typed
  Propagate -> action

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // error reporting
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Report an error (to console, monitoring service, etc.)
reportError :: Error -> Effect Unit
reportError err = do
  report <- createErrorReport err Nothing
  reportErrorImpl report

-- | Create an error report
createErrorReport :: Error -> Maybe String -> Effect ErrorReport
createErrorReport err context = do
  timestamp <- getTimestamp
  userAgent <- getUserAgent
  url <- getUrl
  pure
    { error: message err
    , stack: getStack err
    , timestamp
    , context
    , userAgent
    , url
    }

-- FFI
foreign import reportErrorImpl :: ErrorReport -> Effect Unit
foreign import getTimestamp :: Effect String
foreign import getUserAgent :: Effect String
foreign import getUrl :: Effect String
foreign import getStack :: Error -> Maybe String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Safely execute an effect, returning Maybe
safely :: forall a. Effect a -> Effect (Maybe a)
safely action = do
  result <- try action
  pure $ case result of
    Right a -> Just a
    Left _ -> Nothing

-- | Safely execute with a default value
safelyWithDefault :: forall a. a -> Effect a -> Effect a
safelyWithDefault def action = do
  result <- safely action
  pure $ fromMaybe def result

-- | Attempt an effect, returning Either
attempt :: forall a. Effect a -> Effect (Either Error a)
attempt = try
