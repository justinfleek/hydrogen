-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // storage // session
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Session Storage — Configuration and types for session-scoped persistence.
-- |
-- | ## Design Philosophy
-- |
-- | Session storage differs from local storage in lifecycle:
-- | - Local storage persists indefinitely
-- | - Session storage clears when the browser tab closes
-- | - Cookies have configurable TTL and cross-request semantics
-- |
-- | This module provides a unified configuration for all three storage types,
-- | allowing agents to specify persistence requirements declaratively.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Storage configuration is pure data. Agents can reason about storage
-- | semantics, compare configurations, and serialize storage intents
-- | without executing browser APIs.

module Hydrogen.Schema.Storage.Session
  ( -- * Storage Type
    StorageType(LocalStorage, SessionStorage, Cookies)
  , storageTypeLabel
  , storageTypePersists
  , storageTypeCrossTab
  
  -- * Session Config
  , SessionConfig
  , sessionConfig
  , configStorageType
  , configKey
  , configTTL
  , hasTTL
  , isExpired
  
  -- * Cookie Options
  , CookieOptions
  , cookieOptions
  , defaultCookieOptions
  , secureCookieOptions
  , sessionCookieOptions
  , cookiePath
  , cookieDomain
  , cookieSecure
  , cookieSameSite
  , cookieHttpOnly
  
  -- * SameSite Policy
  , SameSite(SameSiteStrict, SameSiteLax, SameSiteNone)
  , sameSiteLabel
  , isSameSiteStrict
  
  -- * Session Error
  , SessionError(SessionExpired, SessionNotFound, SessionCorrupted, SessionStorageUnavailable, CookieBlocked)
  , sessionErrorMessage
  , isSessionExpiredError
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (>=)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Storage.Local (StorageKey)
import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Duration (toMilliseconds) as Duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // storage type
-- ═════════════════════════════════════════════════════════════════════════════

-- | StorageType — the persistence mechanism to use.
-- |
-- | Each type has different characteristics:
-- | - LocalStorage: persists indefinitely, same-origin only
-- | - SessionStorage: cleared on tab close, same-origin only
-- | - Cookies: configurable TTL, sent with HTTP requests
data StorageType
  = LocalStorage       -- ^ Persists indefinitely until cleared
  | SessionStorage     -- ^ Cleared when browser tab closes
  | Cookies            -- ^ HTTP cookies with optional TTL

derive instance eqStorageType :: Eq StorageType
derive instance ordStorageType :: Ord StorageType

instance showStorageType :: Show StorageType where
  show = storageTypeLabel

-- | Get display label for storage type.
storageTypeLabel :: StorageType -> String
storageTypeLabel LocalStorage = "Local Storage"
storageTypeLabel SessionStorage = "Session Storage"
storageTypeLabel Cookies = "Cookies"

-- | Check if storage type persists across browser sessions.
storageTypePersists :: StorageType -> Boolean
storageTypePersists LocalStorage = true
storageTypePersists SessionStorage = false
storageTypePersists Cookies = true  -- If TTL set appropriately

-- | Check if storage type is shared across browser tabs.
storageTypeCrossTab :: StorageType -> Boolean
storageTypeCrossTab LocalStorage = true
storageTypeCrossTab SessionStorage = false
storageTypeCrossTab Cookies = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // session config
-- ═════════════════════════════════════════════════════════════════════════════

-- | SessionConfig — configuration for session-scoped storage.
-- |
-- | Combines storage type, key, and optional TTL for unified
-- | configuration of persistence behavior.
type SessionConfig =
  { storage :: StorageType
  , key :: StorageKey
  , ttl :: Maybe Duration     -- ^ Time-to-live (Nothing = no expiry)
  , cookieOptions :: Maybe CookieOptions  -- ^ Only used when storage = Cookies
  }

-- | Construct a session config.
sessionConfig :: StorageType -> StorageKey -> Maybe Duration -> SessionConfig
sessionConfig st k ttlDuration =
  { storage: st
  , key: k
  , ttl: ttlDuration
  , cookieOptions: Nothing
  }

-- | Get storage type from config.
configStorageType :: SessionConfig -> StorageType
configStorageType cfg = cfg.storage

-- | Get storage key from config.
configKey :: SessionConfig -> StorageKey
configKey cfg = cfg.key

-- | Get TTL from config.
configTTL :: SessionConfig -> Maybe Duration
configTTL cfg = cfg.ttl

-- | Check if config has a TTL set.
hasTTL :: SessionConfig -> Boolean
hasTTL cfg = case cfg.ttl of
  Just _ -> true
  Nothing -> false

-- | Check if a stored value has expired given elapsed time.
-- |
-- | Returns false if no TTL is configured (never expires).
isExpired :: SessionConfig -> Duration -> Boolean
isExpired cfg elapsed = case cfg.ttl of
  Nothing -> false
  Just ttlDuration ->
    Duration.toMilliseconds elapsed >= Duration.toMilliseconds ttlDuration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cookie options
-- ═════════════════════════════════════════════════════════════════════════════

-- | CookieOptions — detailed configuration for cookie storage.
-- |
-- | These options map directly to browser cookie attributes.
type CookieOptions =
  { path :: String              -- ^ Cookie path (default "/")
  , domain :: Maybe String      -- ^ Cookie domain (Nothing = current host)
  , secure :: Boolean           -- ^ Require HTTPS
  , sameSite :: SameSite        -- ^ Cross-site request policy
  , httpOnly :: Boolean         -- ^ Prevent JavaScript access
  }

-- | Construct cookie options.
cookieOptions :: String -> Maybe String -> Boolean -> SameSite -> Boolean -> CookieOptions
cookieOptions p d s ss ho =
  { path: p
  , domain: d
  , secure: s
  , sameSite: ss
  , httpOnly: ho
  }

-- | Default cookie options: path="/", not secure, SameSite=Lax.
defaultCookieOptions :: CookieOptions
defaultCookieOptions =
  { path: "/"
  , domain: Nothing
  , secure: false
  , sameSite: SameSiteLax
  , httpOnly: false
  }

-- | Secure cookie options: HTTPS required, SameSite=Strict, HttpOnly.
secureCookieOptions :: CookieOptions
secureCookieOptions =
  { path: "/"
  , domain: Nothing
  , secure: true
  , sameSite: SameSiteStrict
  , httpOnly: true
  }

-- | Session cookie options: secure, SameSite=Strict, HttpOnly, expires with session.
-- |
-- | These are appropriate for session-scoped authentication and sensitive data.
-- | The cookie is automatically cleared when the browser closes.
sessionCookieOptions :: CookieOptions
sessionCookieOptions =
  { path: "/"
  , domain: Nothing
  , secure: true
  , sameSite: SameSiteStrict
  , httpOnly: true
  }

-- | Get cookie path.
cookiePath :: CookieOptions -> String
cookiePath opts = opts.path

-- | Get cookie domain.
cookieDomain :: CookieOptions -> Maybe String
cookieDomain opts = opts.domain

-- | Check if cookie requires HTTPS.
cookieSecure :: CookieOptions -> Boolean
cookieSecure opts = opts.secure

-- | Get SameSite policy.
cookieSameSite :: CookieOptions -> SameSite
cookieSameSite opts = opts.sameSite

-- | Check if cookie is HttpOnly.
cookieHttpOnly :: CookieOptions -> Boolean
cookieHttpOnly opts = opts.httpOnly

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // samesite policy
-- ═════════════════════════════════════════════════════════════════════════════

-- | SameSite — cookie cross-site request policy.
-- |
-- | Controls when cookies are sent with cross-origin requests:
-- | - Strict: only sent for same-site requests
-- | - Lax: sent for top-level navigations
-- | - None: always sent (requires Secure flag)
data SameSite
  = SameSiteStrict    -- ^ Only same-site requests
  | SameSiteLax       -- ^ Same-site + top-level navigations
  | SameSiteNone      -- ^ All requests (requires Secure)

derive instance eqSameSite :: Eq SameSite
derive instance ordSameSite :: Ord SameSite

instance showSameSite :: Show SameSite where
  show = sameSiteLabel

-- | Get display label for SameSite policy.
sameSiteLabel :: SameSite -> String
sameSiteLabel SameSiteStrict = "Strict"
sameSiteLabel SameSiteLax = "Lax"
sameSiteLabel SameSiteNone = "None"

-- | Check if policy is strict.
isSameSiteStrict :: SameSite -> Boolean
isSameSiteStrict SameSiteStrict = true
isSameSiteStrict _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // session error
-- ═════════════════════════════════════════════════════════════════════════════

-- | SessionError — errors specific to session storage operations.
data SessionError
  = SessionExpired StorageKey     -- ^ TTL exceeded
  | SessionNotFound StorageKey    -- ^ Session does not exist
  | SessionCorrupted String       -- ^ Data could not be decoded
  | SessionStorageUnavailable     -- ^ Storage mechanism not available
  | CookieBlocked                 -- ^ Third-party cookies blocked

derive instance eqSessionError :: Eq SessionError

instance showSessionError :: Show SessionError where
  show (SessionExpired k) = "(SessionExpired " <> show k <> ")"
  show (SessionNotFound k) = "(SessionNotFound " <> show k <> ")"
  show (SessionCorrupted msg) = "(SessionCorrupted " <> show msg <> ")"
  show SessionStorageUnavailable = "SessionStorageUnavailable"
  show CookieBlocked = "CookieBlocked"

-- | Get human-readable error message.
sessionErrorMessage :: SessionError -> String
sessionErrorMessage (SessionExpired k) = "Session expired: " <> show k
sessionErrorMessage (SessionNotFound k) = "Session not found: " <> show k
sessionErrorMessage (SessionCorrupted msg) = "Session data corrupted: " <> msg
sessionErrorMessage SessionStorageUnavailable = "Session storage is not available"
sessionErrorMessage CookieBlocked = "Cookies are blocked by browser settings"

-- | Check if error is a session expired error.
isSessionExpiredError :: SessionError -> Boolean
isSessionExpiredError (SessionExpired _) = true
isSessionExpiredError _ = false
