-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // guard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Route guards for protected routes
-- |
-- | Type-safe route protection with role-based access control.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Auth.Guard as Guard
-- |
-- | -- Simple auth guard
-- | Guard.requireAuth session do
-- |   renderProtectedPage
-- |
-- | -- Role-based guard
-- | Guard.requireRole session "admin" do
-- |   renderAdminPage
-- |
-- | -- Permission-based guard
-- | Guard.requirePermission session "users:write" do
-- |   renderUserEditor
-- |
-- | -- With fallback
-- | Guard.withAuth session
-- |   { authenticated: renderDashboard
-- |   , unauthenticated: renderLogin
-- |   }
-- | ```
module Hydrogen.Auth.Guard
  ( -- * Guards
    requireAuth
  , requireRole
  , requireRoles
  , requirePermission
  , requirePermissions
  , requireAny
  , requireAll
    -- * Conditional Rendering
  , withAuth
  , whenAuthenticated
  , unlessAuthenticated
    -- * Types
  , GuardResult(Allowed, NotAuthenticated, NotAuthorized)
  , class HasRole
  , getRoles
  , class HasPermission
  , getPermissions
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Halogen.HTML as HH
import Hydrogen.Auth.Session (Session, AuthState(Unauthenticated, Authenticating, Authenticated, Refreshing, Expired), getAuthState, getUser)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Result of a guard check
data GuardResult
  = Allowed
  | NotAuthenticated
  | NotAuthorized String  -- Reason

derive instance eqGuardResult :: Eq GuardResult

instance showGuardResult :: Show GuardResult where
  show Allowed = "Allowed"
  show NotAuthenticated = "NotAuthenticated"
  show (NotAuthorized reason) = "NotAuthorized: " <> reason

-- | Typeclass for users with roles
class HasRole user where
  getRoles :: user -> Array String

-- | Typeclass for users with permissions
class HasPermission user where
  getPermissions :: user -> Array String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // guards
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Require authentication
requireAuth 
  :: forall user w i
   . Session user 
  -> HH.HTML w i  -- Protected content
  -> HH.HTML w i  -- Fallback
  -> Effect (HH.HTML w i)
requireAuth session protected fallback = do
  authState <- getAuthState session
  pure $ case authState of
    Authenticated -> protected
    _ -> fallback

-- | Require a specific role
requireRole
  :: forall user w i
   . HasRole user
  => Session user
  -> String  -- Required role
  -> HH.HTML w i  -- Protected content
  -> HH.HTML w i  -- Fallback
  -> Effect (HH.HTML w i)
requireRole session role protected fallback = do
  authState <- getAuthState session
  maybeUser <- getUser session
  pure $ case authState, maybeUser of
    Authenticated, Just user ->
      if Array.elem role (getRoles user)
        then protected
        else fallback
    _, _ -> fallback

-- | Require any of multiple roles
requireRoles
  :: forall user w i
   . HasRole user
  => Session user
  -> Array String  -- Any of these roles
  -> HH.HTML w i
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
requireRoles session roles protected fallback = do
  authState <- getAuthState session
  maybeUser <- getUser session
  pure $ case authState, maybeUser of
    Authenticated, Just user ->
      let userRoles = getRoles user
      in if Array.any (\r -> Array.elem r userRoles) roles
        then protected
        else fallback
    _, _ -> fallback

-- | Require a specific permission
requirePermission
  :: forall user w i
   . HasPermission user
  => Session user
  -> String  -- Required permission
  -> HH.HTML w i
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
requirePermission session permission protected fallback = do
  authState <- getAuthState session
  maybeUser <- getUser session
  pure $ case authState, maybeUser of
    Authenticated, Just user ->
      if Array.elem permission (getPermissions user)
        then protected
        else fallback
    _, _ -> fallback

-- | Require multiple permissions
requirePermissions
  :: forall user w i
   . HasPermission user
  => Session user
  -> Array String  -- All required permissions
  -> HH.HTML w i
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
requirePermissions session permissions protected fallback = do
  authState <- getAuthState session
  maybeUser <- getUser session
  pure $ case authState, maybeUser of
    Authenticated, Just user ->
      let userPerms = getPermissions user
      in if Array.all (\p -> Array.elem p userPerms) permissions
        then protected
        else fallback
    _, _ -> fallback

-- | Require any of multiple conditions
requireAny
  :: forall w i
   . Array (Effect Boolean)  -- Conditions
  -> HH.HTML w i
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
requireAny conditions protected fallback = do
  results <- sequence conditions
  pure $ if Array.any identity results
    then protected
    else fallback
  where
  sequence :: Array (Effect Boolean) -> Effect (Array Boolean)
  sequence = traverse identity
  
  traverse :: forall a b. (a -> Effect b) -> Array a -> Effect (Array b)
  traverse f arr = case Array.uncons arr of
    Nothing -> pure []
    Just { head, tail } -> do
      b <- f head
      bs <- traverse f tail
      pure $ [b] <> bs

-- | Require all conditions
requireAll
  :: forall w i
   . Array (Effect Boolean)
  -> HH.HTML w i
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
requireAll conditions protected fallback = do
  results <- sequence conditions
  pure $ if Array.all identity results
    then protected
    else fallback
  where
  sequence :: Array (Effect Boolean) -> Effect (Array Boolean)
  sequence = traverse identity
  
  traverse :: forall a b. (a -> Effect b) -> Array a -> Effect (Array b)
  traverse f arr = case Array.uncons arr of
    Nothing -> pure []
    Just { head, tail } -> do
      b <- f head
      bs <- traverse f tail
      pure $ [b] <> bs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // conditional rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render different content based on auth state
withAuth
  :: forall user w i
   . Session user
  -> { authenticated :: HH.HTML w i
     , unauthenticated :: HH.HTML w i
     }
  -> Effect (HH.HTML w i)
withAuth session { authenticated, unauthenticated } = do
  authState <- getAuthState session
  pure $ case authState of
    Authenticated -> authenticated
    _ -> unauthenticated

-- | Render content only when authenticated
whenAuthenticated
  :: forall user w i
   . Session user
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
whenAuthenticated session content = do
  authState <- getAuthState session
  pure $ case authState of
    Authenticated -> content
    _ -> HH.text ""

-- | Render content only when NOT authenticated
unlessAuthenticated
  :: forall user w i
   . Session user
  -> HH.HTML w i
  -> Effect (HH.HTML w i)
unlessAuthenticated session content = do
  authState <- getAuthState session
  pure $ case authState of
    Authenticated -> HH.text ""
    _ -> content
