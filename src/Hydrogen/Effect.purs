-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Effect System — Graded Monads Following Orchard & Petricek
-- |
-- | This module provides a complete graded effect system for Hydrogen,
-- | built on the foundations of "Embedding Effect Systems in Haskell"
-- | (Orchard & Petricek, Haskell 2014).
-- |
-- | ## Why Graded Monads?
-- |
-- | At billion-agent scale, knowing PRECISELY what effects a computation
-- | may perform is critical:
-- |
-- | - Type signatures document capabilities: `HydrogenM '[Net, Auth] a`
-- | - PureScript prevents unauthorized effects at compile time
-- | - Static analysis can optimize resource loading
-- | - Proofs can verify effect bounds
-- |
-- | ## Module Structure
-- |
-- | - `Hydrogen.Effect.Class` — The Effect type class (graded monad)
-- | - `Hydrogen.Effect.Grade` — Effect labels and type-level Union
-- | - `Hydrogen.Effect.Graded` — HydrogenM, the concrete graded monad
-- |
-- | ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Effect
  ( -- * Effect Class (Graded Monad)
    module Hydrogen.Effect.Class
  
  -- * Effect Grades
  , module Hydrogen.Effect.Grade
  
  -- * Graded Monad
  , module Hydrogen.Effect.Graded
  ) where

import Hydrogen.Effect.Class
  ( class Effect
  , return
  , bind
  , discard
  , class Subeffect
  , sub
  )

import Hydrogen.Effect.Grade
  ( GradeLabel
  , Net
  , Auth
  , Config
  , Log
  , Crypto
  , Fs
  , class Union
  , class Member
  , Pure
  , NetOnly
  , AuthOnly
  , NetAuth
  , Full
  )

import Hydrogen.Effect.Graded
  ( HydrogenM(HydrogenM)
  , HydrogenGrade
  , HydrogenCoEffect
  , runHydrogenM
  , runHydrogenMPure
  , emptyGrade
  , combineGrades
  , emptyCoEffect
  , liftPure
  , liftNet
  , liftAuth
  , liftConfig
  , liftLog
  , liftCrypto
  , liftAff
  )
