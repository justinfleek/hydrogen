-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // Effects.Grade
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--  Type-level grade lattice for the gateway graded monad.
--
--  Effect categories form a bounded join-semilattice:
--
--      Pure ⊑ Net ⊑ Net∪Auth ⊑ ... ⊑ ⊤
--
--  Composition (Plus) is set union: if f : GatewayM '[Net] a and
--  g : GatewayM '[Auth] b, then (f >>= \_ -> g) : GatewayM '[Net, Auth] b.
--
--  This is the type-level tracking. Runtime cost data (latency, tokens,
--  timestamps) is still accumulated at the value level in GatewayGrade,
--  GatewayCoEffect, and GatewayProvenance — those are orthogonal.
--
--  Corresponds to Continuity.lean's Coeffect inductive type, lifted to kinds.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Effect.Grade
  ( -- * Effect labels
    GradeLabel

  -- * Type-level labels
  , Net
  , Auth
  , Config
  , Log
  , Crypto
  , Fs

    -- * Type-level set operations
  , class Union
  , class Member

    -- * Convenience aliases
  , Pure
  , NetOnly
  , AuthOnly
  , NetAuth
  , Full
  ) where

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // imports
-- ════════════════════════════════════════════════════════════════════════════

import Prim.Ordering (Ordering, LT, EQ, GT)
import Type.Data.List (type (:>), List', Nil')

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // effect labels
-- ════════════════════════════════════════════════════════════════════════════

-- | Effect labels — the atoms of the grade lattice.
-- Each label corresponds to a category of side effect that
-- the gateway may perform. A computation's type-level grade
-- is a sorted, deduplicated list of these labels.
data GradeLabel

-- | Network I/O (HTTP calls to providers)
foreign import data Net :: GradeLabel

-- | Authentication credential usage
foreign import data Auth :: GradeLabel

-- | Configuration access (env vars, files)
foreign import data Config :: GradeLabel

-- | Structured logging / observability
foreign import data Log :: GradeLabel

-- | Cryptographic operations (signing, hashing)
foreign import data Crypto :: GradeLabel

-- | Filesystem access outside sandbox
foreign import data Fs :: GradeLabel

-- ════════════════════════════════════════════════════════════════════════════
--                                              // type-level set operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Type-level sorted set union. This is the 'Plus' operation for our
-- graded monad: composing two computations unions their effect sets.
--
-- We maintain sorted order so that '[Net, Auth] ~ '[Auth, Net]' after
-- normalization. PureScript's instance resolution handles this.
class Union (xs :: List' GradeLabel) (ys :: List' GradeLabel) (result :: List' GradeLabel) 
  | xs ys -> result

-- Base case: left is empty
instance unionNil :: Union Nil' ys ys

-- Case: right is empty, left is non-empty
else instance unionConsNil :: Union (x :> xs) Nil' (x :> xs)

-- Recursive case: both non-empty — use ordered merge
else instance unionCons :: 
  ( LabelOrder x y ord
  , UnionOrd ord x y xs ys result
  ) => Union (x :> xs) (y :> ys) result

-- | Total ordering on effect labels.
-- Net < Auth < Config < Log < Crypto < Fs
class LabelOrder (a :: GradeLabel) (b :: GradeLabel) (ord :: Ordering) 
  | a b -> ord

-- Self-comparisons
instance labelOrderNetNet :: LabelOrder Net Net EQ
instance labelOrderAuthAuth :: LabelOrder Auth Auth EQ
instance labelOrderConfigConfig :: LabelOrder Config Config EQ
instance labelOrderLogLog :: LabelOrder Log Log EQ
instance labelOrderCryptoCrypto :: LabelOrder Crypto Crypto EQ
instance labelOrderFsFs :: LabelOrder Fs Fs EQ

-- Net < everything
instance labelOrderNetAuth :: LabelOrder Net Auth LT
instance labelOrderNetConfig :: LabelOrder Net Config LT
instance labelOrderNetLog :: LabelOrder Net Log LT
instance labelOrderNetCrypto :: LabelOrder Net Crypto LT
instance labelOrderNetFs :: LabelOrder Net Fs LT

-- Auth > Net, < Config, Log, Crypto, Fs
instance labelOrderAuthNet :: LabelOrder Auth Net GT
instance labelOrderAuthConfig :: LabelOrder Auth Config LT
instance labelOrderAuthLog :: LabelOrder Auth Log LT
instance labelOrderAuthCrypto :: LabelOrder Auth Crypto LT
instance labelOrderAuthFs :: LabelOrder Auth Fs LT

-- Config > Net, Auth
instance labelOrderConfigNet :: LabelOrder Config Net GT
instance labelOrderConfigAuth :: LabelOrder Config Auth GT
instance labelOrderConfigLog :: LabelOrder Config Log LT
instance labelOrderConfigCrypto :: LabelOrder Config Crypto LT
instance labelOrderConfigFs :: LabelOrder Config Fs LT

-- Log > Net, Auth, Config
instance labelOrderLogNet :: LabelOrder Log Net GT
instance labelOrderLogAuth :: LabelOrder Log Auth GT
instance labelOrderLogConfig :: LabelOrder Log Config GT
instance labelOrderLogCrypto :: LabelOrder Log Crypto LT
instance labelOrderLogFs :: LabelOrder Log Fs LT

-- Crypto > Net, Auth, Config, Log
instance labelOrderCryptoNet :: LabelOrder Crypto Net GT
instance labelOrderCryptoAuth :: LabelOrder Crypto Auth GT
instance labelOrderCryptoConfig :: LabelOrder Crypto Config GT
instance labelOrderCryptoLog :: LabelOrder Crypto Log GT
instance labelOrderCryptoFs :: LabelOrder Crypto Fs LT

-- Fs is largest
instance labelOrderFsNet :: LabelOrder Fs Net GT
instance labelOrderFsAuth :: LabelOrder Fs Auth GT
instance labelOrderFsConfig :: LabelOrder Fs Config GT
instance labelOrderFsLog :: LabelOrder Fs Log GT
instance labelOrderFsCrypto :: LabelOrder Fs Crypto GT

-- | Helper: ordered merge based on comparison result
class UnionOrd (ord :: Ordering) (x :: GradeLabel) (y :: GradeLabel)
               (xs :: List' GradeLabel) (ys :: List' GradeLabel) 
               (result :: List' GradeLabel) | ord x y xs ys -> result

-- x < y: x goes first, continue merging xs with (y:ys)
instance unionOrdLT :: Union xs (y :> ys) rest => UnionOrd LT x y xs ys (x :> rest)

-- x = y: dedup, continue merging xs with ys
instance unionOrdEQ :: Union xs ys rest => UnionOrd EQ x y xs ys (x :> rest)

-- x > y: y goes first, continue merging (x:xs) with ys
instance unionOrdGT :: Union (x :> xs) ys rest => UnionOrd GT x y xs ys (y :> rest)

-- | Type-level membership test.
-- @Member Net es@ holds iff Net is in the sorted list @es@.
class Member (x :: GradeLabel) (xs :: List' GradeLabel)

-- Found at head
instance memberHead :: Member x (x :> xs)

-- Search in tail (only if x > head, since list is sorted)
else instance memberTail :: Member x xs => Member x (y :> xs)

-- Note: No instance for Member x Nil' gives a type error at the call site,
-- which is exactly what we want: "you tried to do Net in a Pure context"

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // convenience aliases
-- ════════════════════════════════════════════════════════════════════════════

-- | Pure computation — no effects.
type Pure = Nil'

-- | Network-only computation.
type NetOnly = Net :> Nil'

-- | Auth-only computation.
type AuthOnly = Auth :> Nil'

-- | Network + Auth (the common case for provider calls).
type NetAuth = Net :> Auth :> Nil'

-- | Full effect set (everything).
type Full = Net :> Auth :> Config :> Log :> Crypto :> Fs :> Nil'
