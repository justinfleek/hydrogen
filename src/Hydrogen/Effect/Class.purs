-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // Control.Effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Specifies "parametric effect monads" which are essentially monads but
-- annotated by a type-level monoid formed by 'Plus' and 'Unit'.
--
-- Based on "Embedding Effect Systems in Haskell" (Orchard & Petricek, 2014)
-- and the effect-monad library.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Effect.Class
  ( class Effect
  , return
  , bind
  , discard
  , class Subeffect
  , sub
  ) where

import Type.Data.List (List')

import Hydrogen.Effect.Grade (GradeLabel, class Union, Pure)

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // effect type class
-- ════════════════════════════════════════════════════════════════════════════

-- | Specifies "parametric effect monads" which are essentially monads but
-- annotated by a type-level monoid formed by 'Plus' (Union) and 'Unit' (Pure).
--
-- The grade is a type-level list of GradeLabel atoms.
--
-- Laws:
--   Left identity:  bind (return a) f ≡ f a
--   Right identity: bind m return ≡ m
--   Associativity:  bind (bind m f) g ≡ bind m (\x -> bind (f x) g)
--
-- Grade laws (follow from monoid laws on Union/Pure):
--   Union Pure f ≡ f
--   Union f Pure ≡ f
--   Union (Union f g) h ≡ Union f (Union g h)
class Effect (m :: List' GradeLabel -> Type -> Type) where
  
  -- | Effect-parameterised version of 'return'. Annotated with Pure effect,
  -- denoting pure computation.
  return :: forall a. a -> m Pure a

  -- | Effect-parameterised version of '>>=' (bind). Combines
  -- two effect annotations 'f' and 'g' on its parameter computations into Union.
  bind :: forall f g fg a b. Union f g fg => m f a -> (a -> m g b) -> m fg b

-- | Sequence two effectful computations, discarding the first result.
discard :: forall m f g fg a b
         . Effect m
        => Union f g fg
        => m f a
        -> m g b
        -> m fg b
discard ma mb = bind ma (\_ -> mb)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // subeffect
-- ════════════════════════════════════════════════════════════════════════════

-- | Specifies subeffecting behaviour.
--
-- f ⊑ g means grade f is a subset of grade g.
-- This allows widening a computation's grade when needed.
class Subeffect (m :: List' GradeLabel -> Type -> Type) f g where
  sub :: forall a. m f a -> m g a
