{-# LANGUAGE TypeFamilies, ConstraintKinds, PolyKinds, ImportQualifiedPost #-}

-- | QualifiedDo support for graded monads.
--
-- Instead of @RebindableSyntax@ (which hijacks /all/ @do@-blocks in a module),
-- import this module qualified and use @QualifiedDo@:
--
-- @
-- {-\# LANGUAGE QualifiedDo \#-}
-- import Control.Effect.Do qualified as E
--
-- example :: Counter 2 Int
-- example = E.do
--   x <- tick 1
--   y <- tick 2
--   E.return (x + y)
-- @
--
-- Regular @do@-notation still works normally in the same module.
-- Both can coexist in the same function.

module Control.Effect.Do
  ( Control.Effect.Do.return
  , (Control.Effect.Do.>>=)
  , (Control.Effect.Do.>>)
  , Control.Effect.Do.fail
  ) where

import Prelude (String, error)
import Control.Effect (Effect(Unit, Plus, Inv))
import Control.Effect qualified as E

-- | Re-export graded 'return'.
return :: Effect m => a -> m (Unit m) a
return = E.return

-- | Re-export graded '>>='.
(>>=) :: (Effect m, Inv m f g) => m f a -> (a -> m g b) -> m (Plus m f g) b
(>>=) = (E.>>=)

-- | Re-export graded '>>'.
(>>) :: (Effect m, Inv m f g) => m f a -> m g b -> m (Plus m f g) b
(>>) = (E.>>)

-- | Graded monads have no meaningful failure. Bottom by default.
fail :: String -> a
fail = error
