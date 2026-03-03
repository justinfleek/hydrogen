{-# LANGUAGE TypeFamilies, ConstraintKinds, PolyKinds #-}

-- | QualifiedDo-style support for coeffect comonads.
--
-- Usage with @comonadic@ style (if you define a @do@-like combinator):
--
-- @
-- {-\# LANGUAGE QualifiedDo \#-}
-- import Control.Coeffect.Do qualified as C
-- @
--
-- Since Haskell has no built-in comonadic @do@-notation, this module
-- primarily provides a consistent qualified namespace for 'extract'
-- and 'extend', paralleling "Control.Effect.Do".

module Control.Coeffect.Do
  ( extract
  , extend
  ) where

import Prelude ()
import Control.Coeffect (Coeffect(..))
import qualified Control.Coeffect as C

-- | Re-export coeffect 'extract'.
extract :: Coeffect c => c (Unit c) a -> a
extract = C.extract

-- | Re-export coeffect 'extend'.
extend :: (Coeffect c, Inv c s t) => (c t a -> b) -> c (Plus c s t) a -> c s b
extend = C.extend
