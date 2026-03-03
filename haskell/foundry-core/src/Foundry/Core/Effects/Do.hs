{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // Foundry.Core.Effects.Do
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- QualifiedDo support for FoundryM.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Foundry.Core.Effects.Do
  ( return
  , (>>=)
  , (>>)
  , fail
  ) where

import Prelude (String, error)
import Control.Effect qualified as E
import Foundry.Core.Effects.Graded (FoundryM)
import Foundry.Core.Effects.Grade (Union, Pure)

return :: a -> FoundryM Pure a
return = E.return

(>>=) :: FoundryM f a -> (a -> FoundryM g b) -> FoundryM (Union f g) b
(>>=) = (E.>>=)

(>>) :: FoundryM f a -> FoundryM g b -> FoundryM (Union f g) b
(>>) = (E.>>)

fail :: String -> a
fail = error
