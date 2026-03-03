{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DataKinds #-}
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // Foundry.Core.Effects.Do
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- QualifiedDo support for FoundryM.
--
-- Usage:
--
--     {-# LANGUAGE QualifiedDo #-}
--     import Foundry.Core.Effects.Do qualified as F
--
--     handleScrape :: ScrapeRequest -> FoundryM '[Net, Fs, Crypto] ScrapeResult
--     handleScrape req = F.do
--       F.return ()                              -- Pure, no effect labels added
--       url      <- parseUrl req                  -- Pure
--       response <- fetchPage url                 -- '[Net]
--       elements <- extractElements response      -- '[Fs]
--       signed   <- signResult elements           -- '[Crypto]
--       F.return signed                           -- grade = Net ∪ Fs ∪ Crypto
--
-- Regular do-notation still works in the same module for IO/other monads.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Foundry.Core.Effects.Do
  ( return
  , (>>=)
  , (>>)
  , fail
  ) where

import Prelude (String)
import Control.Effect qualified as E
import Foundry.Core.Effects.Graded (FoundryM)
import Foundry.Core.Effects.Grade (GradeLabel, Union)

-- | Graded return. Grade: Pure ('[]). 
return :: a -> FoundryM '[] a
return = E.return

-- | Graded bind. Grade: Union f g.
(>>=) :: FoundryM f a -> (a -> FoundryM g b) -> FoundryM (Union f g) b
(>>=) = (E.>>=)

-- | Graded sequence. Grade: Union f g.
(>>) :: FoundryM f a -> FoundryM g b -> FoundryM (Union f g) b
(>>) = (E.>>)

-- | Graded fail. Bottom — graded monads have no meaningful failure.
fail :: String -> a
fail = E.fail
