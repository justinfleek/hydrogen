-- | Unique ID Generation
-- |
-- | Generates unique IDs for accessibility attributes (aria-labelledby, etc.)
-- | Uses a simple counter-based approach.
-- |
-- | Vendored from purescript-radix (straylight/purescript-radix)
module Hydrogen.UI.Id
  ( IdGenerator
  , createIdGenerator
  , nextId
  , useId
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref as Ref

-- | An ID generator that produces unique IDs with a given prefix
type IdGenerator = 
  { prefix :: String
  , counterRef :: Ref.Ref Int
  }

-- | Create a new ID generator with the given prefix
createIdGenerator :: String -> Effect IdGenerator
createIdGenerator prefix = do
  counterRef <- Ref.new 0
  pure { prefix, counterRef }

-- | Generate the next unique ID
nextId :: IdGenerator -> Effect String
nextId gen = do
  n <- Ref.read gen.counterRef
  Ref.write (n + 1) gen.counterRef
  pure $ gen.prefix <> "-" <> show n

-- | Generate a unique ID for a specific use case
-- | e.g., useId gen "dialog" "content" -> "hydrogen-dialog-0-content"
useId :: IdGenerator -> String -> Effect String
useId gen suffix = do
  base <- nextId gen
  pure $ base <> "-" <> suffix
