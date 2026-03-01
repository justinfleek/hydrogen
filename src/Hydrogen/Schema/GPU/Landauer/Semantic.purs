-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // gpu // landauer // semantic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Semantic types and information bundles for Landauer precision.
-- |
-- | Different data types have natural entropy bounds based on their semantic
-- | meaning. A pixel has ~24 bits of information, while a VAE latent has ~4 bits.
-- |
-- | The `InfoBundle` type describes data by its entropy and semantic type,
-- | allowing precision to be derived at materialization time rather than
-- | being specified upfront.

module Hydrogen.Schema.GPU.Landauer.Semantic
  ( -- * Semantic Types
    SemanticType(Pixel, Latent, Token, Embedding, Attention, Probability, Gradient, Accumulator)
  , semanticTypeEntropy
  , semanticTypeBits
  
  -- * Information Bundle
  , InfoBundle
  , infoBundle
  , bundleShape
  , bundleEntropy
  , bundleSemanticType
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.GPU.Landauer.Types
  ( Entropy
  , NaturalPrecision
  , entropy
  , naturalPrecision
  , unwrapPrecision
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // semantic types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic types with natural entropy bounds.
-- |
-- | Different data types have inherent information content bounds.
data SemanticType
  = Pixel         -- RGB pixels, ~24 bits
  | Latent        -- VAE latent space, ~4 bits
  | Token         -- Token IDs, log₂(vocab) bits
  | Embedding     -- Token embeddings, ~12 bits
  | Attention     -- Attention weights, ~8 bits
  | Probability   -- Output probabilities, ≤ log₂(classes)
  | Gradient      -- Gradients, ~8 bits
  | Accumulator   -- FP32 accumulator, ~32 bits

derive instance eqSemanticType :: Eq SemanticType

instance showSemanticType :: Show SemanticType where
  show Pixel = "Pixel"
  show Latent = "Latent"
  show Token = "Token"
  show Embedding = "Embedding"
  show Attention = "Attention"
  show Probability = "Probability"
  show Gradient = "Gradient"
  show Accumulator = "Accumulator"

-- | Get typical entropy for a semantic type
semanticTypeEntropy :: SemanticType -> Entropy
semanticTypeEntropy Pixel = entropy 24.0
semanticTypeEntropy Latent = entropy 4.0
semanticTypeEntropy Token = entropy 16.0      -- 65k vocab typical
semanticTypeEntropy Embedding = entropy 12.0
semanticTypeEntropy Attention = entropy 8.0
semanticTypeEntropy Probability = entropy 10.0 -- ~1000 classes
semanticTypeEntropy Gradient = entropy 8.0
semanticTypeEntropy Accumulator = entropy 32.0

-- | Get typical bit count for a semantic type
semanticTypeBits :: SemanticType -> Int
semanticTypeBits st = unwrapPrecision (naturalPrecision (semanticTypeEntropy st))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // information bundle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Information bundle — data described by entropy, not precision.
-- |
-- | Shape + Entropy + Semantic type. Precision is a **gauge choice** at
-- | materialization time, not part of the bundle definition.
type InfoBundle =
  { shape :: Array Int          -- Logical dimensions
  , entropy :: Entropy          -- Upper bound on bits of information
  , semanticType :: SemanticType
  }

-- | Create an information bundle
infoBundle :: Array Int -> Entropy -> SemanticType -> InfoBundle
infoBundle shape ent semType =
  { shape: shape
  , entropy: ent
  , semanticType: semType
  }

-- | Get bundle shape
bundleShape :: InfoBundle -> Array Int
bundleShape b = b.shape

-- | Get bundle entropy
bundleEntropy :: InfoBundle -> Entropy
bundleEntropy b = b.entropy

-- | Get bundle semantic type
bundleSemanticType :: InfoBundle -> SemanticType
bundleSemanticType b = b.semanticType
