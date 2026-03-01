-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // submodular // matroid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matroid Constraint Types and Instances.
-- |
-- | A matroid (V, I) encodes independence constraints:
-- | - V is the ground set
-- | - I ⊆ 2^V is the family of independent sets
-- |
-- | ## Matroid Axioms
-- |
-- | 1. ∅ ∈ I (empty set is independent)
-- | 2. If A ∈ I and B ⊆ A, then B ∈ I (hereditary)
-- | 3. If A, B ∈ I and |A| < |B|, then ∃e ∈ B\A : A ∪ {e} ∈ I (exchange)
-- |
-- | ## Supported Matroids
-- |
-- | - **Cardinality**: I = {S ⊆ V : |S| ≤ k}
-- | - **Partition**: V partitioned into blocks, select ≤ k_i from each
-- | - **Uniform**: All k-subsets are bases
-- | - **Graphic**: Independent sets are forests in a graph
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Optimize.Submodular.Types.GroundSet
-- | - Hydrogen.Schema.Tensor.Dimension (Dim)

module Hydrogen.Optimize.Submodular.Types.Matroid
  ( -- * Matroid Typeclass
    class Matroid
  , rank
  , maxRank
  , isIndependent
  , canExtend
  , extensionElements
  
    -- * Rank Type
  , MatroidRank(MatroidRank)
  , IndependentSet
  
    -- * Matroid Implementations
  , CardinalityMatroid(CardinalityMatroid)
  , PartitionMatroid(PartitionMatroid)
  , PartitionBlock(PartitionBlock)
  , UniformMatroid(UniformMatroid)
  , GraphicMatroid(GraphicMatroid)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , min
  , not
  , show
  , (<>)
  , (<=)
  , (<)
  , (>=)
  , (+)
  , (-)
  , (&&)
  )

import Data.Array as Array
import Data.Foldable (foldl, any, all)
import Data.Map (Map)
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), unwrapDim)

import Hydrogen.Optimize.Submodular.Types.GroundSet
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // matroid constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matroid rank (maximum independent set size).
-- |
-- | For a cardinality matroid with constraint |S| ≤ k, the rank is k.
-- | Bounded to [1, 2^30] since rank must be positive.
newtype MatroidRank = MatroidRank Dim

derive instance eqMatroidRank :: Eq MatroidRank
derive instance ordMatroidRank :: Ord MatroidRank

instance showMatroidRank :: Show MatroidRank where
  show (MatroidRank (Dim k)) = "rank=" <> show k

-- | A set that is independent in the matroid.
-- |
-- | Invariant: the set satisfies the matroid independence axioms.
type IndependentSet :: Type -> Type
type IndependentSet v = ElementSet v

-- | A matroid (V, I) where:
-- | - V is the ground set
-- | - I ⊆ 2^V is the family of independent sets
-- |
-- | Matroid axioms:
-- | 1. ∅ ∈ I (empty set is independent)
-- | 2. If A ∈ I and B ⊆ A, then B ∈ I (hereditary)
-- | 3. If A, B ∈ I and |A| < |B|, then ∃e ∈ B\A : A ∪ {e} ∈ I (exchange)
-- |
-- | Encoded as a typeclass to enable different matroid implementations.
class Matroid :: Type -> Type -> Constraint
class Matroid m v | m -> v where
  -- | Matroid rank function: r(S) = max{|I| : I ⊆ S, I ∈ I}
  rank :: m -> ElementSet v -> MatroidRank
  
  -- | Maximum rank (rank of entire ground set)
  maxRank :: m -> MatroidRank
  
  -- | Check if a set is independent
  isIndependent :: m -> ElementSet v -> Boolean
  
  -- | Check if adding an element maintains independence
  canExtend :: m -> Element v -> IndependentSet v -> Boolean
  
  -- | Get all elements that can extend the current independent set
  extensionElements :: m -> IndependentSet v -> Array (Element v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // matroid implementations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cardinality matroid: I = {S ⊆ V : |S| ≤ k}
-- |
-- | The simplest matroid constraint: select at most k elements.
-- | Rank function: r(S) = min(|S|, k)
newtype CardinalityMatroid :: Type -> Type
newtype CardinalityMatroid v = CardinalityMatroid
  { k :: Dim                       -- ^ Cardinality constraint
  , groundSet :: GroundSet v       -- ^ Ground set V
  }

derive instance eqCardinalityMatroid :: Eq (CardinalityMatroid v)

instance showCardinalityMatroid :: Show (CardinalityMatroid v) where
  show (CardinalityMatroid c) = "Card≤" <> show c.k

-- | A block in a partition matroid.
-- |
-- | Each block has elements and a cardinality limit.
newtype PartitionBlock :: Type -> Type
newtype PartitionBlock v = PartitionBlock
  { elements :: ElementSet v       -- ^ Elements in this block
  , limit :: Dim                   -- ^ Max elements selectable from this block
  }

derive instance eqPartitionBlock :: Eq (PartitionBlock v)

instance showPartitionBlock :: Show (PartitionBlock v) where
  show (PartitionBlock b) = "Block[" <> show b.limit <> "]"

-- | Partition matroid: V partitioned into blocks, select ≤ k_i from each.
-- |
-- | I = {S : |S ∩ V_i| ≤ k_i for all blocks i}
-- |
-- | Generalizes cardinality matroids. Common in resource allocation.
newtype PartitionMatroid :: Type -> Type
newtype PartitionMatroid v = PartitionMatroid
  { blocks :: Array (PartitionBlock v)  -- ^ Partition blocks
  , groundSet :: GroundSet v            -- ^ Ground set V
  }

derive instance eqPartitionMatroid :: Eq (PartitionMatroid v)

instance showPartitionMatroid :: Show (PartitionMatroid v) where
  show (PartitionMatroid p) = "Partition[" <> show (Array.length p.blocks) <> " blocks]"

-- | Uniform matroid: all k-subsets are bases.
-- |
-- | I = {S ⊆ V : |S| ≤ k}
-- | Same as cardinality matroid, but emphasizes that any k elements form a basis.
newtype UniformMatroid :: Type -> Type
newtype UniformMatroid v = UniformMatroid
  { n :: Dim                       -- ^ Ground set size
  , k :: Dim                       -- ^ Rank
  }

derive instance eqUniformMatroid :: Eq (UniformMatroid v)

instance showUniformMatroid :: Show (UniformMatroid v) where
  show (UniformMatroid u) = "U(" <> show u.n <> "," <> show u.k <> ")"

-- | Graphic matroid: independent sets are forests in a graph.
-- |
-- | V = edges of graph G
-- | I = {S ⊆ E : S forms a forest (no cycles)}
-- |
-- | Rank = |V(G)| - 1 for connected G (spanning tree).
newtype GraphicMatroid :: Type -> Type
newtype GraphicMatroid v = GraphicMatroid
  { vertices :: Dim                -- ^ Number of vertices in graph
  , edges :: GroundSet v           -- ^ Edges as ground set
  , adjacency :: Map Int (Set Int) -- ^ Adjacency list: vertex -> neighbors
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // matroid instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cardinality matroid instance: I = {S ⊆ V : |S| ≤ k}
-- |
-- | Rank function: r(S) = min(|S|, k)
instance matroidCardinality :: Matroid (CardinalityMatroid v) v where
  rank (CardinalityMatroid { k }) s =
    let setSize = Set.size s
        kVal = unwrapDim k
    in MatroidRank (Dim (min setSize kVal))
  
  maxRank (CardinalityMatroid { k }) = MatroidRank k
  
  isIndependent (CardinalityMatroid { k }) s =
    Set.size s <= unwrapDim k
  
  canExtend (CardinalityMatroid { k }) _ s =
    Set.size s < unwrapDim k
  
  extensionElements (CardinalityMatroid { k, groundSet }) s =
    if Set.size s >= unwrapDim k
      then []
      else
        let (GroundSet { elements }) = groundSet
        in Array.filter (\e -> not (Set.member e s)) elements

-- | Partition matroid instance: select ≤ k_i from each partition block.
-- |
-- | I = {S : ∀i. |S ∩ V_i| ≤ k_i}
-- | Rank function: r(S) = Σ_i min(|S ∩ V_i|, k_i)
instance matroidPartition :: Matroid (PartitionMatroid v) v where
  rank (PartitionMatroid { blocks }) s =
    let blockRank :: PartitionBlock v -> Int
        blockRank (PartitionBlock { elements, limit }) =
          let intersection = Set.intersection s elements
          in min (Set.size intersection) (unwrapDim limit)
        totalRank = foldl (\acc b -> acc + blockRank b) 0 blocks
    in MatroidRank (Dim totalRank)
  
  maxRank (PartitionMatroid { blocks }) =
    let sumLimits = foldl (\acc (PartitionBlock { limit }) -> acc + unwrapDim limit) 0 blocks
    in MatroidRank (Dim sumLimits)
  
  isIndependent (PartitionMatroid { blocks }) s =
    all (blockSatisfied s) blocks
    where
      blockSatisfied :: ElementSet v -> PartitionBlock v -> Boolean
      blockSatisfied set (PartitionBlock { elements, limit }) =
        Set.size (Set.intersection set elements) <= unwrapDim limit
  
  canExtend (PartitionMatroid { blocks }) e s =
    any (canAddToBlock e s) blocks
    where
      canAddToBlock :: Element v -> ElementSet v -> PartitionBlock v -> Boolean
      canAddToBlock elem set (PartitionBlock { elements, limit }) =
        Set.member elem elements &&
        Set.size (Set.intersection set elements) < unwrapDim limit
  
  extensionElements (PartitionMatroid { blocks, groundSet }) s =
    let (GroundSet { elements }) = groundSet
        canAdd e = not (Set.member e s) && any (canAddToBlock e s) blocks
        canAddToBlock elem set (PartitionBlock { elements: blockElems, limit }) =
          Set.member elem blockElems &&
          Set.size (Set.intersection set blockElems) < unwrapDim limit
    in Array.filter canAdd elements

-- | Uniform matroid instance: U_{n,k} where all k-subsets are bases.
-- |
-- | Equivalent to cardinality matroid, emphasizes basis structure.
instance matroidUniform :: Matroid (UniformMatroid v) v where
  rank (UniformMatroid { k }) s =
    let setSize = Set.size s
        kVal = unwrapDim k
    in MatroidRank (Dim (min setSize kVal))
  
  maxRank (UniformMatroid { k }) = MatroidRank k
  
  isIndependent (UniformMatroid { k }) s =
    Set.size s <= unwrapDim k
  
  canExtend (UniformMatroid { k }) _ s =
    Set.size s < unwrapDim k
  
  extensionElements (UniformMatroid { n, k }) s =
    if Set.size s >= unwrapDim k
      then []
      else
        let nVal = unwrapDim n
            allElements = Array.range 0 (nVal - 1)
        in map Element (Array.filter (\i -> not (Set.member (Element i) s)) allElements)
