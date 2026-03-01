-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // gpu // kernel // text // composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kernel Composition and Dispatch Utilities
-- |
-- | Provides functions for composing kernels, computing workgroup/dispatch
-- | sizes, estimating costs, and transforming kernel pipelines.

module Hydrogen.GPU.Kernel.Text.Composition
  ( -- * Kernel Composition
    sequenceTextKernels
  , conditionalTextKernel
  , andThen
  , applyTo
  , composeTransforms
  , pipeTransforms
  , identityKernel
  , isIdentityKernel
  , sequenceAll
  , mapSequence
  
  -- * Dispatch Calculation
  , computeTextWorkgroupSize
  , computeTextDispatchSize
  , getKernelDimensions
  
  -- * Cost Estimation
  , estimateTextKernelCost
  , isKernelCheaper
  , isKernelCostAcceptable
  , isZeroCostKernel
  , exceedsCostBudget
  , cheaperKernel
  , categorizeKernelCost
  , compareKernelCost
  , kernelCostOrder
  , orderKernelsByCost
  
  -- * Kernel Analysis
  , mapKernels
  , isKernelDimensionsValid
  , isWorkgroupSizeValid
  , allKernelsSatisfy
  , anyKernelSatisfies
  , foldKernels
  , traverseKernels
  , foldrKernels
  , foldMapKernels
  , sequenceKernelEffects
  , forEachKernel
  
  -- * Effect Utilities
  , flipShadowOffset
  , invertShadowDirection
  
  -- * Algebraic Composition
  , identityTransform
  , selectKernel
  , chainKernelEffects
  , curryKernelConfig
  , uncurryKernelConfig
  , swapDimensions
  , dimensionPair
  , traversableArrayWitness
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Applicative
  , class Bind
  , class Eq
  , Ordering(LT, EQ, GT)
  , map
  , pure
  , bind
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (&&)
  , (||)
  , (<<<)
  , (>>>)
  , otherwise
  , negate
  , compare
  , identity
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Tuple (Tuple(Tuple), fst, curry, uncurry, swap)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Monoid (class Monoid)
import Data.Foldable (class Foldable, foldl, foldr, foldMap)
import Data.Traversable (class Traversable, traverse, sequence, for)

import Hydrogen.GPU.Kernel.Text.Types
  ( WorkgroupSize
  , DispatchSize
  , TextKernel
      ( KernelGlyphRasterize
      , KernelTextLayout
      , KernelSubpixelAA
      , KernelCursorBlink
      , KernelTextMask
      , KernelTextSequence
      , KernelTextNoop
      )
  , GlyphRasterizeKernel(GlyphRasterizeKernel)
  , TextLayoutKernel(TextLayoutKernel)
  , SubpixelAAKernel(SubpixelAAKernel)
  , CursorBlinkKernel(CursorBlinkKernel)
  , TextMaskKernel(TextMaskKernel)
  , ShadowConfig
  , TextEffect(EffectShadow)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // kernel composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence multiple text kernels
sequenceTextKernels :: Array TextKernel -> TextKernel
sequenceTextKernels kernels =
  case Array.length kernels of
    0 -> KernelTextNoop
    1 -> case Array.head kernels of
           Nothing -> KernelTextNoop
           Just k -> k
    _ -> KernelTextSequence kernels

-- | Conditional text kernel execution
conditionalTextKernel 
  :: Boolean 
  -> TextKernel 
  -> TextKernel 
  -> TextKernel
conditionalTextKernel condition thenKernel elseKernel =
  if condition
    then thenKernel
    else elseKernel

-- | Pipeline composition: sequence two kernels
-- | Uses >>> internally for function chaining
andThen :: TextKernel -> TextKernel -> TextKernel
andThen k1 k2 = sequenceTextKernels [k1, k2]

-- | Pipeline composition: apply transform then kernel
-- | Uses <<< internally for function composition
applyTo :: (TextKernel -> TextKernel) -> TextKernel -> TextKernel
applyTo f k = f k

-- | Compose two kernel transforms (right to left)
composeTransforms :: (TextKernel -> TextKernel) -> (TextKernel -> TextKernel) -> (TextKernel -> TextKernel)
composeTransforms f g = f <<< g

-- | Compose two kernel transforms (left to right)
pipeTransforms :: (TextKernel -> TextKernel) -> (TextKernel -> TextKernel) -> (TextKernel -> TextKernel)
pipeTransforms f g = f >>> g

-- | Identity kernel (for composition)
identityKernel :: TextKernel
identityKernel = KernelTextNoop

-- | Zero-cost operation check
isIdentityKernel :: TextKernel -> Boolean
isIdentityKernel KernelTextNoop = true
isIdentityKernel _ = false

-- | Sequence all kernels from foldable
sequenceAll :: forall f. Foldable f => f TextKernel -> TextKernel
sequenceAll kernels = 
  KernelTextSequence (foldl (\acc k -> Array.snoc acc k) [] kernels)

-- | Map and sequence kernels  
mapSequence :: forall a. (a -> TextKernel) -> Array a -> TextKernel
mapSequence f items = sequenceTextKernels (map f items)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dispatch calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute workgroup size for text kernel
computeTextWorkgroupSize :: TextKernel -> WorkgroupSize
computeTextWorkgroupSize kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) -> k.config.workgroupSize
    KernelTextLayout (TextLayoutKernel k) -> k.config.workgroupSize
    KernelSubpixelAA (SubpixelAAKernel k) -> k.config.workgroupSize
    KernelCursorBlink (CursorBlinkKernel k) -> k.config.workgroupSize
    KernelTextMask (TextMaskKernel k) -> k.config.workgroupSize
    KernelTextSequence kernels -> 
      case Array.head kernels of
        Nothing -> { x: 8, y: 8, z: 1 }
        Just k -> computeTextWorkgroupSize k
    KernelTextNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size for text kernel
computeTextDispatchSize :: TextKernel -> DispatchSize
computeTextDispatchSize kernel =
  let
    workgroup = computeTextWorkgroupSize kernel
    dims = getKernelDimensions kernel
    divCeil a b = (a + b - 1) / b
  in
    { x: divCeil dims.width workgroup.x
    , y: divCeil dims.height workgroup.y
    , z: 1
    }

-- | Get kernel dimensions
getKernelDimensions :: TextKernel -> { width :: Int, height :: Int }
getKernelDimensions kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextLayout (TextLayoutKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelSubpixelAA (SubpixelAAKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelCursorBlink (CursorBlinkKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextMask (TextMaskKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextSequence kernels ->
      case Array.head kernels of
        Nothing -> { width: 0, height: 0 }
        Just k -> getKernelDimensions k
    KernelTextNoop -> { width: 0, height: 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // cost estimation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimate kernel execution cost (microseconds)
estimateTextKernelCost :: TextKernel -> Number
estimateTextKernelCost kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) ->
      -- SDF generation is expensive: ~100us per glyph
      Int.toNumber (k.codepointEnd - k.codepointStart + 1) * 100.0
    KernelTextLayout (TextLayoutKernel k) ->
      -- Layout is fast: ~1us per character
      Int.toNumber (Array.length k.runs) * 100.0
    KernelSubpixelAA (SubpixelAAKernel k) ->
      -- Subpixel AA: ~10us per 1K pixels
      Int.toNumber (k.config.width * k.config.height) / 100.0
    KernelCursorBlink _ ->
      -- Cursor is trivial: ~1us
      1.0
    KernelTextMask (TextMaskKernel k) ->
      -- Effects: ~5us per effect per 1K pixels
      Int.toNumber (Array.length k.effects) * 
      Int.toNumber (k.config.width * k.config.height) / 200.0
    KernelTextSequence kernels ->
      foldlArray (\acc k -> acc + estimateTextKernelCost k) 0.0 kernels
    KernelTextNoop -> 0.0

-- | Compare two kernels by estimated cost
-- | Returns true if the first kernel is cheaper than the second
isKernelCheaper :: TextKernel -> TextKernel -> Boolean
isKernelCheaper k1 k2 = estimateTextKernelCost k1 < estimateTextKernelCost k2

-- | Check if kernel cost is within acceptable bounds
-- | Bounds are in microseconds
isKernelCostAcceptable :: Number -> Number -> TextKernel -> Boolean
isKernelCostAcceptable minCost maxCost kernel =
  let cost = estimateTextKernelCost kernel
  in cost >= minCost && cost <= maxCost

-- | Check if a kernel has zero cost (noop or empty sequence)
isZeroCostKernel :: TextKernel -> Boolean
isZeroCostKernel kernel = estimateTextKernelCost kernel == 0.0

-- | Check if kernel exceeds a cost threshold (for budgeting)
exceedsCostBudget :: Number -> TextKernel -> Boolean
exceedsCostBudget budget kernel = estimateTextKernelCost kernel > budget

-- | Select the cheaper of two kernels
cheaperKernel :: TextKernel -> TextKernel -> TextKernel
cheaperKernel k1 k2 =
  if isKernelCheaper k1 k2
    then k1
    else k2

-- | Categorize kernel cost
-- | Returns "trivial" (<10us), "fast" (<100us), "moderate" (<1000us), "expensive"
categorizeKernelCost :: TextKernel -> String
categorizeKernelCost kernel =
  let cost = estimateTextKernelCost kernel
  in if cost < 10.0 then "trivial"
     else if cost < 100.0 then "fast"
     else if cost < 1000.0 then "moderate"
     else "expensive"

-- | Compare kernel costs
compareKernelCost :: TextKernel -> TextKernel -> Ordering
compareKernelCost k1 k2 = compare (estimateTextKernelCost k1) (estimateTextKernelCost k2)

-- | Sort kernels by cost (returns indices)
-- | Useful for scheduling optimization
kernelCostOrder :: Array TextKernel -> Array Int
kernelCostOrder kernels =
  map fst (Array.sortBy compareCosts indexed)
  where
    indexed = Array.mapWithIndex Tuple kernels
    compareCosts (Tuple _ k1) (Tuple _ k2) = compareKernelCost k1 k2

-- | Compare kernel costs returning Ordering
orderKernelsByCost :: TextKernel -> TextKernel -> Ordering
orderKernelsByCost k1 k2 =
  let c1 = estimateTextKernelCost k1
      c2 = estimateTextKernelCost k2
  in if c1 < c2 then LT
     else if c1 > c2 then GT
     else EQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // kernel analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a transformation over all kernels in a sequence
-- | For non-sequence kernels, applies the transform directly
mapKernels :: (TextKernel -> TextKernel) -> TextKernel -> TextKernel
mapKernels f kernel =
  case kernel of
    KernelTextSequence kernels -> KernelTextSequence (map f kernels)
    other -> f other

-- | Validate kernel dimensions are positive
isKernelDimensionsValid :: TextKernel -> Boolean
isKernelDimensionsValid kernel =
  let dims = getKernelDimensions kernel
  in dims.width > 0 && dims.height > 0 || isZeroCostKernel kernel

-- | Validate workgroup size is reasonable (1-1024 per dimension)
isWorkgroupSizeValid :: TextKernel -> Boolean
isWorkgroupSizeValid kernel =
  let ws = computeTextWorkgroupSize kernel
  in ws.x > 0 && ws.x <= 1024 
  && ws.y > 0 && ws.y <= 1024 
  && ws.z > 0 && ws.z <= 64

-- | Check if all kernels in a sequence meet a predicate
allKernelsSatisfy :: (TextKernel -> Boolean) -> TextKernel -> Boolean
allKernelsSatisfy pred kernel =
  case kernel of
    KernelTextSequence kernels -> foldlArray (\acc k -> acc && pred k) true kernels
    KernelTextNoop -> true
    other -> pred other

-- | Check if any kernel in a sequence meets a predicate
anyKernelSatisfies :: (TextKernel -> Boolean) -> TextKernel -> Boolean
anyKernelSatisfies pred kernel =
  case kernel of
    KernelTextSequence kernels -> foldlArray (\acc k -> acc || pred k) false kernels
    KernelTextNoop -> false
    other -> pred other

-- | Fold over kernel sequence with accumulator
foldKernels :: forall a. (a -> TextKernel -> a) -> a -> TextKernel -> a
foldKernels f acc kernel =
  case kernel of
    KernelTextSequence kernels -> foldl f acc kernels
    KernelTextNoop -> acc
    other -> f acc other

-- | Traverse kernel sequence with effect
traverseKernels :: forall m. Applicative m => (TextKernel -> m TextKernel) -> TextKernel -> m TextKernel
traverseKernels f kernel =
  case kernel of
    KernelTextSequence kernels -> 
      map KernelTextSequence (traverse f kernels)
    KernelTextNoop -> pure KernelTextNoop
    other -> f other

-- | Right fold over kernels (builds structure from right)
foldrKernels :: forall a. (TextKernel -> a -> a) -> a -> Array TextKernel -> a
foldrKernels f z kernels = foldr f z kernels

-- | Map kernels to monoidal summary
foldMapKernels :: forall m. Monoid m => (TextKernel -> m) -> Array TextKernel -> m
foldMapKernels f kernels = foldMap f kernels

-- | Sequence kernel effects
sequenceKernelEffects :: forall m. Applicative m => Array (m TextKernel) -> m (Array TextKernel)
sequenceKernelEffects = sequence

-- | For-each kernel (flipped traverse)
forEachKernel :: forall m a. Applicative m => Array a -> (a -> m TextKernel) -> m (Array TextKernel)
forEachKernel = for

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // effect utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Negate shadow offset (flip shadow direction)
flipShadowOffset :: ShadowConfig -> ShadowConfig
flipShadowOffset cfg = cfg 
  { offsetX = negate cfg.offsetX
  , offsetY = negate cfg.offsetY
  }

-- | Create inverted shadow effect (light from opposite direction)
invertShadowDirection :: TextEffect -> TextEffect
invertShadowDirection effect =
  case effect of
    EffectShadow cfg -> EffectShadow (flipShadowOffset cfg)
    other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // algebraic composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity function for kernel transforms
identityTransform :: TextKernel -> TextKernel
identityTransform = identity

-- | Conditional kernel selection using otherwise pattern
selectKernel :: Boolean -> TextKernel -> TextKernel -> TextKernel
selectKernel cond k1 k2
  | cond = k1
  | otherwise = k2

-- | Chain kernel operations using bind
chainKernelEffects :: forall m a b. Bind m => m a -> (a -> m b) -> m b
chainKernelEffects ma f = ma `bind` f

-- | Curry a kernel config function
curryKernelConfig :: ((Int /\ Int) -> TextKernel) -> Int -> Int -> TextKernel
curryKernelConfig f = curry f

-- | Uncurry a kernel config function
uncurryKernelConfig :: (Int -> Int -> TextKernel) -> (Int /\ Int) -> TextKernel
uncurryKernelConfig f = uncurry f

-- | Swap dimensions in a tuple
swapDimensions :: forall a b. Tuple a b -> Tuple b a
swapDimensions = swap

-- | Create a dimension tuple directly
dimensionPair :: Int -> Int -> Int /\ Int
dimensionPair w h = w /\ h

-- | Witness that Array is Traversable
traversableArrayWitness :: forall a. Traversable Array => Array a -> Array a
traversableArrayWitness = identity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr =
  case Array.uncons arr of
    Nothing -> init
    Just { head, tail } -> foldlArray f (f init head) tail
