-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // allocation // strategy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Allocation.Strategy — Frame allocation algorithms.
-- |
-- | ## Purpose
-- |
-- | Implements allocation strategies for distributing rendering resources:
-- | - Basic adaptive allocation (P0)
-- | - FAA-enhanced submodular optimization (P2)
-- |
-- | ## Architecture
-- |
-- | ```
-- | ViewportState + PerformanceState + AllocationState
-- |                      ↓
-- |           allocateFrame / allocateFrameFAA
-- |                      ↓
-- |              AllocationResult
-- | ```
-- |
-- | ## Algorithm Selection
-- |
-- | - allocateFrame: Simple tier-based allocation for real-time use
-- | - allocateFrameFAA: Optimal allocation via submodular optimization

module Hydrogen.GPU.FrameState.Allocation.Strategy
  ( -- * Basic Allocation
    allocateFrame
  , adaptiveSelection
  , adjustStepsForQuality
  
  -- * FAA-Enhanced Allocation
  , allocateFrameFAA
  , adaptiveSelectionFAA
  
  -- * Ground Set Conversion
  , regionsToGroundSetFAA
  
  -- * Oracle Creation
  , regionUtilityOracle
  
  -- * Utilities
  , intToNumSafe
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , max
  , min
  , ($)
  , (*)
  , (+)
  , (-)
  , (<)
  , (/=)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set as Set

-- FrameState types
import Hydrogen.GPU.FrameState
  ( ViewportState
  , PerformanceState
  , viewportLatentWidth
  , viewportLatentHeight
  )

-- Render.Online types
import Hydrogen.Render.Online.Core
  ( GridLevel
  , Region(Region)
  , RegionSelection(RegionSelection)
  , DiffusionSteps(DiffusionSteps)
  , RenderTier(Foveal, Peripheral, Background)
  , tierDefaultSteps
  , EpochId
  , nextEpoch
  )

-- Submodular Optimization Types
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , SubmodularOracle(SubmodularOracle)
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  , CardinalityMatroid(CardinalityMatroid)
  )

-- FAA-Enhanced Continuous Greedy
import Hydrogen.Optimize.Submodular.Continuous
  ( mkFAAConfig
  , continuousGreedyFAA
  , FractionalSolution
  , solutionCoord
  )

-- Min-Energy Rounding
import Hydrogen.Optimize.Submodular.Rounding
  ( mkMinEnergyConfig
  , minEnergyRound
  )

-- Dimension type
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim))

-- Math functions
import Hydrogen.Math.Core (sqrt) as Math

-- Local types
import Hydrogen.GPU.FrameState.Allocation.Types
  ( AllocationState
  , AllocationResult
  , FAAAllocationConfig(FAAAllocationConfig)
  , RegionIndex
  , Tuple(Tuple)
  , allocationGridLevel
  , allocationRegions
  , faaTargetIterations
  , faaMaxRegions
  , faaRoundingCandidates
  , faaQualityWeight
  , faaCoverageWeight
  )

import Hydrogen.GPU.FrameState.Allocation.Regions
  ( selectGridLevel
  , viewportToRegions
  )

import Hydrogen.GPU.FrameState.Allocation.Performance
  ( qualityFromPerformance
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // frame // allocation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Allocate rendering resources for a frame.
-- |
-- | Adapts allocation based on performance feedback:
-- | - If quality headroom is high (>0.7): use tier defaults
-- | - If quality headroom is medium (0.3-0.7): reduce background quality
-- | - If quality headroom is low (<0.3): reduce peripheral and background
-- |
-- | Will be enhanced with full submodular optimization in P2.
allocateFrame :: ViewportState -> PerformanceState -> AllocationState -> AllocationResult
allocateFrame vs perf state =
  let
    -- Check if viewport changed (need to regenerate regions)
    currentLevel = selectGridLevel (viewportLatentWidth vs) (viewportLatentHeight vs)
    regionsChanged = currentLevel /= allocationGridLevel state
    
    -- Regenerate regions if viewport changed
    regions = if regionsChanged 
              then viewportToRegions vs 
              else allocationRegions state
    
    -- Advance epoch
    newEpoch = nextEpoch (state.epoch)
    
    -- Compute quality headroom
    quality = qualityFromPerformance perf
    
    -- Adaptive allocation based on performance
    selections = map (adaptiveSelection quality) regions
    
    newState = 
      { epoch: newEpoch
      , regions
      , gridLevel: currentLevel
      }
  in
    { selections
    , nextState: newState
    }

-- | Adaptive selection: adjust diffusion steps based on quality headroom.
adaptiveSelection :: Number -> Region -> RegionSelection
adaptiveSelection quality region@(Region r) =
  let
    baseSteps = tierDefaultSteps r.tier
    adjustedSteps = adjustStepsForQuality quality r.tier baseSteps
  in
    RegionSelection { region, steps: adjustedSteps }

-- | Adjust diffusion steps based on quality headroom and tier.
-- |
-- | - Foveal: always gets full steps (highest priority)
-- | - Peripheral: reduced when quality < 0.5
-- | - Background: reduced when quality < 0.7
adjustStepsForQuality :: Number -> RenderTier -> DiffusionSteps -> DiffusionSteps
adjustStepsForQuality quality tier (DiffusionSteps steps) =
  let
    factor = case tier of
      Foveal -> 1.0  -- Never reduce foveal
      Peripheral -> if quality < 0.5 then 0.7 else 1.0
      Background -> if quality < 0.7 then 0.5 else if quality < 0.3 then 0.3 else 1.0
    
    adjusted = Int.floor (Int.toNumber steps * factor)
    clamped = max 1 (min 50 adjusted)
  in
    -- Use unsafe constructor since we've clamped to valid range
    DiffusionSteps clamped

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // faa-enhanced // allocation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert regions to a ground set for submodular optimization.
-- |
-- | Each region becomes an Element indexed by position in the array.
-- | Returns (groundSet, indexToRegion) for mapping back after optimization.
regionsToGroundSetFAA :: Array Region -> { groundSet :: GroundSet RegionIndex, indexToRegion :: Array Region }
regionsToGroundSetFAA regions =
  let n = Array.length regions
      elements = map Element (Array.range 0 (n - 1))
      groundSet = GroundSet { size: Dim n, elements }
  in { groundSet, indexToRegion: regions }

-- | Create a submodular oracle for region allocation.
-- |
-- | ## Utility Function
-- |
-- | The utility of selecting a set of regions S is:
-- |
-- |   f(S) = qualityWeight · Σ_{r ∈ S} tierQuality(r)
-- |        + coverageWeight · coverage(S)
-- |
-- | Where:
-- | - tierQuality(r) = 1.0 for Foveal, 0.6 for Peripheral, 0.3 for Background
-- | - coverage(S) = √|S| (concave, encouraging spread)
-- |
-- | ## Submodularity
-- |
-- | The function is submodular because:
-- | - Linear sum is modular (trivially submodular)
-- | - √|S| is concave in |S| (submodular)
-- | - Non-negative sum of submodular functions is submodular
regionUtilityOracle 
  :: FAAAllocationConfig 
  -> Array Region 
  -> GroundSet RegionIndex 
  -> SubmodularOracle RegionIndex
regionUtilityOracle config regions groundSet =
  SubmodularOracle
    { eval: evalUtility
    , marginal: marginalUtility
    , groundSet
    , fMax: Nothing  -- Unknown upper bound
    }
  where
    qualityWeight = faaQualityWeight config
    coverageWeight = faaCoverageWeight config
    
    -- | Evaluate utility of a region set.
    evalUtility :: ElementSet RegionIndex -> SetValue
    evalUtility selected =
      let selectedIndices = Set.toUnfoldable selected :: Array (Element RegionIndex)
          qualitySum = foldl (\acc (Element i) -> 
            acc + regionQuality (Array.index regions i)) 0.0 selectedIndices
          coverageVal = intToNumSafe (Set.size selected)
          -- Coverage utility: √|S| (concave, submodular)
          coverageUtility = Math.sqrt coverageVal
          totalUtility = qualityWeight * qualitySum 
                       + coverageWeight * coverageUtility
      in SetValue totalUtility
    
    -- | Marginal gain from adding a region.
    marginalUtility :: Element RegionIndex -> ElementSet RegionIndex -> MarginalGain
    marginalUtility e@(Element i) currentSet =
      if Set.member e currentSet
        then MarginalGain 0.0  -- Already included
        else
          let -- Quality gain (modular)
              qualityGain = regionQuality (Array.index regions i)
              -- Coverage gain: √(|S|+1) - √|S| (diminishing returns)
              currentSize = Set.size currentSet
              currentCoverage = Math.sqrt (intToNumSafe currentSize)
              newCoverage = Math.sqrt (intToNumSafe (currentSize + 1))
              coverageGain = newCoverage - currentCoverage
              totalGain = qualityWeight * qualityGain 
                        + coverageWeight * coverageGain
          in MarginalGain totalGain
    
    -- | Get quality value for a region based on tier.
    regionQuality :: Maybe Region -> Number
    regionQuality maybeRegion = case maybeRegion of
      Nothing -> 0.0  -- Invalid index
      Just (Region r) -> case r.tier of
        Foveal -> 1.0       -- Highest priority
        Peripheral -> 0.6   -- Medium priority
        Background -> 0.3   -- Lower priority

-- | Allocate frame using FAA-enhanced submodular optimization.
-- |
-- | ## Algorithm
-- |
-- | 1. Convert regions to ground set
-- | 2. Create utility oracle (quality + coverage)
-- | 3. Create cardinality matroid (k = maxRegions)
-- | 4. Run FAA-enhanced continuous greedy (√T iterations)
-- | 5. Round using min-energy selection (deterministic)
-- | 6. Convert selected elements back to RegionSelections
-- |
-- | ## Guarantees (Proven in proofs/Hydrogen/Optimize/Submodular/)
-- |
-- | - (1 - 1/e - O(1/√T)) approximation to optimal k-region selection
-- | - √T iterations instead of T (FAA speedup)
-- | - Deterministic rounding (min-energy)
allocateFrameFAA 
  :: ViewportState 
  -> PerformanceState 
  -> AllocationState 
  -> FAAAllocationConfig 
  -> AllocationResult
allocateFrameFAA vs perf state config =
  let 
    -- Check if viewport changed (need to regenerate regions)
    currentLevel = selectGridLevel (viewportLatentWidth vs) (viewportLatentHeight vs)
    regionsChanged = currentLevel /= allocationGridLevel state
    
    -- Regenerate regions if viewport changed
    regions = if regionsChanged 
              then viewportToRegions vs 
              else allocationRegions state
    
    -- Advance epoch
    newEpoch = nextEpoch (state.epoch)
    
    -- Convert regions to ground set
    { groundSet, indexToRegion } = regionsToGroundSetFAA regions
    
    -- Create utility oracle
    oracle = regionUtilityOracle config indexToRegion groundSet
    
    -- Create cardinality matroid: select at most k regions
    matroid = CardinalityMatroid 
      { k: Dim (min (faaMaxRegions config) (Array.length regions))
      , groundSet
      }
    
    -- Create FAA config
    faaConfig = mkFAAConfig (faaTargetIterations config)
    
    -- Run FAA-enhanced continuous greedy
    fractionalSolution = continuousGreedyFAA matroid oracle faaConfig
    
    -- Round using min-energy selection
    minEnergyConfig = mkMinEnergyConfig (faaRoundingCandidates config)
    selectedElements = minEnergyRound fractionalSolution minEnergyConfig
    
    -- Convert selected elements back to regions
    selectedIndices = Set.toUnfoldable selectedElements :: Array (Element RegionIndex)
    selectedRegions = Array.mapMaybe (\(Element i) -> Array.index indexToRegion i) selectedIndices
    
    -- Create selections with quality-adjusted steps
    quality = qualityFromPerformance perf
    selections = map (adaptiveSelectionFAA quality fractionalSolution) 
                     (Array.mapWithIndex Tuple selectedRegions)
    
    newState = 
      { epoch: newEpoch
      , regions
      , gridLevel: currentLevel
      }
  in
    { selections
    , nextState: newState
    }

-- | Adaptive selection for FAA: use fractional value to modulate steps.
-- |
-- | Regions with higher fractional values in the continuous solution
-- | get more diffusion steps, as they were "more selected" by the optimizer.
-- |
-- | ## Fractional Value Modulation
-- |
-- | The continuous greedy produces fractional values x_e ∈ [0, 1] for each
-- | element. After rounding, we use these values to modulate quality:
-- | - x_e close to 1.0: strong selection → more diffusion steps
-- | - x_e close to 0.5: marginal selection → baseline diffusion steps
-- | - x_e close to 0.0: weak selection (shouldn't happen after rounding)
-- |
-- | The fractional value acts as a "confidence" weight from the optimizer.
adaptiveSelectionFAA 
  :: Number 
  -> FractionalSolution RegionIndex 
  -> Tuple Int Region 
  -> RegionSelection
adaptiveSelectionFAA quality fractionalSol (Tuple idx region@(Region r)) =
  let baseSteps = tierDefaultSteps r.tier
      -- Get fractional value for this element (confidence from optimizer)
      fractionalValue = solutionCoord fractionalSol (Element idx)
      -- Modulate quality by fractional confidence
      -- Higher fractional value = more confident → boost quality
      -- fractionalValue in [0, 1], typically > 0.5 for selected elements
      confidenceBoost = 0.5 + fractionalValue * 0.5  -- Maps [0,1] → [0.5, 1.0]
      modulatedQuality = min 1.0 (quality * confidenceBoost)
      -- Apply standard quality adjustment with boosted quality
      adjustedSteps = adjustStepsForQuality modulatedQuality r.tier baseSteps
  in RegionSelection { region, steps: adjustedSteps }

-- | Safe Int to Number conversion without FFI.
intToNumSafe :: Int -> Number
intToNumSafe i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)
