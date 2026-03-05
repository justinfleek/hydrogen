-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // core // constraint
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Constraints — Presburger arithmetic for Element resource bounds.
-- |
-- | ## Research Foundation
-- |
-- | All Element constraints are linear inequalities over bounded integers:
-- |   c₁x₁ + c₂x₂ + ... + cₙxₙ ≤ b
-- |
-- | This makes constraint satisfaction decidable via Presburger arithmetic.
-- | The Lean proofs in `proofs/Hydrogen/Layout/Presburger.lean` provide
-- | formal verification of constraint solving correctness.
-- |
-- | ## Constraint Categories
-- |
-- | 1. **Resource Bounds**: Font count ≤ limit, image count ≤ limit
-- | 2. **Memory Budget**: Total bytes ≤ available memory
-- | 3. **Effect Compatibility**: Pure elements cannot contain interactive children
-- | 4. **Co-Effect Satisfaction**: Environment must provide all required resources
-- |
-- | ## ILP Connection
-- |
-- | Element tree optimization is an ILP problem:
-- | - Minimize: Resource loading time, memory usage
-- | - Maximize: Preload coverage
-- | - Subject to: Resource constraints, effect compatibility
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show, Ord)
-- | - Hydrogen.Element.Core.Effect (ElementCoEffect)

module Hydrogen.Element.Core.Constraint
  ( -- * Resource Bounds
    ResourceBound
  , fontBound
  , iconBound
  , imageBound
  , dataBound
  , audioBound
  , videoBound
  , model3DBound
  , memoryBound
  
  -- * Element Constraints
  , ElementConstraint
      ( ConstraintResourceBound
      , ConstraintMemoryBudget
      , ConstraintEffectPurity
      , ConstraintCoEffectProvided
      , ConstraintAnd
      , ConstraintOr
      , ConstraintTrue
      , ConstraintFalse
      )
  , constraintSatisfied
  , constraintSimplify
  
  -- * Constraint Builders
  , resourceBoundConstraint
  , memoryBudgetConstraint
  , effectPurityConstraint
  , coEffectProvidedConstraint
  , conjConstraints
  , disjConstraints
  
  -- * Resource Environment
  , ResourceEnvironment
  , emptyEnvironment
  , environmentWithFonts
  , environmentWithImages
  , environmentWithMemory
  , environmentSatisfies
  
  -- * Optimization Objective
  , OptimizationMetric
      ( MetricLoadTime
      , MetricMemoryUsage
      , MetricPreloadCount
      , MetricCacheHits
      )
  , ElementObjective
  , minimizeLoadTime
  , minimizeMemory
  , maximizePreload
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , (<>)
  , (+)
  , not
  )

import Data.Array (foldl, all) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Core.Effect
  ( ElementCoEffect
      ( CoEffectNone
      , CoEffectNeedsFont
      , CoEffectNeedsIcon
      , CoEffectNeedsImage
      , CoEffectNeedsData
      , CoEffectNeedsAudio
      , CoEffectNeedsVideo
      , CoEffectNeeds3DModel
      , CoEffectComposite
      )
  , ElementEffect
      ( EffectPure
      , EffectComposite
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // resource bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resource bound: current usage ≤ maximum allowed.
-- |
-- | All bounds are bounded integers, making this decidable via Presburger.
-- |
-- | ## Practical Limits
-- |
-- | - Fonts: 0..256 (browser practical limit)
-- | - Icons: 0..1024 (icon sprite limit)
-- | - Images: 0..512 (memory practical limit)
-- | - Data queries: 0..64 (concurrent request limit)
-- | - Audio/Video: 0..32 (browser media element limit)
-- | - 3D Models: 0..16 (GPU memory limit)
-- | - Memory: 0..2GB (32-bit address space limit)
type ResourceBound =
  { resourceType :: String  -- ^ Resource category name
  , current :: Int          -- ^ Current usage count/bytes
  , maximum :: Int          -- ^ Maximum allowed count/bytes
  }

-- | Font resource bound.
fontBound :: Int -> Int -> ResourceBound
fontBound current maximum = { resourceType: "font", current: current, maximum: maximum }

-- | Icon resource bound.
iconBound :: Int -> Int -> ResourceBound
iconBound current maximum = { resourceType: "icon", current: current, maximum: maximum }

-- | Image resource bound.
imageBound :: Int -> Int -> ResourceBound
imageBound current maximum = { resourceType: "image", current: current, maximum: maximum }

-- | Data query resource bound.
dataBound :: Int -> Int -> ResourceBound
dataBound current maximum = { resourceType: "data", current: current, maximum: maximum }

-- | Audio resource bound.
audioBound :: Int -> Int -> ResourceBound
audioBound current maximum = { resourceType: "audio", current: current, maximum: maximum }

-- | Video resource bound.
videoBound :: Int -> Int -> ResourceBound
videoBound current maximum = { resourceType: "video", current: current, maximum: maximum }

-- | 3D model resource bound.
model3DBound :: Int -> Int -> ResourceBound
model3DBound current maximum = { resourceType: "model3d", current: current, maximum: maximum }

-- | Memory resource bound (bytes).
memoryBound :: Int -> Int -> ResourceBound
memoryBound current maximum = { resourceType: "memory", current: current, maximum: maximum }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // element constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints on Element resource usage and effect compatibility.
-- |
-- | All constraints are decidable via Presburger arithmetic because:
-- | 1. Resource counts are bounded integers
-- | 2. Effect compatibility is finite enumeration
-- | 3. Boolean combination preserves decidability
-- |
-- | ## Constraint Categories
-- |
-- | - **ResourceBound**: current ≤ maximum for each resource type
-- | - **MemoryBudget**: total_bytes ≤ budget
-- | - **EffectPurity**: if parent is Pure, children must be Pure
-- | - **CoEffectProvided**: environment must provide all required resources
data ElementConstraint
  = -- | Resource usage ≤ maximum
    ConstraintResourceBound ResourceBound
    
  | -- | Total memory ≤ budget (bytes)
    ConstraintMemoryBudget Int Int         -- current ≤ budget
    
  | -- | Effect purity propagation
    -- | If true, element and all children must have EffectPure
    ConstraintEffectPurity Boolean         -- is_pure_required
    
  | -- | Co-effect satisfaction
    -- | Environment must provide the required co-effect
    ConstraintCoEffectProvided ElementCoEffect
    
  | -- | Conjunction: both must be satisfied
    ConstraintAnd ElementConstraint ElementConstraint
    
  | -- | Disjunction: at least one must be satisfied
    ConstraintOr ElementConstraint ElementConstraint
    
  | -- | Always satisfied (identity for conjunction)
    ConstraintTrue
    
  | -- | Never satisfied (identity for disjunction)
    ConstraintFalse

derive instance eqElementConstraint :: Eq ElementConstraint
derive instance ordElementConstraint :: Ord ElementConstraint

instance showElementConstraint :: Show ElementConstraint where
  show (ConstraintResourceBound rb) = 
    rb.resourceType <> "(" <> show rb.current <> " ≤ " <> show rb.maximum <> ")"
  show (ConstraintMemoryBudget current budget) = 
    "memory(" <> show current <> " ≤ " <> show budget <> " bytes)"
  show (ConstraintEffectPurity required) = 
    "purity(" <> (if required then "required" else "optional") <> ")"
  show (ConstraintCoEffectProvided coeff) = 
    "provides(" <> show coeff <> ")"
  show (ConstraintAnd a b) = 
    "(" <> show a <> " ∧ " <> show b <> ")"
  show (ConstraintOr a b) = 
    "(" <> show a <> " ∨ " <> show b <> ")"
  show ConstraintTrue = "⊤"
  show ConstraintFalse = "⊥"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // constraint builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create resource bound constraint.
resourceBoundConstraint :: ResourceBound -> ElementConstraint
resourceBoundConstraint = ConstraintResourceBound

-- | Create memory budget constraint.
memoryBudgetConstraint :: Int -> Int -> ElementConstraint
memoryBudgetConstraint current budget = ConstraintMemoryBudget current budget

-- | Create effect purity constraint.
effectPurityConstraint :: Boolean -> ElementConstraint
effectPurityConstraint = ConstraintEffectPurity

-- | Create co-effect provided constraint.
coEffectProvidedConstraint :: ElementCoEffect -> ElementConstraint
coEffectProvidedConstraint = ConstraintCoEffectProvided

-- | Conjunction of multiple constraints.
conjConstraints :: Array ElementConstraint -> ElementConstraint
conjConstraints constraints = 
  Array.foldl ConstraintAnd ConstraintTrue constraints

-- | Disjunction of multiple constraints.
disjConstraints :: Array ElementConstraint -> ElementConstraint
disjConstraints constraints = 
  Array.foldl ConstraintOr ConstraintFalse constraints

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // resource environment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Environment that provides resources for co-effect satisfaction.
-- |
-- | This represents what the runtime has available to provide:
-- | - Loaded fonts
-- | - Loaded images
-- | - Available memory
-- | - Cached data
type ResourceEnvironment =
  { fontsAvailable :: Int       -- ^ Number of fonts loaded
  , iconsAvailable :: Int       -- ^ Number of icons available
  , imagesAvailable :: Int      -- ^ Number of images loaded
  , dataQueriesCached :: Int    -- ^ Number of data queries cached
  , audioSourcesReady :: Int    -- ^ Number of audio sources ready
  , videoSourcesReady :: Int    -- ^ Number of video sources ready
  , models3DReady :: Int        -- ^ Number of 3D models loaded
  , memoryAvailable :: Int      -- ^ Available memory (bytes)
  }

-- | Empty environment (nothing loaded).
emptyEnvironment :: ResourceEnvironment
emptyEnvironment =
  { fontsAvailable: 0
  , iconsAvailable: 0
  , imagesAvailable: 0
  , dataQueriesCached: 0
  , audioSourcesReady: 0
  , videoSourcesReady: 0
  , models3DReady: 0
  , memoryAvailable: 0
  }

-- | Environment with fonts loaded.
environmentWithFonts :: Int -> ResourceEnvironment -> ResourceEnvironment
environmentWithFonts n env = env { fontsAvailable = n }

-- | Environment with images loaded.
environmentWithImages :: Int -> ResourceEnvironment -> ResourceEnvironment
environmentWithImages n env = env { imagesAvailable = n }

-- | Environment with memory available.
environmentWithMemory :: Int -> ResourceEnvironment -> ResourceEnvironment
environmentWithMemory n env = env { memoryAvailable = n }

-- | Check if environment satisfies a co-effect requirement.
environmentSatisfies :: ResourceEnvironment -> ElementCoEffect -> Boolean
environmentSatisfies _ CoEffectNone = true
environmentSatisfies env (CoEffectNeedsFont n) = env.fontsAvailable >= n
environmentSatisfies env (CoEffectNeedsIcon n) = env.iconsAvailable >= n
environmentSatisfies env (CoEffectNeedsImage n) = env.imagesAvailable >= n
environmentSatisfies env (CoEffectNeedsData n) = env.dataQueriesCached >= n
environmentSatisfies env (CoEffectNeedsAudio n) = env.audioSourcesReady >= n
environmentSatisfies env (CoEffectNeedsVideo n) = env.videoSourcesReady >= n
environmentSatisfies env (CoEffectNeeds3DModel n) = env.models3DReady >= n
environmentSatisfies env (CoEffectComposite coeffs) = 
  Array.all (environmentSatisfies env) coeffs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // constraint satisfaction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a constraint is satisfied given an environment and effect.
-- |
-- | This is the decision procedure for Element constraints.
-- | Decidable because all predicates are bounded integer comparisons.
constraintSatisfied :: ResourceEnvironment -> ElementEffect -> ElementConstraint -> Boolean
constraintSatisfied _ _ ConstraintTrue = true
constraintSatisfied _ _ ConstraintFalse = false
constraintSatisfied env eff (ConstraintAnd a b) = 
  constraintSatisfied env eff a && constraintSatisfied env eff b
constraintSatisfied env eff (ConstraintOr a b) = 
  constraintSatisfied env eff a || constraintSatisfied env eff b
constraintSatisfied _ _ (ConstraintResourceBound rb) = 
  rb.current <= rb.maximum
constraintSatisfied _ _ (ConstraintMemoryBudget current budget) = 
  current <= budget
constraintSatisfied _ eff (ConstraintEffectPurity required) = 
  if required then isPureEffect eff else true
constraintSatisfied env _ (ConstraintCoEffectProvided coeff) = 
  environmentSatisfies env coeff

-- | Check if effect is pure.
isPureEffect :: ElementEffect -> Boolean
isPureEffect EffectPure = true
isPureEffect (EffectComposite effs) = Array.all isPureEffectSingle effs
isPureEffect _ = false

-- | Check if a single effect is pure.
isPureEffectSingle :: ElementEffect -> Boolean
isPureEffectSingle EffectPure = true
isPureEffectSingle _ = false

-- | Simplify a constraint (constant folding).
-- |
-- | Applies Boolean algebra rules:
-- | - ⊤ ∧ x = x
-- | - ⊥ ∧ x = ⊥
-- | - ⊤ ∨ x = ⊤
-- | - ⊥ ∨ x = x
constraintSimplify :: ElementConstraint -> ElementConstraint
constraintSimplify ConstraintTrue = ConstraintTrue
constraintSimplify ConstraintFalse = ConstraintFalse
constraintSimplify (ConstraintAnd a b) = 
  case constraintSimplify a of
    ConstraintTrue -> constraintSimplify b
    ConstraintFalse -> ConstraintFalse
    a' -> case constraintSimplify b of
      ConstraintTrue -> a'
      ConstraintFalse -> ConstraintFalse
      b' -> ConstraintAnd a' b'
constraintSimplify (ConstraintOr a b) = 
  case constraintSimplify a of
    ConstraintTrue -> ConstraintTrue
    ConstraintFalse -> constraintSimplify b
    a' -> case constraintSimplify b of
      ConstraintTrue -> ConstraintTrue
      ConstraintFalse -> a'
      b' -> ConstraintOr a' b'
constraintSimplify c = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // optimization objective
-- ═════════════════════════════════════════════════════════════════════════════

-- | Optimization metric for Element resource loading.
data OptimizationMetric
  = MetricLoadTime      -- ^ Total resource load time (minimize)
  | MetricMemoryUsage   -- ^ Peak memory usage (minimize)
  | MetricPreloadCount  -- ^ Resources preloaded (maximize)
  | MetricCacheHits     -- ^ Cache hit ratio (maximize)

derive instance eqOptimizationMetric :: Eq OptimizationMetric
derive instance ordOptimizationMetric :: Ord OptimizationMetric

instance showOptimizationMetric :: Show OptimizationMetric where
  show MetricLoadTime = "load-time"
  show MetricMemoryUsage = "memory-usage"
  show MetricPreloadCount = "preload-count"
  show MetricCacheHits = "cache-hits"

-- | Optimization objective for Element resource management.
-- |
-- | This becomes an ILP problem when combined with constraints.
type ElementObjective =
  { minimize :: Array OptimizationMetric
  , maximize :: Array OptimizationMetric
  , constraints :: Array ElementConstraint
  }

-- | Objective: minimize resource load time.
minimizeLoadTime :: Array ElementConstraint -> ElementObjective
minimizeLoadTime constraints =
  { minimize: [MetricLoadTime]
  , maximize: []
  , constraints: constraints
  }

-- | Objective: minimize memory usage.
minimizeMemory :: Array ElementConstraint -> ElementObjective
minimizeMemory constraints =
  { minimize: [MetricMemoryUsage]
  , maximize: []
  , constraints: constraints
  }

-- | Objective: maximize preloaded resources.
maximizePreload :: Array ElementConstraint -> ElementObjective
maximizePreload constraints =
  { minimize: []
  , maximize: [MetricPreloadCount]
  , constraints: constraints
  }
