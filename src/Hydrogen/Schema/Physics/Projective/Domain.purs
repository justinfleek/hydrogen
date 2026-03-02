-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // physics // projective // domain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Domain Decomposition — Parallel projective dynamics with graded effects.
-- |
-- | ## Research Foundation
-- |
-- | Based on SIGGRAPH 2025 paper "Domain-decomposed Projective Dynamics":
-- | - Divide simulation into independent domains
-- | - Solve domains in parallel (local step)
-- | - Reconcile at boundaries (global step / "epilogue")
-- |
-- | ## Connection to Landauer Precision
-- |
-- | Domain boundaries are "epilogues" — the last reversible point:
-- | - Interior DOFs: gauge freedom within domain (parallel, independent)
-- | - Boundary DOFs: shared between exactly 2 domains (pairwise reconciliation)
-- | - Corner DOFs: shared by 3+ domains (global reconciliation point)
-- |
-- | The Landauer insight: information is preserved during local solves
-- | (gauge transformations), and only at boundaries do we pay the
-- | thermodynamic cost of reconciliation.
-- |
-- | ## Graded Effects
-- |
-- | `DomainEffect` tracks what domain operations CAN DO:
-- | - ModifyPositions: Update particle positions
-- | - ModifyVelocities: Update particle velocities
-- | - ExchangeBoundary: Transfer boundary data between domains
-- | - Synchronize: Global barrier for all domains
-- |
-- | ## Co-Effects
-- |
-- | `DomainCoEffect` tracks what domain operations NEED:
-- | - NeedsNeighborDomain: Requires data from adjacent domain
-- | - NeedsGlobalState: Requires full system state
-- | - NeedsConstraints: Requires constraint data
-- | - NeedsMemory: Memory bound (bytes)
-- |
-- | ## Presburger Constraints
-- |
-- | Domain counts, DOF counts, boundary sizes are bounded integers.
-- | All constraints are decidable via Presburger arithmetic.
-- |
-- | ## ILP Optimization
-- |
-- | Load balance vs boundary overhead is an ILP problem:
-- | - Maximize load balance (min domain size / max domain size)
-- | - Minimize boundary ratio (boundary DOFs / total DOFs)
-- | - Subject to: domain count ≤ CPU cores, memory per domain ≤ cache
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe
-- | - Hydrogen.Schema.Attestation.UUID5
-- | - Hydrogen.Schema.Physics.Projective.Core

module Hydrogen.Schema.Physics.Projective.Domain
  ( -- * UUID5 Namespace
    nsDomain
    
  -- * Domain Effects (graded)
  , DomainEffect(..)
  , allDomainEffects
  , effectCombine
  , effectNone
  
  -- * Domain Co-Effects (needs)
  , DomainCoEffect(..)
  , allDomainCoEffects
  , coEffectCombine
  , coEffectNone
  
  -- * Domain Expression AST
  , DomainExpr(..)
  , exprEffect
  , exprCoEffect
  , exprUUID
  
  -- * Domain Operations
  , DomainOp(..)
  , allDomainOps
  , domainOpEffect
  , domainOpCoEffect
  
  -- * Bounded Types
  , DOFIndex
  , mkDOFIndex
  , dofIndexValue
  , DomainId
  , mkDomainId
  , domainIdValue
  , DOFCount
  , mkDOFCount
  , dofCountValue
  
  -- * Domain
  , Domain
  , mkDomain
  , domainId
  , domainInteriorDOFs
  , domainBoundaryDOFs
  , domainConstraintIndices
  
  -- * Domain Boundary
  , DomainBoundary
  , mkDomainBoundary
  , boundaryDomainA
  , boundaryDomainB
  , boundarySharedDOFs
  
  -- * Domain Decomposition
  , DomainDecomposition
  , mkDecomposition
  , decompositionDomains
  , decompositionBoundaries
  , decompositionCornerDOFs
  
  -- * Constraints (Presburger)
  , DomainConstraint(..)
  , domainCountBound
  , dofCountBound
  , boundaryRatioBound
  , constraintSatisfied
  
  -- * Optimization (ILP)
  , DomainObjective
  , LoadBalanceMetric(..)
  , OverheadMetric(..)
  , mkObjective
  , emptyObjective
  
  -- * Domain Lookup
  , findDomainById
  , findBoundaryBetween
  , isCornerDOF
  , domainsContainingDOF
  , dofDomainCount
  
  -- * Metrics
  , DomainMetrics
  , computeMetrics
  , metricsLoadBalance
  , metricsBoundaryRatio
  , metricsInteriorRatio
  -- * Effect Utilities
  , emptyEffect
  , emptyCoEffect
  , estimateDomainMemory
  , isDomainSmall
  , estimateDecompositionMemory
  , hasSmallDomains
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (==)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , max
  , min
  , map
  , mempty
  )

import Data.Array (length, foldl, filter) as Array
import Data.Maybe (Maybe(..))

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Physics.Projective.Core as Core

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for domain decomposition UUIDs.
nsDomain :: UUID5.UUID5
nsDomain = UUID5.uuid5 Core.nsProjective "domain"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // domain effects (graded)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What domain operations CAN DO.
-- |
-- | Graded monoid: effects combine via union.
-- | Grade algebra: E₁ ⊗ E₂ = union of capabilities.
data DomainEffect
  = EffectNone              -- ^ Pure computation, no side effects
  | EffectModifyPositions   -- ^ Can update particle positions
  | EffectModifyVelocities  -- ^ Can update particle velocities
  | EffectExchangeBoundary  -- ^ Can transfer boundary data
  | EffectSynchronize       -- ^ Global barrier across all domains
  | EffectComposite         -- ^ Combination of effects
      (Array DomainEffect)

derive instance eqDomainEffect :: Eq DomainEffect
derive instance ordDomainEffect :: Ord DomainEffect

instance showDomainEffect :: Show DomainEffect where
  show EffectNone = "none"
  show EffectModifyPositions = "modify-positions"
  show EffectModifyVelocities = "modify-velocities"
  show EffectExchangeBoundary = "exchange-boundary"
  show EffectSynchronize = "synchronize"
  show (EffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupDomainEffect :: Semigroup DomainEffect where
  append = effectCombine

instance monoidDomainEffect :: Monoid DomainEffect where
  mempty = EffectNone

-- | All primitive domain effects.
allDomainEffects :: Array DomainEffect
allDomainEffects =
  [ EffectNone
  , EffectModifyPositions
  , EffectModifyVelocities
  , EffectExchangeBoundary
  , EffectSynchronize
  ]

-- | Combine two effects (monoid operation).
effectCombine :: DomainEffect -> DomainEffect -> DomainEffect
effectCombine EffectNone e = e
effectCombine e EffectNone = e
effectCombine (EffectComposite a) (EffectComposite b) = EffectComposite (a <> b)
effectCombine (EffectComposite a) e = EffectComposite (a <> [e])
effectCombine e (EffectComposite b) = EffectComposite ([e] <> b)
effectCombine e1 e2 = if e1 == e2 then e1 else EffectComposite [e1, e2]

-- | No effects (identity).
effectNone :: DomainEffect
effectNone = EffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // domain co-effects (needs)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What domain operations NEED (resources/dependencies).
-- |
-- | Co-effect algebra: tracks what must be provided.
data DomainCoEffect
  = CoEffectNone              -- ^ No special requirements
  | CoEffectNeighborDomain    -- ^ Needs data from adjacent domain
  | CoEffectGlobalState       -- ^ Needs full system state
  | CoEffectConstraints       -- ^ Needs constraint data
  | CoEffectMemory Int        -- ^ Memory bound (bytes)
  | CoEffectCPUCores Int      -- ^ CPU cores needed
  | CoEffectComposite         -- ^ Multiple requirements
      (Array DomainCoEffect)

derive instance eqDomainCoEffect :: Eq DomainCoEffect
derive instance ordDomainCoEffect :: Ord DomainCoEffect

instance showDomainCoEffect :: Show DomainCoEffect where
  show CoEffectNone = "none"
  show CoEffectNeighborDomain = "neighbor-domain"
  show CoEffectGlobalState = "global-state"
  show CoEffectConstraints = "constraints"
  show (CoEffectMemory n) = "memory(" <> show n <> ")"
  show (CoEffectCPUCores n) = "cores(" <> show n <> ")"
  show (CoEffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupDomainCoEffect :: Semigroup DomainCoEffect where
  append = coEffectCombine

instance monoidDomainCoEffect :: Monoid DomainCoEffect where
  mempty = CoEffectNone

-- | All primitive co-effects.
allDomainCoEffects :: Array DomainCoEffect
allDomainCoEffects =
  [ CoEffectNone
  , CoEffectNeighborDomain
  , CoEffectGlobalState
  , CoEffectConstraints
  ]

-- | Combine co-effects.
coEffectCombine :: DomainCoEffect -> DomainCoEffect -> DomainCoEffect
coEffectCombine CoEffectNone e = e
coEffectCombine e CoEffectNone = e
coEffectCombine (CoEffectMemory a) (CoEffectMemory b) = CoEffectMemory (a + b)
coEffectCombine (CoEffectCPUCores a) (CoEffectCPUCores b) = CoEffectCPUCores (max a b)
coEffectCombine (CoEffectComposite a) (CoEffectComposite b) = CoEffectComposite (a <> b)
coEffectCombine (CoEffectComposite a) e = CoEffectComposite (a <> [e])
coEffectCombine e (CoEffectComposite b) = CoEffectComposite ([e] <> b)
coEffectCombine e1 e2 = if e1 == e2 then e1 else CoEffectComposite [e1, e2]

-- | No co-effects (identity).
coEffectNone :: DomainCoEffect
coEffectNone = CoEffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // domain operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Primitive operations on domains.
data DomainOp
  = OpSolveInterior        -- ^ Solve interior DOFs (local step)
  | OpSolveBoundary        -- ^ Solve boundary DOFs (requires neighbor)
  | OpSolveCorners         -- ^ Solve corner DOFs (global)
  | OpExchangeForces       -- ^ Exchange boundary forces
  | OpExchangePositions    -- ^ Exchange boundary positions
  | OpComputeResidual      -- ^ Compute solver residual
  | OpPartition            -- ^ Partition DOFs into domains
  | OpIdentifyBoundaries   -- ^ Find shared DOFs between domains
  | OpIdentifyCorners      -- ^ Find DOFs shared by 3+ domains

derive instance eqDomainOp :: Eq DomainOp
derive instance ordDomainOp :: Ord DomainOp

instance showDomainOp :: Show DomainOp where
  show OpSolveInterior = "solve-interior"
  show OpSolveBoundary = "solve-boundary"
  show OpSolveCorners = "solve-corners"
  show OpExchangeForces = "exchange-forces"
  show OpExchangePositions = "exchange-positions"
  show OpComputeResidual = "compute-residual"
  show OpPartition = "partition"
  show OpIdentifyBoundaries = "identify-boundaries"
  show OpIdentifyCorners = "identify-corners"

-- | All domain operations.
allDomainOps :: Array DomainOp
allDomainOps =
  [ OpSolveInterior
  , OpSolveBoundary
  , OpSolveCorners
  , OpExchangeForces
  , OpExchangePositions
  , OpComputeResidual
  , OpPartition
  , OpIdentifyBoundaries
  , OpIdentifyCorners
  ]

-- | Effect produced by domain operation.
domainOpEffect :: DomainOp -> DomainEffect
domainOpEffect OpSolveInterior = EffectModifyPositions
domainOpEffect OpSolveBoundary = effectCombine EffectModifyPositions EffectExchangeBoundary
domainOpEffect OpSolveCorners = effectCombine EffectModifyPositions EffectSynchronize
domainOpEffect OpExchangeForces = EffectExchangeBoundary
domainOpEffect OpExchangePositions = EffectExchangeBoundary
domainOpEffect OpComputeResidual = EffectNone
domainOpEffect OpPartition = EffectNone
domainOpEffect OpIdentifyBoundaries = EffectNone
domainOpEffect OpIdentifyCorners = EffectNone

-- | Co-effect required by domain operation.
domainOpCoEffect :: DomainOp -> DomainCoEffect
domainOpCoEffect OpSolveInterior = CoEffectConstraints
domainOpCoEffect OpSolveBoundary = coEffectCombine CoEffectConstraints CoEffectNeighborDomain
domainOpCoEffect OpSolveCorners = CoEffectGlobalState
domainOpCoEffect OpExchangeForces = CoEffectNeighborDomain
domainOpCoEffect OpExchangePositions = CoEffectNeighborDomain
domainOpCoEffect OpComputeResidual = CoEffectConstraints
domainOpCoEffect OpPartition = CoEffectGlobalState
domainOpCoEffect OpIdentifyBoundaries = CoEffectGlobalState
domainOpCoEffect OpIdentifyCorners = CoEffectGlobalState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // domain expression ast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Domain decomposition AST.
-- |
-- | Every expression carries its effect grade and co-effect requirements.
-- | This enables static analysis and optimization before execution.
data DomainExpr
  = -- | Pure value (no effects)
    DomainPure Int
    
  | -- | Domain operation
    DomainOp DomainOp
    
  | -- | Sequential composition (solve then exchange)
    DomainSeq DomainExpr DomainExpr
    
  | -- | Parallel composition (independent domains)
    DomainPar DomainExpr DomainExpr
    
  | -- | Loop (iterations of local-global)
    DomainLoop Int DomainExpr
    
  | -- | Annotate with effect
    DomainAnnotate DomainEffect DomainExpr

derive instance eqDomainExpr :: Eq DomainExpr
derive instance ordDomainExpr :: Ord DomainExpr

instance showDomainExpr :: Show DomainExpr where
  show (DomainPure n) = "pure(" <> show n <> ")"
  show (DomainOp op) = "op(" <> show op <> ")"
  show (DomainSeq e1 e2) = "seq(" <> show e1 <> ", " <> show e2 <> ")"
  show (DomainPar e1 e2) = "par(" <> show e1 <> ", " <> show e2 <> ")"
  show (DomainLoop n e) = "loop(" <> show n <> ", " <> show e <> ")"
  show (DomainAnnotate eff e) = "annotate(" <> show eff <> ", " <> show e <> ")"

-- | Compute effect grade of expression.
exprEffect :: DomainExpr -> DomainEffect
exprEffect (DomainPure _) = EffectNone
exprEffect (DomainOp op) = domainOpEffect op
exprEffect (DomainSeq e1 e2) = effectCombine (exprEffect e1) (exprEffect e2)
exprEffect (DomainPar e1 e2) = effectCombine (exprEffect e1) (exprEffect e2)
exprEffect (DomainLoop _ e) = exprEffect e
exprEffect (DomainAnnotate eff _) = eff

-- | Compute co-effect requirements of expression.
exprCoEffect :: DomainExpr -> DomainCoEffect
exprCoEffect (DomainPure _) = CoEffectNone
exprCoEffect (DomainOp op) = domainOpCoEffect op
exprCoEffect (DomainSeq e1 e2) = coEffectCombine (exprCoEffect e1) (exprCoEffect e2)
exprCoEffect (DomainPar e1 e2) = coEffectCombine (exprCoEffect e1) (exprCoEffect e2)
exprCoEffect (DomainLoop _ e) = exprCoEffect e
exprCoEffect (DomainAnnotate _ e) = exprCoEffect e

-- | Compute deterministic UUID for expression.
exprUUID :: DomainExpr -> UUID5.UUID5
exprUUID expr = UUID5.uuid5 nsDomain (show expr)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounded types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded DOF index. Range: [0, 2^20 - 1] (max ~1 million DOFs).
-- | Clamped to bounds on construction.
newtype DOFIndex = DOFIndex Int

derive instance eqDOFIndex :: Eq DOFIndex
derive instance ordDOFIndex :: Ord DOFIndex

instance showDOFIndex :: Show DOFIndex where
  show (DOFIndex i) = "DOF(" <> show i <> ")"

-- | Create a bounded DOF index. Clamps to [0, 1048575].
mkDOFIndex :: Int -> DOFIndex
mkDOFIndex i = DOFIndex (max 0 (min 1048575 i))

-- | Extract DOF index value.
dofIndexValue :: DOFIndex -> Int
dofIndexValue (DOFIndex i) = i

-- | Bounded domain ID. Range: [0, 1023] (max 1024 domains).
newtype DomainId = DomainId Int

derive instance eqDomainId :: Eq DomainId
derive instance ordDomainId :: Ord DomainId

instance showDomainId :: Show DomainId where
  show (DomainId i) = "Domain(" <> show i <> ")"

-- | Create a bounded domain ID. Clamps to [0, 1023].
mkDomainId :: Int -> DomainId
mkDomainId i = DomainId (max 0 (min 1023 i))

-- | Extract domain ID value.
domainIdValue :: DomainId -> Int
domainIdValue (DomainId i) = i

-- | Bounded DOF count. Range: [0, 2^24 - 1] (max ~16 million DOFs).
newtype DOFCount = DOFCount Int

derive instance eqDOFCount :: Eq DOFCount
derive instance ordDOFCount :: Ord DOFCount

instance showDOFCount :: Show DOFCount where
  show (DOFCount n) = "Count(" <> show n <> ")"

-- | Create a bounded DOF count. Clamps to [0, 16777215].
mkDOFCount :: Int -> DOFCount
mkDOFCount n = DOFCount (max 0 (min 16777215 n))

-- | Extract DOF count value.
dofCountValue :: DOFCount -> Int
dofCountValue (DOFCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // domain
-- ═════════════════════════════════════════════════════════════════════════════

-- | A domain in the decomposition.
-- |
-- | Contains interior DOFs (solved independently) and boundary DOFs
-- | (shared with neighboring domains).
type Domain =
  { id :: DomainId
  , interiorDOFs :: Array DOFIndex
  , boundaryDOFs :: Array DOFIndex
  , constraintIndices :: Array Int
  }

-- | Create a domain.
mkDomain :: DomainId -> Array DOFIndex -> Array DOFIndex -> Array Int -> Domain
mkDomain did interior boundary constrs =
  { id: did
  , interiorDOFs: interior
  , boundaryDOFs: boundary
  , constraintIndices: constrs
  }

-- | Get domain ID.
domainId :: Domain -> DomainId
domainId d = d.id

-- | Get interior DOFs.
domainInteriorDOFs :: Domain -> Array DOFIndex
domainInteriorDOFs d = d.interiorDOFs

-- | Get boundary DOFs.
domainBoundaryDOFs :: Domain -> Array DOFIndex
domainBoundaryDOFs d = d.boundaryDOFs

-- | Get constraint indices.
domainConstraintIndices :: Domain -> Array Int
domainConstraintIndices d = d.constraintIndices

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // domain boundary
-- ═════════════════════════════════════════════════════════════════════════════

-- | Boundary between two adjacent domains.
-- |
-- | The sharedDOFs are the "epilogue" in Landauer terms — where
-- | gauge transformations from each domain must be reconciled.
type DomainBoundary =
  { domainA :: DomainId
  , domainB :: DomainId
  , sharedDOFs :: Array DOFIndex
  }

-- | Create a domain boundary.
mkDomainBoundary :: DomainId -> DomainId -> Array DOFIndex -> DomainBoundary
mkDomainBoundary dA dB shared =
  { domainA: dA
  , domainB: dB
  , sharedDOFs: shared
  }

-- | Get first domain.
boundaryDomainA :: DomainBoundary -> DomainId
boundaryDomainA b = b.domainA

-- | Get second domain.
boundaryDomainB :: DomainBoundary -> DomainId
boundaryDomainB b = b.domainB

-- | Get shared DOFs.
boundarySharedDOFs :: DomainBoundary -> Array DOFIndex
boundarySharedDOFs b = b.sharedDOFs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // domain decomposition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete domain decomposition of a system.
-- |
-- | The cornerDOFs are where 3+ domains meet — these require
-- | global reconciliation and are solved first (Schur complement).
type DomainDecomposition =
  { domains :: Array Domain
  , boundaries :: Array DomainBoundary
  , cornerDOFs :: Array DOFIndex
  }

-- | Create a decomposition.
mkDecomposition :: Array Domain -> Array DomainBoundary -> Array DOFIndex -> DomainDecomposition
mkDecomposition doms bounds corners =
  { domains: doms
  , boundaries: bounds
  , cornerDOFs: corners
  }

-- | Get domains.
decompositionDomains :: DomainDecomposition -> Array Domain
decompositionDomains d = d.domains

-- | Get boundaries.
decompositionBoundaries :: DomainDecomposition -> Array DomainBoundary
decompositionBoundaries d = d.boundaries

-- | Get corner DOFs.
decompositionCornerDOFs :: DomainDecomposition -> Array DOFIndex
decompositionCornerDOFs d = d.cornerDOFs

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // constraints (presburger)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear constraints on domain decomposition.
-- |
-- | All constraints are decidable via Presburger arithmetic.
data DomainConstraint
  = -- | Domain count ≤ bound
    ConstraintDomainCount Int Int
    
  | -- | DOF count ≤ bound
    ConstraintDOFCount Int Int
    
  | -- | Boundary ratio ≤ bound (as percentage * 100)
    ConstraintBoundaryRatio Int Int
    
  | -- | Memory per domain ≤ bound
    ConstraintMemoryPerDomain Int Int
    
  | -- | Conjunction of constraints
    ConstraintAnd DomainConstraint DomainConstraint
    
  | -- | Always satisfied
    ConstraintTrue
    
  | -- | Never satisfied
    ConstraintFalse

derive instance eqDomainConstraint :: Eq DomainConstraint

instance showDomainConstraint :: Show DomainConstraint where
  show (ConstraintDomainCount c m) = "domains(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintDOFCount c m) = "dofs(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintBoundaryRatio c m) = "boundary%(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintMemoryPerDomain c m) = "mem/domain(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintAnd a b) = show a <> " ∧ " <> show b
  show ConstraintTrue = "⊤"
  show ConstraintFalse = "⊥"

-- | Create domain count constraint.
domainCountBound :: Int -> Int -> DomainConstraint
domainCountBound current maxCount = ConstraintDomainCount current maxCount

-- | Create DOF count constraint.
dofCountBound :: Int -> Int -> DomainConstraint
dofCountBound current maxDOFs = ConstraintDOFCount current maxDOFs

-- | Create boundary ratio constraint.
boundaryRatioBound :: Int -> Int -> DomainConstraint
boundaryRatioBound currentPercent maxPercent = ConstraintBoundaryRatio currentPercent maxPercent

-- | Check if constraint is satisfied.
constraintSatisfied :: DomainConstraint -> Boolean
constraintSatisfied (ConstraintDomainCount c m) = c <= m
constraintSatisfied (ConstraintDOFCount c m) = c <= m
constraintSatisfied (ConstraintBoundaryRatio c m) = c <= m
constraintSatisfied (ConstraintMemoryPerDomain c m) = c <= m
constraintSatisfied (ConstraintAnd a b) = constraintSatisfied a && constraintSatisfied b
constraintSatisfied ConstraintTrue = true
constraintSatisfied ConstraintFalse = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // optimization (ilp)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Load balance metrics (maximize).
data LoadBalanceMetric
  = MetricMinMaxRatio       -- ^ min domain size / max domain size
  | MetricVariance          -- ^ Variance in domain sizes (minimize)

derive instance eqLoadBalanceMetric :: Eq LoadBalanceMetric
derive instance ordLoadBalanceMetric :: Ord LoadBalanceMetric

instance showLoadBalanceMetric :: Show LoadBalanceMetric where
  show MetricMinMaxRatio = "min-max-ratio"
  show MetricVariance = "variance"

-- | Overhead metrics (minimize).
data OverheadMetric
  = MetricBoundaryRatio     -- ^ boundary DOFs / total DOFs
  | MetricCornerCount       -- ^ Number of corner DOFs
  | MetricCommunication     -- ^ Inter-domain communication volume

derive instance eqOverheadMetric :: Eq OverheadMetric
derive instance ordOverheadMetric :: Ord OverheadMetric

instance showOverheadMetric :: Show OverheadMetric where
  show MetricBoundaryRatio = "boundary-ratio"
  show MetricCornerCount = "corner-count"
  show MetricCommunication = "communication"

-- | Optimization objective for domain decomposition.
type DomainObjective =
  { maximize :: Array LoadBalanceMetric
  , minimize :: Array OverheadMetric
  , constraints :: Array DomainConstraint
  }

-- | Create an objective.
mkObjective :: Array LoadBalanceMetric -> Array OverheadMetric -> Array DomainConstraint -> DomainObjective
mkObjective maxMetrics minMetrics constrs =
  { maximize: maxMetrics
  , minimize: minMetrics
  , constraints: constrs
  }

-- | Empty objective.
emptyObjective :: DomainObjective
emptyObjective =
  { maximize: []
  , minimize: []
  , constraints: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // domain lookup
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find a domain by ID. Returns Nothing if not found.
findDomainById :: DomainId -> Array Domain -> Maybe Domain
findDomainById targetId domains =
  Array.foldl (\acc d ->
    case acc of
      Just found -> Just found
      Nothing -> if d.id == targetId then Just d else Nothing
  ) Nothing domains

-- | Find the boundary between two domains. Returns Nothing if not adjacent.
findBoundaryBetween :: DomainId -> DomainId -> Array DomainBoundary -> Maybe DomainBoundary
findBoundaryBetween domA domB boundaries =
  Array.foldl (\acc b ->
    case acc of
      Just found -> Just found
      Nothing ->
        if (b.domainA == domA && b.domainB == domB) ||
           (b.domainA == domB && b.domainB == domA)
        then Just b
        else Nothing
  ) Nothing boundaries

-- | Check if a DOF is a corner (shared by 3+ domains).
-- |
-- | Corner DOFs are the "deep epilogue" — where multiple gauge
-- | transformations must be reconciled simultaneously.
isCornerDOF :: DOFIndex -> Array DomainBoundary -> Boolean
isCornerDOF dof boundaries =
  let
    count = Array.foldl (\acc b ->
      if dofInArray dof b.sharedDOFs then acc + 1 else acc
    ) 0 boundaries
  in
    count >= 2

-- | Get all domains containing a DOF.
domainsContainingDOF :: DOFIndex -> Array Domain -> Array Domain
domainsContainingDOF dof domains =
  Array.filter (\d ->
    dofInArray dof d.interiorDOFs || dofInArray dof d.boundaryDOFs
  ) domains

-- | Count how many domains share a DOF.
-- | Interior: 1, Boundary: 2, Corner: 3+
dofDomainCount :: DOFIndex -> Array Domain -> Int
dofDomainCount dof domains =
  Array.length (domainsContainingDOF dof domains)

-- | Check if DOF is in array.
dofInArray :: DOFIndex -> Array DOFIndex -> Boolean
dofInArray x arr = Array.foldl (\acc v -> acc || v == x) false arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Computed metrics for a domain decomposition.
type DomainMetrics =
  { loadBalance :: Number      -- ^ min size / max size (1.0 = perfect)
  , boundaryRatio :: Number    -- ^ boundary DOFs / total DOFs
  , interiorRatio :: Number    -- ^ interior DOFs / total DOFs
  }

-- | Compute metrics for a decomposition.
computeMetrics :: DomainDecomposition -> DomainMetrics
computeMetrics decomp =
  let
    domains = decomp.domains
    
    -- Domain sizes
    sizes = map (\d -> 
      Array.length d.interiorDOFs + Array.length d.boundaryDOFs
    ) domains
    
    maxSize = Array.foldl max 1 sizes
    minSize = Array.foldl min maxSize sizes
    
    -- Total DOFs
    totalInterior = Array.foldl (\acc d -> acc + Array.length d.interiorDOFs) 0 domains
    totalBoundary = Array.foldl (\acc d -> acc + Array.length d.boundaryDOFs) 0 domains
    total = totalInterior + totalBoundary
    safeTotal = max 1 total
  in
    { loadBalance: intToNumber minSize / intToNumber maxSize
    , boundaryRatio: intToNumber totalBoundary / intToNumber safeTotal
    , interiorRatio: intToNumber totalInterior / intToNumber safeTotal
    }

-- | Get load balance metric.
metricsLoadBalance :: DomainMetrics -> Number
metricsLoadBalance m = m.loadBalance

-- | Get boundary ratio metric.
metricsBoundaryRatio :: DomainMetrics -> Number
metricsBoundaryRatio m = m.boundaryRatio

-- | Get interior ratio metric.
metricsInteriorRatio :: DomainMetrics -> Number
metricsInteriorRatio m = m.interiorRatio

-- | Convert Int to Number.
intToNumber :: Int -> Number
intToNumber n = intToNumberRec n 0.0
  where
    intToNumberRec :: Int -> Number -> Number
    intToNumberRec 0 acc = acc
    intToNumberRec i acc =
      if i > 0
        then intToNumberRec (i - 1) (acc + 1.0)
        else intToNumberRec (i + 1) (acc - 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // effect utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty effect (monoid identity via mempty).
emptyEffect :: DomainEffect
emptyEffect = mempty

-- | Empty co-effect (monoid identity via mempty).
emptyCoEffect :: DomainCoEffect
emptyCoEffect = mempty

-- | Estimate memory cost of domain in bytes.
-- | Each DOF is 24 bytes (3 * 8 for position xyz).
estimateDomainMemory :: Domain -> Int
estimateDomainMemory d =
  let
    dofCount = Array.length d.interiorDOFs + Array.length d.boundaryDOFs
    bytesPerDOF = 24
  in
    dofCount * bytesPerDOF

-- | Check if domain is smaller than a threshold.
isDomainSmall :: Domain -> Int -> Boolean
isDomainSmall d threshold =
  let size = Array.length d.interiorDOFs + Array.length d.boundaryDOFs
  in size < threshold

-- | Estimate total memory for decomposition.
estimateDecompositionMemory :: DomainDecomposition -> Int
estimateDecompositionMemory decomp =
  Array.foldl (\acc d -> acc + estimateDomainMemory d) 0 decomp.domains

-- | Check if any domain is below minimum size threshold.
hasSmallDomains :: DomainDecomposition -> Int -> Boolean
hasSmallDomains decomp minSize =
  Array.foldl (\acc d -> acc || isDomainSmall d minSize) false decomp.domains
