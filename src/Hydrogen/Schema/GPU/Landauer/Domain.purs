-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // gpu // landauer // domain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Domain boundaries and gauge transformations for Landauer precision.
-- |
-- | A domain is a connected region with consistent gauge choices (precision
-- | and layout). Within a domain, no precision conversions occur.
-- |
-- | Boundaries between domains are where gauge transformations happen.
-- | Bijective transformations have zero Landauer cost and can be fused
-- | into kernel epilogues.

module Hydrogen.Schema.GPU.Landauer.Domain
  ( -- * Domain Boundaries
    Domain
  , domain
  , domainEntropy
  , domainPrecision
  , Boundary
  , boundary
  , boundaryIsFree
  , boundaryCost
  
  -- * Gauge Transformations
  , GaugeTransform
  , bijectiveRemap
  , isInjective
  , gaugeTransformCost
  ) where

import Prelude
  ( ($)
  )

import Hydrogen.Schema.GPU.Landauer.Types
  ( Entropy
  , LandauerCost
  , NaturalPrecision
  , landauerCost
  , freeBoundary
  , isFree
  , precisionBits
  )

import Hydrogen.Schema.GPU.Landauer.Format
  ( PrecisionFormat
  , formatBits
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // domain boundaries
-- ═════════════════════════════════════════════════════════════════════════════

-- | A domain is a connected region with consistent gauge choices.
-- |
-- | Within a domain, no precision/layout conversions occur.
type Domain =
  { id :: Int
  , entropy :: Entropy
  , precision :: PrecisionFormat
  }

-- | Create a domain
domain :: Int -> Entropy -> PrecisionFormat -> Domain
domain domainId ent prec =
  { id: domainId
  , entropy: ent
  , precision: prec
  }

-- | Get domain entropy
domainEntropy :: Domain -> Entropy
domainEntropy d = d.entropy

-- | Get domain precision
domainPrecision :: Domain -> PrecisionFormat
domainPrecision d = d.precision

-- | A boundary between two domains.
-- |
-- | Boundaries are where gauge transformations occur.
type Boundary =
  { source :: Domain
  , target :: Domain
  , cost :: LandauerCost
  }

-- | Create a boundary between domains
boundary :: Domain -> Domain -> Boundary
boundary src tgt =
  let
    srcEntropy = domainEntropy src
    tgtBits = precisionBits (formatBits (domainPrecision tgt))
    c = landauerCost srcEntropy tgtBits
  in
    { source: src
    , target: tgt
    , cost: c
    }

-- | Check if boundary is free (can be fused)
boundaryIsFree :: Boundary -> Boolean
boundaryIsFree b = isFree b.cost

-- | Get boundary cost
boundaryCost :: Boundary -> LandauerCost
boundaryCost b = b.cost

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gauge transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | A gauge transformation (precision/layout change).
-- |
-- | Gauge transformations that are bijective (injective on realized support)
-- | have zero Landauer cost and can be fused into epilogues.
type GaugeTransform =
  { sourcePrecision :: PrecisionFormat
  , targetPrecision :: PrecisionFormat
  , injective :: Boolean
  }

-- | Create a bijective remap (zero cost gauge transformation)
bijectiveRemap :: PrecisionFormat -> PrecisionFormat -> GaugeTransform
bijectiveRemap src tgt =
  { sourcePrecision: src
  , targetPrecision: tgt
  , injective: true  -- Caller asserts bijectivity
  }

-- | Check if transformation is injective
isInjective :: GaugeTransform -> Boolean
isInjective gt = gt.injective

-- | Get cost of gauge transformation.
-- |
-- | Injective transformations are free. Non-injective ones incur
-- | cost based on bits erased.
gaugeTransformCost :: GaugeTransform -> Entropy -> LandauerCost
gaugeTransformCost gt sourceEntropy =
  if gt.injective
    then freeBoundary
    else landauerCost sourceEntropy (precisionBits (formatBits gt.targetPrecision))
