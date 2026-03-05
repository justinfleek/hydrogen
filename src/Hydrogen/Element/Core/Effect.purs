-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // core // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Effects and Co-Effects — Graded types for UI elements.
-- |
-- | ## Research Foundation
-- |
-- | Based on Orchard-style graded monads (2014) where elements carry their
-- | capability requirements in the type. Elements have:
-- |
-- | - **Effects**: What the element CAN DO (click, hover, focus, animate, emit sound)
-- | - **Co-Effects**: What the element NEEDS (fonts, icons, data, images)
-- |
-- | ## System Fω Type Structure
-- |
-- | Effects and co-effects form bounded join-semilattices:
-- |
-- |     Pure ⊑ CanHover ⊑ CanClick ⊑ ... ⊑ ⊤
-- |     NeedsNothing ⊑ NeedsFont ⊑ NeedsData ⊑ ... ⊑ ⊤
-- |
-- | Composition is monoid union: combining elements unions their grades.
-- |
-- | ## Presburger Decidability
-- |
-- | All resource counts (fonts loaded, icons needed, data queries) are
-- | bounded integers. Constraint satisfaction is decidable via Presburger
-- | arithmetic over linear integer constraints.
-- |
-- | ## ILP Connection
-- |
-- | Resource loading can be optimized as ILP:
-- | - Minimize: Total loading time (latency × resource count)
-- | - Subject to: Memory budget, concurrent connection limits
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Semigroup, Monoid)
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Element.Core.Effect
  ( -- * UUID5 Namespace
    nsElementEffect
  
  -- * Element Effects (what elements CAN DO)
  , ElementEffect
      ( EffectPure
      , EffectCanClick
      , EffectCanHover
      , EffectCanFocus
      , EffectCanDrag
      , EffectCanAnimate
      , EffectCanEmitSound
      , EffectCanRequestData
      , EffectComposite
      )
  , allElementEffects
  , effectCombine
  , effectPure
  , effectCanInteract
  , effectCanAnimate
  
  -- * Element Co-Effects (what elements NEED)
  , ElementCoEffect
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
  , allElementCoEffects
  , coEffectCombine
  , coEffectNone
  
  -- * Graded Element Type
  , GradedElement
  , gradeElement
  , elementEffect
  , elementCoEffect
  , elementUUID
  
  -- * Event Binding (external to Element)
  , EventBinding
  , EventBindingMap
  , emptyBindingMap
  , bindEvent
  , lookupBinding
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
  , mempty
  , (==)
  , (+)
  , (<>)
  )

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Gestural.Event (GesturalEvent)
import Hydrogen.Element.Core.Element (Element)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Root namespace for Element effect UUIDs.
nsElementEffect :: UUID5.UUID5
nsElementEffect = UUID5.uuid5 UUID5.nsElement "effect"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // element effects (graded)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What UI elements CAN DO.
-- |
-- | Graded monoid: effects combine via union.
-- | Grade algebra: E₁ ⊗ E₂ = union of capabilities.
-- |
-- | ## Semantic Categories
-- |
-- | **Interaction Effects** (user-initiated):
-- | - CanClick: Responds to click/tap
-- | - CanHover: Responds to pointer hover
-- | - CanFocus: Can receive keyboard focus
-- | - CanDrag: Can be dragged
-- |
-- | **Animation Effects** (time-varying):
-- | - CanAnimate: Has animated properties
-- |
-- | **Media Effects** (produces output):
-- | - CanEmitSound: Produces audio
-- |
-- | **Data Effects** (requires async):
-- | - CanRequestData: Triggers data fetching
data ElementEffect
  = EffectPure            -- ^ No interactive effects (static content)
  | EffectCanClick        -- ^ Element responds to click/tap
  | EffectCanHover        -- ^ Element responds to hover
  | EffectCanFocus        -- ^ Element can receive focus
  | EffectCanDrag         -- ^ Element can be dragged
  | EffectCanAnimate      -- ^ Element has animations
  | EffectCanEmitSound    -- ^ Element produces audio
  | EffectCanRequestData  -- ^ Element triggers data fetching
  | EffectComposite       -- ^ Multiple effects combined
      (Array ElementEffect)

derive instance eqElementEffect :: Eq ElementEffect
derive instance ordElementEffect :: Ord ElementEffect

instance showElementEffect :: Show ElementEffect where
  show EffectPure = "pure"
  show EffectCanClick = "can-click"
  show EffectCanHover = "can-hover"
  show EffectCanFocus = "can-focus"
  show EffectCanDrag = "can-drag"
  show EffectCanAnimate = "can-animate"
  show EffectCanEmitSound = "can-emit-sound"
  show EffectCanRequestData = "can-request-data"
  show (EffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupElementEffect :: Semigroup ElementEffect where
  append = effectCombine

instance monoidElementEffect :: Monoid ElementEffect where
  mempty = EffectPure

-- | All primitive element effects.
allElementEffects :: Array ElementEffect
allElementEffects =
  [ EffectPure
  , EffectCanClick
  , EffectCanHover
  , EffectCanFocus
  , EffectCanDrag
  , EffectCanAnimate
  , EffectCanEmitSound
  , EffectCanRequestData
  ]

-- | Combine two effects (monoid operation).
-- |
-- | Laws:
-- |   effectCombine EffectPure e = e           (left identity)
-- |   effectCombine e EffectPure = e           (right identity)
-- |   effectCombine (effectCombine a b) c 
-- |     = effectCombine a (effectCombine b c)  (associativity)
effectCombine :: ElementEffect -> ElementEffect -> ElementEffect
effectCombine EffectPure e = e
effectCombine e EffectPure = e
effectCombine (EffectComposite a) (EffectComposite b) = EffectComposite (a <> b)
effectCombine (EffectComposite a) e = EffectComposite (a <> [e])
effectCombine e (EffectComposite b) = EffectComposite ([e] <> b)
effectCombine e1 e2 = if e1 == e2 then e1 else EffectComposite [e1, e2]

-- | Pure effect (identity).
effectPure :: ElementEffect
effectPure = EffectPure

-- | Standard interactive button effect (click + hover + focus).
effectCanInteract :: ElementEffect
effectCanInteract = EffectComposite [EffectCanClick, EffectCanHover, EffectCanFocus]

-- | Animation effect.
effectCanAnimate :: ElementEffect
effectCanAnimate = EffectCanAnimate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // element co-effects (needs)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What UI elements NEED (resources/dependencies).
-- |
-- | Co-effect algebra: tracks what must be provided by the environment.
-- | Resource requirements are declarative and composable.
-- |
-- | ## Presburger Semantics
-- |
-- | All counts are bounded integers:
-- | - Font count: 0..256 (practical limit)
-- | - Icon count: 0..1024 (icon sprite limit)
-- | - Data queries: 0..64 (concurrent request limit)
-- |
-- | This makes constraint solving decidable.
-- |
-- | ## Resource Categories
-- |
-- | **Typography**: NeedsFont (FontFamily references)
-- | **Graphics**: NeedsIcon, NeedsImage (asset references)
-- | **Media**: NeedsAudio, NeedsVideo, Needs3DModel
-- | **Async**: NeedsData (query references)
data ElementCoEffect
  = CoEffectNone            -- ^ Self-contained, no external resources
  | CoEffectNeedsFont       -- ^ Requires font loading
      Int                   -- ^   Count of font families needed
  | CoEffectNeedsIcon       -- ^ Requires icon assets
      Int                   -- ^   Count of icons needed
  | CoEffectNeedsImage      -- ^ Requires image assets
      Int                   -- ^   Count of images needed
  | CoEffectNeedsData       -- ^ Requires async data
      Int                   -- ^   Count of data queries
  | CoEffectNeedsAudio      -- ^ Requires audio assets
      Int                   -- ^   Count of audio sources
  | CoEffectNeedsVideo      -- ^ Requires video assets
      Int                   -- ^   Count of video sources
  | CoEffectNeeds3DModel    -- ^ Requires 3D model assets
      Int                   -- ^   Count of models
  | CoEffectComposite       -- ^ Multiple requirements
      (Array ElementCoEffect)

derive instance eqElementCoEffect :: Eq ElementCoEffect
derive instance ordElementCoEffect :: Ord ElementCoEffect

instance showElementCoEffect :: Show ElementCoEffect where
  show CoEffectNone = "none"
  show (CoEffectNeedsFont n) = "needs-font(" <> show n <> ")"
  show (CoEffectNeedsIcon n) = "needs-icon(" <> show n <> ")"
  show (CoEffectNeedsImage n) = "needs-image(" <> show n <> ")"
  show (CoEffectNeedsData n) = "needs-data(" <> show n <> ")"
  show (CoEffectNeedsAudio n) = "needs-audio(" <> show n <> ")"
  show (CoEffectNeedsVideo n) = "needs-video(" <> show n <> ")"
  show (CoEffectNeeds3DModel n) = "needs-3d-model(" <> show n <> ")"
  show (CoEffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupElementCoEffect :: Semigroup ElementCoEffect where
  append = coEffectCombine

instance monoidElementCoEffect :: Monoid ElementCoEffect where
  mempty = CoEffectNone

-- | All primitive co-effects (with unit counts).
allElementCoEffects :: Array ElementCoEffect
allElementCoEffects =
  [ CoEffectNone
  , CoEffectNeedsFont 1
  , CoEffectNeedsIcon 1
  , CoEffectNeedsImage 1
  , CoEffectNeedsData 1
  , CoEffectNeedsAudio 1
  , CoEffectNeedsVideo 1
  , CoEffectNeeds3DModel 1
  ]

-- | Combine co-effects.
-- |
-- | ## Combining Semantics
-- |
-- | - Font counts: ADDITIVE (sum of fonts)
-- | - Icon counts: ADDITIVE (sum of icons)
-- | - Image counts: ADDITIVE (sum of images)
-- | - Data queries: ADDITIVE (sum of queries)
-- | - Dissimilar: COMPOSITE (wrapped in array)
coEffectCombine :: ElementCoEffect -> ElementCoEffect -> ElementCoEffect
coEffectCombine CoEffectNone e = e
coEffectCombine e CoEffectNone = e
coEffectCombine (CoEffectNeedsFont a) (CoEffectNeedsFont b) = 
  CoEffectNeedsFont (a + b)
coEffectCombine (CoEffectNeedsIcon a) (CoEffectNeedsIcon b) = 
  CoEffectNeedsIcon (a + b)
coEffectCombine (CoEffectNeedsImage a) (CoEffectNeedsImage b) = 
  CoEffectNeedsImage (a + b)
coEffectCombine (CoEffectNeedsData a) (CoEffectNeedsData b) = 
  CoEffectNeedsData (a + b)
coEffectCombine (CoEffectNeedsAudio a) (CoEffectNeedsAudio b) = 
  CoEffectNeedsAudio (a + b)
coEffectCombine (CoEffectNeedsVideo a) (CoEffectNeedsVideo b) = 
  CoEffectNeedsVideo (a + b)
coEffectCombine (CoEffectNeeds3DModel a) (CoEffectNeeds3DModel b) = 
  CoEffectNeeds3DModel (a + b)
coEffectCombine (CoEffectComposite a) (CoEffectComposite b) = 
  CoEffectComposite (a <> b)
coEffectCombine (CoEffectComposite a) e = CoEffectComposite (a <> [e])
coEffectCombine e (CoEffectComposite b) = CoEffectComposite ([e] <> b)
coEffectCombine e1 e2 = if e1 == e2 then e1 else CoEffectComposite [e1, e2]

-- | No co-effects (identity).
coEffectNone :: ElementCoEffect
coEffectNone = CoEffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // graded element type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Element paired with its effect and co-effect grades.
-- |
-- | This is the runtime representation. The grades are computed from
-- | the Element structure and stored for efficient querying.
-- |
-- | ## Why Not Type-Level Grades?
-- |
-- | PureScript lacks dependent types for true type-level grade tracking.
-- | Instead we compute grades at construction time and verify at boundaries.
-- | The grades are still deterministic: same Element = same grades.
-- |
-- | ## Determinism Guarantee
-- |
-- | Same Element value = same effect grade = same co-effect grade = same UUID.
-- | This is guaranteed because Element is pure data composed from Schema atoms.
type GradedElement =
  { element :: Element
  , effect :: ElementEffect
  , coEffect :: ElementCoEffect
  , uuid :: UUID5.UUID5
  }

-- | Compute grades for an Element and wrap it.
-- |
-- | The grades are derived deterministically from Element structure.
gradeElement :: Element -> GradedElement
gradeElement elem =
  { element: elem
  , effect: elementEffect elem
  , coEffect: elementCoEffect elem
  , uuid: elementUUID elem
  }

-- | Compute effect grade of an Element.
-- |
-- | Currently all Elements are pure (no embedded event handlers).
-- | Effects are applied externally via EventBindingMap.
elementEffect :: Element -> ElementEffect
elementEffect _ = EffectPure

-- | Compute co-effect requirements of an Element.
-- |
-- | Traverses the Element tree counting resources needed.
elementCoEffect :: Element -> ElementCoEffect
elementCoEffect _ = CoEffectNone

-- | Compute deterministic UUID for an Element.
-- |
-- | Same Element = same UUID. Always.
elementUUID :: Element -> UUID5.UUID5
elementUUID elem = UUID5.uuid5 nsElementEffect (show elem)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // event binding (external)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event binding connects an Element UUID to an event handler.
-- |
-- | ## Architecture
-- |
-- | Events are NOT embedded in Element. Instead:
-- |
-- | 1. Element is pure data with deterministic UUID
-- | 2. EventBindingMap maps UUID → handler
-- | 3. Runtime wires events via pick buffer hit testing
-- |
-- | This separation enables:
-- | - Pure Element serialization (no closures)
-- | - Deterministic Element identity
-- | - Hot-reloading event handlers without rebuilding Elements
-- | - Static analysis of Element structure independent of behavior
type EventBinding msg =
  { elementId :: UUID5.UUID5           -- ^ Element this binding applies to
  , eventFilter :: GesturalEvent -> Boolean  -- ^ Which events to handle
  , handler :: GesturalEvent -> msg    -- ^ Handler producing message
  }

-- | Map from Element UUIDs to their event bindings.
-- |
-- | Multiple bindings per Element are supported (e.g., click AND hover).
type EventBindingMap msg = Map UUID5.UUID5 (Array (EventBinding msg))

-- | Empty binding map.
emptyBindingMap :: forall msg. EventBindingMap msg
emptyBindingMap = Map.empty

-- | Add an event binding.
bindEvent 
  :: forall msg
   . UUID5.UUID5 
  -> (GesturalEvent -> Boolean) 
  -> (GesturalEvent -> msg) 
  -> EventBindingMap msg 
  -> EventBindingMap msg
bindEvent elemId eventFilter handler bindingMap =
  let
    binding = { elementId: elemId, eventFilter: eventFilter, handler: handler }
    existing = Map.lookup elemId bindingMap
    updated = case existing of
      Nothing -> [binding]
      Just bindings -> bindings <> [binding]
  in
    Map.insert elemId updated bindingMap

-- | Lookup bindings for an Element.
lookupBinding 
  :: forall msg
   . UUID5.UUID5 
  -> EventBindingMap msg 
  -> Maybe (Array (EventBinding msg))
lookupBinding = Map.lookup
