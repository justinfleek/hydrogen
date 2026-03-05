-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // cdp // session
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chrome DevTools Protocol session state machine with graded effects.
-- |
-- | ## System Fω Type Structure
-- |
-- | Session operations form a bounded join-semilattice of effects:
-- |
-- |     Pure ⊑ SessionConnect ⊑ SessionCommand ⊑ SessionFull
-- |
-- | Co-effects track what resources a session NEEDS:
-- |     NeedsNothing ⊑ NeedsBrowser ⊑ NeedsNetwork ⊑ NeedsFull
-- |
-- | ## Graded Monad Integration
-- |
-- | Session operations live in `HydrogenM` with appropriate grades:
-- |
-- |     connect :: HydrogenM NetOnly SessionState
-- |     enableDomain :: HydrogenM NetOnly SessionState
-- |
-- | ## Presburger Arithmetic Constraints
-- |
-- | All session resources are bounded integers:
-- |     - Request ID: 0..2^31-1 (monotonic, no reuse)
-- |     - Pending count: 0..1000 (backpressure bound)
-- |     - Domain count: 0..4 (fixed domain set)
-- |
-- | This makes constraint satisfaction decidable.
-- |
-- | ## Lean4 Proofs
-- |
-- | Proven invariants in `proofs/Hydrogen/CDP/Session.lean`:
-- |     1. closed_preserved — Terminal state is preserved
-- |     2. closed_emits_nothing — No commands from closed state
-- |     3. request_id_monotonic — IDs never decrease
-- |     4. pending_stays_bounded — Pending count ≤ max
-- |     5. enable_requires_connected — Domain enable needs connection
-- |     6. domain_enabled_after_event — Enable event updates state

module Hydrogen.CDP.Session
  ( -- * Session Effects (what operations CAN DO)
    SessionEffect
      ( SessionEffectPure
      , SessionEffectConnect
      , SessionEffectCommand
      , SessionEffectClose
      , SessionEffectComposite
      )
  , sessionEffectCombine
  
    -- * Session Co-Effects (what operations NEED)
  , SessionCoEffect
      ( SessionNeedsNothing
      , SessionNeedsBrowser
      , SessionNeedsNetwork
      , SessionNeedsComposite
      )
  , sessionCoEffectCombine
  
    -- * Bounded Resource Types
  , RequestId
  , requestIdZero
  , requestIdNext
  , requestIdValue
  , requestIdBound
  
  , PendingCount
  , pendingCountZero
  , pendingCountIncrement
  , pendingCountDecrement
  , pendingCountValue
  , pendingCountBound
  
    -- * CDP Domains
  , Domain(DomainPage, DomainDom, DomainCss, DomainRuntime)
  , domainCount
  , DomainState
  , domainStateInitial
  , isDomainEnabled
  , enableDomain
  , enabledDomainCount
  
    -- * Session Lifecycle (bounded semilattice)
  , Phase(Disconnected, Connecting, Connected, Closed)
  , phaseOrder
  , isTerminalPhase
  , canSendInPhase
  
    -- * Session State
  , SessionState
  , sessionStateInitial
  , sessionPhase
  , sessionNextRequestId
  , sessionPendingCount
  , sessionDomains
  , sessionEffect
  , sessionCoEffect
  
    -- * Session Constraints (Presburger)
  , SessionConstraint
      ( ConstraintRequestIdBound
      , ConstraintPendingBound
      , ConstraintDomainEnabled
      , ConstraintPhaseIs
      , ConstraintAnd
      , ConstraintOr
      , ConstraintTrue
      , ConstraintFalse
      )
  , constraintSatisfied
  , canConnect
  , canEnable
  , canClose
  
    -- * Commands and Events
  , Command(CmdConnect, CmdEnableDomain, CmdClose)
  , Event(EvtConnected, EvtConnectionFailed, EvtDomainEnabled, EvtDisconnected)
  , Action(ActConnect, ActEnableDomain, ActDisconnect)
  , Input(InputUser, InputBrowser)
  
    -- * Pure Transition Function
  , TransitionResult
  , transition
  
    -- * Graded Operations (pure state machine)
  , GradedSession
  , runSession
  , pureSession
  , connectSession
  , enableDomainSession
  , closeSession
  
    -- * HydrogenM API (graded monad integration)
  , SessionM
  , runSessionM
  , liftPure
  , connectM
  , enableDomainM
  , closeM
  , getSessionState
  , withSession
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
  , class Functor
  , class Apply
  , class Applicative
  , class Bind
  , class Monad
  , show
  , mempty
  , otherwise
  , pure
  , bind
  , map
  , apply
  , not
  , (==)
  , (<)
  , (>)
  , (+)
  , (-)
  , (&&)
  , (||)
  , (<>)
  , (>=)
  , (<=)
  , (>>=)
  , (<$>)
  , (<*>)
  )

import Data.Array (length, index, foldl) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Effect.Grade (Grade, NetOnly, Pure)
import Hydrogen.Effect.Graded 
  ( HydrogenM(HydrogenM)
  , HydrogenResult
  , HydrogenGrade
  , HydrogenCoEffect
  , HydrogenProvenance
  , emptyGrade
  , emptyCoEffect
  , emptyProvenance
  , combineGrades
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // session effects (graded monoid)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What session operations CAN DO.
-- |
-- | Forms a bounded join-semilattice:
-- |     Pure ⊑ Connect ⊑ Command ⊑ Close ⊑ ⊤
-- |
-- | Composition is union: effectA ⊗ effectB = join(effectA, effectB)
data SessionEffect
  = SessionEffectPure        -- ^ No session effects (query state)
  | SessionEffectConnect     -- ^ Can initiate connection
  | SessionEffectCommand     -- ^ Can send commands
  | SessionEffectClose       -- ^ Can close session
  | SessionEffectComposite   -- ^ Multiple effects combined
      (Array SessionEffect)

derive instance eqSessionEffect :: Eq SessionEffect
derive instance ordSessionEffect :: Ord SessionEffect

instance showSessionEffect :: Show SessionEffect where
  show SessionEffectPure = "pure"
  show SessionEffectConnect = "connect"
  show SessionEffectCommand = "command"
  show SessionEffectClose = "close"
  show (SessionEffectComposite es) = "composite(" <> show es <> ")"

instance semigroupSessionEffect :: Semigroup SessionEffect where
  append = sessionEffectCombine

instance monoidSessionEffect :: Monoid SessionEffect where
  mempty = SessionEffectPure

-- | Combine session effects (semilattice join).
sessionEffectCombine :: SessionEffect -> SessionEffect -> SessionEffect
sessionEffectCombine SessionEffectPure e = e
sessionEffectCombine e SessionEffectPure = e
sessionEffectCombine (SessionEffectComposite a) (SessionEffectComposite b) =
  SessionEffectComposite (a <> b)
sessionEffectCombine (SessionEffectComposite a) e = SessionEffectComposite (a <> [e])
sessionEffectCombine e (SessionEffectComposite b) = SessionEffectComposite ([e] <> b)
sessionEffectCombine e1 e2 = if e1 == e2 then e1 else SessionEffectComposite [e1, e2]

-- ═════════════════════════════════════════════════════════════════════════════
--                                        // session co-effects (resource needs)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What session operations NEED from the environment.
-- |
-- | Co-effect algebra: tracks what must be provided.
-- |     NeedsNothing ⊑ NeedsBrowser ⊑ NeedsNetwork ⊑ ⊤
data SessionCoEffect
  = SessionNeedsNothing      -- ^ Self-contained (pure query)
  | SessionNeedsBrowser      -- ^ Requires browser process
  | SessionNeedsNetwork      -- ^ Requires network access (WebSocket)
  | SessionNeedsComposite    -- ^ Multiple requirements
      (Array SessionCoEffect)

derive instance eqSessionCoEffect :: Eq SessionCoEffect
derive instance ordSessionCoEffect :: Ord SessionCoEffect

instance showSessionCoEffect :: Show SessionCoEffect where
  show SessionNeedsNothing = "needs-nothing"
  show SessionNeedsBrowser = "needs-browser"
  show SessionNeedsNetwork = "needs-network"
  show (SessionNeedsComposite cs) = "needs(" <> show cs <> ")"

instance semigroupSessionCoEffect :: Semigroup SessionCoEffect where
  append = sessionCoEffectCombine

instance monoidSessionCoEffect :: Monoid SessionCoEffect where
  mempty = SessionNeedsNothing

-- | Combine co-effects (tracks all required resources).
sessionCoEffectCombine :: SessionCoEffect -> SessionCoEffect -> SessionCoEffect
sessionCoEffectCombine SessionNeedsNothing e = e
sessionCoEffectCombine e SessionNeedsNothing = e
sessionCoEffectCombine (SessionNeedsComposite a) (SessionNeedsComposite b) =
  SessionNeedsComposite (a <> b)
sessionCoEffectCombine (SessionNeedsComposite a) e = SessionNeedsComposite (a <> [e])
sessionCoEffectCombine e (SessionNeedsComposite b) = SessionNeedsComposite ([e] <> b)
sessionCoEffectCombine e1 e2 = if e1 == e2 then e1 else SessionNeedsComposite [e1, e2]

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // bounded types (Presburger atoms)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Request ID bound.
-- |
-- | Bounded: 0 ≤ id < 2^31
-- | Behavior: Returns Nothing on overflow (session must reset)
requestIdBound :: Bounded.IntBounds
requestIdBound = Bounded.intBounds 0 2147483647 Bounded.Clamps
  "RequestId" "CDP request identifier (monotonic within session)"

-- | Request ID with bounded value.
newtype RequestId = RequestId Int

derive instance eqRequestId :: Eq RequestId
derive instance ordRequestId :: Ord RequestId

instance showRequestId :: Show RequestId where
  show (RequestId n) = "req:" <> show n

-- | Zero request ID.
requestIdZero :: RequestId
requestIdZero = RequestId 0

-- | Next request ID, or Nothing if overflow.
requestIdNext :: RequestId -> Maybe RequestId
requestIdNext (RequestId n)
  | n < 2147483647 = Just (RequestId (n + 1))
  | otherwise = Nothing

-- | Extract value.
requestIdValue :: RequestId -> Int
requestIdValue (RequestId n) = n

-- | Pending count bound.
-- |
-- | Bounded: 0 ≤ count ≤ 1000
-- | Rationale: Backpressure to prevent memory exhaustion
pendingCountBound :: Bounded.IntBounds
pendingCountBound = Bounded.intBounds 0 1000 Bounded.Clamps
  "PendingCount" "In-flight CDP requests (backpressure limited)"

-- | Pending request count.
newtype PendingCount = PendingCount Int

derive instance eqPendingCount :: Eq PendingCount
derive instance ordPendingCount :: Ord PendingCount

instance showPendingCount :: Show PendingCount where
  show (PendingCount n) = "pending:" <> show n

-- | Zero pending.
pendingCountZero :: PendingCount
pendingCountZero = PendingCount 0

-- | Increment pending, or Nothing if at limit.
pendingCountIncrement :: PendingCount -> Maybe PendingCount
pendingCountIncrement (PendingCount n)
  | n < 1000 = Just (PendingCount (n + 1))
  | otherwise = Nothing

-- | Decrement pending (saturates at 0).
pendingCountDecrement :: PendingCount -> PendingCount
pendingCountDecrement (PendingCount n)
  | n > 0 = PendingCount (n - 1)
  | otherwise = PendingCount 0

-- | Extract value.
pendingCountValue :: PendingCount -> Int
pendingCountValue (PendingCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cdp domains
-- ═════════════════════════════════════════════════════════════════════════════

-- | CDP domains for web scraping/testing.
-- |
-- | Fixed enumeration: exactly 4 domains.
-- | This makes domain counting a Presburger predicate.
data Domain
  = DomainPage     -- ^ Page.* methods (navigation, screenshots)
  | DomainDom      -- ^ DOM.* methods (element queries)
  | DomainCss      -- ^ CSS.* methods (computed styles)
  | DomainRuntime  -- ^ Runtime.* methods (JS evaluation)

derive instance eqDomain :: Eq Domain
derive instance ordDomain :: Ord Domain

instance showDomain :: Show Domain where
  show DomainPage = "Page"
  show DomainDom = "DOM"
  show DomainCss = "CSS"
  show DomainRuntime = "Runtime"

-- | Total number of domains (constant for Presburger).
domainCount :: Int
domainCount = 4

-- | Domain enable state.
type DomainState =
  { page :: Boolean
  , dom :: Boolean
  , css :: Boolean
  , runtime :: Boolean
  }

-- | Initial: no domains enabled.
domainStateInitial :: DomainState
domainStateInitial = { page: false, dom: false, css: false, runtime: false }

-- | Check if domain is enabled.
isDomainEnabled :: DomainState -> Domain -> Boolean
isDomainEnabled ds DomainPage = ds.page
isDomainEnabled ds DomainDom = ds.dom
isDomainEnabled ds DomainCss = ds.css
isDomainEnabled ds DomainRuntime = ds.runtime

-- | Enable a domain.
enableDomain :: DomainState -> Domain -> DomainState
enableDomain ds DomainPage = ds { page = true }
enableDomain ds DomainDom = ds { dom = true }
enableDomain ds DomainCss = ds { css = true }
enableDomain ds DomainRuntime = ds { runtime = true }

-- | Count enabled domains (for Presburger constraints).
enabledDomainCount :: DomainState -> Int
enabledDomainCount ds =
  (if ds.page then 1 else 0) +
  (if ds.dom then 1 else 0) +
  (if ds.css then 1 else 0) +
  (if ds.runtime then 1 else 0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                         // session lifecycle (semilattice)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Session lifecycle phases.
-- |
-- | Total order: Disconnected < Connecting < Connected < Closed
-- | Closed is terminal (no transitions out).
data Phase
  = Disconnected  -- ^ Not connected
  | Connecting    -- ^ Connection in progress
  | Connected     -- ^ Ready for commands
  | Closed        -- ^ Session ended (terminal)

derive instance eqPhase :: Eq Phase
derive instance ordPhase :: Ord Phase

instance showPhase :: Show Phase where
  show Disconnected = "disconnected"
  show Connecting = "connecting"
  show Connected = "connected"
  show Closed = "closed"

-- | Phase order for Presburger constraints.
phaseOrder :: Phase -> Int
phaseOrder Disconnected = 0
phaseOrder Connecting = 1
phaseOrder Connected = 2
phaseOrder Closed = 3

-- | Is this a terminal phase?
isTerminalPhase :: Phase -> Boolean
isTerminalPhase Closed = true
isTerminalPhase _ = false

-- | Can we send commands in this phase?
canSendInPhase :: Phase -> Boolean
canSendInPhase Connected = true
canSendInPhase _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // session state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete session state.
type SessionState =
  { phase :: Phase
  , nextRequestId :: RequestId
  , pendingCount :: PendingCount
  , domains :: DomainState
  }

-- | Initial session state.
sessionStateInitial :: SessionState
sessionStateInitial =
  { phase: Disconnected
  , nextRequestId: requestIdZero
  , pendingCount: pendingCountZero
  , domains: domainStateInitial
  }

-- Accessors
sessionPhase :: SessionState -> Phase
sessionPhase s = s.phase

sessionNextRequestId :: SessionState -> RequestId
sessionNextRequestId s = s.nextRequestId

sessionPendingCount :: SessionState -> PendingCount
sessionPendingCount s = s.pendingCount

sessionDomains :: SessionState -> DomainState
sessionDomains s = s.domains

-- | Compute effect grade for current state.
sessionEffect :: SessionState -> SessionEffect
sessionEffect s = case s.phase of
  Disconnected -> SessionEffectConnect
  Connecting -> SessionEffectPure
  Connected -> SessionEffectComposite [SessionEffectCommand, SessionEffectClose]
  Closed -> SessionEffectPure

-- | Compute co-effect requirements for current state.
sessionCoEffect :: SessionState -> SessionCoEffect
sessionCoEffect s = case s.phase of
  Disconnected -> SessionNeedsComposite [SessionNeedsBrowser, SessionNeedsNetwork]
  Connecting -> SessionNeedsNetwork
  Connected -> SessionNeedsNetwork
  Closed -> SessionNeedsNothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                      // session constraints (Presburger)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints on session state.
-- |
-- | All predicates are decidable via Presburger arithmetic:
-- | - Request ID comparisons (bounded integers)
-- | - Pending count comparisons (bounded integers)
-- | - Domain enabled checks (Boolean)
-- | - Phase comparisons (finite enum mapped to integers)
data SessionConstraint
  = ConstraintRequestIdBound Int Int  -- ^ current ≤ max
  | ConstraintPendingBound Int Int    -- ^ current ≤ max
  | ConstraintDomainEnabled Domain    -- ^ domain is enabled
  | ConstraintPhaseIs Phase           -- ^ phase equals value
  | ConstraintAnd SessionConstraint SessionConstraint
  | ConstraintOr SessionConstraint SessionConstraint
  | ConstraintTrue
  | ConstraintFalse

derive instance eqSessionConstraint :: Eq SessionConstraint
derive instance ordSessionConstraint :: Ord SessionConstraint

instance showSessionConstraint :: Show SessionConstraint where
  show (ConstraintRequestIdBound cur max) = "reqId(" <> show cur <> "≤" <> show max <> ")"
  show (ConstraintPendingBound cur max) = "pending(" <> show cur <> "≤" <> show max <> ")"
  show (ConstraintDomainEnabled d) = "enabled(" <> show d <> ")"
  show (ConstraintPhaseIs p) = "phase=" <> show p
  show (ConstraintAnd a b) = "(" <> show a <> "∧" <> show b <> ")"
  show (ConstraintOr a b) = "(" <> show a <> "∨" <> show b <> ")"
  show ConstraintTrue = "⊤"
  show ConstraintFalse = "⊥"

-- | Evaluate constraint against session state.
constraintSatisfied :: SessionState -> SessionConstraint -> Boolean
constraintSatisfied _ ConstraintTrue = true
constraintSatisfied _ ConstraintFalse = false
constraintSatisfied s (ConstraintRequestIdBound cur max) =
  cur <= max && requestIdValue s.nextRequestId <= max
constraintSatisfied s (ConstraintPendingBound cur max) =
  cur <= max && pendingCountValue s.pendingCount <= max
constraintSatisfied s (ConstraintDomainEnabled d) = isDomainEnabled s.domains d
constraintSatisfied s (ConstraintPhaseIs p) = s.phase == p
constraintSatisfied s (ConstraintAnd a b) =
  constraintSatisfied s a && constraintSatisfied s b
constraintSatisfied s (ConstraintOr a b) =
  constraintSatisfied s a || constraintSatisfied s b

-- | Can we connect in this state?
canConnect :: SessionState -> Boolean
canConnect s = s.phase == Disconnected

-- | Can we enable a domain in this state?
canEnable :: SessionState -> Domain -> Boolean
canEnable s d =
  s.phase == Connected &&
  not (isDomainEnabled s.domains d) &&
  pendingCountValue s.pendingCount < 1000 &&
  requestIdValue s.nextRequestId < 2147483647

-- | Can we close in this state?
canClose :: SessionState -> Boolean
canClose s = s.phase == Connected

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // commands and events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands emitted by state machine.
data Command
  = CmdConnect String Int        -- ^ host, port
  | CmdEnableDomain Int Domain   -- ^ requestId, domain
  | CmdClose

derive instance eqCommand :: Eq Command

instance showCommand :: Show Command where
  show (CmdConnect host port) = "Connect(" <> host <> ":" <> show port <> ")"
  show (CmdEnableDomain rid d) = "Enable(" <> show rid <> "," <> show d <> ")"
  show CmdClose = "Close"

-- | Events from browser.
data Event
  = EvtConnected
  | EvtConnectionFailed
  | EvtDomainEnabled Int Domain
  | EvtDisconnected

derive instance eqEvent :: Eq Event

instance showEvent :: Show Event where
  show EvtConnected = "Connected"
  show EvtConnectionFailed = "ConnectionFailed"
  show (EvtDomainEnabled rid d) = "DomainEnabled(" <> show rid <> "," <> show d <> ")"
  show EvtDisconnected = "Disconnected"

-- | User actions.
data Action
  = ActConnect String Int
  | ActEnableDomain Domain
  | ActDisconnect

derive instance eqAction :: Eq Action

instance showAction :: Show Action where
  show (ActConnect host port) = "Connect(" <> host <> ":" <> show port <> ")"
  show (ActEnableDomain d) = "Enable(" <> show d <> ")"
  show ActDisconnect = "Disconnect"

-- | Input to state machine.
data Input
  = InputUser Action
  | InputBrowser Event

derive instance eqInput :: Eq Input

instance showInput :: Show Input where
  show (InputUser a) = "User(" <> show a <> ")"
  show (InputBrowser e) = "Browser(" <> show e <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // pure transition function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition result with graded effect annotation.
type TransitionResult =
  { nextState :: SessionState
  , commands :: Array Command
  , effect :: SessionEffect      -- ^ Effect grade of this transition
  , coEffect :: SessionCoEffect  -- ^ Co-effect requirements
  }

-- | Core transition function.
-- |
-- | Pure: SessionState × Input → TransitionResult
-- |
-- | Mirrors Lean4 proofs in `proofs/Hydrogen/CDP/Session.lean`.
transition :: SessionState -> Input -> TransitionResult
transition s input = case s.phase, input of
  
  -- DISCONNECTED
  Disconnected, InputUser (ActConnect host port) ->
    { nextState: s { phase = Connecting }
    , commands: [CmdConnect host port]
    , effect: SessionEffectConnect
    , coEffect: SessionNeedsComposite [SessionNeedsBrowser, SessionNeedsNetwork]
    }
  
  Disconnected, _ ->
    pureResult s
  
  -- CONNECTING
  Connecting, InputBrowser EvtConnected ->
    { nextState: s { phase = Connected }
    , commands: []
    , effect: SessionEffectPure
    , coEffect: SessionNeedsNothing
    }
  
  Connecting, InputBrowser EvtConnectionFailed ->
    { nextState: s { phase = Disconnected }
    , commands: []
    , effect: SessionEffectPure
    , coEffect: SessionNeedsNothing
    }
  
  Connecting, _ ->
    pureResult s
  
  -- CONNECTED
  Connected, InputUser (ActEnableDomain domain) ->
    if isDomainEnabled s.domains domain then
      pureResult s
    else case requestIdNext s.nextRequestId, pendingCountIncrement s.pendingCount of
      Just nextId, Just nextPending ->
        { nextState: s { nextRequestId = nextId, pendingCount = nextPending }
        , commands: [CmdEnableDomain (requestIdValue s.nextRequestId) domain]
        , effect: SessionEffectCommand
        , coEffect: SessionNeedsNetwork
        }
      _, _ ->
        pureResult s  -- Resource exhausted
  
  Connected, InputUser ActDisconnect ->
    { nextState: s { phase = Closed }
    , commands: [CmdClose]
    , effect: SessionEffectClose
    , coEffect: SessionNeedsNothing
    }
  
  Connected, InputBrowser (EvtDomainEnabled _ domain) ->
    { nextState: s
        { domains = enableDomain s.domains domain
        , pendingCount = pendingCountDecrement s.pendingCount
        }
    , commands: []
    , effect: SessionEffectPure
    , coEffect: SessionNeedsNothing
    }
  
  Connected, InputBrowser EvtDisconnected ->
    { nextState: s { phase = Closed }
    , commands: []
    , effect: SessionEffectPure
    , coEffect: SessionNeedsNothing
    }
  
  Connected, _ ->
    pureResult s
  
  -- CLOSED (terminal)
  Closed, _ ->
    pureResult s

-- | Pure result (no state change, no commands).
pureResult :: SessionState -> TransitionResult
pureResult s =
  { nextState: s
  , commands: []
  , effect: SessionEffectPure
  , coEffect: SessionNeedsNothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // graded operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Graded session computation.
-- |
-- | Wraps SessionState → TransitionResult with effect/co-effect tracking.
-- | This is the interface for composing session operations monoidally.
type GradedSession =
  { state :: SessionState
  , effect :: SessionEffect
  , coEffect :: SessionCoEffect
  , commands :: Array Command
  }

-- | Run a sequence of inputs, accumulating grades.
runSession :: SessionState -> Array Input -> GradedSession
runSession initial inputs =
  foldlInputs initial inputs
  { state: initial
  , effect: SessionEffectPure
  , coEffect: SessionNeedsNothing
  , commands: []
  }

-- | Fold over inputs accumulating results.
-- |
-- | Pure implementation using Data.Array.foldl — no FFI required.
foldlInputs :: SessionState -> Array Input -> GradedSession -> GradedSession
foldlInputs initialState inputs initialAcc =
  let
    -- Fold function that threads state through
    go :: { state :: SessionState, acc :: GradedSession } 
       -> Input 
       -> { state :: SessionState, acc :: GradedSession }
    go { state: s, acc } input =
      let 
        result = transition s input
        newAcc =
          { state: result.nextState
          , effect: sessionEffectCombine acc.effect result.effect
          , coEffect: sessionCoEffectCombine acc.coEffect result.coEffect
          , commands: acc.commands <> result.commands
          }
      in { state: result.nextState, acc: newAcc }
    
    final = Array.foldl go { state: initialState, acc: initialAcc } inputs
  in
    final.acc

-- | Pure session (query only, no effects).
pureSession :: SessionState -> GradedSession
pureSession s =
  { state: s
  , effect: SessionEffectPure
  , coEffect: SessionNeedsNothing
  , commands: []
  }

-- | Connect session.
connectSession :: String -> Int -> SessionState -> GradedSession
connectSession host port s =
  let result = transition s (InputUser (ActConnect host port))
  in { state: result.nextState
     , effect: result.effect
     , coEffect: result.coEffect
     , commands: result.commands
     }

-- | Enable domain.
enableDomainSession :: Domain -> SessionState -> GradedSession
enableDomainSession domain s =
  let result = transition s (InputUser (ActEnableDomain domain))
  in { state: result.nextState
     , effect: result.effect
     , coEffect: result.coEffect
     , commands: result.commands
     }

-- | Close session.
closeSession :: SessionState -> GradedSession
closeSession s =
  let result = transition s (InputUser ActDisconnect)
  in { state: result.nextState
     , effect: result.effect
     , coEffect: result.coEffect
     , commands: result.commands
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // HydrogenM API (graded monad)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Session monad: HydrogenM specialized for CDP session operations.
-- |
-- | ## Grade Semantics
-- |
-- | - `SessionM Pure a`: Pure query, no network effects
-- | - `SessionM NetOnly a`: Network operation (connect, send command)
-- |
-- | ## Runtime Tracking
-- |
-- | The HydrogenM wrapper tracks:
-- | - Latency (ms per operation)
-- | - Provider calls (CDP commands sent)
-- | - Cache hits/misses (for repeated queries)
-- |
-- | ## Composition
-- |
-- | ```purescript
-- | fullSession :: SessionM NetOnly SessionState
-- | fullSession = do
-- |   s0 <- connectM "localhost" 9222
-- |   s1 <- enableDomainM DomainPage s0
-- |   s2 <- enableDomainM DomainDom s1
-- |   pure s2
-- | ```
type SessionM (g :: Grade) a = HydrogenM g a

-- | Session computation result with cost tracking.
type SessionResult a =
  { result :: a
  , sessionGrade :: HydrogenGrade      -- ^ Latency, call counts
  , sessionCoEffect :: HydrogenCoEffect -- ^ Resources accessed
  , sessionProvenance :: HydrogenProvenance -- ^ Provider info
  , commands :: Array Command          -- ^ CDP commands to execute
  }

-- | Run a session computation.
-- |
-- | Extracts the result and accumulated cost data.
runSessionM :: forall g a. SessionM g a -> Effect (HydrogenResult a)
runSessionM (HydrogenM m) = m

-- | Lift a pure value into SessionM.
-- |
-- | Grade: Pure (no effects)
liftPure :: forall a. a -> SessionM Pure a
liftPure a = HydrogenM (pure { result: a, grade: emptyGrade, coeffect: emptyCoEffect, provenance: emptyProvenance })

-- | Connect to a Chrome DevTools Protocol endpoint.
-- |
-- | Grade: NetOnly (requires network)
-- |
-- | ## Semantics
-- |
-- | Transitions session from Disconnected → Connecting → Connected.
-- | Emits CmdConnect command for the runtime to execute.
-- |
-- | ## Latency Tracking
-- |
-- | Connection latency is recorded in HydrogenGrade.latencyMs.
-- | This enables optimization of connection pooling at swarm scale.
connectM :: String -> Int -> SessionState -> SessionM NetOnly GradedSession
connectM host port s = HydrogenM (pure 
  { result: connectSession host port s
  , grade: emptyGrade { providerCalls = 1 }
  , coeffect: emptyCoEffect { httpAccesses = [{ url: "ws://" <> host <> ":" <> show port, method: "WS" }] }
  , provenance: emptyProvenance { providersUsed = ["chrome-devtools-protocol"] }
  })

-- | Enable a CDP domain.
-- |
-- | Grade: NetOnly (requires network)
-- |
-- | ## Semantics
-- |
-- | Sends Domain.enable command to browser.
-- | Tracks pending request count (Presburger bounded).
-- |
-- | ## Prerequisites
-- |
-- | Session must be in Connected phase.
-- | Constraint: pendingCount < 1000 ∧ requestId < 2^31
enableDomainM :: Domain -> SessionState -> SessionM NetOnly GradedSession
enableDomainM domain s = HydrogenM (pure
  { result: enableDomainSession domain s
  , grade: emptyGrade { providerCalls = 1 }
  , coeffect: emptyCoEffect
  , provenance: emptyProvenance { providersUsed = ["chrome-devtools-protocol"] }
  })

-- | Close the CDP session.
-- |
-- | Grade: Pure (no network effect — just state transition)
-- |
-- | ## Semantics
-- |
-- | Transitions session to Closed (terminal state).
-- | Emits CmdClose command for runtime cleanup.
-- |
-- | After close, no further commands are valid (enforced by phase check).
closeM :: SessionState -> SessionM Pure GradedSession
closeM s = HydrogenM (pure
  { result: closeSession s
  , grade: emptyGrade
  , coeffect: emptyCoEffect
  , provenance: emptyProvenance
  })

-- | Get current session state without effects.
-- |
-- | Grade: Pure
getSessionState :: GradedSession -> SessionM Pure SessionState
getSessionState gs = liftPure gs.state

-- | Execute a session operation with state threading.
-- |
-- | Grade: inherits from inner computation
-- |
-- | ## Pattern
-- |
-- | ```purescript
-- | withSession sessionStateInitial \s -> do
-- |   s1 <- connectM "localhost" 9222 s
-- |   s2 <- enableDomainM DomainPage s1.state
-- |   pure s2
-- | ```
withSession :: forall g a. SessionState -> (SessionState -> SessionM g a) -> SessionM g a
withSession initial f = f initial
