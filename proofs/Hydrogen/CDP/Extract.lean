/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           HYDROGEN // CDP // EXTRACT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CDP Session State Machine → CodeGen IR for C++ Extraction

  This module defines the CDP Session state machine in a format compatible
  with libevring's Continuity.CodeGen IR. The IR can be consumed by:
    - Continuity.CodeGen.Cpp  → C++23 with std::variant
    - Continuity.CodeGen.Rust → Rust with enums
    - Continuity.CodeGen.Haskell → Haskell with ADTs

  The generated C++ integrates with libevring's io_uring WebSocket machinery
  for a pure native CDP client with zero JavaScript.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.CDP.Session

namespace Hydrogen.CDP.Extract

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §0 CODEGEN IR (mirrors Continuity.CodeGen)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Primitive types with known representations across all targets -/
inductive Prim where
  | unit
  | bool
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | usize | isize
  | f32 | f64
  | bytes
  | string
  deriving Repr, DecidableEq, Inhabited

/-- Type expressions in the IR -/
inductive Ty where
  | prim : Prim → Ty
  | named : String → Ty
  | array : Ty → Ty
  | fixedArray : Ty → Nat → Ty
  | optional : Ty → Ty
  | result : Ty → Ty → Ty
  | tuple : List Ty → Ty
  deriving Repr, Inhabited

/-- A field in a struct or event payload -/
structure Field where
  name : String
  ty : Ty
  doc : Option String := none
  deriving Repr, Inhabited

/-- A state in a state machine -/
structure State where
  name : String
  doc : Option String := none
  isInitial : Bool := false
  isTerminal : Bool := false
  deriving Repr, Inhabited

/-- An event that can trigger transitions -/
structure Event where
  name : String
  payload : List Field := []
  doc : Option String := none
  deriving Repr, Inhabited

/-- An action produced by a transition -/
structure Action where
  name : String
  payload : List Field := []
  doc : Option String := none
  deriving Repr, Inhabited

/-- A transition in the state machine -/
structure Transition where
  from_ : String
  event : String
  to_ : String
  actions : List String := []
  guard : Option String := none
  doc : Option String := none
  deriving Repr, Inhabited

/-- State machine definition -/
structure StateMachine where
  name : String
  states : List State
  events : List Event
  actions : List Action
  transitions : List Transition
  doc : Option String := none
  deriving Repr, Inhabited

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §1 CDP SESSION STATE MACHINE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- CDP Session state machine for C++ extraction -/
def cdpSessionMachine : StateMachine := {
  name := "CDPSession"
  doc := some "Chrome DevTools Protocol session state machine. Proven invariants: request ID monotonicity, domain ordering, lifecycle finality, bounded pending count."

  states := [
    { name := "Disconnected"
    , doc := some "Initial state, no WebSocket connection"
    , isInitial := true
    , isTerminal := false }
  , { name := "Connecting"
    , doc := some "WebSocket handshake in progress"
    , isInitial := false
    , isTerminal := false }
  , { name := "Connected"
    , doc := some "WebSocket open, can send CDP commands"
    , isInitial := false
    , isTerminal := false }
  , { name := "Closed"
    , doc := some "Terminal state, session ended"
    , isInitial := false
    , isTerminal := true }
  ]

  events := [
    -- User actions
    { name := "UserConnect"
    , payload := [
        ⟨"host", .prim .string, some "Chrome DevTools host"⟩
      , ⟨"port", .prim .u16, some "Chrome DevTools port"⟩
      ]
    , doc := some "User requests connection to Chrome" }
  , { name := "UserEnableDomain"
    , payload := [
        ⟨"domain", .prim .u8, some "Domain enum: 0=Page, 1=DOM, 2=CSS, 3=Runtime"⟩
      ]
    , doc := some "User requests domain enable" }
  , { name := "UserDisconnect"
    , payload := []
    , doc := some "User requests graceful disconnect" }
    -- Browser events
  , { name := "BrowserConnected"
    , payload := []
    , doc := some "WebSocket connection established" }
  , { name := "BrowserConnectionFailed"
    , payload := []
    , doc := some "WebSocket connection failed" }
  , { name := "BrowserDomainEnabled"
    , payload := [
        ⟨"requestId", .prim .u32, some "Request ID that was acknowledged"⟩
      , ⟨"domain", .prim .u8, some "Domain that was enabled"⟩
      ]
    , doc := some "CDP domain.enable response received" }
  , { name := "BrowserDisconnected"
    , payload := []
    , doc := some "WebSocket closed by browser" }
  ]

  actions := [
    { name := "EmitConnect"
    , payload := [
        ⟨"host", .prim .string, none⟩
      , ⟨"port", .prim .u16, none⟩
      ]
    , doc := some "Emit WebSocket connect command to io_uring" }
  , { name := "EmitEnableDomain"
    , payload := [
        ⟨"requestId", .prim .u32, none⟩
      , ⟨"domain", .prim .u8, none⟩
      ]
    , doc := some "Emit CDP domain.enable JSON-RPC to WebSocket" }
  , { name := "EmitClose"
    , payload := []
    , doc := some "Emit WebSocket close to io_uring" }
  , { name := "UpdateDomainState"
    , payload := [
        ⟨"domain", .prim .u8, none⟩
      ]
    , doc := some "Mark domain as enabled in session state" }
  , { name := "DecrementPending"
    , payload := []
    , doc := some "Decrement pending request count" }
  ]

  transitions := [
    -- From Disconnected
    { from_ := "Disconnected"
    , event := "UserConnect"
    , to_ := "Connecting"
    , actions := ["EmitConnect"]
    , doc := some "Start WebSocket connection" }

    -- From Connecting
  , { from_ := "Connecting"
    , event := "BrowserConnected"
    , to_ := "Connected"
    , actions := []
    , doc := some "WebSocket handshake complete" }
  , { from_ := "Connecting"
    , event := "BrowserConnectionFailed"
    , to_ := "Disconnected"
    , actions := []
    , doc := some "Connection failed, return to disconnected" }

    -- From Connected
  , { from_ := "Connected"
    , event := "UserEnableDomain"
    , to_ := "Connected"
    , actions := ["EmitEnableDomain"]
    , guard := some "!domainEnabled && requestIdAvailable && pendingUnderLimit"
    , doc := some "Send domain.enable if not already enabled and resources available" }
  , { from_ := "Connected"
    , event := "UserDisconnect"
    , to_ := "Closed"
    , actions := ["EmitClose"]
    , doc := some "Graceful disconnect" }
  , { from_ := "Connected"
    , event := "BrowserDomainEnabled"
    , to_ := "Connected"
    , actions := ["UpdateDomainState", "DecrementPending"]
    , doc := some "Domain enabled response received" }
  , { from_ := "Connected"
    , event := "BrowserDisconnected"
    , to_ := "Closed"
    , actions := []
    , doc := some "Browser closed connection" }

    -- From Closed (terminal - no transitions out)
    -- Closed state accepts all events but produces no state change or actions
  ]
}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §2 CORRESPONDENCE PROOF
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The IR state names correspond to Session.Phase -/
theorem states_match_phase : 
    cdpSessionMachine.states.length = 4 ∧
    (cdpSessionMachine.states.map (·.name)) = 
      ["Disconnected", "Connecting", "Connected", "Closed"] := by
  simp [cdpSessionMachine]

/-- The IR has exactly one initial state -/
theorem single_initial_state :
    (cdpSessionMachine.states.filter (·.isInitial)).length = 1 := by
  simp [cdpSessionMachine]

/-- The IR has exactly one terminal state -/
theorem single_terminal_state :
    (cdpSessionMachine.states.filter (·.isTerminal)).length = 1 := by
  simp [cdpSessionMachine]

/-- Closed state has no outgoing transitions (matches Session.closed_is_terminal) -/
theorem closed_no_outgoing :
    (cdpSessionMachine.transitions.filter (·.from_ == "Closed")).length = 0 := by
  simp [cdpSessionMachine]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §3 CAPTURE STATE MACHINE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- CDP Capture state machine for temporal frame capture -/
def cdpCaptureMachine : StateMachine := {
  name := "CDPCapture"
  doc := some "Temporal capture state machine for recording browser frames over time."

  states := [
    { name := "Idle"
    , doc := some "No capture in progress"
    , isInitial := true
    , isTerminal := false }
  , { name := "Preparing"
    , doc := some "Setting up capture (enabling domains)"
    , isInitial := false
    , isTerminal := false }
  , { name := "Capturing"
    , doc := some "Actively capturing frames"
    , isInitial := false
    , isTerminal := false }
  , { name := "Paused"
    , doc := some "Capture paused, can resume"
    , isInitial := false
    , isTerminal := false }
  , { name := "Completed"
    , doc := some "Capture finished successfully"
    , isInitial := false
    , isTerminal := true }
  , { name := "Failed"
    , doc := some "Capture failed with error"
    , isInitial := false
    , isTerminal := true }
  ]

  events := [
    { name := "StartCapture"
    , payload := [
        ⟨"durationMs", .prim .u64, some "Capture duration in milliseconds"⟩
      , ⟨"intervalMs", .prim .u32, some "Frame interval in milliseconds"⟩
      ]
    , doc := some "User starts a capture" }
  , { name := "DomainsReady"
    , payload := []
    , doc := some "All required CDP domains enabled" }
  , { name := "FrameCaptured"
    , payload := [
        ⟨"frameIndex", .prim .u32, some "Zero-based frame index"⟩
      , ⟨"timestampMs", .prim .u64, some "Capture timestamp"⟩
      ]
    , doc := some "A frame was successfully captured" }
  , { name := "PauseCapture"
    , payload := []
    , doc := some "User pauses capture" }
  , { name := "ResumeCapture"
    , payload := []
    , doc := some "User resumes paused capture" }
  , { name := "StopCapture"
    , payload := []
    , doc := some "User stops capture early" }
  , { name := "CaptureComplete"
    , payload := [
        ⟨"totalFrames", .prim .u32, some "Total frames captured"⟩
      ]
    , doc := some "Capture duration elapsed" }
  , { name := "CaptureError"
    , payload := [
        ⟨"errorCode", .prim .u32, some "Error code"⟩
      ]
    , doc := some "Error during capture" }
  ]

  actions := [
    { name := "EnableDomains"
    , payload := []
    , doc := some "Enable Page, DOM, CSS, Runtime domains" }
  , { name := "StartTimer"
    , payload := [
        ⟨"intervalMs", .prim .u32, none⟩
      ]
    , doc := some "Start frame capture timer" }
  , { name := "StopTimer"
    , payload := []
    , doc := some "Stop frame capture timer" }
  , { name := "CaptureFrame"
    , payload := []
    , doc := some "Capture current DOM state" }
  , { name := "FinalizeCapture"
    , payload := []
    , doc := some "Finalize and save capture data" }
  ]

  transitions := [
    -- From Idle
    { from_ := "Idle"
    , event := "StartCapture"
    , to_ := "Preparing"
    , actions := ["EnableDomains"]
    , doc := some "Begin capture preparation" }

    -- From Preparing  
  , { from_ := "Preparing"
    , event := "DomainsReady"
    , to_ := "Capturing"
    , actions := ["StartTimer", "CaptureFrame"]
    , doc := some "Domains ready, start capturing" }
  , { from_ := "Preparing"
    , event := "CaptureError"
    , to_ := "Failed"
    , actions := []
    , doc := some "Domain enable failed" }

    -- From Capturing
  , { from_ := "Capturing"
    , event := "FrameCaptured"
    , to_ := "Capturing"
    , actions := ["CaptureFrame"]
    , doc := some "Frame captured, continue" }
  , { from_ := "Capturing"
    , event := "PauseCapture"
    , to_ := "Paused"
    , actions := ["StopTimer"]
    , doc := some "Pause capture" }
  , { from_ := "Capturing"
    , event := "StopCapture"
    , to_ := "Completed"
    , actions := ["StopTimer", "FinalizeCapture"]
    , doc := some "Stop capture early" }
  , { from_ := "Capturing"
    , event := "CaptureComplete"
    , to_ := "Completed"
    , actions := ["StopTimer", "FinalizeCapture"]
    , doc := some "Capture duration elapsed" }
  , { from_ := "Capturing"
    , event := "CaptureError"
    , to_ := "Failed"
    , actions := ["StopTimer"]
    , doc := some "Error during capture" }

    -- From Paused
  , { from_ := "Paused"
    , event := "ResumeCapture"
    , to_ := "Capturing"
    , actions := ["StartTimer"]
    , doc := some "Resume capture" }
  , { from_ := "Paused"
    , event := "StopCapture"
    , to_ := "Completed"
    , actions := ["FinalizeCapture"]
    , doc := some "Stop while paused" }
  ]
}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §4 EXPORT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- All CDP state machines for extraction -/
def cdpMachines : List StateMachine := [
  cdpSessionMachine
, cdpCaptureMachine
]

end Hydrogen.CDP.Extract
