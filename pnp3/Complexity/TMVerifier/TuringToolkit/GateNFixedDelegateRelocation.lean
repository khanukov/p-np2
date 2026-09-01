import Complexity.TMVerifier.TuringToolkit.GateOneFiveTagTraceSafety

/-!
# GN-3C1 fixed outer delegate and concrete shifted G1 run (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module defines one closed finite outer control.  Its delegated states carry
only the already-finite complete `G1M.state`; its five outer states are fixed.
There is no request, result, natural number, base, width, offset, index, or
runtime datum in the control.  The initial `idle` state is an inert sink.

Ordinary delegated states execute the exact `G1M.step` tuple.  The only two
interceptions are the complete canonical states `g1DoneQ false` and
`g1DoneQ true`, including both the unique phase and the complete `G1State`.
Malformed output modes, buffers, positions, and contexts therefore continue to
delegate.  The successful five-tag source trace cannot reach either intercepted
state at a proper prefix; that source fact is proved from the live
`outputDone -> accept` row, the stable accept sink, and the exact merged
output-done endpoint, without target delegation, relocation, or `G1RunSafe`.

The capstone overlays exactly `[0,W+5)` into a caller-supplied ambient target
tape, relocates the complete safe source trace, preserves every outside cell at
every prefix, and executes one further stationary target step into the fixed
result-indexed returned state.  It adds no parser, copier, installer, runtime
base discovery, commit sweep, multi-gate loop, clock-adequacy theorem, verdict,
or acceptance result.  The fixed outer `accept` and `reject` states are currently
unreachable placeholders: no transition row enters them.  Installing the
shifted word from a live GN tape remains the open E1 blocker.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Closed finite outer machine -/

/-- The complete one-phase source state at the canonical output-done boundary. -/
def g1DoneQ (b : Bool) : G1M.state :=
  ⟨(0 : Fin 1), g1OutputDoneState b⟩

/-- The complete one-phase source accept state. -/
def g1AcceptQ : G1M.state := ⟨(0 : Fin 1), g1AcceptState⟩

set_option synthInstance.maxSize 4096 in
/-- Fixed GN outer control.  The delegated payload is itself a closed finite
G1 control state; none of the constructors contains runtime geometry or data. -/
inductive GNState where
  | delegated (q : G1M.state)
  | returnedFalse
  | returnedTrue
  | idle
  | accept
  | reject
  deriving Fintype, DecidableEq

/-- Result-indexed fixed returned state. -/
def gnReturnedState : Bool → GNState
  | false => .returnedFalse
  | true => .returnedTrue

/-- The exact outer transition table.  Equality tests intercept only the two
complete canonical `g1DoneQ` values. -/
def gnTransition (_phase : Fin 1) (s : GNState) (scan : Bool) :
    Fin 1 × GNState × Bool × Move :=
  match s with
  | .delegated q =>
      if q = g1DoneQ false then (0, .returnedFalse, scan, .stay)
      else if q = g1DoneQ true then (0, .returnedTrue, scan, .stay)
      else
        let out := G1M.step q scan
        (0, .delegated out.fst, out.snd.fst, out.snd.snd)
  | .returnedFalse => (0, .returnedFalse, scan, .stay)
  | .returnedTrue => (0, .returnedTrue, scan, .stay)
  | .idle => (0, .idle, scan, .stay)
  | .accept => (0, .accept, scan, .stay)
  | .reject => (0, .reject, scan, .stay)

/-- Closed outer clock declaration.  No adequacy claim is made here. -/
def gnClock (N : Nat) : Nat := g1Clock N

/-- One fixed GN outer program.  Its real initial state is deliberately inert. -/
def gnCS : ConstStatePhasedProgram GNState where
  numPhases := 1
  startPhase := 0
  startState := .idle
  acceptPhase := 0
  acceptState := .accept
  transition := gnTransition
  timeBound := gnClock

/-- The fixed compiled outer machine. -/
abbrev GNM := gnCS.toPhased.toTM

/-- Embed one complete source state into the delegated outer region. -/
def gnEmbed (q : G1M.state) : GNM.state :=
  ⟨(0 : Fin 1), .delegated q⟩

/-- Complete target state reached when the shell intercepts a result. -/
def gnReturnedQ (b : Bool) : GNM.state :=
  ⟨(0 : Fin 1), gnReturnedState b⟩

@[simp] theorem gnTransition_idle (phase : Fin 1) (scan : Bool) :
    gnTransition phase .idle scan = (0, .idle, scan, .stay) := rfl

@[simp] theorem gnTransition_returnedFalse (phase : Fin 1) (scan : Bool) :
    gnTransition phase .returnedFalse scan =
      (0, .returnedFalse, scan, .stay) := rfl

@[simp] theorem gnTransition_returnedTrue (phase : Fin 1) (scan : Bool) :
    gnTransition phase .returnedTrue scan =
      (0, .returnedTrue, scan, .stay) := rfl

@[simp] theorem gnTransition_accept (phase : Fin 1) (scan : Bool) :
    gnTransition phase .accept scan = (0, .accept, scan, .stay) := rfl

@[simp] theorem gnTransition_reject (phase : Fin 1) (scan : Bool) :
    gnTransition phase .reject scan = (0, .reject, scan, .stay) := rfl

theorem gnTransition_delegate_ordinary (phase : Fin 1) (q : G1M.state)
    (scan : Bool) (hf : q ≠ g1DoneQ false) (ht : q ≠ g1DoneQ true) :
    gnTransition phase (.delegated q) scan =
      (0, .delegated (G1M.step q scan).fst,
        (G1M.step q scan).snd.fst, (G1M.step q scan).snd.snd) := by
  simp [gnTransition, hf, ht]

theorem gnTransition_intercept_false (phase : Fin 1) (scan : Bool) :
    gnTransition phase (.delegated (g1DoneQ false)) scan =
      (0, .returnedFalse, scan, .stay) := by
  simp [gnTransition]

theorem gnTransition_intercept_true (phase : Fin 1) (scan : Bool) :
    gnTransition phase (.delegated (g1DoneQ true)) scan =
      (0, .returnedTrue, scan, .stay) := by
  have hne : g1DoneQ true ≠ g1DoneQ false := by
    intro h
    exact G1Mode.noConfusion (congrArg (fun q : G1M.state => q.snd.mode) h)
  simp [gnTransition, hne]

theorem g1M_step_done (b scan : Bool) :
    G1M.step (g1DoneQ b) scan = (g1AcceptQ, scan, .stay) := by
  cases b <;> rfl

theorem g1M_step_accept (scan : Bool) :
    G1M.step g1AcceptQ scan = (g1AcceptQ, scan, .stay) := rfl

theorem gnM_step_embed_ordinary (q : G1M.state) (scan : Bool)
    (hf : q ≠ g1DoneQ false) (ht : q ≠ g1DoneQ true) :
    GNM.step (gnEmbed q) scan =
      (gnEmbed (G1M.step q scan).fst,
        (G1M.step q scan).snd.fst, (G1M.step q scan).snd.snd) := by
  simp [gnEmbed, gnCS, ConstStatePhasedProgram.toPhased,
    PhasedProgram.toTM, gnTransition, hf, ht]

theorem gnM_step_embed_done (b scan : Bool) :
    GNM.step (gnEmbed (g1DoneQ b)) scan =
      (gnReturnedQ b, scan, .stay) := by
  cases b
  · simp [gnEmbed, gnReturnedQ, gnReturnedState, gnCS,
      ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, gnTransition]
  · have hne : g1DoneQ true ≠ g1DoneQ false := by
      intro h
      exact G1Mode.noConfusion (congrArg (fun q : G1M.state => q.snd.mode) h)
    simp [gnEmbed, gnReturnedQ, gnReturnedState, gnCS,
      ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, gnTransition, hne]

/-! ## Source-only proper-prefix exclusion and concrete delegation -/

private theorem g1_runConfig_accept_state {W : Nat}
    (c : Configuration (M := G1M) W) (hstate : c.state = g1AcceptQ)
    (k : Nat) :
    (TM.runConfig (M := G1M) c k).state = g1AcceptQ := by
  induction k with
  | zero => simpa using hstate
  | succ k ih =>
      rw [runConfig_succ, stepConfig_state, ih, g1M_step_accept]

/-- A successful canonical source run reaches neither exact output-done state
at a proper prefix.  This proof uses only source transition rows, source accept
stability, and the merged exact source endpoint. -/
theorem g1CS_gate_done_no_early_outputDone (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    (j : Nat) (hj : j < g1GateDoneSteps r) (b : Bool) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) j).state ≠ g1DoneQ b := by
  intro hearly
  let c0 := G1M.initialConfig (g1Point (encodeG1 r))
  have hnext : (TM.runConfig (M := G1M) c0 (j + 1)).state = g1AcceptQ := by
    rw [runConfig_succ, stepConfig_state, hearly, g1M_step_done]
  have hsplit : g1GateDoneSteps r =
      (j + 1) + (g1GateDoneSteps r - (j + 1)) := by omega
  have haccept :
      (TM.runConfig (M := G1M) c0 (g1GateDoneSteps r)).state = g1AcceptQ := by
    rw [hsplit, runConfig_add]
    exact g1_runConfig_accept_state _ hnext _
  have hdone :
      (TM.runConfig (M := G1M) c0 (g1GateDoneSteps r)).state =
        g1DoneQ res := by
    rw [g1CS_gate_done_exact r hc res hs]
    rfl
  rw [hdone] at haccept
  have hm := congrArg (fun q : G1M.state => q.snd.mode) haccept
  cases res <;> exact G1Mode.noConfusion hm

/-- The concrete shell delegates the complete successful canonical five-tag
source prefix, and only that proper prefix. -/
theorem gn_g1_gate_done_delegates (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    G1RunDelegates GNM gnEmbed
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1GateDoneSteps r) := by
  intro j hj
  let c := TM.runConfig (M := G1M)
    (G1M.initialConfig (g1Point (encodeG1 r))) j
  have hf : c.state ≠ g1DoneQ false :=
    g1CS_gate_done_no_early_outputDone r hc res hs j hj false
  have ht : c.state ≠ g1DoneQ true :=
    g1CS_gate_done_no_early_outputDone r hc res hs j hj true
  unfold G1StepDelegates
  exact gnM_step_embed_ordinary c.state (c.tape c.head) hf ht

/-- Delegation genuinely fails at either intercepted output-done endpoint. -/
theorem gn_g1_outputDone_not_delegates {W : Nat}
    (c : Configuration (M := G1M) W) (b : Bool)
    (hstate : c.state = g1DoneQ b) :
    ¬ G1StepDelegates GNM gnEmbed c := by
  intro h
  unfold G1StepDelegates at h
  rw [hstate, gnM_step_embed_done, g1M_step_done] at h
  have hq := congrArg (fun out => out.fst.snd) h
  cases b <;> exact GNState.noConfusion hq

/-! ## Minimal endpoint geometry -/

/-- The real G1 initial head lies in its exact local relocation span. -/
theorem g1InitialConfig_head_lt_gnLocalSpan (r : G1Request) :
    ((G1M.initialConfig (g1Point (encodeG1 r))).head : Nat) <
      gnLocalSpan (encodeG1 r).length := by
  simp [gnLocalSpan]

/-- The exact output-done exit head lies in the same local span. -/
theorem g1OutputDoneConfig_head_lt_gnLocalSpan (r : G1Request) (res : Bool) :
    ((g1OutputDoneConfig r res).head : Nat) <
      gnLocalSpan (encodeG1 r).length := by
  simp [g1OutputExitHead, g1OutputBase_eq, gnLocalSpan, encodeG1_length]
  omega

/-! ## Concrete shifted source run and intercepted endpoint -/

/-- Overlay the exact `W+5` source footprint into a caller ambient tape. -/
def gnGateShiftConfig (r : G1Request) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    Configuration (M := GNM) N :=
  gnShiftConfig GNM base gnEmbed ambient
    (G1M.initialConfig (g1Point (encodeG1 r))) hroom
    (g1InitialConfig_head_lt_gnLocalSpan r)

private theorem gnShiftConfig_congr {W N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan W ≤ GNM.tapeLength N)
    {c d : Configuration (M := G1M) W} (hcd : c = d)
    (hc : (c.head : Nat) < gnLocalSpan W)
    (hd : (d.head : Nat) < gnLocalSpan W) :
    gnShiftConfig GNM base gnEmbed ambient c hroom hc =
      gnShiftConfig GNM base gnEmbed ambient d hroom hd := by
  subst d
  rfl

/-- Exact relocation conjugacy from the shifted real source initial
configuration through the complete successful output-done prefix. -/
theorem gnCS_gate_shift_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
        (g1GateDoneSteps r) =
      gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
        (g1OutputDoneConfig_head_lt_gnLocalSpan r res) := by
  unfold gnGateShiftConfig
  rw [gn_delegate_run_shift gnEmbed ambient _ hroom
    (g1InitialConfig_head_lt_gnLocalSpan r)
    (g1CS_gate_done_trace_safe r hc res hs).1
    (gn_g1_gate_done_delegates r hc res hs)]
  exact gnShiftConfig_congr ambient hroom
    (g1CS_gate_done_trace_safe r hc res hs).2 _ _

/-- Every target prefix through output-done preserves every cell outside the
shifted exact local footprint. -/
theorem gnCS_gate_shift_outside_every_prefix (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base j : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N)
    (hj : j ≤ g1GateDoneSteps r) (i : Fin (GNM.tapeLength N))
    (hout : (i : Nat) < base ∨
      base + gnLocalSpan (encodeG1 r).length ≤ (i : Nat)) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom) j).tape i =
      ambient i := by
  unfold gnGateShiftConfig
  exact gn_delegate_run_shift_outside_prefix gnEmbed ambient _ hroom
    (g1InitialConfig_head_lt_gnLocalSpan r)
    (g1CS_gate_done_trace_safe r hc res hs).1
    (gn_g1_gate_done_delegates r hc res hs) hj i hout

/-- Replace only the control state of a target configuration by the fixed
result-indexed returned state. -/
def gnReturnConfig {N : Nat} (res : Bool) (c : Configuration (M := GNM) N) :
    Configuration (M := GNM) N :=
  { c with state := gnReturnedQ res }

private theorem gnCS_step_outputDone {N : Nat}
    (c : Configuration (M := GNM) N) (res : Bool)
    (hstate : c.state = gnEmbed (g1DoneQ res)) :
    TM.runConfig (M := GNM) c 1 = gnReturnConfig res c := by
  rw [runConfig_one]
  apply Configuration.ext_of_components
  · rw [stepConfig_state, hstate, gnM_step_embed_done]
    rfl
  · rw [stepConfig_head, hstate, gnM_step_embed_done]
    rfl
  · rw [stepConfig_tape, hstate, gnM_step_embed_done]
    funext i
    by_cases hi : i = c.head
    · subst i
      exact Configuration.write_self c c.head (c.tape c.head)
    · exact Configuration.write_other c hi (c.tape c.head)

/-- One target step intercepts an exact shifted output-done source state.  It
is stationary and writes back the scanned bit, hence preserves head and tape. -/
theorem gnCS_step_shifted_outputDone (r : G1Request) (res : Bool)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM)
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) 1 =
      gnReturnConfig res
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) := by
  apply gnCS_step_outputDone
  rfl

/-- Concrete relocation capstone: the safe shifted G1 run reaches exact
shifted output-done, and the one additional target row returns its result. -/
theorem gnCS_gate_shift_intercept_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
        (g1GateDoneSteps r + 1) =
      gnReturnConfig res
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) := by
  rw [runConfig_add, gnCS_gate_shift_exact r hc res hs ambient hroom]
  exact gnCS_step_shifted_outputDone r res ambient hroom

/-- Exact result-indexed target state after the intercepted shifted run. -/
theorem gnCS_gate_shift_intercept_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)).state = gnReturnedQ res := by
  rw [gnCS_gate_shift_intercept_exact r hc res hs ambient hroom]
  rfl

/-- Exact fixed outer mode after the intercepted shifted run. -/
theorem gnCS_gate_shift_intercept_mode (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)).state.snd = gnReturnedState res := by
  rw [gnCS_gate_shift_intercept_exact r hc res hs ambient hroom]
  rfl

/-- The same capstone exposed at the outer-mode level, with exact unchanged
head and tape relative to the shifted source endpoint. -/
theorem gnCS_gate_shift_intercept_structure (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    let out := TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)
    let shifted := gnShiftConfig GNM base gnEmbed ambient
      (g1OutputDoneConfig r res) hroom
      (g1OutputDoneConfig_head_lt_gnLocalSpan r res)
    out.state.snd = gnReturnedState res ∧
      out.head = shifted.head ∧ out.tape = shifted.tape := by
  dsimp only
  rw [gnCS_gate_shift_intercept_exact r hc res hs ambient hroom]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Concrete schedule probes -/

namespace GNFixedDelegateProbes

open G1AResultProbes

/-- Literal true probe: `N=64`, `base=7`, all-true ambient, `229+1=230`. -/
theorem literal_input_true_shifted_intercept :
    TM.runConfig (M := GNM)
      (gnGateShiftConfig (N := 64) (base := 7) reqInputT (fun _ => true) (by decide))
      230 =
    gnReturnConfig true
      (gnShiftConfig GNM 7 gnEmbed (fun _ => true)
        (g1OutputDoneConfig reqInputT true) (by decide)
        (g1OutputDoneConfig_head_lt_gnLocalSpan reqInputT true)) := by
  have h := gnCS_gate_shift_intercept_exact reqInputT
    literal_canonical.1 true literal_specs.1
    (N := 64) (base := 7) (fun _ => true) (by decide)
  rw [G1FiveTagTraceProbes.literal_done_steps.1] at h
  simpa using h

/-- Literal false probe: `N=64`, `base=7`, all-true ambient, `151+1=152`. -/
theorem literal_const_false_shifted_intercept :
    TM.runConfig (M := GNM)
      (gnGateShiftConfig (N := 64) (base := 7) reqConstF (fun _ => true) (by decide))
      152 =
    gnReturnConfig false
      (gnShiftConfig GNM 7 gnEmbed (fun _ => true)
        (g1OutputDoneConfig reqConstF false) (by decide)
        (g1OutputDoneConfig_head_lt_gnLocalSpan reqConstF false)) := by
  have h := gnCS_gate_shift_intercept_exact reqConstF
    literal_canonical.2.2.2.2.1 false literal_specs.2.2.2.2.1
    (N := 64) (base := 7) (fun _ => true) (by decide)
  rw [G1FiveTagTraceProbes.literal_done_steps.2.1] at h
  simpa using h

end GNFixedDelegateProbes

end Pnp3.Internal.PsubsetPpoly.TM
