import Complexity.TMVerifier.TuringToolkit.GateNRelocation
import Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept

/-!
# GN-3B1: canonical G1 output-done boundary (2026-08-30)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module stops the canonical one-gate execution at the result-indexed
`g1OutputDoneConfig`, exactly one step before the literal accept handoff.  The
result is an index of the theorem and of the already-existing output-done
control state; it is not stored in a new annotation.

The generic prefix lemmas below record the machine-independent one-cell head
growth bound and its strict `W + 5` right-footprint consequence.  They do not
claim the still-separate, schedule-specific full canonical trace theorem.  In
particular no strong trace-safety assumption is introduced here.

No GN machine, controller, copier, clock, or acceptance construction is added,
and the literal accept state is not mapped into a future GN control.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Exact output-done schedule -/

/-- Exact canonical schedule stopping one transition before literal accept. -/
def g1GateDoneSteps (r : G1Request) : Nat :=
  g1GateResultSteps r + (1 + g1OutputKernelSteps r)

theorem g1GateDoneSteps_provenance (r : G1Request) :
    g1GateDoneSteps r =
      g1GateResultSteps r + 1 + g1OutputKernelSteps r := by
  rw [g1GateDoneSteps]
  omega

theorem g1GateAcceptSteps_eq_done_add_one (r : G1Request) :
    g1GateAcceptSteps r = g1GateDoneSteps r + 1 := by
  rw [g1GateAcceptSteps, g1GateDoneSteps]
  omega

theorem g1GateDoneSteps_closed (r : G1Request) :
    g1GateDoneSteps r = g1GateResultSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps, g1OutputKernelSteps]
  omega

theorem g1GateDoneSteps_const (r : G1Request) (ht : r.tag = .const) :
    g1GateDoneSteps r = g1ConstActivatedSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_const r ht]

theorem g1GateDoneSteps_input (r : G1Request) (ht : r.tag = .input) :
    g1GateDoneSteps r = g1UACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_unary r (Or.inl ht)]

theorem g1GateDoneSteps_not (r : G1Request) (ht : r.tag = .not) :
    g1GateDoneSteps r = g1UACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_unary r (Or.inr ht)]

theorem g1GateDoneSteps_and (r : G1Request) (ht : r.tag = .and) :
    g1GateDoneSteps r = g1BACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_binary r (Or.inl ht)]

theorem g1GateDoneSteps_or (r : G1Request) (ht : r.tag = .or) :
    g1GateDoneSteps r = g1BACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_binary r (Or.inr ht)]

theorem g1GateDoneSteps_le_clock (r : G1Request) :
    g1GateDoneSteps r ≤ g1Clock (encodeG1 r).length := by
  have haccept := g1GateAcceptSteps_le_clock r
  rw [g1GateAcceptSteps_eq_done_add_one] at haccept
  omega

/-- Combine door plus the exact S10a kernel, stopping at output-done. -/
theorem g1CS_output_done_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1CombineConfig r res)
        (1 + g1OutputKernelSteps r) = g1OutputDoneConfig r res := by
  rw [runConfig_add, g1CS_step_combine_output, g1CS_output_kernel_exact]

/-- Exact real-initial canonical endpoint, one step before literal accept. -/
theorem g1CS_gate_done_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) = g1OutputDoneConfig r res := by
  rw [g1GateDoneSteps, runConfig_add, g1CS_gate_result_exact r hc res hs]
  exact g1CS_output_done_exact r res

theorem g1CS_gate_done_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).state.snd = g1OutputDoneState res := by
  rw [g1CS_gate_done_exact r hc res hs]
  rfl

theorem g1CS_gate_done_mode (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).state.snd.mode =
        if res then .outputDoneTrue else .outputDoneFalse := by
  rw [g1CS_gate_done_state r hc res hs]
  cases res <;> rfl

theorem g1CS_gate_done_context (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).state.snd.ctx = g1Ctx0 := by
  rw [g1CS_gate_done_state r hc res hs]
  cases res <;> rfl

theorem g1CS_gate_done_head (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).head : Nat) = g1OutputExitHead r := by
  rw [g1CS_gate_done_exact r hc res hs]
  rfl

theorem g1CS_gate_done_tape (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape =
        writeCell (g1OutputPosition r) res
          (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_gate_done_exact r hc res hs, g1OutputDoneConfig_tape,
    g1OutputTape_eq_writeCell]

theorem g1CS_gate_done_frames (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape =
        g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) := by
  rw [g1CS_gate_done_exact r hc res hs]
  rfl

theorem g1CS_gate_done_output (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape i = res := by
  rw [g1CS_gate_done_tape r hc res hs]
  simp [writeCell, hi]

theorem g1CS_gate_done_off (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) ≠ g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape i =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape i := by
  rw [g1CS_gate_done_tape r hc res hs]
  simp [writeCell, hi]

/-! ## Generic proper-prefix head growth and strict right room -/

theorem g1_runConfig_head_le_start_add {W k : Nat}
    (c : Configuration (M := G1M) W) :
    ((TM.runConfig (M := G1M) c k).head : Nat) ≤ (c.head : Nat) + k := by
  exact runConfig_head_val_le c k

theorem g1_initial_prefix_head_le_steps (r : G1Request) (k : Nat) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r))) k).head :
      Nat) ≤ k := by
  simpa using g1_runConfig_head_le_start_add
    (c := G1M.initialConfig (g1Point (encodeG1 r))) (k := k)

/-- A generic strict-right-footprint reduction at the exact `span - 1`
boundary.  It separates the natural head bound from the only boundary control
case that a complete schedule proof must discharge. -/
theorem g1_local_right_safe_of_head_le_span_pred {W : Nat}
    (c : Configuration (M := G1M) W)
    (hhead : (c.head : Nat) + 1 ≤ gnLocalSpan W)
    (hboundary : (c.head : Nat) + 1 = gnLocalSpan W →
      (G1M.step c.state (c.tape c.head)).snd.snd ≠ Move.right) :
    (c.head : Nat) < gnLocalSpan W ∧
      (((G1M.step c.state (c.tape c.head)).snd.snd = Move.right) →
        (c.head : Nat) + 1 < gnLocalSpan W) := by
  constructor
  · omega
  · intro hright
    by_contra hnot
    have heq : (c.head : Nat) + 1 = gnLocalSpan W := by omega
    exact hboundary heq hright

/-- Generic early-prefix right safety.  The schedule-specific extension from
this early prefix to all `k < g1GateDoneSteps r` is deliberately not inferred
from the output-done endpoint. -/
theorem g1_initial_prefix_right_safe_of_steps_lt_span (r : G1Request) (k : Nat)
    (hk : k + 1 < gnLocalSpan (encodeG1 r).length) :
    let c := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) k
    (c.head : Nat) < gnLocalSpan (encodeG1 r).length ∧
      (((G1M.step c.state (c.tape c.head)).snd.snd = Move.right) →
        (c.head : Nat) + 1 < gnLocalSpan (encodeG1 r).length) := by
  dsimp only
  have hhead := g1_initial_prefix_head_le_steps r k
  constructor <;> omega

/-! ## Exact inspection of the `W + 4` validation boundary -/

theorem g1CS_validation_reaches_span_pred (r : G1Request) (hc : r.Canonical) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4)).head : Nat) + 1 =
        gnLocalSpan (encodeG1 r).length := by
  rw [g1CS_validate_encoded_exact r hc]
  simp [gnLocalSpan]

theorem g1CS_validation_span_pred_moves_left (r : G1Request)
    (hc : r.Canonical) :
    (G1M.step
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).state
      ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).tape
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).head)).snd.snd = Move.left := by
  rw [g1CS_validate_encoded_exact r hc]
  rfl

/-- The maximum-head validation configuration is locally safe: it is inside
`W + 5`, and its actual next row is left, not right. -/
theorem g1CS_validation_span_pred_local_safe (r : G1Request)
    (hc : r.Canonical) :
    G1LocalStepSafe
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)) := by
  have hhead := g1CS_validation_reaches_span_pred r hc
  have hleft := g1CS_validation_span_pred_moves_left r hc
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    rw [g1CS_validate_encoded_exact r hc]
    simp
  · intro hright
    rw [hleft] at hright
    exact Move.noConfusion hright

/-! ## Nonvacuous literal false/true probes -/

namespace G1TraceSafetyProbes

open G1AResultProbes

theorem literal_done_steps :
    g1GateDoneSteps reqConstF = 151 ∧ g1GateDoneSteps reqConstT = 171 := by
  decide

theorem literal_false_done :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 151 =
      g1OutputDoneConfig reqConstF false := by
  rw [← literal_done_steps.1]
  exact g1CS_gate_done_exact reqConstF literal_canonical.2.2.2.2.1 false
    literal_specs.2.2.2.2.1

theorem literal_true_done :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 171 =
      g1OutputDoneConfig reqConstT true := by
  rw [← literal_done_steps.2]
  exact g1CS_gate_done_exact reqConstT literal_canonical.2.2.2.2.2 true
    literal_specs.2.2.2.2.2

/-- False literal at the actually attained maximum validation head `W+4`. -/
theorem literal_false_span_pred_safe :
    G1LocalStepSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstF)))
        ((encodeG1 reqConstF).length + 4)) :=
  g1CS_validation_span_pred_local_safe reqConstF
    literal_canonical.2.2.2.2.1

/-- True literal at the actually attained maximum validation head `W+4`. -/
theorem literal_true_span_pred_safe :
    G1LocalStepSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstT)))
        ((encodeG1 reqConstT).length + 4)) :=
  g1CS_validation_span_pred_local_safe reqConstT
    literal_canonical.2.2.2.2.2

end G1TraceSafetyProbes

end Pnp3.Internal.PsubsetPpoly.TM
