import Complexity.TMVerifier.TuringToolkit.GateOneOutputDoneTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneUnaryARepairTraceSafety

/-!
# GN-3B2fC complete five-tag G1 output-done trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module closes successful real-initial `G1RunSafe` for all five canonical
G1 request tags.  Unary requests compose the merged GN-3B2fB `aRepairDone`
endpoint with the tag-generic result/output suffix.  Constants compose the
merged GN-3B2fA activation-to-combine endpoint with the same output suffix.
Binary requests reuse the merged GN-3B2e4 theorem unchanged.

Every route stops exactly at `g1OutputDoneConfig r res`.  In particular, this
module adds no output-done-to-accept step, `ShiftRunSafe`, GN controller,
multigate, clock, verdict, or P-vs-NP mainline claim.  Successful five-tag
full-prefix G1 safety is closed at output-done; relocation is the next blocker.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Unary and constant schedule-pinned compositions -/

/-- Exact unary decomposition: repaired pass A, three result rows, the combine
door, and the output kernel. -/
theorem g1GateDoneSteps_unary_trace_eq (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1GateDoneSteps r =
      g1AUnaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r := by
  rw [g1GateDoneSteps, g1GateResultSteps_unary r ht, g1UACombineSteps]
  omega

/-- Successful canonical input/not requests are safe from the real initial
configuration through the exact result-indexed output-done boundary. -/
theorem g1CS_gate_done_unary_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (res : Bool)
    (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res := by
  rcases g1CS_aRepair_unary_spec_trace_safe r hc ht res hs with
    ⟨hrepair, selectedA, hrepairExact, hres⟩
  have hsuffix0 := g1CS_aRepairDone_output_trace_safe r false selectedA
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r))
      (3 + (1 + g1OutputKernelSteps r)) :=
    G1RunSafe.transport hrepairExact.symm hsuffix0.1
  rw [g1GateDoneSteps_unary_trace_eq r ht]
  have hcount : g1AUnaryRepairSteps r +
      (3 + (1 + g1OutputKernelSteps r)) =
      g1AUnaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r := by omega
  refine ⟨by
    rw [← hcount]
    exact G1RunSafe.add hrepair hsuffix, ?_⟩
  rw [← hcount, runConfig_add, hrepairExact, hsuffix0.2, hres]

/-- Exact constant decomposition: the merged activation-to-combine prefix,
the combine door, and the output kernel. -/
theorem g1GateDoneSteps_const_trace_eq (r : G1Request)
    (ht : r.tag = .const) :
    g1GateDoneSteps r =
      g1ConstActivatedSteps r + 1 + g1OutputKernelSteps r := by
  rw [g1GateDoneSteps, g1GateResultSteps_const r ht]
  omega

/-- Successful canonical constants are safe from the real initial
configuration through output-done.  The result follows from `spec`; no values
premise is needed. -/
theorem g1CS_gate_done_const_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (res : Bool) (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res := by
  have hactivate := g1CS_activate_const_trace_safe r hc ht res hs
  have hsuffix0 := g1CS_output_done_trace_safe r res
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstActivatedSteps r))
      (1 + g1OutputKernelSteps r) :=
    G1RunSafe.transport hactivate.2.symm hsuffix0.1
  rw [g1GateDoneSteps_const_trace_eq r ht]
  have hcount : g1ConstActivatedSteps r +
      (1 + g1OutputKernelSteps r) =
      g1ConstActivatedSteps r + 1 + g1OutputKernelSteps r := by omega
  refine ⟨by
    rw [← hcount]
    exact G1RunSafe.add hactivate.1 hsuffix, ?_⟩
  rw [← hcount, runConfig_add, hactivate.2, hsuffix0.2]

/-! ## Common five-tag capstone and endpoint structure -/

/-- Successful canonical requests of any of the exact five tags have a safe
full G1 prefix and reach the exact output-done boundary. -/
theorem g1CS_gate_done_five_tag_trace_safe (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res := by
  rcases htag : r.tag with h | h | h | h | h
  · exact ⟨(g1CS_gate_done_unary_trace_safe r hc (Or.inl htag) res hs).1,
      g1CS_gate_done_exact r hc res hs⟩
  · exact ⟨(g1CS_gate_done_const_trace_safe r hc htag res hs).1,
      g1CS_gate_done_exact r hc res hs⟩
  · exact ⟨(g1CS_gate_done_unary_trace_safe r hc (Or.inr htag) res hs).1,
      g1CS_gate_done_exact r hc res hs⟩
  · exact ⟨(g1CS_gate_done_binary_trace_safe r hc (Or.inl htag) res hs).1,
      g1CS_gate_done_exact r hc res hs⟩
  · exact ⟨(g1CS_gate_done_binary_trace_safe r hc (Or.inr htag) res hs).1,
      g1CS_gate_done_exact r hc res hs⟩

/-- Common five-tag output-done structure after rewriting by the capstone:
the designated cell contains the result, all other cells are unchanged, and
head/state/mode/context are exact and distinct from reject and OOB. -/
theorem g1CS_gate_done_five_tag_structure (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    let out := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1GateDoneSteps r)
    out.tape = writeCell (g1OutputPosition r) res
        (G1M.initialConfig (g1Point (encodeG1 r))).tape ∧
      (out.head : Nat) = g1OutputExitHead r ∧
      out.state.snd = g1OutputDoneState res ∧
      out.state.snd.mode = (if res then .outputDoneTrue else .outputDoneFalse) ∧
      out.state.snd.ctx = g1Ctx0 ∧
      out.state.snd ≠ g1RejectState ∧
      (∀ ctx, out.state.snd ≠ g1OOBState ctx) ∧
      (∀ i : Fin (G1M.tapeLength (encodeG1 r).length),
        (i : Nat) = g1OutputPosition r -> out.tape i = res) ∧
      (∀ i : Fin (G1M.tapeLength (encodeG1 r).length),
        (i : Nat) ≠ g1OutputPosition r ->
          out.tape i =
            (G1M.initialConfig (g1Point (encodeG1 r))).tape i) := by
  dsimp only
  rw [(g1CS_gate_done_five_tag_trace_safe r hc res hs).2]
  refine ⟨g1OutputTape_eq_writeCell r res, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · cases res <;> rfl
  · intro h
    cases res <;> exact G1Mode.noConfusion (congrArg G1State.mode h)
  · intro ctx h
    cases res <;> exact G1Mode.noConfusion (congrArg G1State.mode h)
  · intro i hi
    exact g1OutputTape_at r res i hi
  · intro i hi
    exact g1OutputTape_off r res i hi

/-! ## Full existing literal matrix -/

namespace G1FiveTagTraceProbes

open G1PassATraceProbes
open G1AResultProbes

/-- Exact output-done totals for the six existing five-tag requests and the
existing larger binary request. -/
theorem literal_done_steps :
    g1GateDoneSteps reqInputT = 229 ∧
      g1GateDoneSteps reqConstF = 151 ∧
      g1GateDoneSteps reqConstT = 171 ∧
      g1GateDoneSteps reqNotF = 285 ∧
      g1GateDoneSteps reqAndF = 484 ∧
      g1GateDoneSteps reqOrT = 512 ∧
      g1GateDoneSteps reqA = 606 := by
  decide

theorem literal_input_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 229 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 229 =
        g1OutputDoneConfig reqInputT true := by
  have h := g1CS_gate_done_five_tag_trace_safe reqInputT
    literal_canonical.1 true literal_specs.1
  rw [literal_done_steps.1] at h
  exact h

theorem literal_const_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 151 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 151 =
        g1OutputDoneConfig reqConstF false := by
  have h := g1CS_gate_done_five_tag_trace_safe reqConstF
    literal_canonical.2.2.2.2.1 false literal_specs.2.2.2.2.1
  rw [literal_done_steps.2.1] at h
  exact h

theorem literal_const_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 171 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 171 =
        g1OutputDoneConfig reqConstT true := by
  have h := g1CS_gate_done_five_tag_trace_safe reqConstT
    literal_canonical.2.2.2.2.2 true literal_specs.2.2.2.2.2
  rw [literal_done_steps.2.2.1] at h
  exact h

theorem literal_not_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 285 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 285 =
        g1OutputDoneConfig reqNotF false := by
  have h := g1CS_gate_done_five_tag_trace_safe reqNotF
    literal_canonical.2.1 false literal_specs.2.1
  rw [literal_done_steps.2.2.2.1] at h
  exact h

theorem literal_and_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 =
        g1OutputDoneConfig reqAndF false := by
  have h := g1CS_gate_done_five_tag_trace_safe reqAndF
    literal_canonical.2.2.1 false literal_specs.2.2.1
  rw [literal_done_steps.2.2.2.2.1] at h
  exact h

theorem literal_or_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 =
        g1OutputDoneConfig reqOrT true := by
  have h := g1CS_gate_done_five_tag_trace_safe reqOrT
    literal_canonical.2.2.2.1 true literal_specs.2.2.2.1
  rw [literal_done_steps.2.2.2.2.2.1] at h
  exact h

theorem literal_binary_a_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 =
        g1OutputDoneConfig reqA true := by
  have h := g1CS_gate_done_five_tag_trace_safe reqA (by decide) true (by decide)
  rw [literal_done_steps.2.2.2.2.2.2] at h
  exact h

end G1FiveTagTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
