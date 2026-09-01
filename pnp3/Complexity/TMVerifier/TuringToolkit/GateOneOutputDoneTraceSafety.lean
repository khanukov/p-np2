import Complexity.TMVerifier.TuringToolkit.GateOneARepairTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneTraceSafety

/-!
# GN-3B2e4 binary result/combine/output-done trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module composes the merged e3 binary `aRepairDone` capstone with the
three stationary result rows, the stationary `combineStart` door, and the
complete result-indexed output kernel.  The output scan reuses the generic
strict forward-scanner safety theorem; its turn and literal four-cell writer
reuse the local-margin theorem.

The endpoint is exactly `g1OutputDoneConfig r res`.  Thus the designated
output cell, every off-target cell, head, mode, context, and false/true result
index are inherited from that existing boundary.  The run stops before the
separate `outputDone -> accept` row.  Only successful canonical binary requests
are composed from the real initial configuration: no unary, constant,
five-tag, shifted, controller, clock, verdict, or acceptance theorem is added.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1OutputDone_runSafe_one {W : Nat}
    (c : Configuration (M := G1M) W) (h : G1LocalStepSafe c) :
    G1RunSafe c 1 := by
  simpa using G1RunSafe.succ (G1RunSafe.empty c) h

private theorem g1Aligned_stay_local_safe {W h : Nat}
    (hh : h < G1M.tapeLength W) (tape : Fin (G1M.tapeLength W) -> Bool)
    (mode mode' : G1Mode) (position position' : G1FramePosition)
    (b0 b1 b2 b0' b1' b2' : Bool) (ctx ctx' : G1Ctx)
    (hspan : h < gnLocalSpan W)
    (hstep : g1Transition (0 : Fin 1)
      (g1State mode position b0 b1 b2 ctx) (tape ⟨h, hh⟩) =
      (0, g1State mode' position' b0' b1' b2' ctx',
        tape ⟨h, hh⟩, Move.stay)) :
    G1LocalStepSafe
      (g1AlignedConfig W h hh tape mode position b0 b1 b2 ctx) := by
  simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
    g1AlignedConfig_state, g1AlignedConfig_tape]
  refine ⟨hspan, ?_, ?_⟩
  · intro hleft
    change (g1Transition (0 : Fin 1) (g1State mode position b0 b1 b2 ctx)
      (tape ⟨h, hh⟩)).snd.snd.snd = Move.left at hleft
    rw [hstep] at hleft
    exact Move.noConfusion hleft
  · intro hright
    change (g1Transition (0 : Fin 1) (g1State mode position b0 b1 b2 ctx)
      (tape ⟨h, hh⟩)).snd.snd.snd = Move.right at hright
    rw [hstep] at hright
    exact Move.noConfusion hright

/-! ## Three stationary result rows -/

/-- All three genuine rows from `aRepairDone` through `readAStart` are locally
safe, including at head zero, where each row is stationary. -/
theorem g1CS_aRepairDone_result_runSafe (r : G1Request) (b v : Bool) :
    G1RunSafe (g1ARepairDoneConfig r b v) 3 := by
  let W := (encodeG1 r).length
  let hh := g1_route_lt_tapeLength r 0 (by omega)
  let tape := g1ListTape (n := W)
    ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits)
  let ctx := g1AWalkCtx r b v
  let c0 := g1AlignedConfig W 0 hh tape .aRepairDone .p0
    false false false ctx
  let c1 := g1AlignedConfig W 0 hh tape .aResultStart .p0
    false false false ctx
  let c2 := g1AlignedConfig W 0 hh tape .readAStart .p0
    false false false (g1ResultCtx ((g1Residual r.tag b).apply v))
  have h0 : G1LocalStepSafe c0 := by
    apply g1Aligned_stay_local_safe hh tape .aRepairDone .aResultStart
      .p0 .p0 false false false false false false ctx ctx
    · simp [gnLocalSpan]
    · exact g1Transition_aRepairDone_result 0 .p0 false false false _ ctx
  have h1 : G1LocalStepSafe c1 := by
    apply g1Aligned_stay_local_safe hh tape .aResultStart .readAStart
      .p0 .p0 false false false false false false ctx
      (g1ResultCtx ((g1Residual r.tag b).apply v))
    · simp [gnLocalSpan]
    · simpa [ctx] using
        g1Transition_aResultStart_apply 0 .p0 false false false _ ctx
  have h2 : G1LocalStepSafe c2 := by
    apply g1Aligned_stay_local_safe hh tape .readAStart .combineStart
      .p0 .p0 false false false false false false
      (g1ResultCtx ((g1Residual r.tag b).apply v))
      (g1ResultCtx ((g1Residual r.tag b).apply v))
    · simp [gnLocalSpan]
    · exact g1Transition_readAStart_result 0 .p0 false false false _ _ rfl
  have hs0 : TM.runConfig (M := G1M) c0 1 = c1 := by
    exact g1CS_step_aRepairDone_result W 0 hh tape ctx
  have hs1 : TM.runConfig (M := G1M) c1 1 = c2 := by
    simpa [ctx] using g1CS_step_aResultStart_apply W 0 hh tape ctx
  have hr1 : TM.runConfig (M := G1M) c0 1 = c1 := hs0
  have hr2 : TM.runConfig (M := G1M) c0 2 = c2 := by
    rw [show (2 : Nat) = 1 + 1 by omega, runConfig_add, hs0, hs1]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · change G1LocalStepSafe c0
    exact h0
  · change G1LocalStepSafe (TM.runConfig (M := G1M) c0 1)
    rw [hr1]
    exact h1
  · change G1LocalStepSafe (TM.runConfig (M := G1M) c0 2)
    rw [hr2]
    exact h2

/-- Exact result handoff paired with the three-row safety proof. -/
theorem g1CS_aRepairDone_combine_trace_safe (r : G1Request) (b v : Bool) :
    G1RunSafe (g1ARepairDoneConfig r b v) 3 ∧
      TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v) 3 =
        g1CombineConfig r ((g1Residual r.tag b).apply v) :=
  ⟨g1CS_aRepairDone_result_runSafe r b v,
    g1CS_aRepairDone_combine_exact r b v⟩

/-! ## Combine door and complete output kernel -/

/-- The head-zero `combineStart` door is one stationary safe step. -/
theorem g1CS_combine_entry_runSafe (r : G1Request) (res : Bool) :
    G1RunSafe (g1CombineConfig r res) 1 := by
  apply g1OutputDone_runSafe_one
  apply g1Aligned_stay_local_safe
    (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .combineStart .outSeek .p0 .p0 false false false false false false
    (g1ResultCtx res) (g1ResultCtx res)
  · simp [gnLocalSpan]
  · exact g1Transition_combineStart_output 0 .p0 false false false _ _

/-- The strict output route, including its unique `output false` target, is
safe for the exact four-cells-per-frame scanner schedule. -/
theorem g1CS_output_scan_runSafe (r : G1Request) (res : Bool) :
    G1RunSafe (g1OutputStartConfig r res)
      (4 * ((g1PrefixFrames r).length + 1)) := by
  have hfix : ∀ f ∈ g1PrefixFrames r,
      g1Advance .outSeek f = .outSeek :=
    fun f hf => g1Advance_outSeek_of_skip (g1PrefixFrames_outSkip r f hf)
  have hpath : G1ValidPath .outSeek
      (g1PrefixFrames r ++ [G1Frame.output false]) :=
    g1ValidPath_fix (mode := .outSeek) trivial [G1Frame.output false]
      ⟨trivial, by decide, trivial⟩ (g1PrefixFrames r) hfix
  have hs := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) []
    (g1PrefixFrames r ++ [G1Frame.output false])
    [G1Frame.finish, G1Frame.blank] .outSeek (g1ResultCtx res) hpath (by
      simp [gnLocalSpan, encodeG1_length]
      omega)
  have hframes : [] ++ (g1PrefixFrames r ++ [G1Frame.output false]) ++
      [G1Frame.finish, G1Frame.blank] = g1OutputFrames r false := by
    simp [g1OutputFrames, List.append_assoc]
  rw [hframes, g1OutputTape_false] at hs
  simpa [g1OutputStartConfig] using hs

/-- The tape-preserving turn and four literal writer rows are safe through,
but not beyond, the exact result-indexed output-done endpoint. -/
theorem g1CS_output_turn_write_runSafe (r : G1Request) (res : Bool) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length (g1OutputBase r + 4)
        (g1OutputBase_safe r)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .outTurn .p0 false false false (g1ResultCtx res)) 5 := by
  apply g1RunSafe_of_margins
  · simp only [g1AlignedConfig_head_val]
    simp [g1OutputBase_eq]
    omega
  · simp only [g1AlignedConfig_head_val]
    simp [g1OutputBase_eq, gnLocalSpan, encodeG1_length]
    omega

/-- Complete caller-supplied output-kernel safety and exact output-done
endpoint, with the scanner/writer decomposition visible in the proof. -/
theorem g1CS_output_kernel_trace_safe (r : G1Request) (res : Bool) :
    G1RunSafe (g1OutputStartConfig r res) (g1OutputKernelSteps r) ∧
      TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (g1OutputKernelSteps r) = g1OutputDoneConfig r res := by
  have hscan := g1CS_output_scan_runSafe r res
  have htail0 := g1CS_output_turn_write_runSafe r res
  have htail : G1RunSafe
      (TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (4 * ((g1PrefixFrames r).length + 1))) 5 :=
    G1RunSafe.transport (g1CS_output_scan_exact r res).symm htail0
  refine ⟨?_, g1CS_output_kernel_exact r res⟩
  rw [g1OutputKernelSteps_eq]
  exact G1RunSafe.add hscan htail

/-- Stationary combine entry plus the complete output kernel, stopping exactly
at output-done and excluding its successor. -/
theorem g1CS_output_done_trace_safe (r : G1Request) (res : Bool) :
    G1RunSafe (g1CombineConfig r res) (1 + g1OutputKernelSteps r) ∧
      TM.runConfig (M := G1M) (g1CombineConfig r res)
        (1 + g1OutputKernelSteps r) = g1OutputDoneConfig r res := by
  have hentry := g1CS_combine_entry_runSafe r res
  have hkernel0 := (g1CS_output_kernel_trace_safe r res).1
  have hkernel : G1RunSafe
      (TM.runConfig (M := G1M) (g1CombineConfig r res) 1)
      (g1OutputKernelSteps r) :=
    G1RunSafe.transport (g1CS_step_combine_output r res).symm hkernel0
  exact ⟨G1RunSafe.add hentry hkernel, g1CS_output_done_exact r res⟩

/-! ## Binary real-initial composition -/

/-- Kernel-visible binary schedule: merged e3 repair, three result rows, the
combine door, and the output kernel. -/
theorem g1GateDoneSteps_binary_trace_eq (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1GateDoneSteps r =
      g1ABinaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r := by
  rw [g1GateDoneSteps, g1GateResultSteps_binary r ht, g1BACombineSteps]
  omega

/-- The result/output suffix from the exact e3 endpoint is safe and reaches
the result computed by the latched residual and operand-A value. -/
theorem g1CS_aRepairDone_output_trace_safe (r : G1Request) (b v : Bool) :
    let res := (g1Residual r.tag b).apply v
    G1RunSafe (g1ARepairDoneConfig r b v)
        (3 + (1 + g1OutputKernelSteps r)) ∧
      TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v)
          (3 + (1 + g1OutputKernelSteps r)) =
        g1OutputDoneConfig r res := by
  dsimp only
  have hresult := g1CS_aRepairDone_combine_trace_safe r b v
  have hout0 := g1CS_output_done_trace_safe r
    ((g1Residual r.tag b).apply v)
  have hout : G1RunSafe
      (TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v) 3)
      (1 + g1OutputKernelSteps r) :=
    G1RunSafe.transport hresult.2.symm hout0.1
  exact ⟨G1RunSafe.add hresult.1 hout, by
    rw [runConfig_add, hresult.2, hout0.2]⟩

set_option maxHeartbeats 800000 in
/-- Successful canonical binary requests have a fully safe real-initial trace
through the exact result-indexed output-done boundary. -/
theorem g1CS_gate_done_binary_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (res : Bool)
    (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res := by
  obtain ⟨a, b, ha, hb⟩ := g1Spec_operands_binary ht hs
  obtain ⟨v, hv, hva, rest, hvals⟩ := g1Vals_prefix_witness ha
  have hrepair := g1CS_aRepair_binary_initial_trace_safe r hc ht
    (v 0) b rest hb v hv hvals rfl
  have hsuffix0 := g1CS_aRepairDone_output_trace_safe r b (v r.arg1)
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryRepairSteps r))
      (3 + (1 + g1OutputKernelSteps r)) :=
    G1RunSafe.transport hrepair.2.symm hsuffix0.1
  have hres : (g1Residual r.tag b).apply (v r.arg1) = res := by
    rw [hva]
    exact g1Residual_apply_spec_binary ht ha hb hs
  rw [g1GateDoneSteps_binary_trace_eq r ht]
  have hcount : g1ABinaryRepairSteps r +
      (3 + (1 + g1OutputKernelSteps r)) =
      g1ABinaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r := by omega
  refine ⟨by
    rw [← hcount]
    exact G1RunSafe.add hrepair.1 hsuffix, ?_⟩
  rw [show g1ABinaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r =
      g1ABinaryRepairSteps r + (3 + (1 + g1OutputKernelSteps r)) by omega,
    runConfig_add, hrepair.2, hsuffix0.2, hres]

/-! ## Exact endpoint structure -/

/-- The binary endpoint pins its tape, designated output cell, off-target
cells, head, result mode/context, and separation from reject/OOB. -/
theorem g1CS_gate_done_binary_structure (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (res : Bool)
    (hs : r.spec = some res) :
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
  rw [(g1CS_gate_done_binary_trace_safe r hc ht res hs).2]
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

namespace G1OutputDoneTraceProbes

open G1PassATraceProbes
open G1AResultProbes

theorem literal_binary_done_steps : g1GateDoneSteps reqA = 606 := by decide

theorem literal_binary_output_done_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 =
        g1OutputDoneConfig reqA true := by
  have h := g1CS_gate_done_binary_trace_safe reqA (by decide)
    (Or.inl rfl) true (by decide)
  rw [literal_binary_done_steps] at h
  exact h

theorem literal_binary_false_done_steps : g1GateDoneSteps reqAndF = 484 := by
  decide

theorem literal_binary_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 =
        g1OutputDoneConfig reqAndF false := by
  have h := g1CS_gate_done_binary_trace_safe reqAndF (by decide)
    (Or.inl rfl) false (by decide)
  rw [literal_binary_false_done_steps] at h
  exact h

theorem literal_binary_true_done_steps : g1GateDoneSteps reqOrT = 512 := by
  decide

theorem literal_binary_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 =
        g1OutputDoneConfig reqOrT true := by
  have h := g1CS_gate_done_binary_trace_safe reqOrT (by decide)
    (Or.inr rfl) true (by decide)
  rw [literal_binary_true_done_steps] at h
  exact h

end G1OutputDoneTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
