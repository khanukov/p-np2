import Complexity.TMVerifier.TuringToolkit.GateOnePassBTerminalRepairTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneRepairExamples

/-!
# GN-3B2d: arbitrary-arg2 G1 pass-B driver trace safety (2026-08-31)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module closes the successful binary pass-B safety slice from the real
`G1M.initialConfig` through arrival at the canonical `readAStart` handoff.  It
adds the safety induction that mirrors `g1CS_walk_loop_exact`, composes its
positive endpoint with the merged terminal/repair safety theorem, and proves
the zero-index read prefix safe directly from validation/rewind safety, the
public forward route scanner, and the final stationary store.

The common theorem splits only on `arg2 = 0`.  Its value premise
`r.vals[r.arg2]? = some b` is essential: this module makes no out-of-bounds
claim.  The endpoint has head zero, mode `readAStart`, the selected bit in
`G1Ctx.vB`, and the canonical tape.  No pass-A step is executed.  There is no
full-gate or `ShiftRunSafe` theorem, GN controller/clock theorem, output write,
verdict, or acceptance statement here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

private theorem g1BDriverAligned_congr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n)
    (heq : h = h') (tape tape' : Fin (G1M.tapeLength n) → Bool)
    (hteq : tape = tape') (mode : G1Mode) (position : G1FramePosition)
    (b0 b1 b2 : Bool) (ctx : G1Ctx) :
    g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx =
      g1AlignedConfig n h' hh' tape' mode position b0 b1 b2 ctx := by
  subst heq
  subst hteq
  rfl

/-! ## The arbitrary-round safety induction -/

set_option linter.unusedVariables false in
/-- The actual safety induction matching `g1CS_walk_loop_exact`.  The base is
the real-initial installation safety theorem.  Each successor transports the
one-round safety theorem across the exact loop endpoint and composes it with
`G1RunSafe.add`; the schedule is normalized only by
`g1BLoopSteps_succ`. -/
theorem g1CS_walk_loop_runSafe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k0 : Nat) (h2 : r.arg2 = k0 + 1) :
    ∀ (k : Nat) (hk2 : k ≤ r.arg2) (hk : k < r.vals.length) (v : Bool)
      (hv : r.vals[k]? = some v),
      G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r + g1BLoopSteps k) := by
  intro k
  induction k with
  | zero =>
      intro hk2 hk v hv
      simpa only [g1BLoopSteps_zero, Nat.add_zero] using
        g1CS_walk_install_runSafe r hc ht k0 h2 v hv
  | succ k ih =>
      intro hk2 hk v hv
      have hkk : k < r.vals.length := by omega
      have hvk : r.vals[k]? = some r.vals[k] :=
        List.getElem?_eq_getElem hkk
      have hprefix := ih (by omega) hkk r.vals[k] hvk
      have hexact := g1CS_walk_loop_exact r hc ht k0 h2 k (by omega) hkk
        r.vals[k] hvk
      have hround0 := g1CS_walk_iteration_runSafe r k (by omega) hk
        r.vals[k] v hvk hv
      have hround : G1RunSafe
          (TM.runConfig (M := G1M)
            (G1M.initialConfig (g1Point (encodeG1 r)))
            (g1WalkInstallSteps r + g1BLoopSteps k))
          (16 * k + 37) :=
        G1RunSafe.transport hexact.symm hround0
      have hall := G1RunSafe.add hprefix hround
      rw [g1BLoopSteps_succ]
      simpa only [Nat.add_assoc] using hall

/-! ## The zero-index read prefix -/

/-- A successful zero-index operand-2 read is safe through its existing
`readAResetStart` endpoint.  This uses the merged validation/rewind prefix,
the public zero-read route and forward-scanner safety, and the final stationary
store.  It does not use cursor installation. -/
theorem g1CS_readB_zero_runSafe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBSteps r) := by
  have hb0 : r.vals[0]? = some b := by simpa [h2] using hb
  obtain ⟨rest, hvals⟩ : ∃ rest : List Bool, r.vals = b :: rest := by
    cases hlist : r.vals with
    | nil => simp [hlist] at hb0
    | cons c cs =>
        have hcb : c = b := by simpa [hlist] using hb0
        subst c
        exact ⟨cs, rfl⟩
  let route := g1ReadBRouteFrames r b
  let suffix := rest.map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]
  have hsplit : route ++ suffix = encodeG1Frames r ++ [.blank] := by
    exact g1ReadBRoute_split r h2 b rest hvals
  have hroom : 4 * route.length < gnLocalSpan (encodeG1 r).length := by
    simp [route, gnLocalSpan, encodeG1_length]
    omega
  have htape : g1ListTape (n := (encodeG1 r).length)
      ((route ++ suffix).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [hsplit]
    exact g1ListTape_validation_eq_initial r
  have hscan0 := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) ([] : List G1Frame) route suffix
    .readBStart g1Ctx0 (g1ReadBRoute_validPath r ht b)
    (by simpa using hroom)
  have hscan : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)) (4 * route.length) := by
    apply G1RunSafe.transport _ hscan0
    rw [g1CS_validate_rewind_readB_exact r hc]
    simp only [List.length_nil, Nat.mul_zero]
    rw [show ([] : List G1Frame) ++ route ++ suffix = route ++ suffix by simp,
      htape]
  have hprefix := G1RunSafe.add
    (g1ValidationRewind_run_safe_to_readB r hc) hscan
  have hsafe : 4 * route.length < G1M.tapeLength (encodeG1 r).length :=
    lt_of_lt_of_le hroom
      (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
  have hroute := g1CS_readB_scan r hc route suffix hsplit
    (g1ReadBRoute_validPath r ht b) hsafe
  rw [g1ReadBRoute_advance r ht b] at hroute
  have hstore0 : G1RunSafe
      (g1AlignedConfig (encodeG1 r).length (4 * route.length) hsafe
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1StoreMode b) .p0 false false false g1Ctx0) 1 := by
    apply g1RunSafe_of_margins
    · simp [route]
      omega
    · simp [route, gnLocalSpan, encodeG1_length]
      omega
  have hstore : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * route.length)) 1 :=
    G1RunSafe.transport hroute.symm hstore0
  have hall := G1RunSafe.add hprefix hstore
  simpa only [g1ReadBSteps, route, g1ReadBRouteFrames_length] using hall

/-! ## Positive and zero compositions to the common pass-A handoff -/

/-- The positive-index driver is safe from the real initial configuration
through the complete terminal cleanup and repair sweep, and reaches the exact
canonical pass-A handoff. -/
theorem g1CS_readB_positive_repaired_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (h2 : 0 < r.arg2) (b : Bool) (hb : r.vals[r.arg2]? = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BPassASteps r) = g1ReadAConfig r b := by
  have hm : r.arg2 < r.vals.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hb
    contradiction
  obtain ⟨k0, hk0⟩ : ∃ k0, r.arg2 = k0 + 1 :=
    ⟨r.arg2 - 1, by omega⟩
  have hloop := g1CS_walk_loop_runSafe r hc ht k0 hk0 r.arg2
    (Nat.le_refl _) hm b hb
  have hloopexact := g1CS_walk_loop_exact r hc ht k0 hk0 r.arg2
    (Nat.le_refl _) hm b hb
  have htail := g1CS_walk_terminal_repair_trace_safe r hm b hb
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r + g1BLoopSteps r.arg2))
      ((16 * r.arg2 + 28) + g1RepairSteps r r.arg2) :=
    G1RunSafe.transport hloopexact.symm htail.1
  have hall := G1RunSafe.add hloop hsuffix
  constructor
  · rw [g1BPassASteps, g1BReadSteps_eq]
    simpa only [Nat.add_assoc] using hall
  · exact g1CS_readB_positive_repaired_exact r hc ht h2 b hb

/-- The zero-index driver composes the independently safe zero read with the
merged zero-rewrite repair sweep and reaches the same exact pass-A handoff. -/
theorem g1CS_readB_zero_repaired_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (h2 : r.arg2 = 0) (b : Bool) (hb : r.vals[r.arg2]? = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ZPassASteps r) = g1ReadAConfig r b := by
  have hm : r.arg2 < r.vals.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hb
    contradiction
  have hread := g1CS_readB_zero_runSafe r hc ht h2 b hb
  have hreadExact := g1CS_readB_zero_exact r hc ht h2 b hb
  have hhead : 4 * (r.tag.units + r.arg1 + 5) =
      4 * (g1WalkCursor r r.arg2 + 1) := by
    simp only [g1WalkCursor, h2]
  have hstart : g1AlignedConfig (encodeG1 r).length
      (4 * (r.tag.units + r.arg1 + 5))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .readAResetStart .p0 false false false (g1Ctx0.withVB b) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1WalkCursor r r.arg2 + 1))
      (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
      (g1ListTape ((g1BSpentFrames r 0).flatMap G1Frame.bits))
      .readAResetStart .p0 false false false (g1Ctx0.withVB b) := by
    refine g1BDriverAligned_congr _ _ _ _ _ hhead _ _ ?_ _ _ _ _ _ _
    rw [g1BSpentFrames_zero r, ← g1ListTape_validation_eq_initial r]
    rfl
  have hrepair0 := g1CS_repair_sweep_runSafe r 0 (by omega) hm
    (g1Ctx0.withVB b)
  have hrepair : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r)) (g1RepairSteps r 0) :=
    G1RunSafe.transport (hreadExact.trans hstart).symm hrepair0
  have hall := G1RunSafe.add hread hrepair
  constructor
  · simpa only [g1ZPassASteps] using hall
  · exact g1CS_readB_zero_repaired_exact r hc ht h2 b hb

/-- The public successful binary pass-B safety theorem.  It splits only on
`arg2 = 0`, exposes the exact conditional schedule, and pins the shared
head-zero `readAStart` state and canonical tape. -/
theorem g1CS_readB_repaired_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) =
        g1ReadAConfig r b ∧
      ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r)).head :
          Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r)).state.snd =
        g1ReadAState (g1Ctx0.withVB b) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r)).tape =
        g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
          G1Frame.bits) := by
  by_cases h2 : r.arg2 = 0
  · rw [if_pos h2]
    have h := g1CS_readB_zero_repaired_trace_safe r hc ht h2 b hb
    refine ⟨h.1, h.2, ?_, ?_, ?_⟩ <;> rw [h.2]
    · exact g1ReadAConfig_head r b
    · exact g1ReadAConfig_state r b
    · exact g1ReadAConfig_tape r b
  · rw [if_neg h2]
    have h := g1CS_readB_positive_repaired_trace_safe r hc ht (by omega) b hb
    refine ⟨h.1, h.2, ?_, ?_, ?_⟩ <;> rw [h.2]
    · exact g1ReadAConfig_head r b
    · exact g1ReadAConfig_state r b
    · exact g1ReadAConfig_tape r b

/-! ## Kernel-visible literal capstones -/

namespace G1PassBDriverTraceProbes

open G1InstallScanExamples (g1WalkExample g1WalkExample_canonical)
open G1RepairExamples (g1ZeroExample g1ZeroExample_canonical
  zeroExample_steps twoExample_steps)

/-- The two-round positive request is safe for all `400` genuine steps and
ends at the exact canonical pass-A handoff. -/
theorem literal_positive_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400 =
        g1ReadAConfig g1WalkExample true := by
  have h := g1CS_readB_positive_repaired_trace_safe g1WalkExample
    g1WalkExample_canonical (Or.inl rfl) (by decide) true (by decide)
  rw [twoExample_steps.1] at h
  exact h

/-- The zero-index request is safe for all `172` genuine steps and ends at the
same exact canonical pass-A handoff. -/
theorem literal_zero_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172 =
        g1ReadAConfig g1ZeroExample true := by
  have h := g1CS_readB_zero_repaired_trace_safe g1ZeroExample
    g1ZeroExample_canonical (Or.inl rfl) rfl true (by decide)
  rw [zeroExample_steps.2.1] at h
  exact h

end G1PassBDriverTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
