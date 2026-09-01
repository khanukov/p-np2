import Complexity.TMVerifier.TuringToolkit.GateOneRouteRewindTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneARepairTraceSafety

/-!
# GN-3B2fB unary pass-A install/driver/repair trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module composes the merged unary activation endpoint with the generic
nonconstant pass-A installation safety theorem, the generic A driver and
terminal cleanup, and the live A-repair safety theorem.  Successful canonical
`input`/`not` requests reach the exact head-zero `aRepairDone` endpoint on the
existing `g1AUnaryRepairSteps` schedule.

The public semantic boundary requires only `Canonical`, the unary tag, and
`spec = some res`.  The selected operand and finite prefix witnesses are
derived from the existing pure-spec lemmas.  Empty-value unary requests remain
on the separate OOB route.  No result, combine, output, constant, five-tag,
shifted-run, controller, clock, verdict, or acceptance theorem is added here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Unary installation from the live activation endpoint -/

set_option maxHeartbeats 1000000 in
/-- Remove the already-executed stationary dispatch from the generic
`readAStart` installation proof. -/
theorem g1CS_aBof_install_runSafe (r : G1Request) (htag : r.tag ≠ .const)
    (bA bB : Bool) (rest : List Bool) (hv : r.vals = bA :: rest) :
    G1RunSafe (g1ABofConfig r bB)
      ((4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r) := by
  have hfull := g1CS_readA_install_runSafe r htag bA bB rest hv
  have hdispatch : TM.runConfig (M := G1M) (g1ReadAConfig r bB) 1 =
      g1ABofConfig r bB := by
    simpa [g1ReadAConfig, g1ABofConfig] using
      g1CS_step_readAStart_entry (encodeG1 r).length 0
        (g1_route_lt_tapeLength r 0 (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1Ctx0.withVB bB) rfl
  intro j hj
  have hjfull : 1 + j < g1AReadInstallSteps r := by
    simp only [g1AReadInstallSteps]
    omega
  have hlocal := hfull (1 + j) hjfull
  rw [runConfig_add, hdispatch] at hlocal
  exact hlocal

set_option maxHeartbeats 1000000 in
/-- The real unary route is prefix-safe through installation and reaches the
exact `Σᴬ(0)` configuration on `g1AUnaryCursorSteps`. -/
theorem g1CS_readA_unary_install_from_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (bA : Bool) (rest : List Bool) (hv : r.vals = bA :: rest) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1AUnaryCursorSteps r) =
        g1AWalkConfig r false 0 (Nat.zero_le _) (by rw [hv]; simp) bA
          (by rw [hv]; simp) := by
  have htag : r.tag ≠ .const := by
    rcases ht with h | h <;> rw [h] <;> decide
  have hactivate := g1CS_activate_unary_trace_safe r hc ht
  have hsuffix0 := g1CS_aBof_install_runSafe r htag bA false rest hv
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r))
      ((4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r) :=
    G1RunSafe.transport hactivate.2.symm hsuffix0
  constructor
  · have hall := G1RunSafe.add hactivate.1 hsuffix
    have hsched : g1UActivatedSteps r +
        ((4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r) =
        g1AUnaryCursorSteps r := by
      simp [g1AUnaryCursorSteps]
      omega
    rw [hsched] at hall
    exact hall
  · exact g1CS_readA_sigma0_unary_exact r hc ht bA rest hv

/-! ## Driver and live repair composition -/

/-- Exact decomposition used by the unary safety composition. -/
theorem g1AUnaryRepairSteps_trace_eq (r : G1Request) :
    g1AUnaryRepairSteps r =
      (g1AUnaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) +
      g1ARepairLiveSteps r := by
  simp [g1AUnaryRepairSteps, g1AWalkRepairSteps]
  omega

/-- Caller-supplied finite-prefix form of complete real-initial unary safety.
This is the exact proof-level composition used by the semantic wrapper below. -/
theorem g1CS_aRepair_unary_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1AUnaryRepairSteps r) =
        g1ARepairDoneConfig r false (v r.arg1) := by
  have hlen : r.arg1 < r.vals.length :=
    (List.getElem?_eq_some_iff.1 (hv r.arg1 (Nat.le_refl _))).1
  have hinstall := g1CS_readA_unary_install_from_initial_trace_safe r hc ht
    (v 0) rest hvals
  have hdriver0 := g1CS_aWalk_full_driver_trace_safe r false hlen v hv
  have hdriver : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r))
      (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) :=
    G1RunSafe.transport hinstall.2.symm hdriver0.1
  have hprefix := G1RunSafe.add hinstall.1 hdriver
  have hprefixExact : TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1AUnaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) =
      g1AWalkRepairStartConfig r false (v r.arg1) hlen
        (hv r.arg1 (Nat.le_refl _)) := by
    rw [runConfig_add, hinstall.2, hdriver0.2]
  have hlive0 := g1CS_aRepair_live_trace_safe r false (v r.arg1) hlen
    (hv r.arg1 (Nat.le_refl _))
  have hlive : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r +
          (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)))
      (g1ARepairLiveSteps r) :=
    G1RunSafe.transport hprefixExact.symm hlive0.1
  rw [g1AUnaryRepairSteps_trace_eq]
  exact ⟨G1RunSafe.add hprefix hlive, by
    rw [runConfig_add, hprefixExact, hlive0.2]⟩

/-- Honest unary success boundary.  No selected value, prefix function, list
tail, or runtime/advice field is required from the caller. -/
theorem g1CS_aRepair_unary_spec_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (res : Bool) (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r) ∧
      ∃ selectedA : Bool,
        TM.runConfig (M := G1M)
            (G1M.initialConfig (g1Point (encodeG1 r)))
            (g1AUnaryRepairSteps r) =
          g1ARepairDoneConfig r false selectedA ∧
        (g1Residual r.tag false).apply selectedA = res := by
  obtain ⟨selectedA, hselected⟩ := g1Spec_operand_unary ht hs
  obtain ⟨v, hv, hend, rest, hvals⟩ := g1Vals_prefix_witness hselected
  have htrace := g1CS_aRepair_unary_initial_trace_safe r hc ht v hv rest hvals
  refine ⟨htrace.1, selectedA, ?_,
    g1Residual_apply_spec_unary ht false hselected hs⟩
  simpa [hend] using htrace.2

/-! ## Existing input/not literal pins -/

namespace G1UnaryARepairTraceProbes

open G1AResultProbes

/-- Exact existing intermediate installation and final repair totals. -/
theorem literal_steps :
    g1AUnaryCursorSteps reqInputT = 131 ∧
      g1AUnaryRepairSteps reqInputT = 192 ∧
      g1AUnaryCursorSteps reqNotF = 171 ∧
      g1AUnaryRepairSteps reqNotF = 240 := by
  decide

theorem literal_input_install_repair_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 131 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 131 =
        g1AWalkConfig reqInputT false 0 (by decide) (by decide) true
          (by decide)) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 192 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 192 =
        g1ARepairDoneConfig reqInputT false true) := by
  have hi := g1CS_readA_unary_install_from_initial_trace_safe reqInputT
    literal_canonical.1 (Or.inl rfl) true [] rfl
  have hr := g1CS_aRepair_unary_initial_trace_safe reqInputT
    literal_canonical.1 (Or.inl rfl) (fun _ => true) (by decide) [] rfl
  rw [literal_steps.1] at hi
  rw [literal_steps.2.1] at hr
  exact ⟨hi, hr⟩

theorem literal_not_install_repair_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 171 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 171 =
        g1AWalkConfig reqNotF false 0 (by decide) (by decide) true
          (by decide)) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 240 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 240 =
        g1ARepairDoneConfig reqNotF false true) := by
  have hi := g1CS_readA_unary_install_from_initial_trace_safe reqNotF
    literal_canonical.2.1 (Or.inr rfl) true [] rfl
  have hr := g1CS_aRepair_unary_initial_trace_safe reqNotF
    literal_canonical.2.1 (Or.inr rfl) (fun _ => true) (by decide) [] rfl
  rw [literal_steps.2.2.1] at hi
  rw [literal_steps.2.2.2] at hr
  exact ⟨hi, hr⟩

end G1UnaryARepairTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
