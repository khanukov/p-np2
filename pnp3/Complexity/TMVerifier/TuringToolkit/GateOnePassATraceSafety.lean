import Complexity.TMVerifier.TuringToolkit.GateOnePassBDriverTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInvariant

/-!
# GN-3B2e1a: binary pass-A installation trace safety (2026-08-31)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This dependency-closed e1a module starts at the merged successful binary
`readAStart` handoff.  It proves prefix safety for the stationary dispatch,
pass-A tag rescan, operation latch, and live cursor installation.  Separate
endpoint conjuncts identify the exact `Σᴬ(0)` configuration.  Its real-initial
capstone composes the merged pass-B driver safety with that installation.

The mixed two-mode A reverse seek and one successful round are deliberately
deferred to e1b: no endpoint-to-safety inference or clamp-dependent substitute
is admitted here.  Empty-data and successor-data OOB endpoints remain separate
existing endpoints; neither is presented as a successful binary route.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1A_runSafe_one {W : Nat}
    (c : Configuration (M := G1M) W) (h : G1LocalStepSafe c) :
    G1RunSafe c 1 := by
  simpa using G1RunSafe.succ (G1RunSafe.empty c) h

/-! ## Binary entry and live installation -/

/-- Exact successful schedule from the merged `readAStart` handoff through the
completed A cursor writer. -/
def g1AReadInstallSteps (r : G1Request) : Nat :=
  1 + (4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r

private theorem g1AInstallSkippedFrames_skip (r : G1Request) :
    ∀ f ∈ g1AInstallSkippedFrames r, G1AInstallSkip f := by
  intro f hf
  simp only [g1AInstallSkippedFrames, List.mem_append, List.mem_replicate,
    List.mem_cons] at hf
  rcases hf with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ <;> trivial

private theorem g1AInstall_path (r : G1Request) :
    G1ValidPath .aInsSeek (g1AInstallSkippedFrames r ++ [.separator]) := by
  have hfix : ∀ f ∈ g1AInstallSkippedFrames r,
      g1Advance .aInsSeek f = .aInsSeek :=
    fun f hf => g1Advance_aInsSeek_of_skip
      (g1AInstallSkippedFrames_skip r f hf)
  exact g1ValidPath_fix (mode := .aInsSeek) trivial [.separator]
    ⟨trivial, by decide, trivial⟩ _ hfix

set_option maxHeartbeats 1000000 in
/-- From the merged binary `readAStart` configuration, stationary dispatch,
the forward tag rescan, operation latch, live installation entry, strict
installation scan, probe/latch and cursor writer are all prefix-safe. -/
theorem g1CS_readA_binary_install_runSafe (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    G1RunSafe (g1ReadAConfig r bB) (g1AReadInstallSteps r) := by
  have htag : r.tag ≠ .const := by
    rcases ht with h | h <;> rw [h] <;> decide
  have hdispatchLocal : G1LocalStepSafe (g1ReadAConfig r bB) := by
    apply g1LocalStepSafe_at_zero_of_not_left
    · exact g1ReadAConfig_head r bB
    · have hm : (G1M.step (g1ReadAConfig r bB).state
          ((g1ReadAConfig r bB).tape (g1ReadAConfig r bB).head)).snd.snd =
          Move.stay := by rfl
      rw [hm]
      exact Move.noConfusion
  have hdispatch := g1A_runSafe_one _ hdispatchLocal
  have hdispatchExact : TM.runConfig (M := G1M) (g1ReadAConfig r bB) 1 =
      g1ABofConfig r bB := by
    simpa [g1ReadAConfig, g1ABofConfig] using
      g1CS_step_readAStart_entry (encodeG1 r).length 0
        (g1_route_lt_tapeLength r 0 (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1Ctx0.withVB bB) rfl
  let tagRest := g1TagRouteRest r
  have htagRoom : 4 * (g1TagRouteFrames r).length <
      gnLocalSpan (encodeG1 r).length := by
    simp [gnLocalSpan, encodeG1_length]
    omega
  have htagScan0 := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) ([] : List G1Frame) (g1TagRouteFrames r)
    tagRest .aBof (g1Ctx0.withVB bB)
    (g1ATagRoute_validPath r htag) (by simpa using htagRoom)
  have htagTape : g1ListTape (n := (encodeG1 r).length)
      ((([] : List G1Frame) ++ g1TagRouteFrames r ++ tagRest).flatMap
        G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [List.nil_append, show g1TagRouteFrames r ++ tagRest =
      encodeG1Frames r ++ [.blank] by exact g1TagRoute_split r]
    exact g1ListTape_validation_eq_initial r
  have htagScan : G1RunSafe
      (TM.runConfig (M := G1M) (g1ReadAConfig r bB) 1)
      (4 * (r.tag.units + 2)) := by
    apply G1RunSafe.transport hdispatchExact.symm
    rw [htagTape] at htagScan0
    simpa [g1ABofConfig] using htagScan0
  have hentryPrefix := G1RunSafe.add hdispatch htagScan
  have htagExact : TM.runConfig (M := G1M) (g1ReadAConfig r bB)
      (1 + 4 * (r.tag.units + 2)) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 2))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1AOpMode r.tag) .p0 false false false (g1Ctx0.withVB bB) := by
    rw [runConfig_add, hdispatchExact, g1ABofConfig,
      ← g1ListTape_validation_eq_initial r]
    have h := g1CS_aTagRescan_exact (encodeG1 r).length []
      (g1TagRouteRest r) r htag (g1Ctx0.withVB bB)
      (by simpa using
        g1_route_lt_tapeLength r (r.tag.units + 2) (by omega))
    rw [List.nil_append, g1TagRoute_split] at h
    simpa only [List.length_nil, Nat.zero_add, g1ValidationFrames] using h
  have hop : G1RunSafe
      (TM.runConfig (M := G1M) (g1ReadAConfig r bB)
        (1 + 4 * (r.tag.units + 2))) 1 := by
    rw [htagExact]
    apply g1RunSafe_of_margins
    · simp only [g1AlignedConfig_head_val]
      omega
    · simp only [g1AlignedConfig_head_val]
      simp [gnLocalSpan, encodeG1_length]
      omega
  have hthroughOp := G1RunSafe.add hentryPrefix hop
  have hopExact : TM.runConfig (M := G1M) (g1ReadAConfig r bB)
      (1 + 4 * (r.tag.units + 2) + 1) = g1AInstallConfig r bB := by
    rw [show 1 + 4 * (r.tag.units + 2) + 1 =
      1 + (4 * (r.tag.units + 2) + 1) by omega,
      runConfig_add, hdispatchExact]
    exact g1CS_passA_entry_initial_exact r htag bB
  have hliveEntry : G1RunSafe
      (TM.runConfig (M := G1M) (g1ReadAConfig r bB)
        (1 + 4 * (r.tag.units + 2) + 1)) 1 := by
    rw [hopExact]
    apply g1RunSafe_of_margins
    · simp [g1AInstallConfig]
      omega
    · simp [g1AInstallConfig, gnLocalSpan, encodeG1_length]
      omega
  have hliveExact : TM.runConfig (M := G1M) (g1ReadAConfig r bB)
      (1 + 4 * (r.tag.units + 2) + 1 + 1) =
      g1AInstallSeekConfig r bB := by
    rw [runConfig_add, hopExact]
    exact g1CS_aInstall_entry_initial_exact r bB
  let frames := g1AInstallSkippedFrames r ++ [.separator]
  let suffix := G1Frame.data bA ::
    (rest.map G1Frame.data ++ [.output false, .finish, .blank])
  have hscanRoom : 4 * ((g1TagRouteFrames r).length + frames.length) <
      gnLocalSpan (encodeG1 r).length := by
    simp [frames, gnLocalSpan, encodeG1_length]
    omega
  have hscan0 := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) (g1TagRouteFrames r) frames suffix
    .aInsSeek ((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB))
    (by simpa [frames] using g1AInstall_path r) hscanRoom
  have hword : g1TagRouteFrames r ++ frames ++ suffix =
      encodeG1Frames r ++ [.blank] := by
    simp [frames, suffix, hv, g1AInstallSkippedFrames, encodeG1Frames,
      g1TagRouteFrames, List.append_assoc]
  have hscanTape : g1ListTape (n := (encodeG1 r).length)
      ((g1TagRouteFrames r ++ frames ++ suffix).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [hword]
    exact g1ListTape_validation_eq_initial r
  have hscan : G1RunSafe
      (TM.runConfig (M := G1M) (g1ReadAConfig r bB)
        (1 + 4 * (r.tag.units + 2) + 1 + 1))
      (4 * (r.arg1 + r.arg2 + 2)) := by
    apply G1RunSafe.transport hliveExact.symm
    rw [hscanTape] at hscan0
    simpa [g1AInstallSeekConfig, frames] using hscan0
  have hinstallPrefix := G1RunSafe.add (G1RunSafe.add hthroughOp hliveEntry)
    (by simpa only [Nat.add_assoc] using hscan)
  have hscanExact0 := g1CS_aInstall_scan (encodeG1 r).length
    (g1TagRouteFrames r) (g1AInstallSkippedFrames r) suffix
    ((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB))
    (g1AInstallSkippedFrames_skip r)
    (by
      simp only [g1TagRouteFrames_length, g1AInstallSkippedFrames_length]
      simpa only [show r.tag.units + 2 + (r.arg1 + r.arg2 + 1 + 1) =
        r.tag.units + r.arg1 + r.arg2 + 4 by omega] using
        g1_route_lt_tapeLength r
          (r.tag.units + r.arg1 + r.arg2 + 4) (by omega))
  have hmacroWord : g1TagRouteFrames r ++ g1AInstallSkippedFrames r ++
      G1Frame.separator :: suffix = encodeG1Frames r ++ [.blank] := by
    simpa [frames, List.append_assoc] using hword
  rw [hmacroWord] at hscanExact0
  have hinitTape := g1ListTape_validation_eq_initial r
  simp only [g1ValidationFrames] at hinitTape
  rw [hinitTape] at hscanExact0
  have hscanExact : TM.runConfig (M := G1M) (g1AInstallSeekConfig r bB)
      (4 * (r.arg1 + r.arg2 + 2)) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1InstallRouteFrames r).length)
        (g1_route_lt_tapeLength r _ (by
          rw [g1InstallRouteFrames_length]
          omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .aProbe .p0 false false false
        ((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB)) := by
    simpa only [g1AInstallSeekConfig, g1TagRouteFrames_length,
      g1AInstallSkippedFrames_length, g1InstallRouteFrames_length,
      show r.arg1 + r.arg2 + 1 + 1 = r.arg1 + r.arg2 + 2 by omega,
      show r.tag.units + 2 + (r.arg1 + r.arg2 + 1 + 1) =
        r.tag.units + r.arg1 + r.arg2 + 4 by omega] using hscanExact0
  have hpreTail : TM.runConfig (M := G1M) (g1ReadAConfig r bB)
      (1 + (4 * (r.tag.units + 2) + 1) + 1 +
        4 * (r.arg1 + r.arg2 + 2)) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1InstallRouteFrames r).length)
        (g1_route_lt_tapeLength r _ (by
          rw [g1InstallRouteFrames_length]
          omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .aProbe .p0 false false false
        ((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB)) := by
    rw [show 1 + (4 * (r.tag.units + 2) + 1) + 1 +
      4 * (r.arg1 + r.arg2 + 2) =
        (1 + 4 * (r.tag.units + 2) + 1 + 1) +
          4 * (r.arg1 + r.arg2 + 2) by omega,
      runConfig_add, hliveExact, hscanExact]
  have htail : G1RunSafe
      (TM.runConfig (M := G1M) (g1ReadAConfig r bB)
        (1 + (4 * (r.tag.units + 2) + 1) + 1 +
          4 * (r.arg1 + r.arg2 + 2))) 9 := by
    rw [hpreTail]
    apply g1RunSafe_of_margins
    · simp only [g1AlignedConfig_head_val, g1InstallRouteFrames_length]
      omega
    · simp only [g1AlignedConfig_head_val, g1InstallRouteFrames_length]
      simp [gnLocalSpan, encodeG1_length]
      omega
  have hall := G1RunSafe.add hinstallPrefix (by
    simpa only [Nat.add_assoc] using htail)
  unfold g1AReadInstallSteps g1ALiveInstallSteps
  convert hall using 1
  all_goals omega

/-- The safe binary installation schedule has the exact completed-writer
endpoint, hence the exact `Σᴬ(0)` endpoint when the nonempty data witness is
re-associated with the invariant. -/
theorem g1CS_readA_binary_install_trace_safe (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    G1RunSafe (g1ReadAConfig r bB) (g1AReadInstallSteps r) ∧
      TM.runConfig (M := G1M) (g1ReadAConfig r bB)
        (g1AReadInstallSteps r) = g1APostWriterConfig r bA bB ∧
      TM.runConfig (M := G1M) (g1ReadAConfig r bB)
        (g1AReadInstallSteps r) =
          g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
            (by rw [hv]; simp) := by
  have htag : r.tag ≠ .const := by
    rcases ht with h | h <;> rw [h] <;> decide
  have hexact : TM.runConfig (M := G1M) (g1ReadAConfig r bB)
      (g1AReadInstallSteps r) = g1APostWriterConfig r bA bB := by
    rw [g1AReadInstallSteps,
      show 1 + (4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r =
        1 + ((4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r) by omega,
      runConfig_add]
    have hdispatch : TM.runConfig (M := G1M) (g1ReadAConfig r bB) 1 =
        g1ABofConfig r bB := by
      simpa [g1ReadAConfig, g1ABofConfig] using
        g1CS_step_readAStart_entry (encodeG1 r).length 0
          (g1_route_lt_tapeLength r 0 (by omega))
          (G1M.initialConfig (g1Point (encodeG1 r))).tape
          (g1Ctx0.withVB bB) rfl
    rw [hdispatch, runConfig_add, g1CS_passA_entry_initial_exact r htag bB]
    exact g1CS_aInstall_success_exact r bA bB rest hv
  exact ⟨g1CS_readA_binary_install_runSafe r ht bA bB rest hv, hexact,
    hexact.trans (g1APostWriterConfig_eq_sigma0 r bA bB rest hv)⟩

/-! ## Real-initial binary installation capstone -/

/-- The merged pass-B driver safety composes with the safe binary pass-A
installation and reaches the exact completed writer / `Σᴬ(0)` boundary. -/
theorem g1CS_readA_binary_install_from_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (hv : r.vals = bA :: rest) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryCursorSteps r) = g1APostWriterConfig r bA bB ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryCursorSteps r) =
        g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
          (by rw [hv]; simp) := by
  have hBsafe := g1CS_readB_repaired_trace_safe r hc ht bB hB
  have hAsafe := g1CS_readA_binary_install_runSafe r ht bA bB rest hv
  have hAsafe' : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r))
      (g1AReadInstallSteps r) :=
    G1RunSafe.transport hBsafe.2.1.symm hAsafe
  have hall := G1RunSafe.add hBsafe.1 hAsafe'
  have hsched :
      (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) +
          g1AReadInstallSteps r = g1ABinaryCursorSteps r := by
    simp [g1AReadInstallSteps, g1ABinaryCursorSteps, g1BActivatedSteps,
      g1ALiveInstallSteps]
    omega
  rw [hsched] at hall
  have hexact := g1CS_aCursor_binary_initial_exact r hc ht bA bB rest hB hv
  exact ⟨hall, hexact,
    hexact.trans (g1APostWriterConfig_eq_sigma0 r bA bB rest hv)⟩

/-- Structural projections supported at the e1a endpoint: one cursor, no
spent A unit yet, all operand indices intact, the B residual retained, the A
value latched, and the head inside the local `W+5` footprint. -/
theorem g1CS_readA_binary_install_structure (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (hv : r.vals = bA :: rest) :
    let out := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1ABinaryCursorSteps r)
    out.state.snd.ctx.res = g1Residual r.tag bB ∧
      out.state.snd.ctx.vB = bA ∧
      out.tape = g1ListTape ((g1AWalkFrames r 0).flatMap G1Frame.bits) ∧
      (g1AWalkFrames r 0).count .cursor = 1 ∧
      (g1AWalkFrames r 0).count .spent = 0 ∧
      (g1AWalkFrames r 0).count .index = r.arg1 + r.arg2 ∧
      (out.head : Nat) + 1 < gnLocalSpan (encodeG1 r).length := by
  dsimp only
  rw [(g1CS_readA_binary_install_from_initial_trace_safe r hc ht bA bB rest
    hB hv).2.2]
  refine ⟨g1AWalkConfig_res _ _ _ _ _ _ _, rfl, rfl,
    g1AWalkFrames_count_cursor _ _, g1AWalkFrames_count_spent _ _, ?_, ?_⟩
  · simpa using g1AWalkFrames_count_index r 0
  · simp [g1AWalkConfig, g1AWalkCursor, gnLocalSpan, encodeG1_length]
    omega

namespace G1PassATraceProbes

/-- Literal requested for the binary lane. -/
def reqA : G1Request := ⟨.and, 1, 1, [true, true, false]⟩

/-- The dependency-closed e1a literal reaches `Σᴬ(0)` safely in 370 steps.
The separate first round has exact merged cost 53, so the requested 423-step
`Σᴬ(1)` statement is precisely the deferred e1b composition. -/
theorem literal_install_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 370 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 370 =
        g1AWalkConfig reqA true 0 (by decide) (by decide) true
          (by decide) := by
  have h := g1CS_readA_binary_install_from_initial_trace_safe reqA (by decide)
    (Or.inl rfl) true true [true, false] (by decide) rfl
  simp [reqA, g1ABinaryCursorSteps, g1BActivatedSteps,
    g1BPassASteps, g1BReadSteps, g1InstallScanSteps, g1RepairSteps,
    g1ReadBHandoffSteps, g1ALiveInstallSteps, G1Tag.units] at h
  exact ⟨h.1, h.2.2⟩

end G1PassATraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
