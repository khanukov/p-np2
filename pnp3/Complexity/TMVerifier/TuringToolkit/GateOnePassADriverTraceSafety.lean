import Complexity.TMVerifier.TuringToolkit.GateOnePassARoundTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkDriver

/-!
# GN-3B2e2: arbitrary pass-A driver trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module iterates the merged e1b one-round safety theorem on the exact S7
schedule, proves the successful exhaustion seek safe, and proves the existing
terminal cursor cleanup safe through its exact `aRepairStart` endpoint.  Exact
execution equalities only transport adjacent safe segments; all composition
uses `G1RunSafe.add`.  Every physical bound is a strict local-span bound, so
no clamped-head conclusion is used.

The real-initial capstone uses e1a's successful binary `Σᴬ(0)` safety and the
actual public schedule expression.  Successor-data OOB stays separate.  No
repair step, unary/constant route, result/output/full-gate `ShiftRunSafe`, GN
controller, clock, verdict or acceptance theorem is added.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Exact arbitrary-round safety induction -/

/-- Genuine induction from `Σᴬ(0)` through the first `m` successful rounds. -/
theorem g1CS_aWalk_driver_runSafe (r : G1Request) (b : Bool) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    G1RunSafe
      (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
        (hv 0 (by omega)))
      (g1AWalkDriverSteps r m) := by
  induction m with
  | zero =>
      simpa using (G1RunSafe.empty
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))))
  | succ m ih =>
      have hm' : m < r.vals.length := by omega
      have hprefix := ih (by omega) hm' (fun j hj => hv j (by omega))
      have hexact := g1CS_aWalk_driver_exact r b m (by omega) hm' v
        (fun j hj => hv j (by omega))
      have hround0 := g1CS_aWalk_round_runSafe r b m (by omega) hm
        (v m) (v (m + 1)) (hv m (by omega))
        (hv (m + 1) (Nat.le_refl _))
      have hround : G1RunSafe
          (TM.runConfig (M := G1M)
            (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
              (hv 0 (by omega)))
            (g1AWalkDriverSteps r m))
          (g1AWalkRoundSteps r m) :=
        G1RunSafe.transport hexact.symm hround0
      have hall := G1RunSafe.add hprefix hround
      rw [g1AWalkDriverSteps_succ]
      exact hall

/-- Driver safety paired with the exact existing `Σᴬ(m)` endpoint. -/
theorem g1CS_aWalk_driver_trace_safe (r : G1Request) (b : Bool) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    G1RunSafe
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkDriverSteps r m) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
            (hv 0 (by omega)))
          (g1AWalkDriverSteps r m) =
        g1AWalkConfig r b m hm1 hm (v m) (hv m (Nat.le_refl _)) :=
  ⟨g1CS_aWalk_driver_runSafe r b m hm1 hm v hv,
    g1CS_aWalk_driver_exact r b m hm1 hm v hv⟩

/-! ## Exhaustion seek and terminal cleanup -/

/-- At `j = arg1`, the exact mixed seek to the opening A separator is safe. -/
theorem g1CS_aWalk_exhaust_runSafe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
      (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
      (g1AWalkExhaustSteps r) := by
  have hpre := g1AWalkExhaustPre_length r
  have hinner := g1AWalkInnerRun_length r.arg1
  have houter := g1AWalkOuterRun_length r r.arg1 (by omega)
  have hcursor := g1AWalkCursor_safe r r.arg1 hj
  have hroom : 4 * ((g1AWalkExhaustPre r).length +
      ((g1AWalkInnerRun r.arg1).length +
        (g1AWalkOuterRun r r.arg1).length + 1)) + 8 <
      gnLocalSpan (encodeG1 r).length := by
    rw [hpre, hinner, houter]
    simp [gnLocalSpan, encodeG1_length]
    omega
  have hs := g1ASeek_acrossBoundary_runSafe
    (W := (encodeG1 r).length) (g1AWalkExhaustPre r) .argSep
    (g1AWalkInnerRun r.arg1) (g1AWalkOuterRun r r.arg1)
    (.cursor :: g1AWalkTail r r.arg1) (g1AWalkCtx r b v)
    (g1AWalkOuterRun_skip r r.arg1) (g1AWalkInnerRun_skip r.arg1)
    trivial hroom
  rw [g1AWalkSplit_exhaust r] at hs
  simpa only [g1AWalkConfig, hpre, hinner, houter, g1AWalkExhaustSteps,
    g1AWalkCursor,
    show 4 * (r.tag.units + 1 +
        (r.arg1 + (r.arg2 + r.arg1 + 1) + 1)) + 3 =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.arg1 + 4) - 1 by omega,
    show 4 * (r.arg1 + (r.arg2 + r.arg1 + 1) + 1) + 4 =
      8 * r.arg1 + 4 * r.arg2 + 12 by omega] using hs

/-- The exhaustion seek is safe and has the exact existing `aExh` endpoint. -/
theorem g1CS_aWalk_exhaust_trace_safe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
          (g1AWalkExhaustSteps r) =
        g1AWalkExhaustConfig r b v hj hv :=
  ⟨g1CS_aWalk_exhaust_runSafe r b v hj hv,
    g1CS_aWalk_exhaust_exact r b v hj hv⟩

/-- Safe forward return from `aExh` through the exact skip run and cursor. -/
theorem g1CS_aWalk_exh_to_cursor_runSafe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkExhaustConfig r b v hj hv)
      (8 * r.arg1 + 4 * r.arg2 + 16) := by
  let pre := g1AWalkExhaustPre r
  let skipped := g1AWalkFwdRun r r.arg1
  let suffix := g1AWalkTail r r.arg1
  let frames := G1Frame.argSep :: (skipped ++ [.cursor])
  have hfix : ∀ f ∈ skipped, g1Advance .aRet f = .aRet :=
    fun f hf => g1Advance_aRet_of_skip
      (g1AWalkFwdRun_skip r r.arg1 f hf)
  have hpath : G1ValidPath .aExh frames :=
    ⟨trivial, by decide,
      g1ValidPath_fix (mode := .aRet) trivial [.cursor]
        ⟨trivial, by decide, trivial⟩ skipped hfix⟩
  have hpre : pre.length = r.tag.units + 1 :=
    g1AWalkExhaustPre_length r
  have hskipped : skipped.length = 2 * r.arg1 + r.arg2 + 2 :=
    g1AWalkFwdRun_length r r.arg1 (by omega)
  have hroom : 4 * (pre.length + frames.length) <
      gnLocalSpan (encodeG1 r).length := by
    simp only [frames, List.length_cons, List.length_append,
      hpre, hskipped]
    simp [gnLocalSpan, encodeG1_length]
    omega
  have hs := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) pre frames suffix .aExh
    (g1AWalkCtx r b v) hpath hroom
  have hword : pre ++ frames ++ suffix = g1AWalkFrames r r.arg1 := by
    rw [← g1AWalkSplit_exhaust_fwd r]
    simp [pre, skipped, suffix, frames, List.append_assoc]
  rw [hword] at hs
  simpa only [g1AWalkExhaustConfig, hpre, hskipped, frames,
    List.length_cons, List.length_append, List.length_singleton,
    List.length_nil, Nat.zero_add,
    show 4 * (2 * r.arg1 + r.arg2 + 2 + 1 + 1) =
      8 * r.arg1 + 4 * r.arg2 + 16 by omega] using hs

set_option linter.unusedVariables false in
/-- The four-cell terminal turn and four-cell cursor-removing restore are safe
without a clamp argument. -/
theorem g1CS_aWalk_terminal_turn_restore_runSafe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r r.arg1 + 1)) (by
          have := g1AWalkCursor_safe r r.arg1 hj
          omega)
        (g1ListTape ((g1AWalkFrames r r.arg1).flatMap G1Frame.bits))
        .aTurnFin .p0 false false false (g1AWalkCtx r b v)) 8 := by
  apply g1RunSafe_of_margins
  · simp [g1AWalkCursor]
    omega
  · simp [g1AWalkCursor, gnLocalSpan, encodeG1_length]
    omega

set_option maxHeartbeats 1000000 in
/-- The complete exact terminal cleanup is safe and reaches `aRepairStart`. -/
theorem g1CS_aWalk_terminal_from_exhaust_trace_safe (r : G1Request)
    (b v : Bool) (hj : r.arg1 < r.vals.length)
    (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkExhaustConfig r b v hj hv)
        (g1AWalkTerminalSteps r) ∧
      TM.runConfig (M := G1M) (g1AWalkExhaustConfig r b v hj hv)
          (g1AWalkTerminalSteps r) =
        g1AWalkRepairStartConfig r b v hj hv := by
  have hscan := g1CS_aWalk_exh_to_cursor_runSafe r b v hj hv
  have hscanExact := g1CS_aWalk_exh_to_cursor (encodeG1 r).length
    (g1AWalkExhaustPre r) (g1AWalkFwdRun r r.arg1)
    (g1AWalkTail r r.arg1) (g1AWalkCtx r b v)
    (g1AWalkFwdRun_skip r r.arg1) (by
      have h := g1AWalkCursor_safe r r.arg1 hj
      rw [g1AWalkExhaustPre_length,
        g1AWalkFwdRun_length r r.arg1 (by omega)]
      simp only [g1AWalkCursor] at h
      omega)
  rw [g1AWalkSplit_exhaust_fwd r] at hscanExact
  have hendpoint : TM.runConfig (M := G1M)
      (g1AWalkExhaustConfig r b v hj hv)
      (8 * r.arg1 + 4 * r.arg2 + 16) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1AWalkCursor r r.arg1 + 1)) (by
        have := g1AWalkCursor_safe r r.arg1 hj
        omega)
      (g1ListTape ((g1AWalkFrames r r.arg1).flatMap G1Frame.bits))
      .aTurnFin .p0 false false false (g1AWalkCtx r b v) := by
    simpa only [g1AWalkExhaustConfig, g1AWalkExhaustPre_length,
      g1AWalkFwdRun_length r r.arg1 (by omega), g1AWalkCursor,
      show 4 * (2 * r.arg1 + r.arg2 + 2 + 2) =
        8 * r.arg1 + 4 * r.arg2 + 16 by omega,
      show 4 * (r.tag.units + 1 + (2 * r.arg1 + r.arg2 + 2 + 2)) =
        4 * (r.tag.units + r.arg1 + r.arg2 + r.arg1 + 4 + 1) by omega]
      using hscanExact
  have htail0 := g1CS_aWalk_terminal_turn_restore_runSafe r b v hj hv
  have htail : G1RunSafe
      (TM.runConfig (M := G1M) (g1AWalkExhaustConfig r b v hj hv)
        (8 * r.arg1 + 4 * r.arg2 + 16)) 8 := by
    rw [hendpoint]
    exact htail0
  have hall := G1RunSafe.add hscan htail
  constructor
  · simpa [g1AWalkTerminalSteps] using hall
  · exact g1CS_aWalk_terminal_from_exhaust_exact r b v hj hv

/-- The requested successful `Σᴬ(arg1)` suffix combines the exact exhaustion
seek and exact terminal cleanup schedules and stops at `aRepairStart`. -/
theorem g1CS_aWalk_exhaust_terminal_trace_safe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r + g1AWalkTerminalSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
          (g1AWalkExhaustSteps r + g1AWalkTerminalSteps r) =
        g1AWalkRepairStartConfig r b v hj hv := by
  have hexhaust := g1CS_aWalk_exhaust_trace_safe r b v hj hv
  have hterminal0 := g1CS_aWalk_terminal_from_exhaust_trace_safe r b v hj hv
  have hterminal : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r)) (g1AWalkTerminalSteps r) :=
    G1RunSafe.transport hexhaust.2.symm hterminal0.1
  exact ⟨G1RunSafe.add hexhaust.1 hterminal, by
    rw [runConfig_add, hexhaust.2, hterminal0.2]⟩

/-! ## Full local and real-initial binary capstones -/

/-- All successful rounds followed by exhaustion are safe at the exact
`g1AWalkExhaustDriverSteps` schedule. -/
theorem g1CS_aWalk_exhaust_driver_trace_safe (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    G1RunSafe
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
            (hv 0 (by omega)))
          (g1AWalkExhaustDriverSteps r) =
        g1AWalkExhaustConfig r b (v r.arg1) hlen
          (hv r.arg1 (Nat.le_refl _)) := by
  have hdriver := g1CS_aWalk_driver_runSafe r b r.arg1 (Nat.le_refl _)
    hlen v hv
  have hexact := g1CS_aWalk_driver_exact r b r.arg1 (Nat.le_refl _)
    hlen v hv
  have hexhaust0 := g1CS_aWalk_exhaust_runSafe r b (v r.arg1) hlen
    (hv r.arg1 (Nat.le_refl _))
  have hexhaust : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))) (g1AWalkDriverSteps r r.arg1))
      (g1AWalkExhaustSteps r) :=
    G1RunSafe.transport hexact.symm hexhaust0
  exact ⟨by
      simpa [g1AWalkExhaustDriverSteps] using G1RunSafe.add hdriver hexhaust,
    g1CS_aWalk_exhaust_driver_exact r b hlen v hv⟩

/-- Full local safety through exhaustion and terminal cleanup, ending before
the live A-repair entry step. -/
theorem g1CS_aWalk_full_driver_trace_safe (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    G1RunSafe
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
            (hv 0 (by omega)))
          (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) =
        g1AWalkRepairStartConfig r b (v r.arg1) hlen
          (hv r.arg1 (Nat.le_refl _)) := by
  have hexhaust := g1CS_aWalk_exhaust_driver_trace_safe r b hlen v hv
  have hterminal0 := g1CS_aWalk_terminal_from_exhaust_trace_safe r b
    (v r.arg1) hlen (hv r.arg1 (Nat.le_refl _))
  have hterminal : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))) (g1AWalkExhaustDriverSteps r))
      (g1AWalkTerminalSteps r) :=
    G1RunSafe.transport hexhaust.2.symm hterminal0.1
  exact ⟨G1RunSafe.add hexhaust.1 hterminal,
    g1CS_aWalk_full_driver_exact r b hlen v hv⟩

/-- Successful binary real-initial safety on the existing schedule expression,
ending exactly at the cursor-free `aRepairStart` handoff. -/
theorem g1CS_readA_binary_full_driver_from_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (v : Nat → Bool) (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (hvals : r.vals = bA :: rest) (hv0 : v 0 = bA) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r +
          (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryCursorSteps r +
            (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) =
        g1AWalkRepairStartConfig r bB (v r.arg1) (by
          have h := hv r.arg1 (Nat.le_refl _)
          exact (List.getElem?_eq_some_iff.1 h).1)
          (hv r.arg1 (Nat.le_refl _)) := by
  have hlen : r.arg1 < r.vals.length := by
    have h := hv r.arg1 (Nat.le_refl _)
    exact (List.getElem?_eq_some_iff.1 h).1
  have hinstall := g1CS_readA_binary_install_from_initial_trace_safe r hc ht
    bA bB rest hB hvals
  have hsuffix0 := g1CS_aWalk_full_driver_trace_safe r bB hlen v hv
  have hsigma0 : TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ABinaryCursorSteps r) =
    g1AWalkConfig r bB 0 (Nat.zero_le _) (by omega) (v 0)
      (hv 0 (by omega)) := by
    subst bA
    exact hinstall.2.2
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r))
      (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) :=
    G1RunSafe.transport hsigma0.symm hsuffix0.1
  exact ⟨G1RunSafe.add hinstall.1 hsuffix, by
    rw [runConfig_add, hsigma0, hsuffix0.2]⟩

/-! ## Structural endpoint exports -/

private theorem g1APassADriver_count_data_spent (xs : List Bool) :
    (xs.map G1Frame.data).count .spent = 0 := by
  apply List.count_eq_zero.2
  intro h
  simp only [List.mem_map] at h
  obtain ⟨b, _, hb⟩ := h
  cases b <;> simp at hb

private theorem g1APassADriver_count_data_index (xs : List Bool) :
    (xs.map G1Frame.data).count .index = 0 := by
  apply List.count_eq_zero.2
  intro h
  simp only [List.mem_map] at h
  obtain ⟨b, _, hb⟩ := h
  cases b <;> simp at hb

private theorem g1APassADriver_count_replicate_ne
    (f g : G1Frame) (n : Nat) (hne : f ≠ g) :
    (List.replicate n g).count f = 0 := by
  apply List.count_eq_zero.2
  intro h
  exact hne (List.eq_of_mem_replicate h)

@[simp] theorem g1AWalkDoneFrames_count_spent (r : G1Request) :
    (g1AWalkDoneFrames r).count .spent = r.arg1 := by
  simp [g1AWalkDoneFrames, g1TagRouteFrames, g1AWalkOperand1,
    g1AWalkOperand2, List.count_append, g1APassADriver_count_data_spent,
    g1APassADriver_count_replicate_ne]

@[simp] theorem g1AWalkDoneFrames_count_index (r : G1Request) :
    (g1AWalkDoneFrames r).count .index = r.arg2 := by
  simp [g1AWalkDoneFrames, g1TagRouteFrames, g1AWalkOperand1,
    g1AWalkOperand2, List.count_append, g1APassADriver_count_data_index,
    g1APassADriver_count_replicate_ne]

set_option linter.unusedVariables false in
/-- Exact tape, head, control, context and field counts at the binary capstone. -/
theorem g1CS_readA_binary_full_driver_structure (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (v : Nat → Bool) (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (hvals : r.vals = bA :: rest) (hv0 : v 0 = bA) :
    let hlen : r.arg1 < r.vals.length := by
      have h := hv r.arg1 (Nat.le_refl _)
      exact (List.getElem?_eq_some_iff.1 h).1
    let out := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ABinaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r))
    out.tape = g1ListTape ((g1AWalkDoneFrames r).flatMap G1Frame.bits) ∧
      (out.head : Nat) = 4 * (g1AWalkCursor r r.arg1 + 1) ∧
      out.state.snd = g1State .aRepairStart .p0 false false false
        (g1AWalkCtx r bB (v r.arg1)) ∧
      out.state.snd.ctx = g1AWalkCtx r bB (v r.arg1) ∧
      out.state.snd.ctx.res = g1Residual r.tag bB ∧
      out.state.snd.ctx.vB = v r.arg1 ∧
      (g1AWalkDoneFrames r).count .cursor = 0 ∧
      (g1AWalkDoneFrames r).count .spent = r.arg1 ∧
      (g1AWalkDoneFrames r).count .index = r.arg2 ∧
      (g1AWalkOperand1 r r.arg1).count .spent = r.arg1 ∧
      (g1AWalkOperand1 r r.arg1).count .index = 0 ∧
      (g1AWalkOperand2 r).count .index = r.arg2 := by
  dsimp only
  have hcap := g1CS_readA_binary_full_driver_from_initial_trace_safe r hc ht
    bA bB rest hB v hv hvals hv0
  rw [hcap.2]
  exact ⟨rfl, rfl, rfl, rfl, g1AWalkCtx_res r bB (v r.arg1), rfl,
    g1AWalkDoneFrames_count_cursor r, g1AWalkDoneFrames_count_spent r,
    g1AWalkDoneFrames_count_index r, g1AWalkOperand1_count_spent r r.arg1,
    by simp, g1AWalkOperand2_count_index r⟩

/-! ## Literal multi-round schedule pins -/

namespace G1PassADriverTraceProbes

theorem literal_two_round_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
          (by decide) (by decide) false (by decide)) 106 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
            (by decide) (by decide) false (by decide)) 106 =
        g1AWalkConfig G1AWalkDriverExamples.reqDriver false 2
          (by decide) (by decide) false (by decide) := by
  simpa [g1AWalkDriverSteps, G1AWalkDriverExamples.reqDriver] using
    g1CS_aWalk_driver_trace_safe G1AWalkDriverExamples.reqDriver false 2
      (by decide) (by decide) (fun j => [false, true, false][j]!) (by decide)

theorem literal_exhaustion_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
          (by decide) (by decide) false (by decide)) 134 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
            (by decide) (by decide) false (by decide)) 134 =
        g1AWalkExhaustConfig G1AWalkDriverExamples.reqDriver false false
          (by decide) (by decide) := by
  simpa [g1AWalkExhaustDriverSteps, g1AWalkDriverSteps,
    g1AWalkExhaustSteps, G1AWalkDriverExamples.reqDriver] using
    g1CS_aWalk_exhaust_driver_trace_safe G1AWalkDriverExamples.reqDriver false
      (by decide) (fun j => [false, true, false][j]!) (by decide)

theorem literal_full_driver_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
          (by decide) (by decide) false (by decide)) 174 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
            (by decide) (by decide) false (by decide)) 174 =
        g1AWalkRepairStartConfig G1AWalkDriverExamples.reqDriver false false
          (by decide) (by decide) := by
  simpa [g1AWalkExhaustDriverSteps, g1AWalkDriverSteps,
    g1AWalkExhaustSteps, g1AWalkTerminalSteps,
    G1AWalkDriverExamples.reqDriver] using
    g1CS_aWalk_full_driver_trace_safe G1AWalkDriverExamples.reqDriver false
      (by decide) (fun j => [false, true, false][j]!) (by decide)

end G1PassADriverTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
