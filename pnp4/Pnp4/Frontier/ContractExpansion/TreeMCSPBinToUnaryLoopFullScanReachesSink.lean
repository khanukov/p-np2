import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanHstep
import Pnp4.Frontier.ContractExpansion.TreeMCSPCounterLowestBit

/-!
# `binToUnaryLoopFullScan` — `reachesSink`: the sound loop halts (NP-verifier track — D2t-3 `ε`)

The loop-termination half of `ε`, **proven**: the sound binary→unary loop reaches its sink (halts) on
every valid layout.  This module fixes the back-edge tools + the **loop layout invariant**, the
per-iteration lemma `binToUnaryLoopFullScan_oneIteration`, and the headline
`binToUnaryLoopFullScan_reachesSink`.

`loopUntilSink_stepConfig_loop_tape` — the loop's back-edge (`B`'s accept → `B`'s start) **preserves the
tape** (the re-entry writes the scanned bit back). With `loopUntilSink_stepConfig_loop_{phase,head}` this
characterises the back-edge fully (phase → start, head/tape unchanged), so the per-iteration counter value
after re-entry equals the body pass's output.

`LoopLayout w c u` — the **U-LEFT layout invariant**: the loop is at the start phase with the head on the
sentinel `HOME`, `U = 1^u` occupies `[HOME-u, HOME)`, everything strictly left of `U` is blank, and the
**room invariant** `u + counterValue B ≤ HOME - 1` holds (so `U` can keep growing left as `B` shrinks).
One body pass (`binToUnaryLoopFullScan_runConfig_bodyPass`) maps `LoopLayout w c u` with `B > 0` to
`LoopLayout w c' (u+1)` with `counterValue B' = counterValue B - 1` (the borrow decrements `B`, the append
extends `U`; `u + counterValue` is preserved, so the room invariant survives). The standard library
combinator `loopUntilSink_reachesSink` cannot be applied directly — it quantifies its `hstep`/`hbase` over
*all* start-phase configs, but the run behaviour holds only on layouts — so termination is a **bespoke
strong induction on `counterValue B`** carrying `LoopLayout`, discharging the `B = 0` base from
`binToUnaryLoopFullScan_runConfig_hbase` and the `B > 0` step from `…_bodyPass` + the back-edge tools here.

Everything below is hole-free and axiom-clean.  With this, the loop's run behaviour is fully settled
(`B = 0 → sink` via `hbase`; `B > 0 →` decrement-and-loop via `oneIteration`; termination via
`reachesSink`).  The `ζ` correctness bridge (`|U| = value B = (decodeFin …).val`) is the remaining
follow-up before `ε` is fully closed.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- **Back-edge tape preservation.**  A step from `B`'s accept phase (the `loopUntilSink` re-entry) leaves
the tape unchanged — it writes the scanned bit back.  Completes the back-edge characterisation alongside
`loopUntilSink_stepConfig_loop_{phase,head}`. -/
theorem loopUntilSink_stepConfig_loop_tape (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    {L : Nat} (c : Configuration (M := (loopUntilSink B sink).toPhased.toTM) L) {s : Unit}
    (hstate : c.state = ⟨B.acceptPhase, s⟩) :
    (TM.stepConfig (M := (loopUntilSink B sink).toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (loopUntilSink B sink) c hstate]
  have hbit : ((loopUntilSink B sink).transition B.acceptPhase s (c.tape c.head)).2.2.1
      = c.tape c.head := by rw [loopUntilSink_transition_loop]
  rw [hbit]; funext j; by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### The back-edge on the sound loop machine, directly (avoiding the expensive `loopUntilSink` defeq)

The generic `loopUntilSink_stepConfig_loop_*` lemmas can be applied to a `binToUnaryLoopFullScan` config
only through the `binToUnaryLoopFullScan ≡ loopUntilSink …` defeq, whose `whnf` blows up (it unfolds the
loop's transition, which contains `bZeroFullScan`'s `2^i`).  These FullScan-specific versions instead use
the cheap one-`delta` unfold at the *transition* level (`binToUnaryLoopFullScan_transition_backedge`) plus
the `binToUnaryLoopFullScan`-stated `toTM_stepConfig_*`, exactly the device of
`binToUnaryLoopFullScan_transition_body`. -/

/-- **Transition-level back-edge.**  At the loop body's accept phase `w + 29`, the loop jumps to the body's
start phase (writing the scanned bit back, head stay). -/
theorem binToUnaryLoopFullScan_transition_backedge (w : Nat)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} (hi : (i : Nat) = w + 29) (s : Unit) (b : Bool) :
    (binToUnaryLoopFullScan w).transition i s b
      = ((binToUnaryLoopBodyFullScan w).startPhase, (), b, Move.stay) := by
  have hacc : i = (binToUnaryLoopBodyFullScan w).acceptPhase :=
    Fin.ext (by rw [hi, binToUnaryLoopBodyFullScan_acceptPhase_val])
  rw [hacc]
  exact loopUntilSink_transition_loop (binToUnaryLoopBodyFullScan w)
    ⟨w + 2, by rw [binToUnaryLoopBodyFullScan_numPhases]; omega⟩ s b

/-- **Back-edge step, phase.**  From phase `w + 29` the loop re-enters at the start phase `0`. -/
theorem binToUnaryLoopFullScan_backedge_phase (w : Nat) {L : Nat}
    (cF : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 29) (hstate : cF.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cF).state).fst.val = 0 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) cF hstate,
      binToUnaryLoopFullScan_transition_backedge w hi s (cF.tape cF.head)]
  show ((binToUnaryLoopBodyFullScan w).startPhase : Nat) = 0
  exact binToUnaryLoopFullScan_startPhase_val w

/-- **Back-edge step, head.**  The re-entry leaves the head where the body finished (a `Move.stay`). -/
theorem binToUnaryLoopFullScan_backedge_head (w : Nat) {L : Nat}
    (cF : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 29) (hstate : cF.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cF).head = cF.head := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) cF hstate]
  have hmove : ((binToUnaryLoopFullScan w).transition i s (cF.tape cF.head)).2.2.2 = Move.stay := by
    rw [binToUnaryLoopFullScan_transition_backedge w hi s (cF.tape cF.head)]
  rw [hmove]; simp [Configuration.moveHead]

/-- **Back-edge step, tape.**  The re-entry writes the scanned bit back, leaving the tape unchanged. -/
theorem binToUnaryLoopFullScan_backedge_tape (w : Nat) {L : Nat}
    (cF : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 29) (hstate : cF.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cF).tape = cF.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) cF hstate]
  have hbit : ((binToUnaryLoopFullScan w).transition i s (cF.tape cF.head)).2.2.1 = cF.tape cF.head := by
    rw [binToUnaryLoopFullScan_transition_backedge w hi s (cF.tape cF.head)]
  rw [hbit]; funext j; by_cases hj : j = cF.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- **The loop layout invariant.**  At the loop start phase `0` with the head on the sentinel `HOME`,
`U = 1^u` occupying `[HOME-u, HOME)` (`u ≥ 1`, the permanent endmarker seed is the rightmost `U` cell),
everything strictly left of `U` blank, the width-`w` counter window fitting, and the **room invariant**
`u + counterValue B ≤ HOME - 1` (so `U` keeps room to grow as `B` shrinks).  One body pass maps this to the
same invariant with `u ↦ u+1` and `counterValue B ↦ counterValue B - 1`. -/
def LoopLayout (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat) : Prop :=
  (c.state.fst : Nat) = 0
  ∧ 1 ≤ u
  ∧ 1 ≤ (c.head : Nat)
  ∧ (c.head : Nat) + 3 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L
  ∧ c.tape c.head = false
  ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c.head : Nat) - u ≤ (q : Nat) → (q : Nat) < (c.head : Nat) → c.tape q = true)
  ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) < (c.head : Nat) - u → c.tape q = false)
  ∧ u + counterValue c ((c.head : Nat) + 1) w ≤ (c.head : Nat) - 1

/-! ### One layout-preserving loop iteration, and the loop-termination proof -/

set_option maxHeartbeats 1600000 in
theorem binToUnaryLoopFullScan_oneIteration (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat)
    (hL : LoopLayout w c u)
    (hpos : counterValue c ((c.head : Nat) + 1) w ≠ 0) :
    ∃ sB, ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)).state.fst : Nat) = 0
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)).head : Nat) = (c.head : Nat)
      ∧ LoopLayout w (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)) (u + 1)
      ∧ counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1))
            ((c.head : Nat) + 1) w + 1 = counterValue c ((c.head : Nat) + 1) w := by
  obtain ⟨hph0, hu1, hHOME1, hbound, hsent, hUlay, hblank, hroom⟩ := hL
  obtain ⟨j, hjw, hzeros, hone⟩ := counterValue_pos_imp_lowestBit c ((c.head : Nat) + 1) w hpos
  obtain ⟨hPp, hPh⟩ := binToUnaryLoopFullScan_runConfig_pos w c hph0 j hjw (by omega) hzeros hone
  have hPt := binToUnaryLoopFullScan_runConfig_pos_tape w c hph0 j hjw (by omega) hzeros hone
  set cP := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (j + 3) with hcPdef
  obtain ⟨hQp, hQh, hQt⟩ := binToUnaryLoopFullScan_runConfig_postDivert w cP hPp (by rw [hPh]; omega)
  set cQ := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cP 3 with hcQdef
  have hQt' : cQ.tape = c.tape := hQt.trans hPt
  have hQh' : (cQ.head : Nat) = (c.head : Nat) + 2 + j := by omega
  obtain ⟨hRp, hRh, hRt⟩ := binToUnaryLoopFullScan_seek_home w cQ (c.head : Nat) j hQp hHOME1 hQh'
    (by omega)
    (by intro q hq1 hq2; rw [hQt']
        rcases Nat.lt_or_ge (q : Nat) ((c.head : Nat) + 1) with hlt | hge
        · have heq : (q : Nat) = (c.head : Nat) := by omega
          rw [show q = c.head from Fin.ext heq]; exact hsent
        · exact hzeros q hge (by omega))
    (by intro q hq; rw [hQt']; exact hUlay q (by omega) (by omega))
  set cR := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cQ (j + 10) with hcRdef
  have hRt' : cR.tape = c.tape := hRt.trans hQt'
  have hRh' : (cR.head : Nat) = (c.head : Nat) := hRh
  have hRsent : cR.tape cR.head = false := by
    rw [hRt']; rw [show cR.head = c.head from Fin.ext hRh']; exact hsent
  have hZ : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (cR.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (cR.head : Nat) + 1 + j → cR.tape p = false := by
    intro p hp1 hp2; rw [hRt']; exact hzeros p (by rw [hRh'] at hp1; omega) (by rw [hRh'] at hp2; omega)
  have hO : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (cR.head : Nat) + 1 + j → cR.tape p = true := by
    intro p hp; rw [hRt']; exact hone p (by rw [hRh'] at hp; omega)
  have hUU : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (cR.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (cR.head : Nat) → cR.tape p = true := by
    intro p hp1 hp2; rw [hRt']; exact hUlay p (by rw [hRh'] at hp1; omega) (by rw [hRh'] at hp2; omega)
  have hUb : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (cR.head : Nat) - u - 1 → cR.tape p = false := by
    intro p hp; rw [hRt']; exact hblank p (by rw [hRh'] at hp; omega)
  have hUfitR : u + 1 ≤ (cR.head : Nat) := by rw [hRh']; omega
  obtain ⟨hFp, hFh, hFt⟩ := binToUnaryLoopFullScan_body_runConfig_onePass w cR hRp j
    (by rw [hRh']; omega) hZ hO hRsent (by rw [hRh']; omega) u hUfitR hUU hUb
  have hMeasure := binToUnaryLoopFullScan_body_onePass_counterValue w cR hRp j
    (by rw [hRh']; omega) hZ hO hRsent (by rw [hRh']; omega) u hUfitR hUU hUb hjw (by rw [hRh']; omega)
  set sB := (j + 3) + 3 + (j + 10) + onePassSteps j u with hsBdef
  have hcF : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB
      = TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cR (onePassSteps j u) := by
    rw [hsBdef, hcRdef, hcQdef, hcPdef, ← TM.runConfig_add, ← TM.runConfig_add, ← TM.runConfig_add]
    congr 1; omega
  have hFp' : ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB).state.fst : Nat) = w + 29 := by
    rw [hcF]; exact hFp
  have hFh' : ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB).head : Nat) = (c.head : Nat) := by
    rw [hcF]; exact hFh.trans hRh'
  have hFtape : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB).tape p
        = (if (p : Nat) = (c.head : Nat) - u - 1 then true
          else if (c.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c.head : Nat) + 1 + j then true
          else if (p : Nat) = (c.head : Nat) + 1 + j then false else c.tape p) := by
    intro p; rw [hcF, hFt p, hRt', hRh']
  have hcounterF : counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB)
        ((c.head : Nat) + 1) w + 1 = counterValue c ((c.head : Nat) + 1) w := by
    rw [show ((cR.head : Nat) + 1) = ((c.head : Nat) + 1) from by rw [hRh']] at hMeasure
    rw [hcF, hMeasure]
    exact counterValue_eq_of_tape_eq cR c ((c.head : Nat) + 1) w (fun p _ _ => by rw [hRt'])
  -- back-edge facts on runConfig c (sB+1) = stepConfig (runConfig c sB)
  have hbe_phase : ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)).state.fst : Nat) = 0 := by
    rw [TM.runConfig_succ]
    exact binToUnaryLoopFullScan_backedge_phase w (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB)
      (i := _) (s := _) hFp' rfl
  have hbe_head : ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)).head : Nat) = (c.head : Nat) := by
    rw [TM.runConfig_succ,
      binToUnaryLoopFullScan_backedge_head w (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB)
        (i := _) (s := _) hFp' rfl]
    exact hFh'
  have hbe_tape : (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)).tape
      = (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB).tape := by
    rw [TM.runConfig_succ]
    exact binToUnaryLoopFullScan_backedge_tape w (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB)
      (i := _) (s := _) hFp' rfl
  have hbe_hfin : (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1)).head = c.head :=
    Fin.ext hbe_head
  refine ⟨sB, hbe_phase, hbe_head, ⟨hbe_phase, by omega, by rw [hbe_head]; omega, by rw [hbe_head]; omega, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- sentinel
    rw [hbe_tape, hbe_hfin, hFtape c.head]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact hsent
  · -- U' = 1^(u+1)
    intro q hq1 hq2; rw [hbe_head] at hq1 hq2
    rw [hbe_tape, hFtape q]
    by_cases hqe : (q : Nat) = (c.head : Nat) - u - 1
    · rw [if_pos hqe]
    · rw [if_neg hqe, if_neg (by omega), if_neg (by omega)]; exact hUlay q (by omega) (by omega)
  · -- blank'
    intro q hq; rw [hbe_head] at hq
    rw [hbe_tape, hFtape q, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hblank q (by omega)
  · -- room invariant
    rw [hbe_head]
    have hcD : counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1))
        ((c.head : Nat) + 1) w = counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB)
          ((c.head : Nat) + 1) w :=
      counterValue_eq_of_tape_eq _ _ ((c.head : Nat) + 1) w (fun p _ _ => by rw [hbe_tape])
    rw [hcD]; omega
  · -- counter decrease
    have hcD : counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1))
        ((c.head : Nat) + 1) w = counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c sB)
          ((c.head : Nat) + 1) w :=
      counterValue_eq_of_tape_eq _ _ ((c.head : Nat) + 1) w (fun p _ _ => by rw [hbe_tape])
    rw [hcD]; exact hcounterF


/-- **The sound binary→unary loop halts.**  From any `LoopLayout` config, the loop reaches its sink phase
`w + 2` (the `B = 0` outcome): bespoke strong induction on `counterValue B`, base `B = 0` from `hbase`,
step `B > 0` from `oneIteration` (one pass drops the counter and re-establishes the layout). -/
theorem binToUnaryLoopFullScan_reachesSink (w : Nat) {L : Nat} :
    ∀ (m : Nat) (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat),
      LoopLayout w c u → counterValue c ((c.head : Nat) + 1) w = m →
      ∃ t, ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).state.fst : Nat) = w + 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c u hL hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · obtain ⟨hph0, _, _, hbound, _, _, _, _⟩ := hL
      exact ⟨2 + w, binToUnaryLoopFullScan_runConfig_hbase w c hph0 (by omega) (by rw [hm]; exact hm0)⟩
    · obtain ⟨sB, _, hhd, hLnext, hdec⟩ :=
        binToUnaryLoopFullScan_oneIteration w c u hL (by rw [hm]; omega)
      set d := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1) with hddef
      have hmlt : counterValue d ((d.head : Nat) + 1) w < m := by
        rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
      obtain ⟨t, ht⟩ := ih (counterValue d ((d.head : Nat) + 1) w) hmlt d (u + 1) hLnext rfl
      exact ⟨(sB + 1) + t, by rw [TM.runConfig_add, ← hddef]; exact ht⟩

end ContractExpansion
end Frontier
end Pnp4
