import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanBodyStep

/-!
# `(binToUnaryLoopFullScan w)` body lift — run-through, the `onePass` HOME→HOME engine (NP-verifier track — D2t-3 `ε`)

`hstep`'s body leg.  Building on the single steps (`TreeMCSPBinToUnaryLoopFullScanBodyStep.lean`), this
module composes all seven `binToUnaryBody` elements into the full one-pass engine **directly on the loop
machine** at offset `+15`, mirroring `binToUnaryBody`'s `lead2 → afterDecrement → … → afterScanRight7 →
onePass` segments (identical tape predicates — they depend only on head positions, which are unchanged —
and step counts; only the phases shift `+15` and the machine becomes `(binToUnaryLoopFullScan w)`).

From HOME (phase `15`, head on the sentinel) with `B`'s lowest set bit at offset `j` and `U = 1^u` to the
left, one pass: `stepRight` onto `b₀`, **decrement** `B` (borrow-flip the `j` low zeros to `1`, clear bit
`j`), `stepLeft`, **scanLeft** back over the flipped run to the sentinel, `stepLeft` onto `U`'s right end,
**append** a fresh `1` at `U`'s left boundary `head−u−1`, **scanRight** back over the now-`u+1`-long `U`
to the sentinel — reaching the loop body's **accept phase `29`** (the `loopUntilSink` back-edge target)
with the head **back at HOME** and the tape holding `(B − 1, 1^(u+1))`.

The four scan inductions (`binToUnaryLoopFullScan_body_{decrement,scanLeft,append,scanRight}_scanning`) are
re-derived from this module's bit-conditional single steps; the segment lemmas chain them with the
moves/handoffs up to the headline `binToUnaryLoopFullScan_body_runConfig_onePass`.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Lead-in: `stepRight` onto `B`'s low cell (phases `15 → 17`) -/

/-- From HOME (phase `15`, head on the sentinel), after `2` steps the loop is at phase `17` (the decrement
start), head advanced one cell right onto `B`'s low cell `b₀`, tape unchanged. -/
theorem binToUnaryLoopFullScan_body_runConfig_lead2 (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (hbnd : (c0.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2).state).fst : Nat) = w + 17
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2).tape = c0.tape := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  obtain ⟨h1p, h1h, h1t⟩ := binToUnaryLoopFullScan_body_w15 w c0 (i := c0.state.fst) (s := c0.state.snd)
    hphase rfl hbnd
  set c1 := TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 with hc1
  clear_value c1
  obtain ⟨h2p, h2h, h2t⟩ := binToUnaryLoopFullScan_body_w16 w c1 (i := c1.state.fst) (s := c1.state.snd)
    h1p rfl
  exact ⟨h2p, by rw [h2h, h1h], by rw [h2t, h1t]⟩

/-! ### Element 1 — decrement: the borrow scan (phase `17`) -/

/-- **Decrement borrow scan.**  From phase `17` with the `k` cells `[head, head + k)` all `0`, after any
`m ≤ k` borrow steps the loop is still in phase `17`, the head has advanced `m` cells right, and those `m`
cells are flipped to `1` (tape elsewhere unchanged).  Re-derived from `step17_zero`. -/
theorem binToUnaryLoopFullScan_body_decrement_scanning (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = w + 17)
    (k : Nat) (hbnd : (c0.head : Nat) + k < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) :
    ∀ m, m ≤ k →
      (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m).state).fst : Nat) = w + 17
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m).head : Nat) = (c0.head : Nat) + m
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m).tape p
            = (if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + m then true
                else c0.tape p) := by
  intro m
  induction m with
  | zero => intro _; refine ⟨hstart, by simp, ?_⟩; intro p; simp
  | succ m ih =>
      intro hm
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m).tape
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m).head = false := by
        rw [htp, hhd]
        rw [if_neg (by omega)]
        exact hzeros _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd' : ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m).head : Nat) + 1
          < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L := by rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 m with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w17_zero w c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hbnd'
      refine ⟨sp, by rw [sh, hhd]; omega, ?_⟩
      intro p
      rw [st]
      by_cases hjp : p = c.head
      · subst hjp; rw [Configuration.write, dif_pos rfl, hhd, if_pos ⟨by omega, by omega⟩]
      · rw [Configuration.write, dif_neg hjp, htp p]
        by_cases hlo : (c0.head : Nat) ≤ (p : Nat)
        · by_cases hhi : (p : Nat) < (c0.head : Nat) + m
          · rw [if_pos ⟨hlo, hhi⟩, if_pos ⟨hlo, by omega⟩]
          · rw [if_neg (by tauto), if_neg ?_]
            have : (p : Nat) ≠ (c0.head : Nat) + m := by
              intro he; apply hjp; apply Fin.ext; rw [hhd]; omega
            rintro ⟨_, hcontra⟩; omega
        · rw [if_neg (by tauto), if_neg (by tauto)]

/-- **After the decrement** (phases `15 → 18`).  From HOME with `B`'s low cells `[head+1, head+1+j)` all
`0` and cell `head+1+j` set (`j` = lowest set bit), after `2 + (j + 1)` steps the loop is at phase `18`
(decrement accept), head on the cleared cell `head+1+j`, and `B`'s low `j` cells flipped to `1` with cell
`head+1+j` cleared.  Composes `lead2` + the borrow scan + the read-`1` stop step. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterDecrement (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1))).state).fst : Nat) = w + 18
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1))).head : Nat)
          = (c0.head : Nat) + 1 + j
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1))).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hLp, hLh, hLt⟩ := binToUnaryLoopFullScan_body_runConfig_lead2 w c0 hphase (by omega)
  rw [show (2 + (j + 1)) = 2 + j + 1 from by omega, TM.runConfig_succ, TM.runConfig_add]
  -- Scan the j zeros from `runConfig c0 2` (phase 17, head c0.head+1).
  obtain ⟨hSp, hSh, hSt⟩ := binToUnaryLoopFullScan_body_decrement_scanning w
    (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2) hLp j
    (by rw [hLh]; omega)
    (by
      intro p hp1 hp2; rw [hLt]
      exact h_zeros p (by rw [hLh] at hp1; omega) (by rw [hLh] at hp2; omega)) j (le_refl j)
  set cS := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM)
      (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2) j with hcS
  have hSp' : (cS.state.fst : Nat) = w + 17 := hSp
  have hSh' : (cS.head : Nat) = (c0.head : Nat) + 1 + j := by rw [hcS, hSh, hLh]
  have hSt' : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L), cS.tape p
      = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
          else c0.tape p) := by
    intro p; rw [hcS, hSt p, hLh, hLt]
  clear_value cS
  have hbitS : cS.tape cS.head = true := by
    rw [hSt', if_neg (by rw [hSh']; omega)]; exact h_one cS.head hSh'
  obtain ⟨q1p, q1h, q1t⟩ := binToUnaryLoopFullScan_body_w17_one w cS
    (i := cS.state.fst) (s := cS.state.snd) hSp' rfl hbitS
  refine ⟨q1p, by rw [q1h, hSh'], ?_⟩
  intro p
  rw [q1t]
  by_cases hjp : p = cS.head
  · subst hjp; rw [Configuration.write, dif_pos rfl, hSh', if_neg (by omega), if_pos rfl]
  · rw [Configuration.write, dif_neg hjp, hSt' p]
    by_cases hlo : (c0.head : Nat) + 1 ≤ (p : Nat)
    · by_cases hhi : (p : Nat) < (c0.head : Nat) + 1 + j
      · rw [if_pos ⟨hlo, hhi⟩, if_pos ⟨hlo, hhi⟩]
      · rw [if_neg (by tauto), if_neg (by tauto), if_neg ?_]
        have : (p : Nat) ≠ (c0.head : Nat) + 1 + j := by
          intro he; apply hjp; apply Fin.ext; rw [hSh']; omega
        omega
    · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by omega)]

/-- **After the decrement handoff** (phases `15 → 19`): one more step hands off out of the decrement to
`stepLeft` (element 2, phase `19`); head still on the cleared cell, tape the decremented pattern. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterDecrHandoff (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1)).state).fst : Nat) = w + 19
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1)).head : Nat)
          = (c0.head : Nat) + 1 + j
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hAp, hAh, hAt⟩ := binToUnaryLoopFullScan_body_runConfig_afterDecrement w c0 hphase j hj h_zeros h_one
  rw [TM.runConfig_succ]
  set cA := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1)) with hcA
  clear_value cA
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w18 w cA (i := cA.state.fst) (s := cA.state.snd) hAp rfl
  exact ⟨sp, by rw [sh, hAh], by intro p; rw [st]; exact hAt p⟩

/-- **After `stepLeft` (element 2)** (phases `15 → 20`): one left step off the cleared cell, reaching phase
`20`; head `head + j` (on `B`'s flipped run), tape unchanged. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterStepLeft3 (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1)).state).fst : Nat) = w + 20
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterDecrHandoff w c0 hphase j hj h_zeros h_one
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w19 w cH (i := cH.state.fst) (s := cH.state.snd)
    hHp rfl (by rw [hHh]; omega)
  exact ⟨sp, by rw [sh, hHh]; omega, by intro p; rw [st]; exact hHt p⟩

/-- **After the `stepLeft`→scanLeft handoff** (phases `15 → 21`): hands off into `selfLoopScanLeftOne`
(element 3, phase `21`); head `head + j`, tape unchanged. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterStepLeft3Handoff (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)).state).fst : Nat) = w + 21
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ := binToUnaryLoopFullScan_body_runConfig_afterStepLeft3 w c0 hphase j hj h_zeros h_one
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w20 w cH (i := cH.state.fst) (s := cH.state.snd) hHp rfl
  exact ⟨sp, by rw [sh, hHh], by intro p; rw [st]; exact hHt p⟩

/-! ### Element 3 — scanLeft: the leftward scan back to the sentinel (phase `21`) -/

/-- **ScanLeft scan.**  From phase `21` with the `m` cells `(head − m, head]` all `1`, after any `k ≤ m`
steps the loop is still in phase `21`, the head has retreated `k` cells left, and the tape is unchanged
(a scan writes the `1` back).  Re-derived from `step21_one`. -/
theorem binToUnaryLoopFullScan_body_scanLeft_scanning (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = w + 21)
    (m : Nat) (hm : m ≤ (c0.head : Nat))
    (hones : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - m < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) :
    ∀ k, k ≤ m →
      (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).state).fst : Nat) = w + 21
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hstart, by simp, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head = true := by
        rw [htp]; exact hones _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hhead : 0 < ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat) := by
        rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w21_one w c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hhead
      exact ⟨sp, by rw [sh, hhd]; omega, by rw [st, htp]⟩

/-- **After scanLeft (element 3)** (phases `15 → 22`).  From HOME the leftward scan retraces `B`'s flipped
`1`-run (`j` cells) and stops on the sentinel, reaching phase `22` with the head **back at HOME**; tape
the decremented pattern.  Composes `afterStepLeft3Handoff` + the scanLeft scan (`j` steps) + the read-`0`
stop on the sentinel. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterScanLeft4 (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1))).state).fst : Nat) = w + 22
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1))).head : Nat)
          = (c0.head : Nat)
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1))).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ := binToUnaryLoopFullScan_body_runConfig_afterStepLeft3Handoff w c0 hphase j hj h_zeros h_one
  rw [show (2 + (j + 1) + 1 + 1 + 1 + (j + 1)) = (2 + (j + 1) + 1 + 1 + 1) + j + 1 from by omega,
    TM.runConfig_succ, TM.runConfig_add]
  obtain ⟨hSp, hSh, hSt⟩ := binToUnaryLoopFullScan_body_scanLeft_scanning w
    (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)) hHp j
    (by rw [hHh]; omega)
    (by
      intro p hp1 hp2
      rw [hHt p, if_pos ⟨by rw [hHh] at hp1; omega, by rw [hHh] at hp2; omega⟩]) j (le_refl j)
  set cS := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM)
      (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)) j with hcS
  have hSp' : (cS.state.fst : Nat) = w + 21 := hSp
  have hSh' : (cS.head : Nat) = (c0.head : Nat) := by rw [hSh, hHh]; omega
  clear_value cS
  have hbitS : cS.tape cS.head = false := by
    have hfeq : cS.head = c0.head := Fin.ext hSh'
    rw [hSt, hfeq, hHt c0.head, if_neg (by omega), if_neg (by omega)]; exact h_sentinel
  obtain ⟨q0p, q0h, q0t⟩ := binToUnaryLoopFullScan_body_w21_zero w cS
    (i := cS.state.fst) (s := cS.state.snd) hSp' rfl hbitS
  refine ⟨q0p, by rw [q0h, hSh'], ?_⟩
  intro p; rw [q0t, hSt]; exact hHt p

/-- **After the scanLeft → stepLeft handoff** (phases `15 → 23`): hands off into the second home-seek
`stepLeft` (element 4, phase `23`); head at HOME, tape the decremented pattern. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterScanLeft4Handoff (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1)).state).fst : Nat) = w + 23
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1)).head : Nat)
          = (c0.head : Nat)
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterScanLeft4 w c0 hphase j hj h_zeros h_one h_sentinel
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1)) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w22 w cH (i := cH.state.fst) (s := cH.state.snd) hHp rfl
  exact ⟨sp, by rw [sh, hHh], by intro p; rw [st]; exact hHt p⟩

/-- **After `stepLeft` (element 4)** (phases `15 → 24`): one left step off the sentinel onto `U`'s right
end, reaching phase `24`; head `head − 1`, tape unchanged.  Requires `0 < head` (the U-left layout
invariant: HOME has at least a blank to its left). -/
theorem binToUnaryLoopFullScan_body_runConfig_afterStepLeft5 (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat)) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1)).state).fst : Nat) = w + 24
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1)).head : Nat)
          = (c0.head : Nat) - 1
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterScanLeft4Handoff w c0 hphase j hj h_zeros h_one h_sentinel
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w23 w cH (i := cH.state.fst) (s := cH.state.snd)
    hHp rfl (by rw [hHh]; omega)
  exact ⟨sp, by rw [sh, hHh], by intro p; rw [st]; exact hHt p⟩

/-- **After the `stepLeft` → append handoff** (phases `15 → 25`): hands off into `selfLoopAppendLeftOne`
(element 5, phase `25`, the append start); head at `U`'s right end `head − 1`, tape the decremented
pattern.  This is the headline of the `B`-decrement half — `B` is decremented, the head is positioned to
append a `1` to `U`. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterStepLeft5Handoff (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat)) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1)).state).fst : Nat) = w + 25
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1)).head : Nat)
          = (c0.head : Nat) - 1
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterStepLeft5 w c0 hphase j hj h_zeros h_one h_sentinel hHOME
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w24 w cH (i := cH.state.fst) (s := cH.state.snd) hHp rfl
  exact ⟨sp, by rw [sh, hHh], by intro p; rw [st]; exact hHt p⟩

/-! ### Element 5 — append: the leftward scan over `U` + the appended `1` (phase `25`) -/

/-- **Append scan.**  From phase `25` with the `m` cells `(head − m, head]` all `1`, after any `k ≤ m`
steps the loop is still in phase `25`, the head has retreated `k` cells left, and the tape is unchanged
(the append writes each scanned `1` back unchanged).  Re-derived from `step25_one`. -/
theorem binToUnaryLoopFullScan_body_append_scanning (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = w + 25)
    (m : Nat) (hm : m ≤ (c0.head : Nat))
    (hones : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - m < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) :
    ∀ k, k ≤ m →
      (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).state).fst : Nat) = w + 25
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hstart, by simp, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head = true := by
        rw [htp]; exact hones _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hhead : 0 < ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat) := by
        rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w25_one w c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hhead
      exact ⟨sp, by rw [sh, hhd]; omega, by rw [st, htp]⟩

/-- **After append (element 5)** (phases `15 → 26`).  From `U`'s right end the leftward append scans over
`U`'s `u` `1`s and writes a fresh `1` at `U`'s left `0`-boundary `head − u − 1`, extending `U` to `u + 1`.
After `2 + (j+1) + 1 + 1 + 1 + (j+1) + 1 + 1 + 1 + (u + 1)` steps the loop is at phase `26` (append accept),
head on the new cell `head − u − 1`, tape the decremented `B` pattern **plus** the appended `1`. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterAppend6 (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - u - 1 → c0.tape p = false) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1))).state).fst : Nat) = w + 26
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1))).head : Nat)
          = (c0.head : Nat) - u - 1
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1))).tape p
            = (if (p : Nat) = (c0.head : Nat) - u - 1 then true
                else if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterStepLeft5Handoff w c0 hphase j hj h_zeros h_one h_sentinel hHOME
  rw [show (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1))
        = (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1) + u + 1 from by omega,
    TM.runConfig_succ, TM.runConfig_add]
  obtain ⟨hSp, hSh, hSt⟩ := binToUnaryLoopFullScan_body_append_scanning w
    (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1)) hHp u
    (by rw [hHh]; omega)
    (by
      intro p hp1 hp2
      rw [hHt p, if_neg (by rw [hHh] at hp2; omega), if_neg (by rw [hHh] at hp2; omega)]
      exact hU p (by rw [hHh] at hp1; omega) (by rw [hHh] at hp2; omega)) u (le_refl u)
  set cS := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM)
      (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1)) u with hcS
  have hSp' : (cS.state.fst : Nat) = w + 25 := hSp
  have hSh' : (cS.head : Nat) = (c0.head : Nat) - u - 1 := by rw [hSh, hHh]; omega
  clear_value cS
  have hbitS : cS.tape cS.head = false := by
    rw [hSt, hHt cS.head, if_neg (by rw [hSh']; omega), if_neg (by rw [hSh']; omega)]
    exact hUboundary cS.head hSh'
  obtain ⟨q0p, q0h, q0t⟩ := binToUnaryLoopFullScan_body_w25_zero w cS
    (i := cS.state.fst) (s := cS.state.snd) hSp' rfl hbitS
  refine ⟨q0p, by rw [q0h, hSh'], ?_⟩
  intro p
  rw [q0t]
  by_cases hjp : p = cS.head
  · subst hjp; rw [Configuration.write, dif_pos rfl, if_pos hSh']
  · rw [Configuration.write, dif_neg hjp, hSt]
    have hpn : (p : Nat) ≠ (c0.head : Nat) - u - 1 := by
      intro he; apply hjp; apply Fin.ext; rw [hSh']; omega
    rw [if_neg hpn]; exact hHt p

/-- **After the append → scanRight handoff** (phases `15 → 27`): hands off into `selfLoopScanRightOne`
(element 6, phase `27`); head on `U`'s new left end `head − u − 1`, tape the `U`-extended pattern. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterAppend6Handoff (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - u - 1 → c0.tape p = false) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1)).state).fst : Nat) = w + 27
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1)).head : Nat)
          = (c0.head : Nat) - u - 1
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1)).tape p
            = (if (p : Nat) = (c0.head : Nat) - u - 1 then true
                else if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterAppend6 w c0 hphase j hj h_zeros h_one h_sentinel hHOME u hUfit hU hUboundary
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1)) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w26 w cH (i := cH.state.fst) (s := cH.state.snd) hHp rfl
  exact ⟨sp, by rw [sh, hHh], by intro p; rw [st]; exact hHt p⟩

/-! ### Element 6 — scanRight: the rightward scan back to the sentinel (phase `27`) -/

/-- **ScanRight scan.**  From phase `27` with the `m` cells `[head, head + m)` all `1`, after any `k ≤ m`
steps the loop is still in phase `27`, the head has advanced `k` cells right, and the tape is unchanged.
Re-derived from `step27_one`. -/
theorem binToUnaryLoopFullScan_body_scanRight_scanning (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = w + 27)
    (m : Nat) (hbnd : (c0.head : Nat) + m < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + m → c0.tape p = true) :
    ∀ k, k ≤ m →
      (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).state).fst : Nat) = w + 27
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hstart, by simp, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head = true := by
        rw [htp]; exact hones _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd' : ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat) + 1
          < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L := by rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w27_one w c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hbnd'
      exact ⟨sp, by rw [sh, hhd]; omega, by rw [st, htp]⟩

/-- **After scanRight (element 6)** (phases `15 → 28`).  From `U`'s new left end the rightward scan
retraces the now-`u+1`-long unary block and stops back on the sentinel, reaching phase `28` with the head
**back at HOME**; tape the `U`-extended / `B`-decremented pattern. -/
theorem binToUnaryLoopFullScan_body_runConfig_afterScanRight7 (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - u - 1 → c0.tape p = false) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1))).state).fst : Nat) = w + 28
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1))).head : Nat)
          = (c0.head : Nat)
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1))).tape p
            = (if (p : Nat) = (c0.head : Nat) - u - 1 then true
                else if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterAppend6Handoff w c0 hphase j hj h_zeros h_one h_sentinel hHOME u hUfit hU hUboundary
  rw [show (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1))
        = (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1) + (u + 1) + 1 from by omega,
    TM.runConfig_succ, TM.runConfig_add]
  obtain ⟨hSp, hSh, hSt⟩ := binToUnaryLoopFullScan_body_scanRight_scanning w
    (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1)) hHp (u + 1)
    (by rw [hHh]; omega)
    (by
      intro p hp1 hp2
      rw [hHt p]
      by_cases hpe : (p : Nat) = (c0.head : Nat) - u - 1
      · rw [if_pos hpe]
      · rw [if_neg hpe, if_neg (by rw [hHh] at hp1 hp2; omega), if_neg (by rw [hHh] at hp1 hp2; omega)]
        exact hU p (by rw [hHh] at hp1; omega) (by rw [hHh] at hp2; omega)) (u + 1) (le_refl (u + 1))
  set cS := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM)
      (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1)) (u + 1) with hcS
  have hSp' : (cS.state.fst : Nat) = w + 27 := hSp
  have hSh' : (cS.head : Nat) = (c0.head : Nat) := by rw [hSh, hHh]; omega
  clear_value cS
  have hbitS : cS.tape cS.head = false := by
    have hfeq : cS.head = c0.head := Fin.ext hSh'
    rw [hSt, hfeq, hHt c0.head, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact h_sentinel
  obtain ⟨q0p, q0h, q0t⟩ := binToUnaryLoopFullScan_body_w27_zero w cS
    (i := cS.state.fst) (s := cS.state.snd) hSp' rfl hbitS
  refine ⟨q0p, by rw [q0h, hSh'], ?_⟩
  intro p; rw [q0t, hSt]; exact hHt p

/-- **`onePass` headline** (phases `15 → 29`).  From HOME (phase `15`, head on the sentinel) with `B`'s
lowest set bit at offset `j`, the `B`-zeros / lowest-bit / sentinel layout, and `U = 1^u` to the left
(`hU` / `hUboundary`), one body pass — `decrement B`, re-home, `append 1` to `U`, re-home — reaches the
loop body's **accept phase `29`** (the `loopUntilSink` back-edge target) after the body's step count, with
the head **back at HOME** and the tape holding `(B − 1, 1^(u+1))`: the appended `1` at `head − u − 1`,
`B`'s low `j` cells set, bit `j` cleared.  This is the per-iteration engine `hstep` iterates. -/
theorem binToUnaryLoopFullScan_body_runConfig_onePass (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = w + 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - u - 1 → c0.tape p = false) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1) + 1)).state).fst : Nat) = w + 29
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1) + 1)).head : Nat)
          = (c0.head : Nat)
      ∧ ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1) + 1)).tape p
            = (if (p : Nat) = (c0.head : Nat) - u - 1 then true
                else if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryLoopFullScan_body_runConfig_afterScanRight7 w c0 hphase j hj h_zeros h_one h_sentinel hHOME u hUfit hU hUboundary
  rw [TM.runConfig_succ]
  set cH := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1)) with hcH
  clear_value cH
  obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_body_w28 w cH (i := cH.state.fst) (s := cH.state.snd) hHp rfl
  exact ⟨sp, by rw [sh, hHh], by intro p; rw [st]; exact hHt p⟩

end ContractExpansion
end Frontier
end Pnp4
