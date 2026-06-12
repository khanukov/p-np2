import Pnp4.Frontier.ContractExpansion.TreeMCSPCursorStep
import Pnp4.Frontier.ContractExpansion.TreeMCSPEmitTape
import Pnp4.Frontier.ContractExpansion.TreeMCSPValPush

/-!
# `constStepTape` and its region identities — D2t-5b (Block A4a): the const-arm off-factory

The `const b` reading arm touches three **disjoint** tape regions — the cursor area
(`cursorStepTape`, consume the 4-cell token), the output region (`emitTape`, record append + `FM`
replant; the count prefix is static), and the value zone (`writeBlockTape`, push the index).  This
module defines the composed transformer `constStepTape` over **explicit numeric anchors** and proves
the *off-factory*: on each region of interest the composition equals exactly the one transformer
that owns it (the other two are the identity there).  The keystone (`corridorInv_constStep`, next)
then routes each invariant clause through one off-lemma + one core lemma, with no inline
disjointness reasoning.

* `constStepTape_eq_cursor` / `_eq_emit` / `_eq_write` / `_eq_id` — the composition seen from each
  region (given the pairwise separation hypotheses).

**Progress classification (AGENTS.md): Infrastructure** — pure tape-transformer identities; builds no
machine and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The const-leaf tape transformer over explicit anchors: value push (innermost, block `ventry` at
`vtop`), output emit (record `rec` at `fm`, `FM` replant), cursor-marker update (outermost, 4-cell
token at `cur`). -/
def constStepTape {L : Nat} (tape : Fin L → Bool) (cur vtop fm : Nat)
    (ventry rec : List Bool) : Fin L → Bool :=
  cursorStepTape (emitTape (writeBlockTape tape vtop ventry) fm rec) cur 4

/-- Off all three regions, `constStepTape` is the identity. -/
theorem constStepTape_eq_id {L : Nat} (tape : Fin L → Bool) (cur vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (hc1 : (q : Nat) ≠ cur + 4 - 1) (hc2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1))
    (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hw : ¬ (vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + ventry.length)) :
    constStepTape tape cur vtop fm ventry rec q = tape q := by
  unfold constStepTape
  rw [cursorStepTape_off _ _ _ q hc1 hc2, emitTape_off _ _ _ q he2 he3]
  unfold writeBlockTape
  rw [if_neg hw]

/-- On the cursor area (and off the other regions), `constStepTape` is `cursorStepTape` of the
original tape: the inner transformers are the identity there. -/
theorem constStepTape_eq_cursor {L : Nat} (tape : Fin L → Bool) (cur vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hw : ¬ (vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + ventry.length)) :
    constStepTape tape cur vtop fm ventry rec q = cursorStepTape tape cur 4 q := by
  unfold constStepTape cursorStepTape
  by_cases hq1 : (q : Nat) = cur + 4 - 1
  · rw [if_pos hq1, if_pos hq1]
  · rw [if_neg hq1, if_neg hq1]
    by_cases hq2 : cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1
    · rw [if_pos hq2, if_pos hq2]
    · rw [if_neg hq2, if_neg hq2, emitTape_off _ _ _ q he2 he3]
      unfold writeBlockTape
      rw [if_neg hw]

/-- On the output region (and off the cursor band / value block), `constStepTape` is `emitTape` of
the original tape. -/
theorem constStepTape_eq_emit {L : Nat} (tape : Fin L → Bool) (cur vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (hc1 : (q : Nat) ≠ cur + 4 - 1) (hc2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1))
    (hw : ¬ (vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + ventry.length)) :
    constStepTape tape cur vtop fm ventry rec q = emitTape tape fm rec q := by
  unfold constStepTape
  rw [cursorStepTape_off _ _ _ q hc1 hc2]
  unfold emitTape
  by_cases hq2 : fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length
  · rw [if_pos hq2, if_pos hq2]
  · rw [if_neg hq2, if_neg hq2]
    by_cases hq3 : (q : Nat) = fm + rec.length
    · rw [if_pos hq3, if_pos hq3]
    · rw [if_neg hq3, if_neg hq3]
      unfold writeBlockTape
      rw [if_neg hw]

/-- On the value block (and off the cursor band / emit cells), `constStepTape` is `writeBlockTape` of
the original tape. -/
theorem constStepTape_eq_write {L : Nat} (tape : Fin L → Bool) (cur vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (hc1 : (q : Nat) ≠ cur + 4 - 1) (hc2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1))
    (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length) :
    constStepTape tape cur vtop fm ventry rec q = writeBlockTape tape vtop ventry q := by
  unfold constStepTape
  rw [cursorStepTape_off _ _ _ q hc1 hc2, emitTape_off _ _ _ q he2 he3]

end ContractExpansion
end Frontier
end Pnp4
