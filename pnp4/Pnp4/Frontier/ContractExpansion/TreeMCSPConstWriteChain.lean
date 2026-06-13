import Pnp4.Frontier.ContractExpansion.TreeMCSPConstIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPConstStepTape

/-!
# The const arm's write chain — D2t-5b (Block A5m-6, run algebra)

`constIterProgram` rewrites the tape in three block writes (the marker block from the old marker,
the record-plus-replant block at the old `FM`, the value entry at the value frontier — the fourth,
the `SHW` tick, stays outside `constStepTape` in the keystone too), in machine order: marker
first, then the record, then the entry.  The three regions are disjoint (record < entry < marker,
with the corridor gaps between), so the chain composes to **exactly** the keystone's transformer
`constStepTape` — the `corridorInv_constStep` shape the end-to-end run concludes with.

**Progress classification (AGENTS.md): Infrastructure** — tape-transformer algebra; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The const arm's three block writes compose to `constStepTape`**: the marker block from the
old marker (`cur − 1`), the record-plus-replant block at the old `FM`, and the value entry at the
value frontier `vtop` — regions disjoint (`fm + 4 ≤ vtop`, `vtop + (k + 3) ≤ cur − 1`). -/
theorem writeConstChain_eq_constStepTape {L : Nat} (tape : Fin L → Bool)
    (cur vtop fm k : Nat) (b : Bool)
    (hcur : 1 ≤ cur)
    (hd1 : fm + 4 ≤ vtop)
    (hd2 : vtop + (k + 3) ≤ cur - 1) :
    writeBlockTape (writeBlockTape (writeBlockTape tape (cur - 1) constMarkBlock)
        fm (constRecBlock b)) vtop (encodeNatEntryR k)
      = constStepTape tape cur vtop fm (encodeNatEntryR k) [true, false, b] := by
  have hlen : (encodeNatEntryR k).length = k + 3 := encodeNatEntryR_length k
  funext q
  unfold constStepTape cursorStepTape emitTape writeBlockTape
  simp only [constMarkBlock_length, constRecBlock_length, hlen,
    List.length_cons, List.length_nil]
  by_cases hv : vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + (k + 3)
  · -- the value entry region
    rw [if_pos hv, if_neg (show ¬ (q : Nat) = cur + 4 - 1 from by omega),
      if_neg (show ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1) from by omega),
      if_neg (show ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + (2 + 1)) from by omega),
      if_neg (show ¬ (q : Nat) = fm + (2 + 1) from by omega),
      if_pos hv]
  · rw [if_neg hv]
    by_cases hr : fm ≤ (q : Nat) ∧ (q : Nat) < fm + 4
    · -- the record-plus-replant region
      rw [if_pos (show fm ≤ (q : Nat) ∧ (q : Nat) < fm + 4 from hr),
        if_neg (show ¬ (q : Nat) = cur + 4 - 1 from by omega),
        if_neg (show ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1) from by omega)]
      by_cases hr3 : (q : Nat) = fm + 3
      · rw [if_neg (show ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + (2 + 1)) from by omega),
          if_pos (show (q : Nat) = fm + (2 + 1) from by omega),
          show (q : Nat) - fm = 3 from by omega]
        rfl
      · rw [if_pos (show fm ≤ (q : Nat) ∧ (q : Nat) < fm + (2 + 1) from by omega)]
        have h3 : (q : Nat) - fm = 0 ∨ (q : Nat) - fm = 1 ∨ (q : Nat) - fm = 2 := by omega
        rcases h3 with h | h | h <;> rw [h] <;> rfl
    · rw [if_neg hr]
      by_cases hm : cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur - 1 + 5
      · -- the marker region
        rw [if_pos hm]
        by_cases hm4 : (q : Nat) = cur + 4 - 1
        · rw [if_pos hm4, show (q : Nat) - (cur - 1) = 4 from by omega]
          rfl
        · rw [if_neg hm4,
            if_pos (show cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1 from by omega)]
          have h4 : (q : Nat) - (cur - 1) = 0 ∨ (q : Nat) - (cur - 1) = 1
              ∨ (q : Nat) - (cur - 1) = 2 ∨ (q : Nat) - (cur - 1) = 3 := by omega
          rcases h4 with h | h | h | h <;> rw [h] <;> rfl
      · -- off all three regions
        rw [if_neg hm,
          if_neg (show ¬ (q : Nat) = cur + 4 - 1 from by omega),
          if_neg (show ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 4 - 1) from by omega),
          if_neg (show ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + (2 + 1)) from by omega),
          if_neg (show ¬ (q : Nat) = fm + (2 + 1) from by omega),
          if_neg hv]

end ContractExpansion
end Frontier
end Pnp4
