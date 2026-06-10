import Pnp4.Frontier.ContractExpansion.TreeMCSPValPush

/-!
# `valReplaceTop_window` — D2t-5b (Block A4d): the value-stack pop-then-push core

The settle-EMIT branch of `DriveState.step` (top control frame `rem = 1`) pops the completed gate's
operands off the value stack and pushes the new gate's WORK index:

* `tnot`: `i :: vs ↦ out.length :: vs`     — **pop 1, push 1**;
* `tand`/`tor`: `i₂ :: i₁ :: vs ↦ out.length :: vs` — **pop 2, push 1**.

In every case the surviving suffix `vs` is untouched and the *top* (rightmost, in the right-anchored
`encodeNatStackR`) block — the popped operand entries `oldTop` — is overwritten by the single new
entry `encodeNatEntryR w` (`w = out.length`).  Because `encodeNatStackR (x :: vs) = encodeNatStackR vs
++ encodeNatEntryR x`, both old and new encodings share the prefix `encodeNatStackR vs`; only the
suffix changes, and its **length may grow or shrink** (the popped entries' total width versus the new
index's width — unlike the settle-decrement, where the frame shrinks by exactly one).

This module factors the **window** half of that rewrite into one reusable lemma, the value-stack
analogue of `valPush_window`.  The single write block

```
encodeNatEntryR w ++ replicate (oldTop.length − (encodeNatEntryR w).length) false
```

covers `max oldTop.length (encodeNatEntryR w).length` cells: its prefix is the new entry, and its
trailing zero pad blanks any leftover cells when the new entry is shorter than `oldTop` (when it is
longer, the pad is empty and the extra cells overwrite previously-dead corridor).  The result window
`[valBase, valBase + |encodeNatStackR (w :: vs)|)` spells `encodeNatStackR (w :: vs)` exactly.  The
companion dead-corridor bookkeeping (the blanked / previously-dead cells past the new content) is
discharged in the consuming keystone from `writeBlockTape`'s structure, since it depends on the
ambient zone bounds.

**Progress classification (AGENTS.md): Infrastructure** — a pure tape-window rewrite lemma over the
verified `encodeNatStackR` codec; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The value-stack pop-then-push window.**  If the value zone spells `encodeNatStackR vs ++ oldTop`
(the surviving suffix `vs` followed by the popped operand block `oldTop`), then overwriting from the
suffix's right end with `encodeNatEntryR w` padded to `oldTop`'s width turns the window into one
spelling `encodeNatStackR (w :: vs)` — the new top entry pushed over the untouched suffix.  Generic
over `oldTop` (one entry for `tnot`, two for `tand`/`tor`) and the new index `w`. -/
theorem valReplaceTop_window {L : Nat} (tape : Fin L → Bool) (vbase : Nat) (vs : List Nat)
    (oldTop : List Bool) (w : Nat)
    (hwin : windowSpells tape vbase (encodeNatStackR vs ++ oldTop))
    (hfit : vbase + (encodeNatStackR vs).length + (encodeNatEntryR w).length ≤ L) :
    windowSpells
      (writeBlockTape tape (vbase + (encodeNatStackR vs).length)
        (encodeNatEntryR w ++ List.replicate (oldTop.length - (encodeNatEntryR w).length) false))
      vbase (encodeNatStackR (w :: vs)) := by
  obtain ⟨_hwfit, hwc⟩ := hwin
  rw [encodeNatStackR_cons]
  refine ⟨by rw [List.length_append]; omega, fun q hlo hhi => ?_⟩
  rw [List.length_append] at hhi
  unfold writeBlockTape
  by_cases hq : (q : Nat) < vbase + (encodeNatStackR vs).length
  · -- below the write base: untouched, value comes from the shared prefix `encodeNatStackR vs`.
    rw [if_neg (by omega)]
    rw [hwc q hlo (by rw [List.length_append]; omega),
      List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · -- at or past the write base: inside the new entry (the block's prefix).
    have hblk : (q : Nat) - (vbase + (encodeNatStackR vs).length) < (encodeNatEntryR w).length := by
      omega
    rw [if_pos ⟨by omega, by rw [List.length_append]; omega⟩,
      List.getD_append _ _ _ _ hblk, List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

end ContractExpansion
end Frontier
end Pnp4
