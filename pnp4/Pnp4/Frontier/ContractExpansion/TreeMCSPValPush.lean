import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `valPushTape` — D2t-5b (Block A4a): writing a block at a window's right end

A driver value-stack push writes a new top **entry** just past the current right-anchored stack
encoding (`encodeNatStackR (v :: val) = encodeNatStackR val ++ encodeNatEntryR v`).  `valPushTape` is
the generic "write `ys` into the `|ys|` cells starting at `base + |xs|`, leave everything else fixed"
transformer, and `windowSpells_writeAppend` proves it extends a window spelling `xs` to one spelling
`xs ++ ys`.  Reused by both leaf arms' value-stack push and by the settle pop-emit's pushed index.

**Progress classification (AGENTS.md): Infrastructure** — a pure tape-window append lemma; builds no
machine and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Write `ys` into the cells `[wbase, wbase + |ys|)`, leaving every other cell fixed. -/
def writeBlockTape {L : Nat} (tape : Fin L → Bool) (wbase : Nat) (ys : List Bool) (q : Fin L) : Bool :=
  if wbase ≤ (q : Nat) ∧ (q : Nat) < wbase + ys.length then ys.getD ((q : Nat) - wbase) false
  else tape q

/-- **Append a written block to a spelled window.**  If the window `[base, base + |xs|)` spells `xs`,
then writing `ys` at `base + |xs|` (with room) yields a window `[base, base + |xs| + |ys|)` spelling
`xs ++ ys`. -/
theorem windowSpells_writeAppend {L : Nat} (tape : Fin L → Bool) (base : Nat) (xs ys : List Bool)
    (hwin : windowSpells tape base xs) (hfit : base + xs.length + ys.length ≤ L) :
    windowSpells (writeBlockTape tape (base + xs.length) ys) base (xs ++ ys) := by
  obtain ⟨hxfit, hxc⟩ := hwin
  refine ⟨by rw [List.length_append]; omega, fun q hlo hhi => ?_⟩
  rw [List.length_append] at hhi
  unfold writeBlockTape
  by_cases hq : (q : Nat) < base + xs.length
  · -- inside the old window xs
    rw [if_neg (by omega), hxc q hlo hq, List.getD_append _ _ _ _ (by omega)]
  · -- inside the freshly-written ys
    rw [if_pos ⟨by omega, by omega⟩,
      List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

/-- Writing a block leaves cells left of its base untouched. -/
theorem writeBlockTape_below {L : Nat} (tape : Fin L → Bool) (wbase : Nat) (ys : List Bool)
    (q : Fin L) (hq : (q : Nat) < wbase) : writeBlockTape tape wbase ys q = tape q := by
  unfold writeBlockTape
  rw [if_neg (by omega)]

/-- Writing a block leaves cells at or past its end untouched. -/
theorem writeBlockTape_above {L : Nat} (tape : Fin L → Bool) (wbase : Nat) (ys : List Bool)
    (q : Fin L) (hq : wbase + ys.length ≤ (q : Nat)) : writeBlockTape tape wbase ys q = tape q := by
  unfold writeBlockTape
  rw [if_neg (by omega)]

/-- The value-stack push as a block append: writing `encodeNatEntryR v` at the value zone's right end
turns `encodeNatStackR val` into `encodeNatStackR (v :: val)`. -/
theorem valPush_window {L : Nat} (tape : Fin L → Bool) (valBase v : Nat) (val : List Nat)
    (hwin : windowSpells tape valBase (encodeNatStackR val))
    (hfit : valBase + (encodeNatStackR val).length + (encodeNatEntryR v).length ≤ L) :
    windowSpells (writeBlockTape tape (valBase + (encodeNatStackR val).length) (encodeNatEntryR v))
      valBase (encodeNatStackR (v :: val)) := by
  rw [encodeNatStackR_cons]
  exact windowSpells_writeAppend tape valBase (encodeNatStackR val) (encodeNatEntryR v) hwin hfit

end ContractExpansion
end Frontier
end Pnp4
