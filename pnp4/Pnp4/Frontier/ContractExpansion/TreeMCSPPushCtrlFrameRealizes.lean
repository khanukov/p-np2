import Pnp4.Frontier.ContractExpansion.TreeMCSPPushCtrlFrame
import Mathlib.Data.List.GetD

/-!
# `pushCtrlFrame` realizes the control-stack push (D2t-5a → D2t-5b bridge)

Connects the merged control-stack **machine** `pushCtrlFrame` (#1596) to the merged control-stack **codec**
`encodeCtrlStack` (#1594): running `pushCtrlFrame tag` from the stack-top pointer turns a tape region that
spelled `encodeCtrlStack S` into one spelling `encodeCtrlStack ((tag, tag.arity) :: S)` — i.e. the machine
realises the abstract push `S ↦ (tag, tag.arity) :: S`.

This is the invariant-level step the D2t-5b driver proof uses to maintain the control-stack region across a
node push: it writes the new frame in `[p, p + frameLen)` (untouched cells beyond stay put), and
`encodeCtrlStack`'s cons prepends exactly that frame.

* `windowSpells t base bs` — the cells `[base, base + bs.length)` of tape `t` spell the bit list `bs`.
* `pushCtrlFrame_extends_ctrlStack` — from `windowSpells c.tape (p + frameLen) (encodeCtrlStack S)` (the
  existing stack just past where the frame lands), after the push `windowSpells … p
  (encodeCtrlStack ((tag, tag.arity) :: S))`.

**Progress classification (AGENTS.md): Infrastructure** — a machine↔codec bridge proven at the
configuration level; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The cells `[base, base + bs.length)` of tape `t` spell out the bit list `bs` (read left-to-right;
positions outside the window are unconstrained).  The `base + bs.length ≤ L'` conjunct guarantees the whole
window lies on the (finite) tape — without it the predicate would say nothing about the part of `bs` that
runs past the tape end. -/
def windowSpells {L' : Nat} (t : Fin L' → Bool) (base : Nat) (bs : List Bool) : Prop :=
  base + bs.length ≤ L' ∧
    ∀ q : Fin L', base ≤ (q : Nat) → (q : Nat) < base + bs.length →
      t q = bs.getD ((q : Nat) - base) false

/-- **`pushCtrlFrame` realises the control-stack push.**  If, before the push, the region just past where
the frame will land (`[p + frameLen, …)`) spells `encodeCtrlStack S`, then after running `pushCtrlFrame tag`
from `p` the region `[p, …)` spells `encodeCtrlStack ((tag, tag.arity) :: S)` — the new frame prepended.
The frame window comes from `pushCtrlFrame_runConfig`; the tail is untouched (outside the write window);
`encodeCtrlStack`'s cons equation stitches them via `List.getD_append`/`getD_append_right`. -/
theorem pushCtrlFrame_extends_ctrlStack {L : Nat} (tag : ITag)
    (c : Configuration (M := (pushCtrlFrame tag).toPhased.toTM) L)
    (S : List (ITag × Nat))
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + (encodeCtrlFrame (tag, tag.arity)).length
        < (pushCtrlFrame tag).toPhased.toTM.tapeLength L)
    (hrest : windowSpells c.tape
        ((c.head : Nat) + (encodeCtrlFrame (tag, tag.arity)).length) (encodeCtrlStack S)) :
    windowSpells
        (TM.runConfig (M := (pushCtrlFrame tag).toPhased.toTM) c
          (encodeCtrlFrame (tag, tag.arity)).length).tape
        (c.head : Nat) (encodeCtrlStack ((tag, tag.arity) :: S)) := by
  obtain ⟨_, _, htape⟩ := pushCtrlFrame_runConfig tag c hphase hroom
  obtain ⟨hfit, hcells⟩ := hrest
  have hcons : encodeCtrlStack ((tag, tag.arity) :: S)
      = encodeCtrlFrame (tag, tag.arity) ++ encodeCtrlStack S := rfl
  refine ⟨?_, ?_⟩
  · -- the combined window fits: its tail's fit is exactly `hfit`
    rw [hcons, List.length_append]; omega
  · intro q hlo hhi
    rw [hcons] at hhi ⊢
    rw [htape q]
    rw [List.length_append] at hhi
    by_cases hq : (q : Nat) < (c.head : Nat) + (encodeCtrlFrame (tag, tag.arity)).length
    · -- inside the freshly-written frame window
      rw [if_pos ⟨hlo, hq⟩,
        List.getD_append (encodeCtrlFrame (tag, tag.arity)) (encodeCtrlStack S) false
          ((q : Nat) - (c.head : Nat)) (by omega)]
    · -- past the frame: the cell is untouched, so use the prior stack content `hcells`
      rw [if_neg (fun h => hq h.2),
        List.getD_append_right (encodeCtrlFrame (tag, tag.arity)) (encodeCtrlStack S) false
          ((q : Nat) - (c.head : Nat)) (by omega)]
      rw [hcells q (by omega) (by omega)]
      congr 1
      omega

end ContractExpansion
end Frontier
end Pnp4
