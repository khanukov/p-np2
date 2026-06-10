import Pnp4.Frontier.ContractExpansion.TreeMCSPWriteBits
import Pnp4.Frontier.ContractExpansion.TreeMCSPPushCtrlFrameRealizes
import Pnp4.Frontier.ContractExpansion.TreeMCSPWriteNatField
import Mathlib.Data.List.GetD

/-!
# `writeBits_extends_windowSpells` — D2t-5a: the generic write-extends-window lemma

The two D2t-5a stack-write bridges — `pushCtrlFrame_extends_ctrlStack` (#1597) and
`writeNatField_extends_natStack` (#1598) — share one shape: *write a fixed bit list `bs` at the pointer,
leave the tail untouched, and the combined region now spells `bs ++ tail`*.  This module factors that
shape out once (Qodo's suggested generalization), so every fixed-width write the D2t-5b driver performs
gets its invariant-maintenance step as a one-line corollary instead of re-running the `getD_append`
plumbing.

* `writeBits_extends_windowSpells` — from `windowSpells c.tape (p + bs.length) tail` (the tail just past
  where `bs` lands), after `writeBits bs` from `p` the region `[p, …)` spells `bs ++ tail`.

The two merged bridges are exactly its instances (`bs := encodeCtrlFrame (tag, tag.arity)` with
`tail := encodeCtrlStack S`, and `bs := unaryField v` with `tail := encodeNatStack S`); the value-stack
case is re-derived here as `writeNatField_extends_natStack'` to certify the generalization.

**Progress classification (AGENTS.md): Infrastructure** — a reusable tape-window lemma proven at the
configuration level; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **Generic write-extends-window.**  Writing a fixed bit list `bs` from the pointer `p`, when the region
just past `[p, p + bs.length)` already spells `tail`, leaves `[p, …)` spelling `bs ++ tail` — the prefix is
the freshly-written `bs`, the tail is untouched (outside the write window), and `List.getD_append`/
`getD_append_right` stitch them.  Generalises `pushCtrlFrame_extends_ctrlStack` / `writeNatField_extends_
natStack`. -/
theorem writeBits_extends_windowSpells {L : Nat} (bs : List Bool)
    (c : Configuration (M := (writeBits bs).toPhased.toTM) L)
    (tail : List Bool)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + bs.length < (writeBits bs).toPhased.toTM.tapeLength L)
    (hrest : windowSpells c.tape ((c.head : Nat) + bs.length) tail) :
    windowSpells (TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).tape
        (c.head : Nat) (bs ++ tail) := by
  obtain ⟨_, _, htape⟩ := writeBits_runConfig bs c hphase hroom
  obtain ⟨hfit, hcells⟩ := hrest
  refine ⟨?_, ?_⟩
  · rw [List.length_append]; omega
  · intro q hlo hhi
    rw [htape q]
    rw [List.length_append] at hhi
    by_cases hq : (q : Nat) < (c.head : Nat) + bs.length
    · rw [if_pos ⟨hlo, hq⟩,
        List.getD_append bs tail false ((q : Nat) - (c.head : Nat)) (by omega)]
    · rw [if_neg (fun h => hq h.2),
        List.getD_append_right bs tail false ((q : Nat) - (c.head : Nat)) (by omega)]
      rw [hcells q (by omega) (by omega)]
      congr 1
      omega

/-- The value-stack push bridge re-derived from the generic lemma — certifying that
`writeNatField_extends_natStack` is the `bs := unaryField v`, `tail := encodeNatStack S` instance.  (The
`writeNatField v` machine is definitionally `writeBits (unaryField v)`, and `encodeNatStack (v :: S)
= unaryField v ++ encodeNatStack S`.) -/
theorem writeNatField_extends_natStack' {L : Nat} (v : Nat)
    (c : Configuration (M := (writeNatField v).toPhased.toTM) L)
    (S : List Nat)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + (unaryField v).length < (writeNatField v).toPhased.toTM.tapeLength L)
    (hrest : windowSpells c.tape ((c.head : Nat) + (unaryField v).length) (encodeNatStack S)) :
    windowSpells
        (TM.runConfig (M := (writeNatField v).toPhased.toTM) c (unaryField v).length).tape
        (c.head : Nat) (encodeNatStack (v :: S)) := by
  rw [encodeNatStack_cons]
  exact writeBits_extends_windowSpells (unaryField v) c (encodeNatStack S) hphase hroom hrest

end ContractExpansion
end Frontier
end Pnp4
