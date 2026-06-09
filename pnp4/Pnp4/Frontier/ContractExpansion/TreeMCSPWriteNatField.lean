import Pnp4.Frontier.ContractExpansion.TreeMCSPWriteBits
import Pnp4.Frontier.ContractExpansion.TreeMCSPNatStack
import Pnp4.Frontier.ContractExpansion.TreeMCSPPushCtrlFrameRealizes
import Mathlib.Data.List.GetD

/-!
# `writeNatField` — D2t-5a machine: write one value-stack field (a known unary index)

The value-stack analogue of `pushCtrlFrame`: write the self-delimiting unary field `unaryField v = 1^v 0`
of a **known** index `v` at the stack-top pointer.  As with the control-frame push, a *fixed* `v` makes the
encoding a fixed bit list, so the write is `writeNatField v := writeBits (unaryField v)`, and pushing it
onto an `encodeNatStack`-encoded region prepends `v` (via the merged `encodeNatStack_cons`).

* `writeNatField_runConfig` — the written window `[p, p + (unaryField v).length)` holds exactly
  `unaryField v` (corollary of `writeBits_runConfig`).
* `writeNatField_extends_natStack` — from `windowSpells c.tape (p + |unaryField v|) (encodeNatStack S)`,
  after the write `windowSpells … p (encodeNatStack (v :: S))` — the machine realises the value-stack push
  `S ↦ v :: S`.

**Scope.**  This handles a **known** `v` (e.g. a fixed/computed index supplied by the driver, the value-stack
twin of the per-tag control frame).  The *data-dependent* runtime push — materialising the current WORK
position as `1^v` — is a binary→unary write **loop** (a separate `reachesSink` brick, reusing the D2t-3
loop machinery); it is **not** this fixed-width writer.

**Progress classification (AGENTS.md): Infrastructure** — a stack-write machine + codec-realization bridge
proven at the configuration level; builds no verifier and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Write the value-stack field `unaryField v = 1^v 0` of a known index `v` rightward from the stack-top
pointer (fixed-width, since `v` is known). -/
def writeNatField (v : Nat) : ConstStatePhasedProgram Unit :=
  writeBits (unaryField v)

/-- **`writeNatField` run-through.**  From the pointer `p = c.head` (phase `0`) with room, after
`(unaryField v).length` steps the window `[p, p + …)` holds exactly `unaryField v` and the pointer rests at
`p + …`.  Direct corollary of `writeBits_runConfig`. -/
theorem writeNatField_runConfig {L : Nat} (v : Nat)
    (c : Configuration (M := (writeNatField v).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + (unaryField v).length < (writeNatField v).toPhased.toTM.tapeLength L) :
    ((TM.runConfig (M := (writeNatField v).toPhased.toTM) c (unaryField v).length).state.fst : Nat)
        = (unaryField v).length
      ∧ ((TM.runConfig (M := (writeNatField v).toPhased.toTM) c (unaryField v).length).head : Nat)
        = (c.head : Nat) + (unaryField v).length
      ∧ ∀ q : Fin ((writeNatField v).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (writeNatField v).toPhased.toTM) c (unaryField v).length).tape q
            = if (c.head : Nat) ≤ (q : Nat) ∧ (q : Nat) < (c.head : Nat) + (unaryField v).length
              then (unaryField v).getD ((q : Nat) - (c.head : Nat)) false
              else c.tape q :=
  writeBits_runConfig (unaryField v) c hphase hroom

/-- **`writeNatField` realises the value-stack push.**  If the region just past where the field lands
spells `encodeNatStack S`, then after writing `unaryField v` from `p` the region `[p, …)` spells
`encodeNatStack (v :: S)` — the index `v` prepended.  Mirrors `pushCtrlFrame_extends_ctrlStack`; the field
window comes from `writeNatField_runConfig`, the tail is untouched, and `encodeNatStack_cons` stitches them
via `List.getD_append`/`getD_append_right`. -/
theorem writeNatField_extends_natStack {L : Nat} (v : Nat)
    (c : Configuration (M := (writeNatField v).toPhased.toTM) L)
    (S : List Nat)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + (unaryField v).length < (writeNatField v).toPhased.toTM.tapeLength L)
    (hrest : windowSpells c.tape ((c.head : Nat) + (unaryField v).length) (encodeNatStack S)) :
    windowSpells
        (TM.runConfig (M := (writeNatField v).toPhased.toTM) c (unaryField v).length).tape
        (c.head : Nat) (encodeNatStack (v :: S)) := by
  obtain ⟨_, _, htape⟩ := writeNatField_runConfig v c hphase hroom
  obtain ⟨hfit, hcells⟩ := hrest
  have hcons : encodeNatStack (v :: S) = unaryField v ++ encodeNatStack S := encodeNatStack_cons v S
  refine ⟨?_, ?_⟩
  · rw [hcons, List.length_append]; omega
  · intro q hlo hhi
    rw [hcons] at hhi ⊢
    rw [htape q]
    rw [List.length_append] at hhi
    by_cases hq : (q : Nat) < (c.head : Nat) + (unaryField v).length
    · rw [if_pos ⟨hlo, hq⟩,
        List.getD_append (unaryField v) (encodeNatStack S) false
          ((q : Nat) - (c.head : Nat)) (by omega)]
    · rw [if_neg (fun h => hq h.2),
        List.getD_append_right (unaryField v) (encodeNatStack S) false
          ((q : Nat) - (c.head : Nat)) (by omega)]
      rw [hcells q (by omega) (by omega)]
      congr 1
      omega

end ContractExpansion
end Frontier
end Pnp4
