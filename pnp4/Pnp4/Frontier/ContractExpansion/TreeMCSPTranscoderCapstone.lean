import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverRealization
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateStreamLayout

/-!
# The transcoder capstone — D2t-6b (conditional on the driver instance)

Packages the Configuration-level loop discharge (`DriverRealization.terminal_output`) against the
pure transcoder spec `transcodeWitness` (§9):

* `DriverRealization.transcodes` — for a certificate `encodeCircuit … c ++ tail`, the machine's
  output window spells **exactly the `transcodeWitness` stream** (the count-prefixed postorder
  record stream of `flatten (toTree c)`), within `3 · (toTree c).size · stepBudget` machine steps;
* `DriverRealization.transcodes_faithful` — moreover that stream decodes to a straight-line program
  computing `Circuit.eval c` on **every** input (the end-to-end §9 faithfulness, machine edition).

Both are **conditional on a `DriverRealization` instance** — the arms-and-dispatch machine
construction (A5m-2 … A5m-9 in the fixed plan) is the one remaining input; everything downstream of
it, up to and including the D2t-6b statement shape, is now a theorem.  No instance is constructed
here, and no claim is made beyond the conditional.

**Progress classification (AGENTS.md): Infrastructure** — capstone packaging over the verified loop
discharge and the pure transcoder spec; builds no machine and proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

namespace DriverRealization

variable {n width : Nat} {h_width : n ≤ 2 ^ width} {z : DriverCorridor} {L : Nat}

/-- **D2t-6b, conditional.**  For a certificate `encodeCircuit … c ++ tail`, the driver machine's
output window spells exactly the `transcodeWitness` stream, within
`3 · (toTree c).size · stepBudget` machine steps. -/
theorem transcodes (R : DriverRealization n width h_width z L)
    (c : Pnp3.Models.Circuit n) (tail : List Bool)
    (c0 : Configuration (M := R.P.toPhased.toTM) L)
    (h0 : R.home (⟨preorder (toTree c), [], [], [], false⟩ : DriveState n) c0)
    (hinv0 : driverCorridorInv width h_width z c0.tape
      (⟨preorder (toTree c), [], [], [], false⟩ : DriveState n))
    (hz : CorridorSized z (toTree c)) :
    ∃ (T : Nat) (stream : List Bool),
      T ≤ 3 * (toTree c).size * R.stepBudget
      ∧ transcodeWitness n width (encodeCircuit width h_width c ++ tail) = some stream
      ∧ windowSpells (TM.runConfig (M := R.P.toPhased.toTM) c0 T).tape
          (z.workBase - 1 - (CircuitTree.flatten (toTree c)).gates.length) stream := by
  obtain ⟨T, hT, hwin⟩ := R.terminal_output (toTree c) c0 h0 hinv0 hz
  refine ⟨T, encodeGateStream (CircuitTree.flatten (toTree c)).gates, hT, ?_, hwin⟩
  simp only [transcodeWitness, decodeCircuitFull_encodeCircuit]

/-- **D2t-6b faithfulness, conditional.**  The stream the machine leaves in the output window
decodes to a straight-line program computing `Circuit.eval c` on every input — the end-to-end §9
spec, at the machine level. -/
theorem transcodes_faithful (R : DriverRealization n width h_width z L)
    (c : Pnp3.Models.Circuit n)
    (c0 : Configuration (M := R.P.toPhased.toTM) L)
    (h0 : R.home (⟨preorder (toTree c), [], [], [], false⟩ : DriveState n) c0)
    (hinv0 : driverCorridorInv width h_width z c0.tape
      (⟨preorder (toTree c), [], [], [], false⟩ : DriveState n))
    (hz : CorridorSized z (toTree c)) :
    ∃ (T : Nat) (stream : List Bool) (gates : List (SLGate n)),
      T ≤ 3 * (toTree c).size * R.stepBudget
      ∧ windowSpells (TM.runConfig (M := R.P.toPhased.toTM) c0 T).tape
          (z.workBase - 1 - (CircuitTree.flatten (toTree c)).gates.length) stream
      ∧ decodeGateStream n stream = some (gates, [])
      ∧ ∀ x : Fin n → Bool, SLProgram.eval ⟨gates⟩ x = some (Pnp3.Models.Circuit.eval c x) := by
  obtain ⟨T, hT, hwin⟩ := R.terminal_output (toTree c) c0 h0 hinv0 hz
  refine ⟨T, encodeGateStream (CircuitTree.flatten (toTree c)).gates,
    (CircuitTree.flatten (toTree c)).gates, hT, hwin, ?_, ?_⟩
  · simpa using decodeGateStream_encodeGateStream (CircuitTree.flatten (toTree c)).gates []
  · intro x
    rw [← evalCircuitTree_toTree c x]
    exact CircuitTree.flatten_eval (toTree c) x

end DriverRealization

end ContractExpansion
end Frontier
end Pnp4
