import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixStateQueryCircuits

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# True-extension prefix query circuits

A correction layer for the greedy decision (Block 8a fix).

The greedy step must ask the decider **"is `p ++ true` extendable?"**, where `p` is
the current prefix of length `i`.  A `PrefixExtensionLanguage` decider answers about
the *encoded* prefix inside the query string; so to make it answer about `p ++ true`
the query must encode the prefix-state `(i + 1, p ++ true)`, **not** `(i, p)`.

This file packages exactly that "true-extension" query:

* `prefixTrueExtensionQueryValue codec n i hi x p
    := prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)` — the serialized
  query for the one-bit-true extension;
* `prefixTrueExtensionQueryBitCircuit` — its per-bit `C_DAG` circuit, still over
  `tableLen n + i` inputs (the real instance bits plus the `i` prior bundle outputs):
  the witness-payload region reads the `i` prior outputs (`inputProj`) for positions
  `< i` and is the constant `true` at position `i`; the index field encodes `i + 1`.

With this, a greedy step `composeDeciderWithQuery dec (prefixTrueExtensionQueryBitCircuit …)`
runs `dec` on the encoded `p ++ true`, so the resulting next-bit hypothesis is
dischargeable from an ordinary prefix-extension decider.

Scope discipline — corrected query value + per-bit circuits only:

* **no** greedy fold / `BoundedSearchSolver`;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/-- The serialized "true-extension" query for prefix `p` (length `i`): the
prefix-state query string for `(i + 1, p ++ true)`. -/
def prefixTrueExtensionQueryValue
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    PrefixBitVec (treeMCSPPrefixM codec n) :=
  prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)

/--
The per-bit `C_DAG` circuit (over `tableLen n + i` inputs) computing the `j`-th bit
of the true-extension query `prefixTrueExtensionQueryValue codec n i hi x p`.

Like `prefixStateQueryBitCircuit` for state `(i + 1, ·)`, but the final witness
payload bit is hard-wired to the constant `true` (so the circuit reads only the `i`
prior bundle outputs, not an `(i+1)`-st input); the index field encodes `i + 1`.
The bound `_hi` keeps the API inside the parser contract; the body does not use it.
-/
def prefixTrueExtensionQueryBitCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (_hi : i + 1 ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n + i) :=
  if hTag : j.1 < tagLen then
    Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
      (natBitBE treePrefixTag tagLen ⟨j.1, hTag⟩)
  else
    let gammaOffset := tagLen
    if hGamma : j.1 < gammaOffset + gammaLen n then
      Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
        (gammaBit n ⟨j.1 - gammaOffset, by omega⟩)
    else
      let xOffset := tagLen + gammaLen n
      if hX : j.1 < xOffset + Pnp3.Models.Partial.tableLen n then
        Pnp3.ComplexityInterfaces.DagCircuit.inputProj
          (Fin.castAdd i ⟨j.1 - xOffset, by omega⟩)
      else
        let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
        if hI : j.1 < iOffset + idxWidth codec.witnessBits n then
          Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
            (natBitBE (i + 1) (idxWidth codec.witnessBits n) ⟨j.1 - iOffset, by omega⟩)
        else
          let pOffset := iOffset + idxWidth codec.witnessBits n
          if hP : j.1 < pOffset + i then
            Pnp3.ComplexityInterfaces.DagCircuit.inputProj
              (Fin.natAdd (Pnp3.Models.Partial.tableLen n) ⟨j.1 - pOffset, by omega⟩)
          else if hT : j.1 < pOffset + (i + 1) then
            Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _ true
          else
            Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _ false

/--
Evaluating the true-extension query-bit circuit on `Fin.append x p` reproduces the
corresponding bit of `prefixTrueExtensionQueryValue codec n i hi x p` — i.e. the
prefix-state query for `(i + 1, p ++ true)`.

The payload region splits into the prior-output reads (`Fin.append_right`, and
`Fin.snoc` at positions `< i` is `p`) and the hard-wired `true` (`Fin.snoc` at the
last position is `true`).
-/
theorem eval_prefixTrueExtensionQueryBitCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (prefixTrueExtensionQueryBitCircuit codec n i hi j) (Fin.append x p) =
      prefixTrueExtensionQueryValue codec n i hi x p j := by
  simp only [prefixTrueExtensionQueryValue, prefixStateQueryValue, prefixStateFields,
    encodeTreeMCSPPrefixFields, prefixTrueExtensionQueryBitCircuit]
  split_ifs with hTag hGamma hX hI hP hT <;>
    simp only [C_DAG,
      Pnp3.ComplexityInterfaces.DagCircuit.eval_constCircuit,
      Pnp3.ComplexityInterfaces.DagCircuit.eval_inputProj,
      Fin.append_left, Fin.append_right]
  · -- payload-prior region: `Fin.snoc p true` at a position `< i` is `p`
    have hv : j.1 - (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n
        + idxWidth codec.witnessBits n) < i := by omega
    rw [show (⟨j.1 - (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n
            + idxWidth codec.witnessBits n), by omega⟩ : Fin (i + 1))
          = Fin.castSucc ⟨j.1 - (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n
            + idxWidth codec.witnessBits n), hv⟩ from Fin.ext rfl,
        Fin.snoc_castSucc]
  · -- `hP ∧ ¬hT` is impossible
    exfalso; omega
  · -- payload-last region: `Fin.snoc p true` at the last position is `true`
    rw [show (⟨j.1 - (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n
            + idxWidth codec.witnessBits n), by omega⟩ : Fin (i + 1)) = Fin.last i
          from Fin.ext (by simp only [Fin.val_last]; omega), Fin.snoc_last]

/-- Every true-extension query-bit circuit has size at most `2`. -/
theorem size_prefixTrueExtensionQueryBitCircuit_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (prefixTrueExtensionQueryBitCircuit codec n i hi j) ≤ 2 := by
  simp only [prefixTrueExtensionQueryBitCircuit]
  split_ifs <;> simp [C_DAG]

end ContractExpansion
end Frontier
end Pnp4
