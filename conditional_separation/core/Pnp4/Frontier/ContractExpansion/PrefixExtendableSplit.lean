import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Prefix-extendability split lemmas (pure semantics)

Block 7.5 of the downstream decision→search extraction.  This is the semantic
heart the greedy correctness argument will use, isolated **with no circuits**.

A length-`i` witness prefix `p` for instance `(n, x)` is *extendable*
(`WitnessPrefixExtendable`) when some full witness `w` agrees with `p` on its first
`i` coordinates and solves the search relation.  This is exactly
`PrefixExtendableInput` of the prefix-extension language, restated on the bare
`(n, x, i, p)` data (`prefixExtendableInput_iff_witnessPrefixExtendable`).

The greedy construction extends a prefix one bit at a time; its correctness rests
on the **split** facts proved here:

* `witnessPrefixExtendable_split` — if `p` is extendable then at least one of the
  two next-bit extensions `p ++ true`, `p ++ false` is extendable;
* `witnessPrefixExtendable_snoc_false_of_not_true` — the reject branch: if `p` is
  extendable but `p ++ true` is not, then `p ++ false` is extendable;
* `witnessPrefixExtendable_snoc_true_of_not_false` — the symmetric reject branch.

Scope discipline — pure prefix-extension semantics only:

* **no** circuits, deciders, or `C_DAG`;
* **no** greedy bundle / `BoundedSearchSolver` assembly or solver-correctness;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {problem : SearchMCSPCompressionProblem}

/--
A length-`i` witness prefix `p` for instance `(n, x)` is *extendable* when some full
witness agrees with `p` on its first `i` coordinates and solves the search relation.
This is the bare-data form of `PrefixExtendableInput`.
-/
def WitnessPrefixExtendable
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi : i ≤ problem.witnessBits n) (p : PrefixBitVec i) : Prop :=
  ∃ w : PrefixBitVec (problem.witnessBits n),
    (∀ k : Fin i, w ⟨k.1, Nat.lt_of_lt_of_le k.2 hi⟩ = p k) ∧ problem.relation n x w

/-- The language's `PrefixExtendableInput` is exactly `WitnessPrefixExtendable` on the
parsed input's `(n, x, i, p)` data. -/
theorem prefixExtendableInput_iff_witnessPrefixExtendable
    {m : Nat} (input : PrefixInput problem m) :
    PrefixExtendableInput input ↔
      WitnessPrefixExtendable input.n input.x input.prefixLength_le input.p :=
  Iff.rfl

/--
**Greedy split.**  If a prefix `p` is extendable, then at least one of the two
next-bit extensions `p ++ true`, `p ++ false` is extendable.

The witnessing extension's own `i`-th bit decides which branch survives.
-/
theorem witnessPrefixExtendable_split
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p true)
      ∨ WitnessPrefixExtendable n x hi' (Fin.snoc p false) := by
  obtain ⟨w, hagree, hrel⟩ := hp
  have hlt : i < problem.witnessBits n := hi'
  have hext : WitnessPrefixExtendable n x hi' (Fin.snoc p (w ⟨i, hlt⟩)) := by
    refine ⟨w, ?_, hrel⟩
    intro k
    induction k using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast j => simpa [Fin.snoc_castSucc] using hagree j
  cases hbit : w ⟨i, hlt⟩ with
  | true => rw [hbit] at hext; exact Or.inl hext
  | false => rw [hbit] at hext; exact Or.inr hext

/--
**Reject branch (false).**  If `p` is extendable but `p ++ true` is not, then
`p ++ false` is extendable.
-/
theorem witnessPrefixExtendable_snoc_false_of_not_true
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p)
    (hnt : ¬ WitnessPrefixExtendable n x hi' (Fin.snoc p true)) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p false) := by
  rcases witnessPrefixExtendable_split n x hi' p hp with h | h
  · exact absurd h hnt
  · exact h

/--
**Reject branch (true).**  If `p` is extendable but `p ++ false` is not, then
`p ++ true` is extendable.
-/
theorem witnessPrefixExtendable_snoc_true_of_not_false
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p)
    (hnf : ¬ WitnessPrefixExtendable n x hi' (Fin.snoc p false)) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p true) := by
  rcases witnessPrefixExtendable_split n x hi' p hp with h | h
  · exact h
  · exact absurd h hnf

end ContractExpansion
end Frontier
end Pnp4
