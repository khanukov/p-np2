import Pnp.Boolcube
import Pnp.CanonicalCircuit

open Boolcube

namespace Boolcube

/-!
### Locality property

We say a Boolean function `f : Point n → Bool` is `Local` to at most `k` input
bits if there exists a set of indices of size ≤ `k` such that whenever two
inputs agree on all those coordinates, their outputs under `f` coincide.
-/

/-- A function `f : Point n → Bool` is *local* to at most `k` input bits
    if there exists a set `S` of indices (with `|S| ≤ k`) such that whenever two
    inputs agree on all indices in `S`, the outputs are equal. -/
def Local (n k : ℕ) (f : Point n → Bool) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ k ∧
    ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- **Table Locality** for small circuits (Lemma B‑2).  Any circuit of size
    `≤ n^c` can be rewritten so that its truth table depends only on a bounded
    set of input bits.  The current bound is the trivial `k = n`. -/
theorem tableLocal {n c : ℕ} :
  ∃ k, k ≤ n ∧ ∀ (C : Circuit n), sizeOf C ≤ n^c → Local n k (Circuit.eval C) :=
by
  classical
  refine ⟨n, Nat.le_refl n, ?_⟩
  intro C _hsize
  let S : Finset (Fin n) := Finset.univ
  have cardS : S.card ≤ n := by
    simp [S]
  refine ⟨S, cardS, ?_⟩
  intro x y hxy
  have hxy' : ∀ i, x i = y i := by
    intro i
    have htmp := hxy i (by simp [S])
    simpa using htmp
  exact congr_arg (Circuit.eval C) (funext hxy')

end Boolcube
