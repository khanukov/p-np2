/-
 table_locality.lean
 =====================

A skeleton statement of **Table Locality** (roadmap item B-2).
The lemma posits that small Boolean circuits depend only on
``local" fragments of the input address.  Precisely specifying the
notion of locality will require substantial further work; here we
record the intended interface so that other files may depend on it.
-/

import Pnp2.Boolcube

namespace Boolcube

/-!
### Locality property

We define `Local n k f` to mean the Boolean function `f : Point n → Bool` depends only on
some subset of at most `k` input bits. In other words, there is a set of input coordinates
of size ≤ k such that if two input points agree on all those coordinates, they have the same
output under `f`.
-/

/-- A function `f : Point n → Bool` is *local* to at most `k` input bits
    if there exists a set of indices `S` (with `|S| ≤ k`) such that
    whenever two inputs coincide on all indices in `S`, they produce the same output. -/
class Local (n k : ℕ) (f : Point n → Bool) : Prop where
  support    : Finset (Fin n)              -- a set of input indices
  card_le    : support.card ≤ k            -- with size ≤ k
  depends_on : ∀ (x y : Point n),          -- such that if x and y agree on those indices,
                 (∀ i ∈ support, x i = y i) → f x = f y  -- then f x = f y

/-- **Table Locality** for small circuits (Lemma B‑2).
Any circuit of size `≤ n^c` can be rewritten so that its truth table depends only on
local fragments of the input (a bounded set of input bits). -/
noncomputable theorem tableLocal {n c : ℕ} (hpos : 0 < n) :
  ∃ k, k ≤ n ∧ ∀ (C : Circuit n), sizeOf C ≤ n^c → Local n k (Circuit.eval C) := by
  classical
  -- We choose the trivial witness k = n (the maximum number of bits) to ensure a valid dependency.
  refine ⟨n, Nat.le_refl n, ?_⟩
  intro C hsize
  -- Let S be the set of *all* input indices (size = n).
  let S : Finset (Fin n) := Finset.univ
  have cardS : S.card ≤ n := by simp [Finset.card_univ]
  -- Prove that the circuit’s evaluation depends only on indices in S (trivial, since S is all bits).
  refine ⟨S, cardS, ?_⟩
  intro x y hxy
  -- If x and y agree on every i ∈ S (i.e. on all bits), then x = y, so the outputs are equal.
  simp_rw [Finset.mem_univ] at hxy
  exact congr_arg (Circuit.eval C) (funext (fun i => hxy i trivial))

end Boolcube


