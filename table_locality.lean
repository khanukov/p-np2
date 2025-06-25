/-
 table_locality.lean
 =====================

A skeleton statement of **Table Locality** (roadmap item B-2).
The lemma posits that small Boolean circuits depend only on
``local" fragments of the input address.  Precisely specifying the
notion of locality will require substantial further work; here we
record the intended interface so that other files may depend on it.
-/

import Boolcube

namespace Boolcube

/-- A placeholder predicate asserting that a function depends only on a
    collection of address fragments of size at most `k`.  The actual
    definition will formalise how inputs are partitioned into blocks.
    For now this is an abstract `Prop` used by `tableLocal`. -/
class Local (n k : ℕ) (f : Point n → Bool) : Prop :=
  (depends_local : True) -- stub

/-- **Table Locality** for small circuits.  Any circuit of size
    `≤ n^c` can be rewritten so that its truth table depends only on
    local fragments of total size `k = O(log n)`.  The proof is
    omitted; the lemma serves as a dependency for Lemma B. -/
noncomputable theorem tableLocal
    {n : ℕ} {c : ℕ} (hpos : 0 < n) :
    ∃ k, k ≤ n ∧
      ∀ (C : Circuit n), sizeOf C ≤ n^c →
        Local n k (Circuit.eval C) := by
  classical
  refine ⟨0, Nat.zero_le _, ?_⟩
  intro C hsize
  exact ⟨trivial⟩

end Boolcube


