import Pnp.FamilyEntropyCover
import Pnp.Entropy

open BoolFunc

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

/-- Minimal size of a cover for `F`. Placeholder for the actual definition. -/
axiom minCoverSize (F : Family N) : ℕ

/-- Entropy-based size bound for a family cover. Placeholder theorem. -/
axiom buildCover_size_bound
    (h₀ : BoolFunc.H₂ F ≤ N - Nδ) :
    minCoverSize F ≤ 2 ^ (N - Nδ)

lemma numeric_bound
    (h₀ : BoolFunc.H₂ F ≤ N - Nδ) : minCoverSize F ≤ 2 ^ (N - Nδ) := by
  simpa using buildCover_size_bound (F := F) (Nδ := Nδ) h₀

end CoverNumeric
