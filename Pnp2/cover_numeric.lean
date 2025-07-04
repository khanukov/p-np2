import Pnp2.family_entropy_cover

open BoolFunc

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

-- Placeholder definitions if needed
-- We assume `minCoverSize` and `buildCover_size_bound` are provided elsewhere.

lemma numeric_bound
    (h₀ : H₂ F ≤ N - Nδ) : (minCoverSize F) ≤ 2^(N - Nδ) := by
  simpa using buildCover_size_bound (F := F) h₀

end CoverNumeric
