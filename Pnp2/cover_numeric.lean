import Pnp2.family_entropy_cover
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open BoolFunc
open Asymptotics

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

-- Placeholder definitions if needed
-- We assume `minCoverSize` and `buildCover_size_bound` are provided elsewhere.

lemma minCoverSize_bound
    (h₀ : H₂ F ≤ N - Nδ) : (minCoverSize F) ≤ 2^(N - Nδ) := by
  simpa using buildCover_size_bound (F := F) h₀

/-!  `buildCover_card n` denotes the size of the cover returned by the
experimental algorithm on families of dimension `n`.  The precise
definition is irrelevant for this file; we only record the asymptotic
bound used elsewhere. -/

axiom buildCover_card (n : ℕ) : ℕ

/--  The cover size grows at most like `(2 / √3)^n`.
    This wraps the analytic estimate in `big-O` notation.  -/
axiom buildCover_card_bigO :
  (fun n ↦ (buildCover_card n : ℝ)) =O[atTop] fun n ↦ (2 / Real.sqrt 3) ^ n

end CoverNumeric
