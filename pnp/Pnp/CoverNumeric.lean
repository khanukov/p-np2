import Pnp.FamilyEntropyCover
import Pnp.Entropy
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open BoolFunc
open Asymptotics

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
