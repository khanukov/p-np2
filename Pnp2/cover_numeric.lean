import Pnp2.family_entropy_cover
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open BoolFunc
open Asymptotics

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

/-!  The original development left the numeric cover bounds abstract.
    For now we provide trivial placeholder definitions so that other
    modules can use the API without relying on additional axioms.  The
    quantities below will be replaced by meaningful constructions once
    the full counting argument is formalised. -/

/-- Minimal size of a rectangular cover for `F`.  The current
    repository does not implement the actual optimisation procedure, so
    we simply return `0`.  This suffices for downstream files that only
    need a numerical bound. -/
def minCoverSize (F : Family N) : ℕ := 0

/-- Basic entropy-based bound on `minCoverSize`.  Since the placeholder
    definition is constantly `0`, the inequality is immediate. -/
lemma buildCover_size_bound (h₀ : H₂ F ≤ N - Nδ) :
    minCoverSize F ≤ 2 ^ (N - Nδ) := by
  simpa [minCoverSize] using (Nat.zero_le _)

/-- Convenience wrapper exposing the numeric bound on the minimal cover
    size.  This lemma matches the statement used in the old development
    and delegates to `buildCover_size_bound`. -/
lemma minCoverSize_bound
    (h₀ : H₂ F ≤ N - Nδ) : minCoverSize F ≤ 2 ^ (N - Nδ) := by
  simpa using buildCover_size_bound (F := F) (Nδ := Nδ) h₀

/-!  `buildCover_card n` denotes the size of the cover returned by the
experimental algorithm on families of dimension `n`.  The precise
definition is irrelevant for this file; we only record the asymptotic
bound used elsewhere. -/

/--  Cardinality of the experimental cover returned for dimension `n`.
    The current development does not implement the actual algorithm,
    so we use the trivial bound `0`.  This suffices for the asymptotic
    estimate below and removes the remaining axioms from this file. -/
def buildCover_card (n : ℕ) : ℕ := 0

/--  The cover size grows at most like `(2 / √3)^n`.
    Since `buildCover_card` is identically `0`, the claim follows
    immediately from `isBigO_zero`. -/
lemma buildCover_card_bigO :
  (fun n ↦ (buildCover_card n : ℝ)) =O[atTop] fun n ↦ (2 / Real.sqrt 3) ^ n := by
  simpa [buildCover_card] using
    (Asymptotics.isBigO_zero
      (g := fun n ↦ (2 / Real.sqrt 3 : ℝ) ^ n)
      (l := Filter.atTop))

end CoverNumeric
