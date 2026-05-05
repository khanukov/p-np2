import Magnification.AuditRoutes.LogWidthAdversary.Width_NatLog2
import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2
import Magnification.AuditRoutes.LogWidthAdversary.Diversity_BelowN
import Magnification.AuditRoutes.LogWidthAdversary.Diversity_Unbounded
import Magnification.AuditRoutes.FixedParamsProbe

/-!
# Log-width adversary — final composition

S11 integration for `seed_packs/fp3b1_log_width_hardwiring_lift/`.
This module composes the parallel-engineer outputs into the canonical
diversity theorem that lifts `outputs/nogolog.jsonl::NOGO-000003`
from `status="needs_review"` to `status="formalized"`.

The composition uses Path A (Nat.log2 width) of the seed pack:

* `Width_NatLog2` (S1) — the three width-helper theorems for
  `Nat.log2 (n + 1)`.
* `Family_NatLog2` (S6) — the `prefixAnd`-based adversary family
  whose support is the first `Nat.log2 (n + 1)` input coordinates.
* `Diversity_BelowN` (S9) — parametric reducer for the second
  diversity conjunct.
* `Diversity_Unbounded` (S8 retry) — parametric reducer for the
  first diversity conjunct.

Path B (power-of-two slice via `Family_PowOfTwoSlice`) is also
in the tree as a parallel realisation; it is left wired but not
used by the canonical composition below.  Both paths reach the
same conclusion; we ship Path A because it composes from S1
directly.

The proof has no proof-suspension placeholders, no `axiom`, and stays inside
audit-only zones.  It does NOT touch the trust root, does NOT
construct any `gap_from_*` bridge, does NOT promote
`ProvenanceFilter_v1`, and does NOT create a `pnp3/Candidates/`
directory.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace FixedParamsProbe
namespace FP3Attempt
namespace FP3b1
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces

/-- Auxiliary: every input coordinate occurring in the support of
`prefixAnd n k h` has index strictly below `k`.  Used to discharge
the disjointness obligation when computing the cardinality. -/
private theorem prefixAnd_support_lt (n : Nat) :
    ∀ (k : Nat) (h : k ≤ n) (i : Fin n),
      i ∈ FormulaCircuit.support (prefixAnd n k h) → i.val < k := by
  intro k
  induction k with
  | zero =>
      intro _ i hi
      simp [prefixAnd, FormulaCircuit.support] at hi
  | succ k ih =>
      intro h i hi
      have hk : k ≤ n := Nat.le_of_succ_le h
      simp [prefixAnd, FormulaCircuit.support] at hi
      rcases hi with rfl | hi
      · exact Nat.lt_succ_self k
      · exact Nat.lt_succ_of_lt (ih hk i hi)

/-- The support cardinality of `prefixAnd n k h` is exactly `k`.

The proof is structural induction on `k`.  At the successor step,
the new leaf `input ⟨k, _⟩` is fresh with respect to the inductive
support (every index in there has value `< k`, by
`prefixAnd_support_lt`), so the singleton-vs-set union is
disjoint and the cardinality adds. -/
theorem prefixAnd_support_card (n : Nat) :
    ∀ (k : Nat) (h : k ≤ n),
      (FormulaCircuit.support (prefixAnd n k h)).card = k := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [prefixAnd, FormulaCircuit.support]
  | succ k ih =>
      intro h
      have hk : k ≤ n := Nat.le_of_succ_le h
      have hsupp :
          FormulaCircuit.support (prefixAnd n (k + 1) h) =
            {⟨k, Nat.lt_of_succ_le h⟩} ∪
              FormulaCircuit.support (prefixAnd n k hk) := by
        simp [prefixAnd, FormulaCircuit.support]
      have hnotmem :
          (⟨k, Nat.lt_of_succ_le h⟩ : Fin n) ∉
              FormulaCircuit.support (prefixAnd n k hk) := by
        intro hmem
        exact Nat.lt_irrefl k (prefixAnd_support_lt n k hk _ hmem)
      have hdisj :
          Disjoint ({⟨k, Nat.lt_of_succ_le h⟩} : Finset (Fin n))
            (FormulaCircuit.support (prefixAnd n k hk)) :=
        Finset.disjoint_singleton_left.mpr hnotmem
      rw [hsupp, Finset.card_union_of_disjoint hdisj,
          Finset.card_singleton, ih hk]
      omega

/-- Support cardinality of the Nat.log2 adversary family at length `n`
is exactly `logWidthNat n = Nat.log2 (n + 1)`. -/
theorem adversaryFamily_v_natlog2_support_card (n : Nat) :
    (FormulaCircuit.support (adversaryFamily_v_natlog2 n)).card =
      logWidthNat n := by
  simp [adversaryFamily_v_natlog2, prefixAnd_support_card]

end LogWidthAdversary
end FP3b1
end FP3Attempt
end FixedParamsProbe
end AuditRoutes
end Magnification
end Pnp3

/-!
## Top-level composition

The diversity theorem itself lives outside the deep
`FP3Attempt.FP3b1.LogWidthAdversary` namespace so the seed pack's
expected signature is reachable without a long path prefix.  The
witness it operates on is the S6 record `adversaryWitness_v_natlog2`,
which sits inside `FP3b1.LogWidthAdversary` per S6's design.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt
-- S6's namespace nests one level deeper than FP3b1: every definition
-- (logWidthNat, the family/language/witness, the support-card lemma)
-- lives at FP3b1.LogWidthAdversary.*, not at FP3b1.* directly.
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
  (logWidthNat logWidthNat_le adversaryFamily_v_natlog2
   adversaryLanguage_v_natlog2 adversaryWitness_v_natlog2
   prefixAnd_support_card adversaryFamily_v_natlog2_support_card)

/-- First diversity conjunct against the Nat.log2 family: the support
cardinality is unbounded as `n → ∞`.  Direct application of
`Diversity_Unbounded.adversary_support_unbounded` with width
`logWidthNat`. -/
theorem adversaryWitness_v_natlog2_support_unbounded :
    ∀ B : Nat, ∃ n : Nat,
      B < (FormulaCircuit.support
        (adversaryWitness_v_natlog2.family n)).card := by
  refine adversary_support_unbounded
    adversaryWitness_v_natlog2 logWidthNat ?_ ?_
  · intro n
    have h := adversaryFamily_v_natlog2_support_card n
    -- adversaryWitness_v_natlog2.family is judgmentally adversaryFamily_v_natlog2
    show logWidthNat n ≤ _
    rw [show adversaryWitness_v_natlog2.family
          = adversaryFamily_v_natlog2 from rfl]
    exact Nat.le_of_eq h.symm
  · intro B
    rcases logWidth_unbounded B with ⟨n, hB⟩
    refine ⟨n, ?_⟩
    show B < logWidthNat n
    simpa [logWidthNat] using hB

/-- Second diversity conjunct against the Nat.log2 family: the support
cardinality is strictly below the ambient input length infinitely
often.  Direct application of
`Diversity_BelowN.adversary_support_below_n_io` with width
`logWidthNat`. -/
theorem adversaryWitness_v_natlog2_support_below_n_io :
    ∀ N : Nat, ∃ n : Nat,
      N ≤ n ∧ (FormulaCircuit.support
        (adversaryWitness_v_natlog2.family n)).card < n := by
  refine adversary_support_below_n_io
    adversaryWitness_v_natlog2 logWidthNat ?_ ?_
  · intro n
    have h := adversaryFamily_v_natlog2_support_card n
    show _ ≤ logWidthNat n
    rw [show adversaryWitness_v_natlog2.family
          = adversaryFamily_v_natlog2 from rfl]
    exact Nat.le_of_eq h
  · intro N
    rcases logWidth_lt_self N with ⟨n, hN, hlt⟩
    refine ⟨n, hN, ?_⟩
    show logWidthNat n < n
    simpa [logWidthNat] using hlt

/-- **The S11 integration theorem.**

`adversaryWitness_v_natlog2`, the polynomial-size truth-table-shaped
family on a `Nat.log2 (n + 1)`-window of inputs, satisfies the
candidate filter `FP3Attempt.InSupportFunctionalDiversity`.

Combined with
`FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound`
(the existing Outcome-A obstruction against constant-`polyBound`
families), this proves that the candidate filter as stated does NOT
exclude log-width truth-table hardwiring shapes.  Any future
`ProvenanceFilter_v2` MUST exclude them by an argument other than
support cardinality.

This is the formal lift of `outputs/nogolog.jsonl::NOGO-000003`
from `status = "needs_review"` to `status = "formalized"`.  Kernel-checked,
no proof-suspension placeholders, no `axiom`. -/
theorem logWidthAdversary_satisfies_diversity :
    InSupportFunctionalDiversity adversaryWitness_v_natlog2 :=
  ⟨adversaryWitness_v_natlog2_support_unbounded,
   adversaryWitness_v_natlog2_support_below_n_io⟩

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
