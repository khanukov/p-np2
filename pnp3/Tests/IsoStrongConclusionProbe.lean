import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.FinalResultMainline
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import «pnp3».Tests.GlobalHInDagContractProbe

/-!
# Iso-strong conclusion L0 probe (canonical track)

This file is intentionally local to `pnp3/Tests/` and does **not** alter any
mainline endpoint.  We attempt the recommended Direction N first; in this L0
session we land a structured **partial** result that cleanly exposes the exact
canonical arithmetic obligations produced by `IsoStrongFamilyEventually`.

The key extraction is: from `IsoStrongFamilyEventually` at the canonical family,
we can derive (for sufficiently large slices) the strict slack inequality
`m + 2 < 2^(2^m - κ m β)`.

This is the precise bridge needed by the proposed pigeonhole contradiction
(`m+2` YES-side cap vs. subcube cardinality above `m+2`).
-/

namespace Pnp3
namespace Tests
namespace IsoStrongConclusionProbe

open ComplexityInterfaces
open Models
open Magnification
open LowerBounds
open GlobalHInDagContractProbe
open scoped BigOperators

/-- Shorthand for the canonical eventual gap-slice family. -/
private def F : GapSliceFamilyEventually :=
  eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym

@[simp] lemma F_Mof (n : Nat) : F.Mof n (F.Tof n (0 : Rat)) = n + 2 := by
  simp [F, eventualGapSliceFamily_of_asymptotic]

/--
From iso-strong on the canonical family, extract the eventual strict slack shape
for any admissible `β`: `m + 2 < 2^(2^m - κ m β)`.

This is the arithmetic target required by the Direction N pigeonhole plan.
-/
theorem canonical_isoStrong_implies_eventual_strict_slack
    (W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym)
    (hIso :
      IsoStrongFamilyEventually
        (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
        (globalWitness_to_hInDag W)) :
    ∃ β0 : Rat, 0 < β0 ∧
      ∃ κ : Nat → Rat → Nat,
        ∃ nIso : Rat → Nat,
          ∀ m : Nat, ∀ β : Rat,
            0 < β → β < β0 →
            m ≥ max F.N0 (nIso β) →
              m + 2 < 2 ^ (2 ^ m - κ m β) := by
  rcases hIso with ⟨β0, hβ0, κ, nIso, _hForce, hSlack⟩
  refine ⟨β0, hβ0, κ, nIso, ?_⟩
  intro m β hβPos hβLt hm
  -- Canonical `Mof` is exactly `m+2`, canonical `tableLen` is exactly `2^m`.
  have hRaw := hSlack m β hβPos hβLt hm
  simpa [F, eventualGapSliceFamily_of_asymptotic] using hRaw

/--
L0 status lemma:
we have not (in this bounded session) completed a full Direction N contradiction.
The missing ingredient is a kernel-level pigeonhole lemma converting the strict
slack inequality into an explicit counterexample `z` to the forcing clause.
-/
theorem isoStrong_conclusion_L0_status : True := by
  trivial

/-! ## L1: trace-diagonalisation scaffolding (partial landing) -/

/-- Finite code for size-1 candidate functions: two constants and all projections. -/
inductive Size1Candidate (n : Nat)
  | const : Bool → Size1Candidate n
  | input : Fin n → Size1Candidate n
  deriving DecidableEq

instance (n : Nat) : Fintype (Size1Candidate n) where
  elems :=
    ({Size1Candidate.const false, Size1Candidate.const true} : Finset (Size1Candidate n)) ∪
      Finset.univ.image Size1Candidate.input
  complete := by
    intro c
    cases c with
    | const b =>
      cases b <;> simp
    | input i =>
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

@[simp] theorem card_Size1Candidate (n : Nat) : Fintype.card (Size1Candidate n) = n + 2 := by
  classical
  simp [Fintype.card_ofFinset, Finset.card_union, Finset.card_image]

/-- Value of a size-1 candidate on an input assignment. -/
def evalSize1Candidate {n : Nat} (c : Size1Candidate n) (x : Fin n → Bool) : Bool :=
  match c with
  | .const b => b
  | .input i => x i

/-- Restrict a size-1 candidate to a finite coordinate set `α` via an embedding into `Fin n`. -/
def traceSize1CandidateOnFree {n : Nat} (α : Type) [Fintype α]
    (embed : α → Fin n) (c : Size1Candidate n) : α → Bool :=
  fun a => evalSize1Candidate c (fun i => decide (i = embed a))

/--
Finite-pigeonhole core: if the candidate family has size `< 2^|α|`, there exists
a Boolean labeling of `α` outside all candidate traces.
-/
theorem exists_trace_not_size1_of_card_lt {n : Nat} (α : Type) [Fintype α]
    (embed : α → Fin n)
    (hSlack : n + 2 < 2 ^ Fintype.card α) :
    ∃ label : α → Bool,
      ∀ c : Size1Candidate n,
        label ≠ traceSize1CandidateOnFree α embed c := by
  classical
  have hCand : Fintype.card (Size1Candidate n) < Fintype.card (α → Bool) := by
    simpa [Fintype.card_fun, Fintype.card_bool, card_Size1Candidate] using hSlack
  -- Convert strict inequality of cardinals into existence outside the image.
  have hNotSurj : ¬ Function.Surjective (traceSize1CandidateOnFree α embed) := by
    intro hsurj
    have hCardLe : Fintype.card (α → Bool) ≤ Fintype.card (Size1Candidate n) :=
      Fintype.card_le_of_surjective _ hsurj
    exact (Nat.not_lt.mpr hCardLe) hCand
  rcases not_forall.mp hNotSurj with ⟨label, hLabel⟩
  refine ⟨label, ?_⟩
  intro c hc
  exact hLabel ⟨c, hc⟩

/--
L1 partial landing: free-coordinate trace diagonalisation in abstract form.
This is the corrected (non-naive) pigeonhole ingredient.
-/
theorem exists_trace_not_size1
    (p : GapPartialMCSPParams)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack : p.n + 2 < 2 ^ ((Finset.univ \\ D).card)) :
    ∃ label : (Finset.univ \\ D).attach → Bool,
      ∀ c : Size1Candidate p.n,
        label ≠ traceSize1CandidateOnFree ((Finset.univ \\ D).attach)
          (fun i => ⟨i.1.1, i.1.2.1⟩) c := by
  classical
  -- Rewrite slack into the cardinality form expected by `exists_trace_not_size1_of_card_lt`.
  have hSlack' : p.n + 2 < 2 ^ Fintype.card ((Finset.univ \\ D).attach) := by
    simpa using hSlack
  exact exists_trace_not_size1_of_card_lt ((Finset.univ \\ D).attach)
    (fun i => ⟨i.1.1, i.1.2.1⟩) hSlack'

/-- L1 session status: one kernel-checked sub-lemma family landed. -/
theorem isoStrong_conclusion_L1_status : True := by
  trivial

end IsoStrongConclusionProbe
end Tests
end Pnp3
