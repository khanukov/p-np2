import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.CanonicalAsymptoticDecider
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
Trace a size-1 candidate on an explicit family of truth-table rows.

Unlike `traceSize1CandidateOnFree`, this uses real table-row indices
`Fin (Partial.tableLen n)` (semantic assignments encoded as row numbers),
not variable indices in `Fin n`.
-/
def traceSize1CandidateOnRows
    {n : Nat}
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen n))
    (c : Size1Candidate n) : α → Bool :=
  match c with
  | .const b => fun _ => b
  | .input i => fun a => Nat.testBit (row a).val i.val

/-- Generic finite pigeonhole diagonalisation over a trace family. -/
theorem exists_label_not_in_finite_trace_family
    {α γ : Type} [Fintype α] [Fintype γ]
    (trace : γ → α → Bool)
    (h : Fintype.card γ < 2 ^ Fintype.card α) :
    ∃ label : α → Bool,
      ∀ g : γ, label ≠ trace g := by
  classical
  have hNotSurj : ¬ Function.Surjective trace := by
    intro hsurj
    have hCardLe : Fintype.card (α → Bool) ≤ Fintype.card γ :=
      Fintype.card_le_of_surjective _ hsurj
    have hCardLt : Fintype.card γ < Fintype.card (α → Bool) := by
      simpa [Fintype.card_fun, Fintype.card_bool] using h
    exact (Nat.not_lt.mpr hCardLe) hCardLt
  rcases not_forall.mp hNotSurj with ⟨label, hlabel⟩
  exact ⟨label, fun g hg => hlabel ⟨g, hg⟩⟩

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

/--
Diagonal partial table: keep `yYes` on fixed coordinates `D`, and set free rows
to the chosen diagonal `label`.
-/
def diagonalPartialTable
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \\ D).attach → Bool) :
    PartialTruthTable p.n :=
  fun j =>
    if hD : j ∈ D then
      decodePartial yYes j
    else
      some (label ⟨j, by
        refine Finset.mem_sdiff.mpr ?_
        exact ⟨Finset.mem_univ j, hD⟩⟩)

theorem diagonal_z_valid
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \\ D).attach → Bool) :
    ValidEncoding p (encodePartial (diagonalPartialTable p yYes D label)) := by
  exact validEncoding_encodePartial p _

theorem diagonal_z_agrees_on_D
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \\ D).attach → Bool) :
    AgreeOnValues D yYes (encodePartial (diagonalPartialTable p yYes D label)) := by
  intro i hi
  -- Use canonicality of `yYes` on valid encodings.
  have hy : yYes = encodePartial (decodePartial yYes) := hValidYes
  -- The diagonal table copies `decodePartial yYes` on all points of `D`.
  have hdiag : diagonalPartialTable p yYes D label i = decodePartial yYes i := by
    simp [diagonalPartialTable, hi]
  -- Compare value-bits through the canonical encoding.
  calc
    Partial.valPart yYes i
        = Partial.valPart (encodePartial (decodePartial yYes)) i := by simpa [hy]
    _ = (decodePartial yYes i).getD false := by
      simp [Partial.valPart, encodePartial, Partial.valIndex]
    _ = (diagonalPartialTable p yYes D label i).getD false := by simpa [hdiag]
    _ = Partial.valPart (encodePartial (diagonalPartialTable p yYes D label)) i := by
      symm
      simp [Partial.valPart, encodePartial, Partial.valIndex]

/-- Convert a size-1 candidate code into a concrete circuit. -/
def Size1Candidate.toCircuit {n : Nat} : Size1Candidate n → Circuit n
  | .const b => Circuit.const b
  | .input i => Circuit.input i

@[simp] theorem eval_toCircuit_eq_evalSize1Candidate
    {n : Nat} (c : Size1Candidate n) (x : Fin n → Bool) :
    Circuit.eval (Size1Candidate.toCircuit c) x = evalSize1Candidate c x := by
  cases c <;> rfl

theorem is_consistent_diagonal_table_implies_label_trace
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \\ D).attach → Bool)
    (c : Size1Candidate p.n)
    (hCons :
      is_consistent (Size1Candidate.toCircuit c)
        (diagonalPartialTable p yYes D label)) :
    label =
      traceSize1CandidateOnRows ((Finset.univ \\ D).attach)
        (fun a => a.1) c := by
  funext a
  have hdiag : diagonalPartialTable p yYes D label a.1 = some (label a) := by
    simp [diagonalPartialTable, a.2, Finset.mem_sdiff] at *
  have hAt := hCons (Core.vecOfNat p.n a.1.1.val)
  have hIdx : assignmentIndex (Core.vecOfNat p.n a.1.1.val) = a.1 := by
    exact assignmentIndex_vecOfNat_eq a.1
  rw [hIdx, hdiag] at hAt
  cases c with
  | const b =>
      simp [traceSize1CandidateOnRows, Size1Candidate.toCircuit, Circuit.eval] at hAt ⊢
      simpa [hAt]
  | input i =>
      simpa [traceSize1CandidateOnRows, Size1Candidate.toCircuit] using hAt.symm

theorem diagonal_z_not_yes_of_label_not_trace
    (p : GapPartialMCSPParams)
    (hsYES : p.sYES = 1)
    (yYes : Bitstring (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \\ D).attach → Bool)
    (hLabel : ∀ c : Size1Candidate p.n,
      label ≠ traceSize1CandidateOnRows ((Finset.univ \\ D).attach)
        (fun a => a.1) c) :
    ¬ encodePartial (diagonalPartialTable p yYes D label)
        ∈ (gapSliceOfParams p).Yes := by
  intro hzYes
  rcases (gapSlice_yes_iff p (partialInputLen p)
      (by simp [partialInputLen]) _).1 hzYes with hLang
  rw [gapPartialMCSP_Language_eq_true_iff_yes] at hLang
  rw [PartialMCSP_YES, hsYES] at hLang
  rcases hLang with ⟨C, hSize, hCons⟩
  have hMem : C ∈ size1Candidates p.n :=
    mem_size1Candidates_of_size_le_one C hSize
  have hTable :
      is_consistent C (diagonalPartialTable p yYes D label) := by
    simpa [decodePartial_encodePartial] using hCons
  rcases List.mem_cons.mp hMem with rfl | hRest
  · exact (hLabel (.const false))
      (is_consistent_diagonal_table_implies_label_trace p yYes D label (.const false) hTable)
  rcases List.mem_cons.mp hRest with rfl | hRest2
  · exact (hLabel (.const true))
      (is_consistent_diagonal_table_implies_label_trace p yYes D label (.const true) hTable)
  rcases List.mem_map.mp hRest2 with ⟨i, _, hi⟩
  rw [hi] at hTable
  exact (hLabel (.input i))
    (is_consistent_diagonal_table_implies_label_trace p yYes D label (.input i) hTable)

theorem exists_valid_agreeing_not_yes_under_slack
    (p : GapPartialMCSPParams)
    (hsYES : p.sYES = 1)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack : p.n + 2 < 2 ^ (Partial.tableLen p.n - D.card)) :
    ∃ z : Bitstring (partialInputLen p),
      ValidEncoding p z ∧
      AgreeOnValues D yYes z ∧
      ¬ z ∈ (gapSliceOfParams p).Yes := by
  have hSlack' : p.n + 2 < 2 ^ ((Finset.univ \\ D).card) := by
    simpa [Finset.card_sdiff (Finset.subset_univ D)] using hSlack
  rcases exists_label_not_in_finite_trace_family
      (trace := fun c : Size1Candidate p.n =>
        traceSize1CandidateOnRows ((Finset.univ \\ D).attach) (fun a => a.1) c)
      (by simpa [card_Size1Candidate] using hSlack') with ⟨label, hLabel⟩
  refine ⟨encodePartial (diagonalPartialTable p yYes D label), ?_, ?_, ?_⟩
  · exact diagonal_z_valid p yYes D label
  · exact diagonal_z_agrees_on_D p yYes hValidYes D label
  · exact diagonal_z_not_yes_of_label_not_trace p hsYES yYes D label hLabel


lemma correctOnPromiseSlice_of_InPpolyDAG_family
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (n : Nat) (β : Rat) :
    CorrectOnPromiseSlice
      ((hInDag n β).family (GapSliceFamilyEventually.encodedLen F n β))
      (gapSliceOfParams (F.paramsOf n β)) := by
  constructor
  · intro x hx
    have hCorr := (hInDag n β).correct (GapSliceFamilyEventually.encodedLen F n β) x
    exact hx ▸ hCorr
  · intro x hx
    have hCorr := (hInDag n β).correct (GapSliceFamilyEventually.encodedLen F n β) x
    exact hx ▸ hCorr

lemma slack_for_D_of_isoStrong_slack
    (p : GapPartialMCSPParams)
    (κv : Nat)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hDcard : D.card ≤ κv)
    (hRawSlack : p.n + 2 < 2 ^ (Partial.tableLen p.n - κv)) :
    p.n + 2 < 2 ^ (Partial.tableLen p.n - D.card) := by
  have hExpLe : Partial.tableLen p.n - κv ≤ Partial.tableLen p.n - D.card := by
    exact Nat.sub_le_sub_left hDcard (Partial.tableLen p.n)
  have hPowLe : 2 ^ (Partial.tableLen p.n - κv) ≤ 2 ^ (Partial.tableLen p.n - D.card) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hExpLe
  exact lt_of_lt_of_le hRawSlack hPowLe

@[simp] lemma F_params_sYES (n : Nat) (β : Rat) :
    (F.paramsOf n β).sYES = 1 := by
  simp [F, eventualGapSliceFamily_of_asymptotic]

theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W) := by
  intro W hIso
  rcases hIso with ⟨β0, hβ0, κ, nIso, hForce, hSlack⟩
  let β : Rat := β0 / 2
  have hβPos : 0 < β := by linarith
  have hβLt : β < β0 := by linarith
  let n : Nat := max F.N0 (nIso β)
  have hn : n ≥ max F.N0 (nIso β) := by
    exact le_rfl
  let p := F.paramsOf n β
  let hInDag := globalWitness_to_hInDag W
  let C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β) :=
    (hInDag n β).family (GapSliceFamilyEventually.encodedLen F n β)
  have hSize : ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) := by
    simpa [C, ppolyDAGSizeBoundOnSlicesEventually] using
      (hInDag n β).family_size_le (GapSliceFamilyEventually.encodedLen F n β)
  have hCorrect : CorrectOnPromiseSlice C (gapSliceOfParams p) := by
    simpa [C, p] using correctOnPromiseSlice_of_InPpolyDAG_family F hInDag n β
  rcases hForce n β hβPos hβLt hn C hSize hCorrect with
    ⟨yYes, hyYes, hValidYes, D, hDcard, hAllYes⟩
  have hRawSlack := hSlack n β hβPos hβLt hn
  have hCanonSlack : p.n + 2 < 2 ^ (Partial.tableLen p.n - κ n β) := by
    simpa [p, F, eventualGapSliceFamily_of_asymptotic] using hRawSlack
  have hSlackForD : p.n + 2 < 2 ^ (Partial.tableLen p.n - D.card) :=
    slack_for_D_of_isoStrong_slack p (κ n β) D hDcard hCanonSlack
  have hsYES : p.sYES = 1 := by
    simpa [p] using F_params_sYES n β
  rcases exists_valid_agreeing_not_yes_under_slack p hsYES yYes hValidYes D hSlackForD with
    ⟨z, hzValid, hzAgree, hzNotYes⟩
  exact hzNotYes (hAllYes z hzValid hzAgree)

/-- L1 session status: one kernel-checked sub-lemma family landed. -/
theorem isoStrong_conclusion_L1_status : True := by
  trivial

end IsoStrongConclusionProbe
end Tests
end Pnp3
