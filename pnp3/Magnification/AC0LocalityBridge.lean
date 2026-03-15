import AC0.MultiSwitching.Main
import Core.ShrinkageWitness
import Complexity.Interfaces
import Models.Model_PartialMCSP
import ThirdPartyFacts.Facts_Switching
import ThirdPartyFacts.PartialLocalityLift
import Facts.LocalityLift.Exports

/-!
  pnp3/Magnification/AC0LocalityBridge.lean

  AC0-specific constructive bridge for I-4.

  This module intentionally avoids any global conversion
  `PpolyFormula -> AC0`. Instead, it assumes an explicit AC0/CNF family
  witness at the bridge boundary and reuses the constructive common-CCDT
  pipeline from `AC0.MultiSwitching.Main`.
-/

namespace Pnp3
namespace Magnification
namespace AC0LocalityBridge

open Core
open AC0.MultiSwitching
open Models
open ComplexityInterfaces

/--
I-2B target interface: data that a depth-aware multi-switching/CCDT layer must
provide for each extracted strict formula witness.

The package intentionally asks for:
1) explicit AC0-family provenance (`ac0`, `F`, AC0 witness, multi-switching witness),
2) semantic linkage between `F` and the extracted strict formula `c`,
3) concrete support-derived numeric bounds required by the certificate route.
-/
structure FormulaSupportBoundsFromMultiSwitchingContract where
  package :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
        Classical.choose hFormula
      let c := wf.family (Models.partialInputLen p)
      let alive := ComplexityInterfaces.FormulaCircuit.support c
      let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
        Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
      let hlen :
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
          Models.partialInputLen p :=
        ThirdPartyFacts.inputLen_toFactsPartial p
      let rFacts :
        Facts.LocalityLift.Restriction
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
        ThirdPartyFacts.castRestriction hlen.symm rPartial
      ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
        (hsame : ac0.n = Models.partialInputLen p),
        ThirdPartyFacts.AC0FamilyWitnessProp ac0 F ∧
        Nonempty (ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F) ∧
        (∃ f : Core.BitVec ac0.n → Bool,
          f ∈ F ∧
          ∀ x : Core.BitVec ac0.n,
            f x = ComplexityInterfaces.FormulaCircuit.eval c
              (ThirdPartyFacts.castBitVec hsame x)) ∧
        rFacts.alive.card ≤
          Facts.LocalityLift.polylogBudget
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
        Facts.LocalityLift.LocalCircuitSmallEnough
          { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
            , M := ComplexityInterfaces.FormulaCircuit.size c * rFacts.alive.card.succ
            , ℓ := rFacts.alive.card
            , depth := 0 } ∧
        rFacts.alive.card ≤
          Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

/--
Semantic multi-switching provider (A9 core payload without numeric locality
bounds): for each extracted strict formula `c`, provide AC0 provenance plus a
function in `F` extensionally equal to `eval c` (after length cast).
-/
structure FormulaSemanticMultiSwitchingProvider where
  package :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
        Classical.choose hFormula
      let c := wf.family (Models.partialInputLen p)
      ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
        (hsame : ac0.n = Models.partialInputLen p),
        ThirdPartyFacts.AC0FamilyWitnessProp ac0 F ∧
        Nonempty (ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F) ∧
        (∃ f : Core.BitVec ac0.n → Bool,
          f ∈ F ∧
          ∀ x : Core.BitVec ac0.n,
            f x = ComplexityInterfaces.FormulaCircuit.eval c
              (ThirdPartyFacts.castBitVec hsame x))

/--
Intermediate source-side certificate for one extracted strict formula witness.

This packages exactly the objects that are naturally produced by the current
semantic multi-switching layer:
1) AC0-family provenance,
2) a concrete multi-switching witness,
3) the derived polylog witness,
4) the semantic link back to the extracted strict formula.

Importantly, this certificate still does *not* choose any
`Facts.LocalityLift.Restriction`; that remains the next constructive frontier.
-/
structure SemanticSwitchingCertificatePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  ac0 : ThirdPartyFacts.AC0Parameters
  F : Core.Family ac0.n
  hsame : ac0.n = Models.partialInputLen p
  hFam : ThirdPartyFacts.AC0FamilyWitnessProp ac0 F
  w : ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F
  hpolyW : ThirdPartyFacts.AC0PolylogBoundWitness ac0 F hFam
  hLink :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec ac0.n → Bool,
      f ∈ F ∧
      ∀ x : Core.BitVec ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec hsame x)

/--
Provider interface for the intermediate source-side switching certificate.
-/
def SemanticSwitchingCertificateProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (SemanticSwitchingCertificatePartial hFormula)

/--
Point-assignments list for `x`: one bit-fix `(i, x i)` for every input index.
-/
private noncomputable def pointAssignments {n : Nat}
    (x : Core.BitVec n) : List (Core.BitFix n) :=
  (List.finRange n).map (fun i => (i, x i))

/-- Point-term matching exactly one assignment `x`. -/
private noncomputable def pointTerm {n : Nat}
    (x : Core.BitVec n) : AC0.Term n :=
  { lits := (List.finRange n).map (fun i => ({ idx := i, val := x i } : AC0.Literal n)) }

private lemma termAssignments_pointTerm {n : Nat}
    (x : Core.BitVec n) :
    ThirdPartyFacts.AC0Depth2.termAssignments (pointTerm x) = pointAssignments x := by
  simp [pointTerm, pointAssignments, ThirdPartyFacts.AC0Depth2.termAssignments]

private lemma pointAssignments_satisfy {n : Nat} (x : Core.BitVec n) :
    ∀ u ∈ pointAssignments x, x u.1 = u.2 := by
  intro u hu
  rcases List.mem_map.mp hu with ⟨i, hi, huEq⟩
  cases huEq
  rfl

/--
If an assignment `x` satisfies all updates and already belongs to `β`,
then `assignMany β updates` cannot fail.
-/
private lemma assignMany_ne_none_of_satisfiable
    {n : Nat} (β : Core.Subcube n)
    (updates : List (Core.BitFix n)) (x : Core.BitVec n)
    (hβ : Core.mem β x)
    (hsat : ∀ u ∈ updates, x u.1 = u.2) :
    Core.Subcube.assignMany β updates ≠ none := by
  induction updates generalizing β with
  | nil =>
      simp [Core.Subcube.assignMany]
  | cons u rest ih =>
      rcases u with ⟨i, b⟩
      dsimp [Core.Subcube.assignMany]
      have hxi : x i = b := hsat (i, b) (by simp)
      have hAssignNotNone : Core.Subcube.assign β i b ≠ none := by
        cases hβi : β i with
        | none =>
            simp [Core.Subcube.assign, hβi]
        | some bOld =>
            have hxbOld : x i = bOld := (Core.mem_iff (β := β) (x := x)).1 hβ i bOld hβi
            have hbEq : b = bOld := hxi.symm.trans hxbOld
            simp [Core.Subcube.assign, hβi, hbEq]
      cases hstep : Core.Subcube.assign β i b with
      | none =>
          exact (hAssignNotNone hstep).elim
      | some β' =>
          have hβ' : Core.mem β' x := by
            exact (Core.mem_assign_iff (β := β) (γ := β') (i := i) (b := b) (x := x) hstep).2
              ⟨hβ, hxi⟩
          have hsatRest : ∀ u ∈ rest, x u.1 = u.2 := by
            intro u hu
            exact hsat u (by simp [hu])
          exact ih β' hβ' hsatRest

private lemma pointTerm_consistent {n : Nat}
    (x : Core.BitVec n) :
    ∃ β, ThirdPartyFacts.AC0Depth2.termToSubcube (pointTerm x) = some β := by
  classical
  let updates := pointAssignments x
  have hsat : ∀ u ∈ updates, x u.1 = u.2 := by
    simpa [updates] using pointAssignments_satisfy x
  have hne :
      Core.Subcube.assignMany (ThirdPartyFacts.fullSubcube n) updates ≠ none := by
    exact assignMany_ne_none_of_satisfiable
      (β := ThirdPartyFacts.fullSubcube n)
      (updates := updates)
      (x := x)
      (hβ := Core.mem_top x)
      (hsat := hsat)
  cases hsub : Core.Subcube.assignMany (ThirdPartyFacts.fullSubcube n) updates with
  | none =>
      exact (hne hsub).elim
  | some β =>
      refine ⟨β, ?_⟩
      have hta :
          ThirdPartyFacts.AC0Depth2.termAssignments (pointTerm x) = updates := by
        simpa [updates] using termAssignments_pointTerm x
      have hmap :
          List.map AC0.Literal.toBitFix (pointTerm x).lits = updates := by
        simpa [ThirdPartyFacts.AC0Depth2.termAssignments] using hta
      simpa [ThirdPartyFacts.AC0Depth2.termToSubcube, hmap] using hsub

private lemma pointTerm_eval_true_iff_eq {n : Nat}
    (x y : Core.BitVec n) :
    AC0.Term.eval (pointTerm x) y = true ↔ y = x := by
  constructor
  · intro hEval
    have hAll :
        ∀ i ∈ List.finRange n, decide (y i = x i) = true := by
      simpa [pointTerm, AC0.Term.eval, AC0.Literal.holds] using (List.all_eq_true.mp hEval)
    apply funext
    intro i
    exact (decide_eq_true_eq.mp (hAll i (List.mem_finRange _)))
  · intro hEq
    subst hEq
    simp [pointTerm, AC0.Term.eval, AC0.Literal.holds]

private noncomputable def truthTableTerms {n : Nat}
    (f : Core.BitVec n → Bool) : List (AC0.Term n) :=
  ((Finset.univ : Finset (Core.BitVec n)).toList.filter (fun x => f x)).map pointTerm

private noncomputable def truthTableDNF {n : Nat}
    (f : Core.BitVec n → Bool) : AC0.DNF n :=
  { terms := truthTableTerms f }

private lemma truthTableDNF_eval {n : Nat}
    (f : Core.BitVec n → Bool) (y : Core.BitVec n) :
    AC0.DNF.eval (truthTableDNF f) y = f y := by
  classical
  by_cases hfy : f y = true
  · have hmemFilter :
        y ∈ (Finset.univ : Finset (Core.BitVec n)).toList.filter (fun x => f x) := by
      exact List.mem_filter.mpr ⟨by simp, hfy⟩
    have hmemTerm : pointTerm y ∈ truthTableTerms f := by
      exact List.mem_map.mpr ⟨y, hmemFilter, rfl⟩
    have hterm : AC0.Term.eval (pointTerm y) y = true :=
      (pointTerm_eval_true_iff_eq y y).2 rfl
    have hany :
        (truthTableTerms f).any (fun t => AC0.Term.eval t y) = true :=
      List.any_eq_true.mpr ⟨pointTerm y, hmemTerm, hterm⟩
    simpa [truthTableDNF, AC0.DNF.eval, hfy] using hany
  · have hnotAny :
      (truthTableTerms f).any (fun t => AC0.Term.eval t y) ≠ true := by
      intro hany
      rcases List.any_eq_true.mp hany with ⟨t, htmem, hteval⟩
      rcases List.mem_map.mp htmem with ⟨x, hxmem, rfl⟩
      have hfxTrue : f x = true := (List.mem_filter.mp hxmem).2
      have hyEq : y = x := (pointTerm_eval_true_iff_eq x y).1 hteval
      have : f y = true := by simpa [hyEq] using hfxTrue
      exact hfy this
    have hanyFalse :
        (truthTableTerms f).any (fun t => AC0.Term.eval t y) = false := by
      cases hcase : (truthTableTerms f).any (fun t => AC0.Term.eval t y) with
      | false => rfl
      | true => exact (hnotAny hcase).elim
    have hfyFalse : f y = false := by
      by_cases h : f y = false
      · exact h
      · cases hval : f y with
        | true => exact (hfy hval).elim
        | false => exact (h hval).elim
    simpa [truthTableDNF, AC0.DNF.eval, hfyFalse] using hanyFalse

private noncomputable def semanticParams {n : Nat}
    (f : Core.BitVec n → Bool) : ThirdPartyFacts.AC0Parameters :=
  let m := (truthTableDNF f).terms.length
  let M := Nat.max 2 m
  { n := n, M := M, d := M * M }

private noncomputable def semanticCircuit {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.AC0Circuit (semanticParams f) where
  formula := truthTableDNF f
  terms_consistent := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨x, _hx, rfl⟩
    exact pointTerm_consistent x

private lemma semanticCircuit_computes {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.AC0Circuit.Computes (semanticCircuit f) f := by
  intro x
  simpa [ThirdPartyFacts.AC0Circuit.eval, semanticCircuit] using truthTableDNF_eval f x

private lemma semanticParams_M_ge_two {n : Nat}
    (f : Core.BitVec n → Bool) :
    2 ≤ (semanticParams f).M := by
  dsimp [semanticParams]
  exact Nat.le_max_left 2 ((truthTableDNF f).terms.length)

private lemma semanticCircuit_depth_le {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.AC0Circuit.depth (semanticCircuit f) ≤ (semanticParams f).d := by
  dsimp [semanticParams, ThirdPartyFacts.AC0Circuit.depth]
  have hM2 : 2 ≤ Nat.max 2 (truthTableDNF f).terms.length :=
    Nat.le_max_left 2 (truthTableDNF f).terms.length
  have h4 :
      4 ≤ (Nat.max 2 (truthTableDNF f).terms.length) *
          (Nat.max 2 (truthTableDNF f).terms.length) :=
    Nat.mul_le_mul hM2 hM2
  exact le_trans (by decide : 2 ≤ 4) h4

private lemma semanticCircuit_size_le {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.AC0Circuit.size (semanticCircuit f) ≤ (semanticParams f).M := by
  dsimp [semanticParams, ThirdPartyFacts.AC0Circuit.size, semanticCircuit]
  exact Nat.le_max_right 2 (truthTableDNF f).terms.length

private noncomputable def semanticFamilyWitness {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.AC0FamilyWitness (semanticParams f) ([f] : Core.Family n) where
  circuits := [semanticCircuit f]
  covers := by
    intro g hg
    have hg' : g = f := by simpa using hg
    refine ⟨semanticCircuit f, by simp, ?_⟩
    simpa [hg'] using semanticCircuit_computes f
  depth_le := by
    intro c hc
    have hc' : c = semanticCircuit f := by simpa using hc
    simpa [hc'] using semanticCircuit_depth_le f
  size_le := by
    intro c hc
    have hc' : c = semanticCircuit f := by simpa using hc
    simpa [hc'] using semanticCircuit_size_le f
  circuits_length_le := by
    have hM2 : 2 ≤ (semanticParams f).M := semanticParams_M_ge_two f
    exact le_trans (by decide : 1 ≤ 2) hM2

private theorem semanticFamilyWitnessProp {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.AC0FamilyWitnessProp (semanticParams f) ([f] : Core.Family n) :=
  ⟨semanticFamilyWitness f⟩

private lemma weak_le_polylog_of_M_ge_two (M : Nat) (hM2 : 2 ≤ M) :
    M * M ≤ Nat.pow (Nat.log2 (M + 2)) (M * M + 1) := by
  have hpow4 : Nat.pow 2 2 ≤ M + 2 := by
    have h2plus : 2 + 2 ≤ M + 2 := Nat.add_le_add_right hM2 2
    simpa using h2plus
  have hbaseLog : 2 ≤ Nat.log 2 (M + 2) := Nat.le_log_of_pow_le Nat.one_lt_two hpow4
  have hbase2 : 2 ≤ Nat.log2 (M + 2) := by
    simpa [Nat.log2_eq_log_two] using hbaseLog
  have hM2_lt : M * M < Nat.pow 2 (M * M + 1) := by
    have hsucc_lt : M * M < M * M + 1 := Nat.lt_succ_self (M * M)
    have hpow_lt : M * M + 1 < Nat.pow 2 (M * M + 1) :=
      Nat.lt_pow_self (n := M * M + 1) (a := 2) Nat.one_lt_two
    exact lt_trans hsucc_lt hpow_lt
  have hM2_le_pow2 : M * M ≤ Nat.pow 2 (M * M + 1) := hM2_lt.le
  have hpow_mono :
      Nat.pow 2 (M * M + 1) ≤
        Nat.pow (Nat.log2 (M + 2)) (M * M + 1) :=
    Nat.pow_le_pow_left hbase2 (M * M + 1)
  exact le_trans hM2_le_pow2 hpow_mono

private lemma semanticParams_weak_le_polylog {n : Nat}
    (f : Core.BitVec n → Bool) :
    ThirdPartyFacts.ac0DepthBound_weak (semanticParams f) ≤
      Nat.pow (Nat.log2 ((semanticParams f).M + 2)) ((semanticParams f).d + 1) := by
  dsimp [semanticParams, ThirdPartyFacts.ac0DepthBound_weak]
  exact weak_le_polylog_of_M_ge_two
    (Nat.max 2 (truthTableDNF f).terms.length)
    (Nat.le_max_left 2 (truthTableDNF f).terms.length)

private theorem semanticMultiSwitchingWitness_nonempty {n : Nat}
    (f : Core.BitVec n → Bool) :
    Nonempty
      (ThirdPartyFacts.AC0MultiSwitchingWitness
        (semanticParams f)
        ([f] : Core.Family n)) := by
  classical
  let params := semanticParams f
  let F : Core.Family params.n := [f]
  have hF : ThirdPartyFacts.AC0FamilyWitnessProp params F := by
    simpa [params, F] using semanticFamilyWitnessProp f
  obtain ⟨t, ε, S, hFamilyEq, ht, hε, htStrong, hε0, hεInv⟩ :=
    ThirdPartyFacts.shrinkage_for_AC0 params F hF
  have hWeakLePolylog :
      ThirdPartyFacts.ac0DepthBound_weak params ≤
        Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
    simpa [params] using semanticParams_weak_le_polylog f
  have hStrongEqPolylog :
      ThirdPartyFacts.ac0DepthBound_strong params =
        Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
    unfold ThirdPartyFacts.ac0DepthBound_strong
    exact max_eq_right hWeakLePolylog
  have hDepthPolylog :
      S.t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
    have hDepthStrong : S.t ≤ ThirdPartyFacts.ac0DepthBound_strong params := by
      simpa [ht] using htStrong
    simpa [hStrongEqPolylog] using hDepthStrong
  have hEpsNonneg : (0 : Core.Q) ≤ S.ε := by
    simpa [hε] using hε0
  have hEpsLeInv : S.ε ≤ (1 : Core.Q) / (params.n + 2) := by
    simpa [hε] using hεInv
  refine ⟨{
    base := by
      simpa [params, F] using (Classical.choice hF)
    shrinkage := S
    family_eq := hFamilyEq
    depth_le_polylog := hDepthPolylog
    epsilon_nonneg := hEpsNonneg
    epsilon_le_inv := hEpsLeInv
  }⟩

/--
Internal constructive semantic provider for A9:
for every extracted strict formula witness, it constructs AC0 provenance
(`ac0`, `F`, AC0 witness, multi-switching witness) and a direct semantic link.
-/
noncomputable def formulaSemanticMultiSwitchingProvider_internal :
    FormulaSemanticMultiSwitchingProvider := by
  classical
  refine ⟨?_⟩
  intro p hFormula
  let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
    Classical.choose hFormula
  let c := wf.family (Models.partialInputLen p)
  let f : Core.BitVec (Models.partialInputLen p) → Bool :=
    fun x => ComplexityInterfaces.FormulaCircuit.eval c x
  let ac0 : ThirdPartyFacts.AC0Parameters := semanticParams f
  let F : Core.Family ac0.n := [f]
  have hsame : ac0.n = Models.partialInputLen p := rfl
  have hFam : ThirdPartyFacts.AC0FamilyWitnessProp ac0 F := by
    simpa [ac0, F, f] using semanticFamilyWitnessProp f
  have hMSw : Nonempty (ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F) := by
    simpa [ac0, F, f] using semanticMultiSwitchingWitness_nonempty f
  refine ⟨ac0, F, hsame, hFam, hMSw, ?_⟩
  refine ⟨f, by simp [F], ?_⟩
  intro x
  simp [f, c, wf]

/--
Package the current semantic multi-switching provider into the explicit
source-side certificate layer.
-/
theorem semanticSwitchingCertificate_of_provider
    (hSem : FormulaSemanticMultiSwitchingProvider)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    Nonempty (SemanticSwitchingCertificatePartial hFormula) := by
  classical
  obtain ⟨ac0, F, hsame, hFam, hMSw, hLink⟩ :=
    hSem.package (p := p) hFormula
  obtain ⟨w⟩ := hMSw
  have hpolyW : ThirdPartyFacts.AC0PolylogBoundWitness ac0 F hFam := by
    simpa using ThirdPartyFacts.ac0PolylogBoundWitness_of_multi_switching ac0 F w
  exact ⟨{
    ac0 := ac0
    F := F
    hsame := hsame
    hFam := hFam
    w := w
    hpolyW := hpolyW
    hLink := hLink
  }⟩

/--
Provider-level version of `semanticSwitchingCertificate_of_provider`.
-/
theorem semanticSwitchingCertificateProvider_of_provider
    (hSem : FormulaSemanticMultiSwitchingProvider) :
    SemanticSwitchingCertificateProviderPartial := by
  intro p hFormula
  exact semanticSwitchingCertificate_of_provider hSem (p := p) hFormula

/--
Audit helper: the semantic provider carries an explicit semantic link from some
function in the AC0 family `F` to the extracted strict formula `c`.
-/
theorem semantic_provider_semantic_link
    (hSem : FormulaSemanticMultiSwitchingProvider)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
      (hsame : ac0.n = Models.partialInputLen p),
      ∃ f : Core.BitVec ac0.n → Bool,
        f ∈ F ∧
        ∀ x : Core.BitVec ac0.n,
          f x = ComplexityInterfaces.FormulaCircuit.eval c
            (ThirdPartyFacts.castBitVec hsame x) := by
  classical
  intro wf c
  obtain ⟨ac0, F, hsame, _hFam, _hMSw, hLink⟩ :=
    hSem.package (p := p) hFormula
  exact ⟨ac0, F, hsame, hLink⟩

/--
Audit helper: the I-2B package carries an explicit semantic link from some
function in the AC0 family `F` to the extracted strict formula `c`.
-/
theorem package_semantic_link
    (hMS : FormulaSupportBoundsFromMultiSwitchingContract)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
      (hsame : ac0.n = Models.partialInputLen p),
      ∃ f : Core.BitVec ac0.n → Bool,
        f ∈ F ∧
        ∀ x : Core.BitVec ac0.n,
          f x = ComplexityInterfaces.FormulaCircuit.eval c
            (ThirdPartyFacts.castBitVec hsame x) := by
  classical
  intro wf c
  obtain ⟨ac0, F, hsame, _hFam, _hMSw, hLink, _hpoly, _hsmall0, _hhalf⟩ :=
    hMS.package (p := p) hFormula
  exact ⟨ac0, F, hsame, hLink⟩

end AC0LocalityBridge
end Magnification
end Pnp3
