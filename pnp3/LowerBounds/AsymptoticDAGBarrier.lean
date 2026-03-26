import Complexity.Interfaces
import Complexity.Promise
import Models.Model_PartialMCSP
import LowerBounds.AcceptedFamilyBarrier
import LowerBounds.MCSPGapLocality
import Mathlib.Data.Finset.Card

namespace Pnp3
namespace LowerBounds

open ComplexityInterfaces
open Complexity
open Models

/-- Canonical asymptotic Gap-PartialMCSP language used by magnification layer. -/
noncomputable abbrev AsymptoticGapLanguage := gapPartialMCSP_AsymptoticLanguage

/-- Agreement of two inputs on a coordinate set `S`. -/
def AgreeOn {N : Nat} (S : Finset (Fin N)) (x y : Bitstring N) : Prop :=
  ∀ i ∈ S, x i = y i

/-- Promise slice at one concrete encoded input length `N`. -/
structure GapSlice (N : Nat) where
  Yes : Set (Bitstring N)
  No : Set (Bitstring N)

/-- Semantic correctness of a DAG circuit on one promise slice. -/
def CorrectOnPromiseSlice {N : Nat} (C : DagCircuit N) (P : GapSlice N) : Prop :=
  (∀ x, x ∈ P.Yes → DagCircuit.eval C x = true) ∧
  (∀ x, x ∈ P.No → DagCircuit.eval C x = false)

/-- Slice extracted from fixed `GapPartialMCSPParams`. -/
def gapSliceOfParams (p : GapPartialMCSPParams) : GapSlice (partialInputLen p) where
  Yes := {x | gapPartialMCSP_Language p (partialInputLen p) x = true}
  No := {x | gapPartialMCSP_Language p (partialInputLen p) x = false}

/-- Auxiliary guard-rail only (not the primary endpoint schema). -/
def InfinitelyOftenNontrivial (L : Language) : Prop :=
  ∀ N0 : Nat, ∃ n ≥ N0, ∃ x y : Bitstring n, L n x ≠ L n y

/--
Structured `(n,β)` slice family used by all theorem-level barrier statements.

`hIndex`, `hT`, `hM` are intentional *coherence fields* packed into one object,
so downstream theorems consume a single argument `F` instead of transport data
spread across theorem signatures.
-/
structure GapSliceFamily where
  paramsOf : Nat → Rat → GapPartialMCSPParams
  Tof : Nat → Rat → Nat
  Mof : Nat → Nat → Nat
  hIndex : ∀ n : Nat, ∀ β : Rat, (paramsOf n β).n = n
  hT : ∀ n : Nat, ∀ β : Rat, Tof n β = (paramsOf n β).sNO - 1
  hM : ∀ n : Nat, ∀ T : Nat, Mof n T = Models.circuitCountBound n T

namespace GapSliceFamily

/-- Encoded-input coordinate length (`mask ++ values`) for slice `(n,β)`. -/
def encodedLen (F : GapSliceFamily) (n : Nat) (β : Rat) : Nat :=
  partialInputLen (F.paramsOf n β)

/-- Truth-table coordinate length for slice `(n,β)`. -/
def tableLen (F : GapSliceFamily) (n : Nat) (β : Rat) : Nat :=
  Partial.tableLen (F.paramsOf n β).n

/--
Counting slack used in certificates.

Important note (to avoid future confusion):
* `S` lives on encoded-input coordinates (`encodedLen = 2 * 2^n`),
* exponent uses truth-table length (`tableLen = 2^n`).

So this is a deliberately strong condition comparing table-level entropy budget
against alive encoded coordinates.
-/
def tableSlack (F : GapSliceFamily) (n : Nat) (β : Rat)
    (S : Finset (Fin (encodedLen F n β))) : Nat :=
  tableLen F n β - S.card

end GapSliceFamily

/-- Layer A (counting anti-locality) at one concrete slice `(n,β)`. -/
def GapAntiLocalityAt (F : GapSliceFamily) (n : Nat) (β : Rat) : Prop :=
  ∀ S : Finset (Fin (GapSliceFamily.encodedLen F n β)),
    F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableSlack F n β S) →
      ∃ x y : Bitstring (GapSliceFamily.encodedLen F n β),
        AgreeOn S x y ∧ y ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
        x ∈ (gapSliceOfParams (F.paramsOf n β)).No

/-- Layer A for the whole family. -/
def GapAntiLocalityStatement (F : GapSliceFamily) : Prop :=
  ∀ n : Nat, ∀ β : Rat, GapAntiLocalityAt F n β

/-- Language-level locality at one concrete slice `(n,β)`. -/
def SliceLanguageLocalityAt (F : GapSliceFamily) (n : Nat) (β : Rat) : Prop :=
  ∃ S : Finset (Fin (GapSliceFamily.encodedLen F n β)),
    F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableSlack F n β S) ∧
    ∀ x y : Bitstring (GapSliceFamily.encodedLen F n β),
      AgreeOn S x y →
        gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x =
        gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y

/-- Language-level locality for all slices. -/
def SliceLanguageLocalityStatement (F : GapSliceFamily) : Prop :=
  ∀ n : Nat, ∀ β : Rat, SliceLanguageLocalityAt F n β

/-- Layer B (solver-level locality) at one concrete slice `(n,β)`. -/
def SmallDAGImpliesCoordinateLocalityAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
      ∃ S : Finset (Fin (GapSliceFamily.encodedLen F n β)),
        F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableSlack F n β S) ∧
        ∀ x y : Bitstring (GapSliceFamily.encodedLen F n β),
          AgreeOn S x y → DagCircuit.eval C x = DagCircuit.eval C y

/--
Promise/value version of Layer B at one concrete slice `(n,β)`.

This interface only asks for locality on canonical encoded inputs lying on the
promise domain, and only with respect to semantic truth-table value bits.
-/
def SmallDAGImpliesPromiseValueLocalityAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      ∃ S : Finset (Fin (GapSliceFamily.tableLen F n β)),
        F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableLen F n β - S.card) ∧
        ∀ x y : Bitstring (GapSliceFamily.encodedLen F n β),
          x ∈ (gapSliceOfParams p).Yes →
          y ∈ (gapSliceOfParams p).No →
          ValidEncoding p x →
          ValidEncoding p y →
          AgreeOnValues (p := p) S x y →
            DagCircuit.eval C x = DagCircuit.eval C y

/-- Promise/value version of Layer B for the whole family. -/
def SmallDAGImpliesPromiseValueLocalityStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesPromiseValueLocalityAt F SizeBound n β ε

/--
One-sided YES-centered promise/value version of Layer B at one concrete slice
`(n,β)`.

This is the nearest-term weak-route source theorem target: instead of demanding
pairwise locality across YES/NO pairs, the solver only needs to accept every
valid promise-relevant completion around one concrete YES center on a small
semantic coordinate set.
-/
def SmallDAGImpliesPromiseYesSubcubeAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      ∃ yYes : Bitstring (GapSliceFamily.encodedLen F n β),
        yYes ∈ (gapSliceOfParams p).Yes ∧
        ValidEncoding p yYes ∧
        ∃ S : Finset (Fin (GapSliceFamily.tableLen F n β)),
          F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableLen F n β - S.card) ∧
          ∀ z : Bitstring (GapSliceFamily.encodedLen F n β),
            (z ∈ (gapSliceOfParams p).Yes ∨ z ∈ (gapSliceOfParams p).No) →
            ValidEncoding p z →
            AgreeOnValues (p := p) S yYes z →
              DagCircuit.eval C z = true

/-- One-sided YES-centered promise/value version of Layer B for the whole family. -/
def SmallDAGImpliesPromiseYesSubcubeStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε

/--
Accepted-family version of Layer B at one concrete slice `(n,β)`.

This is the new theorem-minimal weak endpoint: a small correct DAG solver on
the current slice must come with some accepted family of valid truth tables
whose size already exceeds the counting capacity threshold.
-/
def SmallDAGImpliesAcceptedFamilyAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      Nonempty (AcceptedFamilyCertificate (p := p) (DagCircuit.eval C))

/-- Accepted-family version of Layer B for the whole family. -/
def SmallDAGImpliesAcceptedFamilyStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε

/-- Layer B for the whole family. -/
def SmallDAGImpliesCoordinateLocalityStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesCoordinateLocalityAt F SizeBound n β ε

/--
Convert language-locality to solver-locality for `gapSliceOfParams`.
-/
theorem smallDAG_locality_of_sliceLanguageLocality
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hLang : SliceLanguageLocalityStatement F) :
    SmallDAGImpliesCoordinateLocalityStatement F SizeBound := by
  intro n β ε C _hSize hCorrect
  rcases hLang n β with ⟨S, hSlack, hLocalLang⟩
  refine ⟨S, hSlack, ?_⟩
  intro x y hAgree
  have hxLang : DagCircuit.eval C x =
      gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x := by
    have hxCases :
        gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x = true
        ∨ gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x = false := by
      cases h : gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x <;> simp
    cases hxCases with
    | inl hxTrue =>
        have hxYes : x ∈ (gapSliceOfParams (F.paramsOf n β)).Yes := by
          simpa [gapSliceOfParams, GapSliceFamily.encodedLen] using hxTrue
        exact (hCorrect.1 x hxYes).trans hxTrue.symm
    | inr hxFalse =>
        have hxNo : x ∈ (gapSliceOfParams (F.paramsOf n β)).No := by
          simpa [gapSliceOfParams, GapSliceFamily.encodedLen] using hxFalse
        exact (hCorrect.2 x hxNo).trans hxFalse.symm
  have hyLang : DagCircuit.eval C y =
      gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y := by
    have hyCases :
        gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y = true
        ∨ gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y = false := by
      cases h : gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y <;> simp
    cases hyCases with
    | inl hyTrue =>
        have hyYes : y ∈ (gapSliceOfParams (F.paramsOf n β)).Yes := by
          simpa [gapSliceOfParams, GapSliceFamily.encodedLen] using hyTrue
        exact (hCorrect.1 y hyYes).trans hyTrue.symm
    | inr hyFalse =>
        have hyNo : y ∈ (gapSliceOfParams (F.paramsOf n β)).No := by
          simpa [gapSliceOfParams, GapSliceFamily.encodedLen] using hyFalse
        exact (hCorrect.2 y hyNo).trans hyFalse.symm
  calc
    DagCircuit.eval C x
        = gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x := hxLang
    _ = gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y :=
      hLocalLang x y hAgree
    _ = DagCircuit.eval C y := hyLang.symm

/--
Auxiliary notion of a size-bounded solver used by the final ε/β theorem.
-/
def SmallDAGSolver
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  ∃ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) ∧
      CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β))

/-- Single-slice composition: Layer A + Layer B imply no correct DAG solver. -/
theorem no_dag_solver_of_two_layer
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hAnti : GapAntiLocalityStatement F)
    (hLoc : SmallDAGImpliesCoordinateLocalityStatement F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  rcases hLoc n β ε C hSize hCorrect with ⟨S, hSlack, hInv⟩
  rcases hAnti n β S hSlack with ⟨x, y, hAgree, hyYes, hxNo⟩
  have hEq : DagCircuit.eval C x = DagCircuit.eval C y := hInv x y hAgree
  have hy : DagCircuit.eval C y = true := hCorrect.1 y hyYes
  have hx : DagCircuit.eval C x = false := hCorrect.2 x hxNo
  rw [hx, hy] at hEq
  exact Bool.false_ne_true hEq

/-- Single-slice local composition helper (fixed `n,β`). -/
theorem no_dag_solver_of_two_layer_at
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hAnti : GapAntiLocalityAt F n β)
    (hLoc : SmallDAGImpliesCoordinateLocalityAt F SizeBound n β ε) :
    ¬ SmallDAGSolver F SizeBound n β ε := by
  intro hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  rcases hLoc C hSize hCorrect with ⟨S, hSlack, hInv⟩
  rcases hAnti S hSlack with ⟨x, y, hAgree, hyYes, hxNo⟩
  have hEq : DagCircuit.eval C x = DagCircuit.eval C y := hInv x y hAgree
  have hy : DagCircuit.eval C y = true := hCorrect.1 y hyYes
  have hx : DagCircuit.eval C x = false := hCorrect.2 x hxNo
  rw [hx, hy] at hEq
  exact Bool.false_ne_true hEq

/--
Single-slice composition using the promise/value locality interface.
-/
theorem no_dag_solver_of_promise_value_locality_at
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hLoc : SmallDAGImpliesPromiseValueLocalityAt F SizeBound n β ε) :
    ¬ SmallDAGSolver F SizeBound n β ε := by
  intro hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  rcases hLoc C hSize hCorrect with ⟨S, hSlack, hValueLocal⟩
  let p := F.paramsOf n β
  have hSlack' :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - S.card) := by
    calc
      Models.circuitCountBound p.n (p.sNO - 1)
          = F.Mof n (F.Tof n β) := by
              simp [p, F.hM, F.hT, F.hIndex]
      _ < 2 ^ (GapSliceFamily.tableLen F n β - S.card) := hSlack
      _ = 2 ^ (Models.Partial.tableLen p.n - S.card) := by
            simp [GapSliceFamily.tableLen, p, F.hIndex]
  have hCorrectPromise :
      SolvesPromise (GapPartialMCSPPromise p) (DagCircuit.eval C) := by
    constructor
    · intro x hx
      exact hCorrect.1 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hx)
    · intro x hx
      exact hCorrect.2 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hx)
  exact
    LowerBounds.no_value_local_function_solves_mcsp_of_countingSlack
      (p := p)
      (f := DagCircuit.eval C)
      (S := S)
      hSlack'
      (fun x y hxYes hyNo hxValid hyValid hAgree =>
        hValueLocal x y
          (by simpa [gapSliceOfParams, p] using hxYes)
          (by simpa [gapSliceOfParams, p] using hyNo)
          hxValid
          hyValid
          hAgree)
      hCorrectPromise

/--
Single-slice closure using the one-sided YES-centered promise/value endpoint.
-/
theorem no_dag_solver_of_promise_yes_subcube_at
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hYes : SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε) :
    ¬ SmallDAGSolver F SizeBound n β ε := by
  intro hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let p := F.paramsOf n β
  rcases hYes C hSize hCorrect with ⟨yYes, hyYes, hyValidYes, S, hSlack, hAccept⟩
  have hSlack' :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - S.card) := by
    calc
      Models.circuitCountBound p.n (p.sNO - 1)
          = F.Mof n (F.Tof n β) := by
              simp [p, F.hM, F.hT, F.hIndex]
      _ < 2 ^ (GapSliceFamily.tableLen F n β - S.card) := hSlack
      _ = 2 ^ (Models.Partial.tableLen p.n - S.card) := by
            simp [GapSliceFamily.tableLen, p, F.hIndex]
  have hCorrectPromise :
      SolvesPromise (GapPartialMCSPPromise p) (DagCircuit.eval C) := by
    constructor
    · intro x hx
      exact hCorrect.1 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hx)
    · intro x hx
      exact hCorrect.2 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hx)
  exact
    LowerBounds.no_one_sided_value_local_function_solves_mcsp_of_countingSlack
      (p := p)
      (f := DagCircuit.eval C)
      (x_yes := yYes)
      (S := S)
      (hYes := by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hyYes)
      (hValidYes := hyValidYes)
      hSlack'
      (fun z hzPromise hzValid hAgree =>
        hAccept z
          ((by
            cases hzPromise with
            | inl hzYes =>
                exact Or.inl (by simpa [gapSliceOfParams, p] using hzYes)
            | inr hzNo =>
                exact Or.inr (by simpa [gapSliceOfParams, p] using hzNo)))
          hzValid
          hAgree)
      hCorrectPromise

/--
Single-slice closure using the generic accepted-family weak endpoint.
-/
theorem no_dag_solver_of_acceptedFamily_at
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hAccepted : SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε) :
    ¬ SmallDAGSolver F SizeBound n β ε := by
  intro hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let p := F.paramsOf n β
  rcases hAccepted C hSize hCorrect with ⟨cert⟩
  have hCorrectPromise :
      SolvesPromise (GapPartialMCSPPromise p) (DagCircuit.eval C) := by
    constructor
    · intro x hx
      exact hCorrect.1 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hx)
    · intro x hx
      exact hCorrect.2 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams, p] using hx)
  exact
    no_function_solves_mcsp_of_acceptedFamilyCertificate
      (p := p)
      (f := DagCircuit.eval C)
      cert
      hCorrectPromise

/--
Family-level closure using the generic accepted-family weak endpoint.
-/
theorem no_dag_solver_of_acceptedFamily
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hAccepted : SmallDAGImpliesAcceptedFamilyStatement F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε
  exact no_dag_solver_of_acceptedFamily_at F SizeBound n β ε (hAccepted n β ε)

/--
Family-level closure using the one-sided YES-centered promise/value endpoint.
-/
theorem no_dag_solver_of_promise_yes_subcube
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hYes : SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε
  exact no_dag_solver_of_promise_yes_subcube_at F SizeBound n β ε (hYes n β ε)

/--
Primary endpoint schema (magnification-style quantifiers):

`∃ ε>0, ∃ β₀>0, ∀ β∈(0,β₀), ∃ n₀, ∀ n≥n₀, ¬ SmallDAGSolver(n,β,ε)`.
-/
def MagnificationStyleNoSmallDAG
    (SmallSolver : Nat → Rat → Rat → Prop) : Prop :=
  ∃ ε : Rat, 0 < ε ∧
    ∃ β0 : Rat, 0 < β0 ∧
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ n0 : Nat, ∀ n ≥ n0, ¬ SmallSolver n β ε

/--
Family/eventual glue theorem requested by the barrier plan.

If both layers are available eventually for every sufficiently small β, then
we obtain the full magnification-style no-small-DAG statement.
-/
theorem magnificationStyleNoSmallDAG_of_eventually_two_layer
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyAnti :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nAnti : Nat, ∀ n ≥ nAnti, GapAntiLocalityAt F n β)
    (hEventuallyLoc :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nLoc : Nat, ∀ n ≥ nLoc, SmallDAGImpliesCoordinateLocalityAt F SizeBound n β ε) :
    MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) := by
  refine ⟨ε, hε, β0, hβ0, ?_⟩
  intro β hβpos hβlt
  rcases hEventuallyAnti β hβpos hβlt with ⟨nAnti, hnAnti⟩
  rcases hEventuallyLoc β hβpos hβlt with ⟨nLoc, hnLoc⟩
  refine ⟨max nAnti nLoc, ?_⟩
  intro n hn
  have hnA : n ≥ nAnti := le_trans (Nat.le_max_left _ _) hn
  have hnL : n ≥ nLoc := le_trans (Nat.le_max_right _ _) hn
  have hNoSolver :
      ¬ SmallDAGSolver F SizeBound n β ε := by
    exact no_dag_solver_of_two_layer_at F SizeBound n β ε (hnAnti n hnA) (hnLoc n hnL)
  intro hSolver
  exact hNoSolver hSolver

/--
Eventual magnification-style closure using the generic accepted-family weak
endpoint directly.

This is the new asymptotic weak-route schema: once the source side can produce
accepted-family certificates eventually on all sufficiently large slices for a
fixed `(β, ε)`, the magnification-style no-small-DAG conclusion follows
without routing through coordinate-locality geometry.
-/
theorem magnificationStyleNoSmallDAG_of_eventually_acceptedFamily
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyAccepted :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nAcc : Nat, ∀ n ≥ nAcc, SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε) :
    MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) := by
  refine ⟨ε, hε, β0, hβ0, ?_⟩
  intro β hβpos hβlt
  rcases hEventuallyAccepted β hβpos hβlt with ⟨nAcc, hnAcc⟩
  refine ⟨nAcc, ?_⟩
  intro n hn
  exact no_dag_solver_of_acceptedFamily_at F SizeBound n β ε (hnAcc n hn)

/--
Eventual magnification-style closure using the nearer-term one-sided
YES-centered promise/value endpoint directly.

This statement isolates the currently chosen mainline theorem target before the
final reduction to generic accepted families.
-/
theorem magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyYes :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nYes : Nat, ∀ n ≥ nYes, SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε) :
    MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) := by
  refine ⟨ε, hε, β0, hβ0, ?_⟩
  intro β hβpos hβlt
  rcases hEventuallyYes β hβpos hβlt with ⟨nYes, hnYes⟩
  refine ⟨nYes, ?_⟩
  intro n hn
  exact no_dag_solver_of_promise_yes_subcube_at F SizeBound n β ε (hnYes n hn)

end LowerBounds
end Pnp3
