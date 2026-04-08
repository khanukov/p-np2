import LowerBounds.AsymptoticDAGBarrierInterfaces

namespace Pnp3
namespace LowerBounds

open ComplexityInterfaces
open Complexity
open Models

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

/--
Canonical size-bound surface extracted from a slice-indexed strict `PpolyDAG`
witness family.

For each slice `(n,β)`, the bound is read from that slice witness at the
encoded input length `GapSliceFamily.encodedLen F n β`; the `ε` parameter is
ignored intentionally (non-uniform witnesses do not depend on approximation
accuracy in this interface).
-/
def ppolyDAGSizeBoundOnSlices
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    Nat → Rat → Rat → Nat → Prop :=
  fun n β _ε s => s ≤ (hInDag n β).polyBound (GapSliceFamily.encodedLen F n β)

/--
Bridge lemma (witness-indexed form):
from strict DAG witnesses on each slice language to explicit small-solver
existence on every `(n,β,ε)`.

This is the intended theorem-skeleton target for Q3-style bridge work: once a
global route is able to provide `InPpolyDAG` witnesses for each slice language,
the asymptotic barrier surface receives concrete `SmallDAGSolver` witnesses
mechanically.
-/
theorem smallDAGSolver_of_inPpolyDAGFamilyOnSlices
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    ∀ n : Nat, ∀ β ε : Rat,
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  intro n β ε
  let w : ComplexityInterfaces.InPpolyDAG
      (gapPartialMCSP_Language (F.paramsOf n β)) := hInDag n β
  refine ⟨w.family (GapSliceFamily.encodedLen F n β), ?_, ?_⟩
  · simpa [ppolyDAGSizeBoundOnSlices] using
      w.family_size_le (GapSliceFamily.encodedLen F n β)
  · constructor
    · intro x hxYes
      have hxLang :
          gapPartialMCSP_Language (F.paramsOf n β)
              (GapSliceFamily.encodedLen F n β) x = true := by
        simpa [gapSliceOfParams] using hxYes
      exact (w.correct (GapSliceFamily.encodedLen F n β) x).trans hxLang
    · intro x hxNo
      have hxLang :
          gapPartialMCSP_Language (F.paramsOf n β)
              (GapSliceFamily.encodedLen F n β) x = false := by
        simpa [gapSliceOfParams] using hxNo
      exact (w.correct (GapSliceFamily.encodedLen F n β) x).trans hxLang

/--
Choice-level adapter from proposition-level per-slice DAG membership
(`PpolyDAG`) to strict witnesses (`InPpolyDAG`).

This is intentionally noncomputable: `PpolyDAG` is an existential proposition,
and the bridge extracts a concrete witness family for theorem composition.
-/
noncomputable def inPpolyDAGFamilyOnSlices_of_PpolyDAG
    (F : GapSliceFamily)
    (hDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language (F.paramsOf n β)) := by
  classical
  intro n β
  exact Classical.choose (hDag n β)

/--
Bridge lemma (membership-level form):
if each slice language is in `PpolyDAG`, then the asymptotic barrier receives
explicit small-solver witnesses on every `(n,β,ε)` via the canonical extracted
size bound `ppolyDAGSizeBoundOnSlices`.
-/
theorem smallDAGSolver_of_PpolyDAGOnSlices
    (F : GapSliceFamily)
    (hDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    let hInDag := inPpolyDAGFamilyOnSlices_of_PpolyDAG F hDag
    ∀ n : Nat, ∀ β ε : Rat,
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  intro hInDag
  exact smallDAGSolver_of_inPpolyDAGFamilyOnSlices F hInDag

/--
Eventual per-`β` strict witness-family hypothesis.

Interpretation:
for each sufficiently small positive `β`, there is a cutoff `n0(β)` such that
every slice language `(n,β)` with `n ≥ n0(β)` already has a strict
`InPpolyDAG` witness.
-/
abbrev EventuallyInPpolyDAGWitnessFamily
    (F : GapSliceFamily)
    (β0 : Rat) : Type :=
  ∀ β : Rat, 0 < β → β < β0 →
    Σ n0 : Nat, ∀ n ≥ n0,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language (F.paramsOf n β))

/--
Eventual per-`β` proposition-level witness-family hypothesis (`PpolyDAG` form).
-/
def EventuallyPpolyDAGWitnessFamily
    (F : GapSliceFamily)
    (β0 : Rat) : Prop :=
  ∀ β : Rat, 0 < β → β < β0 →
    ∃ n0 : Nat, ∀ n ≥ n0,
      ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_Language (F.paramsOf n β))

/--
Canonical "eventually small-solver surface" used by the bridge milestone.

This keeps exactly the asymptotic quantifier shape needed downstream, but on
the **existence** side (`SmallDAGSolver`) rather than contradiction side
(`¬ SmallDAGSolver`): a fixed `(ε,β0)` window and eventual-in-`n` solver
existence for each sufficiently small `β`.
-/
def EventuallySmallDAGSolverSurface (F : GapSliceFamily) : Prop :=
  ∃ SizeBound : Nat → Rat → Rat → Nat → Prop,
    ∃ ε : Rat, 0 < ε ∧
      ∃ β0 : Rat, 0 < β0 ∧
        ∀ β : Rat, 0 < β → β < β0 →
          ∃ n0 : Nat, ∀ n ≥ n0, SmallDAGSolver F SizeBound n β ε

/--
Bridge theorem (strict-witness family form):
`EventuallyInPpolyDAGWitnessFamily` implies the eventual `SmallDAGSolver`
surface.

Implementation note:
`SizeBound := True` is intentional in this bridge layer.  The goal here is
quantifier plumbing from witness families to solver existence; quantitative
size refinements can be layered later without changing the asymptotic shape.
-/
theorem eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily
    (F : GapSliceFamily)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hWitness : EventuallyInPpolyDAGWitnessFamily F β0) :
    EventuallySmallDAGSolverSurface F := by
  refine ⟨fun _n _β _ε _s => True, ε, hε, β0, hβ0, ?_⟩
  intro β hβpos hβlt
  rcases hWitness β hβpos hβlt with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n hn
  let w : ComplexityInterfaces.InPpolyDAG
      (gapPartialMCSP_Language (F.paramsOf n β)) := hn0 n hn
  refine ⟨w.family (GapSliceFamily.encodedLen F n β), trivial, ?_⟩
  constructor
  · intro x hxYes
    have hxLang :
        gapPartialMCSP_Language (F.paramsOf n β)
            (GapSliceFamily.encodedLen F n β) x = true := by
      simpa [gapSliceOfParams] using hxYes
    exact (w.correct (GapSliceFamily.encodedLen F n β) x).trans hxLang
  · intro x hxNo
    have hxLang :
        gapPartialMCSP_Language (F.paramsOf n β)
            (GapSliceFamily.encodedLen F n β) x = false := by
      simpa [gapSliceOfParams] using hxNo
    exact (w.correct (GapSliceFamily.encodedLen F n β) x).trans hxLang

/--
Bridge theorem (proposition-level family form):
`EventuallyPpolyDAGWitnessFamily` implies the eventual `SmallDAGSolver`
surface by extracting strict witnesses pointwise via `Classical.choose`.
-/
theorem eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily
    (F : GapSliceFamily)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hWitness : EventuallyPpolyDAGWitnessFamily F β0) :
    EventuallySmallDAGSolverSurface F := by
  classical
  refine eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily
    (F := F) (ε := ε) (β0 := β0) hε hβ0 ?_
  intro β hβpos hβlt
  let hExists :
      ∃ n0 : Nat, ∀ n ≥ n0,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    hWitness β hβpos hβlt
  let n0 : Nat := Classical.choose hExists
  let hn0 :
      ∀ n ≥ n0, ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_Language (F.paramsOf n β)) :=
    Classical.choose_spec hExists
  refine ⟨n0, ?_⟩
  intro n hn
  exact Classical.choose (hn0 n hn)

/--
Bridge package connecting one global asymptotic language `L` to all concrete
slice languages of a fixed family `F`.

This is the missing "single-global witness packaging" interface: if a theorem
is proved for one global `L`, this structure records the extensional equality
needed to transport that witness to each `(n,β)` slice language.
-/
structure AsymptoticDAGLanguageBridge (F : GapSliceFamily) : Type where
  L : Language
  sliceEq :
    ∀ n : Nat, ∀ β : Rat, ∀ N : Nat, ∀ x : Bitstring N,
      L N x = gapPartialMCSP_Language (F.paramsOf n β) N x

/--
Single-global-witness transport:
from `PpolyDAG` on one global language `bridge.L` to `PpolyDAG` on every slice
language of `F`.

No asymptotic cutoff is needed here: transport is pointwise and exact for all
`(n,β)` by `bridge.sliceEq`.
-/
theorem ppolyDAGOnSlices_of_globalWitness
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hDagGlobal : ComplexityInterfaces.PpolyDAG bridge.L) :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_Language (F.paramsOf n β)) := by
  rcases hDagGlobal with ⟨w, -⟩
  intro n β
  refine ⟨{ polyBound := w.polyBound
            polyBound_poly := w.polyBound_poly
            family := w.family
            family_size_le := w.family_size_le
            correct := ?_ }, trivial⟩
  intro N x
  have hEvalGlobal : DagCircuit.eval (w.family N) x = bridge.L N x := w.correct N x
  have hSlice :
      bridge.L N x =
        gapPartialMCSP_Language (F.paramsOf n β) N x := by
    exact bridge.sliceEq n β N x
  exact hEvalGlobal.trans hSlice

/--
Global-to-eventual bridge in one theorem:
`PpolyDAG bridge.L` gives the eventual `SmallDAGSolver` surface.

This theorem is intentionally phrased with explicit `(ε,β0)` parameters so it
matches the quantifier front used by magnification-style endpoint wrappers.
Since the transported slice witnesses hold for all `n`, the eventual cutoff can
be chosen as `n0 = 0`.
-/
theorem eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hDagGlobal : ComplexityInterfaces.PpolyDAG bridge.L) :
    EventuallySmallDAGSolverSurface F := by
  have hSlices :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    ppolyDAGOnSlices_of_globalWitness F bridge hDagGlobal
  refine eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily
    (F := F) (ε := ε) (β0 := β0) hε hβ0 ?_
  intro β hβpos hβlt
  refine ⟨0, ?_⟩
  intro n _hn
  exact hSlices n β

/--
Global contradiction schema for the new bridge layer.

Assume we have a *uniform no-small-solver barrier* for every canonical
size-bound family produced by strict slice witnesses. Then any global
`PpolyDAG` witness on `bridge.L` is impossible.

This theorem is intentionally bridge-centric and still independent of the final
`NP_not_subset_PpolyDAG` endpoint. It isolates the core contradiction step:

`global DAG witness` + `magnification-style no-small-solver` -> `False`.
-/
theorem not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hNoSmall :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  intro hDagGlobal
  have hSlices :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    ppolyDAGOnSlices_of_globalWitness F bridge hDagGlobal
  let hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    inPpolyDAGFamilyOnSlices_of_PpolyDAG F hSlices
  have hBarrier :
      ∃ ε : Rat, 0 < ε ∧
        ∃ β0 : Rat, 0 < β0 ∧
          ∀ β : Rat, 0 < β → β < β0 →
            ∃ n0 : Nat, ∀ n ≥ n0,
              ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
    hNoSmall hInDag
  rcases hBarrier with ⟨ε, hε, β0, hβ0, hEventuallyNo⟩
  -- Choose a concrete β strictly inside the magnification window.
  let β : Rat := β0 / 2
  have hβpos : 0 < β := by
    dsimp [β]
    nlinarith [hβ0]
  have hβlt : β < β0 := by
    dsimp [β]
    nlinarith [hβ0]
  rcases hEventuallyNo β hβpos hβlt with ⟨n0, hnNo⟩
  have hSolverAtN0 :
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n0 β ε :=
    smallDAGSolver_of_inPpolyDAGFamilyOnSlices F hInDag n0 β ε
  exact (hnNo n0 (le_rfl)) hSolverAtN0

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
Builder lemma: derive `SmallDAGImpliesPromiseYesSubcubeAt` from an isolation-style
source property that already yields:
- a YES center `yYes`,
- a coordinate set `S` with the required slack inequality,
- and the fact that every promise-valid input agreeing on `S` lies in YES.

This removes the need for source proofs to produce `DagCircuit.eval C z = true`
directly; correctness on YES then finishes that field automatically.
-/
theorem smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hYesValid :
      ∀ y : Bitstring (GapSliceFamily.encodedLen F n β),
        y ∈ (gapSliceOfParams (F.paramsOf n β)).Yes →
          ValidEncoding (F.paramsOf n β) y)
    (hIso :
      ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
        SizeBound n β ε (DagCircuit.size C) →
        CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
          ∃ yYes : Bitstring (GapSliceFamily.encodedLen F n β),
            yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
            ∃ S : Finset (Fin (GapSliceFamily.tableLen F n β)),
              F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableLen F n β - S.card) ∧
              ∀ z : Bitstring (GapSliceFamily.encodedLen F n β),
                (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                  z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                ValidEncoding (F.paramsOf n β) z →
                AgreeOnValues (p := F.paramsOf n β) S yYes z →
                  z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) :
    SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε := by
  intro C hSize hCorrect
  rcases hIso C hSize hCorrect with ⟨yYes, hyYes, S, hSlack, hAllYes⟩
  refine ⟨yYes, hyYes, hYesValid yYes hyYes, S, hSlack, ?_⟩
  intro z hzPromise hzValid hAgree
  exact hCorrect.1 z (hAllYes z hzPromise hzValid hAgree)

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
Helper: convert a pointwise no-small-solver statement into the explicit
magnification quantifier shape used by
`not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies`.

This keeps the canonical contradiction theorem generic while allowing concrete
weak-route source theorems to plug in without restating quantifier plumbing.
-/
theorem noSmallQuantifierShape_of_pointwiseNoSmall
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hNo : ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε) :
    ∃ ε : Rat, 0 < ε ∧
      ∃ β0 : Rat, 0 < β0 ∧
        ∀ β : Rat, 0 < β → β < β0 →
          ∃ n0 : Nat, ∀ n ≥ n0, ¬ SmallDAGSolver F SizeBound n β ε := by
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro β _hβpos _hβlt
  refine ⟨0, ?_⟩
  intro n _hn
  exact hNo n β 1

/--
Concrete bridge-local contradiction instantiated with the weak accepted-family
source theorem.

If the accepted-family weak route is available for every canonical witness
size-bound family, then the bridged global language is not in `PpolyDAG`.
-/
theorem not_globalPpolyDAG_of_acceptedFamilyWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      (F := F) (bridge := bridge) ?_
  intro hInDag
  have hNoPointwise :
      ∀ n : Nat, ∀ β ε : Rat,
        ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
    no_dag_solver_of_acceptedFamily
      F (ppolyDAGSizeBoundOnSlices F hInDag) (hAcceptedWeak hInDag)
  exact
    noSmallQuantifierShape_of_pointwiseNoSmall
      F (ppolyDAGSizeBoundOnSlices F hInDag) hNoPointwise

/--
Concrete bridge-local contradiction instantiated with the nearer-term one-sided
promise-YES source theorem.
-/
theorem not_globalPpolyDAG_of_promiseYesWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesPromiseYesSubcubeStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      (F := F) (bridge := bridge) ?_
  intro hInDag
  have hNoPointwise :
      ∀ n : Nat, ∀ β ε : Rat,
        ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
    no_dag_solver_of_promise_yes_subcube
      F (ppolyDAGSizeBoundOnSlices F hInDag) (hYesWeak hInDag)
  exact
    noSmallQuantifierShape_of_pointwiseNoSmall
      F (ppolyDAGSizeBoundOnSlices F hInDag) hNoPointwise

/--
Bridge-local contradiction instantiated with an eventual one-sided promise-YES
payload on canonical slices.

Compared with `not_globalPpolyDAG_of_promiseYesWeakRoute`, this theorem accepts
the eventual (`∃ ε, ∃ β0, ...`) source shape directly, without first requiring
the stronger pointwise statement `SmallDAGImpliesPromiseYesSubcubeStatement`.
-/
theorem not_globalPpolyDAG_of_eventuallyPromiseYesWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hEventuallyYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                SmallDAGImpliesPromiseYesSubcubeAt
                  F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      (F := F) (bridge := bridge) ?_
  intro hInDag
  rcases hEventuallyYesWeak hInDag with ⟨ε, hε, β0, hβ0, hEventuallyYes⟩
  refine ⟨ε, hε, β0, hβ0, ?_⟩
  intro β hβPos hβLt
  rcases hEventuallyYes β hβPos hβLt with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact no_dag_solver_of_promise_yes_subcube_at
    F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε (hn0 n hn)

/--
Class-level closure from the weak accepted-family source theorem to
`NP_not_subset_PpolyDAG`, parameterized by an explicit NP witness for
`bridge.L`.
-/
theorem NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact not_globalPpolyDAG_of_acceptedFamilyWeakRoute F bridge hAcceptedWeak

/--
Class-level closure from the one-sided promise-YES weak source theorem to
`NP_not_subset_PpolyDAG`, parameterized by an explicit NP witness for
`bridge.L`.
-/
theorem NP_not_subset_PpolyDAG_of_promiseYesWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesPromiseYesSubcubeStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact not_globalPpolyDAG_of_promiseYesWeakRoute F bridge hYesWeak

/--
Class-level closure from an eventual one-sided promise-YES payload on canonical
slices to `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEventuallyYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                SmallDAGImpliesPromiseYesSubcubeAt
                  F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact not_globalPpolyDAG_of_eventuallyPromiseYesWeakRoute
    F bridge hEventuallyYesWeak

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
Canonical "eventual weak-route payload" extracted from a pointwise
`SmallDAGImpliesPromiseYesSubcubeStatement`.

This helper packages the quantifier shape required by the magnification bridge:
we choose fixed positive constants `ε = 1/4` and `β0 = 1/2`, and use the
pointwise statement directly with cutoff `n0 = 0` on every valid `β < β0`.

The theorem is intentionally generic in `SizeBound`; in the P/poly route it is
instantiated with `SizeBound := ppolyDAGSizeBoundOnSlices F hInDag`.
-/
theorem eventual_promiseYesSubcube_of_smallDAG
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hYes : SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound) :
    ∃ ε : Rat, 0 < ε ∧
      ∃ β0 : Rat, 0 < β0 ∧
        ∀ (β : Rat), 0 < β → β < β0 →
          ∃ n0 : Nat, ∀ n ≥ n0,
            SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε := by
  refine ⟨(1 / 4 : Rat), by positivity, (1 / 2 : Rat), by positivity, ?_⟩
  intro β hβPos hβLt
  refine ⟨0, ?_⟩
  intro n hn
  simpa using hYes n β (1 / 4 : Rat)

/--
Canonical-slice specialization of `eventual_promiseYesSubcube_of_smallDAG`.

This matches the Gate-G1 / bridge-facing shape where the size bound is obtained
from a concrete global witness family via `ppolyDAGSizeBoundOnSlices`.
The proof is purely a specialization step.
-/
theorem eventual_promiseYesSubcube_of_smallDAG_onCanonicalSlices
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)))
    (hYes :
      SmallDAGImpliesPromiseYesSubcubeStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∃ ε : Rat, 0 < ε ∧
      ∃ β0 : Rat, 0 < β0 ∧
        ∀ (β : Rat), 0 < β → β < β0 →
          ∃ n0 : Nat, ∀ n ≥ n0,
            SmallDAGImpliesPromiseYesSubcubeAt
              F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  exact eventual_promiseYesSubcube_of_smallDAG
    F (ppolyDAGSizeBoundOnSlices F hInDag) hYes

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
