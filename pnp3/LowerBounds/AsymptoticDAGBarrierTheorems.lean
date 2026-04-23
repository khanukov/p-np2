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
Refined builder lemma with **local** validity of the chosen YES center.

Compared with `smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt`, this
variant does not assume the global side condition
`∀ y ∈ Yes, ValidEncoding y`.  Instead, the source package returns
`ValidEncoding` for the specific witness center `yYes` it constructs.
-/
theorem smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt_localValid
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hIso :
      ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
        SizeBound n β ε (DagCircuit.size C) →
        CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
          ∃ yYes : Bitstring (GapSliceFamily.encodedLen F n β),
            yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
            ValidEncoding (F.paramsOf n β) yYes ∧
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
  rcases hIso C hSize hCorrect with ⟨yYes, hyYes, hyValidYes, S, hSlack, hAllYes⟩
  refine ⟨yYes, hyYes, hyValidYes, S, hSlack, ?_⟩
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
Canonical eventual promise-YES payload from an isolation+envelope source package.

This theorem packages the generic reduction used in the handoff:
if on each sufficiently large slice every small correct solver admits
- a YES center and coordinate set `D` forcing YES on all agreeing promise-valid
  points,
- a cardinality bound `D.card ≤ κ n β`,
- and a numeric envelope `M < 2^(tableLen - κ n β)`,
then we obtain the eventual `SmallDAGImpliesPromiseYesSubcubeAt` payload on
canonical bounds (with fixed `ε = 1`).
-/
theorem eventual_promiseYesSubcube_onCanonicalSlices_of_eventualIsolationEnvelope
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)))
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hIso :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ nIso β →
        ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
          ppolyDAGSizeBoundOnSlices F hInDag n β 1 (DagCircuit.size C) →
          CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
            ∃ yYes : Bitstring (GapSliceFamily.encodedLen F n β),
              yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
              ValidEncoding (F.paramsOf n β) yYes ∧
              ∃ D : Finset (Fin (GapSliceFamily.tableLen F n β)),
                D.card ≤ κ n β ∧
                ∀ z : Bitstring (GapSliceFamily.encodedLen F n β),
                  (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                    z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                  ValidEncoding (F.paramsOf n β) z →
                  AgreeOnValues (p := F.paramsOf n β) D yYes z →
                    z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes)
    (hSlackEnvelope :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ nIso β →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamily.tableLen F n β - κ n β)) :
    ∃ ε : Rat, 0 < ε ∧
      ∃ β0' : Rat, 0 < β0' ∧
        ∀ β : Rat, 0 < β → β < β0' →
          ∃ n0 : Nat, ∀ n ≥ n0,
            SmallDAGImpliesPromiseYesSubcubeAt
              F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  refine ⟨(1 : Rat), by norm_num, β0, hβ0, ?_⟩
  intro β hβPos hβLt
  refine ⟨nIso β, ?_⟩
  intro n hn
  refine smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt_localValid
    F (ppolyDAGSizeBoundOnSlices F hInDag) n β 1 ?_
  intro C hSize hCorrect
  rcases hIso n β hβPos hβLt hn C hSize hCorrect with
    ⟨yYes, hyYes, hyValidYes, D, hDCard, hAllYes⟩
  refine ⟨yYes, hyYes, hyValidYes, D, ?_, hAllYes⟩
  have hSub :
      GapSliceFamily.tableLen F n β - κ n β ≤
        GapSliceFamily.tableLen F n β - D.card :=
    Nat.sub_le_sub_left hDCard (GapSliceFamily.tableLen F n β)
  have hPowNat :
      (2 ^ (GapSliceFamily.tableLen F n β - κ n β) : Nat) ≤
        (2 ^ (GapSliceFamily.tableLen F n β - D.card) : Nat) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hSub
  exact lt_of_lt_of_le (hSlackEnvelope n β hβPos hβLt hn) hPowNat

/--
Class-level closure from an eventual isolation-envelope family package.

This theorem is the direct code-level endpoint for the handoff contract:
once the family provides the eventual isolation+envelope data uniformly for
every canonical witness family, `NP_not_subset_PpolyDAG` follows mechanically.
-/
theorem NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hIsoFamily :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ β0 : Rat, 0 < β0 ∧
          ∃ κ : Nat → Rat → Nat,
            ∃ nIso : Rat → Nat,
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ nIso β →
                ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
                  ppolyDAGSizeBoundOnSlices F hInDag n β 1 (DagCircuit.size C) →
                  CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
                    ∃ yYes : Bitstring (GapSliceFamily.encodedLen F n β),
                      yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                      ValidEncoding (F.paramsOf n β) yYes ∧
                      ∃ D : Finset (Fin (GapSliceFamily.tableLen F n β)),
                        D.card ≤ κ n β ∧
                        ∀ z : Bitstring (GapSliceFamily.encodedLen F n β),
                          (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                          ValidEncoding (F.paramsOf n β) z →
                          AgreeOnValues (p := F.paramsOf n β) D yYes z →
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ nIso β →
                  F.Mof n (F.Tof n β) <
                    2 ^ (GapSliceFamily.tableLen F n β - κ n β))) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRoute F bridge hNP ?_
  intro hInDag
  rcases hIsoFamily hInDag with ⟨β0, hβ0, κ, nIso, hIso, hSlackEnvelope⟩
  exact eventual_promiseYesSubcube_onCanonicalSlices_of_eventualIsolationEnvelope
    F hInDag β0 hβ0 κ nIso hIso hSlackEnvelope

/-!
## Non-vacuous eventual-carrier route (`GapSliceFamilyEventually`)

The legacy wrappers above are parametrized by `GapSliceFamily` (kept for
compatibility).  The declarations below lift the same route to the non-vacuous
carrier `GapSliceFamilyEventually`.
-/

/-- Canonical DAG-size bound on eventual slices. -/
def ppolyDAGSizeBoundOnSlicesEventually
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    Nat → Rat → Rat → Nat → Prop :=
  fun n β _ε s =>
    s ≤ (hInDag n β).polyBound (GapSliceFamilyEventually.encodedLen F n β)

/-- Eventual-slice analogue of `SmallDAGSolver`. -/
def SmallDAGSolverEventually
    (F : GapSliceFamilyEventually)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  ∃ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) ∧
      CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β))

/--
Eventual-slice analogue of the one-sided YES-centered source predicate.
-/
def SmallDAGImpliesPromiseYesSubcubeAtEventually
    (F : GapSliceFamilyEventually)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
        yYes ∈ (gapSliceOfParams p).Yes ∧
        ValidEncoding p yYes ∧
        ∃ S : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - S.card) ∧
          ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
            (z ∈ (gapSliceOfParams p).Yes ∨ z ∈ (gapSliceOfParams p).No) →
            ValidEncoding p z →
            AgreeOnValues (p := p) S yYes z →
            DagCircuit.eval C z = true

/--
Eventual-carrier local-validity builder.
-/
theorem smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt_localValid_eventually
    (F : GapSliceFamilyEventually)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hIso :
      ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
        SizeBound n β ε (DagCircuit.size C) →
        CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
          ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
            yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
            ValidEncoding (F.paramsOf n β) yYes ∧
            ∃ S : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
              F.Mof n (F.Tof n β) <
                2 ^ (GapSliceFamilyEventually.tableLen F n β - S.card) ∧
              ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                  z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                ValidEncoding (F.paramsOf n β) z →
                AgreeOnValues (p := F.paramsOf n β) S yYes z →
                  z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) :
    SmallDAGImpliesPromiseYesSubcubeAtEventually F SizeBound n β ε := by
  intro C hSize hCorrect
  rcases hIso C hSize hCorrect with ⟨yYes, hyYes, hyValid, S, hSlack, hForce⟩
  refine ⟨yYes, hyYes, hyValid, S, hSlack, ?_⟩
  intro z hzPromise hzValid hAgree
  exact hCorrect.1 z (hForce z hzPromise hzValid hAgree)

/-- Coherence rewrite used in eventual closure steps (`n ≥ F.N0`). -/
theorem eventual_coherence_at
    (F : GapSliceFamilyEventually)
    (n : Nat) (β : Rat)
    (hn0 : F.N0 ≤ n) :
    (F.paramsOf n β).n = n ∧
      F.Tof n β = (F.paramsOf n β).sNO - 1 ∧
      F.Mof n (F.Tof n β) =
        Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
  constructor
  · exact F.hIndex n hn0 β
  constructor
  · exact F.hT n hn0 β
  · calc
      F.Mof n (F.Tof n β)
          = Models.circuitCountBound n (F.Tof n β) := by
              simpa using F.hM n hn0 (F.Tof n β)
      _ = Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
            simp [F.hIndex n hn0 β, F.hT n hn0 β]

/--
At the canonical encoded length, every input belongs to `Yes ∪ No`.

This packages the Bool totality of `gapPartialMCSP_Language` into slice
membership form and is useful for simplifying source payloads.
-/
lemma mem_yes_or_no_gapSliceOfParams
    (p : GapPartialMCSPParams)
    (x : Bitstring (partialInputLen p)) :
    x ∈ (gapSliceOfParams p).Yes ∨ x ∈ (gapSliceOfParams p).No := by
  cases hLang : gapPartialMCSP_Language p (partialInputLen p) x <;>
    simp [gapSliceOfParams, hLang]

/--
Strong family-specific isolation package (without explicit `Yes ∨ No` premise in
the forcing clause).

This is the narrowed source contract after introducing
`mem_yes_or_no_gapSliceOfParams`.
-/
def IsoStrongFamilyEventually
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) : Prop :=
  ∃ β0 : Rat, 0 < β0 ∧
    ∃ κ : Nat → Rat → Nat,
      ∃ nIso : Rat → Nat,
        (∀ n : Nat, ∀ β : Rat,
          0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
            ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
            CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
              ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                ValidEncoding (F.paramsOf n β) yYes ∧
                ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                  D.card ≤ κ n β ∧
                  ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                    ValidEncoding (F.paramsOf n β) z →
                    AgreeOnValues (p := F.paramsOf n β) D yYes z →
                      z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
        (∀ n : Nat, ∀ β : Rat,
          0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
            F.Mof n (F.Tof n β) <
              2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β))

/--
Adapter from the stronger source contract (`IsoStrongFamilyEventually`) to the
wrapper-ready contract with an explicit `Yes ∨ No` premise.

The only extra step is inserting
`mem_yes_or_no_gapSliceOfParams (p := F.paramsOf n β) z`.
-/
theorem isoFamily_withPromise_of_isoStrongFamilyEventually
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)))
    (hStrong : IsoStrongFamilyEventually F hInDag) :
    ∃ β0 : Rat, 0 < β0 ∧
      ∃ κ : Nat → Rat → Nat,
        ∃ nIso : Rat → Nat,
          (∀ n : Nat, ∀ β : Rat,
            0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
            ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
              ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
              CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
                ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                  yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                  ValidEncoding (F.paramsOf n β) yYes ∧
                  ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                    D.card ≤ κ n β ∧
                    ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                      (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                        z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                      ValidEncoding (F.paramsOf n β) z →
                      AgreeOnValues (p := F.paramsOf n β) D yYes z →
                        z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
          (∀ n : Nat, ∀ β : Rat,
            0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
              F.Mof n (F.Tof n β) <
                2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β)) := by
  rcases hStrong with ⟨β0, hβ0, κ, nIso, hIsoStrong, hSlack⟩
  refine ⟨β0, hβ0, κ, nIso, ?_, hSlack⟩
  intro n β hβPos hβLt hn C hSize hCorrect
  rcases hIsoStrong n β hβPos hβLt hn C hSize hCorrect with
    ⟨yYes, hyYes, hyValid, D, hDCard, hForce⟩
  refine ⟨yYes, hyYes, hyValid, D, hDCard, ?_⟩
  intro z hzPromise hzValid hzAgree
  have _hzAutoFromAssumption :
      z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
      z ∈ (gapSliceOfParams (F.paramsOf n β)).No := hzPromise
  have _hzAutoCanonical :
      z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
      z ∈ (gapSliceOfParams (F.paramsOf n β)).No :=
    mem_yes_or_no_gapSliceOfParams (p := F.paramsOf n β) z
  -- `hzPromise` is now redundant: the strong forcing hypothesis already ignores it.
  exact hForce z hzValid hzAgree

/--
Table-level forcing package requested for family-specific handoff.

This is often the cleanest source surface: the forcing condition is stated on
`PartialTruthTable`s instead of raw bitstrings.
-/
def tableForceFamilyEventually
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat) : Prop :=
  ∀ n : Nat, ∀ β : Rat,
    0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
    let p := F.paramsOf n β
    ∃ Ty : PartialTruthTable p.n,
      PartialMCSP_YES p Ty ∧
      ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
        D.card ≤ κ n β ∧
        ∀ T : PartialTruthTable p.n,
          (∀ i ∈ D,
            Partial.valPart (encodePartial T) i =
            Partial.valPart (encodePartial Ty) i) →
          PartialMCSP_YES p T

/--
Pattern-oriented family package (`D + a*`) that is stronger than the table-force
form and is often natural for witness-coordinate constructions.
-/
def patternForceFamilyEventually
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat) : Prop :=
  ∀ n : Nat, ∀ β : Rat,
    0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
    let p := F.paramsOf n β
    ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
      D.card ≤ κ n β ∧
      ∃ aStar : Fin (GapSliceFamilyEventually.tableLen F n β) → Bool,
        ∃ Ty : PartialTruthTable p.n,
          PartialMCSP_YES p Ty ∧
          (∀ i ∈ D,
            Partial.valPart (encodePartial Ty) i = aStar i) ∧
          ∀ T : PartialTruthTable p.n,
            (∀ i ∈ D,
              Partial.valPart (encodePartial T) i = aStar i) →
            PartialMCSP_YES p T

/--
`patternForceFamilyEventually` immediately implies
`tableForceFamilyEventually` by choosing the same `Ty` and eliminating `a*`.
-/
theorem tableForceFamilyEventually_of_patternForceFamilyEventually
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hPattern : patternForceFamilyEventually F β0 κ nIso) :
    tableForceFamilyEventually F β0 κ nIso := by
  intro n β hβPos hβLt hn
  rcases hPattern n β hβPos hβLt hn with ⟨D, hDCard, aStar, Ty, hTyYes, hTyPat, hForce⟩
  refine ⟨Ty, hTyYes, D, hDCard, ?_⟩
  intro T hEqTy
  apply hForce T
  intro i hi
  calc
    Partial.valPart (encodePartial T) i = Partial.valPart (encodePartial Ty) i := hEqTy i hi
    _ = aStar i := hTyPat i hi

/--
Build the strong eventual isolation package from a table-level forcing package
plus a slack envelope.

This theorem is the last generic reduction step: it discharges the entire
family-to-wrapper adaptation and leaves only concrete family instantiation
(`F`, `κ`, forcing, slack, slice-constancy, NP-entry`) to the source side.
-/
theorem isoStrongFamilyEventually_of_tableForceFamilyEventually
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSlack :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
      IsoStrongFamilyEventually F hInDag := by
  intro hInDag
  refine ⟨β0, hβ0, κ, nIso, ?_, hSlack⟩
  intro n β hβPos hβLt hn _C _hSize _hCorrect
  -- `_C`, `_hSize`, `_hCorrect` are part of the wrapper shape but are not needed
  -- by pure table-level forcing.
  let p := F.paramsOf n β
  rcases hTable n β hβPos hβLt hn with ⟨Ty, hTyYes, D, hDCard, hTableForce⟩
  let yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β) := encodePartial Ty
  have hyYesYes : yYes ∈ (gapSliceOfParams p).Yes := by
    have hLangTrue :
      gapPartialMCSP_Language p (partialInputLen p) yYes = true := by
      -- Use the canonical-length language characterization and the explicit
      -- decode-after-encode lemma from the partial-table model.
      exact (gapPartialMCSP_language_true_iff_yes p yYes).2 (by
        simpa [yYes, decodePartial_encodePartial] using hTyYes)
    simpa [gapSliceOfParams, p, GapSliceFamilyEventually.encodedLen, yYes] using hLangTrue
  have hyYesValid : ValidEncoding p yYes := by
    simpa [p, yYes] using validEncoding_encodePartial p Ty
  refine ⟨yYes, hyYesYes, hyYesValid, D, hDCard, ?_⟩
  intro z hzValid hzAgree
  have hzCanonical : z = encodePartial (decodePartial z) := hzValid
  have hEqOnD :
      ∀ i ∈ D,
        Partial.valPart (encodePartial (decodePartial z)) i =
          Partial.valPart (encodePartial Ty) i := by
    intro i hi
    have hAgreeZi : Partial.valPart z i = Partial.valPart yYes i := Eq.symm (hzAgree i hi)
    have hCanonicalVal :
        Partial.valPart (encodePartial (decodePartial z)) i =
          Partial.valPart z i :=
      congrArg (fun x => Partial.valPart x i) (Eq.symm hzCanonical)
    calc
      Partial.valPart (encodePartial (decodePartial z)) i = Partial.valPart z i := hCanonicalVal
      _ = Partial.valPart yYes i := hAgreeZi
      _ = Partial.valPart (encodePartial Ty) i := by simp [yYes]
  have hYesDecoded : PartialMCSP_YES p (decodePartial z) := hTableForce (decodePartial z) hEqOnD
  have hLangTrue :
      gapPartialMCSP_Language p (partialInputLen p) z = true :=
    (gapPartialMCSP_language_true_iff_yes p z).2 hYesDecoded
  simpa [gapSliceOfParams] using hLangTrue

/-- Canonical global language representative for eventual family routes. -/
noncomputable def canonicalGlobalLanguageEventually
    (F : GapSliceFamilyEventually) : Language :=
  gapPartialMCSP_Language (F.paramsOf F.N0 (1 : Rat))

/--
Pairwise constancy of slice languages against one canonical representative.
-/
def sliceConstFamilyEventually
    (F : GapSliceFamilyEventually) : Prop :=
  ∀ n : Nat, ∀ β : Rat, ∀ N : Nat, ∀ x : Bitstring N,
    canonicalGlobalLanguageEventually F N x =
      gapPartialMCSP_Language (F.paramsOf n β) N x

/--
Eventual envelope package -> eventual one-sided promise-YES payload on canonical
bounds (non-vacuous carrier).
-/
theorem eventual_promiseYesSubcube_onCanonicalSlices_of_eventualIsolationEnvelopeEventually
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)))
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hIso :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
        ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
          ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
          CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
            ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
              yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
              ValidEncoding (F.paramsOf n β) yYes ∧
              ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                D.card ≤ κ n β ∧
                ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                  (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                    z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                  ValidEncoding (F.paramsOf n β) z →
                  AgreeOnValues (p := F.paramsOf n β) D yYes z →
                    z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes)
    (hSlackEnvelope :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β)) :
    ∃ ε : Rat, 0 < ε ∧
      ∃ β0' : Rat, 0 < β0' ∧
        ∀ β : Rat, 0 < β → β < β0' →
          ∃ n0 : Nat, F.N0 ≤ n0 ∧
            ∀ n ≥ n0,
              SmallDAGImpliesPromiseYesSubcubeAtEventually
                F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε := by
  refine ⟨(1 : Rat), by norm_num, β0, hβ0, ?_⟩
  intro β hβPos hβLt
  refine ⟨max F.N0 (nIso β), le_max_left _ _, ?_⟩
  intro n hn
  refine smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt_localValid_eventually
    F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β 1 ?_
  intro C hSize hCorrect
  rcases hIso n β hβPos hβLt hn C hSize hCorrect with
    ⟨yYes, hyYes, hyValidYes, D, hDCard, hAllYes⟩
  refine ⟨yYes, hyYes, hyValidYes, D, ?_, hAllYes⟩
  have hSub :
      GapSliceFamilyEventually.tableLen F n β - κ n β ≤
        GapSliceFamilyEventually.tableLen F n β - D.card :=
    Nat.sub_le_sub_left hDCard (GapSliceFamilyEventually.tableLen F n β)
  have hPowNat :
      (2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β) : Nat) ≤
        (2 ^ (GapSliceFamilyEventually.tableLen F n β - D.card) : Nat) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hSub
  exact lt_of_lt_of_le (hSlackEnvelope n β hβPos hβLt hn) hPowNat

/--
Bridge package connecting one global language to all eventual slice languages.
-/
structure AsymptoticDAGLanguageBridgeEventually
    (F : GapSliceFamilyEventually) : Type where
  L : Language
  sliceEq :
    ∀ n : Nat, ∀ β : Rat, ∀ N : Nat, ∀ x : Bitstring N,
      L N x = gapPartialMCSP_Language (F.paramsOf n β) N x

/--
Canonical-length-only bridge (non-collapsing variant).

This is the mathematically safe eventual bridge: agreement is required only on
the canonical encoded length of each slice.
-/
structure AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths
    (F : GapSliceFamilyEventually) : Type where
  L : Language
  sliceEq :
    ∀ n : Nat, ∀ β : Rat,
      ∀ x : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
        L (GapSliceFamilyEventually.encodedLen F n β) x =
          gapPartialMCSP_Language (F.paramsOf n β)
            (GapSliceFamilyEventually.encodedLen F n β) x

/-- One-gate constant-false DAG used off canonical lengths. -/
private def constFalseDag (n : Nat) : ComplexityInterfaces.DagCircuit n where
  gates := 1
  gate := fun _ => ComplexityInterfaces.DagGate.const false
  output := ComplexityInterfaces.DagWire.gate ⟨0, by simp⟩

@[simp] private theorem constFalseDag_size {n : Nat} :
    ComplexityInterfaces.DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, ComplexityInterfaces.DagCircuit.size]

@[simp] private theorem constFalseDag_eval {n : Nat}
    (x : ComplexityInterfaces.Bitstring n) :
    ComplexityInterfaces.DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, ComplexityInterfaces.DagCircuit.eval,
    ComplexityInterfaces.DagCircuit.eval.evalGateAt]

/-- Monotone padding used for the canonical-length transport witness. -/
private theorem dag_poly_bound_lift (n c : Nat) :
    n ^ c + c ≤ n ^ (c + 2) + (c + 2) := by
  by_cases hn : n = 0
  · subst hn
    cases c <;> simp
  · have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hpow : n ^ c ≤ n ^ (c + 2) := by
      simpa [Nat.add_assoc] using Nat.pow_le_pow_right h1 (Nat.le_add_right c 2)
    have hc : c ≤ c + 2 := by omega
    exact Nat.add_le_add hpow hc

/--
Construct the eventual bridge object from pairwise slice constancy.
-/
noncomputable def bridgeEventually_of_sliceConst
    (F : GapSliceFamilyEventually)
    (hConst : sliceConstFamilyEventually F) :
    AsymptoticDAGLanguageBridgeEventually F where
  L := canonicalGlobalLanguageEventually F
  sliceEq := hConst

/-- Transport global `PpolyDAG` witness to all eventual slices. -/
theorem ppolyDAGOnSlicesEventually_of_globalWitness
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventually F)
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
  exact (w.correct N x).trans (bridge.sliceEq n β N x)

/--
Transport from a global witness using the canonical-length-only bridge.

On the target canonical length we reuse the global witness family.
Off that length we use `constFalseDag`; correctness is immediate because
`gapPartialMCSP_Language` is definitionally `false` off canonical length.
-/
theorem ppolyDAGOnSlicesEventually_of_globalWitness_atCanonicalLengths
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F)
    (hDagGlobal : ComplexityInterfaces.PpolyDAG bridge.L) :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_Language (F.paramsOf n β)) := by
  rcases hDagGlobal with ⟨w, -⟩
  intro n β
  let N0 := GapSliceFamilyEventually.encodedLen F n β
  rcases w.polyBound_poly with ⟨c, hc⟩
  refine ⟨{ polyBound := fun N => N ^ (c + 2) + (c + 2)
            polyBound_poly := ?_
            family := fun N => if hN : N = N0 then w.family N else constFalseDag N
            family_size_le := ?_
            correct := ?_ }, trivial⟩
  · refine ⟨c + 2, ?_⟩
    intro N
    rfl
  · intro N
    by_cases hN : N = N0
    · cases hN
      simp
      exact Nat.le_trans (w.family_size_le N0) (Nat.le_trans (hc N0) (dag_poly_bound_lift N0 c))
    · simp [hN]
      have hTwo : 2 ≤ c + 2 := by omega
      exact Nat.le_trans hTwo (Nat.le_add_left (c + 2) (N ^ (c + 2)))
  · intro N x
    by_cases hN : N = N0
    · subst hN
      have hGlobal :
          DagCircuit.eval (w.family N0) x = bridge.L N0 x := w.correct N0 x
      have hSlice :
          bridge.L N0 x =
            gapPartialMCSP_Language (F.paramsOf n β) N0 x :=
        bridge.sliceEq n β x
      simpa [N0] using hGlobal.trans hSlice
    · have hOff :
        gapPartialMCSP_Language (F.paramsOf n β) N x = false := by
          have hLen :
              N ≠ partialInputLen (F.paramsOf n β) := by
            simpa [GapSliceFamilyEventually.encodedLen, N0] using hN
          simp [gapPartialMCSP_Language, hLen]
      simp [hN, hOff]

/-- Canonical small-solver witness on eventual slices from `InPpolyDAG` witnesses. -/
theorem smallDAGSolverEventually_of_inPpolyDAGFamilyOnSlices
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    ∀ n : Nat, ∀ β ε : Rat,
      SmallDAGSolverEventually
        F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε := by
  intro n β ε
  let w : ComplexityInterfaces.InPpolyDAG
      (gapPartialMCSP_Language (F.paramsOf n β)) := hInDag n β
  refine ⟨w.family (GapSliceFamilyEventually.encodedLen F n β), ?_, ?_⟩
  · simpa [ppolyDAGSizeBoundOnSlicesEventually] using
      w.family_size_le (GapSliceFamilyEventually.encodedLen F n β)
  · constructor
    · intro x hxYes
      have hxLang :
          gapPartialMCSP_Language (F.paramsOf n β)
              (GapSliceFamilyEventually.encodedLen F n β) x = true := by
        simpa [gapSliceOfParams] using hxYes
      exact (w.correct (GapSliceFamilyEventually.encodedLen F n β) x).trans hxLang
    · intro x hxNo
      have hxLang :
          gapPartialMCSP_Language (F.paramsOf n β)
              (GapSliceFamilyEventually.encodedLen F n β) x = false := by
        simpa [gapSliceOfParams] using hxNo
      exact (w.correct (GapSliceFamilyEventually.encodedLen F n β) x).trans hxLang

/--
Single-slice contradiction on the eventual carrier (requires `n ≥ F.N0` for
coherence rewrites from `F.Mof/F.Tof` to the counting theorem format).
-/
theorem no_dag_solver_of_promise_yes_subcube_at_eventually
    (F : GapSliceFamilyEventually)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat)
    (hn0 : F.N0 ≤ n)
    (hYes :
      SmallDAGImpliesPromiseYesSubcubeAtEventually F SizeBound n β ε) :
    ¬ SmallDAGSolverEventually F SizeBound n β ε := by
  intro hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let p := F.paramsOf n β
  rcases hYes C hSize hCorrect with ⟨yYes, hyYes, hyValidYes, S, hSlack, hAccept⟩
  have hcoh := eventual_coherence_at F n β hn0
  rcases hcoh with ⟨hpn, hTof, hMof⟩
  have hSlack' :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - S.card) := by
    calc
      Models.circuitCountBound p.n (p.sNO - 1)
          = Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
              simp [p]
      _ = F.Mof n (F.Tof n β) := by simpa [hMof]
      _ < 2 ^ (GapSliceFamilyEventually.tableLen F n β - S.card) := hSlack
      _ = 2 ^ (Models.Partial.tableLen p.n - S.card) := by
            simp [GapSliceFamilyEventually.tableLen, p, hpn]
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
Non-vacuous global contradiction schema for eventual-carrier one-sided
promise-YES payloads.
-/
theorem not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventually F)
    (hEventuallyYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, F.N0 ≤ n0 ∧
                ∀ n ≥ n0,
                  SmallDAGImpliesPromiseYesSubcubeAtEventually
                    F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  intro hDagGlobal
  have hSlices :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    ppolyDAGOnSlicesEventually_of_globalWitness F bridge hDagGlobal
  let hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    fun n β => Classical.choose (hSlices n β)
  rcases hEventuallyYesWeak hInDag with ⟨ε, hε, β0, hβ0, hEventuallyYes⟩
  let β : Rat := β0 / 2
  have hβpos : 0 < β := by
    dsimp [β]
    nlinarith [hβ0]
  have hβlt : β < β0 := by
    dsimp [β]
    nlinarith [hβ0]
  rcases hEventuallyYes β hβpos hβlt with ⟨n0, hn0_ge, hNoAtLarge⟩
  have hSolverAtN0 :
      SmallDAGSolverEventually
        F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n0 β ε :=
    smallDAGSolverEventually_of_inPpolyDAGFamilyOnSlices F hInDag n0 β ε
  exact
    (no_dag_solver_of_promise_yes_subcube_at_eventually
      F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n0 β ε hn0_ge
      (hNoAtLarge n0 (le_rfl))) hSolverAtN0

/--
Canonical-length variant of
`not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually`.

This is the non-collapsing bridge surface: global/slice agreement is only
required on encoded lengths of the target slices.
-/
theorem not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually_atCanonicalLengths
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F)
    (hEventuallyYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, F.N0 ≤ n0 ∧
                ∀ n ≥ n0,
                  SmallDAGImpliesPromiseYesSubcubeAtEventually
                    F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  intro hDagGlobal
  have hSlices :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    ppolyDAGOnSlicesEventually_of_globalWitness_atCanonicalLengths F bridge hDagGlobal
  let hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)) :=
    fun n β => Classical.choose (hSlices n β)
  rcases hEventuallyYesWeak hInDag with ⟨ε, hε, β0, hβ0, hEventuallyYes⟩
  let β : Rat := β0 / 2
  have hβpos : 0 < β := by
    dsimp [β]
    nlinarith [hβ0]
  have hβlt : β < β0 := by
    dsimp [β]
    nlinarith [hβ0]
  rcases hEventuallyYes β hβpos hβlt with ⟨n0, hn0_ge, hNoAtLarge⟩
  have hSolverAtN0 :
      SmallDAGSolverEventually
        F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n0 β ε :=
    smallDAGSolverEventually_of_inPpolyDAGFamilyOnSlices F hInDag n0 β ε
  exact
    (no_dag_solver_of_promise_yes_subcube_at_eventually
      F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n0 β ε hn0_ge
      (hNoAtLarge n0 (le_rfl))) hSolverAtN0

/-- Class-level endpoint from eventual-carrier one-sided promise-YES payloads. -/
theorem NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventually F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEventuallyYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, F.N0 ≤ n0 ∧
                ∀ n ≥ n0,
                  SmallDAGImpliesPromiseYesSubcubeAtEventually
                    F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually
    F bridge hEventuallyYesWeak

/--
Class-level endpoint from eventual-carrier one-sided promise-YES payloads on
the canonical-length bridge surface.
-/
theorem NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually_atCanonicalLengths
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEventuallyYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, F.N0 ≤ n0 ∧
                ∀ n ≥ n0,
                  SmallDAGImpliesPromiseYesSubcubeAtEventually
                    F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually_atCanonicalLengths
    F bridge hEventuallyYesWeak

/--
Non-vacuous eventual isolation-envelope -> NP endpoint.
-/
theorem NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventually F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hIsoFamily :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ β0 : Rat, 0 < β0 ∧
          ∃ κ : Nat → Rat → Nat,
            ∃ nIso : Rat → Nat,
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
                  ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
                  CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
                    ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                      yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                      ValidEncoding (F.paramsOf n β) yYes ∧
                      ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                        D.card ≤ κ n β ∧
                        ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                          (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                          ValidEncoding (F.paramsOf n β) z →
                          AgreeOnValues (p := F.paramsOf n β) D yYes z →
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                  F.Mof n (F.Tof n β) <
                    2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β))) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually
    F bridge hNP ?_
  intro hInDag
  rcases hIsoFamily hInDag with ⟨β0, hβ0, κ, nIso, hIso, hSlackEnvelope⟩
  exact eventual_promiseYesSubcube_onCanonicalSlices_of_eventualIsolationEnvelopeEventually
    F hInDag β0 hβ0 κ nIso hIso hSlackEnvelope

/--
Canonical-length bridge variant of the eventual isolation-envelope endpoint.

Compared to `...WeakRouteEventually`, this endpoint requires only
canonical-length agreement between the global language and each slice.
-/
theorem NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_atCanonicalLengths
    (F : GapSliceFamilyEventually)
    (bridge : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hIsoFamily :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ β0 : Rat, 0 < β0 ∧
          ∃ κ : Nat → Rat → Nat,
            ∃ nIso : Rat → Nat,
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
                  ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
                  CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
                    ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                      yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                      ValidEncoding (F.paramsOf n β) yYes ∧
                      ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                        D.card ≤ κ n β ∧
                        ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                          (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                          ValidEncoding (F.paramsOf n β) z →
                          AgreeOnValues (p := F.paramsOf n β) D yYes z →
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                  F.Mof n (F.Tof n β) <
                    2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β))) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually_atCanonicalLengths
    F bridge hNP ?_
  intro hInDag
  rcases hIsoFamily hInDag with ⟨β0, hβ0, κ, nIso, hIso, hSlackEnvelope⟩
  exact eventual_promiseYesSubcube_onCanonicalSlices_of_eventualIsolationEnvelopeEventually
    F hInDag β0 hβ0 κ nIso hIso hSlackEnvelope

/--
Convenience endpoint: use `(hSliceConst, hNP0)` instead of explicitly passing a
bridge object.
-/
theorem NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_of_sliceConst
    (F : GapSliceFamilyEventually)
    (hSliceConst : sliceConstFamilyEventually F)
    (hNP0 : ComplexityInterfaces.NP (canonicalGlobalLanguageEventually F))
    (hIsoFamily :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ β0 : Rat, 0 < β0 ∧
          ∃ κ : Nat → Rat → Nat,
            ∃ nIso : Rat → Nat,
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
                  ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
                  CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
                    ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                      yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                      ValidEncoding (F.paramsOf n β) yYes ∧
                      ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                        D.card ≤ κ n β ∧
                        ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                          (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                          ValidEncoding (F.paramsOf n β) z →
                          AgreeOnValues (p := F.paramsOf n β) D yYes z →
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                  F.Mof n (F.Tof n β) <
                    2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β))) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  let bridge : AsymptoticDAGLanguageBridgeEventually F :=
    bridgeEventually_of_sliceConst F hSliceConst
  have hNP : ComplexityInterfaces.NP bridge.L := by
    simpa [bridge, bridgeEventually_of_sliceConst, canonicalGlobalLanguageEventually] using hNP0
  exact NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually
    F bridge hNP hIsoFamily

/--
Deprecated convenience endpoint.

For active/non-collapsing developments prefer
`NP_not_subset_PpolyDAG_of_tableForceSlackEventually_atCanonicalLengths`.
-/
theorem NP_not_subset_PpolyDAG_of_tableForceSlackEventually_of_sliceConst
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSlack :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β))
    (hSliceConst : sliceConstFamilyEventually F)
    (hNP0 : ComplexityInterfaces.NP (canonicalGlobalLanguageEventually F)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_of_sliceConst
    F hSliceConst hNP0 ?_
  intro hInDag
  -- 1) Build the strong forcing package from table-force + slack.
  have hStrong : IsoStrongFamilyEventually F hInDag :=
    isoStrongFamilyEventually_of_tableForceFamilyEventually
      F β0 hβ0 κ nIso hTable hSlack hInDag
  -- 2) Adapt to the wrapper format with explicit `Yes ∨ No`.
  exact isoFamily_withPromise_of_isoStrongFamilyEventually F hInDag hStrong

/--
If all eventual slices are forced equal to one fixed canonical global language
(`sliceConstFamilyEventually`), then every strictly-later canonical slice is
forced into the `No` side.

This theorem formalizes the collapse risk of the convenience `sliceConst`
surface: once `n > F.N0`, the canonical encoded lengths differ, so the fixed
global language evaluates to `false` on that length by definition.
-/
theorem no_membership_on_later_canonical_slice_of_sliceConst
    (F : GapSliceFamilyEventually)
    (hSliceConst : sliceConstFamilyEventually F)
    (n : Nat)
    (β : Rat)
    (hnGt : F.N0 < n)
    (x : Bitstring (GapSliceFamilyEventually.encodedLen F n β)) :
    x ∈ (gapSliceOfParams (F.paramsOf n β)).No := by
  have hnGe : F.N0 ≤ n := Nat.le_of_lt hnGt
  have hIndexN :
      (F.paramsOf n β).n = n := (eventual_coherence_at F n β hnGe).1
  have hIndex0 :
      (F.paramsOf F.N0 (1 : Rat)).n = F.N0 := (eventual_coherence_at F F.N0 (1 : Rat) (le_rfl)).1
  have hLenNe :
      GapSliceFamilyEventually.encodedLen F n β ≠
        GapSliceFamilyEventually.encodedLen F F.N0 (1 : Rat) := by
    intro hEq
    have hEqInputLen : Partial.inputLen n = Partial.inputLen F.N0 := by
      simpa [GapSliceFamilyEventually.encodedLen, partialInputLen, hIndexN, hIndex0] using hEq
    exact (Nat.ne_of_gt hnGt) (Models.partialInputLen_injective hEqInputLen)
  have hCanonFalse :
      canonicalGlobalLanguageEventually F (GapSliceFamilyEventually.encodedLen F n β) x = false := by
    have hNe :
        GapSliceFamilyEventually.encodedLen F n β ≠
          partialInputLen (F.paramsOf F.N0 (1 : Rat)) := by
      simpa [GapSliceFamilyEventually.encodedLen] using hLenNe
    simp [canonicalGlobalLanguageEventually, gapPartialMCSP_Language, hNe]
  have hSliceFalse :
      gapPartialMCSP_Language (F.paramsOf n β)
        (GapSliceFamilyEventually.encodedLen F n β) x = false := by
    simpa [hSliceConst n β (GapSliceFamilyEventually.encodedLen F n β) x] using hCanonFalse
  simpa [gapSliceOfParams] using hSliceFalse

/--
`tableForceFamilyEventually` and `sliceConstFamilyEventually` are incompatible
on nontrivial eventual carriers (strictly after `F.N0`).

This extracts the concrete contradiction used to audit the convenience
`..._of_sliceConst` route.
-/
theorem false_of_tableForceFamilyEventually_and_sliceConst
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSliceConst : sliceConstFamilyEventually F) :
    False := by
  let β : Rat := β0 / 2
  have hβPos : 0 < β := by
    dsimp [β]
    nlinarith [hβ0]
  have hβLt : β < β0 := by
    dsimp [β]
    nlinarith [hβ0]
  let n : Nat := max (F.N0 + 1) (nIso β)
  have hnGe : n ≥ max F.N0 (nIso β) := by
    dsimp [n]
    exact max_le (Nat.le_trans (Nat.le_add_right F.N0 1) (Nat.le_max_left _ _))
      (Nat.le_max_right _ _)
  have hnGt : F.N0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le (Nat.lt_succ_self F.N0) (Nat.le_max_left _ _)
  rcases hTable n β hβPos hβLt hnGe with ⟨Ty, hTyYes, D, hDCard, hForce⟩
  let p := F.paramsOf n β
  let y : Bitstring (GapSliceFamilyEventually.encodedLen F n β) := encodePartial Ty
  have hyYes : y ∈ (gapSliceOfParams p).Yes := by
    have hLangTrue : gapPartialMCSP_Language p (partialInputLen p) y = true :=
      (gapPartialMCSP_language_true_iff_yes p y).2 (by
        simpa [y, decodePartial_encodePartial] using hTyYes)
    simpa [gapSliceOfParams, p, GapSliceFamilyEventually.encodedLen, y] using hLangTrue
  have hyNo : y ∈ (gapSliceOfParams p).No := by
    simpa [p] using
      no_membership_on_later_canonical_slice_of_sliceConst F hSliceConst n β hnGt y
  have hTrue :
      gapPartialMCSP_Language p (GapSliceFamilyEventually.encodedLen F n β) y = true := by
    simpa [gapSliceOfParams] using hyYes
  have hFalse :
      gapPartialMCSP_Language p (GapSliceFamilyEventually.encodedLen F n β) y = false := by
    simpa [gapSliceOfParams] using hyNo
  have hContra : true = false := by simpa [hFalse] using hTrue
  exact Bool.noConfusion hContra

/--
Counting obstruction for the table-force source contract.

This theorem is independent of `sliceConst`: it shows that, under the intended
MCSP counting semantics (wired through `eventual_coherence_at` and the Shannon
counting witness for prescribed constraints), `tableForceFamilyEventually`
cannot coexist with the standard slack inequality.
-/
theorem false_of_tableForceFamilyEventually_and_slack
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSlack :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β)) :
    False := by
  let β : Rat := β0 / 2
  have hβPos : 0 < β := by
    dsimp [β]
    nlinarith [hβ0]
  have hβLt : β < β0 := by
    dsimp [β]
    nlinarith [hβ0]
  let n : Nat := max F.N0 (nIso β)
  have hn : n ≥ max F.N0 (nIso β) := by
    exact le_rfl
  let p := F.paramsOf n β
  rcases hTable n β hβPos hβLt hn with ⟨Ty, hTyYes, D, hDCard, hForce⟩
  have hcoh := eventual_coherence_at F n β (le_trans (Nat.le_max_left _ _) hn)
  rcases hcoh with ⟨hpn, hTof, hMof⟩
  have hSub :
      GapSliceFamilyEventually.tableLen F n β - κ n β ≤
        GapSliceFamilyEventually.tableLen F n β - D.card :=
    Nat.sub_le_sub_left hDCard (GapSliceFamilyEventually.tableLen F n β)
  have hPowNat :
      (2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β) : Nat) ≤
        (2 ^ (GapSliceFamilyEventually.tableLen F n β - D.card) : Nat) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hSub
  have hSlackCount :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - D.card) := by
    calc
      Models.circuitCountBound p.n (p.sNO - 1)
          = F.Mof n (F.Tof n β) := by
              symm
              simpa [p, hpn] using hMof
      _ < 2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β) :=
        hSlack n β hβPos hβLt hn
      _ ≤ 2 ^ (GapSliceFamilyEventually.tableLen F n β - D.card) := hPowNat
      _ = 2 ^ (Partial.tableLen p.n - D.card) := by
            simp [GapSliceFamilyEventually.tableLen, p, hpn]
  let values : Fin (Partial.tableLen p.n) → Bool :=
    fun i => Partial.valPart (encodePartial Ty) i
  rcases Counting.exists_hard_function_with_value_constraints_of_countingSlack
      p D values hSlackCount with ⟨g, hgValues, hgNo⟩
  have hAgree :
      ∀ i ∈ D,
        Partial.valPart (encodePartial (Models.totalTableToPartial g)) i =
          Partial.valPart (encodePartial Ty) i := by
    intro i hi
    calc
      Partial.valPart (encodePartial (Models.totalTableToPartial g)) i = g i := by
        simp [Models.encodeTotalAsPartial, Models.totalTableToPartial,
          Partial.valPart, encodePartial, Partial.valIndex]
      _ = Partial.valPart (encodePartial Ty) i := by
        simpa [values] using hgValues i hi
  have hYesTotal : PartialMCSP_YES p (Models.totalTableToPartial g) :=
    hForce (Models.totalTableToPartial g) hAgree
  exact partial_no_not_yes p (Models.totalTableToPartial g) hgNo hYesTotal

/--
Historical canonical-length endpoint for the table-force/slack route.

This is retained as an audit surface, not as an active unconditional target:
`false_of_tableForceFamilyEventually_and_slack` proves that the source package
`tableForceFamilyEventually + hSlack` is already inconsistent for the intended
MCSP counting semantics. The theorem is therefore only an ex-falso compatibility
endpoint for older callers.
-/
theorem NP_not_subset_PpolyDAG_of_tableForceSlackEventually_atCanonicalLengths
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSlack :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β))
    (bridge : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F)
    (hNP : ComplexityInterfaces.NP bridge.L) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_atCanonicalLengths
    F bridge hNP ?_
  intro hInDag
  have hStrong : IsoStrongFamilyEventually F hInDag :=
    isoStrongFamilyEventually_of_tableForceFamilyEventually
      F β0 hβ0 κ nIso hTable hSlack hInDag
  exact isoFamily_withPromise_of_isoStrongFamilyEventually F hInDag hStrong

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
