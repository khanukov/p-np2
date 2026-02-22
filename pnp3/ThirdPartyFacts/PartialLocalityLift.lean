import Mathlib.Data.Finset.Basic
import Facts.LocalityLift.Exports
import Models.Model_PartialMCSP
import LowerBounds.AntiChecker_Partial
import ThirdPartyFacts.Facts_Switching
import ThirdPartyFacts.PartialTransport
import Core.BooleanBasics
import Magnification.LocalityInterfaces_Partial

/-!
  Bridge between the stand-alone `Facts/LocalityLift` package and the internal
  Partial MCSP solver wrappers.  The external package uses the legacy name
  `GapMCSPParams` for its *numeric* parameters; we only reuse that record as a
  length container.  We map Partial MCSP parameters by shifting `n ↦ n+1`,
  so that input lengths coincide:

    inputLen (n+1) = 2^(n+1) = 2 * 2^n = partialInputLen n.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Facts.LocalityLift
open Models
open LowerBounds
open Magnification

@[simp] def toFactsParamsPartial (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.GapMCSPParams :=
  { n := p.n + 1 }

@[simp] lemma inputLen_toFactsPartial (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.inputLen (toFactsParamsPartial p) = Models.partialInputLen p := by
  simp [toFactsParamsPartial, Facts.LocalityLift.inputLen, Models.partialInputLen,
    Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm]

@[simp] lemma inputLen_toFactsPartial' (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.inputLen { n := p.n + 1 } = Models.partialInputLen p := by
  simpa [toFactsParamsPartial] using inputLen_toFactsPartial p

@[simp] lemma polylogBudget_toFactsPartial (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (toFactsParamsPartial p)) =
      Models.polylogBudget (Models.partialInputLen p) := by
  -- Сводим обе стороны к одинаковому числовому аргументу.
  simp [Facts.LocalityLift.polylogBudget, Models.polylogBudget]

@[simp] lemma polylogBudget_toFactsPartial' (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen { n := p.n + 1 }) =
      Models.polylogBudget (Models.partialInputLen p) := by
  simpa [toFactsParamsPartial] using polylogBudget_toFactsPartial p

@[simp] def toFactsGeneralSolverPartial
    {p : Models.GapPartialMCSPParams}
    (solver : Magnification.SmallGeneralCircuitSolver_Partial p) :
    Facts.LocalityLift.SmallGeneralCircuitSolver (toFactsParamsPartial p) :=
  {
    params :=
      {
        n := solver.params.params.n
        size := solver.params.params.size
        depth := solver.params.params.depth
      }
    same_n := by
      simpa [toFactsParamsPartial, Facts.LocalityLift.inputLen,
        Models.partialInputLen, Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
        using solver.params.same_n
  }

/-- `solver.decide` viewed on the `Facts.LocalityLift.BitVec` domain. -/
@[simp] def solverDecideFacts
    {p : Models.GapPartialMCSPParams}
    (solver : Magnification.SmallGeneralCircuitSolver_Partial p) :
    Facts.LocalityLift.BitVec (Facts.LocalityLift.inputLen (toFactsParamsPartial p)) → Bool :=
  fun x => solver.decide (castBitVec (inputLen_toFactsPartial p) x)

@[simp] def fromFactsLocalParametersPartial
    (params : Facts.LocalityLift.LocalCircuitParameters) :
    ThirdPartyFacts.LocalCircuitParameters :=
  {
    n := params.n
    M := params.M
    ℓ := params.ℓ
    depth := params.depth
  }

@[simp] def fromFactsLocalParamsPartial
    {p : Models.GapPartialMCSPParams}
    (solver : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParamsPartial p)) :
    LowerBounds.SmallLocalCircuitParamsPartial p :=
  {
    params := fromFactsLocalParametersPartial solver.params
    same_n := by
      simpa [fromFactsLocalParametersPartial, toFactsParamsPartial,
        Facts.LocalityLift.inputLen, Models.partialInputLen,
        Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using solver.same_n
    small := by
      simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
        ThirdPartyFacts.LocalCircuitSmallEnough, fromFactsLocalParametersPartial]
        using solver.small
  }

@[simp] def toFactsLocalSolverPartial
    {p : Models.GapPartialMCSPParams}
    (solver : LowerBounds.SmallLocalCircuitSolver_Partial p) :
    Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParamsPartial p) :=
  {
    params :=
      {
        n := solver.params.params.n
        M := solver.params.params.M
        ℓ := solver.params.params.ℓ
        depth := solver.params.params.depth
      }
    same_n := by
      simpa [toFactsParamsPartial, Facts.LocalityLift.inputLen,
        Models.partialInputLen, Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
        using solver.params.same_n
    small := by
      simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
        ThirdPartyFacts.LocalCircuitSmallEnough, toFactsParamsPartial]
        using solver.params.small
  }

/--
Bridge lemma: stability under a restriction implies locality (`decideLocal`)
for the same alive set.
-/
theorem decideLocal_of_stable_restriction
    {p : Models.GapPartialMCSPParams}
    (decide : Core.BitVec (Models.partialInputLen p) → Bool)
    (hStable :
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          decide (r.apply x) = decide x) :
    ∃ (alive : Finset (Fin (Models.partialInputLen p))),
      alive.card ≤ Partial.tableLen p.n / 2 ∧
      ∀ x y : Core.BitVec (Models.partialInputLen p),
        (∀ i ∈ alive, x i = y i) → decide x = decide y := by
  obtain ⟨r, h_card, h_stable⟩ := hStable
  refine ⟨r.alive, h_card, ?_⟩
  exact Facts.LocalityLift.Restriction.localizedOn_of_stable
    (r := r) (f := decide) h_stable

/--
Extract a stability witness on `partialInputLen p` from a provided
`ShrinkageCertificate` for the corresponding Facts-side solver.

The only extra assumption is the target locality bound `|alive| ≤ tableLen/2`
for the certificate restriction.
-/
theorem stableRestriction_of_certificate
    {p : Models.GapPartialMCSPParams}
    (solver : Magnification.SmallGeneralCircuitSolver_Partial p)
    [hCert :
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
        (p := toFactsParamsPartial p)
        (toFactsGeneralSolverPartial solver)
        (solverDecideFacts (p := p) solver)]
    (hCardHalf :
      (Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
          (p := toFactsParamsPartial p)
          (general := toFactsGeneralSolverPartial solver)
          (generalEval := solverDecideFacts (p := p) solver)).restriction.alive.card
        ≤ Partial.tableLen p.n / 2) :
    ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
      r.alive.card ≤ Partial.tableLen p.n / 2 ∧
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x := by
  classical
  let cert :=
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
      (p := toFactsParamsPartial p)
      (general := toFactsGeneralSolverPartial solver)
      (generalEval := solverDecideFacts (p := p) solver)
  let hlen : Facts.LocalityLift.inputLen (toFactsParamsPartial p) = Models.partialInputLen p :=
    inputLen_toFactsPartial p
  let r : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    castRestriction hlen cert.restriction
  refine ⟨r, ?_, ?_⟩
  · simpa [r, cert] using hCardHalf
  · intro x
    have hstable_cast :
        ∀ x0 : Core.BitVec (Facts.LocalityLift.inputLen (toFactsParamsPartial p)),
          solver.decide (castBitVec hlen (cert.restriction.apply x0)) =
            solver.decide (castBitVec hlen x0) := by
      intro x0
      simpa [cert, solverDecideFacts, hlen] using cert.stable x0
    have hstable :=
      stable_of_stable_cast
        (h := hlen) (decide := solver.decide)
        (r := cert.restriction) hstable_cast
    simpa [r] using hstable x

def locality_lift_partial
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver_Partial p)
  (hStable :
    ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
      r.alive.card ≤ Partial.tableLen p.n / 2 ∧
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x)
  (hProvider :
    Facts.LocalityLift.ShrinkageWitness.Provider
      (p := toFactsParamsPartial p)
      (toFactsGeneralSolverPartial solver)) :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth := by
  classical
  letI :
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := toFactsParamsPartial p)
        (toFactsGeneralSolverPartial solver) := hProvider
  obtain ⟨T, locFacts, hT, hM, hℓ, hdepth⟩ :=
    Facts.LocalityLift.locality_lift (toFactsGeneralSolverPartial solver)
  let localParams : LowerBounds.SmallLocalCircuitParamsPartial p :=
    fromFactsLocalParamsPartial (p := p) locFacts
  let localSolver : LowerBounds.SmallLocalCircuitSolver_Partial p :=
    { params := localParams
      sem := solver.sem
      witness := solver.witness
      correct := solver.correct_decide
      decideLocal := by
        exact decideLocal_of_stable_restriction (p := p) solver.decide hStable }
  refine ⟨(by
    simpa [Facts.LocalityLift.BitVec, Core.BitVec, inputLen_toFactsPartial,
      toFactsParamsPartial] using T),
    localSolver, ?_, ?_, ?_, ?_⟩
  · simpa [polylogBudget_toFactsPartial]
      using hT
  · simpa [localParams, localSolver, fromFactsLocalParamsPartial]
      using hM
  · simpa [polylogBudget_toFactsPartial, toFactsParamsPartial, localParams, localSolver,
      fromFactsLocalParamsPartial]
      using hℓ
  · simpa [localParams, localSolver, fromFactsLocalParamsPartial]
      using hdepth

/--
Certificate-driven wrapper: obtain the required stability witness from
`ShrinkageCertificate.Provider` and run `locality_lift_partial`.
-/
def locality_lift_partial_of_certificate
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver_Partial p)
  [hCert :
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
      (p := toFactsParamsPartial p)
      (toFactsGeneralSolverPartial solver)
      (solverDecideFacts (p := p) solver)]
  (hCardHalf :
    (Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
        (p := toFactsParamsPartial p)
        (general := toFactsGeneralSolverPartial solver)
        (generalEval := solverDecideFacts (p := p) solver)).restriction.alive.card
      ≤ Partial.tableLen p.n / 2) :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth := by
  classical
  let cert :=
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
      (p := toFactsParamsPartial p)
      (general := toFactsGeneralSolverPartial solver)
      (generalEval := solverDecideFacts (p := p) solver)
  let hProvider :
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := toFactsParamsPartial p)
        (toFactsGeneralSolverPartial solver) :=
    ⟨cert.toShrinkageWitness⟩
  have hStable := stableRestriction_of_certificate (p := p) solver hCardHalf
  exact locality_lift_partial (p := p) solver hStable hProvider

/--
Typeclass wrapper for the half-table cardinality side-condition used by
`stableRestriction_of_certificate`.
-/
class HalfTableCertificateBound
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver_Partial p)
  [Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
    (p := toFactsParamsPartial p)
    (toFactsGeneralSolverPartial solver)
    (solverDecideFacts (p := p) solver)] : Prop where
  half_bound :
    (Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
        (p := toFactsParamsPartial p)
        (general := toFactsGeneralSolverPartial solver)
        (generalEval := solverDecideFacts (p := p) solver)).restriction.alive.card
      ≤ Partial.tableLen p.n / 2

/--
Length arithmetic bridge used to transport certificate-side quarter-input
bounds into the Partial-side half-table bounds.
-/
@[simp] lemma inputLen_div4_to_partial_table_half (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.inputLen (toFactsParamsPartial p) / 4 =
      Partial.tableLen p.n / 2 := by
  have htwo : 0 < (2 : Nat) := by decide
  calc
    Facts.LocalityLift.inputLen (toFactsParamsPartial p) / 4
        = (2 * 2 ^ p.n) / (2 * 2) := by
          simp [toFactsParamsPartial, Facts.LocalityLift.inputLen, Nat.pow_succ, Nat.mul_comm]
    _ = 2 ^ p.n / 2 := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.mul_div_mul_left (m := 2) (2 ^ p.n) 2 htwo)
    _ = Partial.tableLen p.n / 2 := by
      simp [Partial.tableLen]

/--
Canonical extraction: any provided shrinkage certificate already carries the
cardinality bound needed by `HalfTableCertificateBound`.
-/
instance halfTableCertificateBound_of_certificate
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver_Partial p)
  [hCert :
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
      (p := toFactsParamsPartial p)
      (toFactsGeneralSolverPartial solver)
      (solverDecideFacts (p := p) solver)] :
  HalfTableCertificateBound (p := p) solver where
  half_bound := by
    classical
    let cert :=
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
        (p := toFactsParamsPartial p)
        (general := toFactsGeneralSolverPartial solver)
        (generalEval := solverDecideFacts (p := p) solver)
    calc
      cert.restriction.alive.card
          ≤ Facts.LocalityLift.inputLen (toFactsParamsPartial p) / 4 :=
        cert.half_input_bound
      _ = Partial.tableLen p.n / 2 := inputLen_div4_to_partial_table_half p

/--
Certificate-driven locality lift without a manual `hCardHalf` argument.
The bound is supplied via the `HalfTableCertificateBound` typeclass.
-/
def locality_lift_partial_of_certificate_auto
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver_Partial p)
  [hCert :
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
      (p := toFactsParamsPartial p)
      (toFactsGeneralSolverPartial solver)
      (solverDecideFacts (p := p) solver)]
  [hHalf : HalfTableCertificateBound (p := p) solver] :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth := by
  exact locality_lift_partial_of_certificate (p := p) solver hHalf.half_bound

def no_general_solver_of_no_local_partial
  {p : Models.GapPartialMCSPParams}
  (H : ∀ _solver : LowerBounds.SmallLocalCircuitSolver_Partial p, False)
  (hGeneralStable :
    ∀ solver : Magnification.SmallGeneralCircuitSolver_Partial p,
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (r.apply x) = solver.decide x)
  (hProvider :
    ∀ solver : Magnification.SmallGeneralCircuitSolver_Partial p,
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := toFactsParamsPartial p)
        (toFactsGeneralSolverPartial solver)) :
  ∀ _solver : Magnification.SmallGeneralCircuitSolver_Partial p, False := by
  classical
  intro solver
  have hStable := hGeneralStable solver
  letI :
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := toFactsParamsPartial p)
        (toFactsGeneralSolverPartial solver) := hProvider solver
  have : ∀ solver' : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParamsPartial p),
      False := by
    intro solver'
    let localParams : LowerBounds.SmallLocalCircuitParamsPartial p :=
      fromFactsLocalParamsPartial (p := p) solver'
    let localSolver : LowerBounds.SmallLocalCircuitSolver_Partial p :=
      { params := localParams
        sem := solver.sem
        witness := solver.witness
        correct := solver.correct_decide
        decideLocal := by
          exact decideLocal_of_stable_restriction (p := p) solver.decide hStable }
    exact H localSolver
  have h := Facts.LocalityLift.no_general_solver_of_no_local (p := toFactsParamsPartial p) this
  simpa using h (toFactsGeneralSolverPartial solver)

end ThirdPartyFacts
end Pnp3
