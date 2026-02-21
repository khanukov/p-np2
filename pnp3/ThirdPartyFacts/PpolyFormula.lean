import Mathlib.Data.Finset.Basic
import Complexity.Interfaces
import Core.BooleanBasics
import Models.Model_PartialMCSP

/-!
  pnp3/ThirdPartyFacts/PpolyFormula.lean

  This file defines explicit external goals for the strict-structured bridge.
  They are modeled as `Prop` targets (to be assumed/proved by callers), not as
  global `axiom` declarations.
-/

namespace Pnp3
namespace ThirdPartyFacts

open ComplexityInterfaces
open Models

/--
Constructive realization target for the localized embedding step:
for the fixed language `gapPartialMCSP_Language p`, every lightweight `P/poly`
witness can be reified into the strict formula class.
-/
def GapPartialMCSPFormulaRealization (p : GapPartialMCSPParams) : Prop :=
  ComplexityInterfaces.PpolyReal (gapPartialMCSP_Language p) →
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)

/--
Stronger constructive target: a reifier that transforms an explicit lightweight
`InPpoly` witness for `gapPartialMCSP_Language p` into an explicit strict
`InPpolyFormula` witness.
-/
def GapPartialMCSPFormulaReifier (p : GapPartialMCSPParams) : Prop :=
  ∀ (_w : ComplexityInterfaces.InPpolyReal (gapPartialMCSP_Language p)),
    ∃ wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p),
      ∀ n (x : ComplexityInterfaces.Bitstring n),
        ComplexityInterfaces.FormulaCircuit.eval (wf.family n) x =
          ComplexityInterfaces.FormulaCircuit.eval (_w.family n) x

/--
Structured decomposition of the reifier task.

`familyOf` provides a concrete formula family for each lightweight witness.
`familyCorrect` states semantic equivalence with the target language.
`familyPoly` gives an explicit polynomial size bound for the constructed family.
-/
structure GapPartialMCSPFormulaizer (p : GapPartialMCSPParams) where
  familyOf :
    ComplexityInterfaces.InPpolyReal (gapPartialMCSP_Language p) →
      ∀ n, ComplexityInterfaces.FormulaCircuit n
  familyCorrect :
    ∀ (w : ComplexityInterfaces.InPpolyReal (gapPartialMCSP_Language p))
      (n : Nat) (x : ComplexityInterfaces.Bitstring n),
      ComplexityInterfaces.FormulaCircuit.eval (familyOf w n) x =
        gapPartialMCSP_Language p n x
  familyPoly :
    ∀ (w : ComplexityInterfaces.InPpolyReal (gapPartialMCSP_Language p)),
      ∃ c : Nat, ∀ n,
        ComplexityInterfaces.FormulaCircuit.size (familyOf w n) ≤ n ^ c + c

/--
Bridge lemma: any constructive realization immediately yields the localized
embed used by the magnification pipeline.
-/
theorem gapPartialMCSP_ppoly_to_ppolyFormula_of_realization
    (p : GapPartialMCSPParams)
    (hReal : GapPartialMCSPFormulaRealization p) :
    ComplexityInterfaces.PpolyReal (gapPartialMCSP_Language p) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
  hReal

/--
Any explicit reifier of `InPpoly` witnesses yields a localized realization.
-/
theorem gapPartialMCSP_realization_of_reifier
    (p : GapPartialMCSPParams)
    (hReify : GapPartialMCSPFormulaReifier p) :
    GapPartialMCSPFormulaRealization p := by
  intro hPpoly
  rcases hPpoly with ⟨w, _⟩
  rcases hReify w with ⟨wf, hRefine⟩
  let _ := hRefine
  exact ⟨wf, trivial⟩

/--
If we can explicitly build a formula family with correctness and polynomial
size for each lightweight witness, then the localized realization follows.
-/
theorem gapPartialMCSP_realization_of_formulaizer
    (p : GapPartialMCSPParams)
    (hF : GapPartialMCSPFormulaizer p) :
    GapPartialMCSPFormulaRealization p := by
  classical
  intro hPpoly
  rcases hPpoly with ⟨w, _⟩
  refine ⟨{ polyBound := fun n => n ^ (Classical.choose (hF.familyPoly w)) + Classical.choose (hF.familyPoly w)
            polyBound_poly := ?_
            family := hF.familyOf w
            family_size_le := ?_
            correct := ?_ }, trivial⟩
  · refine ⟨Classical.choose (hF.familyPoly w), ?_⟩
    intro n
    rfl
  · intro n
    exact Classical.choose_spec (hF.familyPoly w) n
  · intro n x
    exact hF.familyCorrect w n x

end ThirdPartyFacts
end Pnp3
