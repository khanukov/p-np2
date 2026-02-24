import Mathlib.Data.Finset.Basic
import Complexity.Interfaces
import Core.BooleanBasics
import Models.Model_PartialMCSP
import ThirdPartyFacts.Facts_Switching

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
Localized constructive bridge to depth-bounded strict formulas
for the fixed language `gapPartialMCSP_Language p`.
-/
def GapPartialMCSPPpolyToDepthAt (p : GapPartialMCSPParams) (d : Nat) : Prop :=
  ComplexityInterfaces.Ppoly (gapPartialMCSP_Language p) →
    ComplexityInterfaces.PpolyFormulaDepth (gapPartialMCSP_Language p) d

/--
AC0-slice packaging of the localized depth-bounded bridge:
the target depth is read from an explicit `AC0Parameters` witness (`ac0.d`).
-/
structure GapPartialMCSPPpolyToDepthViaAC0 (p : GapPartialMCSPParams) where
  ac0 : AC0Parameters
  same_n : ac0.n = Models.partialInputLen p
  lift : GapPartialMCSPPpolyToDepthAt p ac0.d

/--
Constructive reifier package for the localized AC0-depth bridge.

For the fixed language `gapPartialMCSP_Language p` and explicit AC0 parameters,
it turns every lightweight `Ppoly` witness into an explicit strict witness with
uniform depth bound `ac0.d`.
-/
structure GapPartialMCSPPpolyDepthReifierViaAC0 (p : GapPartialMCSPParams) where
  ac0 : AC0Parameters
  same_n : ac0.n = Models.partialInputLen p
  reify :
    ∀ (_w : ComplexityInterfaces.Ppoly (gapPartialMCSP_Language p)),
      Nonempty
        (ComplexityInterfaces.InPpolyFormulaDepth (gapPartialMCSP_Language p) ac0.d)

/-- Forget the AC0 package and expose the localized depth bridge. -/
theorem gapPartialMCSP_ppoly_to_depth_of_viaAC0
    (p : GapPartialMCSPParams)
    (h : GapPartialMCSPPpolyToDepthViaAC0 p) :
    GapPartialMCSPPpolyToDepthAt p h.ac0.d :=
  h.lift

/--
Build the localized AC0-depth bridge package from an explicit reifier.
-/
noncomputable def gapPartialMCSP_ppoly_to_depth_viaAC0_of_reifier
    (p : GapPartialMCSPParams)
    (hR : GapPartialMCSPPpolyDepthReifierViaAC0 p) :
    GapPartialMCSPPpolyToDepthViaAC0 p := by
  refine
    { ac0 := hR.ac0
      same_n := hR.same_n
      lift := ?_ }
  intro hPpoly
  have wf : ComplexityInterfaces.InPpolyFormulaDepth (gapPartialMCSP_Language p) hR.ac0.d :=
    Classical.choice (hR.reify hPpoly)
  exact ⟨wf, trivial⟩

/--
Build the localized AC0-depth reifier package from a `viaAC0` bridge package.
-/
noncomputable def gapPartialMCSP_ppoly_depth_reifier_viaAC0_of_bridge
    (p : GapPartialMCSPParams)
    (h : GapPartialMCSPPpolyToDepthViaAC0 p) :
    GapPartialMCSPPpolyDepthReifierViaAC0 p := by
  refine
    { ac0 := h.ac0
      same_n := h.same_n
      reify := ?_ }
  intro hPpoly
  rcases h.lift hPpoly with ⟨wf, _⟩
  exact ⟨wf⟩

/--
Build the localized AC0-depth bridge package from:
* explicit AC0 parameters (depth source `ac0.d`),
* length alignment `ac0.n = partialInputLen p`,
* global depth-bounded bridge at depth `ac0.d`.
-/
def gapPartialMCSP_ppoly_to_depth_viaAC0_of_global_bridge
    (p : GapPartialMCSPParams)
    (ac0 : AC0Parameters)
    (hsame : ac0.n = Models.partialInputLen p)
    (hGlobal : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth ac0.d) :
    GapPartialMCSPPpolyToDepthViaAC0 p :=
  { ac0 := ac0
    same_n := hsame
    lift := fun hPpoly => hGlobal (gapPartialMCSP_Language p) hPpoly }

/--
Build the localized AC0-depth reifier package from a global depth bridge.
-/
noncomputable def gapPartialMCSP_ppoly_depth_reifier_viaAC0_of_global_bridge
    (p : GapPartialMCSPParams)
    (ac0 : AC0Parameters)
    (hsame : ac0.n = Models.partialInputLen p)
    (hGlobal : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth ac0.d) :
    GapPartialMCSPPpolyDepthReifierViaAC0 p :=
  gapPartialMCSP_ppoly_depth_reifier_viaAC0_of_bridge
    p (gapPartialMCSP_ppoly_to_depth_viaAC0_of_global_bridge p ac0 hsame hGlobal)

/-- Default-availability flag for a localized AC0-depth reifier package. -/
def hasDefaultGapPartialMCSPPpolyDepthReifierViaAC0
    (p : GapPartialMCSPParams) : Prop :=
  Nonempty (GapPartialMCSPPpolyDepthReifierViaAC0 p)

/-- Extract a localized AC0-depth reifier package from its default flag. -/
noncomputable def defaultGapPartialMCSPPpolyDepthReifierViaAC0
    (p : GapPartialMCSPParams)
    (h : hasDefaultGapPartialMCSPPpolyDepthReifierViaAC0 p) :
    GapPartialMCSPPpolyDepthReifierViaAC0 p :=
  Classical.choice h

/-- Default-availability flag for a localized AC0-depth bridge package. -/
def hasDefaultGapPartialMCSPPpolyToDepthViaAC0
    (p : GapPartialMCSPParams) : Prop :=
  Nonempty (GapPartialMCSPPpolyToDepthViaAC0 p)

/-- Extract an explicit AC0-depth bridge package from its default flag. -/
noncomputable def defaultGapPartialMCSPPpolyToDepthViaAC0
    (p : GapPartialMCSPParams)
    (h : hasDefaultGapPartialMCSPPpolyToDepthViaAC0 p) :
    GapPartialMCSPPpolyToDepthViaAC0 p :=
  Classical.choice h

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

/--
Trivial constructive formulaizer for the current `InPpolyReal` interface:
reuse the witness family directly as a strict formula family.
-/
noncomputable def trivialFormulaizer (p : GapPartialMCSPParams) :
    GapPartialMCSPFormulaizer p := by
  classical
  refine
    { familyOf := fun w n => w.family n
      familyCorrect := ?_
      familyPoly := ?_ }
  · intro w n x
    exact w.correct n x
  · intro w
    rcases w.polyBound_poly with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro n
    exact le_trans (w.family_size_le n) (hc n)

/--
Localized `PpolyReal -> PpolyFormula` realization obtained from the trivial
formulaizer for the current witness format.
-/
theorem gapPartialMCSP_realization_trivial
    (p : GapPartialMCSPParams) :
    GapPartialMCSPFormulaRealization p :=
  gapPartialMCSP_realization_of_formulaizer p (trivialFormulaizer p)

end ThirdPartyFacts
end Pnp3
