import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyComponentDecomposition

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Accepted-input pair decomposition for a finite selector

The component-pair expansion is not yet the object charged by canonical
derivation-path arguments.  Those arguments group **accepted inputs** by the
last common prefix of their edge-labelled accepting traces.

This file moves the exact Fourier identity to that level.  Under family
unambiguity, the dependent sum of a component index and an input accepted by
that component is equivalent to the set of inputs accepted by the union.
Independently of that equivalence, the selector indicator is the sum of point
indicators over accepted inputs.  Consequently its masked high-tail second
moment is exactly the ordered sum of accepted-input-pair correlations.

No first-divergence geometry and no correlation estimate is assumed here.
-/

namespace FiniteLayeredQueryProgramFamily

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteUnambiguousFBDD

local instance familyIndexFintypeForAcceptedInputs {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Fintype family.Index :=
  family.indexFintype

/-- Inputs accepted by one fixed component. -/
def ComponentModel {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (index : family.Index) : Type :=
  {input : Fin n → Bool // (family.program index).eval input = true}

/-- Inputs accepted by the finite Boolean union. -/
def AcceptedModel {n : Nat} (family : FiniteLayeredQueryProgramFamily n) :
    Type :=
  {input : Fin n → Bool // family.eval input = true}

instance componentModelFintype {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (index : family.Index) :
    Fintype (family.ComponentModel index) := by
  unfold ComponentModel
  infer_instance

instance acceptedModelFintype {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    Fintype family.AcceptedModel := by
  unfold AcceptedModel
  infer_instance

/-- Forget the accepting component while retaining the proof that the union
accepts the input. -/
def sigmaComponentModelToAcceptedModel {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    (Σ index, family.ComponentModel index) → family.AcceptedModel :=
  fun model =>
    ⟨model.2.1, (family.eval_eq_true_iff model.2.1).2
      ⟨model.1, model.2.2⟩⟩

/-- Family unambiguity makes the component/model forgetful map injective. -/
theorem sigmaComponentModelToAcceptedModel_injective
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    Function.Injective family.sigmaComponentModelToAcceptedModel := by
  intro left right heq
  rcases left with ⟨leftIndex, ⟨leftInput, hleft⟩⟩
  rcases right with ⟨rightIndex, ⟨rightInput, hright⟩⟩
  have hinput : leftInput = rightInput :=
    congrArg Subtype.val heq
  have hrightAtLeft :
      (family.program rightIndex).eval leftInput = true := by
    simpa [hinput] using hright
  have hindex : leftIndex = rightIndex :=
    hunambiguous leftInput leftIndex rightIndex hleft hrightAtLeft
  subst rightIndex
  subst rightInput
  rfl

/-- Every accepted union input has an accepting component witness. -/
theorem sigmaComponentModelToAcceptedModel_surjective
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n) :
    Function.Surjective family.sigmaComponentModelToAcceptedModel := by
  intro accepted
  obtain ⟨index, hindex⟩ :=
    (family.eval_eq_true_iff accepted.1).1 accepted.2
  refine ⟨⟨index, ⟨accepted.1, hindex⟩⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Under unambiguity, accepted inputs are exactly component-tagged accepted
inputs, with neither duplication nor loss. -/
noncomputable def sigmaComponentModelEquivAcceptedModel
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    (Σ index, family.ComponentModel index) ≃ family.AcceptedModel :=
  Equiv.ofBijective family.sigmaComponentModelToAcceptedModel
    ⟨family.sigmaComponentModelToAcceptedModel_injective hunambiguous,
      family.sigmaComponentModelToAcceptedModel_surjective⟩

/-- The forward map of the accepted-model equivalence is the original
component-forgetful map.  This keeps the accepting component accessible when a
downstream reverse-trace argument transports along the equivalence. -/
@[simp]
theorem sigmaComponentModelEquivAcceptedModel_apply
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (model : Σ index, family.ComponentModel index) :
    family.sigmaComponentModelEquivAcceptedModel hunambiguous model =
      family.sigmaComponentModelToAcceptedModel model := rfl

/-- Cardinal form of the exact accepted-input decomposition. -/
theorem card_acceptedModel_eq_sum_componentModels
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    Fintype.card family.AcceptedModel =
      ∑ index : family.Index, Fintype.card (family.ComponentModel index) := by
  classical
  calc
    Fintype.card family.AcceptedModel =
        Fintype.card (Σ index, family.ComponentModel index) := by
          symm
          exact Fintype.card_congr
            (family.sigmaComponentModelEquivAcceptedModel hunambiguous)
    _ = ∑ index : family.Index,
        Fintype.card (family.ComponentModel index) := by
          exact Fintype.card_sigma

/-! ## Atomic point kernels -/

/-- Rational point indicator of one accepted input. -/
noncomputable def ratAcceptedPointIndicator {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) (input : Fin n → Bool) : ℚ :=
  if input = accepted.1 then 1 else 0

/-- The selector indicator is exactly the sum of point indicators over the
accepted inputs. -/
theorem selector_ratAcceptanceIndicator_eq_sum_acceptedPoints
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n → Bool) :
    family.selectorFBDD.ratAcceptanceIndicator input =
      ∑ accepted : family.AcceptedModel,
        family.ratAcceptedPointIndicator accepted input := by
  classical
  by_cases haccepts : family.eval input = true
  · let chosen : family.AcceptedModel := ⟨input, haccepts⟩
    have hselector : family.selectorFBDD.Accepts input :=
      (family.selectorFBDD_accepts_iff_eval_eq_true input).2 haccepts
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    rw [if_pos hselector]
    symm
    calc
      (∑ accepted : family.AcceptedModel,
          family.ratAcceptedPointIndicator accepted input) =
          family.ratAcceptedPointIndicator chosen input := by
        apply Finset.sum_eq_single chosen
        · intro accepted _ hne
          have hinput : input ≠ accepted.1 := by
            intro heq
            apply hne
            apply Subtype.ext
            exact heq.symm
          simp [ratAcceptedPointIndicator, hinput]
        · simp
      _ = 1 := by simp [ratAcceptedPointIndicator, chosen]
  · have hselector : ¬ family.selectorFBDD.Accepts input := by
      intro hacc
      exact haccepts
        ((family.selectorFBDD_accepts_iff_eval_eq_true input).1 hacc)
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    rw [if_neg hselector]
    symm
    apply Finset.sum_eq_zero
    intro accepted _
    have hinput : input ≠ accepted.1 := by
      intro heq
      apply haccepts
      simpa [heq] using accepted.2
    simp [ratAcceptedPointIndicator, hinput]

/-- Atomic accepted-input contribution to the signed masked uniform average
of the degree-`>k` Fourier tail. -/
noncomputable def acceptedPointHighTailAverage {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) (k : Nat)
    (base mask : Fin n → Bool) : ℚ :=
  finiteAverage (fun uniform : Fin n → Bool =>
    ratHighDegreeFourierTail
      (family.ratAcceptedPointIndicator accepted) k
      (maskedInput base mask uniform))

/-- The selector high-tail average is exactly the sum of its accepted-input
point kernels. -/
theorem selector_highTailAverage_eq_sum_acceptedPoints
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (k : Nat) (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      ratHighDegreeFourierTail
        family.selectorFBDD.ratAcceptanceIndicator k
        (maskedInput base mask uniform)) =
      ∑ accepted : family.AcceptedModel,
        family.acceptedPointHighTailAverage accepted k base mask := by
  classical
  have hfunction : family.selectorFBDD.ratAcceptanceIndicator =
      fun input => ∑ accepted : family.AcceptedModel,
        family.ratAcceptedPointIndicator accepted input := by
    funext input
    exact family.selector_ratAcceptanceIndicator_eq_sum_acceptedPoints input
  rw [hfunction]
  calc
    finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail
          (fun input => ∑ accepted : family.AcceptedModel,
            family.ratAcceptedPointIndicator accepted input) k
          (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n → Bool =>
        ∑ accepted : family.AcceptedModel,
          ratHighDegreeFourierTail
            (family.ratAcceptedPointIndicator accepted) k
            (maskedInput base mask uniform)) := by
        apply finiteAverage_congr
        intro uniform
        exact ratHighDegreeFourierTail_fintype_sum
          (fun accepted => family.ratAcceptedPointIndicator accepted)
          k (maskedInput base mask uniform)
    _ = ∑ accepted : family.AcceptedModel,
        family.acceptedPointHighTailAverage accepted k base mask := by
      rw [finiteAverage_fintype_sum]
      rfl

/-- Exact accepted-input-pair expansion of the selector's masked high-tail
second moment.  This is the insertion surface for an edge-labelled reverse
trace and residual-splicing charge.  The identity itself is unconditional;
constructing a unique accepting reverse trace downstream additionally requires
`family.IsUnambiguous`. -/
theorem selector_highTailAverage_secondMoment_eq_sum_acceptedPointPairs
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (family : FiniteLayeredQueryProgramFamily n)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail
          family.selectorFBDD.ratAcceptanceIndicator k
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      ∑ left : family.AcceptedModel, ∑ right : family.AcceptedModel,
        finiteAverage (fun seed : DSeed × TSeed =>
          family.acceptedPointHighTailAverage left k
              (D seed.1) (T seed.2) *
            family.acceptedPointHighTailAverage right k
              (D seed.1) (T seed.2)) := by
  classical
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail
            family.selectorFBDD.ratAcceptanceIndicator k
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (∑ accepted : family.AcceptedModel,
          family.acceptedPointHighTailAverage accepted k
            (D seed.1) (T seed.2)) ^ 2) := by
              apply finiteAverage_congr
              intro seed
              rw [family.selector_highTailAverage_eq_sum_acceptedPoints]
    _ = ∑ left : family.AcceptedModel, ∑ right : family.AcceptedModel,
        finiteAverage (fun seed : DSeed × TSeed =>
          family.acceptedPointHighTailAverage left k
              (D seed.1) (T seed.2) *
            family.acceptedPointHighTailAverage right k
              (D seed.1) (T seed.2)) := by
      exact finiteAverage_sq_fintype_sum_eq_sum_pair
        (Seed := DSeed × TSeed) (Index := family.AcceptedModel)
        (fun accepted seed => family.acceptedPointHighTailAverage accepted k
          (D seed.1) (T seed.2))

end FiniteLayeredQueryProgramFamily
end OneTapeMagnification
end Frontier
end Pnp4
