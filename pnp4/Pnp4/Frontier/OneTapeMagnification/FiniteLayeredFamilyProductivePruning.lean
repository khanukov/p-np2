import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelector

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Pruning extensionally rejecting members of a finite layered family

The alpha-indexed canonical family may contain statically well-formed members
which reject every Boolean input.  This file removes exactly those members.
The pruning preserves the family Boolean pointwise, read-once behavior, and
unambiguity.

For an unambiguous family, choosing one accepting input for each productive
member gives an injection into the Boolean input cube.  Consequently there are
at most `2 ^ n` productive members.  This is only a finite cardinal bound: it
is still exponential, and it does not bound or share the state slots inside
the remaining components.
-/

namespace FiniteLayeredQueryProgramFamily

/-- A component is productive when it accepts at least one Boolean input. -/
def ProductiveIndex {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :=
  { index : family.Index //
    exists input : Fin n -> Bool,
      (family.program index).eval input = true }

/-- Explicit finite enumeration of the productive subtype. -/
noncomputable def productiveIndexFintype {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    Fintype family.ProductiveIndex := by
  classical
  letI : Fintype family.Index := family.indexFintype
  letI : Finite family.ProductiveIndex :=
    Finite.of_injective (fun index : family.ProductiveIndex => index.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance instProductiveIndexFintype {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n} :
    Fintype family.ProductiveIndex :=
  family.productiveIndexFintype

/-- Restrict a finite family to components which accept some input. -/
noncomputable def productiveSubfamily {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    FiniteLayeredQueryProgramFamily n where
  Index := family.ProductiveIndex
  indexFintype := family.productiveIndexFintype
  layers := fun index => family.layers index.1
  program := fun index => family.program index.1

/-- Pruning extensionally rejecting components preserves the finite OR on
every input. -/
theorem productiveSubfamily_eval_eq_true_iff {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) :
    family.productiveSubfamily.eval input = true <->
      family.eval input = true := by
  rw [eval_eq_true_iff, eval_eq_true_iff]
  constructor
  · rintro ⟨index, haccepts⟩
    exact ⟨index.1, haccepts⟩
  · rintro ⟨index, haccepts⟩
    exact ⟨⟨index, input, haccepts⟩, haccepts⟩

/-- Boolean-valued pointwise equality corresponding to the exact acceptance
equivalence. -/
theorem productiveSubfamily_eval {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) :
    family.productiveSubfamily.eval input = family.eval input := by
  have hiff := family.productiveSubfamily_eval_eq_true_iff input
  cases hleft : family.productiveSubfamily.eval input <;>
      cases hright : family.eval input
  · rfl
  · have htrue := hiff.mpr hright
    simp [hleft] at htrue
  · have htrue := hiff.mp hleft
    simp [hright] at htrue
  · rfl

/-- Componentwise read-once behavior is inherited by the productive
subfamily. -/
theorem productiveSubfamily_isReadOnce {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hreadOnce : family.IsReadOnce) :
    family.productiveSubfamily.IsReadOnce := by
  intro index
  exact hreadOnce index.1

/-- Pointwise uniqueness of an accepting component is inherited by the
productive subfamily. -/
theorem productiveSubfamily_isUnambiguous {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    family.productiveSubfamily.IsUnambiguous := by
  intro input left right hleft hright
  apply Subtype.ext
  exact hunambiguous input left.1 right.1 hleft hright

/-- One fixed accepting input chosen for a productive component. -/
noncomputable def productiveAcceptingInput {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n}
    (index : family.ProductiveIndex) : Fin n -> Bool :=
  Classical.choose index.2

/-- The chosen witness really is accepted by its productive component. -/
theorem productiveAcceptingInput_spec {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n}
    (index : family.ProductiveIndex) :
    (family.program index.1).eval (productiveAcceptingInput index) = true :=
  Classical.choose_spec index.2

/-- In an unambiguous family, distinct productive components have distinct
chosen accepting inputs. -/
theorem productiveAcceptingInput_injective {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    Function.Injective
      (fun index : family.ProductiveIndex => productiveAcceptingInput index) := by
  intro left right hequal
  change productiveAcceptingInput left = productiveAcceptingInput right at hequal
  apply Subtype.ext
  apply hunambiguous (productiveAcceptingInput left) left.1 right.1
  · exact productiveAcceptingInput_spec left
  · rw [hequal]
    exact productiveAcceptingInput_spec right

/-- An unambiguous family has at most one productive component per Boolean
input.  The resulting `2 ^ n` bound is exponential and carries no component
width or sharing conclusion. -/
theorem card_productiveIndex_le_two_pow {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    @Fintype.card family.ProductiveIndex family.productiveIndexFintype <=
      2 ^ n := by
  classical
  letI : Fintype family.ProductiveIndex := family.productiveIndexFintype
  calc
    Fintype.card family.ProductiveIndex <=
        Fintype.card (Fin n -> Bool) :=
      Fintype.card_le_of_injective
        (fun index : family.ProductiveIndex => productiveAcceptingInput index)
        (productiveAcceptingInput_injective family hunambiguous)
    _ = 2 ^ n := by simp

/-- The selector of the productive subfamily still realizes the original
finite-family Boolean exactly. -/
theorem productiveSubfamily_selectorFBDD_accepts_iff {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) :
    family.productiveSubfamily.selectorFBDD.Accepts input <->
      family.eval input = true := by
  rw [selectorFBDD_accepts_iff_eval_eq_true]
  exact family.productiveSubfamily_eval_eq_true_iff input

/-- Exact selector size after productive pruning.  It remains the honest sum
of every surviving component's layer-by-width contribution. -/
theorem productiveSubfamily_selectorFBDD_vertex_card {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    @Fintype.card family.productiveSubfamily.selectorFBDD.Vertex
        family.productiveSubfamily.selectorFBDD.vertexFintype =
      (∑ index : family.ProductiveIndex,
        (family.layers index.1 + 1) * (family.program index.1).width) + 3 := by
  rw [selectorFBDD_vertex_card]
  classical
  letI : Fintype family.ProductiveIndex := family.productiveIndexFintype
  unfold layeredStateSlotCount
  rfl

end FiniteLayeredQueryProgramFamily

end OneTapeMagnification
end Frontier
end Pnp4
