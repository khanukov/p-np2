import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalAlphaFunctionalRelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A witness-first cut-state barrier

Fix one input length and a finite unambiguous family.  Suppose an exact
realizer first reads the encoded component witness, compresses it to a finite
state, and only then sees the input.  Every component which accepts at least
one input must induce a different cut state.  Otherwise an input accepted by
one component would also make the other encoded witness accept, contradicting
family unambiguity.

This is a finite information lower bound for a *witness-first* factorization.
It does not say that an arbitrary variable order has such a cut, and it does
not lower-bound a checker which interleaves witness and input queries.
-/

namespace FiniteLayeredQueryProgramFamily

/-! ## Exact encoded-witness semantics -/

/-- On a valid code word, the encoded relation is exactly acceptance by the
named component. -/
@[simp]
theorem encodedAcceptingRelation_witnessCode_iff {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) (index : family.Index) :
    family.EncodedAcceptingRelation input (family.witnessCode index) <->
      (family.program index).eval input = true := by
  constructor
  · rintro ⟨other, hcode, haccepts⟩
    have hindex : index = other := family.witnessCode_injective hcode
    subst other
    exact haccepts
  · intro haccepts
    exact ⟨index, rfl, haccepts⟩

/-! ## Components active on the fixed input-length slice -/

/-- Component indices which accept at least one input of the fixed length.
This is an extensional finite set; no efficient procedure for enumerating it
is asserted. -/
noncomputable def acceptingIndices {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Finset family.Index := by
  classical
  letI : Fintype family.Index := family.indexFintype
  exact Finset.univ.filter fun index =>
    ∃ input : Fin n -> Bool, (family.program index).eval input = true

@[simp]
theorem mem_acceptingIndices_iff {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (index : family.Index) :
    index ∈ family.acceptingIndices <->
      ∃ input : Fin n -> Bool,
        (family.program index).eval input = true := by
  classical
  letI : Fintype family.Index := family.indexFintype
  simp [acceptingIndices]

/-- A classically chosen input accepted by an active component. -/
noncomputable def acceptingIndexInput {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n}
    (index : ↥family.acceptingIndices) : Fin n -> Bool :=
  Classical.choose
    ((family.mem_acceptingIndices_iff index.1).1 index.2)

/-- The chosen input is accepted by its component. -/
theorem acceptingIndexInput_spec {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n}
    (index : ↥family.acceptingIndices) :
    (family.program index.1).eval (acceptingIndexInput index) = true :=
  Classical.choose_spec
    ((family.mem_acceptingIndices_iff index.1).1 index.2)

/-! ## Exact witness-first factorizations -/

/-- An exact witness-first factorization through `State`: `prefixState` sees
only the encoded component word, while `suffixAccepts` subsequently sees the
input.  The equivalence is required for every code, including invalid ones. -/
def witnessFirstFactorization {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) {State : Type*}
    (prefixState : (Fin family.witnessBitWidth -> Bool) -> State)
    (suffixAccepts : State -> (Fin n -> Bool) -> Prop) : Prop :=
  ∀ code input,
    suffixAccepts (prefixState code) input <->
      family.EncodedAcceptingRelation input code

/-- In an unambiguous family, the witness-prefix states of all active
components are pairwise distinct. -/
theorem witnessFirstFactorization_acceptingIndices_injective
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    {State : Type*}
    (prefixState : (Fin family.witnessBitWidth -> Bool) -> State)
    (suffixAccepts : State -> (Fin n -> Bool) -> Prop)
    (hfactor : family.witnessFirstFactorization
      prefixState suffixAccepts) :
    Function.Injective
      (fun index : ↥family.acceptingIndices =>
        prefixState (family.witnessCode index.1)) := by
  classical
  rw [witnessFirstFactorization] at hfactor
  intro left right hstate
  change prefixState (family.witnessCode left.1) =
    prefixState (family.witnessCode right.1) at hstate
  apply Subtype.ext
  apply hunambiguous (acceptingIndexInput left) left.1 right.1
  · exact acceptingIndexInput_spec left
  · have hrelationLeft :
        family.EncodedAcceptingRelation (acceptingIndexInput left)
          (family.witnessCode left.1) :=
      (family.encodedAcceptingRelation_witnessCode_iff
        (acceptingIndexInput left) left.1).2
          (acceptingIndexInput_spec left)
    have hsuffixLeft :
        suffixAccepts
          (prefixState (family.witnessCode left.1))
          (acceptingIndexInput left) :=
      (hfactor (family.witnessCode left.1)
        (acceptingIndexInput left)).2 hrelationLeft
    have hsuffixRight :
        suffixAccepts
          (prefixState (family.witnessCode right.1))
          (acceptingIndexInput left) := by
      rw [← hstate]
      exact hsuffixLeft
    have hrelationRight :
        family.EncodedAcceptingRelation (acceptingIndexInput left)
          (family.witnessCode right.1) :=
      (hfactor (family.witnessCode right.1)
        (acceptingIndexInput left)).1 hsuffixRight
    exact (family.encodedAcceptingRelation_witnessCode_iff
      (acceptingIndexInput left) right.1).1 hrelationRight

/-- Every exact witness-first cut state space has at least as many states as
there are active components on the fixed input-length slice. -/
theorem card_acceptingIndices_le_of_witnessFirstFactorization
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (State : Type*) [Fintype State]
    (prefixState : (Fin family.witnessBitWidth -> Bool) -> State)
    (suffixAccepts : State -> (Fin n -> Bool) -> Prop)
    (hfactor : family.witnessFirstFactorization
      prefixState suffixAccepts) :
    family.acceptingIndices.card <= Fintype.card State := by
  classical
  calc
    family.acceptingIndices.card =
        Fintype.card (↥family.acceptingIndices) := by simp
    _ <= Fintype.card State :=
      Fintype.card_le_of_injective
        (fun index : ↥family.acceptingIndices =>
          prefixState (family.witnessCode index.1))
        (family.witnessFirstFactorization_acceptingIndices_injective
          hunambiguous prefixState suffixAccepts hfactor)

/-! ## Explicit bit summaries -/

/-- A witness-first summary consisting of `summaryBits` Boolean bits can
represent at most `2 ^ summaryBits` active component witnesses. -/
theorem card_acceptingIndices_le_two_pow_of_witnessFirstFactorization
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (summaryBits : Nat)
    (prefixState : (Fin family.witnessBitWidth -> Bool) ->
      (Fin summaryBits -> Bool))
    (suffixAccepts : (Fin summaryBits -> Bool) ->
      (Fin n -> Bool) -> Prop)
    (hfactor : family.witnessFirstFactorization
      prefixState suffixAccepts) :
    family.acceptingIndices.card <= 2 ^ summaryBits := by
  simpa using
    family.card_acceptingIndices_le_of_witnessFirstFactorization
      hunambiguous (Fin summaryBits -> Bool) prefixState suffixAccepts hfactor

/-- If the slice has at least `2 ^ witnessBits` active components, then any
exact Boolean witness-first summary needs at least `witnessBits` bits. -/
theorem witnessBits_le_summaryBits_of_witnessFirstFactorization
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (witnessBits summaryBits : Nat)
    (hmany : 2 ^ witnessBits <= family.acceptingIndices.card)
    (prefixState : (Fin family.witnessBitWidth -> Bool) ->
      (Fin summaryBits -> Bool))
    (suffixAccepts : (Fin summaryBits -> Bool) ->
      (Fin n -> Bool) -> Prop)
    (hfactor : family.witnessFirstFactorization
      prefixState suffixAccepts) :
    witnessBits <= summaryBits := by
  have hpow : 2 ^ witnessBits <= 2 ^ summaryBits :=
    hmany.trans
      (family.card_acceptingIndices_le_two_pow_of_witnessFirstFactorization
        hunambiguous summaryBits prefixState suffixAccepts hfactor)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hpow

end FiniteLayeredQueryProgramFamily

end OneTapeMagnification
end Frontier
end Pnp4
