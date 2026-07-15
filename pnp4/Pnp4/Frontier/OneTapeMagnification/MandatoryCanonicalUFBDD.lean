import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorProperties
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelectorUnambiguity

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The exact mandatory canonical uFBDD

This file packages the mandatory canonical family as one finite selector
diagram.  For positive block size, the diagram has exactly the cached
one-tape acceptance semantics, is syntactically read-once, and is
unambiguous.  Its vertex count remains the explicit disjoint-family sum; no
sharing or polynomial-size bound is asserted here.
-/

/-- The single finite selector diagram obtained from all eligible mandatory
canonical components. -/
noncomputable abbrev mandatoryCanonicalUFBDD
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) : FiniteUnambiguousFBDD n :=
  (mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b).selectorFBDD

/-- Exact list-input semantics of the mandatory canonical selector. -/
theorem mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalUFBDD machine input.length T b).Accepts
        (fun coordinate => input.get coordinate) <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  rw [FiniteLayeredQueryProgramFamily.selectorFBDD_accepts_iff_eval_eq_true]
  exact mandatoryFiniteRejectingGuardedCanonicalFamily_eval_eq_true_iff
    machine input T b hb

/-- Every formal start-rooted path in the mandatory canonical selector reads
each input coordinate at most once. -/
theorem mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    (mandatoryCanonicalUFBDD machine n T b).IsSyntacticallyReadOnce :=
  mandatoryFiniteRejectingGuardedCanonicalSelector_isSyntacticallyReadOnce
    machine n T b

/-- Positive block size makes the accepting canonical component unique, and
input compatibility then makes its accepting selector walk unique. -/
theorem mandatoryCanonicalUFBDD_isUnambiguous
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalUFBDD machine n T b).IsUnambiguous := by
  apply FiniteLayeredQueryProgramFamily.selectorFBDD_isUnambiguous_of_family
  exact mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
    machine n T b hb

/-- Exact vertex count of the diagram.  The sum is deliberately not replaced
by an unproved sharing or polynomial-size estimate. -/
theorem mandatoryCanonicalUFBDD_vertex_card
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    @Fintype.card (mandatoryCanonicalUFBDD machine n T b).Vertex
        (mandatoryCanonicalUFBDD machine n T b).vertexFintype =
      (∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        (n + 1) *
          (mandatoryBuiltRejectingGuardedCanonicalComponent
            machine n index).width) + 3 :=
  mandatoryFiniteRejectingGuardedCanonicalSelector_vertex_card
    machine n T b

end OneTapeMagnification
end Frontier
end Pnp4
