import Complexity.Interfaces

/-!
# Runtime advice in the repository `P` interface

The repository Turing-machine interface stores `runTime : Nat -> Nat` as an
unrestricted field of the machine.  Polynomial-time membership only bounds
that field pointwise; it does not require the field to be computable or time
constructible.

Consequently an arbitrary Boolean sequence indexed by input length can be
placed directly in the choice between zero and one execution step.  The
two-state machine below makes this observation exact: at length `n` it starts
in the rejecting state and performs one transition to the accepting state
exactly when `A n = true`.

This is a model audit theorem.  It does not assert an unformalized
noncomputability or cardinality result.  It records why membership in the
current repository `P` cannot, by itself, be treated as a callable uniform
`StreamingRAM.Program`: such a program has finite operational code, whereas
the `runTime` field below contains the whole arbitrary length-indexed sequence.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace RuntimeAdviceBarrier

open Pnp3.ComplexityInterfaces

/-- The language whose answer depends only on the input length through `A`. -/
def lengthAdviceLanguage (A : Nat -> Bool) : Language :=
  fun n _input => A n

/--
An explicit two-state repository TM carrying `A` in its unrestricted runtime
field.  Zero steps leave the machine in `false`; one step moves it to `true`.
-/
def lengthAdviceTM (A : Nat -> Bool) :
    Pnp3.Internal.PsubsetPpoly.TM.{0} where
  state := Bool
  start := false
  accept := true
  step := fun _state symbol =>
    (true, symbol, Pnp3.Internal.PsubsetPpoly.Move.stay)
  runTime := fun n => if A n then 1 else 0

/-- The advice clock uses at most one step at every input length. -/
theorem lengthAdviceTM_runTime_le_one
    (A : Nat -> Bool) (n : Nat) :
    (lengthAdviceTM A).runTime n <= 1 := by
  cases hA : A n <;> simp [lengthAdviceTM, hA]

/-- The repository acceptance semantics samples exactly the advice bit. -/
theorem lengthAdviceTM_accepts
    (A : Nat -> Bool) (n : Nat)
    (input : Pnp3.ComplexityInterfaces.Bitstring n) :
    Pnp3.Internal.PsubsetPpoly.TM.accepts
        (M := lengthAdviceTM A) (n := n) input = A n := by
  cases hA : A n <;>
    simp [Pnp3.Internal.PsubsetPpoly.TM.accepts,
      Pnp3.Internal.PsubsetPpoly.TM.run,
      Pnp3.Internal.PsubsetPpoly.TM.runConfig,
      Pnp3.Internal.PsubsetPpoly.TM.stepConfig,
      lengthAdviceTM, hA]

/--
Every length-indexed Boolean sequence defines a language in the current
repository `P`.  The polynomial exponent is zero, so the declared bound is the
constant `n^0 = 1`.
-/
theorem lengthAdviceLanguage_in_repo_P (A : Nat -> Bool) :
    P (lengthAdviceLanguage A) := by
  refine ⟨lengthAdviceTM A, 0, ?_, ?_⟩
  · intro n
    simpa using lengthAdviceTM_runTime_le_one A n
  · intro n input
    exact lengthAdviceTM_accepts A n input

end RuntimeAdviceBarrier
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.RuntimeAdviceBarrier.lengthAdviceTM_runTime_le_one
#print axioms Pnp4.Frontier.StreamingMagnification.RuntimeAdviceBarrier.lengthAdviceTM_accepts
#print axioms Pnp4.Frontier.StreamingMagnification.RuntimeAdviceBarrier.lengthAdviceLanguage_in_repo_P
