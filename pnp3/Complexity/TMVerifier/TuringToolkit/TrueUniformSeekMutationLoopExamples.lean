import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoop

/-!
# Concrete T1b-B one-iteration probes

These named proof values instantiate the genuine loop-step and OOB theorems.
They are not evaluator tests and make no induction, restoration, output, or
acceptance claim.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- Three data cells and three unary index units: a normal `j = 0` loop step. -/
def t1bbIterationRequest : T1Request := ⟨3, [true, false, true]⟩

def t1bbIterationZero :=
  t1CS_loop_iteration_exact t1bbIterationRequest 0
    (by decide) (by decide) true false rfl rfl

/-- Two data cells but three index units: `j = 1` runs out of data. -/
def t1bbOobRequest : T1Request := ⟨3, [true, false]⟩

def t1bbOobAtOne :=
  t1CS_loop_oob_exact t1bbOobRequest 1
    (by decide) rfl false rfl

end Pnp3.Internal.PsubsetPpoly.TM
