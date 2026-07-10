import Pnp4.Frontier.OneTapeMagnification.Counting

/-!
# Finite local-HSG exclusion for standard-DAG MCSP

This file composes the two proved finite ingredients:

1. canonical DAG-code counting makes uniform MCSP acceptance `< 1/2` under
   the explicit code-length inequality;
2. a local generator plus MCSP completeness makes generator acceptance
   `>= 2/3`.

Their exact rational gap is greater than `1/6`, contradicting fooling error
at most `1/6`.  The result is conditional on a concrete generator that fools
the concrete machine.  No existence claim for the open small-seed generator
is stored in a structure, instance, or axiom.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open StreamingMagnification
open StreamingMagnification.TotalSearch
open Counting

/-- Exact two-sided bounded-error MCSP behavior at one finite length. -/
def BoundedErrorMCSPBehavior
    (machine : RandomizedMachine)
    (n threshold randomBits steps : Nat) : Prop :=
  (forall table : TruthTable n,
      HasCircuit n threshold table ->
        (2 : Rat) / 3 <= machineAcceptance machine table randomBits steps) /\
    (forall table : TruthTable n,
      Not (HasCircuit n threshold table) ->
        machineAcceptance machine table randomBits steps <= (1 : Rat) / 3)

/-- The concrete counting and locality hypotheses force a gap above `1/6`. -/
theorem code_counted_localGenerator_gap_gt_one_sixth
    (machine : RandomizedMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hBehavior :
      BoundedErrorMCSPBehavior machine n threshold randomBits steps) :
    (1 : Rat) / 6 <
      |uniformMachineAcceptance machine n randomBits steps -
        generatedMachineAcceptance machine generator randomBits steps| := by
  apply localGenerator_acceptance_gap_gt_one_sixth
    machine generator randomBits steps hBehavior.1
  exact uniformMachineAcceptance_lt_half_of_code_count
    machine n threshold randomBits steps hLength hBehavior.2

/--
CHMY-style finite exclusion: a generator that fools this machine to error
`1/6` rules out two-sided bounded-error MCSP behavior for that machine.
-/
theorem localGenerator_fooling_excludes_boundedErrorMCSP
    (machine : RandomizedMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hFools : FoolsOneTapeMachineWithin machine generator randomBits steps
      ((1 : Rat) / 6)) :
    Not (BoundedErrorMCSPBehavior machine n threshold randomBits steps) := by
  intro hBehavior
  have hGap := code_counted_localGenerator_gap_gt_one_sixth
    machine generator randomBits steps hLength hBehavior
  exact (not_lt_of_ge hFools) hGap

end OneTapeMagnification
end Frontier
end Pnp4
