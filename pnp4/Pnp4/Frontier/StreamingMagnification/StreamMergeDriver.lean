import Pnp4.Frontier.StreamingMagnification.StreamMergeCorrectness
import Mathlib.Tactic

/-!
# Pure executable block driver for reference Stream-Merge

This driver repeatedly invokes `referenceStreamMerge` on the exact next
truth-table block.  Its recursion is structural on explicit fuel; the public
entry point supplies `2 ^ n + 1`, while the correctness module proves that a
positive block length strictly decreases the unread suffix and therefore the
fuel-exhausted branch is unreachable.

This remains a finite executable **reference function**, not a
`StreamingRAM.Program`.  It has direct access to the mathematical truth table
and inherits the exhaustive circuit search of `referenceStreamMerge`; no
streaming time or space claim is made here.

The driver takes an encoded initial bounded circuit.  Its values on the empty
prefix are irrelevant, but the code itself must decode successfully.  This
boundary is explicit: for parameters such as `n = 0, s = 0`, where the chosen
standard-DAG model has no bounded circuit at all, this entry point returns
`invalidInitialPrior` rather than manufacturing a fake initial object.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeDriver

open StandardDAG
open TotalSearch
open StreamMerge

/-- Driver-only malformed states.  A valid initial code, positive block
length, and sufficient fuel make the last three constructors unreachable. -/
inductive MalformedReason where
  | invalidInitialPrior
  | zeroBlockLength
  | fuelExhausted
  | cursorPastEnd
  | mergeRejected
  deriving DecidableEq, Repr

/-- Final reference-driver result. -/
inductive Result (n s : Nat) where
  | found (code : DAGCodec.Code n s)
  | noCircuit
  | malformed (reason : MalformedReason)

/-- Exact next literal block. -/
def nextBlock {n : Nat} (table : TruthTable n)
    (blockLength consumed : Nat) : List Bool :=
  tableBlock table consumed (expectedLength n blockLength consumed)

/-- Fuelled reference loop.  It stops immediately after a genuine
`noCircuit`, preserving the earliest prefix at which bounded extension became
impossible. -/
def runFuel {n s : Nat} (table : TruthTable n) (blockLength : Nat) :
    Nat -> Nat -> DAGCodec.Code n s -> Result n s
  | 0, _consumed, _currentCode => .malformed .fuelExhausted
  | fuel + 1, consumed, currentCode =>
      if consumed = 2 ^ n then
        .found currentCode
      else if consumed < 2 ^ n then
        let block := nextBlock table blockLength consumed
        match referenceStreamMerge currentCode blockLength consumed block with
        | .found nextCode =>
            runFuel table blockLength fuel
              (consumed + block.length) nextCode
        | .noCircuit => .noCircuit
        | .malformed _ => .malformed .mergeRejected
      else
        .malformed .cursorPastEnd

/-- Public pure reference driver.  Validation order is initial code and then
positive nominal block length. -/
def referenceStreamDriver {n s : Nat}
    (initialCode : DAGCodec.Code n s)
    (blockLength : Nat) (table : TruthTable n) : Result n s :=
  match DAGCodec.decode initialCode with
  | none => .malformed .invalidInitialPrior
  | some _initial =>
      if blockLength = 0 then
        .malformed .zeroBlockLength
      else
        runFuel table blockLength (2 ^ n + 1) 0 initialCode

end StreamMergeDriver
end StreamingMagnification
end Frontier
end Pnp4
