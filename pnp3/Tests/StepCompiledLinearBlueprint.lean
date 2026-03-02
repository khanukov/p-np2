import Complexity.PsubsetPpolyInternal.Simulation

namespace Pnp3
namespace Tests

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.Simulation

theorem stepCompiledLinearBlueprint_ready_check
    (M : TM) (n : Nat) (sc : StraightConfig M n) :
    Nonempty (StraightConfig.BuiltWire.LinearStepBlueprint (M := M) (n := n) sc) :=
  StraightConfig.BuiltWire.linearStepBlueprint_ready (M := M) (n := n) sc

theorem stepCompiledLinearBlueprint_base_le_check
    (M : TM) (n : Nat) (sc : StraightConfig M n) :
    sc.circuit.gates ≤
      (StraightConfig.BuiltWire.linearStepBlueprint (M := M) (n := n) sc).writeBit.ctx.circuit.gates := by
  exact (StraightConfig.BuiltWire.linearStepBlueprint_base_le (M := M) (n := n) sc).1

end Tests
end Pnp3
