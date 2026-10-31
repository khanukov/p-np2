import Complexity.Interfaces

namespace Pnp3
namespace Complexity
namespace Simulation

open ComplexityInterfaces

abbrev Move := Internal.PsubsetPpoly.Move
abbrev TM := Internal.PsubsetPpoly.TM.{0}
abbrev Configuration (M : TM) (n : Nat) := Internal.PsubsetPpoly.TM.Configuration (M := M) n

namespace TM

abbrev tapeLength (M : Simulation.TM) (n : Nat) : Nat :=
  Internal.PsubsetPpoly.TM.tapeLength (M := M) n

abbrev initialConfig (M : Simulation.TM) {n : Nat} (x : Bitstring n) : Configuration M n :=
  Internal.PsubsetPpoly.TM.initialConfig (M := M) x

abbrev stepConfig (M : Simulation.TM) {n : Nat} (c : Configuration M n) : Configuration M n :=
  Internal.PsubsetPpoly.TM.stepConfig (M := M) c

abbrev runConfig (M : Simulation.TM) {n : Nat} (c : Configuration M n) (t : Nat) : Configuration M n :=
  Internal.PsubsetPpoly.TM.runConfig (M := M) c t

abbrev run (M : Simulation.TM) {n : Nat} (x : Bitstring n) : Configuration M n :=
  Internal.PsubsetPpoly.TM.run (M := M) x

abbrev accepts (M : Simulation.TM) (n : Nat) (x : Bitstring n) : Bool :=
  Internal.PsubsetPpoly.TM.accepts (M := M) (n := n) x

end TM

/-- Unpack a `P` witness into an explicit TM decider with polynomial runtime. -/
theorem exists_poly_tm_for_P {L : Language} :
    P L →
      ∃ (M : TM) (c : Nat),
        (∀ n, M.runTime n ≤ n ^ c + c) ∧
        (∀ n (x : Bitstring n), TM.accepts M n x = L n x) := by
  intro hP
  rcases hP with ⟨M, c, hRun, hCorrect⟩
  exact ⟨M, c, hRun, hCorrect⟩

end Simulation
end Complexity
end Pnp3
