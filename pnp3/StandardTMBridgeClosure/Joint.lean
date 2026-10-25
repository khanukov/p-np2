import NormalClockClosure.Surface
import NormalClockClosure.Pins
import Mathlib.Computability.PostTuringMachine
namespace StandardTMBridgeClosure
#check (NormalClockClosure.bridge : ∀ k : Nat, NormalClockClosure.Target.Bridge k)
#check Turing.TM0.Machine
#check Turing.TM0.step
#check Turing.TM0.init
#print axioms NormalClockClosure.bridge
#print axioms NormalClockClosure.bridge_full
end StandardTMBridgeClosure
