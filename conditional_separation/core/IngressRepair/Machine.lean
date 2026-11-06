import RawFrontier.Surface
namespace IngressRepair
open Pnp3.Complexity.Uniform.V1
/-- Experimental single-row header guard. No source, length or semantic advice. -/
def producer : UniformTM where
  stateCount := 288
  start := SmallIngress.producer.start
  accept := SmallIngress.producer.accept
  reject := SmallIngress.producer.reject
  accept_ne_reject := SmallIngress.producer.accept_ne_reject
  rawStep := fun q b => if q.val=138 ∧ b=none then (SmallIngress.producer.reject,none,.stay)
    else SmallIngress.producer.rawStep q b
/-- Same literal Cursor suffix; this is a new experimental raw family. -/
def machine (k : Nat) : UniformTM := producer.seq (Cursor.machine k)
end IngressRepair
