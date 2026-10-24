import NormalClockClosure.Target
namespace NormalClockClosure.Audit
/-- Independent complete type expressions for each new public original and pin. -/
def pin_degree : Nat → Nat := @NormalClockClosure.degree
example : (k : Nat) → Nat := @NormalClockClosure.degree
example : (k : Nat) → Nat := @pin_degree
def pin_Bridge : Nat → Prop := @NormalClockClosure.Target.Bridge
example : (k : Nat) → Prop := @NormalClockClosure.Target.Bridge
example : (k : Nat) → Prop := @pin_Bridge
#print axioms NormalClockClosure.degree
#print axioms pin_degree
#print axioms NormalClockClosure.Target.Bridge
#print axioms pin_Bridge
end NormalClockClosure.Audit
