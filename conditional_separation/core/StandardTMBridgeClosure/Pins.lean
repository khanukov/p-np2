import StandardTMBridgeClosure.Target
namespace StandardTMBridgeClosure.Audit
open Pnp3.Complexity.Uniform.V1 Turing
/-- Every new public definition and its pin has a separate complete typed expression. -/
def pin_encode : List Bool → List (Bool × Option Bool) := @StandardTMBridgeClosure.encode
example : List Bool → List (Bool × Option Bool) := @StandardTMBridgeClosure.encode
example : List Bool → List (Bool × Option Bool) := @pin_encode
def pin_compile : (M : UniformTM) → TM0.Machine (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) := @StandardTMBridgeClosure.compile
example : (M : UniformTM) → TM0.Machine (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) := @StandardTMBridgeClosure.compile
example : (M : UniformTM) → TM0.Machine (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) := @pin_compile
def pin_steps : (M : UniformTM) → Nat → TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) →
    Option (TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) := @StandardTMBridgeClosure.steps
example : (M : UniformTM) → Nat → TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) →
    Option (TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) := @StandardTMBridgeClosure.steps
example : (M : UniformTM) → Nat → TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) →
    Option (TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) := @pin_steps
def pin_Represents : (M : UniformTM) → {N B : Nat} → Config M.stateCount N B →
    TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) → Prop := @StandardTMBridgeClosure.Represents
example : (M : UniformTM) → {N B : Nat} → Config M.stateCount N B →
    TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) → Prop := @StandardTMBridgeClosure.Represents
example : (M : UniformTM) → {N B : Nat} → Config M.stateCount N B →
    TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) → Prop := @pin_Represents
def pin_degree : Nat → Nat := @StandardTMBridgeClosure.degree
example : (k : Nat) → Nat := @StandardTMBridgeClosure.degree
example : (k : Nat) → Nat := @pin_degree
def pin_Source : (k N : Nat) → (Fin N → Bool) → Nat → Nat → Prop := @StandardTMBridgeClosure.Target.Source
example : (k N : Nat) → (Fin N → Bool) → Nat → Nat → Prop := @StandardTMBridgeClosure.Target.Source
example : (k N : Nat) → (Fin N → Bool) → Nat → Nat → Prop := @pin_Source
def pin_Simulation : UniformTM → Prop := @StandardTMBridgeClosure.Target.Simulation
example : UniformTM → Prop := @StandardTMBridgeClosure.Target.Simulation
example : UniformTM → Prop := @pin_Simulation
def pin_Raw : Nat → Prop := @StandardTMBridgeClosure.Target.Raw
example : (k : Nat) → Prop := @StandardTMBridgeClosure.Target.Raw
example : (k : Nat) → Prop := @pin_Raw
#print axioms StandardTMBridgeClosure.encode
#print axioms pin_encode
#print axioms StandardTMBridgeClosure.compile
#print axioms pin_compile
#print axioms StandardTMBridgeClosure.steps
#print axioms pin_steps
#print axioms StandardTMBridgeClosure.Represents
#print axioms pin_Represents
#print axioms StandardTMBridgeClosure.degree
#print axioms pin_degree
#print axioms StandardTMBridgeClosure.Target.Source
#print axioms pin_Source
#print axioms StandardTMBridgeClosure.Target.Simulation
#print axioms pin_Simulation
#print axioms StandardTMBridgeClosure.Target.Raw
#print axioms pin_Raw
end StandardTMBridgeClosure.Audit
