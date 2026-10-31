import UniformClassBridgeClosure.Model
import UniformClassBridgeClosure.PpolyDAG

/-! Literal transport from the admitted Ordinary model to the direct TM0 circuit route.
This proves identities of the actual raw trace and initialization, not halt padding. -/
namespace UniformClassBridgeClosure.Ordinary
open Turing Pnp3.ComplexityInterfaces

theorem trace_eq_rawTrace {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (t : Nat)
    (s : TM0.Cfg (Bool × Option Bool) Λ) :
    trace T t s = TM0DAG.rawTrace T t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => simp only [trace, TM0DAG.rawTrace, ih]

theorem check_trace_eq_rawTrace {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (t : Nat)
    (s : TM0.Cfg (Bool × Option Bool) Λ) :
    trace T t s = TM0DAG.rawTrace T t s :=
  trace_eq_rawTrace T t s

theorem inputConfig_eq_init {Λ : Type} [Inhabited Λ] {N : Nat} (y : Bitstring N) :
    TM0DAG.Window.inputConfig (Λ := Λ) y =
      TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)) := by
  rfl

theorem check_inputConfig_eq_init {Λ : Type} [Inhabited Λ] {N : Nat} (y : Bitstring N) :
    TM0DAG.Window.inputConfig (Λ := Λ) y =
      TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)) :=
  inputConfig_eq_init y

#check (@trace : {Λ : Type} → [Inhabited Λ] → TM0.Machine (Bool × Option Bool) Λ →
  Nat → TM0.Cfg (Bool × Option Bool) Λ → Option (TM0.Cfg (Bool × Option Bool) Λ))
#check (@TM0DAG.Window.inputConfig : {Λ : Type} → [Inhabited Λ] → {N : Nat} →
  Bitstring N → TM0.Cfg (Bool × Option Bool) Λ)
#check (@trace_eq_rawTrace : ∀ {Λ : Type} [Inhabited Λ]
  (T : TM0.Machine (Bool × Option Bool) Λ) (t : Nat)
  (s : TM0.Cfg (Bool × Option Bool) Λ), trace T t s = TM0DAG.rawTrace T t s)
#check (@check_trace_eq_rawTrace : ∀ {Λ : Type} [Inhabited Λ]
  (T : TM0.Machine (Bool × Option Bool) Λ) (t : Nat)
  (s : TM0.Cfg (Bool × Option Bool) Λ), trace T t s = TM0DAG.rawTrace T t s)
#check (@inputConfig_eq_init : ∀ {Λ : Type} [Inhabited Λ] {N : Nat} (y : Bitstring N),
  TM0DAG.Window.inputConfig (Λ := Λ) y =
    TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))
#check (@check_inputConfig_eq_init : ∀ {Λ : Type} [Inhabited Λ] {N : Nat} (y : Bitstring N),
  TM0DAG.Window.inputConfig (Λ := Λ) y =
    TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))
#print axioms trace_eq_rawTrace
#print axioms check_trace_eq_rawTrace
#print axioms inputConfig_eq_init
#print axioms check_inputConfig_eq_init
end UniformClassBridgeClosure.Ordinary
