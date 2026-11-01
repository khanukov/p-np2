import Mathlib.Computability.PostTuringMachine

/-! SG2 shrinking radius-one observation. This is not a whole-run compiler. -/
namespace UniformClassBridgeClosure.TM0DAG
open Turing
abbrev Symbol := Bool × Option Bool
abbrev Local (Λ : Type) := Bool × Λ × Symbol × Symbol × Symbol
abbrev Center (Λ : Type) := Bool × Λ × Symbol

/-- Exact unpadded iteration of the same TM0.step.
Ordinary.trace_eq_rawTrace in TM0OrdinaryTrace proves the actual model equality.
The saturated run below freezes after halt and is not continued Ordinary.trace. -/
def rawTrace {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ) :
    Nat → TM0.Cfg Symbol Λ → Option (TM0.Cfg Symbol Λ)
  | 0, s => some s
  | n+1, s => (TM0.step T s).bind (rawTrace T n)

def saturatedStep {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (s : Bool × TM0.Cfg Symbol Λ) : Bool × TM0.Cfg Symbol Λ :=
  if s.1 then s else match TM0.step T s.2 with
    | none => (true, s.2)
    | some v => (false, v)

def saturatedRun {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ) :
    Nat → (Bool × TM0.Cfg Symbol Λ) → Bool × TM0.Cfg Symbol Λ
  | 0, s => s
  | n+1, s => saturatedRun T n (saturatedStep T s)

def observe {Λ : Type} (s : Bool × TM0.Cfg Symbol Λ) : Local Λ :=
  (s.1, s.2.q, s.2.Tape.nth (-1), s.2.Tape.head, s.2.Tape.nth 1)

def center {Λ : Type} (s : Bool × TM0.Cfg Symbol Λ) : Center Λ :=
  (s.1, s.2.q, s.2.Tape.head)

def localStep {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (x : Local Λ) : Center Λ :=
  if x.1 then (true, x.2.1, x.2.2.2.1) else
    match T x.2.1 x.2.2.2.1 with
    | none => (true, x.2.1, x.2.2.2.1)
    | some (q, .move .left) => (false, q, x.2.2.1)
    | some (q, .move .right) => (false, q, x.2.2.2.2)
    | some (q, .write a) => (false, q, a)

theorem localStep_correct {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (s : Bool × TM0.Cfg Symbol Λ) :
    localStep T (observe s) = center (saturatedStep T s) := by
  rcases s with ⟨h, q, tape⟩
  cases h
  · cases e : T q tape.head with
    | none => simp [localStep, observe, center, saturatedStep, TM0.step, e]
    | some v =>
      rcases v with ⟨q', a⟩
      cases a with
      | write a => simp [localStep, observe, center, saturatedStep, TM0.step, e, Tape.write]
      | move d =>
        cases d with
        | left =>
          have hh : (tape.move Dir.left).head = tape.nth (-1) := by
            simpa only [Tape.nth_zero, zero_sub] using Tape.move_left_nth tape 0
          simp [localStep, observe, center, saturatedStep, TM0.step, e, hh]
        | right =>
          have hh : (tape.move Dir.right).head = tape.nth 1 := by
            simpa only [Tape.nth_zero, zero_add] using Tape.move_right_nth tape 0
          simp [localStep, observe, center, saturatedStep, TM0.step, e, hh]
  · rfl

theorem check_localStep_correct {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ)
    (s : Bool × TM0.Cfg (Bool × Option Bool) Λ) :
    localStep T (observe s) = center (saturatedStep T s) := localStep_correct T s

theorem saturatedRun_true {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (n : Nat) (s : TM0.Cfg Symbol Λ) : saturatedRun T n (true, s) = (true, s) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [saturatedRun, saturatedStep] using ih

theorem check_saturatedRun_true {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (n : Nat)
    (s : TM0.Cfg (Bool × Option Bool) Λ) :
    saturatedRun T n (true, s) = (true, s) := saturatedRun_true T n s

theorem trace_some {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (n : Nat) (s v : TM0.Cfg Symbol Λ) (h : rawTrace T n s = some v) :
    saturatedRun T n (false, s) = (false, v) := by
  induction n generalizing s with
  | zero => cases h; rfl
  | succ n ih =>
    cases e : TM0.step T s with
    | none => simp [rawTrace, e] at h
    | some w =>
      simp only [rawTrace, e, Option.bind_some] at h
      simpa [saturatedRun, saturatedStep, e] using ih w h

theorem check_trace_some {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (n : Nat)
    (s v : TM0.Cfg (Bool × Option Bool) Λ) (h : rawTrace T n s = some v) :
    saturatedRun T n (false, s) = (false, v) := trace_some T n s v h

theorem halted_after {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (n : Nat) (s v : TM0.Cfg Symbol Λ) (h : rawTrace T n s = some v)
    (stop : TM0.step T v = none) :
    saturatedRun T (n+1) (false, s) = (true, v) := by
  have commute : ∀ j x, saturatedRun T (j+1) x =
      saturatedStep T (saturatedRun T j x) := by
    intro j; induction j with
    | zero => intro x; rfl
    | succ j ih => intro x; exact ih (saturatedStep T x)
  rw [commute, trace_some T n s v h]
  simp [saturatedStep, stop]

theorem check_halted_after {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (n : Nat)
    (s v : TM0.Cfg (Bool × Option Bool) Λ) (h : rawTrace T n s = some v)
    (stop : TM0.step T v = none) :
    saturatedRun T (n+1) (false, s) = (true, v) := halted_after T n s v h stop

#check (Symbol : Type)
#check (Local : Type → Type)
#check (Center : Type → Type)
#check (@rawTrace : {Λ : Type} → [Inhabited Λ] → TM0.Machine Symbol Λ →
  Nat → TM0.Cfg Symbol Λ → Option (TM0.Cfg Symbol Λ))
#check (@saturatedStep : {Λ : Type} → [Inhabited Λ] → TM0.Machine Symbol Λ →
  (Bool × TM0.Cfg Symbol Λ) → Bool × TM0.Cfg Symbol Λ)
#check (@saturatedRun : {Λ : Type} → [Inhabited Λ] → TM0.Machine Symbol Λ →
  Nat → (Bool × TM0.Cfg Symbol Λ) → Bool × TM0.Cfg Symbol Λ)
#check (@observe : {Λ : Type} → (Bool × TM0.Cfg Symbol Λ) → Local Λ)
#check (@center : {Λ : Type} → (Bool × TM0.Cfg Symbol Λ) → Center Λ)
#check (@localStep : {Λ : Type} → [Inhabited Λ] → TM0.Machine Symbol Λ → Local Λ → Center Λ)
#print axioms Symbol
#print axioms Local
#print axioms Center
#print axioms rawTrace
#print axioms saturatedStep
#print axioms saturatedRun
#print axioms observe
#print axioms center
#print axioms localStep
#print axioms localStep_correct
#print axioms check_localStep_correct
#print axioms saturatedRun_true
#print axioms check_saturatedRun_true
#print axioms trace_some
#print axioms check_trace_some
#print axioms halted_after
#print axioms check_halted_after
-- SG2_LITERAL_TYPE_PINS: mechanical elaboration checks, not independent reproof.
#check (@localStep_correct : ∀ {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (s : Bool × TM0.Cfg Symbol Λ),
    localStep T (observe s) = center (saturatedStep T s))
#check (@check_localStep_correct : ∀ {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ)
    (s : Bool × TM0.Cfg (Bool × Option Bool) Λ),
    localStep T (observe s) = center (saturatedStep T s))
#check (@saturatedRun_true : ∀ {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (n : Nat) (s : TM0.Cfg Symbol Λ),
    saturatedRun T n (true, s) = (true, s))
#check (@check_saturatedRun_true : ∀ {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (n : Nat)
    (s : TM0.Cfg (Bool × Option Bool) Λ),
    saturatedRun T n (true, s) = (true, s))
#check (@trace_some : ∀ {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (n : Nat) (s v : TM0.Cfg Symbol Λ) (_h : rawTrace T n s = some v),
    saturatedRun T n (false, s) = (false, v))
#check (@check_trace_some : ∀ {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (n : Nat)
    (s v : TM0.Cfg (Bool × Option Bool) Λ) (_h : rawTrace T n s = some v),
    saturatedRun T n (false, s) = (false, v))
#check (@halted_after : ∀ {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (n : Nat) (s v : TM0.Cfg Symbol Λ) (_h : rawTrace T n s = some v)
    (_stop : TM0.step T v = none),
    saturatedRun T (n+1) (false, s) = (true, v))
#check (@check_halted_after : ∀ {Λ : Type} [Inhabited Λ]
    (T : TM0.Machine (Bool × Option Bool) Λ) (n : Nat)
    (s v : TM0.Cfg (Bool × Option Bool) Λ) (_h : rawTrace T n s = some v)
    (_stop : TM0.step T v = none),
    saturatedRun T (n+1) (false, s) = (true, v))

end UniformClassBridgeClosure.TM0DAG
