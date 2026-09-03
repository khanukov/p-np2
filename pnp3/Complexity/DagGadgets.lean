import Complexity.DagBundleCompose

/-!
# Small direct DAG gadgets

Only the projection, constant, NOT, AND, OR, and MUX gadgets needed by the
next fixed-width compilation slices are provided here.  Each bundle has one
output and owns one shared copy of its circuit gate graph.
-/

namespace Pnp3
namespace ComplexityInterfaces
namespace DagCircuit

/-- One-output, zero-gate projection bundle. -/
def projectionBundle {n : Nat} (j : Fin n) : DagBundle n 1 where
  gates := 0
  gate := fun i => absurd i.2 (Nat.not_lt_zero i.1)
  output := fun _ => DagWire.input j

@[simp] theorem projectionBundle_gates {n : Nat} (j : Fin n) :
    (projectionBundle j).gates = 0 := rfl

@[simp] theorem evalOutput_projectionBundle {n : Nat} (j : Fin n)
    (x : Bitstring n) :
    (projectionBundle j).evalOutput 0 x = x j := rfl

private def singletonBundle {n : Nat} (C : DagCircuit n) : DagBundle n 1 where
  gates := C.gates
  gate := C.gate
  output := fun _ => C.output

private theorem evalOutput_singletonBundle {n : Nat} (C : DagCircuit n)
    (x : Bitstring n) :
    (singletonBundle C).evalOutput 0 x = eval C x := rfl

/-- One-output constant bundle, reusing the existing constant circuit. -/
def constantBundle (n : Nat) (b : Bool) : DagBundle n 1 :=
  singletonBundle (constCircuit n b)

@[simp] theorem constantBundle_gates (n : Nat) (b : Bool) :
    (constantBundle n b).gates = 1 := rfl

@[simp] theorem evalOutput_constantBundle (n : Nat) (b : Bool)
    (x : Bitstring n) :
    (constantBundle n b).evalOutput 0 x = b := by
  rw [constantBundle, evalOutput_singletonBundle, eval_constCircuit]

/-- Direct one-gate Boolean negation circuit. -/
def notCircuit : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input 0)
  output := DagWire.gate ⟨0, Nat.zero_lt_one⟩

@[simp] theorem notCircuit_gates : notCircuit.gates = 1 := rfl

@[simp] theorem size_notCircuit : size notCircuit = 2 := rfl

@[simp] theorem eval_notCircuit (x : Bitstring 1) :
    eval notCircuit x = !x 0 := by
  simp [eval, DagCircuit.eval.evalGateAt, notCircuit]

/-- Direct one-gate Boolean conjunction circuit. -/
def andCircuit : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.and (DagWire.input 0) (DagWire.input 1)
  output := DagWire.gate ⟨0, Nat.zero_lt_one⟩

@[simp] theorem andCircuit_gates : andCircuit.gates = 1 := rfl

@[simp] theorem size_andCircuit : size andCircuit = 2 := rfl

@[simp] theorem eval_andCircuit (x : Bitstring 2) :
    eval andCircuit x = (x 0 && x 1) := by
  simp [eval, DagCircuit.eval.evalGateAt, andCircuit]

/-- Direct one-gate Boolean disjunction circuit. -/
def orCircuit : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.or (DagWire.input 0) (DagWire.input 1)
  output := DagWire.gate ⟨0, Nat.zero_lt_one⟩

@[simp] theorem orCircuit_gates : orCircuit.gates = 1 := rfl

@[simp] theorem size_orCircuit : size orCircuit = 2 := rfl

@[simp] theorem eval_orCircuit (x : Bitstring 2) :
    eval orCircuit x = (x 0 || x 1) := by
  simp [eval, DagCircuit.eval.evalGateAt, orCircuit]

/-! ## Linear false-seeded big OR -/

/-- Disjoin a list of direct circuits.  The empty list is represented by one
false gate; each nonempty row appends that circuit once and one OR gate. -/
def bigOrCircuit {n : Nat} : List (DagCircuit n) → DagCircuit n
  | [] => constCircuit n false
  | C :: Cs => substInputs orCircuit ![C, bigOrCircuit Cs]

/-- Exact evaluation of the false-seeded big OR. -/
@[simp] theorem eval_bigOrCircuit {n : Nat} (Cs : List (DagCircuit n))
    (x : Bitstring n) :
    eval (bigOrCircuit Cs) x = Cs.any (fun C => eval C x) := by
  induction Cs with
  | nil => simp [bigOrCircuit]
  | cons C Cs ih => simp [bigOrCircuit, ih]

/-- Map-friendly evaluation form used by finite compile-time enumerations. -/
theorem eval_bigOrCircuit_map {n : Nat} {A : Type} (xs : List A)
    (C : A → DagCircuit n) (x : Bitstring n) :
    eval (bigOrCircuit (xs.map C)) x = xs.any (fun a => eval (C a) x) := by
  simp [Function.comp_def]

/-- `Fin`-enumeration specialization of `eval_bigOrCircuit_map`. -/
theorem eval_bigOrCircuit_finRange {n k : Nat} (C : Fin k → DagCircuit n)
    (x : Bitstring n) :
    eval (bigOrCircuit ((List.finRange k).map C)) x =
      (List.finRange k).any (fun i => eval (C i) x) :=
  eval_bigOrCircuit_map (List.finRange k) C x

/-- Exact linear gate formula, including the empty-list false seed. -/
@[simp] theorem bigOrCircuit_gates {n : Nat} (Cs : List (DagCircuit n)) :
    (bigOrCircuit Cs).gates =
      1 + (Cs.map (fun C => C.gates + 1)).sum := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
      rw [bigOrCircuit]
      change (bundleOfFamily 2 ![C, bigOrCircuit Cs]).gates + 1 = _
      rw [bundleOfFamily_gates]
      simp [ih]
      omega

/-- Coarse size-accounting form: the big OR uses at most the false seed plus
the sum of the input circuit sizes. -/
theorem bigOrCircuit_gates_le_size {n : Nat} (Cs : List (DagCircuit n)) :
    (bigOrCircuit Cs).gates ≤ 1 + (Cs.map size).sum := by
  rw [bigOrCircuit_gates]
  rfl

/-- Four-gate MUX assembled by circuit substitution.  Input 0 is the selector,
input 1 the true branch, and input 2 the false branch. -/
def muxCircuit : DagCircuit 3 :=
  substInputs orCircuit ![
    substInputs andCircuit ![inputProj 0, inputProj 1],
    substInputs andCircuit ![
      substInputs notCircuit ![inputProj 0],
      inputProj 2]]

@[simp] theorem muxCircuit_gates : muxCircuit.gates = 4 := rfl

@[simp] theorem size_muxCircuit : size muxCircuit = 5 := rfl

@[simp] theorem eval_muxCircuit (x : Bitstring 3) :
    eval muxCircuit x = if x 0 then x 1 else x 2 := by
  simp [muxCircuit]
  cases x 0 <;> simp

/-- Singleton bundle forms of the direct Boolean circuits. -/
def notBundle : DagBundle 1 1 := singletonBundle notCircuit
def andBundle : DagBundle 2 1 := singletonBundle andCircuit
def orBundle : DagBundle 2 1 := singletonBundle orCircuit
def muxBundle : DagBundle 3 1 := singletonBundle muxCircuit

@[simp] theorem notBundle_gates : notBundle.gates = 1 := rfl
@[simp] theorem andBundle_gates : andBundle.gates = 1 := rfl
@[simp] theorem orBundle_gates : orBundle.gates = 1 := rfl
@[simp] theorem muxBundle_gates : muxBundle.gates = 4 := rfl

@[simp] theorem evalOutput_notBundle (x : Bitstring 1) :
    notBundle.evalOutput 0 x = !x 0 := by
  rw [notBundle, evalOutput_singletonBundle, eval_notCircuit]

@[simp] theorem evalOutput_andBundle (x : Bitstring 2) :
    andBundle.evalOutput 0 x = (x 0 && x 1) := by
  rw [andBundle, evalOutput_singletonBundle, eval_andCircuit]

@[simp] theorem evalOutput_orBundle (x : Bitstring 2) :
    orBundle.evalOutput 0 x = (x 0 || x 1) := by
  rw [orBundle, evalOutput_singletonBundle, eval_orCircuit]

@[simp] theorem evalOutput_muxBundle (x : Bitstring 3) :
    muxBundle.evalOutput 0 x = if x 0 then x 1 else x 2 := by
  rw [muxBundle, evalOutput_singletonBundle, eval_muxCircuit]

/-- All eight MUX rows, including the selector-false negative literals. -/
theorem muxBundle_truthTable :
    (muxBundle.evalOutput 0 ![false, false, false] = false) ∧
    (muxBundle.evalOutput 0 ![false, false, true] = true) ∧
    (muxBundle.evalOutput 0 ![false, true, false] = false) ∧
    (muxBundle.evalOutput 0 ![false, true, true] = true) ∧
    (muxBundle.evalOutput 0 ![true, false, false] = false) ∧
    (muxBundle.evalOutput 0 ![true, false, true] = false) ∧
    (muxBundle.evalOutput 0 ![true, true, false] = true) ∧
    (muxBundle.evalOutput 0 ![true, true, true] = true) := by
  simp

/-- Two iterations of the NOT bundle compute the identity, derived from the
generic iteration semantics. -/
theorem doubleNot_iteration (v : Bitstring 1) :
    (iterateBundle notBundle 2).evalOutput 0 v = v 0 := by
  rw [evalOutput_iterateBundle_two]
  simp

/-- Concrete negative-literal regression for double negation. -/
theorem doubleNot_false_literal :
    (iterateBundle notBundle 2).evalOutput 0 ![false] = false := by
  rw [doubleNot_iteration]
  rfl

end DagCircuit
end ComplexityInterfaces
end Pnp3
