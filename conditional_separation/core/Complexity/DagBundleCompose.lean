import Complexity.DagCompose

/-!
# Generic fixed-width DAG-bundle composition

This infrastructure composes a whole upper bundle over one shared predecessor
bundle.  The predecessor gate graph is stored once, output width is unchanged,
and repeated fixed-width composition therefore has an exact linear gate count.
-/

namespace Pnp3
namespace ComplexityInterfaces
namespace DagCircuit

/-- Substitute all outputs of `B` for the inputs of every output of `S`.
The shared gate list of `B` occurs once, followed by the shared gate list of
`S`; no per-output circuit is copied. -/
def substBundle {m mid out : Nat} (S : DagBundle mid out)
    (B : DagBundle m mid) : DagBundle m out where
  gates := B.gates + S.gates
  gate := Fin.addCases (motive := fun i => DagGate m i.1)
    (fun p => B.gate p)
    (fun j => substGateWithBundle B (S.gate j))
  output := fun o => substWireWithBundle B (S.output o)

@[simp] theorem substBundle_gates {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) :
    (substBundle S B).gates = B.gates + S.gates := rfl

/-- The composed output family still has domain `Fin out`; composition does
not append historical outputs. -/
theorem substBundle_output_no_growth {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) :
    (substBundle S B).output = fun o : Fin out =>
      substWireWithBundle B (S.output o) := rfl

/-- Each output circuit is exactly the existing single-output substitution. -/
theorem asCircuit_substBundle {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) (o : Fin out) :
    (substBundle S B).asCircuit o =
      substInputsWithBundle (S.asCircuit o) B := rfl

/-- Bundle composition evaluates the upper output on the vector of lower
bundle outputs. -/
@[simp] theorem evalOutput_substBundle {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) (o : Fin out)
    (x : Bitstring m) :
    (substBundle S B).evalOutput o x =
      S.evalOutput o (fun j => B.evalOutput j x) := by
  rw [DagBundle.evalOutput, asCircuit_substBundle,
    eval_substInputsWithBundle]
  rfl

/-- Width-`W` identity bundle made only of input projections. -/
def identityBundle (W : Nat) : DagBundle W W where
  gates := 0
  gate := fun i => absurd i.2 (Nat.not_lt_zero i.1)
  output := fun o => DagWire.input o

@[simp] theorem identityBundle_gates (W : Nat) :
    (identityBundle W).gates = 0 := rfl

@[simp] theorem identityBundle_output (W : Nat) (o : Fin W) :
    (identityBundle W).output o = DagWire.input o := rfl

@[simp] theorem evalOutput_identityBundle (W : Nat) (o : Fin W)
    (v : Bitstring W) :
    (identityBundle W).evalOutput o v = v o := rfl

/-- The Boolean-vector function computed by a DAG bundle. -/
def DagBundle.evalFun {n out : Nat} (B : DagBundle n out) :
    Bitstring n → Bitstring out :=
  fun v o => B.evalOutput o v

@[simp] theorem DagBundle.evalFun_apply {n out : Nat} (B : DagBundle n out)
    (v : Bitstring n) (o : Fin out) :
    B.evalFun v o = B.evalOutput o v := rfl

@[simp] theorem evalFun_identityBundle (W : Nat) (v : Bitstring W) :
    (identityBundle W).evalFun v = v := by
  funext o
  exact evalOutput_identityBundle W o v

/-- Select, permute, or duplicate output wires without changing the shared
gate graph. -/
def reindexOutputs {n out out' : Nat} (B : DagBundle n out)
    (f : Fin out' → Fin out) : DagBundle n out' where
  gates := B.gates
  gate := B.gate
  output := fun o => B.output (f o)

@[simp] theorem reindexOutputs_gates {n out out' : Nat}
    (B : DagBundle n out) (f : Fin out' → Fin out) :
    (reindexOutputs B f).gates = B.gates := rfl

@[simp] theorem evalOutput_reindexOutputs {n out out' : Nat}
    (B : DagBundle n out) (f : Fin out' → Fin out) (o : Fin out')
    (v : Bitstring n) :
    (reindexOutputs B f).evalOutput o v = B.evalOutput (f o) v := rfl

/-- Repeat a fixed-width bundle, starting from the zero-gate identity.  The
orientation is `S` over the preceding iterate, matching repeated application
of `S.evalFun`. -/
def iterateBundle {W : Nat} (S : DagBundle W W) : Nat → DagBundle W W
  | 0 => identityBundle W
  | t + 1 => substBundle S (iterateBundle S t)

@[simp] theorem iterateBundle_zero {W : Nat} (S : DagBundle W W) :
    iterateBundle S 0 = identityBundle W := rfl

theorem iterateBundle_succ {W : Nat} (S : DagBundle W W) (t : Nat) :
    iterateBundle S (t + 1) = substBundle S (iterateBundle S t) := rfl

/-- Exact linear recurrence: each iteration appends the gate graph of `S`
once to the already-shared predecessor graph. -/
@[simp] theorem iterateBundle_gates {W : Nat} (S : DagBundle W W) :
    ∀ t : Nat, (iterateBundle S t).gates = t * S.gates
  | 0 => by simp [iterateBundle]
  | t + 1 => by
      rw [iterateBundle_succ, substBundle_gates, iterateBundle_gates]
      simp [Nat.add_mul]

/-- Exact semantics, oriented to Lean's `Nat.iterate`. -/
@[simp] theorem evalOutput_iterateBundle {W : Nat} (S : DagBundle W W) :
    ∀ (t : Nat) (v : Bitstring W) (o : Fin W),
      (iterateBundle S t).evalOutput o v = (S.evalFun^[t]) v o
  | 0, v, o => by simp
  | t + 1, v, o => by
      rw [iterateBundle_succ, evalOutput_substBundle]
      simp only [evalOutput_iterateBundle]
      change S.evalFun ((S.evalFun^[t]) v) o = _
      rw [Function.iterate_succ_apply']

@[simp] theorem iterateBundle_zero_gates {W : Nat} (S : DagBundle W W) :
    (iterateBundle S 0).gates = 0 := by
  rw [iterateBundle_gates]
  simp

@[simp] theorem iterateBundle_one_gates {W : Nat} (S : DagBundle W W) :
    (iterateBundle S 1).gates = S.gates := by
  rw [iterateBundle_gates]
  simp

@[simp] theorem iterateBundle_two_gates {W : Nat} (S : DagBundle W W) :
    (iterateBundle S 2).gates = 2 * S.gates :=
  iterateBundle_gates S 2

@[simp] theorem evalOutput_iterateBundle_zero {W : Nat}
    (S : DagBundle W W) (v : Bitstring W) (o : Fin W) :
    (iterateBundle S 0).evalOutput o v = v o := by simp

@[simp] theorem evalOutput_iterateBundle_one {W : Nat}
    (S : DagBundle W W) (v : Bitstring W) (o : Fin W) :
    (iterateBundle S 1).evalOutput o v = S.evalOutput o v := by simp

@[simp] theorem evalOutput_iterateBundle_two {W : Nat}
    (S : DagBundle W W) (v : Bitstring W) (o : Fin W) :
    (iterateBundle S 2).evalOutput o v = S.evalFun (S.evalFun v) o := by
  rw [evalOutput_iterateBundle]
  rfl

end DagCircuit
end ComplexityInterfaces
end Pnp3
