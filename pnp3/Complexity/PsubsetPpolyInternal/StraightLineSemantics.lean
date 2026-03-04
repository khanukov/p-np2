import Complexity.PsubsetPpolyInternal.StraightLine

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace StraightLine

open Pnp3.Complexity
open Pnp3.Complexity.ArchiveStraightLineAdapter
open Boolcube

variable {n : Nat}

mutual
  theorem eval_toCircuitWireAux (C : Circuit n) :
      ∀ {g : Nat} {hg : g ≤ C.gates} {i : Fin (n + g)} {x : Point n},
        Circuit.eval (toCircuitWireAux C g hg i) x =
          evalWireAux C x g hg i
    | g, hg, i, x => by
        classical
        by_cases h : (i : Nat) < n
        · have hi : (⟨(i : Nat), h⟩ : Fin n) = ⟨i, h⟩ := rfl
          simpa [toCircuitWireAux, h, evalWireAux, hi, Circuit.eval]
        · set j : Nat := (i : Nat) - n with hj
          have hInputs : n ≤ (i : Nat) := Nat.le_of_not_gt h
          have hj_lt : j < g := by
            have hlt : (i : Nat) < n + g := i.isLt
            dsimp [j] at *
            omega
          have hj_total : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          have hGate := eval_toCircuitGateAux (C := C) (g := j) (hg := hj_total) (x := x)
          unfold toCircuitWireAux evalWireAux
          simp [h, hj, hInputs, hj_lt]
          exact hGate

  theorem eval_toCircuitGateAux (C : Circuit n) :
      ∀ {g : Nat} {hg : g < C.gates} {x : Point n},
        Circuit.eval (toCircuitGateAux C hg) x =
          evalGateAux C x hg
    | g, hg, x => by
        classical
        cases hOp : C.gate ⟨g, hg⟩ with
        | const b =>
            simp [toCircuitGateAux, hOp, evalGateAux, Circuit.eval]
        | not i =>
          have hi := eval_toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) (i := i) (x := x)
          simpa [toCircuitGateAux, hOp, evalGateAux, Circuit.eval] using
            congrArg (fun t => !t) hi
        | and i j =>
            have hi := eval_toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) (i := i) (x := x)
            have hj := eval_toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) (i := j) (x := x)
            simpa [toCircuitGateAux, hOp, evalGateAux, Circuit.eval, hi, hj]
        | or i j =>
            have hi := eval_toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) (i := i) (x := x)
            have hj := eval_toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) (i := j) (x := x)
            simpa [toCircuitGateAux, hOp, evalGateAux, Circuit.eval, hi, hj]
end

mutual
  theorem evalWireAux_withOutput (C : Circuit n) (out : Fin (n + C.gates)) :
      ∀ {g : Nat} {hg : g ≤ C.gates} {i : Fin (n + g)} {x : Point n},
        evalWireAux (withOutput C out) x g (by simpa [withOutput] using hg) i =
          evalWireAux C x g hg i
    | g, hg, i, x => by
        classical
        by_cases h : (i : Nat) < n
        · simp [evalWireAux, h]
        · set j : Nat := (i : Nat) - n with hj
          have hInputs : n ≤ (i : Nat) := Nat.le_of_not_gt h
          have hj_lt : j < g := by
            have hlt : (i : Nat) < n + g := i.isLt
            dsimp [j] at *
            omega
          have hj_total : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          have hGate := evalGateAux_withOutput (C := C) (out := out)
            (g := j) (hg := hj_total) (x := x)
          unfold evalWireAux
          simp [h, hj, hInputs, hj_lt]
          exact hGate

  theorem evalGateAux_withOutput (C : Circuit n) (out : Fin (n + C.gates)) :
      ∀ {g : Nat} {hg : g < C.gates} {x : Point n},
        evalGateAux (withOutput C out) x (by simpa [withOutput] using hg) =
          evalGateAux C x hg
    | g, hg, x => by
        classical
        cases hOp : C.gate ⟨g, hg⟩ with
        | const b =>
            simp [evalGateAux, withOutput, hOp]
        | not i =>
            have hi := evalWireAux_withOutput (C := C) (out := out)
              (g := g) (hg := Nat.le_of_lt hg) (i := i) (x := x)
            simpa [evalGateAux, withOutput, hOp] using congrArg (fun t => !t) hi
        | and i j =>
            have hi := evalWireAux_withOutput (C := C) (out := out)
              (g := g) (hg := Nat.le_of_lt hg) (i := i) (x := x)
            have hj := evalWireAux_withOutput (C := C) (out := out)
              (g := g) (hg := Nat.le_of_lt hg) (i := j) (x := x)
            simpa [evalGateAux, withOutput, hOp, hi, hj] using congrArg₂ (fun a b => a && b) hi hj
        | or i j =>
            have hi := evalWireAux_withOutput (C := C) (out := out)
              (g := g) (hg := Nat.le_of_lt hg) (i := i) (x := x)
            have hj := evalWireAux_withOutput (C := C) (out := out)
              (g := g) (hg := Nat.le_of_lt hg) (i := j) (x := x)
            simpa [evalGateAux, withOutput, hOp, hi, hj] using congrArg₂ (fun a b => a || b) hi hj
end

mutual
  lemma evalWireAux_snoc_old (C : Circuit n)
      (op : GateOp (n + C.gates)) (x : Point n) :
      ∀ {g : Nat} (hg : g ≤ C.gates) (i : Fin (n + g)),
        evalWireAux (snoc C op) x g (Nat.le_trans hg (Nat.le_succ _)) i =
          evalWireAux C x g hg i
    | 0, _, i => by
        simp [evalWireAux]
    | Nat.succ g, hg, i => by
        by_cases hInput : (i : Nat) < n
        · simp [evalWireAux, hInput]
        · have hInputs : n ≤ (i : Nat) := Nat.le_of_not_gt hInput
          set j : Nat := (i : Nat) - n
          have hj_lt : j < Nat.succ g := by
            dsimp [j]
            omega
          have hj_gate : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          have ihGate := evalGateAux_snoc_old C op x (g := j) hj_gate
          unfold evalWireAux
          simp only [hInput, snoc]
          exact ihGate

  lemma evalGateAux_snoc_old (C : Circuit n)
      (op : GateOp (n + C.gates)) (x : Point n) :
      ∀ {g : Nat} (hg : g < C.gates),
        evalGateAux (snoc C op) x (Nat.lt_of_lt_of_le hg (Nat.le_succ _)) =
          evalGateAux C x hg
    | g, hg => by
        have hgate :
            (snoc C op).gate ⟨g, Nat.lt_of_lt_of_le hg (Nat.le_succ _)⟩ =
              C.gate ⟨g, hg⟩ := by
          simp [snoc, hg]
        cases hOp : C.gate ⟨g, hg⟩ with
        | const b =>
            simp [evalGateAux, hgate, hOp]
        | not u =>
            have hu := evalWireAux_snoc_old C op x (g := g) (hg := Nat.le_of_lt hg) u
            simpa [evalGateAux, hgate, hOp] using congrArg (fun t => !t) hu
        | and u v =>
            have hu := evalWireAux_snoc_old C op x (g := g) (hg := Nat.le_of_lt hg) u
            have hv := evalWireAux_snoc_old C op x (g := g) (hg := Nat.le_of_lt hg) v
            simpa [evalGateAux, hgate, hOp, hu, hv]
        | or u v =>
            have hu := evalWireAux_snoc_old C op x (g := g) (hg := Nat.le_of_lt hg) u
            have hv := evalWireAux_snoc_old C op x (g := g) (hg := Nat.le_of_lt hg) v
            simpa [evalGateAux, hgate, hOp, hu, hv]
end

@[simp] lemma evalWire_snoc_lift (C : Circuit n)
    (op : GateOp (n + C.gates)) (x : Point n)
    (i : Fin (n + C.gates)) :
    evalWire (snoc C op) x (liftWire C i) = evalWire C x i := by
  unfold evalWire evalWireInternal
  by_cases hIn : (i : Nat) < n
  · have hInLift : ((liftWire C i : Fin (n + (C.gates + 1))) : Nat) < n := by
      simpa [liftWire] using hIn
    simp [hIn, hInLift, liftWire]
  · have hInLift : ¬ ((liftWire C i : Fin (n + (C.gates + 1))) : Nat) < n := by
      simpa [liftWire] using hIn
    let j : Nat := (i : Nat) - n
    have hj : j < C.gates := by
      have hi : (i : Nat) < n + C.gates := i.isLt
      dsimp [j] at *
      omega
    have hjSucc : j < (snoc C op).gates := by
      simpa [snoc] using Nat.lt_succ_of_lt hj
    have hGate :
        evalGateAux (snoc C op) x hjSucc = evalGateAux C x hj := by
      exact evalGateAux_snoc_old C op x (g := j) hj
    simp [hIn, hInLift, liftWire, j, hj, hjSucc, hGate]

@[simp] lemma eval_withOutput_eq_evalWire (C : Circuit n)
    (out : Fin (n + C.gates)) (x : Point n) :
    eval (withOutput C out) x = evalWire C x out := by
  unfold eval evalInternal evalWire evalWireInternal
  by_cases hIn : (out : Nat) < n
  · simp [hIn, withOutput]
  · let j : Nat := (out : Nat) - n
    have hj : j < C.gates := by
      have hout : (out : Nat) < n + C.gates := out.isLt
      dsimp [j]
      omega
    have hGate := evalGateAux_withOutput (C := C) (out := out)
      (g := j) (hg := hj) (x := x)
    simp [hIn, j, withOutput] at hGate ⊢
    exact hGate

lemma evalWireAux_full_eq_evalWireInternal (C : Circuit n) (x : Point n)
    (i : Fin (n + C.gates)) :
    evalWireAux C x C.gates le_rfl i = evalWireInternal C x i := by
  by_cases h : (i : Nat) < n
  · simp [evalWireAux, evalWireInternal, h]
  · set j : Nat := (i : Nat) - n with hj
    have hj_lt : j < C.gates := by
      have hi : (i : Nat) < n + C.gates := i.isLt
      dsimp [j] at *
      omega
    unfold evalWireAux evalWireInternal
    unfold evalGateAux
    simp [h, hj, hj_lt]

@[simp] lemma evalWire_snoc_last (C : Circuit n)
    (op : GateOp (n + C.gates)) (x : Point n) :
    evalWire (snoc C op) x (Fin.last (n + C.gates)) =
      match op with
      | .const b => b
      | .not u => !(evalWire C x u)
      | .and u v => (evalWire C x u) && (evalWire C x v)
      | .or u v => (evalWire C x u) || (evalWire C x v) := by
  classical
  have hj : C.gates < (snoc C op).gates := by simp [snoc]
  have hWire :
      evalWire (snoc C op) x (Fin.last (n + C.gates)) =
        evalGateAux (snoc C op) x hj := by
    simpa [evalWire, snoc] using
      (evalWireInternal_gate (C := snoc C op) (x := x) (j := C.gates) hj)
  have hGate : (snoc C op).gate ⟨C.gates, hj⟩ = op := by simp [snoc]
  cases op with
  | const b =>
      simp [hWire, evalGateAux, hGate]
  | not u =>
      have hu := evalWireAux_snoc_old (C := C) (op := .not u) (x := x)
        (g := C.gates) (hg := le_rfl) u
      have hu' : evalWireAux C x C.gates le_rfl u = evalWireInternal C x u :=
        evalWireAux_full_eq_evalWireInternal (C := C) (x := x) u
      simp [hWire, evalGateAux, hGate, hu, hu', evalWire]
  | and u v =>
      have hu := evalWireAux_snoc_old (C := C) (op := .and u v) (x := x)
        (g := C.gates) (hg := le_rfl) u
      have hv := evalWireAux_snoc_old (C := C) (op := .and u v) (x := x)
        (g := C.gates) (hg := le_rfl) v
      have hu' : evalWireAux C x C.gates le_rfl u = evalWireInternal C x u :=
        evalWireAux_full_eq_evalWireInternal (C := C) (x := x) u
      have hv' : evalWireAux C x C.gates le_rfl v = evalWireInternal C x v :=
        evalWireAux_full_eq_evalWireInternal (C := C) (x := x) v
      simp [hWire, evalGateAux, hGate, hu, hv, hu', hv', evalWire]
  | or u v =>
      have hu := evalWireAux_snoc_old (C := C) (op := .or u v) (x := x)
        (g := C.gates) (hg := le_rfl) u
      have hv := evalWireAux_snoc_old (C := C) (op := .or u v) (x := x)
        (g := C.gates) (hg := le_rfl) v
      have hu' : evalWireAux C x C.gates le_rfl u = evalWireInternal C x u :=
        evalWireAux_full_eq_evalWireInternal (C := C) (x := x) u
      have hv' : evalWireAux C x C.gates le_rfl v = evalWireInternal C x v :=
        evalWireAux_full_eq_evalWireInternal (C := C) (x := x) v
      simp [hWire, evalGateAux, hGate, hu, hv, hu', hv', evalWire]

@[simp] lemma eval_toCircuitWire (C : Circuit n) (x : Point n)
    (i : Fin (n + C.gates)) :
    Circuit.eval (toCircuitWire (C := C) i) x =
      evalWire (C := C) (x := x) i := by
  calc
    Circuit.eval (toCircuitWire (C := C) i) x
        = evalWireAux C x C.gates le_rfl i := by
            simpa [toCircuitWire] using
              (eval_toCircuitWireAux (C := C) (g := C.gates) (hg := le_rfl) (i := i) (x := x))
    _ = evalWireInternal C x i := evalWireAux_full_eq_evalWireInternal (C := C) (x := x) i
    _ = evalWire (C := C) (x := x) i := by rfl

@[simp] lemma eval_toCircuit (C : Circuit n) (x : Point n) :
    Circuit.eval (toCircuit (C := C)) x = eval C x := by
  simpa [toCircuit, eval_eq_evalWire, toCircuitWire]
    using eval_toCircuitWire (C := C) (x := x) C.output

/-!
## Eval agreement: archive (DAG) semantics = internal straight-line semantics

The archive layer evaluates via `DagCircuit.eval (toDag C) x`, while the
internal layer uses `evalInternal C x` (= `evalGateAux`-based recursion).
Both are structurally recursive on gate index and agree pointwise.
-/

section EvalAgreement

open Pnp3.ComplexityInterfaces
open Pnp3.Complexity.ArchiveStraightLineAdapter

/--
Key lemma: `toDagWire` on an input-range index produces `.input`.
-/
private lemma toDagWire_input {n g : Nat} (i : Fin (n + g)) (h : (i : Nat) < n) :
    toDagWire (n := n) (g := g) i = DagWire.input ⟨i, h⟩ := by
  unfold toDagWire
  simp [h]

/--
Key lemma: `toDagWire` on a gate-range index produces `.gate`.
-/
private lemma toDagWire_gate {n g : Nat} (i : Fin (n + g)) (h : ¬ (i : Nat) < n) :
    toDagWire (n := n) (g := g) i =
      DagWire.gate ⟨(i : Nat) - n, by omega⟩ := by
  unfold toDagWire
  simp [h]

/--
Auxiliary: for all gate indices below bound `G`, DAG evalGateAt and
internal evalGateAux agree.  Standard Nat induction encoding strong induction.
-/
private theorem dagEvalGateAt_eq_aux (C : Circuit n) (x : Point n) :
    ∀ (G : Nat) (g : Nat), g < G →
      ∀ (hgDag : g < (toDag C).gates) (hg : g < C.gates),
        DagCircuit.eval.evalGateAt (toDag C) x g hgDag =
          evalGateAux C x hg := by
  intro G
  induction G with
  | zero => intro g hgG; exact absurd hgG (Nat.not_lt_zero g)
  | succ G ih =>
    intro g hgG hgDag hg
    have ih' : ∀ j, j < g →
        ∀ (hjDag : j < (toDag C).gates) (hj : j < C.gates),
          DagCircuit.eval.evalGateAt (toDag C) x j hjDag =
            evalGateAux C x hj := by
      intro j hjg hjDag hj
      exact ih j (Nat.lt_of_lt_of_le hjg (Nat.lt_succ_iff.mp hgG)) hjDag hj
    -- Case split on the gate operation
    -- The key step: unfold both DagCircuit.eval.evalGateAt and evalGateAux
    -- one level, then match on the gate operation.
    have hGateDag : (toDag C).gate ⟨g, hgDag⟩ = toDagOp (C.gate ⟨g, hg⟩) := by
      simp [toDag]
    cases hOp : C.gate ⟨g, hg⟩ with
    | const b =>
      unfold DagCircuit.eval.evalGateAt evalGateAux
      simp [hGateDag, hOp, toDagOp]
    | not u =>
      unfold DagCircuit.eval.evalGateAt evalGateAux
      simp only [hGateDag, hOp, toDagOp]
      congr 1
      by_cases hu : (u : Nat) < n
      · simp [toDagWire_input u hu]; rfl
      · have huGate := toDagWire_gate (n := n) (g := g) u hu
        simp [huGate]
        have hlt : (u : Nat) - n < g := by omega
        have hlt' : (u : Nat) - n < C.gates := by omega
        have hltDag : (u : Nat) - n < (toDag C).gates := by
          simpa [toDag] using hlt'
        rw [ih' _ hlt hltDag hlt']
        unfold evalWireAux; simp [hu]
    | and u v =>
      unfold DagCircuit.eval.evalGateAt evalGateAux
      simp only [hGateDag, hOp, toDagOp]
      congr 1
      · by_cases hu : (u : Nat) < n
        · simp [toDagWire_input u hu]; rfl
        · have huGate := toDagWire_gate (n := n) (g := g) u hu
          simp [huGate]
          have hlt : (u : Nat) - n < g := by omega
          have hlt' : (u : Nat) - n < C.gates := by omega
          have hltDag : (u : Nat) - n < (toDag C).gates := by
            simpa [toDag] using hlt'
          rw [ih' _ hlt hltDag hlt']
          unfold evalWireAux; simp [hu]
      · by_cases hv : (v : Nat) < n
        · simp [toDagWire_input v hv]; rfl
        · have hvGate := toDagWire_gate (n := n) (g := g) v hv
          simp [hvGate]
          have hlt : (v : Nat) - n < g := by omega
          have hlt' : (v : Nat) - n < C.gates := by omega
          have hltDag : (v : Nat) - n < (toDag C).gates := by
            simpa [toDag] using hlt'
          rw [ih' _ hlt hltDag hlt']
          unfold evalWireAux; simp [hv]
    | or u v =>
      unfold DagCircuit.eval.evalGateAt evalGateAux
      simp only [hGateDag, hOp, toDagOp]
      congr 1
      · by_cases hu : (u : Nat) < n
        · simp [toDagWire_input u hu]; rfl
        · have huGate := toDagWire_gate (n := n) (g := g) u hu
          simp [huGate]
          have hlt : (u : Nat) - n < g := by omega
          have hlt' : (u : Nat) - n < C.gates := by omega
          have hltDag : (u : Nat) - n < (toDag C).gates := by
            simpa [toDag] using hlt'
          rw [ih' _ hlt hltDag hlt']
          unfold evalWireAux; simp [hu]
      · by_cases hv : (v : Nat) < n
        · simp [toDagWire_input v hv]; rfl
        · have hvGate := toDagWire_gate (n := n) (g := g) v hv
          simp [hvGate]
          have hlt : (v : Nat) - n < g := by omega
          have hlt' : (v : Nat) - n < C.gates := by omega
          have hltDag : (v : Nat) - n < (toDag C).gates := by
            simpa [toDag] using hlt'
          rw [ih' _ hlt hltDag hlt']
          unfold evalWireAux; simp [hv]

/--
Gate-level agreement between DAG evalGateAt and internal evalGateAux.
-/
private theorem dagEvalGateAt_eq_evalGateAux (C : Circuit n) (x : Point n)
    (g : Nat) (hgDag : g < (toDag C).gates) (hg : g < C.gates) :
    DagCircuit.eval.evalGateAt (toDag C) x g hgDag =
      evalGateAux C x hg :=
  dagEvalGateAt_eq_aux C x (g + 1) g (Nat.lt_succ_self g) hgDag hg

/--
Archive DAG evaluation agrees with internal straight-line evaluation for
any `StraightLineCircuit`.

This is the universal `EvalAgreement` statement needed by the compiler
assembly route.
-/
theorem archive_eval_eq_internal (C : Circuit n) (x : Point n) :
    ArchiveStraightLineAdapter.eval C x = StraightLine.eval C x := by
  unfold ArchiveStraightLineAdapter.eval StraightLine.eval evalInternal
  -- Unfold the DAG evaluation
  show DagCircuit.eval (toDag C) x = _
  unfold DagCircuit.eval
  -- Case split on output wire
  by_cases hOut : (C.output : Nat) < n
  · -- Output is an input wire
    have hOutDag : (toDag C).output = DagWire.input ⟨C.output, hOut⟩ := by
      simp [toDag, toDagWire, hOut]
    simp [hOutDag]
  · -- Output is a gate wire
    have hOutDag : (toDag C).output =
        DagWire.gate ⟨(C.output : Nat) - n, by
          have := C.output.isLt; omega⟩ := by
      simp [toDag, toDagWire, hOut]
    simp [hOutDag]
    have hj : (C.output : Nat) - n < C.gates := by
      have := C.output.isLt; omega
    exact dagEvalGateAt_eq_evalGateAux C x _ _ hj

end EvalAgreement

/-!
## Prefix preservation: evaluating old wires in an extended circuit

When `C'` extends `C` by appending gates (i.e. `C.gates ≤ C'.gates` and the
shared prefix of gates agrees), evaluating a wire from `C` in `C'` gives the
same result. This is the multi-gate generalisation of `evalWire_snoc_lift`.
-/

section PrefixPreservation

/-- Gate at index `j` in `snoc C op` agrees with `C` when `j < C.gates`. -/
@[simp] lemma snoc_gate_old {n : Nat} (C : Circuit n)
    (op : GateOp (n + C.gates)) (j : Nat) (hj : j < C.gates) :
    (snoc C op).gate ⟨j, Nat.lt_of_lt_of_le hj (Nat.le_succ _)⟩ =
      C.gate ⟨j, hj⟩ := by
  simp [snoc, hj]

mutual
  theorem evalWireAux_prefix {n : Nat} {C C' : Circuit n} (x : Boolcube.Point n)
      (hGates : C.gates ≤ C'.gates)
      (hGate : ∀ (j : Nat) (hj : j < C.gates),
        C'.gate ⟨j, Nat.lt_of_lt_of_le hj hGates⟩ = C.gate ⟨j, hj⟩) :
      ∀ (g : Nat) (hg : g ≤ C.gates) (i : Fin (n + g)),
        evalWireAux C' x g (Nat.le_trans hg hGates) i = evalWireAux C x g hg i
    | 0, _, i => by simp [evalWireAux]
    | Nat.succ g, hg, i => by
        by_cases hInput : (i : Nat) < n
        · simp [evalWireAux, hInput]
        · set j : Nat := (i : Nat) - n
          have hj_lt : j < Nat.succ g := by dsimp [j]; omega
          have hj_gate : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          have ihGate := evalGateAux_prefix (C := C) (C' := C') x hGates hGate hj_gate
          unfold evalWireAux
          simp only [hInput, ↓reduceDIte]
          exact ihGate

  theorem evalGateAux_prefix {n : Nat} {C C' : Circuit n} (x : Boolcube.Point n)
      (hGates : C.gates ≤ C'.gates)
      (hGate : ∀ (j : Nat) (hj : j < C.gates),
        C'.gate ⟨j, Nat.lt_of_lt_of_le hj hGates⟩ = C.gate ⟨j, hj⟩) :
      ∀ {g : Nat} (hg : g < C.gates),
        evalGateAux C' x (Nat.lt_of_lt_of_le hg hGates) = evalGateAux C x hg
    | g, hg => by
        have hgate_eq :
            C'.gate ⟨g, Nat.lt_of_lt_of_le hg hGates⟩ = C.gate ⟨g, hg⟩ :=
          hGate g hg
        cases hOp : C.gate ⟨g, hg⟩ with
        | const b =>
            simp [evalGateAux, hgate_eq, hOp]
        | not u =>
            have hu := evalWireAux_prefix (C := C) (C' := C') x hGates hGate
              g (Nat.le_of_lt hg) u
            simpa [evalGateAux, hgate_eq, hOp] using congrArg (fun t => !t) hu
        | and u v =>
            have hu := evalWireAux_prefix (C := C) (C' := C') x hGates hGate
              g (Nat.le_of_lt hg) u
            have hv := evalWireAux_prefix (C := C) (C' := C') x hGates hGate
              g (Nat.le_of_lt hg) v
            simpa [evalGateAux, hgate_eq, hOp, hu, hv]
        | or u v =>
            have hu := evalWireAux_prefix (C := C) (C' := C') x hGates hGate
              g (Nat.le_of_lt hg) u
            have hv := evalWireAux_prefix (C := C) (C' := C') x hGates hGate
              g (Nat.le_of_lt hg) v
            simpa [evalGateAux, hgate_eq, hOp, hu, hv]
end

/--
General prefix preservation: evaluating a wire from `C` in the extended
circuit `C'` gives the same value, provided the two circuits agree on all
gates below `C.gates`.
-/
theorem evalWire_prefix {n : Nat} {C C' : Circuit n} (x : Boolcube.Point n)
    (hGates : C.gates ≤ C'.gates)
    (hGate : ∀ (j : Nat) (hj : j < C.gates),
      C'.gate ⟨j, Nat.lt_of_lt_of_le hj hGates⟩ = C.gate ⟨j, hj⟩)
    (i : Fin (n + C.gates)) :
    evalWire C' x ⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.add_le_add_left hGates n)⟩ =
      evalWire C x i := by
  unfold evalWire evalWireInternal
  by_cases hIn : (i : Nat) < n
  · simp [hIn]
  · simp only [hIn, ↓reduceDIte]
    have hj : (i : Nat) - n < C.gates := by omega
    exact evalGateAux_prefix x hGates hGate hj

end PrefixPreservation

end StraightLine
end PsubsetPpoly
end Internal
end Pnp3
