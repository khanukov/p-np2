import Complexity.PsubsetPpolyInternal.StraightLine
import Complexity.PsubsetPpolyInternal.StraightLineSemantics

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace StraightLine

open Boolcube

variable {n : Nat}

/-- Result of compiling a tree circuit into a straight-line circuit. -/
structure Compiled (n : Nat) where
  ckt : Circuit n
  out : Fin (n + ckt.gates)

/-- Compiled family indexed by `Fin m` into one shared straight-line circuit. -/
structure CompiledFin (n m : Nat) where
  ckt : Circuit n
  out : Fin m → Fin (n + ckt.gates)

/-- Embed a wire from a suffix circuit into an appended circuit with `g₁` prefix gates. -/
def liftWireIntoAppend {n g₁ g₂ : Nat} :
    Fin (n + g₂) → Fin (n + (g₁ + g₂)) := by
  intro i
  by_cases hIn : (i : Nat) < n
  · exact ⟨i, by
      have hlt : (i : Nat) < n + (g₁ + g₂) :=
        Nat.lt_of_lt_of_le hIn (Nat.le_add_right n (g₁ + g₂))
      exact hlt⟩
  · have hge : n ≤ (i : Nat) := Nat.le_of_not_gt hIn
    let j : Nat := (i : Nat) - n
    have hj : j < g₂ := by
      have hi : (i : Nat) < n + g₂ := i.isLt
      dsimp [j]
      omega
    exact ⟨n + (g₁ + j), by
      have : g₁ + j < g₁ + g₂ := Nat.add_lt_add_left hj g₁
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.add_lt_add_left this n⟩

/-- Lift a gate operation through prefix-gate appending. -/
def liftOpIntoAppend {n g₁ g : Nat} :
    GateOp (n + g) → GateOp (n + (g₁ + g))
  | .const b => .const b
  | .not u => .not (liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g) u)
  | .and u v =>
      .and
        (liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g) u)
        (liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g) v)
  | .or u v =>
      .or
        (liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g) u)
        (liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g) v)

/-- Append `C₂` after `C₁` with canonical wire renumbering. -/
def appendCircuit {n : Nat} (C₁ C₂ : Circuit n) : Circuit n where
  gates := C₁.gates + C₂.gates
  gate := fun g =>
    if h : (g : Nat) < C₁.gates then
      by simpa using C₁.gate ⟨g, h⟩
    else
      by
        have hge : C₁.gates ≤ (g : Nat) := Nat.le_of_not_gt h
        let j : Nat := (g : Nat) - C₁.gates
        have hj : j < C₂.gates := by
          dsimp [j]
          omega
        have hgEq : (g : Nat) = C₁.gates + j := by
          dsimp [j]
          omega
        simpa [hgEq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (liftOpIntoAppend (n := n) (g₁ := C₁.gates) (g := j) (C₂.gate ⟨j, hj⟩))
  output := liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) C₂.output

/-- Wire of `C₁` viewed inside `appendCircuit C₁ C₂`. -/
def leftWireInAppend {n : Nat} (C₁ C₂ : Circuit n) :
    Fin (n + C₁.gates) → Fin (n + (C₁.gates + C₂.gates)) := by
  intro i
  by_cases hIn : (i : Nat) < n
  · exact ⟨i, by
      have hlt : (i : Nat) < n + (C₁.gates + C₂.gates) :=
        Nat.lt_of_lt_of_le hIn (Nat.le_add_right n (C₁.gates + C₂.gates))
      exact hlt⟩
  · let j : Nat := (i : Nat) - n
    have hj : j < C₁.gates := by
      have hi : (i : Nat) < n + C₁.gates := i.isLt
      dsimp [j]
      omega
    exact ⟨n + j, by
      have : n + j < n + C₁.gates := Nat.add_lt_add_left hj n
      have hle : n + C₁.gates ≤ n + (C₁.gates + C₂.gates) := by
        omega
      exact Nat.lt_of_lt_of_le this hle⟩

@[simp] lemma leftWireInAppend_val
    {n : Nat} (C₁ C₂ : Circuit n) (i : Fin (n + C₁.gates)) :
    ((leftWireInAppend C₁ C₂ i : Fin (n + (C₁.gates + C₂.gates))) : Nat) = i := by
  unfold leftWireInAppend
  by_cases hIn : (i : Nat) < n
  · simp [hIn]
  · simp [hIn]
    exact Nat.add_sub_of_le (Nat.le_of_not_gt hIn)


/-- A lifted wire is an input iff the original wire is an input. -/
@[simp] lemma liftWire_is_input
    {n g₁ g₂ : Nat} (w : Fin (n + g₂)) :
    (((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
      Fin (n + (g₁ + g₂))) : Nat) < n) ↔ ((w : Nat) < n) := by
  unfold liftWireIntoAppend
  by_cases h : (w : Nat) < n
  · simp [h]
  · simp [h]

/-- Value of a lifted wire in the input branch. -/
lemma liftWire_val_input
    {n g₁ g₂ : Nat} (w : Fin (n + g₂)) (h : (w : Nat) < n) :
    ((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
      Fin (n + (g₁ + g₂))) : Nat) = (w : Nat) := by
  unfold liftWireIntoAppend
  simp [h]

/-- Value of a lifted wire in the gate branch. -/
lemma liftWire_val_gate
    {n g₁ g₂ : Nat} (w : Fin (n + g₂)) (h : ¬ ((w : Nat) < n)) :
    ((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
      Fin (n + (g₁ + g₂))) : Nat) = (w : Nat) + g₁ := by
  unfold liftWireIntoAppend
  simp [h]
  omega

/--
Right-branch normal form for lifted wire values.

This is the concrete pointwise normalization used in append-right proofs:
the lifted wire value is either unchanged (input branch) or shifted by
`g₁` (gate branch).
-/
lemma liftWire_val_right
    {n g₁ g₂ : Nat} (w : Fin (n + g₂)) :
    ((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
      Fin (n + (g₁ + g₂))) : Nat) =
      if (w : Nat) < n then (w : Nat) else (w : Nat) + g₁ := by
  by_cases hw : (w : Nat) < n
  · simp [liftWire_val_input (n := n) (g₁ := g₁) (g₂ := g₂) (w := w) hw, hw]
  · simp [liftWire_val_gate (n := n) (g₁ := g₁) (g₂ := g₂) (w := w) hw, hw]


/--
Arithmetic normal form for the non-input branch of `liftWireIntoAppend`:
subtracting `n` from the lifted index exposes prefix offset `g₁` explicitly.
-/
lemma liftWire_sub_n_gate
    {n g₁ g₂ : Nat} (w : Fin (n + g₂)) (h : ¬ ((w : Nat) < n)) :
    (((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
      Fin (n + (g₁ + g₂))) : Nat) - n) = g₁ + ((w : Nat) - n) := by
  have hval := liftWire_val_gate (n := n) (g₁ := g₁) (g₂ := g₂) (w := w) h
  omega

/--
Bounded form of `liftWire_sub_n_gate`: the normalized lifted gate index stays
below the total appended gate budget.
-/
lemma liftWire_sub_n_gate_lt
    {n g₁ g₂ : Nat} (w : Fin (n + g₂)) (h : ¬ ((w : Nat) < n)) :
    (((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
      Fin (n + (g₁ + g₂))) : Nat) - n) < g₁ + g₂ := by
  have hw_lt : (w : Nat) - n < g₂ := by
    have hw : (w : Nat) < n + g₂ := w.isLt
    omega
  rw [liftWire_sub_n_gate (n := n) (g₁ := g₁) (g₂ := g₂) (w := w) h]
  exact Nat.add_lt_add_left hw_lt g₁

/--
If two input indices have the same `Nat` value, evaluating a boolean point at
those indices yields the same bit.

This tiny helper avoids repeating `Fin.ext`-style coercion arguments in
append/right proofs where only `val` equalities are available.
-/
lemma point_eval_eq_of_val_eq
    {n : Nat} (x : Boolcube.Point n) {i j : Fin n}
    (hval : (i : Nat) = (j : Nat)) :
    x i = x j := by
  have hij : i = j := Fin.ext hval
  simpa [hij]

/--
Input-case specialization for `liftWireIntoAppend`: the corresponding input
lookup in the original and lifted wires agrees.
-/
lemma point_eval_liftWire_input
    {n g₁ g₂ : Nat} (x : Boolcube.Point n)
    (w : Fin (n + g₂)) (hw : (w : Nat) < n) :
    x ⟨((liftWireIntoAppend (n := n) (g₁ := g₁) (g₂ := g₂) w :
          Fin (n + (g₁ + g₂))) : Nat),
        (liftWire_is_input (n := n) (g₁ := g₁) (g₂ := g₂) (w := w)).2 hw⟩ =
    x ⟨(w : Nat), hw⟩ := by
  apply point_eval_eq_of_val_eq (x := x)
  exact liftWire_val_input (n := n) (g₁ := g₁) (g₂ := g₂) (w := w) hw

/--
Generic non-input index normalization: inside `Fin (n + g)`, if a wire is not
an input (`¬ (w:Nat) < n`), then its gate-part index `(w:Nat) - n` is strictly
below the visible gate budget `g`.

This fact is used repeatedly in right-branch append proofs.
-/
lemma wire_sub_lt_of_not_input
    {n g : Nat} (w : Fin (n + g)) (hw : ¬ (w : Nat) < n) :
    (w : Nat) - n < g := by
  have hwLt : (w : Nat) < n + g := w.isLt
  omega

/--
Append-right specialization of `wire_sub_lt_of_not_input`: combining a visible
suffix bound `g < C₂.gates` with non-input status yields `(w:Nat)-n < C₂.gates`.
-/
lemma wire_sub_lt_suffix
    {n : Nat} (C₂ : Circuit n) {g : Nat} (hg : g < C₂.gates)
    (w : Fin (n + g)) (hw : ¬ (w : Nat) < n) :
    (w : Nat) - n < C₂.gates := by
  exact Nat.lt_trans (wire_sub_lt_of_not_input (w := w) hw) hg

/--
Input-branch specialization for `evalWireOf` under `liftWireIntoAppend`.

No recursive gate payload is needed in this branch: both sides reduce to the
same input lookup (up to `Fin` value equality).
-/
lemma evalWireOf_liftWire_input
    {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (hg : g < C₂.gates) (w : Fin (n + g)) (hw : (w : Nat) < n)
    (recA : ∀ j : Nat, j < C₁.gates + g → j < (appendCircuit C₁ C₂).gates → Bool)
    (recB : ∀ j : Nat, j < g → j < C₂.gates → Bool) :
    evalWireOf (appendCircuit C₁ C₂) x
      (by simpa [appendCircuit] using Nat.add_lt_add_left hg C₁.gates)
      (liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := g) w) recA =
    evalWireOf C₂ x hg w recB := by
  have hLiftIn :
      (((liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := g) w :
        Fin (n + (C₁.gates + g))) : Nat) < n) :=
    (liftWire_is_input (n := n) (g₁ := C₁.gates) (g₂ := g) (w := w)).2 hw
  unfold evalWireOf
  simp [hLiftIn, hw]
  simpa using point_eval_liftWire_input (x := x) (g₁ := C₁.gates) (g₂ := g) (w := w) hw

/--
Gate-branch specialization for `evalWireOf` under `liftWireIntoAppend`.

This isolates all index arithmetic/casts into explicit hypotheses (`hRec`), so
callers can focus on proving recursive payload equality.
-/
lemma evalWireOf_liftWire_gate
    {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (hg : g < C₂.gates) (w : Fin (n + g)) (hw : ¬ (w : Nat) < n)
    (recA : ∀ j : Nat, j < C₁.gates + g → j < (appendCircuit C₁ C₂).gates → Bool)
    (recB : ∀ j : Nat, j < g → j < C₂.gates → Bool)
    (hRec :
      recA (C₁.gates + ((w : Nat) - n))
        (by
          have hwSub : (w : Nat) - n < g := by
            omega
          exact Nat.add_lt_add_left hwSub C₁.gates)
        (by
          have hwSub : (w : Nat) - n < g := by
            omega
          have hwSub2 : (w : Nat) - n < C₂.gates := Nat.lt_trans hwSub hg
          simpa [appendCircuit] using Nat.add_lt_add_left hwSub2 C₁.gates)
      =
      recB ((w : Nat) - n)
        (by
          omega)
        (by
          have hwSub : (w : Nat) - n < g := by omega
          exact Nat.lt_trans hwSub hg)) :
    evalWireOf (appendCircuit C₁ C₂) x
      (by simpa [appendCircuit] using Nat.add_lt_add_left hg C₁.gates)
      (liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := g) w) recA =
    evalWireOf C₂ x hg w recB := by
  have hLiftOut :
      ¬ (((liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := g) w :
          Fin (n + (C₁.gates + g))) : Nat) < n) :=
    (liftWire_is_input (n := n) (g₁ := C₁.gates) (g₂ := g) (w := w)).not.mpr hw
  have hLiftSub :
      (((liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := g) w :
          Fin (n + (C₁.gates + g))) : Nat) - n) = C₁.gates + ((w : Nat) - n) :=
    liftWire_sub_n_gate (n := n) (g₁ := C₁.gates) (g₂ := g) (w := w) hw
  unfold evalWireOf
  simp [hLiftOut, hw, hLiftSub, hRec]

/--
Unified append-right wire bridge for lifted suffix wires.

Compared to the branch-specialized lemmas above, this wrapper takes the
gate-branch equality as a function of `¬ (w:Nat) < n` and performs the case
split internally.
-/
lemma evalWireOf_liftWire_right
    {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (hg : g < C₂.gates) (w : Fin (n + g))
    (recA : ∀ j : Nat, j < C₁.gates + g → j < (appendCircuit C₁ C₂).gates → Bool)
    (recB : ∀ j : Nat, j < g → j < C₂.gates → Bool)
    (hRecGate : ∀ (hw : ¬ (w : Nat) < n),
      recA (C₁.gates + ((w : Nat) - n))
        (Nat.add_lt_add_left (wire_sub_lt_of_not_input (w := w) hw) C₁.gates)
        (by
          have hwSub2 : (w : Nat) - n < C₂.gates := wire_sub_lt_suffix C₂ hg w hw
          simpa [appendCircuit] using Nat.add_lt_add_left hwSub2 C₁.gates)
      =
      recB ((w : Nat) - n)
        (wire_sub_lt_of_not_input (w := w) hw)
        (wire_sub_lt_suffix C₂ hg w hw)) :
    evalWireOf (appendCircuit C₁ C₂) x
      (by simpa [appendCircuit] using Nat.add_lt_add_left hg C₁.gates)
      (liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := g) w) recA =
    evalWireOf C₂ x hg w recB := by
  by_cases hw : (w : Nat) < n
  · exact evalWireOf_liftWire_input C₁ C₂ x hg w hw recA recB
  · have hRec :
      recA (C₁.gates + ((w : Nat) - n))
        (by
          exact Nat.add_lt_add_left (wire_sub_lt_of_not_input (w := w) hw) C₁.gates)
        (by
          have hwSub2 : (w : Nat) - n < C₂.gates := wire_sub_lt_suffix C₂ hg w hw
          simpa [appendCircuit] using Nat.add_lt_add_left hwSub2 C₁.gates)
      = recB ((w : Nat) - n)
        (wire_sub_lt_of_not_input (w := w) hw)
        (wire_sub_lt_suffix C₂ hg w hw) :=
      hRecGate hw
    exact evalWireOf_liftWire_gate C₁ C₂ x hg w hw recA recB hRec

/-- One-gate circuit returning a constant bit. -/
def constCircuit (n : Nat) (b : Bool) : Circuit n where
  gates := 1
  gate := fun _ => .const b
  output := ⟨n, by
    have : n < n + 1 := Nat.lt_succ_self n
    simpa [Nat.add_comm] using this⟩

/-- One-gate circuit with irrelevant dummy output, used as input carrier. -/
def inputCarrier (n : Nat) : Circuit n :=
  constCircuit n false

/-- Compile a tree circuit into a straight-line circuit with an explicit output wire. -/
noncomputable def compileTree : Boolcube.Circuit n → Compiled n
  | .var i =>
      { ckt := inputCarrier n
        out := ⟨i, by
          have hi : (i : Nat) < n := i.isLt
          have : n ≤ n + (inputCarrier n).gates := Nat.le_add_right n (inputCarrier n).gates
          exact Nat.lt_of_lt_of_le hi this⟩ }
  | .const b =>
      { ckt := constCircuit n b
        out := ⟨n, by
          have : n < n + (constCircuit n b).gates := by
            simpa [constCircuit] using Nat.lt_succ_self n
          exact this⟩ }
  | .not c =>
      let cc := compileTree c
      let ckt' := snoc cc.ckt (.not cc.out)
      { ckt := ckt'
        out := Fin.last (n + cc.ckt.gates) }
  | .and c1 c2 =>
      let cc1 := compileTree c1
      let cc2 := compileTree c2
      let merged := appendCircuit cc1.ckt cc2.ckt
      let out1 := leftWireInAppend cc1.ckt cc2.ckt cc1.out
      let out2 := liftWireIntoAppend (n := n) (g₁ := cc1.ckt.gates) (g₂ := cc2.ckt.gates) cc2.out
      let ckt' := snoc merged (.and out1 out2)
      { ckt := ckt'
        out := Fin.last (n + merged.gates) }
  | .or c1 c2 =>
      let cc1 := compileTree c1
      let cc2 := compileTree c2
      let merged := appendCircuit cc1.ckt cc2.ckt
      let out1 := leftWireInAppend cc1.ckt cc2.ckt cc1.out
      let out2 := liftWireIntoAppend (n := n) (g₁ := cc1.ckt.gates) (g₂ := cc2.ckt.gates) cc2.out
      let ckt' := snoc merged (.or out1 out2)
      { ckt := ckt'
        out := Fin.last (n + merged.gates) }

/-- Compile a tree circuit with output redirected to the compiled output wire. -/
noncomputable def compileTreeCircuit (c : Boolcube.Circuit n) : Circuit n :=
  let cc := compileTree c
  { cc.ckt with output := cc.out }

@[simp] lemma eval_constCircuit (n : Nat) (b : Bool) (x : Boolcube.Point n) :
    eval (constCircuit n b) x = b := by
  have hgate := evalWireInternal_gate (C := constCircuit n b) (x := x) (j := 0)
    (by simp [constCircuit])
  have hout :
      (constCircuit n b).output =
        ⟨n, by
          have : n < n + (constCircuit n b).gates := by
            simp [constCircuit]
          exact this⟩ := rfl
  have hEvalWire :
      evalWire (C := constCircuit n b) (x := x) (constCircuit n b).output = b := by
    simpa [evalWire, constCircuit, Nat.add_assoc] using hgate
  simpa [eval_eq_evalWire] using hEvalWire

@[simp] lemma eval_inputCarrier (n : Nat) (x : Boolcube.Point n) :
    eval (inputCarrier n) x = false := by
  simpa [inputCarrier] using eval_constCircuit n false x

@[simp] lemma evalWire_compileTree_var
    {n : Nat} (i : Fin n) (x : Boolcube.Point n) :
    evalWire (C := (compileTree (Boolcube.Circuit.var i)).ckt) (x := x)
      (compileTree (Boolcube.Circuit.var i)).out = x i := by
  dsimp [compileTree, inputCarrier, constCircuit]
  simp [evalWire, evalWireInternal]

@[simp] lemma evalWire_compileTree_const
    {n : Nat} (b : Bool) (x : Boolcube.Point n) :
    evalWire (C := (compileTree (Boolcube.Circuit.const b)).ckt) (x := x)
      (compileTree (Boolcube.Circuit.const b)).out = b := by
  dsimp [compileTree]
  have h := evalWireInternal_gate (C := constCircuit n b) (x := x) (j := 0)
    (by simp [constCircuit])
  simpa [evalWire] using h

/-- Pack a finite family of tree circuits into one shared straight-line circuit. -/
noncomputable def packFin (m : Nat) (f : Fin m → Boolcube.Circuit n) : CompiledFin n m := by
  induction m with
  | zero =>
      exact {
        ckt := inputCarrier n
        out := fun i => Fin.elim0 i
      }
  | succ m ih =>
      let pref : CompiledFin n m := ih (fun i => f (Fin.castLT i (Nat.lt_trans i.isLt (Nat.lt_succ_self m))))
      let lastCompiled : Compiled n := compileTree (f (Fin.last m))
      let merged : Circuit n := appendCircuit pref.ckt lastCompiled.ckt
      let lastOut : Fin (n + merged.gates) :=
        liftWireIntoAppend (n := n) (g₁ := pref.ckt.gates) (g₂ := lastCompiled.ckt.gates) lastCompiled.out
      refine {
        ckt := merged
        out := ?_
      }
      intro i
      by_cases hi : (i : Nat) < m
      · let i' : Fin m := ⟨i, hi⟩
        exact leftWireInAppend pref.ckt lastCompiled.ckt (pref.out i')
      · have hiEq : (i : Nat) = m := by
          have hle : m ≤ (i : Nat) := Nat.le_of_not_gt hi
          have hlt : (i : Nat) < m + 1 := i.isLt
          omega
        exact lastOut

/-- Contract: compiled output wire computes the source tree circuit semantics. -/
def CompileTreeWireSemantics : Prop :=
  ∀ {n : Nat} (c : Boolcube.Circuit n) (x : Boolcube.Point n),
    evalWire (C := (compileTree c).ckt) (x := x) (compileTree c).out =
      Boolcube.Circuit.eval c x

/-- Contract: packed family preserves semantics at every index. -/
def PackFinWireSemantics : Prop :=
  ∀ {n m : Nat} (f : Fin m → Boolcube.Circuit n) (x : Boolcube.Point n) (i : Fin m),
    evalWire (C := (packFin (n := n) (m := m) f).ckt) (x := x)
      ((packFin (n := n) (m := m) f).out i) =
        Boolcube.Circuit.eval (f i) x

/-- Contract: append/renumbering preserves source-wire semantics. -/
def AppendWireSemantics : Prop :=
  (∀ {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n) (i : Fin (n + C₁.gates)),
      evalWire (C := appendCircuit C₁ C₂) (x := x) (leftWireInAppend C₁ C₂ i) =
        evalWire (C := C₁) (x := x) i) ∧
  (∀ {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n) (i : Fin (n + C₂.gates)),
      evalWire (C := appendCircuit C₁ C₂) (x := x)
          (liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) i) =
        evalWire (C := C₂) (x := x) i)

/-- Right-branch index normalization for `appendCircuit` gate lookup. -/
@[simp] lemma cast_gateIdx_append_right
    {n : Nat} {C₁ C₂ : Circuit n} {g : Nat}
    (hg : g < C₁.gates + C₂.gates) (h_not_left : ¬ g < C₁.gates) :
    g - C₁.gates < C₂.gates := by
  omega

/--
Normalized right-branch index in `appendCircuit`: if `g` is in the suffix part,
then `g = C₁.gates + (g - C₁.gates)`.

This is a dedicated arithmetic normal form used to keep append-right proofs
stable under dependent index casts.
-/
lemma append_right_index_normalize
    {n : Nat} {C₁ C₂ : Circuit n} {g : Nat}
    (_hg : g < C₁.gates + C₂.gates) (h_not_left : ¬ g < C₁.gates) :
    g = C₁.gates + (g - C₁.gates) := by
  omega

/--
Right-branch gate index shifted by prefix gates is below append gate budget.

This avoids repeated `simpa [appendCircuit]` boilerplate at call sites.
-/
lemma append_right_shift_lt
    {n : Nat} {C₁ C₂ : Circuit n} {j : Nat}
    (hj : j < C₂.gates) :
    C₁.gates + j < (appendCircuit C₁ C₂).gates := by
  simpa [appendCircuit] using Nat.add_lt_add_left hj C₁.gates

/-- Right-branch additive index is never in the left prefix. -/
lemma append_right_not_left_add
    {n : Nat} {C₁ C₂ : Circuit n} {j : Nat}
    (_hj : j < C₂.gates) :
    ¬ C₁.gates + j < C₁.gates := by
  omega

/--
`cast_gateIdx_append_right` specialized to additive right-branch indices.

This is the canonical transport shape used in append-right gate proofs.
-/
lemma cast_gateIdx_append_right_add
    {n : Nat} {C₁ C₂ : Circuit n} {j : Nat}
    (hj : j < C₂.gates) :
    (C₁.gates + j) - C₁.gates < C₂.gates := by
  exact cast_gateIdx_append_right
    (C₁ := C₁) (C₂ := C₂)
    (g := C₁.gates + j)
    (append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj)
    (append_right_not_left_add (C₁ := C₁) (C₂ := C₂) (j := j) hj)

/-- Additive right-branch subtraction normal form for append indices. -/
@[simp] lemma append_right_sub_add_cancel
    {n : Nat} {C₁ C₂ : Circuit n} {j : Nat}
    (_hj : j < C₂.gates) :
    (C₁.gates + j) - C₁.gates = j := by
  omega

/--
Auxiliary contract: right-branch `appendCircuit` gate semantics agrees with the
suffix circuit at every suffix gate index.

This is the exact gate-level obligation needed to derive
`AppendWireSemantics` for the lifted-right wire branch.
-/
def AppendGateRightSemantics : Prop :=
  ∀ {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n)
      {j : Nat} (hj : j < C₂.gates),
    evalGateAux (appendCircuit C₁ C₂) x
        (append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj) =
      evalGateAux C₂ x hj

/--
Arithmetic cancellation for right-branch gate indices in `appendCircuit`.

This tiny normalization is used when rewriting goals of the form
`(C₁.gates + g) - C₁.gates` that appear after unfolding `liftOpIntoAppend`
on the suffix branch.
-/
@[simp] lemma append_right_cancel_sub
    {n : Nat} {C₁ : Circuit n} {g : Nat} :
    (C₁.gates + g) - C₁.gates = g := by
  omega

/--
When a gate index is in the suffix part of `appendCircuit`, `gate` unfolds to
the lifted gate from `C₂` at normalized index `g - C₁.gates`.
-/
lemma append_gate_right_eq
    {n : Nat} {C₁ C₂ : Circuit n} {g : Nat}
    (hg : g < C₁.gates + C₂.gates) (h_not_left : ¬ g < C₁.gates) :
    (appendCircuit C₁ C₂).gate ⟨g, hg⟩ =
      cast (by
        have hnorm : C₁.gates + (g - C₁.gates) = g := by
          omega
        simp [hnorm])
        (liftOpIntoAppend (n := n) (g₁ := C₁.gates) (g := (g - C₁.gates))
          (C₂.gate ⟨g - C₁.gates, cast_gateIdx_append_right hg h_not_left⟩)) := by
  unfold appendCircuit
  simp [h_not_left]

/--
Rephrase `append_gate_right_eq` so the cast target uses the normalized index
equation from `append_right_index_normalize` explicitly.
-/
lemma append_gate_right_eq_normalized
    {n : Nat} {C₁ C₂ : Circuit n} {g : Nat}
    (hg : g < C₁.gates + C₂.gates) (h_not_left : ¬ g < C₁.gates) :
    (appendCircuit C₁ C₂).gate ⟨g, hg⟩ =
      cast (by
        have hnorm : C₁.gates + (g - C₁.gates) = g :=
          (append_right_index_normalize (C₁ := C₁) (C₂ := C₂)
            (g := g) hg h_not_left).symm
        simp [hnorm])
        (liftOpIntoAppend (n := n) (g₁ := C₁.gates) (g := (g - C₁.gates))
          (C₂.gate ⟨g - C₁.gates, cast_gateIdx_append_right hg h_not_left⟩)) := by
  simpa using append_gate_right_eq (C₁ := C₁) (C₂ := C₂) (g := g) hg h_not_left

/--
Specialized right-branch gate normalization at the concrete shifted index
`C₁.gates + j`.

The statement is intentionally value-normalized (`(C₁.gates + j) - C₁.gates`)
to expose the exact subtraction term that appears in dependent goals.
-/
lemma append_gate_right_eq_add
    {n : Nat} {C₁ C₂ : Circuit n} {j : Nat}
    (hj : j < C₂.gates) :
    (appendCircuit C₁ C₂).gate
      ⟨C₁.gates + j, append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj⟩ =
      cast (by
        have hnorm : C₁.gates + ((C₁.gates + j) - C₁.gates) = C₁.gates + j := by
          omega
        simp [hnorm])
      (liftOpIntoAppend (n := n) (g₁ := C₁.gates) (g := ((C₁.gates + j) - C₁.gates))
        (C₂.gate
          ⟨(C₁.gates + j) - C₁.gates,
            cast_gateIdx_append_right
              (append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj)
              (append_right_not_left_add (C₁ := C₁) (C₂ := C₂) (j := j) hj)⟩)) := by
  exact append_gate_right_eq
    (C₁ := C₁) (C₂ := C₂) (g := C₁.gates + j)
    (append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj)
    (append_right_not_left_add (C₁ := C₁) (C₂ := C₂) (j := j) hj)

/--
Normalized suffix gate index in `Fin C₂.gates` for the concrete shifted index
`C₁.gates + j`.
-/
lemma append_gate_right_finIdx_eq
    {n : Nat} {C₁ C₂ : Circuit n} {j : Nat}
    (hj : j < C₂.gates) :
    (⟨(C₁.gates + j) - C₁.gates,
      cast_gateIdx_append_right
        (append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj)
        (append_right_not_left_add (C₁ := C₁) (C₂ := C₂) (j := j) hj)⟩ :
      Fin C₂.gates) =
    ⟨j, hj⟩ := by
  apply Fin.ext
  simp [append_right_sub_add_cancel (C₁ := C₁) (C₂ := C₂) (j := j) hj]

/--
Cast-eliminator for `evalWireOf`: once the domain-size equality is rewritten by
`subst`, both sides are definitionally equal.

This is a small but important helper for dependent-`Fin` transport-heavy
proofs in append/right branches.
-/
@[simp] lemma evalWireOf_cast
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (hg : g < C.gates)
    (m : Nat) (hEq : m = n + g) (i : Fin m) :
    evalWireOf C x hg (Fin.cast hEq i)
      (fun j _ hj' => evalGateAux C x hj') =
    evalWireOf C x hg (Fin.cast (by simpa [hEq]) i)
      (fun j _ hj' => evalGateAux C x hj') := by
  subst hEq
  rfl

/-- Cast-eliminator twin for `toCircuitWireOf`. -/
@[simp] lemma toCircuitWireOf_cast
    {n : Nat} (C : Circuit n)
    {g : Nat} (hg : g < C.gates)
    (m : Nat) (hEq : m = n + g) (i : Fin m) :
    toCircuitWireOf C hg (Fin.cast hEq i)
      (fun j _ hj' => toCircuitGateAux C hj') =
    toCircuitWireOf C hg (Fin.cast (by simpa [hEq]) i)
      (fun j _ hj' => toCircuitGateAux C hj') := by
  subst hEq
  rfl

/--
`evalWireAux` is proof-irrelevant in its bound proof argument.

This helper removes dependent noise when arithmetic normalizations produce
extensionally equal but non-definitional `≤` witnesses.
-/
@[simp] lemma evalWireAux_proof_irrel
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (h₁ h₂ : g ≤ C.gates) (i : Fin (n + g)) :
    evalWireAux C x g h₁ i = evalWireAux C x g h₂ i := by
  cases proof_irrel_heq h₁ h₂
  rfl

/--
`evalGateAux` is proof-irrelevant in its gate-bound witness.
-/
@[simp] lemma evalGateAux_proof_irrel
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (h₁ h₂ : g < C.gates) :
    evalGateAux C x h₁ = evalGateAux C x h₂ := by
  cases proof_irrel_heq h₁ h₂
  rfl

mutual
  lemma evalWireAux_append_left (C₁ C₂ : Circuit n) (x : Boolcube.Point n) :
      ∀ {g : Nat} (hg : g ≤ C₁.gates) (i : Fin (n + g)),
        evalWireAux (appendCircuit C₁ C₂) x g
            (Nat.le_trans hg (Nat.le_add_right _ _)) i =
          evalWireAux C₁ x g hg i
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
          have hj_gate : j < C₁.gates := Nat.lt_of_lt_of_le hj_lt hg
          have ihGate := evalGateAux_append_left C₁ C₂ x (g := j) hj_gate
          unfold evalWireAux
          simp only [hInput]
          exact ihGate

  lemma evalGateAux_append_left (C₁ C₂ : Circuit n) (x : Boolcube.Point n) :
      ∀ {g : Nat} (hg : g < C₁.gates),
        evalGateAux (appendCircuit C₁ C₂) x
            (Nat.lt_of_lt_of_le hg (Nat.le_add_right _ _)) =
          evalGateAux C₁ x hg
    | g, hg => by
        have hgate :
            (appendCircuit C₁ C₂).gate
              ⟨g, Nat.lt_of_lt_of_le hg (Nat.le_add_right _ _)⟩ =
              C₁.gate ⟨g, hg⟩ := by
          simp [appendCircuit, hg]
        cases hOp : C₁.gate ⟨g, hg⟩ with
        | const b =>
            simp [evalGateAux, hgate, hOp]
        | not u =>
            have hu := evalWireAux_append_left C₁ C₂ x
              (g := g) (hg := Nat.le_of_lt hg) u
            simpa [evalGateAux, hgate, hOp] using congrArg (fun t => !t) hu
        | and u v =>
            have hu := evalWireAux_append_left C₁ C₂ x
              (g := g) (hg := Nat.le_of_lt hg) u
            have hv := evalWireAux_append_left C₁ C₂ x
              (g := g) (hg := Nat.le_of_lt hg) v
            simpa [evalGateAux, hgate, hOp, hu, hv]
        | or u v =>
            have hu := evalWireAux_append_left C₁ C₂ x
              (g := g) (hg := Nat.le_of_lt hg) u
            have hv := evalWireAux_append_left C₁ C₂ x
              (g := g) (hg := Nat.le_of_lt hg) v
            simpa [evalGateAux, hgate, hOp, hu, hv]
end

lemma appendWireSemantics_left :
    ∀ {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n) (i : Fin (n + C₁.gates)),
      evalWire (C := appendCircuit C₁ C₂) (x := x) (leftWireInAppend C₁ C₂ i) =
        evalWire (C := C₁) (x := x) i := by
  intro n C₁ C₂ x i
  unfold evalWire evalWireInternal
  have hval :
      ((leftWireInAppend C₁ C₂ i : Fin (n + (C₁.gates + C₂.gates))) : Nat) = i := by
    simpa using leftWireInAppend_val (C₁ := C₁) (C₂ := C₂) i
  by_cases hIn : (i : Nat) < n
  · have hInL : ((leftWireInAppend C₁ C₂ i : Fin (n + (C₁.gates + C₂.gates))) : Nat) < n := by
      simpa [hval] using hIn
    simp [hIn, hInL]
  · have hInL : ¬ ((leftWireInAppend C₁ C₂ i : Fin (n + (C₁.gates + C₂.gates))) : Nat) < n := by
      simpa [hval] using hIn
    let j : Nat := (i : Nat) - n
    have hj : j < C₁.gates := by
      have hi : (i : Nat) < n + C₁.gates := i.isLt
      dsimp [j] at *
      omega
    have hjL : j < C₁.gates + C₂.gates := by
      exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
    have hGate :
        evalGateAux (appendCircuit C₁ C₂) x hjL = evalGateAux C₁ x hj := by
      exact evalGateAux_append_left C₁ C₂ x (g := j) hj
    simp [hIn, hInL, hval, j, hj, hjL, hGate]

/--
Right append semantics reduced to a gate-level contract on suffix gates.

This isolates the remaining hard part (`evalGateAux` on the append-right
branch) behind a local assumption `hGate`, so downstream assembly can use this
lemma as soon as that gate-level theorem is available.
-/
lemma appendWireSemantics_right_of_gate
    {n : Nat} (C₁ C₂ : Circuit n) (x : Boolcube.Point n)
    (hGate : ∀ {j : Nat} (hj : j < C₂.gates),
      evalGateAux (appendCircuit C₁ C₂) x
          (append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj) =
        evalGateAux C₂ x hj) :
    ∀ (i : Fin (n + C₂.gates)),
      evalWire (C := appendCircuit C₁ C₂) (x := x)
        (liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) i) =
      evalWire (C := C₂) (x := x) i := by
  intro i
  unfold evalWire evalWireInternal
  by_cases hIn : (i : Nat) < n
  · have hInLift :
      (((liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) i :
          Fin (n + (C₁.gates + C₂.gates))) : Nat) < n) :=
      (liftWire_is_input (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) (w := i)).2 hIn
    simpa [hIn, hInLift] using
      point_eval_liftWire_input (x := x) (g₁ := C₁.gates) (g₂ := C₂.gates) (w := i) hIn
  · have hInLift :
      ¬ (((liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) i :
            Fin (n + (C₁.gates + C₂.gates))) : Nat) < n) :=
      (liftWire_is_input (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) (w := i)).not.mpr hIn
    let j : Nat := (i : Nat) - n
    have hj : j < C₂.gates := by
      have hi : (i : Nat) < n + C₂.gates := i.isLt
      dsimp [j] at *
      omega
    have hLiftSub :
        (((liftWireIntoAppend (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) i :
          Fin (n + (C₁.gates + C₂.gates))) : Nat) - n) = C₁.gates + j := by
      simpa [j] using
        liftWire_sub_n_gate (n := n) (g₁ := C₁.gates) (g₂ := C₂.gates) (w := i) hIn
    have hGate' :
        evalGateAux (appendCircuit C₁ C₂) x
          (by
            have hjA : C₁.gates + j < (appendCircuit C₁ C₂).gates :=
              append_right_shift_lt (C₁ := C₁) (C₂ := C₂) (j := j) hj
            simpa [hLiftSub] using hjA)
        = evalGateAux C₂ x hj := by
      simpa using hGate (j := j) hj
    simp [hIn, hInLift, j, hj, hLiftSub, hGate']

/--
Assemble full `AppendWireSemantics` from:
1) the already-proved left-branch theorem; and
2) a global right-branch gate-level contract.
-/
theorem appendWireSemantics_of_gateContracts
    (hGate : AppendGateRightSemantics) :
    AppendWireSemantics := by
  refine ⟨appendWireSemantics_left, ?_⟩
  intro n C₁ C₂ x i
  exact appendWireSemantics_right_of_gate C₁ C₂ x (hGate (C₁ := C₁) (C₂ := C₂) (x := x)) i

/--
Compile-tree semantic correctness assembled from append-wire semantics.

The only non-trivial constructor cases (`and`/`or`) require append transport;
the base cases and `not` use direct `snoc`/induction reasoning.
-/
theorem compileTreeWireSemantics_of_append
    (hAppend : AppendWireSemantics) :
    CompileTreeWireSemantics := by
  intro n c
  induction c with
  | var i =>
      intro x
      simpa [Boolcube.Circuit.eval] using evalWire_compileTree_var (i := i) (x := x)
  | const b =>
      intro x
      simpa [Boolcube.Circuit.eval] using evalWire_compileTree_const (b := b) (x := x)
  | not c ih =>
      intro x
      dsimp [compileTree]
      have hLast := evalWire_snoc_last
        (C := (compileTree c).ckt) (op := .not (compileTree c).out) (x := x)
      simpa [Boolcube.Circuit.eval, ih x] using hLast
  | and c1 c2 ih1 ih2 =>
      intro x
      rcases hAppend with ⟨hLeft, hRight⟩
      dsimp [compileTree]
      set cc1 : Compiled n := compileTree c1
      set cc2 : Compiled n := compileTree c2
      set merged : Circuit n := appendCircuit cc1.ckt cc2.ckt
      set out1 : Fin (n + merged.gates) := leftWireInAppend cc1.ckt cc2.ckt cc1.out
      set out2 : Fin (n + merged.gates) :=
        liftWireIntoAppend (n := n) (g₁ := cc1.ckt.gates) (g₂ := cc2.ckt.gates) cc2.out
      have hL : evalWire (C := merged) (x := x) out1 = evalWire (C := cc1.ckt) (x := x) cc1.out := by
        simpa [merged, out1] using hLeft cc1.ckt cc2.ckt x cc1.out
      have hR : evalWire (C := merged) (x := x) out2 = evalWire (C := cc2.ckt) (x := x) cc2.out := by
        simpa [merged, out2] using hRight cc1.ckt cc2.ckt x cc2.out
      have hLast := evalWire_snoc_last (C := merged) (op := .and out1 out2) (x := x)
      simpa [Boolcube.Circuit.eval, cc1, cc2, merged, out1, out2, ih1 x, ih2 x, hL, hR] using hLast
  | or c1 c2 ih1 ih2 =>
      intro x
      rcases hAppend with ⟨hLeft, hRight⟩
      dsimp [compileTree]
      set cc1 : Compiled n := compileTree c1
      set cc2 : Compiled n := compileTree c2
      set merged : Circuit n := appendCircuit cc1.ckt cc2.ckt
      set out1 : Fin (n + merged.gates) := leftWireInAppend cc1.ckt cc2.ckt cc1.out
      set out2 : Fin (n + merged.gates) :=
        liftWireIntoAppend (n := n) (g₁ := cc1.ckt.gates) (g₂ := cc2.ckt.gates) cc2.out
      have hL : evalWire (C := merged) (x := x) out1 = evalWire (C := cc1.ckt) (x := x) cc1.out := by
        simpa [merged, out1] using hLeft cc1.ckt cc2.ckt x cc1.out
      have hR : evalWire (C := merged) (x := x) out2 = evalWire (C := cc2.ckt) (x := x) cc2.out := by
        simpa [merged, out2] using hRight cc1.ckt cc2.ckt x cc2.out
      have hLast := evalWire_snoc_last (C := merged) (op := .or out1 out2) (x := x)
      simpa [Boolcube.Circuit.eval, cc1, cc2, merged, out1, out2, ih1 x, ih2 x, hL, hR] using hLast

/--
Compile-tree semantics from the gate-level append-right contract.

This theorem closes both layers internally:
1) build `AppendWireSemantics` from `AppendGateRightSemantics`; then
2) derive `CompileTreeWireSemantics` from append correctness.
-/
theorem compileTreeWireSemantics_of_gateContracts
    (hGate : AppendGateRightSemantics) :
    CompileTreeWireSemantics :=
  compileTreeWireSemantics_of_append (appendWireSemantics_of_gateContracts hGate)


theorem packFinWireSemantics_of_contracts
    (hCompile : CompileTreeWireSemantics)
    (hAppend : AppendWireSemantics) :
    PackFinWireSemantics := by
  intro n m f x i
  induction m with
  | zero =>
      exact Fin.elim0 i
  | succ m ih =>
      classical
      let fPref : Fin m → Boolcube.Circuit n := fun j =>
        f (Fin.castLT j (Nat.lt_trans j.isLt (Nat.lt_succ_self m)))
      let pref : CompiledFin n m := packFin (n := n) (m := m) fPref
      let lastCompiled : Compiled n := compileTree (f (Fin.last m))
      let merged : Circuit n := appendCircuit pref.ckt lastCompiled.ckt
      let lastOut : Fin (n + merged.gates) :=
        liftWireIntoAppend (n := n) (g₁ := pref.ckt.gates) (g₂ := lastCompiled.ckt.gates) lastCompiled.out
      rcases hAppend with ⟨hLeft, hRight⟩
      have hPref : ∀ j : Fin m,
          evalWire (C := pref.ckt) (x := x) (pref.out j) = Boolcube.Circuit.eval (fPref j) x :=
        by
          intro j
          exact ih fPref j
      unfold packFin
      simp [fPref, pref, lastCompiled, merged, lastOut]
      by_cases hi : (i : Nat) < m
      · let i' : Fin m := ⟨i, hi⟩
        let iUp : Fin (m + 1) := Fin.castLT i' (Nat.lt_trans i'.isLt (Nat.lt_succ_self m))
        have hL :
            evalWire (C := merged) (x := x)
              (leftWireInAppend pref.ckt lastCompiled.ckt (pref.out i')) =
              evalWire (C := pref.ckt) (x := x) (pref.out i') :=
          hLeft pref.ckt lastCompiled.ckt x (pref.out i')
        have hP : evalWire (C := pref.ckt) (x := x) (pref.out i') = Boolcube.Circuit.eval (f iUp) x := by
          simpa [fPref, i'] using hPref i'
        have hiUpEq : iUp = i := by
          ext
          rfl
        simpa [hi, i', iUp, hiUpEq] using hL.trans hP
      · have hiEq : (i : Nat) = m := by
          have hle : m ≤ (i : Nat) := Nat.le_of_not_gt hi
          have hlt : (i : Nat) < m + 1 := i.isLt
          omega
        have hR :
            evalWire (C := merged) (x := x) lastOut =
              evalWire (C := lastCompiled.ckt) (x := x) lastCompiled.out := by
          simpa [lastOut] using hRight pref.ckt lastCompiled.ckt x lastCompiled.out
        have hC :
            evalWire (C := lastCompiled.ckt) (x := x) lastCompiled.out =
              Boolcube.Circuit.eval (f (Fin.last m)) x :=
          hCompile (f (Fin.last m)) x
        have hiFin : i = Fin.last m := by
          ext
          simpa [hiEq]
        simpa [hi, hiEq, hiFin] using hR.trans hC

end StraightLine
end PsubsetPpoly
end Internal
end Pnp3
