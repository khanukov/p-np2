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
