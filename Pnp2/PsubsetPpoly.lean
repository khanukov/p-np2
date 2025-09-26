import Pnp2.ComplexityClasses
import Pnp2.Circuit.Family
import Pnp2.TM.Encoding

/--
`PsubsetPpoly.lean` develops the infrastructure required to replace the
axiomatic inclusion `P ⊆ P/poly` with a fully formal proof.  The file
currently focuses on the basic combinatorial gadgets used to translate a
Turing-machine computation into Boolean circuits.  Subsequent commits will
extend these constructions to complete the classical simulation argument.
-/

open Boolcube
open TM

open scoped BigOperators

namespace List

lemma any_map {α β} (l : List α) (f : α → β) (p : β → Bool) :
    List.any (l.map f) p = List.any l (fun a => p (f a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [List.map, List.any, ih]

lemma foldl_or_eq_any {α} (l : List α) (f : α → Bool) :
    l.foldl (fun acc x => acc || f x) false = List.any l f := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [List.any, ih, Bool.or_left_comm, Bool.or_assoc]

end List

namespace Complexity

/-- Cardinality of the control-state set of a machine.  The quantity is
treated as a compile-time constant for the purpose of size bounds. -/
def stateCard (M : TM) : ℕ := Fintype.card M.state

/-- The canonical equivalence between the state set and `Fin (stateCard M)`. -/
noncomputable def stateEquiv (M : TM) : M.state ≃ Fin (stateCard M) :=
  Fintype.equivFin _

/-- Index of a control state in the canonical enumeration. -/
noncomputable def stateIndex (M : TM) (q : M.state) : Fin (stateCard M) :=
  (stateEquiv M) q

/--
Boolean indicator for the current head position.  The encoding is compatible
with the circuit representation where each cell obtains its own Boolean
wire.
-/
def headIndicator {M : TM} {n : ℕ}
    (c : TM.Configuration M n) : Fin (M.tapeLength n) → Bool := fun i =>
  decide (c.head = i)

/-- Boolean indicator for the control state. -/
def stateIndicator (M : TM) {n : ℕ}
    (c : TM.Configuration M n) : Fin (stateCard M) → Bool := fun i =>
  decide (stateIndex M c.state = i)

lemma headIndicator_true_iff {M : TM} {n : ℕ}
    (c : TM.Configuration M n) (i : Fin (M.tapeLength n)) :
    headIndicator (M := M) (n := n) c i = true ↔ c.head = i := by
  classical
  unfold headIndicator
  by_cases h : c.head = i
  · simp [h]
  · simp [h] at *

lemma headIndicator_self {M : TM} {n : ℕ}
    (c : TM.Configuration M n) :
    headIndicator (M := M) (n := n) c c.head = true := by
  classical
  simpa using
    (headIndicator_true_iff (M := M) (n := n) c c.head)

lemma headIndicator_ne {M : TM} {n : ℕ}
    (c : TM.Configuration M n) {i : Fin (M.tapeLength n)}
    (h : i ≠ c.head) :
    headIndicator (M := M) (n := n) c i = false := by
  classical
  unfold headIndicator
  by_cases h' : c.head = i
  · have : i = c.head := by simpa [h', eq_comm]
    exact (False.elim (h this))
  · simp [h']

lemma stateIndicator_true_iff {M : TM} {n : ℕ}
    (c : TM.Configuration M n) (i : Fin (stateCard M)) :
    stateIndicator M (n := n) c i = true ↔ stateIndex M c.state = i := by
  classical
  unfold stateIndicator
  by_cases h : stateIndex M c.state = i
  · simp [h]
  · simp [h]

lemma stateIndicator_self {M : TM} {n : ℕ}
    (c : TM.Configuration M n) :
    stateIndicator M (n := n) c (stateIndex M c.state) = true := by
  classical
  simpa using
    (stateIndicator_true_iff (M := M) (n := n) c (stateIndex M c.state))

lemma stateIndicator_ne {M : TM} {n : ℕ}
    (c : TM.Configuration M n) {i : Fin (stateCard M)}
    (h : stateIndex M c.state ≠ i) :
    stateIndicator M (n := n) c i = false := by
  classical
  unfold stateIndicator
  by_cases h' : stateIndex M c.state = i
  · exact (False.elim (h h'))
  · simp [h']

/--
Circuits describing all bits of a configuration for inputs of length `n`.
We maintain one circuit per tape cell, one per head position and one per
control state (using a one-hot encoding).
-/
structure ConfigCircuits (M : TM) (n : ℕ) where
  tape : Fin (M.tapeLength n) → Circuit n
  head : Fin (M.tapeLength n) → Circuit n
  state : Fin (stateCard M) → Circuit n

namespace ConfigCircuits

variable {M : TM} {n : ℕ}

/-- Evaluation of tape circuits as Boolean vectors. -/
def evalTape (cc : ConfigCircuits M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool := fun i => Circuit.eval (cc.tape i) x

/-- Evaluation of head circuits. -/
def evalHead (cc : ConfigCircuits M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool := fun i => Circuit.eval (cc.head i) x

/-- Evaluation of state circuits. -/
def evalState (cc : ConfigCircuits M n) (x : Point n) :
    Fin (stateCard M) → Bool := fun i => Circuit.eval (cc.state i) x

/--
Correctness predicate relating circuits to a family of configurations.  The
parameter `f` associates to each input its concrete machine configuration. -/
structure Spec (cc : ConfigCircuits M n)
    (f : Point n → TM.Configuration M n) : Prop where
  tape_eq : ∀ x i, evalTape cc x i = (f x).tape i
  head_eq : ∀ x i, evalHead cc x i = headIndicator (f x) i
  state_eq : ∀ x i, evalState cc x i = stateIndicator M (f x) i

/--
Initial circuits encoding the start configuration of `M` on an input of
length `n`.
-/
noncomputable def initial (M : TM) (n : ℕ) : ConfigCircuits M n where
  tape := fun i =>
    if h : (i : ℕ) < n then
      Circuit.var ⟨i, h⟩
    else
      Circuit.const false
  head := fun i =>
    if h : i = ⟨0, by
          have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
          simpa [TM.tapeLength] using this⟩ then
      Circuit.const true
    else
      Circuit.const false
  state := fun i =>
    if h : i = stateIndex M M.start then
      Circuit.const true
    else
      Circuit.const false

/-- The initial circuits faithfully represent the machine's starting
configuration. -/
lemma initial_spec (M : TM) (n : ℕ) :
    Spec (M := M) (n := n) (initial (M := M) n)
      (fun x => M.initialConfig x) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    by_cases hi : (i : ℕ) < n
    · have : (M.initialConfig x).tape i = x ⟨i, hi⟩ :=
        TM.initial_tape_input (M := M) (x := x) (i := i) hi
      simp [initial, hi, this]
    · have hi' : n ≤ (i : ℕ) := not_lt.mp hi
      have : (M.initialConfig x).tape i = false :=
        TM.initial_tape_blank (M := M) (x := x) (i := i) hi'
      simp [initial, hi, this]
  · intro x i
    by_cases hi : i = ⟨0, by
        have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
        simpa [TM.tapeLength] using this⟩
    · subst hi
      have : (M.initialConfig x).head = ⟨0, by
          have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
          simpa [TM.tapeLength] using this⟩ := TM.initial_head (M := M) (x := x)
      simp [initial, headIndicator, this]
    · have : (M.initialConfig x).head ≠ i := by
        intro hcontr; apply hi; simpa [hcontr]
      simp [initial, headIndicator, hi, this]
  · intro x i
    by_cases hi : i = stateIndex M M.start
    · subst hi
      have : (M.initialConfig x).state = M.start := TM.initial_state (M := M) (x := x)
      simp [initial, stateIndicator, stateIndex, stateEquiv, this]
    · have : stateIndex M (M.initialConfig x).state ≠ i := by
        intro hcontr
        apply hi
        have : (M.initialConfig x).state = M.start :=
          TM.initial_state (M := M) (x := x)
        simpa [stateIndex, stateEquiv, this] using hcontr
      have hstate : (M.initialConfig x).state = M.start := TM.initial_state (M := M) (x := x)
      simp [initial, stateIndicator, hi, stateIndex, stateEquiv, hstate, this]

/--
Straight-line representation of configuration circuits.  The straight-line
model keeps a single pool of gates that subsequent layers can reuse via wire
references.  The tape, head and state projections simply identify which wires
encode the observable components of the configuration.
-/-
structure StraightConfig (M : TM) (n : ℕ) where
  circuit : StraightLineCircuit n
  tape : Fin (M.tapeLength n) → Fin (n + circuit.gates)
  head : Fin (M.tapeLength n) → Fin (n + circuit.gates)
  state : Fin (stateCard M) → Fin (n + circuit.gates)

namespace StraightConfig

variable {M : TM} {n : ℕ}

open Boolcube
open StraightLineCircuit

/-- Evaluate the tape portion of a straight-line configuration. -/
def evalTape (sc : StraightConfig M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool :=
  fun i => StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.tape i)

/-- Evaluate the head-indicator portion of a straight-line configuration. -/
def evalHead (sc : StraightConfig M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool :=
  fun i => StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.head i)

/-- Evaluate the state-indicator portion of a straight-line configuration. -/
def evalState (sc : StraightConfig M n) (x : Point n) :
    Fin (stateCard M) → Bool :=
  fun i => StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.state i)

/--
Specification predicate connecting a straight-line configuration to a concrete
machine configuration.  The statement mirrors `ConfigCircuits.Spec` but operates
on `StraightLineCircuit` evaluations.
-/-
structure Spec (sc : StraightConfig M n)
    (f : Point n → TM.Configuration M n) : Prop where
  tape_eq : ∀ x i, evalTape sc x i = (f x).tape i
  head_eq : ∀ x i, evalHead sc x i = headIndicator (f x) i
  state_eq : ∀ x i, evalState sc x i = stateIndicator M (f x) i

/--
Straight-line circuit consisting of a single constant gate.  The designated
output wire points to the newly created gate, providing a convenient source of
Boolean literals that later constructions can reuse.
-/-
@[simp] def constCircuit (n : ℕ) (b : Bool) : StraightLineCircuit n :=
  { gates := 1
    , gate := fun g =>
        match g with
        | ⟨0, _⟩ => StraightOp.const b
    , output := Fin.last (n + 1) }

@[simp] lemma eval_constCircuit (n : ℕ) (b : Bool) (x : Point n) :
    StraightLineCircuit.eval (constCircuit (n := n) b) x = b := by
  -- Evaluating the unique gate simply returns the stored constant.
  simp [constCircuit, StraightLineCircuit.eval, StraightLineCircuit.evalWireAux,
    StraightLineCircuit.evalGateAux]

/--
Initial straight-line configuration encoding the start configuration of `M` on
inputs of length `n`.  The construction introduces two reusable constant gates
(`false` and `true`) that subsequent layers may reference without adding new
gates.
-/-
def initial (M : TM) (n : ℕ) : StraightConfig M n :=
  let base := constCircuit (n := n) false
  let circuit := StraightLineCircuit.snoc base (StraightOp.const true)
  let falseWire := StraightLineCircuit.liftWire (C := base) base.output
  let trueWire : Fin (n + circuit.gates) := Fin.last _
  { circuit
    , tape := fun i =>
        if hi : (i : ℕ) < n then
          -- Positions inside the input prefix forward the corresponding input.
          ⟨(i : ℕ), Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)⟩
        else
          -- Cells beyond the input prefix start as blanks.
          falseWire
    , head := fun i =>
        if hi : i = ⟨0, by
              -- The tape length is at least one cell (`n + T(n) + 1`).
              have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
              simpa [TM.tapeLength] using this⟩ then
          trueWire
        else
          falseWire
    , state := fun i =>
        if hi : i = stateIndex M M.start then
          trueWire
        else
          falseWire }

/--
The straight-line initial configuration evaluates to the genuine machine start
configuration.
-/-
lemma initial_spec (M : TM) (n : ℕ) :
    Spec (M := M) (n := n) (initial (M := M) n)
      (fun x => M.initialConfig x) := by
  classical
  -- Unfold the definition to expose the helper bindings.
  unfold initial
  set base := constCircuit (n := n) false
  set circuit := StraightLineCircuit.snoc base (StraightOp.const true)
  set falseWire := StraightLineCircuit.liftWire (C := base) base.output
  set trueWire : Fin (n + circuit.gates) := Fin.last _
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    by_cases hi : (i : ℕ) < n
    · -- Inside the input prefix the circuit simply forwards the input bit.
      simp [evalTape, evalHead, evalState, hi, StraightLineCircuit.evalWire_input,
        TM.initial_tape_input (M := M) (x := x) (i := i) hi]
    · -- Beyond the input prefix the circuit resorts to the cached `false` gate.
      have hfalseBase : StraightLineCircuit.evalWire (C := base) (x := x)
          base.output = false := by
        simpa [StraightLineCircuit.eval_eq_evalWire]
          using eval_constCircuit (n := n) (b := false) (x := x)
      have hfalse : StraightLineCircuit.evalWire (C := circuit) (x := x)
          falseWire = false := by
        simpa [falseWire, circuit, StraightLineCircuit.evalWire_snoc_lift]
          using hfalseBase
      have hi' : ¬ (i : ℕ) < n := hi
      have : (M.initialConfig x).tape i = false :=
        TM.initial_tape_blank (M := M) (x := x) (i := i) (Nat.le_of_not_lt hi')
      simp [evalTape, evalHead, evalState, hi, hfalse, this]
  · intro x i
    by_cases hi : i = ⟨0, by
        have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
        simpa [TM.tapeLength] using this⟩
    · subst hi
      have htrueEval : StraightLineCircuit.eval (snoc (C := base) (StraightOp.const true)) x = true := by
        simpa [circuit, StraightOp.eval] using
          StraightLineCircuit.eval_snoc (C := base)
            (op := StraightOp.const true) (x := x)
      have htrue : StraightLineCircuit.evalWire (C := circuit) (x := x) trueWire = true := by
        simpa [trueWire, StraightLineCircuit.eval_eq_evalWire] using htrueEval
      have hhead := TM.initial_head (M := M) (x := x)
      simp [evalHead, evalTape, evalState, trueWire, falseWire,
        htrue, hhead, headIndicator]
    · have hfalseBase : StraightLineCircuit.evalWire (C := base) (x := x)
          base.output = false := by
        simpa [StraightLineCircuit.eval_eq_evalWire]
          using eval_constCircuit (n := n) (b := false) (x := x)
      have hfalse : StraightLineCircuit.evalWire (C := circuit) (x := x)
          falseWire = false := by
        simpa [falseWire, circuit, StraightLineCircuit.evalWire_snoc_lift]
          using hfalseBase
      have : headIndicator (M := M) (n := n) (M.initialConfig x) i = false := by
        have hi' : i ≠ ⟨0, by
            have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
            simpa [TM.tapeLength] using this⟩ := hi
        simp [headIndicator, TM.initial_head, hi']
      simp [evalHead, evalTape, evalState, hi, hfalse, this]
  · intro x i
    by_cases hi : i = stateIndex M M.start
    · subst hi
      have htrueEval : StraightLineCircuit.eval (snoc (C := base) (StraightOp.const true)) x = true := by
        simpa [circuit, StraightOp.eval] using
          StraightLineCircuit.eval_snoc (C := base)
            (op := StraightOp.const true) (x := x)
      have htrue : StraightLineCircuit.evalWire (C := circuit) (x := x) trueWire = true := by
        simpa [trueWire, StraightLineCircuit.eval_eq_evalWire] using htrueEval
      have hstate := TM.initial_state (M := M) (x := x)
      simp [evalState, evalTape, evalHead, htrue, hstate, stateIndicator,
        stateIndex, stateEquiv]
    · have hfalseBase : StraightLineCircuit.evalWire (C := base) (x := x)
          base.output = false := by
        simpa [StraightLineCircuit.eval_eq_evalWire]
          using eval_constCircuit (n := n) (b := false) (x := x)
      have hfalse : StraightLineCircuit.evalWire (C := circuit) (x := x)
          falseWire = false := by
        simpa [falseWire, circuit, StraightLineCircuit.evalWire_snoc_lift]
          using hfalseBase
      have hstate := TM.initial_state (M := M) (x := x)
      have : stateIndicator (M := M) (c := M.initialConfig x) i = false := by
        have hi' : i ≠ stateIndex M M.start := hi
        simp [stateIndicator, stateIndex, stateEquiv, hstate, hi']
      simp [evalState, evalTape, evalHead, hi, hfalse, this]

/--
Helper used in the construction of the symbol wire: given a current builder and
an accumulator wire computing the disjunction of the previously processed
entries, append the contribution of the next tape cell.
-/
def symbolBuilderStep (sc : StraightConfig M n) :
    (Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
        Fin (n + b.circuit.gates)) →
      Fin (M.tapeLength n) →
        Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
          Fin (n + b.circuit.gates)
  | ⟨b, acc⟩, i =>
      let head := b.liftBase (sc.head i)
      let tape := b.liftBase (sc.tape i)
      let andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := b) head tape
      let accLift := (StraightLineCircuit.EvalBuilder.appendFin_lift
        (b := b) (op := StraightOp.and head tape)) acc
      let orResult := StraightLineCircuit.EvalBuilder.appendOrFin
        (b := andResult.fst) accLift andResult.snd
      ⟨orResult.fst, orResult.snd⟩

/--
Build a wire computing the Boolean symbol currently scanned by the head.  The
construction iterates over all tape cells, successively accumulating the OR of
the conjunctions `head[i] ∧ tape[i]`.
-/
def symbolBuilder (sc : StraightConfig M n) :
    Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
      Fin (n + b.circuit.gates) :=
  let start := StraightLineCircuit.EvalBuilder.appendConstFin
    (b := StraightLineCircuit.EvalBuilder.mk sc.circuit) false
  let init : Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
      Fin (n + b.circuit.gates) := ⟨start.fst, start.snd⟩
  (tapeIndexList (M := M) n).foldl (fun acc i =>
      symbolBuilderStep (M := M) (n := n) sc acc i) init

/--
Token-based version of `symbolBuilder`.  The returned wire remembers the gate
count of the augmented circuit, making it convenient to transport across
further gate insertions without having to rebuild the index from scratch.
-/
def symbolBuilderWire (sc : StraightConfig M n) :
    Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
      StraightLineCircuit.Wire n :=
  let result := symbolBuilder (M := M) (n := n) sc
  ⟨ result.fst
  , StraightLineCircuit.Wire.ofFin (n := n)
      (g := result.fst.circuit.gates) result.snd ⟩

/--
Evaluation of the wire returned by `symbolBuilder`.  The result is the OR-fold
over all cells, matching the combinational definition of the scanned symbol.
-/
lemma symbolBuilder_eval (sc : StraightConfig M n) (x : Point n) :
    let result := symbolBuilder (M := M) (n := n) sc
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
      (tapeIndexList (M := M) n).foldl (fun acc i =>
        acc ||
          (StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.head i) &&
            StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.tape i)))
        false := by
  classical
  unfold symbolBuilder
  generalize hfold : (tapeIndexList (M := M) n) = cells
  revert sc
  induction cells with
  | nil =>
      intro sc
      simp [symbolBuilderStep]
  | cons i cells ih =>
      intro sc
      simp [symbolBuilderStep, List.foldl_cons, ih, Bool.or_assoc,
        Bool.or_left_comm, Bool.or_comm,
        StraightLineCircuit.EvalBuilder.appendAndFin_eval,
        StraightLineCircuit.EvalBuilder.appendOrFin_eval,
        StraightLineCircuit.EvalBuilder.appendFin_lift_eval]

/--
Evaluation rule for the token-based symbol builder.  It simply forwards the
statement of `symbolBuilder_eval` after translating the stored wire token back
into a concrete index.
-/
lemma symbolBuilderWire_eval (sc : StraightConfig M n) (x : Point n) :
    let result := symbolBuilderWire (M := M) (n := n) sc
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (result.snd.toFin (n := n) (g := result.fst.circuit.gates)
          (Nat.le_of_eq rfl)) =
      (tapeIndexList (M := M) n).foldl (fun acc i =>
        acc ||
          (StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.head i) &&
            StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.tape i)))
        false := by
  classical
  unfold symbolBuilderWire
  simpa [StraightLineCircuit.Wire.toFin_ofFin]
    using symbolBuilder_eval (M := M) (n := n) (sc := sc) (x := x)

/--
The symbol wire produced by `symbolBuilder` evaluates to the tape bit located
under the head whenever the straight-line configuration satisfies its
specification.
-/
lemma symbolBuilder_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    ∀ x,
      let result := symbolBuilder (M := M) (n := n) sc
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
        (f x).tape (f x).head := by
  classical
  intro x
  have hEval := symbolBuilder_eval (M := M) (n := n) (sc := sc) (x := x)
  simp [symbolBuilder, foldl_or_eq_any, List.any_map, evalHead, evalTape,
    Bool.and_left_comm, Bool.and_assoc, Bool.and_comm,
    hsc.head_eq, hsc.tape_eq] at hEval
  have hMem : (f x).head ∈ tapeIndexList (M := M) n := by
    simpa [tapeIndexList] using List.mem_finRange (f x).head
  by_cases hbit : (f x).tape (f x).head = true
  · have hWitness : headIndicator (M := M) (n := n) (f x) ((f x).head) &&
        (f x).tape ((f x).head) = true := by
        simp [hbit, headIndicator_self]
    have hAny : List.any (tapeIndexList (M := M) n)
        (fun i => headIndicator (M := M) (n := n) (f x) i && (f x).tape i) = true := by
      refine (List.any_eq_true).2 ?_
      exact ⟨(f x).head, hMem, hWitness⟩
    simpa [hAny, hbit] using hEval
  · have hAnyFalse : List.any (tapeIndexList (M := M) n)
        (fun i => headIndicator (M := M) (n := n) (f x) i && (f x).tape i) = false := by
      refine (List.any_eq_false).2 ?_
      intro i hi
      by_cases hEq : i = (f x).head
      · subst hEq
        simp [hbit, headIndicator_self]
      · have : headIndicator (M := M) (n := n) (f x) i = false :=
          headIndicator_ne (M := M) (n := n) (f x) (by simpa [eq_comm] using hEq)
      simp [this, Bool.false_and]
    simpa [hAnyFalse, hbit] using hEval

/--
Correctness statement for `symbolBuilderWire`: translating the stored token
into a concrete wire yields the actual tape symbol located under the head.
-/
lemma symbolBuilderWire_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    ∀ x,
      let result := symbolBuilderWire (M := M) (n := n) sc
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
          (result.snd.toFin (n := n) (g := result.fst.circuit.gates)
            (Nat.le_of_eq rfl)) =
        (f x).tape (f x).head := by
  classical
  intro x
  unfold symbolBuilderWire
  simpa [StraightLineCircuit.Wire.toFin_ofFin]
    using symbolBuilder_spec (M := M) (n := n) (sc := sc) (f := f) hsc (x := x)

/-!
### Branch indicators in the straight-line world

The next helper packages the ubiquitous conjunction
`stateIndicator(q) ∧ guardSymbol(b)` into a single reusable wire.  The
construction mirrors `branchIndicator` from the tree-based circuit
development but operates in the straight-line builder monad so that the
resulting wire can be referenced by later gates without rebuilding the
intermediate bookkeeping each time.
-/

/--
Specialised helper building the conjunction "the control state is `q` and the
scanned symbol equals `b`" when a reusable symbol wire is already available.
The function merely appends the necessary gates to the supplied builder,
returning both the extended builder and the freshly created wire.
-/
def branchBuilderFrom (sc : StraightConfig M n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (symbolWire : Fin (n + b.circuit.gates)) (qs : M.state × Bool) :
    Σ' (b' : StraightLineCircuit.EvalBuilder n sc.circuit),
      Fin (n + b'.circuit.gates) := by
  classical
  -- The state component is an existing wire of the base circuit; lift it into
  -- the current builder so that the subsequent gates may reference it.
  let stateWire := b.liftBase (sc.state (stateIndex M qs.1))
  -- Depending on the requested symbol value we either negate the symbol first
  -- or directly form the conjunction `state ∧ symbol`.
  cases hsym : qs.2 with
  | false =>
      let negResult := StraightLineCircuit.EvalBuilder.appendNotFin
        (b := b) symbolWire
      let liftedState :=
        (StraightLineCircuit.EvalBuilder.appendFin_lift
          (b := b) (op := StraightOp.not symbolWire)) stateWire
      let andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := negResult.fst) liftedState negResult.snd
      exact ⟨andResult.fst, andResult.snd⟩
  | true =>
      let andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := b) stateWire symbolWire
      exact ⟨andResult.fst, andResult.snd⟩

/--
Straight-line counterpart of `branchIndicator`.  Starting from a straight-line
configuration, the builder augments the circuit with the necessary gates to
compute the conjunction "the control state is `q` and the scanned symbol is
`b`".  The resulting sigma package exposes both the extended builder and the
wire pointing to the freshly created gate.
-/
def branchBuilder (sc : StraightConfig M n) (qs : M.state × Bool) :
    Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
      Fin (n + b.circuit.gates) := by
  classical
  -- First obtain the wire computing the tape symbol under the head.
  let symbol := symbolBuilder (M := M) (n := n) sc
  -- Delegate to the helper, which reuses the symbol across all branches.
  exact branchBuilderFrom (M := M) (n := n) (sc := sc)
    (b := symbol.fst) (symbolWire := symbol.snd) qs

/--
Semantic characterisation of the straight-line branch indicator.  When the
input straight-line configuration satisfies `Spec`, the resulting wire evaluates
to the Boolean guard checking that the control state equals `q` and that the
scanned tape symbol is `b`.
-/
lemma branchBuilder_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    ∀ x (qs : M.state × Bool),
      let result := branchBuilder (M := M) (n := n) sc qs
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
        (stateIndicator M (f x) (stateIndex M qs.1) &&
          cond qs.2 ((f x).tape (f x).head)
            (!(f x).tape (f x).head)) := by
  classical
  intro x qs
  -- Expose the straight-line symbol wire and instantiate the generic helper.
  set symbol := symbolBuilder (M := M) (n := n) sc with hsymbolDef
  -- Apply the general branch builder lemma.
  simpa [branchBuilder, symbol, hsymbolDef]
    using branchBuilderFrom_spec (M := M) (n := n) (sc := sc)
      (b := symbol.fst) (symbolWire := symbol.snd)
      (hsymbol := by intro y; simpa [symbol, hsymbolDef]
        using symbolBuilder_spec (M := M) (n := n)
          (sc := sc) (f := f) hsc (x := y)) (x := x) (qs := qs)

/--
Specification of `branchBuilderFrom`: assuming the supplied symbol wire indeed
computes the scanned tape bit, the resulting gate realises the conjunction of
the state indicator and the corresponding symbol guard.
-/
lemma branchBuilderFrom_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (symbolWire : Fin (n + b.circuit.gates))
    (hsymbol : ∀ x,
      StraightLineCircuit.evalWire (C := b.circuit) (x := x) symbolWire =
        (f x).tape (f x).head) :
    ∀ x (qs : M.state × Bool),
      let result := branchBuilderFrom (M := M) (n := n) (sc := sc)
        (b := b) (symbolWire := symbolWire) qs
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
        (stateIndicator M (f x) (stateIndex M qs.1) &&
          cond qs.2 ((f x).tape (f x).head)
            (!(f x).tape (f x).head)) := by
  classical
  intro x qs
  -- Lift the state wire once; its evaluation is determined by the specification.
  let stateWire := b.liftBase (sc.state (stateIndex M qs.1))
  have hstateEval :
      StraightLineCircuit.evalWire (C := b.circuit) (x := x) stateWire =
        stateIndicator M (f x) (stateIndex M qs.1) := by
    have hLift := StraightLineCircuit.EvalBuilder.eval_liftBase_eq
        (b := b) (x := x) (i := sc.state (stateIndex M qs.1))
    have hBase : StraightLineCircuit.evalWire (C := sc.circuit) (x := x)
        (sc.state (stateIndex M qs.1)) =
          stateIndicator M (f x) (stateIndex M qs.1) := by
      simpa [evalState]
        using hsc.state_eq (x := x) (i := stateIndex M qs.1)
    simpa [stateWire] using hLift.trans hBase
  -- Split on the requested symbol value.
  cases hqs : qs.2 with
  | false =>
      -- Append the negation gate followed by the final conjunction.
      have hneg := StraightLineCircuit.EvalBuilder.appendFin_eval
        (b := b) (op := StraightOp.not symbolWire) (x := x)
      have hstateLift := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
        (b := b) (op := StraightOp.not symbolWire) (x := x)
        (w := stateWire)
      set negResult := StraightLineCircuit.EvalBuilder.appendNotFin
        (b := b) symbolWire with hnegResult
      set liftedState :=
        (StraightLineCircuit.EvalBuilder.appendFin_lift
          (b := b) (op := StraightOp.not symbolWire)) stateWire
        with hlifted
      have hstateLiftEval :
          StraightLineCircuit.evalWire
              (C := negResult.fst.circuit) (x := x) liftedState =
            stateIndicator M (f x) (stateIndex M qs.1) := by
        simpa [hstateEval, hnegResult, liftedState, hlifted]
          using hstateLift
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := negResult.fst) liftedState negResult.snd with handResult
      have hnegEval : StraightLineCircuit.evalWire
          (C := negResult.fst.circuit) (x := x) negResult.snd =
          ! StraightLineCircuit.evalWire (C := b.circuit) (x := x) symbolWire := by
        simpa [negResult, hnegResult] using hneg
      have := StraightLineCircuit.EvalBuilder.appendAndFin_eval
        (b := negResult.fst) (u := liftedState) (v := negResult.snd) (x := x)
      have hsymEval := hsymbol x
      simpa [branchBuilderFrom, hqs, cond_false, stateWire, hstateEval,
        hstateLiftEval, hnegEval, hsymEval, Bool.and_left_comm, Bool.and_assoc,
        negResult, andResult, hnegResult, handResult]
        using this
  | true =>
      -- Direct conjunction case.
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := b) stateWire symbolWire with handResult
      have := StraightLineCircuit.EvalBuilder.appendAndFin_eval
        (b := b) (u := stateWire) (v := symbolWire) (x := x)
      have hsymEval := hsymbol x
      simpa [branchBuilderFrom, hqs, cond_true, stateWire, hstateEval,
        hsymEval, Bool.and_left_comm, Bool.and_assoc, andResult, handResult]
        using this

/--
Token-based variant of `branchBuilder`.  Packaging the resulting wire as a
`StraightLineCircuit.Wire` facilitates transporting it across subsequent gate
insertions without repeating the underlying arithmetic bounds.
-/
def branchBuilderWire (sc : StraightConfig M n) (qs : M.state × Bool) :
    Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
      StraightLineCircuit.Wire n :=
  let result := branchBuilder (M := M) (n := n) sc qs
  ⟨ result.fst
  , StraightLineCircuit.Wire.ofFin (n := n)
      (g := result.fst.circuit.gates) result.snd ⟩

/--
Evaluation rule for the token returned by `branchBuilderWire`.
-/
lemma branchBuilderWire_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    ∀ x (qs : M.state × Bool),
      let result := branchBuilderWire (M := M) (n := n) sc qs
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
          (result.snd.toFin (n := n) (g := result.fst.circuit.gates)
            (Nat.le_of_eq rfl)) =
        (stateIndicator M (f x) (stateIndex M qs.1) &&
          cond qs.2 ((f x).tape (f x).head)
            (!(f x).tape (f x).head)) := by
  classical
  intro x qs
  unfold branchBuilderWire
  simpa [StraightLineCircuit.Wire.toFin_ofFin]
    using branchBuilder_spec (M := M) (n := n) (sc := sc) (f := f) hsc (x := x)
      (qs := qs)

/--
The straight-line construction of `branchBuilderFrom` only appends gates to the
current builder.  Consequently the number of gates monotonically increases, a
fact we will repeatedly rely on when transporting previously created wires
through subsequent builder extensions.
-/
lemma branchBuilderFrom_gate_le (sc : StraightConfig M n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (symbolWire : Fin (n + b.circuit.gates)) (qs : M.state × Bool) :
    b.circuit.gates ≤
      (branchBuilderFrom (M := M) (n := n) (sc := sc)
        (b := b) (symbolWire := symbolWire) qs).fst.circuit.gates := by
  classical
  -- Peel off the two cases present in the definition of `branchBuilderFrom`.
  cases hqs : qs.2 with
  | false =>
      -- In the `false` branch we append a negation followed by a conjunction.
      -- We expose the intermediate builders in order to reason about their
      -- gate counts explicitly.
      set negResult :=
        StraightLineCircuit.EvalBuilder.appendNotFin (b := b) symbolWire
        with hneg
      set liftedState :=
        (StraightLineCircuit.EvalBuilder.appendFin_lift
          (b := b) (op := StraightOp.not symbolWire))
          (b.liftBase (sc.state (stateIndex M qs.1))) with hlift
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := negResult.fst) liftedState negResult.snd with hand
      have hnegGate :
          negResult.fst.circuit.gates = b.circuit.gates + 1 := by
        -- Appending the negation adds a single gate.
        simpa [negResult, StraightLineCircuit.EvalBuilder.appendNotFin]
          using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
            (b := b) (op := StraightOp.not symbolWire)
      have handGate :
          andResult.fst.circuit.gates = negResult.fst.circuit.gates + 1 := by
        -- Appending the final conjunction adds one more gate.
        simpa [andResult, StraightLineCircuit.EvalBuilder.appendAndFin,
          hnegGate]
          using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
            (b := negResult.fst)
            (op := StraightOp.and liftedState negResult.snd)
      -- Combine the two increments to obtain the desired inequality.
      have hle₁ : b.circuit.gates ≤ negResult.fst.circuit.gates := by
        have := Nat.le_succ b.circuit.gates
        simpa [hnegGate, Nat.succ_eq_add_one] using this
      have hle₂ : negResult.fst.circuit.gates ≤ andResult.fst.circuit.gates := by
        have := Nat.le_succ negResult.fst.circuit.gates
        simpa [handGate, Nat.succ_eq_add_one] using this
      exact Nat.le_trans hle₁ hle₂
  | true =>
      -- When the scanned symbol is true we only append a single conjunction.
      set stateWire := b.liftBase (sc.state (stateIndex M qs.1)) with hstate
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := b) stateWire symbolWire with hand
      have handGate :
          andResult.fst.circuit.gates = b.circuit.gates + 1 := by
        simpa [andResult, StraightLineCircuit.EvalBuilder.appendAndFin,
          hstate]
          using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
            (b := b) (op := StraightOp.and stateWire symbolWire)
      have := Nat.le_succ b.circuit.gates
      simpa [handGate, Nat.succ_eq_add_one]
        using this

/--
Auxiliary structure recording the state after constructing the straight-line
branch indicators for every pair `(q, b)` appearing in `stateSymbolPairs`.  The
data keeps track of the accumulated builder, the reusable symbol wire and all
branch wires together with the guarantees that the recorded wires remain within
the range of the builder's gate count.
-/
structure BranchSnapshot (sc : StraightConfig M n) where
  builder : StraightLineCircuit.EvalBuilder n sc.circuit
  symbol  : StraightLineCircuit.Wire n
  symbol_le : symbol.bound ≤ builder.circuit.gates
  branches : List ((M.state × Bool) × StraightLineCircuit.Wire n)
  branches_le :
    ∀ {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
      ((qs, w) ∈ branches) → w.bound ≤ builder.circuit.gates

/--
Internal helper used to accumulate the list of branch wires.  The function
processes the supplied list of transition pairs sequentially, invoking
`branchBuilderFrom` at each step and recording the resulting wire token.  The
return value packages the final builder together with the updated bookkeeping
information required to keep track of index bounds.
-/
def branchSnapshotAux (sc : StraightConfig M n)
    (symbol : StraightLineCircuit.Wire n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hSymbol : symbol.bound ≤ b.circuit.gates)
    : ∀ (pairs : List (M.state × Bool)),
        Σ' (b' : StraightLineCircuit.EvalBuilder n sc.circuit),
          (symbol.bound ≤ b'.circuit.gates) ×
            (b.circuit.gates ≤ b'.circuit.gates) ×
            { l : List ((M.state × Bool) × StraightLineCircuit.Wire n) //
              ∀ {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
                ((qs, w) ∈ l) → w.bound ≤ b'.circuit.gates }
  | [] =>
      -- No more branches to process: return the current builder unchanged.
      ⟨ b
      , hSymbol
      , le_rfl
      , ⟨[], by intro qs w hmem; cases hmem⟩ ⟩
  | qs :: rest =>
      by
        -- Interpret the cached symbol wire inside the current builder.
        have hSymbolCurrent : symbol.bound ≤ b.circuit.gates := hSymbol
        let symbolFin := symbol.toFin (n := n) (g := b.circuit.gates)
          hSymbolCurrent
        -- Append the branch corresponding to `qs` and convert the resulting
        -- index into a reusable wire token.
        let result := branchBuilderFrom (M := M) (n := n) (sc := sc)
          (b := b) (symbolWire := symbolFin) qs
        let token : StraightLineCircuit.Wire n :=
          StraightLineCircuit.Wire.ofFin (n := n)
            (g := result.fst.circuit.gates) result.snd
        -- The symbol wire remains valid in the extended builder thanks to the
        -- monotonicity lemma established above.
        have hSymbolNext : symbol.bound ≤ result.fst.circuit.gates := by
          exact Nat.le_trans hSymbol
            (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
              (b := b) (symbolWire := symbolFin) (qs := qs))
        -- Recursively process the remaining branches.
        obtain ⟨bRest, hSymbolRest, hMonoRest, restList⟩ :=
          branchSnapshotAux (M := M) (n := n) (sc := sc)
            symbol result.fst hSymbolNext rest
        -- Assemble the final list together with its bound witnesses.
        refine ⟨ bRest
               , hSymbolRest
               , ?_ 
               , ⟨ (qs, token) :: restList.val, ?_ ⟩ ⟩
        · -- The final builder contains all gates produced so far.
          exact Nat.le_trans
            (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
              (b := b) (symbolWire := symbolFin) (qs := qs))
            hMonoRest
        · -- Every recorded wire remains within range of the final builder.
          intro qs' w hmem
          have hmem' := List.mem_cons.1 hmem
          cases hmem' with
          | inl hhead =>
              -- The head of the list corresponds to the freshly created wire.
              cases hhead with
              | rfl =>
                  have : result.fst.circuit.gates ≤ bRest.circuit.gates :=
                    hMonoRest
                  simpa [token] using this
          | inr htail =>
              -- All other wires come from the recursive call where the bound
              -- property is already available.
              exact restList.property htail

/--
Construct the full branch snapshot starting from a straight-line configuration.
The function first materialises the reusable symbol wire (via
`symbolBuilderWire`) and subsequently processes every transition pair.  The
resulting snapshot records the extended builder together with the collected
branch wires.
-/
def branchSnapshot (sc : StraightConfig M n) : BranchSnapshot (M := M) (n := n) sc := by
  classical
  -- Obtain the initial builder equipped with the symbol wire.
  let symbolResult := symbolBuilderWire (M := M) (n := n) sc
  have hSymbol : symbolResult.snd.bound ≤ symbolResult.fst.circuit.gates := by
    -- The token was created directly from the builder, hence the bounds agree.
    have := (by
      simp [symbolResult] : symbolResult.snd.bound = symbolResult.fst.circuit.gates)
    exact le_of_eq this
  -- Process all pairs contained in `stateSymbolPairs`.
  obtain ⟨bFinal, hSymbolFinal, _hMono, restList⟩ :=
    branchSnapshotAux (M := M) (n := n) (sc := sc)
      symbolResult.snd symbolResult.fst hSymbol (stateSymbolPairs M)
  -- Package the collected information into the `BranchSnapshot` structure.
  refine { builder := bFinal
         , symbol := symbolResult.snd
         , symbol_le := hSymbolFinal
         , branches := restList.val
         , branches_le := ?_ }
  intro qs w hmem
  exact restList.property hmem

/--
The branch snapshot is the foundation for subsequent straight-line
constructions.  In addition to reusing the symbol wire we will also need the
aggregated write bit.  The following structure extends the snapshot with a
dedicated wire computing the write contribution of the current configuration.
-/
structure WriteSnapshot (sc : StraightConfig M n)
    extends BranchSnapshot (M := M) (n := n) sc where
  write : StraightLineCircuit.Wire n
  write_le : write.bound ≤ builder.circuit.gates

/--
Appending a `bigOr` never decreases the number of gates of an
`EvalBuilder`.  The lemma is proved by induction on the list of wires,
tracking the recursive shape of `appendBigOr`.
-/
lemma StraightLineCircuit.EvalBuilder.appendBigOr_gate_le
    (b : StraightLineCircuit.EvalBuilder n base)
    (ws : List (Fin (n + b.circuit.gates))) :
    b.circuit.gates ≤
      (StraightLineCircuit.EvalBuilder.appendBigOr (b := b) ws).fst.circuit.gates := by
  classical
  induction ws with
  | nil =>
      -- The empty list introduces a fresh constant gate.
      simp [StraightLineCircuit.EvalBuilder.appendBigOr]
      -- The helper `appendConstFin` appends a single gate.
      have := StraightLineCircuit.EvalBuilder.appendFin_gate_eq
        (b := b) (op := StraightOp.const false)
      simpa [StraightLineCircuit.EvalBuilder.appendConstFin,
        StraightLineCircuit.EvalBuilder.appendBigOr] using
        (Nat.le_succ b.circuit.gates)
  | cons w ws ih =>
      cases ws with
      | nil =>
          -- A singleton list leaves the builder unchanged.
          simp [StraightLineCircuit.EvalBuilder.appendBigOr]
      | cons w' ws' =>
          -- The recursion appends one OR gate and continues with the lifted list.
          simp [StraightLineCircuit.EvalBuilder.appendBigOr] at ih ⊢
          set result := StraightLineCircuit.EvalBuilder.appendOrFin
            (b := b) w w' with hresult
          have hStep : b.circuit.gates ≤ result.fst.circuit.gates := by
            -- Appending a single gate increases the count by one.
            simpa [result, StraightLineCircuit.EvalBuilder.appendOrFin] using
              (Nat.le_succ b.circuit.gates)
          -- Compose with the induction hypothesis for the recursive call.
          exact Nat.le_trans hStep ih

/--
Construct the write-bit wire alongside the branch snapshot.  The resulting
`WriteSnapshot` stores the accumulated builder together with all auxiliary wires
required to analyse the transition step.
-/
def writeSnapshot (sc : StraightConfig M n) : WriteSnapshot (M := M) (n := n) sc := by
  classical
  -- Start from the branch snapshot which already provides the symbol and all
  -- branch guards.
  let base := branchSnapshot (M := M) (n := n) sc
  -- Helper collecting all write-contributing wires.  The predicate `h` provides
  -- the bound guarantee for the sublist currently under consideration.
  let rec collect
      (branches : List ((M.state × Bool) × StraightLineCircuit.Wire n)) :
      (∀ {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
          ((qs, w) ∈ branches) → w.bound ≤ base.builder.circuit.gates) →
        List (Fin (n + base.builder.circuit.gates)) :=
    fun h =>
      match branches with
      | [] => []
      | (qs, w) :: rest =>
          -- Process the tail first, inheriting the bound invariant.
          let restCollected := collect rest (fun {qs'} {w'} hmem =>
            h (by exact List.mem_cons_of_mem _ hmem))
          -- The head contributes iff the transition writes `true`.
          let hbound : w.bound ≤ base.builder.circuit.gates :=
            h (by exact List.mem_cons_self _ _)
          if (M.step qs.1 qs.2).2 then
            (w.toFin (n := n) (g := base.builder.circuit.gates) hbound) ::
              restCollected
          else
            restCollected
    termination_by collect branches _ => branches.length
  -- Instantiate the helper with the complete branch list.
  let writeIndices := collect base.branches base.branches_le
  -- Augment the builder with the disjunction of all write contributions.
  let writeResult := StraightLineCircuit.EvalBuilder.appendBigOr
    (b := base.builder) writeIndices
  -- The newly created gate serves as the write-bit wire.
  let writeWire : StraightLineCircuit.Wire n :=
    StraightLineCircuit.Wire.ofFin (n := n)
      (g := writeResult.fst.circuit.gates) writeResult.snd
  -- Assemble the final structure, updating the bound witnesses accordingly.
  refine { builder := writeResult.fst
         , symbol := base.symbol
         , symbol_le := ?_
         , branches := base.branches
         , branches_le := ?_
         , write := writeWire
         , write_le := by
             have := StraightLineCircuit.Wire.ofFin_bound
               (n := n) (g := writeResult.fst.circuit.gates) writeResult.snd
             simpa [writeWire] using (le_of_eq this) }
  · -- The symbol wire remains in range thanks to gate-count monotonicity.
    have := StraightLineCircuit.EvalBuilder.appendBigOr_gate_le
      (b := base.builder) (ws := writeIndices)
    exact Nat.le_trans base.symbol_le this
  · -- Every branch wire continues to be valid in the extended builder.
    intro qs w hmem
    have := StraightLineCircuit.EvalBuilder.appendBigOr_gate_le
      (b := base.builder) (ws := writeIndices)
    have hbranch := base.branches_le hmem
    exact Nat.le_trans hbranch this

end StraightConfig

/-- Enumerate all tape indices as a list. -/
def tapeIndexList (M : TM) (n : ℕ) : List (Fin (M.tapeLength n)) :=
  List.finRange (M.tapeLength n)

/-- Circuit returning the bit currently scanned by the head. -/
noncomputable def symbol (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) : Circuit n :=
  Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
    Circuit.and (cc.head i) (cc.tape i))

lemma symbol_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x, Circuit.eval (symbol (M := M) cc) x = (f x).tape (f x).head := by
  classical
  intro x
  have hHead := hcc.head_eq (x := x)
  have hTape := hcc.tape_eq (x := x)
  have hMem : (f x).head ∈ tapeIndexList (M := M) n := by
    simpa [tapeIndexList] using List.mem_finRange (f x).head
  have hEval :
      Circuit.eval (symbol (M := M) cc) x =
        List.any (tapeIndexList (M := M) n) (fun i =>
          headIndicator (f x) i && (f x).tape i) := by
    simp [symbol, tapeIndexList, Circuit.eval_bigOr_any, List.any_map,
      Circuit.eval, ConfigCircuits.evalHead, ConfigCircuits.evalTape,
      hHead, hTape, Bool.and_left_comm, Bool.and_assoc]
  by_cases hbit : (f x).tape (f x).head = true
  · have hWitness :
        headIndicator (f x) ((f x).head) && (f x).tape ((f x).head) = true := by
        simp [hbit, headIndicator_self]
    have hAny :
        List.any (tapeIndexList (M := M) n)
          (fun i => headIndicator (f x) i && (f x).tape i) = true := by
      refine (List.any_eq_true).2 ?_
      exact ⟨(f x).head, hMem, hWitness⟩
    simp [hEval, hbit, hAny]
  · have hAnyFalse :
        List.any (tapeIndexList (M := M) n)
          (fun i => headIndicator (f x) i && (f x).tape i) = false := by
      refine (List.any_eq_false).2 ?_
      intro i hi
      by_cases hEq : i = (f x).head
      · subst hEq
        simp [hbit, headIndicator_self]
    · have : headIndicator (f x) i = false :=
        headIndicator_ne (M := M) (n := n) (f x) (by simpa [eq_comm] using hEq)
      simp [this, Bool.false_and]
    simp [hEval, hbit, hAnyFalse]

/-- Enumerate the states of the machine as a list. -/
noncomputable def stateList (M : TM) : List M.state :=
  (Fintype.elems M.state).toList

/-- Auxiliary list containing every pair `(q, b)` with `q` a control state and
`b ∈ {false, true}`.  The list powers the various `bigOr` constructions used in
the transition circuit. -/
def stateSymbolPairs (M : TM) : List (M.state × Bool) :=
  (stateList M).bind fun q => [(q, false), (q, true)]

lemma state_mem_stateList (M : TM) (q : M.state) : q ∈ stateList M := by
  classical
  have : q ∈ (Fintype.elems M.state) := by
    simpa using (Finset.mem_universe q)
  simpa [stateList] using this

lemma length_tapeIndexList (M : TM) (n : ℕ) :
    (tapeIndexList (M := M) n).length = M.tapeLength n := by
  classical
  simpa [tapeIndexList] using List.length_finRange (M.tapeLength n)

lemma length_stateList (M : TM) : (stateList M).length = stateCard M := by
  classical
  have := Finset.length_toList (Fintype.elems M.state)
  simpa [stateList, stateCard] using this

lemma length_stateSymbolPairs (M : TM) :
    (stateSymbolPairs M).length = 2 * stateCard M := by
  classical
  have :=
    List.length_bind (stateList M)
      (fun q => ([(q, false), (q, true)] : List (M.state × Bool)))
  -- Simplify the generic formula: each branch contributes exactly two elements.
  simpa [stateSymbolPairs, List.length_bind, length_stateList, List.map_const,
    List.sum_replicate, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

lemma pair_mem_stateSymbolPairs (M : TM) (q : M.state) (b : Bool) :
    (q, b) ∈ stateSymbolPairs M := by
  classical
  refine List.mem_bind.2 ?_
  refine ⟨q, state_mem_stateList (M := M) q, ?_⟩
  cases b <;> simp

/-- Boolean guard capturing the conjunction "the control state equals `q` and
the scanned symbol equals `b`" for a concrete configuration.  This predicate is
the semantic counterpart of the straight-line branch builders. -/
def branchGuard (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (qs : M.state × Bool) : Bool :=
  stateIndicator M conf (stateIndex M qs.1) &&
    cond qs.2 (conf.tape conf.head) (!(conf.tape conf.head))

/-- Contribution of the transition branch `(q, b)` to the write bit.  The branch
affects the next tape value precisely when the transition function writes `true`
for the corresponding pair. -/
def writeContribution (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (qs : M.state × Bool) : Bool :=
  match M.step qs.1 qs.2 with
  | ⟨_, write, _⟩ =>
      if write then branchGuard (M := M) (conf := conf) qs else false

/-- Fold function used to aggregate the write-bit contributions of the processed
branches.  The helper is phrased in terms of a Boolean OR so that standard
lemmas about `List.any` become directly applicable. -/
def writeFoldFun (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (acc : Bool) (qs : M.state × Bool) : Bool :=
  acc || writeContribution (M := M) (conf := conf) qs

/-- Aggregated effect of the supplied branch list on the tape bit written by the
machine.  The definition mirrors the Boolean structure of `writeBit` but is
stated directly on configurations rather than circuits. -/
def writeAccumulator (M : TM) {n : ℕ}
    (pairs : List (M.state × Bool)) (conf : TM.Configuration M n) : Bool :=
  pairs.foldl (writeFoldFun (M := M) (conf := conf)) false

@[simp] lemma writeAccumulator_nil (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) :
    writeAccumulator (M := M) (pairs := []) conf = false := rfl

lemma writeAccumulator_cons (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (qs : M.state × Bool)
    (pairs : List (M.state × Bool)) :
    writeAccumulator (M := M) (pairs := qs :: pairs) conf =
      writeFoldFun (M := M) (conf := conf) false qs := by
  simp [writeAccumulator, writeFoldFun]

lemma writeAccumulator_append_singleton (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (pairs : List (M.state × Bool))
    (qs : M.state × Bool) :
    writeAccumulator (M := M) (pairs := pairs ++ [qs]) conf =
      writeFoldFun (M := M) (conf := conf)
        (writeAccumulator (M := M) (pairs := pairs) conf) qs := by
  simp [writeAccumulator, writeFoldFun, List.foldl_append]

lemma writeAccumulator_eq_or (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (pairs : List (M.state × Bool)) :
    writeAccumulator (M := M) (pairs := pairs) conf =
      pairs.foldl (fun acc qs =>
        acc || writeContribution (M := M) (conf := conf) qs) false := by
  simp [writeAccumulator, writeFoldFun]

lemma writeAccumulator_eq_any (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (pairs : List (M.state × Bool)) :
    writeAccumulator (M := M) (pairs := pairs) conf =
      List.any pairs (fun qs =>
        writeContribution (M := M) (conf := conf) qs) := by
  classical
  induction pairs generalizing conf with
  | nil => simp [writeAccumulator]
  | cons qs pairs ih =>
      simp [writeAccumulator, writeFoldFun, Bool.or_comm, Bool.or_left_comm,
        Bool.or_assoc, ih]

lemma writeContribution_spec (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) (qs : M.state × Bool) :
    writeContribution (M := M) (conf := conf) qs = true ↔
      (conf.state = qs.1 ∧ conf.tape conf.head = qs.2 ∧
        (M.step qs.1 qs.2).2 = true) := by
  classical
  unfold writeContribution branchGuard
  cases hstep : M.step qs.1 qs.2 with
  | mk next write move =>
      cases write <;>
        simp [stateIndicator_true_iff, stateIndicator_ne, stateIndex,
          stateEquiv, hstep]

lemma writeAccumulator_spec (M : TM) {n : ℕ}
    (conf : TM.Configuration M n) :
    writeAccumulator (M := M) (pairs := stateSymbolPairs M) conf =
      let sym := conf.tape conf.head
      let (_, bit, _) := M.step conf.state sym
      bit := by
  classical
  obtain ⟨next, bit, move⟩ := M.step conf.state (conf.tape conf.head)
  have hPairs := pair_mem_stateSymbolPairs (M := M)
      conf.state (conf.tape conf.head)
  have hAny := writeAccumulator_eq_any (M := M) (n := n) (conf := conf)
      (pairs := stateSymbolPairs M)
  have hWitness : writeContribution (M := M) (conf := conf)
      (conf.state, conf.tape conf.head) = bit := by
    cases bit <;> simp [writeContribution, branchGuard]
  have hAllFalse : ∀ qs ∈ stateSymbolPairs M,
      qs ≠ (conf.state, conf.tape conf.head) →
      writeContribution (M := M) (conf := conf) qs = false := by
    intro qs hqs hneq
    rcases qs with ⟨q, b⟩
    by_cases hq : q = conf.state
    · subst hq
      by_cases hb : b = conf.tape conf.head
      · exact (hneq (by cases hb; simp)).elim
      · cases hb <;> simp [writeContribution, branchGuard]
    · cases hq <;> simp [writeContribution, branchGuard]
  cases bit with
  | false =>
      have :
          List.any (stateSymbolPairs M)
            (fun qs => writeContribution (M := M) (conf := conf) qs) = false :=
        by
          refine (List.any_eq_false).2 ?_
          intro qs hqs
          by_cases hq : qs = (conf.state, conf.tape conf.head)
          · subst hq
            simpa [hWitness]
          · exact hAllFalse qs hqs hq
      simpa [writeAccumulator, writeFoldFun, hAny, this]
  | true =>
      have :
          List.any (stateSymbolPairs M)
            (fun qs => writeContribution (M := M) (conf := conf) qs) = true :=
        by
          refine (List.any_eq_true).2 ?_
          exact ⟨(conf.state, conf.tape conf.head), hPairs, by simpa [hWitness]⟩
      simpa [writeAccumulator, writeFoldFun, hAny, this]

/-- Guard ensuring that the symbol tested in a transition branch equals the
chosen Boolean value. -/
noncomputable def guardSymbol (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (b : Bool) : Circuit n :=
  if b then symbol (M := M) cc else Circuit.not (symbol (M := M) cc)

lemma guardSymbol_eval {M : TM} {n : ℕ}
    (cc : ConfigCircuits M n) (x : Point n) (b : Bool) :
    Circuit.eval (guardSymbol (M := M) (n := n) cc b) x =
      cond b (Circuit.eval (symbol (M := M) cc) x)
        (! Circuit.eval (symbol (M := M) cc) x) := by
  cases b <;> simp [guardSymbol]

/--
The guard circuit simply checks whether the scanned symbol equals the
Boolean parameter `b`.  The statement reuses the specification of the
`symbol` circuit, hence it holds for every configuration that `cc`
faithfully describes.
-/
lemma guardSymbol_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x b,
      Circuit.eval (guardSymbol (M := M) (n := n) cc b) x = true ↔
        (f x).tape (f x).head = b := by
  classical
  intro x b
  have hsym :=
    (symbol_spec (M := M) (n := n) (cc := cc) (f := f) hcc x)
  cases hb : (f x).tape (f x).head <;> cases b <;>
    simp [guardSymbol_eval, hsym, hb]

/--
Conjunction of the state indicator with the symbol guard.  This auxiliary
definition encapsulates the common premise "the machine is in state `q`
and reads bit `b`" that appears in every transition branch.
-/
noncomputable def branchIndicator (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (qs : M.state × Bool) : Circuit n :=
  Circuit.and (cc.state (stateIndex M qs.1))
    (guardSymbol (M := M) (n := n) cc qs.2)

/--
`branchIndicator` evaluates to true precisely when the encoded
configuration matches the pair `(q, b)`.
-/
lemma branchIndicator_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x (qs : M.state × Bool),
      Circuit.eval (branchIndicator (M := M) (n := n) cc qs) x = true ↔
        (f x).state = qs.1 ∧ (f x).tape (f x).head = qs.2 := by
  classical
  intro x qs
  constructor
  · intro h
    have hpair := Bool.and_eq_true.mp (by simpa [branchIndicator] using h)
    have hState := hcc.state_eq (x := x) (i := stateIndex M qs.1)
    have hGuard := guardSymbol_spec (M := M) (n := n)
      (cc := cc) (f := f) hcc x qs.2
    have hstateTrue :
        stateIndicator M (f x) (stateIndex M qs.1) = true := by
      have := hState.symm.trans hpair.1
      simpa [ConfigCircuits.evalState] using this
    have hguardTrue : (f x).tape (f x).head = qs.2 :=
      (hGuard).1 hpair.2
    have hstateEq : stateIndex M (f x).state = stateIndex M qs.1 := by
      simpa using
        (stateIndicator_true_iff (M := M) (n := n) (f x)
          (stateIndex M qs.1)).mp hstateTrue
    refine ⟨?_, hguardTrue⟩
    have hstates : (f x).state = qs.1 := by
      have := congrArg (fun i => (stateEquiv M).symm i) hstateEq
      simpa [stateIndex, Equiv.symm_apply_apply] using this
    exact hstates
  · intro h
    obtain ⟨hstate, hsymbol⟩ := h
    have hStateIndicator :
        Circuit.eval (cc.state (stateIndex M qs.1)) x = true := by
      have hIndicator :
          stateIndicator M (f x) (stateIndex M qs.1) = true := by
        have hidx : stateIndex M (f x).state = stateIndex M qs.1 := by
          simpa [hstate]
        exact
          (stateIndicator_true_iff (M := M) (n := n) (f x)
            (stateIndex M qs.1)).2 hidx
      have := hcc.state_eq (x := x) (i := stateIndex M qs.1)
      simpa [ConfigCircuits.evalState] using this.trans hIndicator
    have hGuardIndicator :
        Circuit.eval (guardSymbol (M := M) (n := n) cc qs.2) x = true :=
      (guardSymbol_spec (M := M) (n := n)
        (cc := cc) (f := f) hcc x qs.2)).2 hsymbol
    exact Bool.and_eq_true.mpr ⟨hStateIndicator, hGuardIndicator⟩
/-- Circuit corresponding to a single branch of the transition function. -/
noncomputable def writeTerm (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (qs : M.state × Bool) : Circuit n :=
  match M.step qs.1 qs.2 with
  | ⟨_, b, _⟩ =>
      if b then
        Circuit.and (cc.state (stateIndex M qs.1))
          (guardSymbol (M := M) (n := n) cc qs.2)
      else
        Circuit.const false

/-- Circuit computing the bit written on the head position during one step. -/
noncomputable def writeBit (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) : Circuit n :=
  Circuit.bigOr ((stateSymbolPairs M).map fun qs =>
    writeTerm (M := M) (n := n) cc qs)

lemma writeBit_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x,
      Circuit.eval (writeBit (M := M) (n := n) cc) x =
        let sym := (f x).tape (f x).head
        let (_, b, _) := M.step (f x).state sym
        b := by
  classical
  intro x
  have hState := hcc.state_eq (x := x)
  have hSymbol :=
    (symbol_spec (M := M) (n := n) (cc := cc) (f := f) hcc x)
  have hState_true :
      Circuit.eval (cc.state (stateIndex M (f x).state)) x = true := by
    have := hState (stateIndex M (f x).state)
    simpa [ConfigCircuits.evalState, stateIndicator_self]
      using this
  have hState_false :
      ∀ {q : M.state}, q ≠ (f x).state →
        Circuit.eval (cc.state (stateIndex M q)) x = false := by
    intro q hneq
    have hx := hState (stateIndex M q)
    have hindex :
        stateIndex M (f x).state ≠ stateIndex M q := by
      intro hcontr
      apply hneq
      have := congrArg (fun i => (stateEquiv M).symm i) hcontr
      simpa [stateIndex, Equiv.symm_apply_apply] using this
    have := stateIndicator_ne (M := M) (n := n) (f x) hindex
    simpa [ConfigCircuits.evalState, this] using hx
  obtain ⟨q', b, move⟩ :=
    M.step (f x).state ((f x).tape (f x).head)
  have hEval :
      Circuit.eval (writeBit (M := M) (n := n) cc) x =
        List.any (stateSymbolPairs M)
          (fun qs =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, b', _⟩ =>
                if b' then
                  Circuit.eval (cc.state (stateIndex M qs.1)) x &&
                    Circuit.eval (guardSymbol (M := M) (n := n) cc qs.2) x
                else
                  false) := by
    simp [writeBit, stateSymbolPairs, Circuit.eval_bigOr_any, List.any_map,
      writeTerm, guardSymbol]
  have hGuard_true :
      Circuit.eval (guardSymbol (M := M) (n := n) cc
        ((f x).tape (f x).head)) x = true := by
    have : cond ((f x).tape (f x).head)
        ((f x).tape (f x).head)
        (! (f x).tape (f x).head) = true := by
      cases (f x).tape (f x).head <;> simp
    simpa [guardSymbol_eval, hSymbol, this]
  have hGuard_false :
      ∀ {b' : Bool}, b' ≠ (f x).tape (f x).head →
        Circuit.eval (guardSymbol (M := M) (n := n) cc b') x = false := by
    intro b' hb'
    cases hb : (f x).tape (f x).head with
    | false =>
        have hb'false : b' = true := by
          cases b' <;> simpa [hb] using hb'
        subst hb'false
        simp [guardSymbol_eval, hSymbol, hb]
    | true =>
        have hb'true : b' = false := by
          cases b' <;> simpa [hb] using hb'
        subst hb'true
        simp [guardSymbol_eval, hSymbol, hb]
  have hPairs := pair_mem_stateSymbolPairs (M := M)
      (f x).state ((f x).tape (f x).head)
  by_cases hb : b
  · have hWitness :
        (let step := M.step (f x).state ((f x).tape (f x).head)
         match step with
         | ⟨_, b', _⟩ =>
             if b' then
               Circuit.eval (cc.state (stateIndex M (f x).state)) x &&
                 Circuit.eval (guardSymbol (M := M) (n := n) cc
                   ((f x).tape (f x).head)) x
             else false) = true := by
        simp [hb, hState_true, hGuard_true]
    have hAny :
        List.any (stateSymbolPairs M)
          (fun qs =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, b', _⟩ =>
                if b' then
                  Circuit.eval (cc.state (stateIndex M qs.1)) x &&
                    Circuit.eval (guardSymbol (M := M) (n := n) cc qs.2) x
                else false) = true := by
      refine (List.any_eq_true).2 ?_
      exact ⟨_, hPairs, by simpa using hWitness⟩
    simpa [hb, hEval, hAny]
  · have hAllFalse :
        ∀ qs ∈ stateSymbolPairs M,
          (let step := M.step qs.1 qs.2
           match step with
           | ⟨_, b', _⟩ =>
               if b' then
                 Circuit.eval (cc.state (stateIndex M qs.1)) x &&
                   Circuit.eval (guardSymbol (M := M) (n := n) cc qs.2) x
               else false) = false := by
      intro qs hqs
      obtain ⟨q, b', rfl⟩ := by
        rcases qs with ⟨q, b'⟩
        exact ⟨q, b', rfl⟩
      by_cases hq : q = (f x).state
      · subst hq
        by_cases hb' : b' = (f x).tape (f x).head
        · subst hb'
          simp [hb, hState_true, hGuard_true]
        · simp [hb, hState_true, hGuard_false hb']
      · have hstate := hState_false (q := q) hq
        simp [hstate]
    have hAnyFalse :
        List.any (stateSymbolPairs M)
          (fun qs =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, b', _⟩ =>
                if b' then
                  Circuit.eval (cc.state (stateIndex M qs.1)) x &&
                    Circuit.eval (guardSymbol (M := M) (n := n) cc qs.2) x
                else false) = false :=
      (List.any_eq_false).2 hAllFalse
    simpa [hb, hEval, hAnyFalse]

/--
Circuit selecting the branch associated with a prescribed head movement. -/
noncomputable def moveTerm (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (m : Move) : Circuit n :=
  match M.step qs.1 qs.2 with
  | ⟨_, _, m'⟩ =>
      if h : m' = m then
        branchIndicator (M := M) (n := n) cc qs
      else
        Circuit.const false

/--
Circuit asserting that the control flow of the current configuration moves
the head according to the supplied command `m`. -/
noncomputable def moveIndicator (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (m : Move) : Circuit n :=
  Circuit.bigOr ((stateSymbolPairs M).map fun qs =>
    moveTerm (M := M) (n := n) cc qs m)

lemma moveIndicator_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x (m : Move),
      Circuit.eval (moveIndicator (M := M) (n := n) cc m) x = true ↔
        let sym := (f x).tape (f x).head
        let (_, _, mv) := M.step (f x).state sym
        mv = m := by
  classical
  intro x m
  have hSpec := branchIndicator_spec (M := M) (n := n)
    (cc := cc) (f := f) hcc
  have hEval :
      Circuit.eval (moveIndicator (M := M) (n := n) cc m) x =
        List.any (stateSymbolPairs M) (fun qs =>
          let step := M.step qs.1 qs.2
          match step with
          | ⟨_, _, mv⟩ =>
              if mv = m then
                Circuit.eval
                  (branchIndicator (M := M) (n := n) cc qs) x
              else
                false) := by
    simp [moveIndicator, Circuit.eval_bigOr_any, moveTerm,
      List.any_map]
  obtain ⟨_, _, mv⟩ :=
    M.step (f x).state ((f x).tape (f x).head)
  constructor
  · intro h
    have :
        ∃ qs ∈ stateSymbolPairs M,
          (let step := M.step qs.1 qs.2
           match step with
           | ⟨_, _, mv⟩ =>
               if mv = m then
                 Circuit.eval
                   (branchIndicator (M := M) (n := n) cc qs) x
               else false) = true :=
      (List.any_eq_true).1 (by simpa [hEval] using h)
    rcases this with ⟨qs, _, hval⟩
    rcases qs with ⟨q, sym⟩
    by_cases hm : (M.step q sym).2.2 = m
    · simp [hm] at hval
      have hBranchTrue :
          Circuit.eval (branchIndicator (M := M) (n := n) cc (q, sym)) x = true :=
        hval
      have hStateSym :=
        (hSpec (x := x) (qs := (q, sym))).1 hBranchTrue
      obtain rfl : q = (f x).state := hStateSym.1.symm
      obtain rfl : sym = (f x).tape (f x).head := hStateSym.2.symm
      have : mv = m := by
        simpa using hm
      exact this
    · simp [hm] at hval
      exact False.elim (Bool.false_ne_true hval)
  · intro hmove
    have hPairs := pair_mem_stateSymbolPairs (M := M)
      (f x).state ((f x).tape (f x).head)
    have hBranch := (hSpec (x := x)
      (qs := ((f x).state, (f x).tape (f x).head))).2
      ⟨rfl, rfl⟩
    have hTermTrue :
        (let step := M.step (f x).state ((f x).tape (f x).head)
         match step with
         | ⟨_, _, mv⟩ =>
             if mv = m then
               Circuit.eval
                 (branchIndicator (M := M) (n := n)
                   cc ((f x).state, (f x).tape (f x).head)) x
             else false) = true := by
      have hm : mv = m := by
        simpa using hmove
      simp [hm, hBranch]
    have hAny :
        List.any (stateSymbolPairs M)
          (fun qs =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, _, mv⟩ =>
                if mv = m then
                  Circuit.eval (branchIndicator (M := M) (n := n) cc qs) x
                else false) = true := by
      refine (List.any_eq_true).2 ?_
      exact ⟨_, hPairs, by simpa using hTermTrue⟩
    simpa [hEval] using hAny

/--
The helper `nextHeadIndex` computes the index obtained after applying a
movement command `m` to a head currently located at `i`.  The definition mirrors
`Configuration.moveHead`, hence the resulting element of `Fin` is directly
usable when reasoning about the next head position.
-/
def nextHeadIndex (M : TM) (n : ℕ)
    (i : Fin (M.tapeLength n)) (m : Move) : Fin (M.tapeLength n) :=
  match m with
  | Move.left  =>
      if h : (i : ℕ) = 0 then
        i
      else
        ⟨(i : ℕ) - 1, by
          have hle : (i : ℕ) - 1 ≤ (i : ℕ) := Nat.sub_le _ _
          exact lt_of_le_of_lt hle i.is_lt⟩
  | Move.stay  => i
  | Move.right =>
      if h : (i : ℕ) + 1 < M.tapeLength n then
        ⟨(i : ℕ) + 1, h⟩
      else
        i

/--
Replacing the configuration head by an explicit index and running
`nextHeadIndex` produces the same result as `Configuration.moveHead`.
-/
lemma nextHeadIndex_spec {M : TM} {n : ℕ}
    (c : TM.Configuration M n) (m : Move) :
    nextHeadIndex (M := M) (n := n) c.head m =
      TM.Configuration.moveHead (c := c) m := by
  cases m <;> rfl

/--
Circuit describing the activation of a control state `q'` after a single step.
The circuit ranges over all `(state, symbol)` pairs and selects those whose
transition leads to `q'`.
-/
noncomputable def stateTerm (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (q' : M.state) : Circuit n :=
  match M.step qs.1 qs.2 with
  | ⟨q'', _, _⟩ =>
      if h : q'' = q' then
        branchIndicator (M := M) (n := n) cc qs
      else
        Circuit.const false

/--
Boolean circuit computing the indicator of the next control state.  The
construction simply folds all relevant `stateTerm`s using a big OR.
-/
noncomputable def nextStateCircuit (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (q' : M.state) : Circuit n :=
  Circuit.bigOr ((stateSymbolPairs M).map fun qs =>
    stateTerm (M := M) (n := n) cc qs q')

/--
Correctness of the state-update circuit.  Evaluating the circuit yields the
indicator telling whether the successor configuration occupies the state `q'`.
-/
lemma nextStateCircuit_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x (q' : M.state),
      Circuit.eval (nextStateCircuit (M := M) (n := n) cc q') x = true ↔
        let sym := (f x).tape (f x).head
        let (q'', _, _) := M.step (f x).state sym
        q'' = q' := by
  classical
  intro x q'
  have hSpec := branchIndicator_spec (M := M) (n := n)
    (cc := cc) (f := f) hcc
  have hEval :
      Circuit.eval (nextStateCircuit (M := M) (n := n) cc q') x =
        List.any (stateSymbolPairs M) (fun qs =>
          let step := M.step qs.1 qs.2
          match step with
          | ⟨q'', _, _⟩ =>
              if q'' = q' then
                Circuit.eval
                  (branchIndicator (M := M) (n := n) cc qs) x
              else false) := by
    simp [nextStateCircuit, Circuit.eval_bigOr_any, List.any_map,
      stateTerm]
  obtain ⟨q'', b, mv⟩ :=
    M.step (f x).state ((f x).tape (f x).head)
  constructor
  · intro h
    have :
        ∃ qs ∈ stateSymbolPairs M,
          (let step := M.step qs.1 qs.2
           match step with
           | ⟨q'', _, _⟩ =>
               if q'' = q' then
                 Circuit.eval
                   (branchIndicator (M := M) (n := n) cc qs) x
               else false) = true :=
      (List.any_eq_true).1 (by simpa [hEval] using h)
    rcases this with ⟨qs, hqs, hval⟩
    rcases qs with ⟨q, sym⟩
    by_cases hstep : (M.step q sym).1 = q'
    · simp [hstep] at hval
      have hBranch :
          Circuit.eval (branchIndicator (M := M) (n := n) cc (q, sym)) x =
            true := hval
      have hInfo := (hSpec (x := x) (qs := (q, sym))).1 hBranch
      obtain rfl : q = (f x).state := hInfo.1.symm
      obtain rfl : sym = (f x).tape (f x).head := hInfo.2.symm
      simpa [hstep]
    · simp [hstep] at hval
      exact False.elim (Bool.false_ne_true hval)
  · intro hstate
    have hPairs := pair_mem_stateSymbolPairs (M := M)
      (f x).state ((f x).tape (f x).head)
    have hBranch := (hSpec (x := x)
      (qs := ((f x).state, (f x).tape (f x).head))).2
      ⟨rfl, rfl⟩
    have hTermTrue :
        (let step := M.step (f x).state ((f x).tape (f x).head)
         match step with
         | ⟨q'', _, _⟩ =>
             if q'' = q' then
               Circuit.eval
                 (branchIndicator (M := M) (n := n)
                   cc ((f x).state, (f x).tape (f x).head)) x
             else false) = true := by
      have hq : q'' = q' := by simpa using hstate
      simp [hq, hBranch]
    have hAny :
        List.any (stateSymbolPairs M)
          (fun qs =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨q'', _, _⟩ =>
                if q'' = q' then
                  Circuit.eval (branchIndicator (M := M) (n := n) cc qs) x
                else false) = true := by
      refine (List.any_eq_true).2 ?_
      exact ⟨_, hPairs, by simpa using hTermTrue⟩
    simpa [hEval] using hAny

/--
Circuit describing one branch of the head update.  The circuit fires exactly
when the current configuration matches `(qs, i)` and the subsequent head index
equals `j`.
-/
noncomputable def headTerm (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (qs : M.state × Bool)
    (i j : Fin (M.tapeLength n)) : Circuit n :=
  match M.step qs.1 qs.2 with
  | ⟨_, _, mv⟩ =>
      if h : nextHeadIndex (M := M) (n := n) i mv = j then
        Circuit.and
          (branchIndicator (M := M) (n := n) cc qs)
          (cc.head i)
      else
        Circuit.const false

/--
Aggregated circuit computing the next head indicator for position `j`.
-/
noncomputable def nextHeadCircuit (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (j : Fin (M.tapeLength n)) : Circuit n :=
  Circuit.bigOr ((stateSymbolPairs M).map fun qs =>
    Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
      headTerm (M := M) (n := n) cc qs i j))

/-- Tape update for a single cell `i`.  The cell keeps its previous value unless
the head points to `i`, in which case the freshly computed bit is written. -/
noncomputable def nextTapeCircuit (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) (i : Fin (M.tapeLength n)) : Circuit n :=
  Circuit.or
    (Circuit.and (cc.head i) (writeBit (M := M) (n := n) cc))
    (Circuit.and (Circuit.not (cc.head i)) (cc.tape i))

/--
Correctness of the head-update circuit: it evaluates to true iff the successor
configuration places the head at index `j`.
-/
lemma nextHeadCircuit_true_iff {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x (j : Fin (M.tapeLength n)),
      Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x = true ↔
        (TM.stepConfig (M := M) (n := n) (f x)).head = j := by
  classical
  intro x j
  have hBranch := branchIndicator_spec (M := M) (n := n)
    (cc := cc) (f := f) hcc
  have hHead := hcc.head_eq (x := x)
  have hEval :
      Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x =
        List.any (stateSymbolPairs M) (fun qs =>
          List.any (tapeIndexList (M := M) n) (fun i =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, _, mv⟩ =>
                if nextHeadIndex (M := M) (n := n) i mv = j then
                  Circuit.eval (branchIndicator (M := M) (n := n) cc qs) x &&
                    Circuit.eval (cc.head i) x
                else false)) := by
    simp [nextHeadCircuit, Circuit.eval_bigOr_any, List.any_map,
      headTerm]
  obtain ⟨q', b', mv⟩ :=
    M.step (f x).state ((f x).tape (f x).head)
  constructor
  · intro h
    have :
        ∃ qs ∈ stateSymbolPairs M,
          List.any (tapeIndexList (M := M) n) (fun i =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, _, mv⟩ =>
                if nextHeadIndex (M := M) (n := n) i mv = j then
                  Circuit.eval (branchIndicator (M := M) (n := n) cc qs) x &&
                    Circuit.eval (cc.head i) x
                else false) = true :=
      (List.any_eq_true).1 (by simpa [hEval] using h)
    rcases this with ⟨qs, hqs, hInner⟩
    obtain ⟨i, hi, hTerm⟩ := (List.any_eq_true).1 hInner
    rcases qs with ⟨q, sym⟩
    by_cases hmove : nextHeadIndex (M := M) (n := n) i
        ((M.step q sym).2.2) = j
    · simp [hmove] at hTerm
      have hBranchTrue :
          Circuit.eval (branchIndicator (M := M) (n := n) cc (q, sym)) x = true :=
        (Bool.and_eq_true.mp hTerm).1
      have hHeadTrue : Circuit.eval (cc.head i) x = true :=
        (Bool.and_eq_true.mp hTerm).2
      have hInfo := (hBranch (x := x) (qs := (q, sym))).1 hBranchTrue
      have hState : (f x).state = q := hInfo.1
      have hSymbol : (f x).tape (f x).head = sym := hInfo.2
      have hIndicator := hHead i
      have hIndicatorTrue : headIndicator (f x) i = true := by
        simpa [ConfigCircuits.evalHead] using
          hHeadTrue.trans hIndicator.symm
      have hHeadIdx : i = (f x).head :=
        (headIndicator_true_iff (M := M) (n := n) (f x) i).1
          hIndicatorTrue
      subst hState
      subst hSymbol
      subst hHeadIdx
      have : nextHeadIndex (M := M) (n := n) (f x).head mv = j := by
        simpa using hmove
      have hStep := nextHeadIndex_spec (M := M) (n := n) (f x) mv
      simpa [TM.stepConfig] using this.trans hStep.symm
    · simp [hmove] at hTerm
      exact False.elim (Bool.false_ne_true hTerm)
  · intro hHeadEq
    have hqs := pair_mem_stateSymbolPairs (M := M)
      (f x).state ((f x).tape (f x).head)
    have hBranchTrue := (hBranch (x := x)
      (qs := ((f x).state, (f x).tape (f x).head))).2 ⟨rfl, rfl⟩
    have hHeadTrue : Circuit.eval (cc.head (f x).head) x = true := by
      simpa [ConfigCircuits.evalHead, headIndicator_self]
        using hHead (f x).head
    have hMove : nextHeadIndex (M := M) (n := n) (f x).head mv = j := by
      have hStep := nextHeadIndex_spec (M := M) (n := n) (f x) mv
      simpa [TM.stepConfig] using hStep ▸ hHeadEq
    have hTermTrue :
        (let step := M.step (f x).state ((f x).tape (f x).head)
         match step with
         | ⟨_, _, mv⟩ =>
             if nextHeadIndex (M := M) (n := n) (f x).head mv = j then
               Circuit.eval
                 (branchIndicator (M := M) (n := n)
                   cc ((f x).state, (f x).tape (f x).head)) x &&
                 Circuit.eval (cc.head (f x).head) x
             else false) = true := by
      have hmove' : nextHeadIndex (M := M) (n := n) (f x).head mv = j := hMove
      simp [hmove', hBranchTrue, hHeadTrue]
    have hAnyInner :
        List.any (tapeIndexList (M := M) n) (fun i =>
          let step := M.step (f x).state ((f x).tape (f x).head)
          match step with
          | ⟨_, _, mv⟩ =>
              if nextHeadIndex (M := M) (n := n) i mv = j then
                Circuit.eval
                  (branchIndicator (M := M) (n := n)
                    cc ((f x).state, (f x).tape (f x).head)) x &&
                  Circuit.eval (cc.head i) x
              else false) = true := by
      refine (List.any_eq_true).2 ?_
      refine ⟨(f x).head, ?_, by simpa using hTermTrue⟩
      simpa [tapeIndexList]
        using List.mem_finRange (f x).head
    have hAnyOuter :
        List.any (stateSymbolPairs M) (fun qs =>
          List.any (tapeIndexList (M := M) n) (fun i =>
            let step := M.step qs.1 qs.2
            match step with
            | ⟨_, _, mv⟩ =>
                if nextHeadIndex (M := M) (n := n) i mv = j then
                  Circuit.eval (branchIndicator (M := M) (n := n) cc qs) x &&
                    Circuit.eval (cc.head i) x
                else false)) = true := by
      refine (List.any_eq_true).2 ?_
      exact ⟨_, hqs, hAnyInner⟩
    simpa [hEval] using hAnyOuter

/-- The head circuits produced by `nextHeadCircuit` agree with the head
indicator of the successor configuration. -/
lemma nextHeadCircuit_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x (j : Fin (M.tapeLength n)),
      Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x =
        headIndicator (TM.stepConfig (M := M) (n := n) (f x)) j := by
  classical
  intro x j
  have hiff := nextHeadCircuit_true_iff (M := M) (n := n)
    (cc := cc) (f := f) hcc x j
  have hind := headIndicator_true_iff (M := M) (n := n)
    (TM.stepConfig (M := M) (n := n) (f x)) j
  by_cases h : (TM.stepConfig (M := M) (n := n) (f x)).head = j
  · have hcircuit : Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x = true :=
      (hiff).2 h
    have hhead : headIndicator (TM.stepConfig (M := M) (n := n) (f x)) j = true :=
      (hind).2 h
    simp [hcircuit, hhead]
  · have hhead : headIndicator (TM.stepConfig (M := M) (n := n) (f x)) j = false :=
      headIndicator_ne (M := M) (n := n)
        (TM.stepConfig (M := M) (n := n) (f x))
        (by simpa [eq_comm] using h)
    have hnot : Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x ≠ true := by
      intro htrue
      have := (hiff).1 htrue
      exact h (by simpa using this)
    have hcircuit : Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x = false := by
      cases hCircuit : Circuit.eval (nextHeadCircuit (M := M) (n := n) cc j) x with
      | false => simpa using hCircuit
      | true =>
          exact False.elim (hnot (by simpa [hCircuit]))
    simp [hcircuit, hhead]

/-- The tape circuits faithfully implement the single-step update. -/
lemma nextTapeCircuit_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ x (i : Fin (M.tapeLength n)),
      Circuit.eval (nextTapeCircuit (M := M) (n := n) cc i) x =
        (TM.stepConfig (M := M) (n := n) (f x)).tape i := by
  classical
  intro x i
  have hHead := hcc.head_eq (x := x) (i := i)
  have hTape := hcc.tape_eq (x := x) (i := i)
  have hWrite := writeBit_spec (M := M) (n := n)
    (cc := cc) (f := f) hcc x
  obtain ⟨q', b', mv⟩ :=
    M.step (f x).state ((f x).tape (f x).head)
  by_cases hEq : i = (f x).head
  · subst hEq
    have hHeadTrue : Circuit.eval (cc.head (f x).head) x = true := by
      simpa [ConfigCircuits.evalHead, headIndicator_self] using hHead
    have hHeadFalse : Circuit.eval (Circuit.not (cc.head (f x).head)) x = false := by
      simpa [Circuit.eval, hHeadTrue]
    have hWriteVal : Circuit.eval (writeBit (M := M) (n := n) cc) x = b' := by
      simpa using hWrite
    have hTapeNew :
        (TM.stepConfig (M := M) (n := n) (f x)).tape (f x).head = b' := by
      simp [TM.stepConfig, Configuration.write_self]
    simp [nextTapeCircuit, Circuit.eval, hHeadTrue, hHeadFalse,
      hWriteVal, hTapeNew]
  · have hHeadFalse : Circuit.eval (cc.head i) x = false := by
      have := headIndicator_ne (M := M) (n := n) (f x)
        (by simpa [eq_comm] using hEq)
      simpa [ConfigCircuits.evalHead] using hHead.trans this
    have hHeadTrue : Circuit.eval (Circuit.not (cc.head i)) x = true := by
      simpa [Circuit.eval, hHeadFalse]
    have hTapeOld :
        (TM.stepConfig (M := M) (n := n) (f x)).tape i = (f x).tape i := by
      have hi : i ≠ (f x).head := by simpa [eq_comm] using hEq
      simp [TM.stepConfig, Configuration.write_other, hi]
    simp [nextTapeCircuit, Circuit.eval, hHeadFalse, hHeadTrue,
      hTape, hTapeOld]

/-- Combine all successor components to obtain the configuration after one
step. -/
noncomputable def stepCircuits (M : TM) {n : ℕ}
    (cc : ConfigCircuits M n) : ConfigCircuits M n where
  tape := fun i => nextTapeCircuit (M := M) (n := n) cc i
  head := fun j => nextHeadCircuit (M := M) (n := n) cc j
  state := fun i =>
    let q := (stateEquiv M).symm i
    nextStateCircuit (M := M) (n := n) cc q

/-- Specification of the combined successor circuits. -/
lemma step_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    Spec (M := M) (n := n) (stepCircuits (M := M) (n := n) cc)
      (fun x => TM.stepConfig (M := M) (n := n) (f x)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    simpa using nextTapeCircuit_spec (M := M) (n := n)
      (cc := cc) (f := f) hcc x i
  · intro x j
    simpa using nextHeadCircuit_spec (M := M) (n := n)
      (cc := cc) (f := f) hcc x j
  · intro x i
    let q := (stateEquiv M).symm i
    have hiff := nextStateCircuit_spec (M := M) (n := n)
      (cc := cc) (f := f) hcc x q
    have hind := stateIndicator_true_iff (M := M) (n := n)
      (TM.stepConfig (M := M) (n := n) (f x)) i
    by_cases hState : (TM.stepConfig (M := M) (n := n) (f x)).state = q
    · have hcircuit :
        Circuit.eval (nextStateCircuit (M := M) (n := n) cc q) x = true :=
        (hiff).2 hState
      have hIndicator :
          stateIndicator M (TM.stepConfig (M := M) (n := n) (f x)) i = true :=
        (hind).2 (by simpa [stateIndex, stateEquiv] using
          congrArg (stateIndex M) hState)
      simp [stepCircuits, stateEquiv, hcircuit, hIndicator]
    · have hIndicatorFalse :
        stateIndicator M (TM.stepConfig (M := M) (n := n) (f x)) i = false := by
        have hineq : stateIndex M (TM.stepConfig (M := M) (n := n) (f x)).state ≠ i := by
          intro hcontr
          apply hState
          have := congrArg ((stateEquiv M).symm) hcontr
          simpa [stateIndex, Equiv.symm_apply_apply] using this
        simpa [stateIndex, stateEquiv]
          using (stateIndicator_ne (M := M) (n := n)
            (TM.stepConfig (M := M) (n := n) (f x)) hineq)
      have hnot :
          Circuit.eval (nextStateCircuit (M := M) (n := n) cc q) x ≠ true := by
        intro htrue
        have := (hiff).1 htrue
        exact hState (by simpa using this)
      have hcircuitFalse :
          Circuit.eval (nextStateCircuit (M := M) (n := n) cc q) x = false := by
        cases hCircuit : Circuit.eval (nextStateCircuit (M := M) (n := n) cc q) x with
        | false => simpa using hCircuit
        | true =>
            exact False.elim (hnot (by simpa [hCircuit]))
      simp [stepCircuits, stateEquiv, hcircuitFalse,
        hIndicatorFalse]

/-- Iterate the step circuits `t` times starting from an initial specification. -/
lemma iterate_spec {M : TM} {n : ℕ}
    {cc : ConfigCircuits M n} {f : Point n → TM.Configuration M n}
    (hcc : Spec (M := M) (n := n) cc f) :
    ∀ t,
      Spec (M := M) (n := n)
        (Nat.iterate (stepCircuits (M := M) (n := n)) t cc)
        (fun x => Nat.iterate (TM.stepConfig (M := M) (n := n)) t (f x)) := by
  classical
  intro t
  induction t with
  | zero => simpa using hcc
  | succ t ih =>
      simpa [Nat.iterate_succ, Function.comp, TM.stepConfig]
        using step_spec (M := M) (n := n)
          (cc := Nat.iterate (stepCircuits (M := M) (n := n)) t cc)
          (f := fun x => Nat.iterate (TM.stepConfig (M := M) (n := n)) t (f x))
          ih

/-- Circuits describing the configuration after `runTime n` steps. -/
noncomputable def runtimeCircuits (M : TM) (n : ℕ) : ConfigCircuits M n :=
  Nat.iterate (stepCircuits (M := M) (n := n)) (M.runTime n)
    (initial (M := M) n)

/-- The runtime circuits match the machine configuration after `runTime n` steps. -/
lemma runtime_spec (M : TM) (n : ℕ) :
    Spec (M := M) (n := n) (runtimeCircuits (M := M) n)
      (fun x => TM.run (M := M) (n := n) x) := by
  classical
  have := iterate_spec (M := M) (n := n)
    (cc := initial (M := M) n)
    (f := fun x => M.initialConfig x)
    (initial_spec (M := M) (n := n)) (M.runTime n)
  simpa [runtimeCircuits, TM.run, TM.runConfig]

/-- Output circuit deciding whether the machine accepts the input. -/
noncomputable def acceptCircuit (M : TM) (n : ℕ) : Circuit n :=
  (runtimeCircuits (M := M) n).state (stateIndex M M.accept)

/-- The acceptance circuit agrees with the machine's decision procedure. -/
lemma acceptCircuit_spec (M : TM) (n : ℕ) :
    ∀ x, Circuit.eval (acceptCircuit (M := M) (n := n)) x =
      TM.accepts (M := M) (n := n) x := by
  classical
  intro x
  have hSpec := runtime_spec (M := M) (n := n)
  have hState := hSpec.state_eq (x := x) (i := stateIndex M M.accept)
  have hIndicator :
      stateIndicator M (TM.run (M := M) (n := n) x) (stateIndex M M.accept) =
        decide ((TM.run (M := M) (n := n) x).state = M.accept) := by
    simp [stateIndicator, stateIndex, stateEquiv, Equiv.apply_symm_apply]
  simpa [acceptCircuit, TM.accepts, hIndicator]

/-!
### Gate-count bookkeeping

The remaining sections develop the quantitative bounds required to show that
the circuits constructed above stay within polynomial size.  We collect a few
combinatorial facts about the helper lists used throughout the construction and
translate them into convenient `Finset` sums.  This allows us to express gate
counts as manageable algebraic expressions.
-/

section GateCount

variable {M : TM} {n : ℕ}

/-- Sum of gate counts for all tape-cell circuits. -/
def tapeGateCount (cc : ConfigCircuits M n) : ℕ :=
  ∑ i : Fin (M.tapeLength n), Circuit.gateCount (cc.tape i)

/-- Sum of gate counts for the head-indicator circuits. -/
def headGateCount (cc : ConfigCircuits M n) : ℕ :=
  ∑ i : Fin (M.tapeLength n), Circuit.gateCount (cc.head i)

/-- Sum of gate counts for state-indicator circuits. -/
def stateGateCount (cc : ConfigCircuits M n) : ℕ :=
  ∑ i : Fin (stateCard M), Circuit.gateCount (cc.state i)

/--
Maximal gate count among the tape-cell circuits.  When the tape is empty the
value defaults to `0`.
-/
def tapeGateSup (cc : ConfigCircuits M n) : ℕ :=
  (Finset.univ : Finset (Fin (M.tapeLength n))).sup
    (fun i => Circuit.gateCount (cc.tape i))

/-- Maximum gate count among the head-indicator circuits. -/
def headGateSup (cc : ConfigCircuits M n) : ℕ :=
  (Finset.univ : Finset (Fin (M.tapeLength n))).sup
    (fun i => Circuit.gateCount (cc.head i))

/-- Maximum gate count among the state-indicator circuits. -/
def stateGateSup (cc : ConfigCircuits M n) : ℕ :=
  (Finset.univ : Finset (Fin (stateCard M))).sup
    (fun i => Circuit.gateCount (cc.state i))

/-- Combined size measure aggregating the three families of circuits. -/
def totalGateCount (cc : ConfigCircuits M n) : ℕ :=
  tapeGateCount (M := M) (n := n) cc +
    headGateCount (M := M) (n := n) cc +
    stateGateCount (M := M) (n := n) cc

/-- Maximal-gate-count bounds packaged in the `GateVector` format. -/
def supGateBounds (cc : ConfigCircuits M n) : GateVector where
  tape := tapeGateSup (M := M) (n := n) cc
  head := headGateSup (M := M) (n := n) cc
  state := stateGateSup (M := M) (n := n) cc

lemma tapeGateCount_nonneg (cc : ConfigCircuits M n) :
    0 ≤ tapeGateCount (M := M) (n := n) cc := by
  exact Nat.zero_le _

lemma headGateCount_nonneg (cc : ConfigCircuits M n) :
    0 ≤ headGateCount (M := M) (n := n) cc := by
  exact Nat.zero_le _

lemma stateGateCount_nonneg (cc : ConfigCircuits M n) :
    0 ≤ stateGateCount (M := M) (n := n) cc := by
  exact Nat.zero_le _

lemma tapeGateSup_nonneg (cc : ConfigCircuits M n) :
    0 ≤ tapeGateSup (M := M) (n := n) cc := by
  unfold tapeGateSup
  exact Nat.zero_le _

lemma headGateSup_nonneg (cc : ConfigCircuits M n) :
    0 ≤ headGateSup (M := M) (n := n) cc := by
  unfold headGateSup
  exact Nat.zero_le _

lemma stateGateSup_nonneg (cc : ConfigCircuits M n) :
    0 ≤ stateGateSup (M := M) (n := n) cc := by
  unfold stateGateSup
  exact Nat.zero_le _

lemma gateCount_tape_le_sup (cc : ConfigCircuits M n)
    (i : Fin (M.tapeLength n)) :
    Circuit.gateCount (cc.tape i) ≤
      tapeGateSup (M := M) (n := n) cc := by
  unfold tapeGateSup
  simpa using
    (Finset.le_sup (Finset.mem_univ i) : _)

lemma gateCount_head_le_sup (cc : ConfigCircuits M n)
    (i : Fin (M.tapeLength n)) :
    Circuit.gateCount (cc.head i) ≤
      headGateSup (M := M) (n := n) cc := by
  unfold headGateSup
  simpa using
    (Finset.le_sup (Finset.mem_univ i) : _)

lemma gateCount_state_le_sup (cc : ConfigCircuits M n)
    (i : Fin (stateCard M)) :
    Circuit.gateCount (cc.state i) ≤
      stateGateSup (M := M) (n := n) cc := by
  unfold stateGateSup
  simpa using
    (Finset.le_sup (Finset.mem_univ i) : _)

lemma tapeGateCount_le_card_mul_sup (cc : ConfigCircuits M n) :
    tapeGateCount (M := M) (n := n) cc ≤
      M.tapeLength n * tapeGateSup (M := M) (n := n) cc := by
  classical
  refine Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin (M.tapeLength n))))
    (f := fun i => Circuit.gateCount (cc.tape i)) ?_ ?_
  · intro i hi
    exact gateCount_tape_le_sup (M := M) (n := n) (cc := cc) i
  · simp [Nat.smul_def, tapeGateCount, tapeGateSup]

lemma headGateCount_le_card_mul_sup (cc : ConfigCircuits M n) :
    headGateCount (M := M) (n := n) cc ≤
      M.tapeLength n * headGateSup (M := M) (n := n) cc := by
  classical
  refine Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin (M.tapeLength n))))
    (f := fun i => Circuit.gateCount (cc.head i)) ?_ ?_
  · intro i hi
    exact gateCount_head_le_sup (M := M) (n := n) (cc := cc) i
  · simp [Nat.smul_def, headGateCount, headGateSup]

lemma stateGateCount_le_card_mul_sup (cc : ConfigCircuits M n) :
    stateGateCount (M := M) (n := n) cc ≤
      stateCard M * stateGateSup (M := M) (n := n) cc := by
  classical
  refine Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin (stateCard M))))
    (f := fun i => Circuit.gateCount (cc.state i)) ?_ ?_
  · intro i hi
    exact gateCount_state_le_sup (M := M) (n := n) (cc := cc) i
  · simp [Nat.smul_def, stateGateCount, stateGateSup]

lemma totalGateCount_le_sup (cc : ConfigCircuits M n) :
    totalGateCount (M := M) (n := n) cc ≤
      M.tapeLength n * tapeGateSup (M := M) (n := n) cc +
        M.tapeLength n * headGateSup (M := M) (n := n) cc +
        stateCard M * stateGateSup (M := M) (n := n) cc := by
  have htape := tapeGateCount_le_card_mul_sup (M := M) (n := n) (cc := cc)
  have hhead := headGateCount_le_card_mul_sup (M := M) (n := n) (cc := cc)
  have hstate := stateGateCount_le_card_mul_sup (M := M) (n := n) (cc := cc)
  have hsum := Nat.add_le_add (Nat.add_le_add htape hhead) hstate
  simpa [totalGateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum

lemma totalGateCount_le_supBounds (cc : ConfigCircuits M n) :
    totalGateCount (M := M) (n := n) cc ≤
      M.tapeLength n * (supGateBounds (M := M) (n := n) cc).tape +
        M.tapeLength n * (supGateBounds (M := M) (n := n) cc).head +
        stateCard M * (supGateBounds (M := M) (n := n) cc).state := by
  simpa [supGateBounds, totalGateCount] using
    totalGateCount_le_sup (M := M) (n := n) (cc := cc)

lemma totalGateCount_nonneg (cc : ConfigCircuits M n) :
    0 ≤ totalGateCount (M := M) (n := n) cc := by
  exact Nat.zero_le _

/-- Tape circuits contribute to the combined gate count in an obvious way. -/
lemma tapeGateCount_le_total (cc : ConfigCircuits M n) :
    tapeGateCount (M := M) (n := n) cc ≤
      totalGateCount (M := M) (n := n) cc := by
  have :=
    Nat.le_add_right
      (tapeGateCount (M := M) (n := n) cc)
      (headGateCount (M := M) (n := n) cc +
        stateGateCount (M := M) (n := n) cc)
  simpa [totalGateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Head-indicator circuits are bounded by the aggregate gate count. -/
lemma headGateCount_le_total (cc : ConfigCircuits M n) :
    headGateCount (M := M) (n := n) cc ≤
      totalGateCount (M := M) (n := n) cc := by
  have :=
    Nat.le_add_left
      (headGateCount (M := M) (n := n) cc)
      (tapeGateCount (M := M) (n := n) cc)
  have := Nat.add_le_add this (Nat.le_refl _)
  simpa [totalGateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/-- State-indicator circuits also sit below the total gate-count budget. -/
lemma stateGateCount_le_total (cc : ConfigCircuits M n) :
    stateGateCount (M := M) (n := n) cc ≤
      totalGateCount (M := M) (n := n) cc := by
  have :=
    Nat.le_add_right
      (stateGateCount (M := M) (n := n) cc)
      (tapeGateCount (M := M) (n := n) cc +
        headGateCount (M := M) (n := n) cc)
  simpa [totalGateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/--
Bounding the gate count of the `symbol` circuit purely in terms of the
component-wise suprema.  The statement will be the basic building block in the
forthcoming sup-based size analysis.  The dependence on `tapeLength` reflects
the fact that `symbol` inspects every tape cell. -/
lemma gateCount_symbol_le_sup (cc : ConfigCircuits M n) :
    Circuit.gateCount (symbol (M := M) cc) ≤
      1 + M.tapeLength n +
        M.tapeLength n *
          (tapeGateSup (M := M) (n := n) cc +
            headGateSup (M := M) (n := n) cc + 1) := by
  classical
  -- Each summand in the big-OR is bounded by the sum of the suprema plus one
  -- additional gate coming from the conjunction node.
  have hBound : ∀ i ∈ tapeIndexList (M := M) n,
      Circuit.gateCount (Circuit.and (cc.head i) (cc.tape i)) ≤
        tapeGateSup (M := M) (n := n) cc +
          headGateSup (M := M) (n := n) cc + 1 := by
    intro i hi
    have hHead :
        Circuit.gateCount (cc.head i) ≤
          headGateSup (M := M) (n := n) cc :=
      gateCount_head_le_sup (M := M) (n := n) (cc := cc) i
    have hTape :
        Circuit.gateCount (cc.tape i) ≤
          tapeGateSup (M := M) (n := n) cc :=
      gateCount_tape_le_sup (M := M) (n := n) (cc := cc) i
    -- The gate count of an `and`-gate is additive in the arguments, with one
    -- extra node for the gate itself.
    have := Nat.add_le_add hHead (Nat.add_le_add hTape (Nat.le_refl 1))
    simpa [Circuit.gateCount] using this
  -- Control the accumulated gate count of the list passed to `bigOr`.
  have hList :
      Circuit.listGateCount
          ((tapeIndexList (M := M) n).map fun i =>
              Circuit.and (cc.head i) (cc.tape i)) ≤
        (tapeIndexList (M := M) n).length *
          (tapeGateSup (M := M) (n := n) cc +
            headGateSup (M := M) (n := n) cc + 1) :=
    listGateCount_map_le_const _ _ _ hBound
  have hLen := length_tapeIndexList (M := M) (n := n)
  -- Finally apply the generic `bigOr` estimate and substitute the concrete
  -- length of `tapeIndexList`.
  have hBigOr := Circuit.gateCount_bigOr_le
      ((tapeIndexList (M := M) n).map fun i =>
          Circuit.and (cc.head i) (cc.tape i))
  have hCombined :
      1 + (tapeIndexList (M := M) n).length +
          Circuit.listGateCount
              ((tapeIndexList (M := M) n).map fun i =>
                  Circuit.and (cc.head i) (cc.tape i)) ≤
        1 + (tapeIndexList (M := M) n).length +
          (tapeIndexList (M := M) n).length *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1) := by
    -- Add the list-length and the initial constant to the estimate obtained
    -- from `listGateCount_map_le_const`.
    have := Nat.add_le_add_left hList
      ((tapeIndexList (M := M) n).length)
    have := Nat.add_le_add_left this 1
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  -- Substitute the length of `tapeIndexList` and combine all inequalities.
  have hFinal := Nat.le_trans hBigOr hCombined
  simpa [hLen, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hFinal

lemma gateCount_guardSymbol_le_sup (cc : ConfigCircuits M n) (b : Bool) :
    Circuit.gateCount (guardSymbol (M := M) (n := n) cc b) ≤
      2 + M.tapeLength n +
        M.tapeLength n *
          (tapeGateSup (M := M) (n := n) cc +
            headGateSup (M := M) (n := n) cc + 1) := by
  classical
  set L := M.tapeLength n
  have hSymbol := gateCount_symbol_le_sup (M := M) (n := n) (cc := cc)
  have hSymbol_succ :
      Circuit.gateCount (symbol (M := M) (n := n) cc) + 1 ≤
        (Nat.succ
          (1 + L + L *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1))) :=
    by
      have := Nat.succ_le_succ hSymbol
      simpa [Nat.succ_eq_add_one]
  cases b with
  | true =>
      have hstep := Nat.le_trans hSymbol (Nat.le_succ _)
      simpa [guardSymbol, L, Nat.succ_eq_add_one, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
        using hstep
  | false =>
      have hnot :
          Circuit.gateCount
              (Circuit.not (symbol (M := M) (n := n) cc)) =
            Circuit.gateCount (symbol (M := M) (n := n) cc) + 1 := by
        simp [Circuit.gateCount]
      have := hSymbol_succ
      simpa [guardSymbol, hnot, L, Nat.succ_eq_add_one, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
        using this

lemma gateCount_branchIndicator_le_sup
    (cc : ConfigCircuits M n) (qs : M.state × Bool) :
    Circuit.gateCount (branchIndicator (M := M) (n := n) cc qs) ≤
      stateGateSup (M := M) (n := n) cc +
        (3 + M.tapeLength n +
          M.tapeLength n *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1)) := by
  classical
  have hState := gateCount_state_le_sup (M := M) (n := n)
      (cc := cc) (i := stateIndex M qs.1)
  have hGuard := gateCount_guardSymbol_le_sup (M := M) (n := n)
      (cc := cc) (b := qs.2)
  have hsum :=
    Nat.add_le_add hState
      (Nat.add_le_add hGuard (Nat.le_refl 1))
  simpa [branchIndicator, Circuit.gateCount, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]
    using hsum

lemma gateCount_writeTerm_le_sup
    (cc : ConfigCircuits M n) (qs : M.state × Bool) :
    Circuit.gateCount (writeTerm (M := M) (n := n) cc qs) ≤
      stateGateSup (M := M) (n := n) cc +
        (3 + M.tapeLength n +
          M.tapeLength n *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1)) := by
  classical
  obtain ⟨_, b, _⟩ := M.step qs.1 qs.2
  cases hb : b with
  | false =>
      have hconst : Circuit.gateCount (Circuit.const false : Circuit n) = 1 := by
        simp
      have hpos :
          1 ≤ stateGateSup (M := M) (n := n) cc +
                (3 + M.tapeLength n +
                  M.tapeLength n *
                    (tapeGateSup (M := M) (n := n) cc +
                      headGateSup (M := M) (n := n) cc + 1)) := by
        have : 1 ≤ 3 := by decide
        exact
          this.trans
            (Nat.le_add_left _
              (stateGateSup (M := M) (n := n) cc +
                M.tapeLength n *
                  (tapeGateSup (M := M) (n := n) cc +
                    headGateSup (M := M) (n := n) cc + 1)))
      simpa [writeTerm, hb, hconst]
        using hpos
  | true =>
      simpa [writeTerm, hb]
        using gateCount_branchIndicator_le_sup
          (M := M) (n := n) (cc := cc) (qs := qs)

lemma gateCount_writeBit_le_sup (cc : ConfigCircuits M n) :
    Circuit.gateCount (writeBit (M := M) (n := n) cc) ≤
      1 + 2 * stateCard M +
        (2 * stateCard M) *
          (stateGateSup (M := M) (n := n) cc +
            (3 + M.tapeLength n +
              M.tapeLength n *
                (tapeGateSup (M := M) (n := n) cc +
                  headGateSup (M := M) (n := n) cc + 1))) := by
  classical
  have hlen := length_stateSymbolPairs (M := M)
  have hterm : ∀ qs ∈ stateSymbolPairs M,
      Circuit.gateCount
          (writeTerm (M := M) (n := n) cc qs) ≤
        stateGateSup (M := M) (n := n) cc +
          (3 + M.tapeLength n +
            M.tapeLength n *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1)) := by
    intro qs hqs
    exact gateCount_writeTerm_le_sup (M := M) (n := n)
      (cc := cc) (qs := qs)
  have hlist :=
    listGateCount_map_le_const
      (l := stateSymbolPairs M)
      (f := fun qs => writeTerm (M := M) (n := n) cc qs)
      (B :=
        stateGateSup (M := M) (n := n) cc +
          (3 + M.tapeLength n +
            M.tapeLength n *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1))) hterm
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        writeTerm (M := M) (n := n) cc qs)
  have htotal :=
    Nat.le_trans hbig
      (Nat.add_le_add_left hlist (1 + (stateSymbolPairs M).length))
  simpa [writeBit, List.map_const, hlen, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using htotal

/-- Supremum-style bound for the auxiliary movement branch.  The constant is
chosen slightly generously so that both the active-branch and the
always-false cases are covered uniformly. -/
lemma gateCount_moveTerm_le_sup
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (m : Move) :
    Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) ≤
      stateGateSup (M := M) (n := n) cc +
        (4 + M.tapeLength n +
          M.tapeLength n *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1)) := by
  classical
  set L := M.tapeLength n
  set B := tapeGateSup (M := M) (n := n) cc +
    headGateSup (M := M) (n := n) cc + 1
  obtain ⟨_, _, mv⟩ := M.step qs.1 qs.2
  by_cases hm : mv = m
  · have hbranch :=
      gateCount_branchIndicator_le_sup (M := M) (n := n)
        (cc := cc) (qs := qs)
    have hmono :
        stateGateSup (M := M) (n := n) cc +
            (3 + L + L * B) ≤
          stateGateSup (M := M) (n := n) cc +
            (4 + L + L * B) := by
      have : 3 + L + L * B ≤ 4 + L + L * B := by
        exact Nat.le_add_left _ 1
      exact Nat.add_le_add_left this _
    have := hbranch.trans hmono
    simpa [moveTerm, hm, L, B]
      using this
  · have hconst : Circuit.gateCount (Circuit.const false : Circuit n) = 1 := by
      simp
    have hfour : 1 ≤ 4 := by decide
    have hinner : 1 ≤ 4 + L + L * B := by
      have hle : 4 ≤ 4 + L + L * B := Nat.le_add_right _ _
      exact hfour.trans hle
    have hfinal :
        1 ≤ stateGateSup (M := M) (n := n) cc +
            (4 + L + L * B) := by
      have hpad := Nat.le_add_left (4 + L + L * B)
        (stateGateSup (M := M) (n := n) cc)
      exact hinner.trans hpad
    have hfalse :
        Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) = 1 := by
      simpa [moveTerm, hm, hconst]
    simpa [hfalse, L, B] using hfinal

/-- Supremum bound for the list of movement branches appearing in
`moveIndicator`. -/
lemma listGateCount_moveTerm_le_sup
    (cc : ConfigCircuits M n) (m : Move) :
    Circuit.listGateCount
        ((stateSymbolPairs M).map fun qs =>
          moveTerm (M := M) (n := n) cc qs m) ≤
      (2 * stateCard M) *
        (stateGateSup (M := M) (n := n) cc +
          (4 + M.tapeLength n +
            M.tapeLength n *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1))) := by
  classical
  have hbound : ∀ qs ∈ stateSymbolPairs M,
      Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) ≤
        stateGateSup (M := M) (n := n) cc +
          (4 + M.tapeLength n +
            M.tapeLength n *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1)) := by
    intro qs hqs
    exact gateCount_moveTerm_le_sup (M := M) (n := n)
      (cc := cc) (qs := qs) (m := m)
  have hlen := length_stateSymbolPairs (M := M)
  have :=
    listGateCount_map_le_const
      (l := stateSymbolPairs M)
      (f := fun qs => moveTerm (M := M) (n := n) cc qs m)
      (B := stateGateSup (M := M) (n := n) cc +
        (4 + M.tapeLength n +
          M.tapeLength n *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1))) hbound
  simpa [hlen, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

/-- Movement indicators inherit the supremum control from the individual
branches via the `bigOr` construction. -/
lemma gateCount_moveIndicator_le_sup (cc : ConfigCircuits M n) (m : Move) :
    Circuit.gateCount (moveIndicator (M := M) (n := n) cc m) ≤
      1 + 2 * stateCard M +
        (2 * stateCard M) *
          (stateGateSup (M := M) (n := n) cc +
            (4 + M.tapeLength n +
              M.tapeLength n *
                (tapeGateSup (M := M) (n := n) cc +
                  headGateSup (M := M) (n := n) cc + 1))) := by
  classical
  have hlen : ((stateSymbolPairs M).map fun _ => ()).length =
      2 * stateCard M := by
    simpa using length_stateSymbolPairs (M := M)
  have hlist := listGateCount_moveTerm_le_sup (M := M) (n := n)
      (cc := cc) (m := m)
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        moveTerm (M := M) (n := n) cc qs m)
  refine hbig.trans ?_
  have := Nat.add_le_add_left hlist (1 + (stateSymbolPairs M).length)
  simpa [moveIndicator, List.map_const, hlen, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Supremum bound for an individual head-update branch. -/
lemma gateCount_headTerm_le_sup (cc : ConfigCircuits M n)
    (qs : M.state × Bool) (i j : Fin (M.tapeLength n)) :
    Circuit.gateCount (headTerm (M := M) (n := n) cc qs i j) ≤
      stateGateSup (M := M) (n := n) cc +
        headGateSup (M := M) (n := n) cc +
        (4 + M.tapeLength n +
          M.tapeLength n *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1)) := by
  classical
  set L := M.tapeLength n
  set B := tapeGateSup (M := M) (n := n) cc +
    headGateSup (M := M) (n := n) cc + 1
  obtain ⟨_, _, mv⟩ := M.step qs.1 qs.2
  by_cases hmove : nextHeadIndex (M := M) (n := n) i mv = j
  · have hbranch :=
      gateCount_branchIndicator_le_sup (M := M) (n := n)
        (cc := cc) (qs := qs)
    have hmono :
        stateGateSup (M := M) (n := n) cc +
            (3 + L + L * B) ≤
          stateGateSup (M := M) (n := n) cc +
            (4 + L + L * B) := by
      have : 3 + L + L * B ≤ 4 + L + L * B := by
        exact Nat.le_add_left _ 1
      exact Nat.add_le_add_left this _
    have := hbranch.trans hmono
    have hhead := gateCount_head_le_sup (M := M) (n := n)
      (cc := cc) (i := i)
    have hsum :=
      Nat.add_le_add this (Nat.add_le_add hhead (Nat.le_refl 1))
    simpa [headTerm, hmove, L, B, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
      using hsum
  · have hconst : Circuit.gateCount (Circuit.const false : Circuit n) = 1 := by
      simp
    have hfour : 1 ≤ 4 := by decide
    have hinner : 1 ≤ 4 + L + L * B := by
      have hle : 4 ≤ 4 + L + L * B := Nat.le_add_right _ _
      exact hfour.trans hle
    have hfinal :
        1 ≤ stateGateSup (M := M) (n := n) cc +
            headGateSup (M := M) (n := n) cc +
            (4 + L + L * B) := by
      have hpad :=
        Nat.le_add_left
          (headGateSup (M := M) (n := n) cc + (4 + L + L * B))
          (stateGateSup (M := M) (n := n) cc)
      have hpad' := Nat.le_add_left (4 + L + L * B)
        (headGateSup (M := M) (n := n) cc)
      exact hinner.trans (hpad.trans hpad')
    have hfalse :
        Circuit.gateCount (headTerm (M := M) (n := n) cc qs i j) = 1 := by
      simpa [headTerm, hmove, hconst]
    simpa [hfalse, L, B, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
      using hfinal

/-- Supremum bound for the lists of head-update branches over all tape indices. -/
lemma listGateCount_headTerm_le_sup (cc : ConfigCircuits M n)
    (qs : M.state × Bool) (j : Fin (M.tapeLength n)) :
    Circuit.listGateCount
        ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j) ≤
      M.tapeLength n *
        (stateGateSup (M := M) (n := n) cc +
          headGateSup (M := M) (n := n) cc +
          (4 + M.tapeLength n +
            M.tapeLength n *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1))) := by
  classical
  have hbound : ∀ i ∈ tapeIndexList (M := M) n,
      Circuit.gateCount
          (headTerm (M := M) (n := n) cc qs i j) ≤
        stateGateSup (M := M) (n := n) cc +
          headGateSup (M := M) (n := n) cc +
          (4 + M.tapeLength n +
            M.tapeLength n *
              (tapeGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc + 1)) := by
    intro i hi
    exact gateCount_headTerm_le_sup (M := M) (n := n)
      (cc := cc) (qs := qs) (i := i) (j := j)
  have hlen := length_tapeIndexList (M := M) (n := n)
  have :=
    listGateCount_map_le_const
      (l := tapeIndexList (M := M) n)
      (f := fun i => headTerm (M := M) (n := n) cc qs i j)
      (B := stateGateSup (M := M) (n := n) cc +
        headGateSup (M := M) (n := n) cc +
        (4 + M.tapeLength n +
          M.tapeLength n *
            (tapeGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc + 1))) hbound
  simpa [tapeIndexList, hlen, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]
    using this

/-- Supremum version of the bound for the inner big-OR in the head-update
construction. -/
lemma gateCount_headBranch_le_sup (cc : ConfigCircuits M n)
    (qs : M.state × Bool) (j : Fin (M.tapeLength n)) :
    Circuit.gateCount
        (Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j)) ≤
      1 + M.tapeLength n +
        M.tapeLength n *
          (stateGateSup (M := M) (n := n) cc +
            headGateSup (M := M) (n := n) cc +
            (4 + M.tapeLength n +
              M.tapeLength n *
                (tapeGateSup (M := M) (n := n) cc +
                  headGateSup (M := M) (n := n) cc + 1))) := by
  classical
  have hlen := length_tapeIndexList (M := M) (n := n)
  have hlist := listGateCount_headTerm_le_sup (M := M) (n := n)
      (cc := cc) (qs := qs) (j := j)
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((tapeIndexList (M := M) n).map fun i =>
        headTerm (M := M) (n := n) cc qs i j)
  refine hbig.trans ?_
  have := Nat.add_le_add_left hlist (1 + (tapeIndexList (M := M) n).length)
  simpa [tapeIndexList, hlen, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Supremum bound for the full head-update circuit selecting position `j`. -/
lemma gateCount_nextHeadCircuit_le_sup (cc : ConfigCircuits M n)
    (j : Fin (M.tapeLength n)) :
    Circuit.gateCount (nextHeadCircuit (M := M) (n := n) cc j) ≤
      1 + 2 * stateCard M +
        (2 * stateCard M) *
          (1 + M.tapeLength n +
            M.tapeLength n *
              (stateGateSup (M := M) (n := n) cc +
                headGateSup (M := M) (n := n) cc +
                (4 + M.tapeLength n +
                  M.tapeLength n *
                    (tapeGateSup (M := M) (n := n) cc +
                      headGateSup (M := M) (n := n) cc + 1)))) := by
  classical
  have hlen := length_stateSymbolPairs (M := M)
  have hbound : ∀ qs ∈ stateSymbolPairs M,
      Circuit.gateCount
          (Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
            headTerm (M := M) (n := n) cc qs i j)) ≤
        1 + M.tapeLength n +
          M.tapeLength n *
            (stateGateSup (M := M) (n := n) cc +
              headGateSup (M := M) (n := n) cc +
              (4 + M.tapeLength n +
                M.tapeLength n *
                  (tapeGateSup (M := M) (n := n) cc +
                    headGateSup (M := M) (n := n) cc + 1))) := by
    intro qs hqs
    exact gateCount_headBranch_le_sup (M := M) (n := n)
      (cc := cc) (qs := qs) (j := j)
  have hlist :=
    listGateCount_map_le_const
      (l := stateSymbolPairs M)
      (f := fun qs =>
        Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j))
      (B := 1 + M.tapeLength n +
        M.tapeLength n *
          (stateGateSup (M := M) (n := n) cc +
            headGateSup (M := M) (n := n) cc +
            (4 + M.tapeLength n +
              M.tapeLength n *
                (tapeGateSup (M := M) (n := n) cc +
                  headGateSup (M := M) (n := n) cc + 1)))) hbound
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j))
  refine hbig.trans ?_
  have := Nat.add_le_add_left hlist (1 + (stateSymbolPairs M).length)
  simpa [nextHeadCircuit, List.map_const, hlen, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using this

end GateCount

section GateCountInequalities

variable {M : TM} {n : ℕ}

open scoped BigOperators

open Finset

/-- Each tape circuit contributes at most the total tape gate count. -/
lemma gateCount_tape_le (cc : ConfigCircuits M n)
    (i : Fin (M.tapeLength n)) :
    Circuit.gateCount (cc.tape i) ≤
      tapeGateCount (M := M) (n := n) cc := by
  classical
  have hnonneg : ∀ j : Fin (M.tapeLength n),
      0 ≤ Circuit.gateCount (cc.tape j) := fun _ => Nat.zero_le _
  have : Circuit.gateCount (cc.tape i) ≤
      ∑ j : Fin (M.tapeLength n), Circuit.gateCount (cc.tape j) := by
    simpa [tapeGateCount]
      using
        (Finset.single_le_sum
          (f := fun j : Fin (M.tapeLength n) =>
            Circuit.gateCount (cc.tape j))
          (by intro j _; exact hnonneg j)
          (Finset.mem_universe i))
  simpa [tapeGateCount] using this

/-- Each head circuit is bounded by the aggregate head gate count. -/
lemma gateCount_head_le (cc : ConfigCircuits M n)
    (i : Fin (M.tapeLength n)) :
    Circuit.gateCount (cc.head i) ≤
      headGateCount (M := M) (n := n) cc := by
  classical
  have hnonneg : ∀ j : Fin (M.tapeLength n),
      0 ≤ Circuit.gateCount (cc.head j) := fun _ => Nat.zero_le _
  have : Circuit.gateCount (cc.head i) ≤
      ∑ j : Fin (M.tapeLength n), Circuit.gateCount (cc.head j) := by
    simpa [headGateCount]
      using
        (Finset.single_le_sum
          (f := fun j : Fin (M.tapeLength n) =>
            Circuit.gateCount (cc.head j))
          (by intro j _; exact hnonneg j)
          (Finset.mem_universe i))
  simpa [headGateCount] using this

/-- Each state circuit is bounded by the aggregate state gate count. -/
lemma gateCount_state_le (cc : ConfigCircuits M n)
    (i : Fin (stateCard M)) :
    Circuit.gateCount (cc.state i) ≤
      stateGateCount (M := M) (n := n) cc := by
  classical
  have hnonneg : ∀ j : Fin (stateCard M),
      0 ≤ Circuit.gateCount (cc.state j) := fun _ => Nat.zero_le _
  have : Circuit.gateCount (cc.state i) ≤
      ∑ j : Fin (stateCard M), Circuit.gateCount (cc.state j) := by
    simpa [stateGateCount]
      using
        (Finset.single_le_sum
          (f := fun j : Fin (stateCard M) =>
            Circuit.gateCount (cc.state j))
          (by intro j _; exact hnonneg j)
          (Finset.mem_universe i))
  simpa [stateGateCount] using this

end GateCountInequalities

section ListBounds

variable {M : TM} {n : ℕ}

open scoped BigOperators

/-- If each element of a list maps to a circuit bounded by `B`, then the total
gate count of the mapped list is bounded by `length * B`.  The statement is a
simple consequence of the recursive description of `Circuit.listGateCount`. -/
lemma listGateCount_map_le_const {α : Type _} (l : List α) (f : α → Circuit n)
    (B : ℕ) (hB : ∀ a ∈ l, Circuit.gateCount (f a) ≤ B) :
    Circuit.listGateCount (l.map f) ≤ l.length * B := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hB a (by simp)
      have hrest : ∀ b ∈ l, Circuit.gateCount (f b) ≤ B := by
        intro b hb
        exact hB b (by simp [hb])
      have := ih hrest
      have hsum := Nat.add_le_add ha this
      have hmul : l.length * B + B = (Nat.succ l.length) * B := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_mul]
      simpa [Circuit.listGateCount, List.map_cons, List.length_cons, hmul,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hsum

end ListBounds

section GateCount

variable {M : TM} {n : ℕ}

open scoped BigOperators

namespace Circuit

/--
`listGateCount` of the `finRange` enumeration coincides with the corresponding
`Finset` sum.  The statement is tailored to the circuit constructions used in
this file and lets us transfer arithmetic lemmas on big sums to list-based
descriptions such as `tapeIndexList`.
-/
lemma listGateCount_map_finRange {k : ℕ} {n : ℕ}
    (f : Fin k → Circuit n) :
    listGateCount ((List.finRange k).map f) =
      ∑ i : Fin k, gateCount (f i) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      have hsucc :
          (List.finRange (Nat.succ k)).map f =
            f 0 :: (List.finRange k).map (fun i : Fin k => f i.succ) := by
        classical
        -- expand the `finRange` recursion explicitly to keep the rewrite
        -- manageable for later simp-steps.
        simpa [List.finRange_succ, List.map_cons, List.map_map,
          Function.comp] using (List.map_finRange_succ (fun i => f i))
      -- The inductive hypothesis applies to the tail which enumerates all
      -- successors.  The corresponding sum splits according to
      -- `Fin.sum_univ_succ`.
      have hsum :=
        Fin.sum_univ_succ (fun i : Fin (Nat.succ k) => gateCount (f i))
      -- Unfold the definition step by step; the helper lemma above packages
      -- the required rewrites so that `simp` can finish the algebra.
      simpa [listGateCount, hsucc, ih, Fin.sum_univ_succ]
        using hsum

end Circuit

lemma tapeGateCount_initial (M : TM) (n : ℕ) :
    tapeGateCount (M := M) (n := n) (initial (M := M) n) = M.tapeLength n := by
  classical
  have hOne : ∀ i : Fin (M.tapeLength n),
      Circuit.gateCount ((initial (M := M) n).tape i) = 1 := by
    intro i
    by_cases h : (i : ℕ) < n
    · simp [ConfigCircuits.initial, h]
    · simp [ConfigCircuits.initial, h]
  have hconst :=
    (Finset.sum_const_nat (s := (Finset.universe : Finset (Fin (M.tapeLength n))))
      (a := 1))
  have hcard :
      ((Finset.universe : Finset (Fin (M.tapeLength n))).card * 1) =
        M.tapeLength n := by
    classical
    simpa using (Finset.card_universe (Fin (M.tapeLength n)))
  simpa [tapeGateCount, hOne, hcard] using hconst

lemma headGateCount_initial (M : TM) (n : ℕ) :
    headGateCount (M := M) (n := n) (initial (M := M) n) = M.tapeLength n := by
  classical
  have hOne : ∀ i : Fin (M.tapeLength n),
      Circuit.gateCount ((initial (M := M) n).head i) = 1 := by
    intro i
    by_cases h : i = ⟨0, by
        have : (0 : ℕ) < n + M.runTime n + 1 := Nat.succ_pos _
        simpa [TM.tapeLength] using this⟩
    · simp [ConfigCircuits.initial, h]
    · simp [ConfigCircuits.initial, h]
  have hconst :=
    (Finset.sum_const_nat (s := (Finset.universe : Finset (Fin (M.tapeLength n))))
      (a := 1))
  have hcard :
      ((Finset.universe : Finset (Fin (M.tapeLength n))).card * 1) =
        M.tapeLength n := by
    classical
    simpa using (Finset.card_universe (Fin (M.tapeLength n)))
  simpa [headGateCount, hOne, hcard] using hconst

lemma stateGateCount_initial (M : TM) (n : ℕ) :
    stateGateCount (M := M) (n := n) (initial (M := M) n) = stateCard M := by
  classical
  have hOne : ∀ i : Fin (stateCard M),
      Circuit.gateCount ((initial (M := M) n).state i) = 1 := by
    intro i
    by_cases h : i = stateIndex M M.start
    · simp [ConfigCircuits.initial, h]
    · simp [ConfigCircuits.initial, h]
  have hconst :=
    (Finset.sum_const_nat (s := (Finset.universe : Finset (Fin (stateCard M))))
      (a := 1))
  have hcard :
      ((Finset.universe : Finset (Fin (stateCard M))).card * 1) = stateCard M := by
    classical
    simpa [stateCard] using (Finset.card_universe (Fin (stateCard M)))
  simpa [stateGateCount, hOne, hcard] using hconst

lemma totalGateCount_initial (M : TM) (n : ℕ) :
    totalGateCount (M := M) (n := n) (initial (M := M) n) =
      2 * M.tapeLength n + stateCard M := by
  classical
  simp [totalGateCount, tapeGateCount_initial, headGateCount_initial,
    stateGateCount_initial, two_mul, add_comm, add_left_comm, add_assoc]

end GateCount

section GateBounds

variable {M : TM} {n : ℕ}

open scoped BigOperators

lemma listGateCount_symbol_eq (cc : ConfigCircuits M n) :
    Circuit.listGateCount
        ((tapeIndexList (M := M) n).map fun i =>
          Circuit.and (cc.head i) (cc.tape i)) =
      headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc + M.tapeLength n := by
  classical
  have hlist := Circuit.listGateCount_map_finRange
      (k := M.tapeLength n) (n := n)
      (f := fun i => Circuit.and (cc.head i) (cc.tape i))
  have hsum :
      ∑ i : Fin (M.tapeLength n),
          Circuit.gateCount (Circuit.and (cc.head i) (cc.tape i)) =
        headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc + M.tapeLength n := by
    have hcongr := Finset.sum_congr rfl
      (fun i _ => by simp [Circuit.gateCount])
    have hsplit :=
      Finset.sum_add_distrib
        (s := (Finset.universe : Finset (Fin (M.tapeLength n))))
          (f := fun i => Circuit.gateCount (cc.head i))
          (g := fun i => Circuit.gateCount (cc.tape i) + 1)
    have hconst :=
      (Finset.sum_const_nat (s :=
        (Finset.universe : Finset (Fin (M.tapeLength n)))) (a := 1))
    have hcard :
        ((Finset.universe : Finset (Fin (M.tapeLength n))).card * 1) =
          M.tapeLength n := by
      simpa using (Finset.card_universe (Fin (M.tapeLength n)))
    have hsplit' :=
      Finset.sum_add_distrib
        (s := (Finset.universe : Finset (Fin (M.tapeLength n))))
          (f := fun i => Circuit.gateCount (cc.tape i))
          (g := fun _ => 1)
    simpa [headGateCount, tapeGateCount, hcongr, hsplit, hsplit', hconst,
      hcard, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hsum
  simpa [tapeIndexList, hsum]
    using hlist

/-
Upper bound for the gate count of the `symbol` circuit.  The inequality is the
first stepping stone towards a polynomial bound for the whole simulation.
-/
lemma gateCount_symbol_le (cc : ConfigCircuits M n) :
    Circuit.gateCount (symbol (M := M) (n := n) cc) ≤
      headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 1) := by
  classical
  have hsum := listGateCount_symbol_eq (M := M) (n := n) cc
  have hbound :=
    Circuit.gateCount_bigOr_le
      ((tapeIndexList (M := M) n).map fun i =>
        Circuit.and (cc.head i) (cc.tape i))
  have hlen := length_tapeIndexList (M := M) (n := n)
  simpa [symbol, tapeIndexList, hsum, hlen, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hbound

/--
`guardSymbol` is essentially `symbol` plus a potential negation; consequently
its gate count enjoys a closely related bound.
-/
lemma gateCount_guardSymbol_le (cc : ConfigCircuits M n) (b : Bool) :
    Circuit.gateCount (guardSymbol (M := M) (n := n) cc b) ≤
      headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 2) := by
  classical
  cases b with
  | false =>
      have := gateCount_symbol_le (M := M) (n := n) cc
      have h := Nat.succ_le_succ this
      simpa [guardSymbol, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h
  | true =>
      simpa [guardSymbol] using gateCount_symbol_le (M := M) (n := n) cc

/--
Bounding the gate count of `branchIndicator`: the contribution from the state
indicator appears explicitly while the remaining terms are absorbed via the
previous lemma.
-/
lemma gateCount_branchIndicator_le
    (cc : ConfigCircuits M n) (qs : M.state × Bool) :
    Circuit.gateCount (branchIndicator (M := M) (n := n) cc qs) ≤
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 3) := by
  classical
  have hguard := gateCount_guardSymbol_le (M := M) (n := n) cc qs.2
  have :=
    Nat.add_le_add_right hguard (Circuit.gateCount (cc.state (stateIndex M qs.1)))
  simpa [branchIndicator, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/--
Every write-term is either a constant-false circuit or the branch indicator.
The inequality therefore follows immediately from the previous bound.
-/
lemma gateCount_writeTerm_le
    (cc : ConfigCircuits M n) (qs : M.state × Bool) :
    Circuit.gateCount (writeTerm (M := M) (n := n) cc qs) ≤
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
  classical
  obtain ⟨_, b, _⟩ := M.step qs.1 qs.2
  cases hb : b with
  | false =>
      have hpos : 1 ≤ 2 * M.tapeLength n + 4 := by
        have : 1 ≤ 4 := by decide
        exact this.trans (Nat.le_add_left _ _)
      have hsum : 2 * M.tapeLength n + 4 ≤
          Circuit.gateCount (cc.state (stateIndex M qs.1)) +
            headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 4) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using Nat.le_add_left (2 * M.tapeLength n + 4)
            (Circuit.gateCount (cc.state (stateIndex M qs.1)) +
              headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc)
      have hle := hpos.trans hsum
      simpa [writeTerm, hb, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hle
  | true =>
      have hbranch := gateCount_branchIndicator_le
        (M := M) (n := n) (cc := cc) (qs := qs)
      simpa [writeTerm, hb]
        using hbranch

/--
Coarse bound on the gate count of `writeBit`.  The estimate is intentionally
loose—the aim is merely to obtain a polynomial expression.
-/
lemma gateCount_writeBit_le (cc : ConfigCircuits M n) :
    Circuit.gateCount (writeBit (M := M) (n := n) cc) ≤
      2 * stateGateCount (M := M) (n := n) cc +
        (2 * stateCard M) *
          (headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 5)) +
        1 := by
  classical
  have hlen :
      ((stateSymbolPairs M).map fun _ => ()).length = 2 * stateCard M := by
    simpa using length_stateSymbolPairs (M := M)
  have htermBound := gateCount_writeTerm_le (M := M) (n := n)
  have hlist :
      Circuit.listGateCount
          ((stateSymbolPairs M).map fun qs =>
            writeTerm (M := M) (n := n) cc qs) ≤
        2 * stateGateCount (M := M) (n := n) cc +
          (2 * stateCard M) *
            (headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4)) := by
    classical
    refine List.rec ?base ?step (stateSymbolPairs M) <;> intro qs rest ih
    · simp
    · have hqs := htermBound (qs := qs)
      have hlen_rest : rest.length ≤ stateSymbolPairs M |>.length := by
        exact Nat.le_of_lt (List.length_cons_lt_length_cons qs rest)
      have htail := ih
      have := Nat.add_le_add hqs htail
      simpa [Circuit.listGateCount, List.map_cons, List.length_cons, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
        using this
  have hbound :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        writeTerm (M := M) (n := n) cc qs)
  have hconst :
      (2 * stateCard M) * (2 * M.tapeLength n + 4) + (2 * stateCard M) =
        (2 * stateCard M) * (2 * M.tapeLength n + 5) := by
    ring
  have :=
    Nat.add_le_add_right
      (Nat.add_le_add hlist (Nat.le_of_eq hconst)) 1
  simpa [writeBit, hlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using Nat.le_trans hbound this

/-- Bounding the auxiliary circuit used for movement branches. -/
lemma gateCount_moveTerm_le'
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (m : Move) :
    Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) ≤
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
  classical
  obtain ⟨_, _, mv⟩ := M.step qs.1 qs.2
  by_cases hm : mv = m
  · simpa [moveTerm, hm]
      using gateCount_branchIndicator_le
        (M := M) (n := n) (cc := cc) (qs := qs)
  · have hconst : Circuit.gateCount (Circuit.const false : Circuit n) = 1 := by
        simp
    have hpos : 1 ≤
        Circuit.gateCount (cc.state (stateIndex M qs.1)) +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4) := by
      have hbound : 1 ≤ 2 * M.tapeLength n + 4 := by
        have : 1 ≤ 4 := by decide
        exact this.trans (Nat.le_add_left _ _)
      exact hbound.trans (Nat.le_add_left _ _)
    have hfalse :
        Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) = 1 := by
      simpa [moveTerm, hm, hconst]
    simpa [hfalse] using hpos

/-- Coarser bound avoiding explicit references to an individual state circuit. -/
lemma gateCount_moveTerm_le
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (m : Move) :
    Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) ≤
      stateGateCount (M := M) (n := n) cc +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
  classical
  have hstate :=
    gateCount_state_le (M := M) (n := n) (cc := cc)
      (i := stateIndex M qs.1)
  have := gateCount_moveTerm_le' (M := M) (n := n)
      (cc := cc) (qs := qs) (m := m)
  exact
    (this.trans
      (by
        have hadd :
            Circuit.gateCount (cc.state (stateIndex M qs.1)) +
              headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4) ≤
              stateGateCount (M := M) (n := n) cc +
                headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4) := by
          have := Nat.add_le_add_right
              (Nat.add_le_add_right hstate _)
              (2 * M.tapeLength n + 4)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using this
        exact hadd))

/-- Sum of gate counts for all move terms. -/
lemma listGateCount_moveTerm_le
    (cc : ConfigCircuits M n) (m : Move) :
    Circuit.listGateCount
        ((stateSymbolPairs M).map fun qs =>
          moveTerm (M := M) (n := n) cc qs m) ≤
      (2 * stateCard M) *
        (stateGateCount (M := M) (n := n) cc +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4)) := by
  classical
  have hbound :
      ∀ qs ∈ stateSymbolPairs M,
        Circuit.gateCount (moveTerm (M := M) (n := n) cc qs m) ≤
          stateGateCount (M := M) (n := n) cc +
            headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 4) := by
    intro qs hqs
    exact gateCount_moveTerm_le (M := M) (n := n)
      (cc := cc) (qs := qs) (m := m)
  have hlength := length_stateSymbolPairs (M := M)
  have :=
    listGateCount_map_le_const
      (l := stateSymbolPairs M)
      (f := fun qs => moveTerm (M := M) (n := n) cc qs m)
      (B := stateGateCount (M := M) (n := n) cc +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4)) hbound
  simpa [hlength, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

/-- Movement indicators inherit the previous estimate via `Circuit.bigOr`. -/
lemma gateCount_moveIndicator_le (cc : ConfigCircuits M n) (m : Move) :
    Circuit.gateCount (moveIndicator (M := M) (n := n) cc m) ≤
      1 + 2 * stateCard M +
        (2 * stateCard M) *
          (stateGateCount (M := M) (n := n) cc +
            headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 4)) := by
  classical
  have hlen : ((stateSymbolPairs M).map fun _ => ()).length =
      2 * stateCard M := by
    simpa using length_stateSymbolPairs (M := M)
  have hlist :=
    listGateCount_moveTerm_le (M := M) (n := n)
      (cc := cc) (m := m)
  have hbound :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        moveTerm (M := M) (n := n) cc qs m)
  refine hbound.trans ?_
  have := Nat.add_le_add_left hlist (1 + (stateSymbolPairs M).length)
  simpa [moveIndicator, List.map_const, hlen, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Bounding the circuit used to select the next control state for a given
branch.  The estimate mirrors the one for `writeTerm`. -/
lemma gateCount_stateTerm_le
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (q' : M.state) :
    Circuit.gateCount (stateTerm (M := M) (n := n) cc qs q') ≤
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
  classical
  obtain ⟨q'', b, mv⟩ := M.step qs.1 qs.2
  by_cases hq : q'' = q'
  · have hbranch := gateCount_branchIndicator_le
      (M := M) (n := n) (cc := cc) (qs := qs)
    simpa [stateTerm, hq]
      using hbranch
  · have hconst : Circuit.gateCount (Circuit.const false : Circuit n) = 1 := by
      simp
    have hpos : 1 ≤ 2 * M.tapeLength n + 4 := by
      have : 1 ≤ 4 := by decide
      exact this.trans (Nat.le_add_left _ _)
    have hsum : 2 * M.tapeLength n + 4 ≤
        Circuit.gateCount (cc.state (stateIndex M qs.1)) +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.le_add_left (2 * M.tapeLength n + 4)
          (Circuit.gateCount (cc.state (stateIndex M qs.1)) +
            headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc)
    have hle := hpos.trans hsum
    simpa [stateTerm, hq, hconst, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
      using hle

/-- Coarse variant of the previous lemma replacing individual state counts by
the aggregated `stateGateCount`. -/
lemma gateCount_stateTerm_le'
    (cc : ConfigCircuits M n) (qs : M.state × Bool) (q' : M.state) :
    Circuit.gateCount (stateTerm (M := M) (n := n) cc qs q') ≤
      stateGateCount (M := M) (n := n) cc +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
  classical
  have hterm := gateCount_stateTerm_le (M := M) (n := n)
      (cc := cc) (qs := qs) (q' := q')
  have hstate := gateCount_state_le (M := M) (n := n)
      (cc := cc) (i := stateIndex M qs.1)
  have hsum :
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) ≤
      stateGateCount (M := M) (n := n) cc +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
    have := Nat.add_le_add_right
        (Nat.add_le_add_right hstate
          (headGateCount (M := M) (n := n) cc))
        (tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  exact hterm.trans hsum

/-- Bounding the full state-update circuit via the helper estimate above. -/
lemma gateCount_nextStateCircuit_le (cc : ConfigCircuits M n) (q' : M.state) :
    Circuit.gateCount (nextStateCircuit (M := M) (n := n) cc q') ≤
      1 + 2 * stateCard M +
        (2 * stateCard M) *
          (stateGateCount (M := M) (n := n) cc +
            headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 4)) := by
  classical
  have hlen := length_stateSymbolPairs (M := M)
  have hbound : ∀ qs ∈ stateSymbolPairs M,
      Circuit.gateCount
          (stateTerm (M := M) (n := n) cc qs q') ≤
        stateGateCount (M := M) (n := n) cc +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4) := by
    intro qs hqs
    exact gateCount_stateTerm_le' (M := M) (n := n)
      (cc := cc) (qs := qs) (q' := q')
  have hlist :=
    listGateCount_map_le_const
      (l := stateSymbolPairs M)
      (f := fun qs => stateTerm (M := M) (n := n) cc qs q')
      (B := stateGateCount (M := M) (n := n) cc +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4)) hbound
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        stateTerm (M := M) (n := n) cc qs q')
  refine hbig.trans ?_
  have := Nat.add_le_add_left hlist (1 + (stateSymbolPairs M).length)
  simpa [nextStateCircuit, List.map_const, hlen, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Gate-count bound for the head-update branch associated with fixed `qs` and
head index `i`. -/
lemma gateCount_headTerm_le (cc : ConfigCircuits M n)
    (qs : M.state × Bool) (i j : Fin (M.tapeLength n)) :
    Circuit.gateCount (headTerm (M := M) (n := n) cc qs i j) ≤
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        Circuit.gateCount (cc.head i) +
        (2 * M.tapeLength n + 4) := by
  classical
  obtain ⟨q', b, mv⟩ := M.step qs.1 qs.2
  by_cases hmove : nextHeadIndex (M := M) (n := n) i mv = j
  · have hbranch := gateCount_branchIndicator_le
      (M := M) (n := n) (cc := cc) (qs := qs)
    have hle :=
      Nat.add_le_add_right
        (Nat.add_le_add_right hbranch
          (Circuit.gateCount (cc.head i))) 1
    simpa [headTerm, hmove, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
      using hle
  · have hconst : Circuit.gateCount (Circuit.const false : Circuit n) = 1 := by
      simp
    have hpos : 1 ≤ 2 * M.tapeLength n + 4 := by
      have : 1 ≤ 4 := by decide
      exact this.trans (Nat.le_add_left _ _)
    have hsum : 2 * M.tapeLength n + 4 ≤
        Circuit.gateCount (cc.state (stateIndex M qs.1)) +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          Circuit.gateCount (cc.head i) +
          (2 * M.tapeLength n + 4) := by
      have := Nat.le_add_left (2 * M.tapeLength n + 4)
        (Circuit.gateCount (cc.state (stateIndex M qs.1)) +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          Circuit.gateCount (cc.head i))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    have hle := hpos.trans hsum
    simpa [headTerm, hmove, hconst, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
      using hle

/-- Coarse version of the previous lemma phrased using aggregated gate counts. -/
lemma gateCount_headTerm_le'
    (cc : ConfigCircuits M n) (qs : M.state × Bool)
    (i j : Fin (M.tapeLength n)) :
    Circuit.gateCount (headTerm (M := M) (n := n) cc qs i j) ≤
      stateGateCount (M := M) (n := n) cc +
        2 * headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
  classical
  have hterm := gateCount_headTerm_le (M := M) (n := n)
      (cc := cc) (qs := qs) (i := i) (j := j)
  have hstate := gateCount_state_le (M := M) (n := n)
      (cc := cc) (i := stateIndex M qs.1)
  have hhead := gateCount_head_le (M := M) (n := n)
      (cc := cc) (i := i)
  have hsum :
      Circuit.gateCount (cc.state (stateIndex M qs.1)) +
        headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        Circuit.gateCount (cc.head i) +
        (2 * M.tapeLength n + 4) ≤
      stateGateCount (M := M) (n := n) cc +
        2 * headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4) := by
    have := Nat.add_le_add_right
        (Nat.add_le_add_right hstate
          (headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            Circuit.gateCount (cc.head i)))
        (2 * M.tapeLength n + 4)
    have hhead' :=
      Nat.add_le_add_right
        (Nat.add_le_add_left hhead
          (stateGateCount (M := M) (n := n) cc +
            headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc))
        (2 * M.tapeLength n + 4)
    have hcombine :=
      Nat.le_trans this hhead'
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hcombine
  exact hterm.trans hsum

/-- Sum of head-branch gate counts over all tape indices. -/
lemma listGateCount_headTerm_le (cc : ConfigCircuits M n)
    (qs : M.state × Bool) (j : Fin (M.tapeLength n)) :
    Circuit.listGateCount
        ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j) ≤
      M.tapeLength n *
        (stateGateCount (M := M) (n := n) cc +
          2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4)) := by
  classical
  have hbound : ∀ i ∈ tapeIndexList (M := M) n,
      Circuit.gateCount
          (headTerm (M := M) (n := n) cc qs i j) ≤
        stateGateCount (M := M) (n := n) cc +
          2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4) := by
    intro i hi
    refine gateCount_headTerm_le' (M := M) (n := n)
      (cc := cc) (qs := qs) (i := i) (j := j)
  have hlen := length_tapeIndexList (M := M) (n := n)
  have :=
    listGateCount_map_le_const
      (l := tapeIndexList (M := M) n)
      (f := fun i => headTerm (M := M) (n := n) cc qs i j)
      (B := stateGateCount (M := M) (n := n) cc +
        2 * headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        (2 * M.tapeLength n + 4)) hbound
  simpa [tapeIndexList, hlen, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]
    using this

/-- Bounding the inner big-OR appearing in the head-update circuit. -/
lemma gateCount_headBranch_le (cc : ConfigCircuits M n)
    (qs : M.state × Bool) (j : Fin (M.tapeLength n)) :
    Circuit.gateCount
        (Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j)) ≤
      1 + M.tapeLength n +
        M.tapeLength n *
          (stateGateCount (M := M) (n := n) cc +
            2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 4)) := by
  classical
  have hlen := length_tapeIndexList (M := M) (n := n)
  have hlist :=
    listGateCount_headTerm_le (M := M) (n := n)
      (cc := cc) (qs := qs) (j := j)
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((tapeIndexList (M := M) n).map fun i =>
        headTerm (M := M) (n := n) cc qs i j)
  refine hbig.trans ?_
  have := Nat.add_le_add_left hlist (1 + (tapeIndexList (M := M) n).length)
  simpa [tapeIndexList, hlen, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Final gate-count bound for the next-head circuit. -/
lemma gateCount_nextHeadCircuit_le (cc : ConfigCircuits M n)
    (j : Fin (M.tapeLength n)) :
    Circuit.gateCount (nextHeadCircuit (M := M) (n := n) cc j) ≤
      1 + 2 * stateCard M +
        (2 * stateCard M) *
          (1 + M.tapeLength n +
            M.tapeLength n *
              (stateGateCount (M := M) (n := n) cc +
                2 * headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4))) := by
  classical
  have hlen := length_stateSymbolPairs (M := M)
  have hbound : ∀ qs ∈ stateSymbolPairs M,
      Circuit.gateCount
          (Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
            headTerm (M := M) (n := n) cc qs i j)) ≤
        1 + M.tapeLength n +
          M.tapeLength n *
            (stateGateCount (M := M) (n := n) cc +
              2 * headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4)) := by
    intro qs hqs
    exact gateCount_headBranch_le (M := M) (n := n)
      (cc := cc) (qs := qs) (j := j)
  have hlist :=
    listGateCount_map_le_const
      (l := stateSymbolPairs M)
      (f := fun qs =>
        Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j))
      (B := 1 + M.tapeLength n +
        M.tapeLength n *
          (stateGateCount (M := M) (n := n) cc +
            2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 4))) hbound
  have hbig :=
    Circuit.gateCount_bigOr_le
      ((stateSymbolPairs M).map fun qs =>
        Circuit.bigOr ((tapeIndexList (M := M) n).map fun i =>
          headTerm (M := M) (n := n) cc qs i j))
  refine hbig.trans ?_
  have := Nat.add_le_add_left hlist (1 + (stateSymbolPairs M).length)
  simpa [nextHeadCircuit, List.map_const, hlen, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Gate-count bound for the single-cell tape-update circuit. -/
lemma gateCount_nextTapeCircuit_le (cc : ConfigCircuits M n)
    (i : Fin (M.tapeLength n)) :
    Circuit.gateCount (nextTapeCircuit (M := M) (n := n) cc i) ≤
      2 * headGateCount (M := M) (n := n) cc +
        tapeGateCount (M := M) (n := n) cc +
        2 * stateGateCount (M := M) (n := n) cc +
        (2 * stateCard M) *
          (headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 5)) +
        5 := by
  classical
  have hnot : Circuit.gateCount (Circuit.not (cc.head i)) =
      Circuit.gateCount (cc.head i) + 1 := by
    simp [Circuit.gateCount]
  have hbase : Circuit.gateCount (nextTapeCircuit (M := M) (n := n) cc i) ≤
      2 * Circuit.gateCount (cc.head i) +
        Circuit.gateCount (cc.tape i) +
        Circuit.gateCount (writeBit (M := M) (n := n) cc) +
        4 := by
    simp [nextTapeCircuit, Circuit.gateCount, hnot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      two_mul]
  have hhead := gateCount_head_le (M := M) (n := n)
      (cc := cc) (i := i)
  have htape := gateCount_tape_le (M := M) (n := n)
      (cc := cc) (i := i)
  have hwrite := gateCount_writeBit_le (M := M) (n := n) (cc := cc)
  have hheadScaled :
      2 * Circuit.gateCount (cc.head i) ≤
        2 * headGateCount (M := M) (n := n) cc := by
    exact Nat.mul_le_mul_left _ hhead
  have hsum1 :
      2 * Circuit.gateCount (cc.head i) +
          Circuit.gateCount (cc.tape i) ≤
        2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc := by
    exact Nat.add_le_add hheadScaled htape
  have hsum2 :
      2 * Circuit.gateCount (cc.head i) +
          Circuit.gateCount (cc.tape i) +
          Circuit.gateCount (writeBit (M := M) (n := n) cc) ≤
        2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * stateGateCount (M := M) (n := n) cc +
            (2 * stateCard M) *
              (headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 5)) + 1) := by
    exact Nat.add_le_add hsum1 hwrite
  have hsum3 := Nat.add_le_add_right hsum2 4
  have hfinal := Nat.le_trans hbase hsum3
  have hconst :
      (2 * stateGateCount (M := M) (n := n) cc +
          (2 * stateCard M) *
            (headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 5)) + 1 + 4) =
        2 * stateGateCount (M := M) (n := n) cc +
          (2 * stateCard M) *
            (headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 5)) + 5 := by
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have := Nat.add_le_add_left
    (by simpa [hconst] using Nat.le_of_eq hconst)
    (2 * headGateCount (M := M) (n := n) cc +
      tapeGateCount (M := M) (n := n) cc)
  exact Nat.le_trans hfinal this

end GateBounds

section StepGateBounds

variable {M : TM} {n : ℕ}

open scoped BigOperators

/-- Auxiliary bound controlling the contribution of all tape-cell circuits
after one Turing-machine step.  The inequality is obtained by summing the
single-cell estimate from `gateCount_nextTapeCircuit_le` across every tape
index. -/
lemma tapeGateCount_stepCircuits_le (cc : ConfigCircuits M n) :
    tapeGateCount (M := M) (n := n)
        (stepCircuits (M := M) (n := n) cc) ≤
      (M.tapeLength n) *
        (2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          2 * stateGateCount (M := M) (n := n) cc +
          (2 * stateCard M) *
            (headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 5)) +
          5) := by
  classical
  have hbound : ∀ i : Fin (M.tapeLength n),
      Circuit.gateCount
          (nextTapeCircuit (M := M) (n := n) cc i) ≤
        2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          2 * stateGateCount (M := M) (n := n) cc +
          (2 * stateCard M) *
            (headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 5)) +
          5 :=
    gateCount_nextTapeCircuit_le (M := M) (n := n) (cc := cc)
  have hsum :=
    (Finset.sum_le_sum fun i _ => hbound i)
  have hleft :
      ∑ i : Fin (M.tapeLength n),
          Circuit.gateCount
            (nextTapeCircuit (M := M) (n := n) cc i) =
        tapeGateCount (M := M) (n := n)
          (stepCircuits (M := M) (n := n) cc) := by
    simp [tapeGateCount, ConfigCircuits.stepCircuits]
  have hright :
      ∑ _ : Fin (M.tapeLength n),
          (2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            2 * stateGateCount (M := M) (n := n) cc +
            (2 * stateCard M) *
              (headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 5)) +
            5) =
        ((Finset.univ : Finset (Fin (M.tapeLength n))).card) *
          (2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            2 * stateGateCount (M := M) (n := n) cc +
            (2 * stateCard M) *
              (headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 5)) +
            5) :=
    Finset.sum_const_nat _ _
  have hcard :
      ((Finset.univ : Finset (Fin (M.tapeLength n))).card) =
        M.tapeLength n := by
    simpa using (Finset.card_univ (Fin (M.tapeLength n)))
  have hconverted :
      ((Finset.univ : Finset (Fin (M.tapeLength n))).card) *
          (2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            2 * stateGateCount (M := M) (n := n) cc +
            (2 * stateCard M) *
              (headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 5)) +
            5) =
        (M.tapeLength n) *
          (2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            2 * stateGateCount (M := M) (n := n) cc +
            (2 * stateCard M) *
              (headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 5)) +
            5) := by
    simpa [hcard]
  have hfinal :=
    Nat.le_trans
      (by simpa [hleft] using hsum)
      (by simpa [hright, hconverted])
  simpa using hfinal

/-- Head-indicator circuits satisfy an analogous inequality when we combine
the single-index estimate from `gateCount_nextHeadCircuit_le` over all tape
positions. -/
lemma headGateCount_stepCircuits_le (cc : ConfigCircuits M n) :
    headGateCount (M := M) (n := n)
        (stepCircuits (M := M) (n := n) cc) ≤
      (M.tapeLength n) *
        (1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength n +
              M.tapeLength n *
                (stateGateCount (M := M) (n := n) cc +
                  2 * headGateCount (M := M) (n := n) cc +
                  tapeGateCount (M := M) (n := n) cc +
                  (2 * M.tapeLength n + 4)))) := by
  classical
  have hbound : ∀ j : Fin (M.tapeLength n),
      Circuit.gateCount
          (nextHeadCircuit (M := M) (n := n) cc j) ≤
        1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength n +
              M.tapeLength n *
                (stateGateCount (M := M) (n := n) cc +
                  2 * headGateCount (M := M) (n := n) cc +
                  tapeGateCount (M := M) (n := n) cc +
                  (2 * M.tapeLength n + 4))) :=
    gateCount_nextHeadCircuit_le (M := M) (n := n) (cc := cc)
  have hsum :=
    (Finset.sum_le_sum fun j _ => hbound j)
  have hleft :
      ∑ j : Fin (M.tapeLength n),
          Circuit.gateCount
            (nextHeadCircuit (M := M) (n := n) cc j) =
        headGateCount (M := M) (n := n)
          (stepCircuits (M := M) (n := n) cc) := by
    simp [headGateCount, ConfigCircuits.stepCircuits]
  have hright :
      ∑ _ : Fin (M.tapeLength n),
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (stateGateCount (M := M) (n := n) cc +
                    2 * headGateCount (M := M) (n := n) cc +
                    tapeGateCount (M := M) (n := n) cc +
                    (2 * M.tapeLength n + 4)))) =
        ((Finset.univ : Finset (Fin (M.tapeLength n))).card) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (stateGateCount (M := M) (n := n) cc +
                    2 * headGateCount (M := M) (n := n) cc +
                    tapeGateCount (M := M) (n := n) cc +
                    (2 * M.tapeLength n + 4)))) :=
    Finset.sum_const_nat _ _
  have hcard :
      ((Finset.univ : Finset (Fin (M.tapeLength n))).card) =
        M.tapeLength n := by
    simpa using (Finset.card_univ (Fin (M.tapeLength n)))
  have hconverted :
      ((Finset.univ : Finset (Fin (M.tapeLength n))).card) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (stateGateCount (M := M) (n := n) cc +
                    2 * headGateCount (M := M) (n := n) cc +
                    tapeGateCount (M := M) (n := n) cc +
                    (2 * M.tapeLength n + 4)))) =
        (M.tapeLength n) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (stateGateCount (M := M) (n := n) cc +
                    2 * headGateCount (M := M) (n := n) cc +
                    tapeGateCount (M := M) (n := n) cc +
                    (2 * M.tapeLength n + 4)))) := by
    simpa [hcard]
  have hfinal :=
    Nat.le_trans
      (by simpa [hleft] using hsum)
      (by simpa [hright, hconverted])
  simpa using hfinal

/-- Bounding the aggregated state circuits produced by `stepCircuits`. -/
lemma stateGateCount_stepCircuits_le (cc : ConfigCircuits M n) :
    stateGateCount (M := M) (n := n)
        (stepCircuits (M := M) (n := n) cc) ≤
      (stateCard M) *
        (1 + 2 * stateCard M +
          (2 * stateCard M) *
            (stateGateCount (M := M) (n := n) cc +
              headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4))) := by
  classical
  have hbound : ∀ q : Fin (stateCard M),
      Circuit.gateCount
          (nextStateCircuit (M := M) (n := n) cc
            ((stateEquiv M).symm q)) ≤
        1 + 2 * stateCard M +
          (2 * stateCard M) *
            (stateGateCount (M := M) (n := n) cc +
              headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4)) := by
    intro q
    simpa [Function.comp]
      using gateCount_nextStateCircuit_le (M := M) (n := n)
        (cc := cc) (q' := (stateEquiv M).symm q)
  have hsum :=
    (Finset.sum_le_sum fun q _ => hbound q)
  have hleft :
      ∑ q : Fin (stateCard M),
          Circuit.gateCount
            (nextStateCircuit (M := M) (n := n) cc
              ((stateEquiv M).symm q)) =
        stateGateCount (M := M) (n := n)
          (stepCircuits (M := M) (n := n) cc) := by
    simp [stateGateCount, ConfigCircuits.stepCircuits]
  have hright :
      ∑ _ : Fin (stateCard M),
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (stateGateCount (M := M) (n := n) cc +
                headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4))) =
        ((Finset.univ : Finset (Fin (stateCard M))).card) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (stateGateCount (M := M) (n := n) cc +
                headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4))) :=
    Finset.sum_const_nat _ _
  have hcard :
      ((Finset.univ : Finset (Fin (stateCard M))).card) =
        stateCard M := by
    simpa [stateCard] using (Finset.card_univ (Fin (stateCard M)))
  have hconverted :
      ((Finset.univ : Finset (Fin (stateCard M))).card) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (stateGateCount (M := M) (n := n) cc +
                headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4))) =
        (stateCard M) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (stateGateCount (M := M) (n := n) cc +
                headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4))) := by
    simpa [hcard]
  have hfinal :=
    Nat.le_trans
      (by simpa [hleft] using hsum)
      (by simpa [hright, hconverted])
  simpa using hfinal

/--
Combining the previous lemmas yields a coarse—but fully explicit—upper bound
for the aggregate gate count of a configuration after a single simulated step.
-/
lemma totalGateCount_stepCircuits_le (cc : ConfigCircuits M n) :
    totalGateCount (M := M) (n := n)
        (stepCircuits (M := M) (n := n) cc) ≤
      (M.tapeLength n) *
          (2 * headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            2 * stateGateCount (M := M) (n := n) cc +
            (2 * stateCard M) *
              (headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 5)) +
            5) +
        (M.tapeLength n) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (stateGateCount (M := M) (n := n) cc +
                    2 * headGateCount (M := M) (n := n) cc +
                    tapeGateCount (M := M) (n := n) cc +
                    (2 * M.tapeLength n + 4)))) +
        (stateCard M) *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (stateGateCount (M := M) (n := n) cc +
                headGateCount (M := M) (n := n) cc +
                tapeGateCount (M := M) (n := n) cc +
                (2 * M.tapeLength n + 4))) := by
  classical
  have htape := tapeGateCount_stepCircuits_le (M := M) (n := n) (cc := cc)
  have hhead := headGateCount_stepCircuits_le (M := M) (n := n) (cc := cc)
  have hstate := stateGateCount_stepCircuits_le (M := M) (n := n) (cc := cc)
  have :=
    Nat.add_le_add (Nat.add_le_add htape hhead) hstate
  simpa [totalGateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

end StepGateBounds

section IteratedGateBounds

variable {M : TM} {n : ℕ}

/--
`GateVector` packages simultaneous upper bounds for the aggregated tape,
head and state gate counts of a configuration circuit.  The componentwise
ordering will let us iterate the one-step estimates proved above.
-/
structure GateVector where
  tape : ℕ
  head : ℕ
  state : ℕ

namespace GateVector

/--
Componentwise comparison for gate-count bounds.  The relation `b₁ ⪯ b₂`
asserts that every component of `b₁` is bounded by the corresponding
component of `b₂`.
-/
def le (b₁ b₂ : GateVector) : Prop :=
  b₁.tape ≤ b₂.tape ∧ b₁.head ≤ b₂.head ∧ b₁.state ≤ b₂.state

notation:50 b₁ " ⪯ " b₂ => GateVector.le b₁ b₂

@[simp] lemma le_def {b₁ b₂ : GateVector} : (b₁ ⪯ b₂) ↔
    b₁.tape ≤ b₂.tape ∧ b₁.head ≤ b₂.head ∧ b₁.state ≤ b₂.state := Iff.rfl

lemma le_refl (b : GateVector) : b ⪯ b :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

lemma le_trans {b₁ b₂ b₃ : GateVector}
    (h₁ : b₁ ⪯ b₂) (h₂ : b₂ ⪯ b₃) : b₁ ⪯ b₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1,
    Nat.le_trans h₁.2.1 h₂.2.1,
    Nat.le_trans h₁.2.2 h₂.2.2⟩

lemma le_antisymm {b₁ b₂ : GateVector}
    (h₁ : b₁ ⪯ b₂) (h₂ : b₂ ⪯ b₁) : b₁ = b₂ := by
  cases b₁; cases b₂
  cases h₁ with
  | intro hTape hrest =>
    cases hrest with
    | intro hHead hState =>
      cases h₂ with
      | intro hTape' hrest' =>
        cases hrest' with
        | intro hHead' hState' =>
          simp [GateVector.le, Nat.le_antisymm hTape hTape',
            Nat.le_antisymm hHead hHead', Nat.le_antisymm hState hState']

lemma le_tape {b₁ b₂ : GateVector} (h : b₁ ⪯ b₂) : b₁.tape ≤ b₂.tape := h.1

lemma le_head {b₁ b₂ : GateVector} (h : b₁ ⪯ b₂) : b₁.head ≤ b₂.head := h.2.1

lemma le_state {b₁ b₂ : GateVector} (h : b₁ ⪯ b₂) : b₁.state ≤ b₂.state := h.2.2

end GateVector

/--
One step of the abstract gate-count transformer.  Starting from bounds for
the current configuration (`b`), `stepBounds` returns bounds for the successor
configuration obtained via `stepCircuits`.
-/
def stepBounds (M : TM) (n : ℕ) (b : GateVector) : GateVector where
  tape :=
    (M.tapeLength n) *
        (2 * b.head + b.tape + 2 * b.state +
          (2 * stateCard M) *
            (b.head + b.tape + (2 * M.tapeLength n + 5)) +
          5)
  head :=
    (M.tapeLength n) *
        (1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength n +
              M.tapeLength n *
                (b.state + 2 * b.head + b.tape +
                  (2 * M.tapeLength n + 4))))
  state :=
    (stateCard M) *
        (1 + 2 * stateCard M +
          (2 * stateCard M) *
            (b.state + b.head + b.tape + (2 * M.tapeLength n + 4)))

open GateVector

lemma stepBounds_le {M : TM} {n : ℕ} {b₁ b₂ : GateVector}
    (h : b₁ ⪯ b₂) :
    stepBounds (M := M) (n := n) b₁ ⪯ stepBounds (M := M) (n := n) b₂ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have hHead := Nat.mul_le_mul_left (2) (le_head h)
    have hTape := le_tape h
    have hState := Nat.mul_le_mul_left (2) (le_state h)
    have hHeadTape : b₁.head + b₁.tape ≤ b₂.head + b₂.tape :=
      Nat.add_le_add (le_head h) hTape
    have hStateTerm :
        (2 * stateCard M) *
            (b₁.head + b₁.tape + (2 * M.tapeLength n + 5)) ≤
          (2 * stateCard M) *
            (b₂.head + b₂.tape + (2 * M.tapeLength n + 5)) := by
      refine Nat.mul_le_mul_left _ ?_
      exact Nat.add_le_add hHeadTape (Nat.le_refl _)
    have hInside :
        2 * b₁.head + b₁.tape + 2 * b₁.state +
            (2 * stateCard M) *
              (b₁.head + b₁.tape + (2 * M.tapeLength n + 5)) + 5 ≤
          2 * b₂.head + b₂.tape + 2 * b₂.state +
            (2 * stateCard M) *
              (b₂.head + b₂.tape + (2 * M.tapeLength n + 5)) + 5 := by
      have := Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add hHead hTape) hState)
        hStateTerm
      have := Nat.add_le_add this (Nat.le_refl _)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    exact Nat.mul_le_mul_left _ hInside
  · have hState := le_state h
    have hHead := le_head h
    have hTape := le_tape h
    have hSum :
        b₁.state + 2 * b₁.head + b₁.tape ≤
          b₂.state + 2 * b₂.head + b₂.tape := by
      have := Nat.add_le_add (Nat.add_le_add hState (Nat.mul_le_mul_left 2 hHead)) hTape
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul]
        using this
    have hInner :
        M.tapeLength n *
            (b₁.state + 2 * b₁.head + b₁.tape + (2 * M.tapeLength n + 4)) ≤
          M.tapeLength n *
            (b₂.state + 2 * b₂.head + b₂.tape + (2 * M.tapeLength n + 4)) := by
      have := Nat.add_le_add hSum (Nat.le_refl _)
      exact Nat.mul_le_mul_left _ this
    have hInside :
        1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (b₁.state + 2 * b₁.head + b₁.tape +
                    (2 * M.tapeLength n + 4))) ≤
          1 + 2 * stateCard M +
            (2 * stateCard M) *
              (1 + M.tapeLength n +
                M.tapeLength n *
                  (b₂.state + 2 * b₂.head + b₂.tape +
                    (2 * M.tapeLength n + 4))) := by
      have := Nat.add_le_add (Nat.le_refl (1 + 2 * stateCard M))
        (Nat.mul_le_mul_left _
          (Nat.add_le_add (Nat.le_refl (1 + M.tapeLength n)) hInner))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    exact Nat.mul_le_mul_left _ hInside
  · have hSum :=
      Nat.add_le_add (Nat.add_le_add (le_state h) (le_head h)) (le_tape h)
    have hInside :
        1 + 2 * stateCard M +
            (2 * stateCard M) *
              (b₁.state + b₁.head + b₁.tape + (2 * M.tapeLength n + 4)) ≤
          1 + 2 * stateCard M +
            (2 * stateCard M) *
              (b₂.state + b₂.head + b₂.tape + (2 * M.tapeLength n + 4)) := by
      have := Nat.add_le_add (Nat.le_refl (1 + 2 * stateCard M))
        (Nat.mul_le_mul_left _
          (Nat.add_le_add hSum (Nat.le_refl _)))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    exact Nat.mul_le_mul_left _ hInside

lemma totalBound_mono {b₁ b₂ : GateVector}
    (h : b₁ ⪯ b₂) : totalBound b₁ ≤ totalBound b₂ := by
  have hsum := Nat.add_le_add (le_tape h)
    (Nat.add_le_add (le_head h) (le_state h))
  simpa [totalBound, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hsum

lemma iterate_stepBounds_le (t : ℕ) {b₁ b₂ : GateVector}
    (h : b₁ ⪯ b₂) :
    Nat.iterate (stepBounds (M := M) (n := n)) t b₁ ⪯
      Nat.iterate (stepBounds (M := M) (n := n)) t b₂ := by
  classical
  induction t with
  | zero => simpa
  | succ t ih =>
      simpa [Nat.iterate_succ, Function.comp]
        using stepBounds_le (M := M) (n := n)
          (b₁ := Nat.iterate (stepBounds (M := M) (n := n)) t b₁)
          (b₂ := Nat.iterate (stepBounds (M := M) (n := n)) t b₂) ih

/--
Initial gate-count bounds derived from the explicit description of
`ConfigCircuits.initial`.
-/
def initialBounds (M : TM) (n : ℕ) : GateVector where
  tape := M.tapeLength n
  head := M.tapeLength n
  state := stateCard M

lemma tapeBound_step
    {cc : ConfigCircuits M n} {b : GateVector}
    (hTape : tapeGateCount (M := M) (n := n) cc ≤ b.tape)
    (hHead : headGateCount (M := M) (n := n) cc ≤ b.head)
    (hState : stateGateCount (M := M) (n := n) cc ≤ b.state) :
    tapeGateCount (M := M) (n := n) (stepCircuits (M := M) (n := n) cc) ≤
      (stepBounds (M := M) (n := n) b).tape := by
  classical
  have hstep :=
    tapeGateCount_stepCircuits_le (M := M) (n := n) (cc := cc)
  have hHead' : 2 * headGateCount (M := M) (n := n) cc ≤ 2 * b.head := by
    exact Nat.mul_le_mul_left _ hHead
  have hState' : 2 * stateGateCount (M := M) (n := n) cc ≤ 2 * b.state := by
    exact Nat.mul_le_mul_left _ hState
  have hHeadTape :
      headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc ≤
        b.head + b.tape := by
    exact Nat.add_le_add hHead hTape
  have hconst :
      headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 5) ≤
        b.head + b.tape + (2 * M.tapeLength n + 5) := by
    exact Nat.add_le_add hHeadTape (Nat.le_refl _)
  have hmulConst :
      (2 * stateCard M) *
          (headGateCount (M := M) (n := n) cc +
            tapeGateCount (M := M) (n := n) cc +
            (2 * M.tapeLength n + 5)) ≤
        (2 * stateCard M) *
          (b.head + b.tape + (2 * M.tapeLength n + 5)) := by
    exact Nat.mul_le_mul_left _ hconst
  have hInside :
      2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          2 * stateGateCount (M := M) (n := n) cc +
          (2 * stateCard M) *
            (headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 5)) +
          5 ≤
        2 * b.head + b.tape + 2 * b.state +
          (2 * stateCard M) *
            (b.head + b.tape + (2 * M.tapeLength n + 5)) +
          5 := by
    have := Nat.add_le_add hHead' hTape
    have hsum := Nat.add_le_add this hState'
    have hsum' := Nat.add_le_add hsum hmulConst
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using Nat.add_le_add hsum' (Nat.le_refl _)
  have hmul :
      (M.tapeLength n) *
            (2 * headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              2 * stateGateCount (M := M) (n := n) cc +
              (2 * stateCard M) *
                (headGateCount (M := M) (n := n) cc +
                  tapeGateCount (M := M) (n := n) cc +
                  (2 * M.tapeLength n + 5)) +
              5) ≤
        (M.tapeLength n) *
            (2 * b.head + b.tape + 2 * b.state +
              (2 * stateCard M) *
                (b.head + b.tape + (2 * M.tapeLength n + 5)) +
              5) := by
    exact Nat.mul_le_mul_left _ hInside
  exact Nat.le_trans hstep hmul

lemma headBound_step
    {cc : ConfigCircuits M n} {b : GateVector}
    (hTape : tapeGateCount (M := M) (n := n) cc ≤ b.tape)
    (hHead : headGateCount (M := M) (n := n) cc ≤ b.head)
    (hState : stateGateCount (M := M) (n := n) cc ≤ b.state) :
    headGateCount (M := M) (n := n) (stepCircuits (M := M) (n := n) cc) ≤
      (stepBounds (M := M) (n := n) b).head := by
  classical
  have hstep :=
    headGateCount_stepCircuits_le (M := M) (n := n) (cc := cc)
  have hState' :
      stateGateCount (M := M) (n := n) cc +
          2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc ≤
        b.state + 2 * b.head + b.tape := by
    have hMul := Nat.mul_le_mul_left (2) hHead
    have hsum := Nat.add_le_add hState hMul
    exact Nat.add_le_add hsum hTape
  have hconst :
      stateGateCount (M := M) (n := n) cc +
          2 * headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4) ≤
        b.state + 2 * b.head + b.tape + (2 * M.tapeLength n + 4) := by
    exact Nat.add_le_add hState' (Nat.le_refl _)
  have hmulConst :
      M.tapeLength n *
            (stateGateCount (M := M) (n := n) cc +
              2 * headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4)) ≤
        M.tapeLength n *
            (b.state + 2 * b.head + b.tape + (2 * M.tapeLength n + 4)) := by
    exact Nat.mul_le_mul_left _ hconst
  have hInside :
      1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength n +
              M.tapeLength n *
                (stateGateCount (M := M) (n := n) cc +
                  2 * headGateCount (M := M) (n := n) cc +
                  tapeGateCount (M := M) (n := n) cc +
                  (2 * M.tapeLength n + 4))) ≤
        1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength n +
              M.tapeLength n *
                (b.state + 2 * b.head + b.tape +
                  (2 * M.tapeLength n + 4))) := by
    have := Nat.mul_le_mul_left (2 * stateCard M)
      (Nat.add_le_add (Nat.le_refl _)
        (Nat.add_le_add (Nat.le_refl _)
          (Nat.mul_le_mul_left _ hconst)))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hmul := Nat.mul_le_mul_left _ hInside
  exact Nat.le_trans hstep hmul

lemma stateBound_step
    {cc : ConfigCircuits M n} {b : GateVector}
    (hTape : tapeGateCount (M := M) (n := n) cc ≤ b.tape)
    (hHead : headGateCount (M := M) (n := n) cc ≤ b.head)
    (hState : stateGateCount (M := M) (n := n) cc ≤ b.state) :
    stateGateCount (M := M) (n := n) (stepCircuits (M := M) (n := n) cc) ≤
      (stepBounds (M := M) (n := n) b).state := by
  classical
  have hstep :=
    stateGateCount_stepCircuits_le (M := M) (n := n) (cc := cc)
  have hsum :
      stateGateCount (M := M) (n := n) cc +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc ≤
        b.state + b.head + b.tape := by
    exact Nat.add_le_add hState (Nat.add_le_add hHead hTape)
  have hconst :
      stateGateCount (M := M) (n := n) cc +
          headGateCount (M := M) (n := n) cc +
          tapeGateCount (M := M) (n := n) cc +
          (2 * M.tapeLength n + 4) ≤
        b.state + b.head + b.tape + (2 * M.tapeLength n + 4) := by
    exact Nat.add_le_add hsum (Nat.le_refl _)
  have hInside :
      1 + 2 * stateCard M +
          (2 * stateCard M) *
            (stateGateCount (M := M) (n := n) cc +
              headGateCount (M := M) (n := n) cc +
              tapeGateCount (M := M) (n := n) cc +
              (2 * M.tapeLength n + 4)) ≤
        1 + 2 * stateCard M +
          (2 * stateCard M) *
            (b.state + b.head + b.tape +
              (2 * M.tapeLength n + 4)) := by
    have := Nat.mul_le_mul_left (2 * stateCard M) hconst
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using Nat.add_le_add (Nat.le_refl _) this
  have hmul := Nat.mul_le_mul_left _ hInside
  exact Nat.le_trans hstep hmul

lemma bounds_step
    {cc : ConfigCircuits M n} {b : GateVector}
    (hTape : tapeGateCount (M := M) (n := n) cc ≤ b.tape)
    (hHead : headGateCount (M := M) (n := n) cc ≤ b.head)
    (hState : stateGateCount (M := M) (n := n) cc ≤ b.state) :
    tapeGateCount (M := M) (n := n) (stepCircuits (M := M) (n := n) cc) ≤
        (stepBounds (M := M) (n := n) b).tape ∧
      headGateCount (M := M) (n := n) (stepCircuits (M := M) (n := n) cc) ≤
        (stepBounds (M := M) (n := n) b).head ∧
      stateGateCount (M := M) (n := n) (stepCircuits (M := M) (n := n) cc) ≤
        (stepBounds (M := M) (n := n) b).state := by
  exact ⟨tapeBound_step (M := M) (n := n) hTape hHead hState,
    headBound_step (M := M) (n := n) hTape hHead hState,
    stateBound_step (M := M) (n := n) hTape hHead hState⟩

lemma bounds_initial :
    tapeGateCount (M := M) (n := n) (initial (M := M) n) ≤
        (initialBounds (M := M) (n := n)).tape ∧
      headGateCount (M := M) (n := n) (initial (M := M) n) ≤
        (initialBounds (M := M) (n := n)).head ∧
      stateGateCount (M := M) (n := n) (initial (M := M) n) ≤
        (initialBounds (M := M) (n := n)).state := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [initialBounds] using
      (le_of_eq (tapeGateCount_initial (M := M) (n := n)))
  · simpa [initialBounds] using
      (le_of_eq (headGateCount_initial (M := M) (n := n)))
  · simpa [initialBounds] using
      (le_of_eq (stateGateCount_initial (M := M) (n := n)))

/--
Iterated gate-count bounds: applying `stepBounds` in sync with
`stepCircuits` preserves the componentwise inequality recorded in
`GateVector`.
-/
lemma bounds_iterate (t : ℕ) :
    tapeGateCount (M := M) (n := n)
        (Nat.iterate (stepCircuits (M := M) (n := n)) t
          (initial (M := M) n)) ≤
        (Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n))).tape ∧
      headGateCount (M := M) (n := n)
        (Nat.iterate (stepCircuits (M := M) (n := n)) t
          (initial (M := M) n)) ≤
        (Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n))).head ∧
      stateGateCount (M := M) (n := n)
        (Nat.iterate (stepCircuits (M := M) (n := n)) t
          (initial (M := M) n)) ≤
        (Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n))).state := by
  classical
  induction t with
  | zero =>
      simpa [Nat.iterate_zero, Function.comp] using bounds_initial
  | succ t ih =>
      have := bounds_step (M := M) (n := n)
        (cc := Nat.iterate (stepCircuits (M := M) (n := n)) t
          (initial (M := M) n))
        (b := Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n)))
        ih.1 ih.2.1 ih.2.2
      simpa [Nat.iterate_succ, Function.comp] using this

/--
Bounds for the runtime configuration obtained after `runTime n` steps.
-/
lemma bounds_runtime :
    tapeGateCount (M := M) (n := n) (runtimeCircuits (M := M) n) ≤
        (Nat.iterate (stepBounds (M := M) (n := n)) (M.runTime n)
          (initialBounds (M := M) (n := n))).tape ∧
      headGateCount (M := M) (n := n) (runtimeCircuits (M := M) n) ≤
        (Nat.iterate (stepBounds (M := M) (n := n)) (M.runTime n)
          (initialBounds (M := M) (n := n))).head ∧
      stateGateCount (M := M) (n := n) (runtimeCircuits (M := M) n) ≤
        (Nat.iterate (stepBounds (M := M) (n := n)) (M.runTime n)
          (initialBounds (M := M) (n := n))).state := by
  simpa [runtimeCircuits] using bounds_iterate (M := M) (n := n)
    (t := M.runTime n)

/--
Total gate-count bound extracted from a `GateVector`.
-/
def totalBound (b : GateVector) : ℕ := b.tape + b.head + b.state

lemma totalBound_step
    {cc : ConfigCircuits M n} {b : GateVector}
    (hTape : tapeGateCount (M := M) (n := n) cc ≤ b.tape)
    (hHead : headGateCount (M := M) (n := n) cc ≤ b.head)
    (hState : stateGateCount (M := M) (n := n) cc ≤ b.state) :
    totalGateCount (M := M) (n := n)
        (stepCircuits (M := M) (n := n) cc) ≤
      totalBound (stepBounds (M := M) (n := n) b) := by
  have h := bounds_step (M := M) (n := n)
    (cc := cc) (b := b) hTape hHead hState
  have hsum := Nat.add_le_add h.1 (Nat.add_le_add h.2.1 h.2.2)
  simpa [totalGateCount, totalBound, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hsum

lemma totalBound_initial :
    totalGateCount (M := M) (n := n) (initial (M := M) n) ≤
      totalBound (initialBounds (M := M) (n := n)) := by
  have h := bounds_initial (M := M) (n := n)
  have hsum := Nat.add_le_add h.1 (Nat.add_le_add h.2.1 h.2.2)
  simpa [totalGateCount, totalBound, initialBounds,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum

/--
Iterated total gate-count bounds mirroring `bounds_iterate`.
-/
lemma totalBound_iterate (t : ℕ) :
    totalGateCount (M := M) (n := n)
        (Nat.iterate (stepCircuits (M := M) (n := n)) t
          (initial (M := M) n)) ≤
      totalBound
        (Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n))) := by
  classical
  induction t with
  | zero =>
      simpa [Nat.iterate_zero, Function.comp]
        using totalBound_initial (M := M) (n := n)
  | succ t ih =>
      have := totalBound_step (M := M) (n := n)
        (cc := Nat.iterate (stepCircuits (M := M) (n := n)) t
          (initial (M := M) n))
        (b := Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n)))
        (bounds_iterate (M := M) (n := n) (t := t)).1
        (bounds_iterate (M := M) (n := n) (t := t)).2.1
        (bounds_iterate (M := M) (n := n) (t := t)).2.2
      simpa [Nat.iterate_succ, Function.comp] using this

/--
Total gate-count bound specialised to the runtime configuration after
`runTime n` steps.
-/
lemma totalBound_runtime :
    totalGateCount (M := M) (n := n) (runtimeCircuits (M := M) n) ≤
      totalBound
        (Nat.iterate (stepBounds (M := M) (n := n)) (M.runTime n)
          (initialBounds (M := M) (n := n))) := by
  simpa [runtimeCircuits]
    using totalBound_iterate (M := M) (n := n) (t := M.runTime n)

end IteratedGateBounds

end ConfigCircuits

/--
### Affine recurrences for coarse size bounds

The aggregated gate counts derived so far allow us to control the iteration of
`stepBounds` via an explicit affine recurrence.  While the estimates in this
section are extremely loose, they provide a convenient normal form that will be
refined in subsequent work on polynomial bounds.
-/
section AffineBounds

open Complexity

variable {M : TM} {n : ℕ}

/-- Auxiliary geometric series used to describe the explicit solution of
`affineIter`.  The definition follows the standard recursion
`geomSum a (t+1) = geomSum a t + a^t`. -/
def geomSum (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => geomSum a t + a ^ t

@[simp] lemma geomSum_zero (a : ℕ) : geomSum a 0 = 0 := rfl

@[simp] lemma geomSum_succ (a : ℕ) (t : ℕ) :
    geomSum a (t + 1) = geomSum a t + a ^ t := rfl

/-- Simple rewriting rule for the geometric series: multiplying the partial
sum by `a` and adding one step coincides with extending the series by a
single term.  The identity is the linchpin that converts the affine
recurrence into a closed form. -/
lemma geomSum_mul_add_one (a t : ℕ) :
    a * geomSum a t + 1 = geomSum a (t + 1) := by
  induction t with
  | zero =>
      simp [geomSum]
  | succ t ih =>
      -- Expand the recurrence on both sides and recycle the inductive
      -- hypothesis.  The remaining goal is a routine algebraic identity.
      calc
        a * geomSum a (t.succ) + 1
            = a * (geomSum a t + a ^ t) + 1 := by simp [geomSum]
        _ = (a * geomSum a t + 1) + a ^ (t.succ) := by
              simp [Nat.mul_add, Nat.pow_succ, Nat.mul_comm,
                Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc]
        _ = (geomSum a t + a ^ t) + a ^ (t.succ) := by
              simpa [ih]
        _ = geomSum a (t.succ) + a ^ (t.succ) := by simp [geomSum]
        _ = geomSum a (t.succ.succ) := by simp [geomSum]

/-- Linear coefficient governing the growth of `totalBound` under one
application of `stepBounds`. -/
def affineFactor (M : TM) (n : ℕ) : ℕ :=
  let L := M.tapeLength n
  let Q := stateCard M
  L * (5 + 4 * Q) + (8 * Q) * (L * L) + 6 * (Q * Q)

/-- Constant offset appearing in the affine domination of `stepBounds`. -/
def affineOffset (M : TM) (n : ℕ) : ℕ :=
  let L := M.tapeLength n
  let Q := stateCard M
  L * ((2 * Q) * (2 * L + 5) + 5) +
    L * (1 + 2 * Q + (2 * Q) * (1 + L + L * (2 * L + 4))) +
    Q * (1 + 2 * Q + (2 * Q) * (2 * L + 4))

/--
Single-step affine bound for the total gate-count transformer.  Each occurrence
of the individual gate counters is majorised by the total sum, while the
remaining summands contribute to the constant offset.
-/
lemma totalBound_stepBounds_le_affine (b : GateVector) :
    totalBound (stepBounds (M := M) (n := n) b) ≤
      affineFactor (M := M) (n := n) * totalBound b +
        affineOffset (M := M) (n := n) := by
  classical
  set L := M.tapeLength n
  set Q := stateCard M
  set S := totalBound b with hS
  have hTape_le : b.tape ≤ S := by
    have := Nat.le_add_left b.tape (b.head + b.state)
    simpa [S, totalBound, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hHead_le : b.head ≤ S := by
    have := Nat.le_add_right b.head (b.tape + b.state)
    simpa [S, totalBound, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hState_le : b.state ≤ S := by
    have := Nat.le_add_right b.state (b.tape + b.head)
    simpa [S, totalBound, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  -- tape component
  have hFive : 2 * S + S + 2 * S = 5 * S := by
    ring
  have hTapeSum : 2 * b.head + b.tape + 2 * b.state ≤ 5 * S := by
    have hHead' := Nat.mul_le_mul_left 2 hHead_le
    have hState' := Nat.mul_le_mul_left 2 hState_le
    have hcomb := Nat.add_le_add hHead'
        (Nat.add_le_add hTape_le hState')
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      two_mul, hFive] using hcomb
  have hPair : b.head + b.tape ≤ 2 * S := by
    have := Nat.add_le_add hHead_le hTape_le
    simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hTapeInside :
      2 * b.head + b.tape + 2 * b.state +
          (2 * Q) * (b.head + b.tape + (2 * L + 5)) + 5 ≤
        (5 + 4 * Q) * S + (2 * Q) * (2 * L + 5) + 5 := by
    have hScaled :=
      Nat.mul_le_mul_left (2 * Q)
        (Nat.add_le_add hPair (Nat.le_refl _))
    have hRewrite : (2 * Q) * (2 * S) = (4 * Q) * S := by
      ring
    have hScaled' := by
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        hRewrite] using hScaled
    exact
      Nat.add_le_add hTapeSum
        (Nat.add_le_add hScaled' (Nat.le_refl _))
  have hTape :
      (stepBounds (M := M) (n := n) b).tape ≤
        L * ((5 + 4 * Q) * S + (2 * Q) * (2 * L + 5) + 5) := by
    simpa [stepBounds, L, Q] using Nat.mul_le_mul_left L hTapeInside
  -- head component
  have hStateHead : b.state + 2 * b.head + b.tape ≤ 4 * S := by
    have hHead' := Nat.mul_le_mul_left 2 hHead_le
    have hcomb :=
      Nat.add_le_add hState_le (Nat.add_le_add hHead' hTape_le)
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      two_mul] using hcomb
  have hHeadSplit :
      (stepBounds (M := M) (n := n) b).head =
        L * (1 + 2 * Q + (2 * Q) * (1 + L + L * (2 * L + 4))) +
          (2 * Q) * (L * L) * (b.state + 2 * b.head + b.tape) := by
    simp [stepBounds, L, Q, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm]
  have hHeadVar :
      (2 * Q) * (L * L) * (b.state + 2 * b.head + b.tape) ≤
        (8 * Q) * (L * L) * S := by
    have := Nat.mul_le_mul_left ((2 * Q) * (L * L)) hStateHead
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_assoc, Nat.mul_left_comm, two_mul] using this
  have hHead :
      (stepBounds (M := M) (n := n) b).head ≤
        (8 * Q) * (L * L) * S +
          L * (1 + 2 * Q + (2 * Q) * (1 + L + L * (2 * L + 4))) := by
    have hconst :=
      Nat.le_of_eq
        (by ring)
    simpa [hHeadSplit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using Nat.add_le_add hHeadVar hconst
  -- state component
  have hTriple : b.state + b.head + b.tape ≤ 3 * S := by
    have hpair := Nat.add_le_add hState_le hHead_le
    have := Nat.add_le_add hpair hTape_le
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      three_mul] using this
  have hStateInside :
      (2 * Q) * (b.state + b.head + b.tape + (2 * L + 4)) ≤
        6 * (Q * Q) * S + (2 * Q) * (2 * L + 4) := by
    have := Nat.mul_le_mul_left (2 * Q)
        (Nat.add_le_add hTriple (Nat.le_refl _))
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      three_mul, Nat.mul_assoc, Nat.mul_left_comm] using this
  have hState :
      (stepBounds (M := M) (n := n) b).state ≤
        6 * (Q * Q) * S +
          Q * (1 + 2 * Q + (2 * Q) * (2 * L + 4)) := by
    exact
      Nat.add_le_add hStateInside (Nat.le_refl _)
  -- assemble
  have hsum :=
    Nat.add_le_add hTape (Nat.add_le_add hHead hState)
  simp [affineFactor, affineOffset, totalBound, hS, L, Q,
    Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at hsum
  simpa using hsum

/--
Affine recurrence dominating the iterates of `stepBounds`.
-/
def affineIter (M : TM) (n : ℕ) : ℕ → ℕ
  | 0 => totalBound (initialBounds (M := M) (n := n))
  | t + 1 =>
      affineFactor (M := M) (n := n) * affineIter M n t +
        affineOffset (M := M) (n := n)

@[simp] lemma affineIter_zero :
    affineIter (M := M) (n := n) 0 =
      totalBound (initialBounds (M := M) (n := n)) := rfl

lemma affineIter_succ (t : ℕ) :
    affineIter (M := M) (n := n) (t + 1) =
      affineFactor (M := M) (n := n) * affineIter (M := M) (n := n) t +
        affineOffset (M := M) (n := n) := rfl

/--
Closed form of the affine recurrence.  Unwinding the definition reveals the
expected geometric series expression: the initial value is scaled by
`affineFactor ^ t`, and the offsets accumulate according to the geometric
sum described by `geomSum`.
-/
lemma affineIter_closed_form (t : ℕ) :
    affineIter (M := M) (n := n) t =
      (affineFactor (M := M) (n := n)) ^ t *
          totalBound (initialBounds (M := M) (n := n)) +
        affineOffset (M := M) (n := n) *
          geomSum (affineFactor (M := M) (n := n)) t := by
  classical
  induction t with
  | zero =>
      simp [affineIter]
  | succ t ih =>
      -- Substitute the inductive hypothesis into the defining recurrence and
      -- clean up with the helper lemma about the geometric series.
      have := congrArg
        (fun x => affineFactor (M := M) (n := n) * x +
            affineOffset (M := M) (n := n)) ih
      -- Normalise all occurrences of `affineIter` using the recursive
      -- equation; afterwards the result is a purely algebraic identity.
      -- The previously established `geomSum_mul_add_one` performs the key
      -- simplification.
      simpa [affineIter_succ, Nat.pow_succ, Nat.mul_add,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        geomSum_mul_add_one, geomSum, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using this

/--
Iterating `stepBounds` is controlled by the explicit affine recurrence.
-/
lemma totalBound_iterate_stepBounds_le_affine (t : ℕ) :
    totalBound
        (Nat.iterate (stepBounds (M := M) (n := n)) t
          (initialBounds (M := M) (n := n))) ≤
      affineIter (M := M) (n := n) t := by
  classical
  induction t with
  | zero =>
      simp [affineIter]
  | succ t ih =>
      have h :=
        totalBound_stepBounds_le_affine
          (M := M) (n := n)
          (b := Nat.iterate (stepBounds (M := M) (n := n)) t
            (initialBounds (M := M) (n := n)))
      have hmono := Nat.mul_le_mul_left _ ih
      simpa [affineIter_succ, Nat.iterate_succ, Function.comp]
        using Nat.le_trans h (Nat.add_le_add hmono (Nat.le_refl _))

/--
The affine domination also bounds the total gate count of the runtime
configuration.
-/
lemma totalGateCount_runtime_le_affine :
    totalGateCount (M := M) (n := n) (runtimeCircuits (M := M) n) ≤
      affineIter (M := M) (n := n) (M.runTime n) := by
  have h := totalBound_runtime (M := M) (n := n)
  exact
    Nat.le_trans h
      (totalBound_iterate_stepBounds_le_affine (M := M) (n := n)
        (t := M.runTime n))

end AffineBounds

section AcceptanceBounds

open Circuit

variable {M : TM} {n : ℕ}

/-- The acceptance circuit is one of the state-indicator gadgets and therefore
inherits the global size bound for the runtime configuration. -/
lemma gateCount_acceptCircuit_le_total :
    Circuit.gateCount (acceptCircuit (M := M) (n := n)) ≤
      totalGateCount (M := M) (n := n) (runtimeCircuits (M := M) n) := by
  classical
  have hstate :=
    gateCount_state_le (M := M) (n := n)
      (cc := runtimeCircuits (M := M) n)
      (i := stateIndex M M.accept)
  exact
    Nat.le_trans hstate
      (stateGateCount_le_total (M := M) (n := n)
        (cc := runtimeCircuits (M := M) n))

/-- Combining `gateCount_acceptCircuit_le_total` with the affine domination of
`totalGateCount` yields a convenient bound tailored to the acceptance circuit. -/
lemma gateCount_acceptCircuit_le_affine :
    Circuit.gateCount (acceptCircuit (M := M) (n := n)) ≤
      affineIter (M := M) (n := n) (M.runTime n) := by
  exact
    Nat.le_trans
      (gateCount_acceptCircuit_le_total (M := M) (n := n))
      (totalGateCount_runtime_le_affine (M := M) (n := n))

/-- Translating the gate-count estimate into a `sizeOf` inequality—the form
expected by `InPpoly`. -/
lemma sizeOf_acceptCircuit_le_affine :
    sizeOf (acceptCircuit (M := M) (n := n)) ≤
      affineIter (M := M) (n := n) (M.runTime n) := by
  exact
    Nat.le_trans
      (Circuit.sizeOf_le_gateCount
        (acceptCircuit (M := M) (n := n)))
      (gateCount_acceptCircuit_le_affine (M := M) (n := n))

end AcceptanceBounds

/-!
### Bounding the tape length using the polynomial run-time hypothesis

The forthcoming sections will gradually tighten the coarse affine bounds until
they match the polynomial size requirement from `InPpoly`.  As a first step we
record a purely arithmetic inequality: if the running time of a machine is
dominated by `n ↦ n^c + c`, then the tape length `n + runTime n + 1` is itself
bounded by a polynomial with exponent `max 1 c`.  While simple, phrasing the
statement explicitly keeps subsequent calculations uncluttered.
-/

section RuntimePolynomialBounds

open Complexity

variable {M : TM} {c : ℕ}

/-- Exponent used when turning the run-time bound `runTime n ≤ n^c + c` into a
uniform polynomial estimate.  Making the exponent at least one avoids special
cases in elementary inequalities such as `n ≤ n^k`. -/
def runtimeExponent (c : ℕ) : ℕ := max 1 c

lemma one_le_runtimeExponent : 1 ≤ runtimeExponent c := by
  unfold runtimeExponent
  exact Nat.le_max_left _ _

lemma le_runtimeExponent : c ≤ runtimeExponent c := by
  unfold runtimeExponent
  exact Nat.le_max_right _ _

/-- Auxiliary arithmetic fact used in the proof of `tapeLength_le_poly`. -/
lemma tapeLength_aux_bound (n c : ℕ) :
    let k := runtimeExponent c in n + n ^ c + c + 1 ≤
      3 * (n ^ k + k) := by
  intro k
  have hk_one : 1 ≤ k := by
    simpa [runtimeExponent] using one_le_runtimeExponent (c := c)
  have hc_le_k : c ≤ k := by
    simpa [runtimeExponent] using le_runtimeExponent (c := c)
  cases n with
  | zero =>
      have hPow_le_one : 0 ^ c ≤ 1 := by
        cases c with
        | zero => simp
        | succ c => simp [Nat.pow_succ]
      have hPow_le_k : 0 ^ c ≤ k := Nat.le_trans hPow_le_one hk_one
      have hsum₁ : 0 ^ c + c ≤ k + k := Nat.add_le_add hPow_le_k hc_le_k
      have hsum₂ : 0 ^ c + c + 1 ≤ k + k + 1 := Nat.add_le_add_right hsum₁ 1
      have hsum₃ : k + k + 1 ≤ k + k + k :=
        Nat.add_le_add_left hk_one (k + k)
      have htotal : 0 ^ c + c + 1 ≤ k + k + k :=
        Nat.le_trans hsum₂ hsum₃
      have hk_ne_zero : k ≠ 0 := by
        exact (Nat.lt_of_le_of_lt hk_one (Nat.lt_succ_self 0)).ne'
      obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
      have hZeroPow : 0 ^ k = 0 := by
        simpa [hk', Nat.pow_succ] using (show 0 ^ (Nat.succ k') = 0 by simp)
      have hTriple : k + k + k = 3 * (0 ^ k + k) := by
        simp [hZeroPow, Nat.mul_add, Nat.add_mul, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      simpa [hTriple, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using htotal
  | succ m =>
      have hn_pos : 1 ≤ m.succ := Nat.succ_le_succ (Nat.zero_le m)
      have hpow_dom : m.succ ^ c ≤ m.succ ^ k :=
        Nat.pow_le_pow_of_le_left hn_pos hc_le_k
      have hnat_le_pow : m.succ ≤ m.succ ^ k := by
        have := Nat.pow_le_pow_of_le_left hn_pos hk_one
        simpa using this
      have hsum₁ := Nat.add_le_add hnat_le_pow hpow_dom
      have hsum₂ := Nat.add_le_add_right hsum₁ c
      have hsum₃ := Nat.add_le_add_right hsum₂ 1
      have hone_le : 1 ≤ m.succ ^ k :=
        Nat.le_trans (Nat.succ_le_succ (Nat.zero_le m)) hnat_le_pow
      have hconst :
          m.succ ^ k + m.succ ^ k + c + 1 ≤
            m.succ ^ k + m.succ ^ k + k + m.succ ^ k := by
        have hkconst : c ≤ k := hc_le_k
        have := Nat.add_le_add (Nat.le_refl _) hkconst
        have := Nat.add_le_add_right this 1
        exact
          (Nat.le_trans this
            (Nat.add_le_add_left hone_le (m.succ ^ k + m.succ ^ k + k)))
      have htotal := Nat.le_trans hsum₃ hconst
      have hk_le : k ≤ 3 * k := by
        have : (1 : ℕ) ≤ 3 := by decide
        simpa [Nat.mul_comm] using
          (Nat.mul_le_mul_right k this)
      have :
          m.succ ^ k + m.succ ^ k + k + m.succ ^ k ≤
            3 * (m.succ ^ k + k) := by
        have := Nat.add_le_add_left hk_le (3 * m.succ ^ k)
        simpa [Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
          using this
      exact Nat.le_trans htotal this

/--
Tape length is bounded by the same polynomial that governs the running time,
up to a harmless constant factor.  This reformulation avoids carrying the
`n + runTime n + 1` expression in later proofs.
-/
lemma tapeLength_le_poly (hRun : ∀ n, M.runTime n ≤ n^c + c) :
    ∀ n, M.tapeLength (M := M) n ≤
      3 * (n ^ runtimeExponent c + runtimeExponent c) := by
  intro n
  have hAdd := Nat.add_le_add_left (hRun n) n
  have hAdd' := Nat.add_le_add_right hAdd 1
  have hTape : M.tapeLength (M := M) n ≤ n + n ^ c + c + 1 := by
    simpa [TM.tapeLength, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hAdd'
  have := tapeLength_aux_bound n c
  simpa [runtimeExponent, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using Nat.le_trans hTape this

end RuntimePolynomialBounds

/--
### Polynomial domination for the affine bounds

The coarse affine recurrence developed earlier bounds the gate counts by means
of the parameters `affineFactor` and `affineOffset`.  To exploit the
polynomial running-time hypothesis we now express these parameters themselves
through explicit polynomials.
-/
section AffinePolynomialBounds

open Complexity

variable {M : TM} {c : ℕ}

/-!
We introduce a compact notation for the polynomial `n ↦ n ^ runtimeExponent c
+ runtimeExponent c` that bounds both the running time and, by the lemma above,
the tape length.  Working with this helper keeps the subsequent inequalities
manageable.
-/

/-- Base polynomial dominating both the running time and tape length. -/
def polyBase (n : ℕ) : ℕ :=
  n ^ runtimeExponent c + runtimeExponent c

lemma one_le_polyBase (n : ℕ) : 1 ≤ polyBase (c := c) n := by
  unfold polyBase
  have hk : 1 ≤ runtimeExponent c := one_le_runtimeExponent (c := c)
  exact Nat.le_trans hk (Nat.le_add_left _ _)

lemma tapeLength_pos (M : TM) (n : ℕ) :
    1 ≤ M.tapeLength n := by
  unfold TM.tapeLength
  exact Nat.succ_le_succ (Nat.zero_le _)

lemma one_le_affineFactor {M : TM} {n : ℕ} :
    1 ≤ affineFactor (M := M) (n := n) := by
  classical
  have hL : 1 ≤ M.tapeLength n := tapeLength_pos (M := M) (n := n)
  have hcoeff : 1 ≤ 5 + 4 * stateCard M := by
    have hFive : 1 ≤ 5 := by decide
    exact Nat.le_trans hFive (Nat.le_add_right _ _)
  have hMain : 1 ≤ M.tapeLength n * (5 + 4 * stateCard M) := by
    have := Nat.mul_le_mul hL hcoeff
    simpa using this
  have hAdd :
      M.tapeLength n * (5 + 4 * stateCard M) ≤
        affineFactor (M := M) (n := n) := by
    have := Nat.le_add_right
        (M.tapeLength n * (5 + 4 * stateCard M))
        ((8 * stateCard M) * (M.tapeLength n * M.tapeLength n) +
          6 * (stateCard M * stateCard M))
    simpa [affineFactor, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  exact Nat.le_trans hMain hAdd

lemma geomSum_le_mul_pow (a t : ℕ) (ha : 1 ≤ a) :
    geomSum a t ≤ (t + 1) * a ^ t := by
  classical
  induction t with
  | zero =>
      simp [geomSum]
  | succ t ih =>
      have hgeom : geomSum a (t + 1) = geomSum a t + a ^ t := by
        simp [geomSum]
      have hpow : a ^ t ≤ a ^ (t + 1) := by
        simpa [Nat.pow_succ, Nat.mul_comm] using
          Nat.mul_le_mul_left (a ^ t) ha
      have hstep :
          geomSum a t + a ^ t ≤ (t + 1 + 1) * a ^ t := by
        have := Nat.add_le_add ih (Nat.le_refl _)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      have hscale : (t + 1 + 1) * a ^ t ≤ (t + 1 + 1) * a ^ (t + 1) := by
        exact Nat.mul_le_mul_left _ hpow
      have := Nat.le_trans hstep hscale
      simpa [hgeom, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
        using this

lemma polyBase_le_sq (n : ℕ) :
    polyBase (c := c) n ≤
      polyBase (c := c) n * polyBase (c := c) n := by
  have h₁ : 1 ≤ polyBase (c := c) n := one_le_polyBase (c := c) (n := n)
  calc
    polyBase (c := c) n
        = polyBase (c := c) n * 1 := by simp
    _ ≤ polyBase (c := c) n * polyBase (c := c) n :=
          Nat.mul_le_mul_left _ h₁

lemma polyBase_sq_le_cube (n : ℕ) :
    polyBase (c := c) n * polyBase (c := c) n ≤
      polyBase (c := c) n * polyBase (c := c) n *
        polyBase (c := c) n := by
  have h₁ : 1 ≤ polyBase (c := c) n := one_le_polyBase (c := c) (n := n)
  have := Nat.mul_le_mul_left
      (polyBase (c := c) n * polyBase (c := c) n) h₁
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

lemma tapeLength_le_polyBase {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    M.tapeLength (M := M) n ≤ 3 * polyBase (c := c) n := by
  simpa [polyBase]
    using tapeLength_le_poly (M := M) (c := c) (n := n) hRun

/--
`polyBase` is dominated by a very concrete polynomial of degree
`runtimeExponent c + 1`.  The estimate is intentionally phrased using
simple shifts of `n`; this shape will be convenient when normalising the
final size bounds into the canonical `n^k + k` form required by
`InPpoly`.-/
lemma polyBase_le_mul_pow (n : ℕ) :
    polyBase (c := c) n ≤
      (n + 1) ^ runtimeExponent c *
        (n + runtimeExponent c + 1) := by
  classical
  set R := runtimeExponent c
  have hRpos : 1 ≤ R := one_le_runtimeExponent (c := c)
  -- The term `n^R` is bounded by the same power of `n + 1`, and the
  -- multiplicative factor simply records the additional shift by `R`.
  have hPow :=
    pow_le_pow_of_le_base (a := n) (b := n + 1) (k := R)
      (Nat.le_succ n)
  have hMulBase :
      n ^ R ≤ n ^ R * (n + R + 1) := by
    have hPos : 1 ≤ n + R + 1 := by
      exact Nat.succ_le_succ (Nat.zero_le (n + R))
    have := Nat.mul_le_mul_left (n ^ R) hPos
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hTerm₁ :=
    Nat.le_trans hMulBase (Nat.mul_le_mul_right _ hPow)
  -- The additive constant `R` is also absorbed by the same factor.
  have hTerm₂ :
      R ≤ (n + 1) ^ R * (n + R + 1) := by
    have hBound : R ≤ n + R + 1 := by
      have := Nat.le_add_left R n
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    have hPowPos : 1 ≤ (n + 1) ^ R := by
      have hbase : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have := Nat.pow_le_pow_of_le_left hbase hRpos
      simpa [Nat.one_pow] using this
    have := Nat.mul_le_mul hPowPos hBound
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  -- Combine both pieces to bound `polyBase` itself.
  have hAdd := Nat.add_le_add hTerm₁ hTerm₂
  simpa [polyBase, R, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hAdd

/--
The augmented base `gateBoundBase` inherits the polynomial control from
`polyBase`.  We obtain a slightly larger but still explicit polynomial
bound by observing that `max a 2 ≤ a + 2`.-/
lemma gateBoundBase_le_poly (n : ℕ) :
    gateBoundBase (M := M) (c := c) n ≤
      (n + 1) ^ runtimeExponent c *
        (n + runtimeExponent c + 1) + 2 := by
  classical
  have hMax : gateBoundBase (M := M) (c := c) n ≤
      polyBase (M := M) (c := c) n + 2 := by
    unfold gateBoundBase
    have : polyBase (M := M) (c := c) n ≤ polyBase (M := M) (c := c) n + 2 :=
      Nat.le_add_right _ _
    have : max (polyBase (M := M) (c := c) n) 2 ≤
        polyBase (M := M) (c := c) n + 2 :=
      by
        refine
          (max_le_iff.mpr ?_)
        constructor
        · exact Nat.le_add_right _ _
        · have : 2 ≤ (polyBase (M := M) (c := c) n) + 2 := by
            exact Nat.le_add_left _ _
          simpa using this
    simpa using this
  have :=
    Nat.add_le_add (polyBase_le_mul_pow (M := M) (c := c) (n := n))
      (Nat.le_refl 2)
  exact Nat.le_trans hMax this

/-- Linear coefficient used when bounding `affineFactor`. -/
def affineFactorLinearCoeff (M : TM) : ℕ :=
  3 * (5 + 4 * stateCard M)

/-- Quadratic coefficient used when bounding `affineFactor`. -/
def affineFactorQuadraticCoeff (M : TM) : ℕ :=
  72 * stateCard M

/-- Constant coefficient used when bounding `affineFactor`. -/
def affineFactorConstantCoeff (M : TM) : ℕ :=
  6 * stateCard M * stateCard M

/-- Combined coefficient for the quadratic bound on `affineFactor`. -/
def affineFactorPolyCoeff (M : TM) : ℕ :=
  affineFactorLinearCoeff M +
    affineFactorQuadraticCoeff M + affineFactorConstantCoeff M

/--
`affineFactor` contains the product `tapeLength * (5 + 4 · stateCard)`; this
lemma bounds the contribution by a multiple of the base polynomial.
-/
lemma affineFactor_linear_bound {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    M.tapeLength (M := M) n * (5 + 4 * stateCard M) ≤
      affineFactorLinearCoeff M * polyBase (c := c) n := by
  classical
  have hTape := tapeLength_le_polyBase (M := M) (c := c) (n := n) hRun
  have := Nat.mul_le_mul_right (5 + 4 * stateCard M) hTape
  simpa [affineFactorLinearCoeff, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]
    using this

/-- Quadratic part of `affineFactor` dominated by the base polynomial. -/
lemma affineFactor_quadratic_bound {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    (8 * stateCard M) *
        (M.tapeLength (M := M) n * M.tapeLength (M := M) n) ≤
      affineFactorQuadraticCoeff M *
        (polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have hTape := tapeLength_le_polyBase (M := M) (c := c) (n := n) hRun
  have hSq :
      M.tapeLength (M := M) n * M.tapeLength (M := M) n ≤
        (3 * P) * (3 * P) :=
    Nat.mul_le_mul hTape hTape
  have := Nat.mul_le_mul_left (8 * stateCard M) hSq
  simpa [affineFactorQuadraticCoeff, P, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc, Nat.mul_add, Nat.add_mul]
    using this

/-- Constant contribution of `affineFactor` absorbed into the quadratic term. -/
lemma affineFactor_constant_bound {n : ℕ} :
    6 * stateCard M * stateCard M ≤
      affineFactorConstantCoeff M *
        (polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have hP : 1 ≤ P := one_le_polyBase (c := c) (n := n)
  have hPP : P ≤ P * P := by
    have := Nat.mul_le_mul_left P hP
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have : 1 ≤ P * P := Nat.le_trans hP hPP
  have := Nat.mul_le_mul_left (6 * stateCard M * stateCard M) this
  simpa [affineFactorConstantCoeff, P, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]
    using this

/-- Quadratic polynomial domination for the full `affineFactor`. -/
lemma affineFactor_le_poly {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    affineFactor (M := M) (n := n) ≤
      affineFactorPolyCoeff M *
        (polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have hLinear := affineFactor_linear_bound
    (M := M) (c := c) (n := n) hRun
  have hQuad := affineFactor_quadratic_bound
    (M := M) (c := c) (n := n) hRun
  have hConst := affineFactor_constant_bound
    (M := M) (c := c) (n := n)
  have hLinear' :
      M.tapeLength (M := M) n * (5 + 4 * stateCard M) ≤
        affineFactorLinearCoeff M * (P * P) := by
    have hPP : P ≤ P * P := polyBase_le_sq (c := c) (n := n)
    have := Nat.mul_le_mul_left (affineFactorLinearCoeff M) hPP
    exact Nat.le_trans hLinear
      (by
        simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using this)
  have hSum := Nat.add_le_add (Nat.add_le_add hLinear' hQuad) hConst
  simpa [affineFactor, affineFactorPolyCoeff, P, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]
    using hSum

/-- Coefficient governing the cubic bound on `affineOffset`. -/
def affineOffsetPolyCoeff (M : TM) : ℕ :=
  3 * (22 * stateCard M + 5) +
    3 * (1 + 70 * stateCard M) +
    stateCard M * (1 + 22 * stateCard M)

/-- Coefficient controlling the initial gate-count vector. -/
def initialPolyCoeff (M : TM) : ℕ := 6 + stateCard M

/--
First summand of `affineOffset` bounded by a cubic polynomial in the base
quantity `polyBase`.
-/
lemma affineOffset_first_bound {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    M.tapeLength (M := M) n *
        ((2 * stateCard M) * (2 * M.tapeLength (M := M) n + 5) + 5) ≤
      3 * (22 * stateCard M + 5) *
        (polyBase (c := c) n * polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have hTape := tapeLength_le_polyBase (M := M) (c := c) (n := n) hRun
  have hP : 1 ≤ P := one_le_polyBase (c := c) (n := n)
  have h2L : 2 * M.tapeLength (M := M) n ≤ 6 * P := by
    have := Nat.mul_le_mul_left 2 hTape
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hInside₁ :
      2 * M.tapeLength (M := M) n + 5 ≤ 6 * P + 5 :=
    Nat.add_le_add h2L (Nat.le_refl _)
  have hFive : 5 ≤ 5 * P := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 5 hP
  have hInside₂ : 6 * P + 5 ≤ 6 * P + 5 * P :=
    Nat.add_le_add (Nat.le_refl _) hFive
  have hInside : 2 * M.tapeLength (M := M) n + 5 ≤ 11 * P := by
    have := Nat.le_trans hInside₁ hInside₂
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hMult :
      (2 * stateCard M) * (2 * M.tapeLength (M := M) n + 5) ≤
        (22 * stateCard M) * P :=
    Nat.mul_le_mul_left _ hInside
  have hTerm :
      (2 * stateCard M) * (2 * M.tapeLength (M := M) n + 5) + 5 ≤
        (22 * stateCard M + 5) * P := by
    have hFive' : 5 ≤ 5 * P := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left 5 hP
    have := Nat.add_le_add hMult hFive'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hProd := Nat.mul_le_mul hTape hTerm
  have hCube :
      P * P ≤ P * P * P := polyBase_sq_le_cube (c := c) (n := n)
  have hProd' :
      M.tapeLength (M := M) n *
          ((2 * stateCard M) * (2 * M.tapeLength (M := M) n + 5) + 5) ≤
        3 * (22 * stateCard M + 5) * (P * P) := by
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hProd
  have hCube' :
      3 * (22 * stateCard M + 5) * (P * P) ≤
        3 * (22 * stateCard M + 5) * (P * P * P) := by
    have := Nat.mul_le_mul_left (3 * (22 * stateCard M + 5)) hCube
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  exact Nat.le_trans hProd' hCube'

/--
Second summand of `affineOffset` controlled by a cubic polynomial in the base
quantity.
-/
lemma affineOffset_second_bound {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    M.tapeLength (M := M) n *
        (1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength (M := M) n +
              M.tapeLength (M := M) n *
                (2 * M.tapeLength (M := M) n + 4))) ≤
      3 * (1 + 70 * stateCard M) *
        (polyBase (c := c) n * polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have hTape := tapeLength_le_polyBase (M := M) (c := c) (n := n) hRun
  have hP : 1 ≤ P := one_le_polyBase (c := c) (n := n)
  -- Bound `2L + 4` by `10P`.
  have h2L : 2 * M.tapeLength (M := M) n ≤ 6 * P := by
    have := Nat.mul_le_mul_left 2 hTape
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hInside₁ : 2 * M.tapeLength (M := M) n + 4 ≤ 6 * P + 4 :=
    Nat.add_le_add h2L (Nat.le_refl _)
  have hFour : 4 ≤ 4 * P := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hP
  have hInside₂ : 6 * P + 4 ≤ 6 * P + 4 * P :=
    Nat.add_le_add (Nat.le_refl _) hFour
  have hInside : 2 * M.tapeLength (M := M) n + 4 ≤ 10 * P := by
    have := Nat.le_trans hInside₁ hInside₂
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hLmul :
      M.tapeLength (M := M) n *
          (2 * M.tapeLength (M := M) n + 4) ≤ 30 * (P * P) := by
    have := Nat.mul_le_mul hTape hInside
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul]
      using this
  -- Collect the pieces of `1 + L + L*(2L+4)`.
  have hPP : P ≤ P * P := polyBase_le_sq (c := c) (n := n)
  have hOne_to_pp : 1 ≤ P * P :=
    Nat.le_trans hP hPP
  have hL_to_pp :
      M.tapeLength (M := M) n ≤ 3 * (P * P) := by
    have := Nat.mul_le_mul_left 3 hPP
    exact Nat.le_trans hTape
      (by
        simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using this)
  have hSum_base :
      M.tapeLength (M := M) n +
          M.tapeLength (M := M) n *
            (2 * M.tapeLength (M := M) n + 4) ≤
        (3 + 30) * (P * P) := by
    have := Nat.add_le_add hL_to_pp hLmul
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
      using this
  have hInner_bound :
      1 + M.tapeLength (M := M) n +
          M.tapeLength (M := M) n *
            (2 * M.tapeLength (M := M) n + 4) ≤
        34 * (P * P) := by
    have := Nat.add_le_add hOne_to_pp hSum_base
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
      using this
  -- Multiply by `2 * stateCard M` and add the remaining constants.
  have hInner_scaled :
      (2 * stateCard M) *
          (1 + M.tapeLength (M := M) n +
            M.tapeLength (M := M) n *
              (2 * M.tapeLength (M := M) n + 4)) ≤
        (68 * stateCard M) * (P * P) := by
    have := Nat.mul_le_mul_left (2 * stateCard M) hInner_bound
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
      using this
  have hInner_total :
      1 + 2 * stateCard M +
          (2 * stateCard M) *
            (1 + M.tapeLength (M := M) n +
              M.tapeLength (M := M) n *
                (2 * M.tapeLength (M := M) n + 4)) ≤
        (1 + 70 * stateCard M) * (P * P) := by
    have hTwo : 2 * stateCard M ≤ 2 * stateCard M * (P * P) := by
      have := Nat.mul_le_mul_left (2 * stateCard M) hPP
      simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this
    have := Nat.add_le_add hOne_to_pp hTwo
    have := Nat.add_le_add this hInner_scaled
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
      using this
  have hProd := Nat.mul_le_mul hTape hInner_total
  have hCube :
      P * P ≤ P * P * P := polyBase_sq_le_cube (c := c) (n := n)
  have := Nat.mul_le_mul_left (3 * (1 + 70 * stateCard M)) hCube
  exact
    Nat.le_trans
      (by
        simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hProd)
      (by
        simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using this)

/-- Third summand of `affineOffset` bounded by a cubic polynomial. -/
lemma affineOffset_third_bound {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    stateCard M *
        (1 + 2 * stateCard M +
          (2 * stateCard M) *
            (2 * M.tapeLength (M := M) n + 4)) ≤
      stateCard M * (1 + 22 * stateCard M) *
        (polyBase (c := c) n * polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have hTape := tapeLength_le_polyBase (M := M) (c := c) (n := n) hRun
  have hP : 1 ≤ P := one_le_polyBase (c := c) (n := n)
  have hInside : 2 * M.tapeLength (M := M) n + 4 ≤ 10 * P := by
    have h2L : 2 * M.tapeLength (M := M) n ≤ 6 * P := by
      have := Nat.mul_le_mul_left 2 hTape
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    have hInside₁ := Nat.add_le_add h2L (Nat.le_refl (4 : ℕ))
    have hFour : 4 ≤ 4 * P := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hP
    have hInside₂ := Nat.add_le_add (Nat.le_refl _) hFour
    have := Nat.le_trans hInside₁ hInside₂
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  have hTerm :
      (2 * stateCard M) * (2 * M.tapeLength (M := M) n + 4) ≤
        (20 * stateCard M) * P := by
    have := Nat.mul_le_mul_left (2 * stateCard M) hInside
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul]
      using this
  have hBase :
      1 + 2 * stateCard M +
          (2 * stateCard M) *
            (2 * M.tapeLength (M := M) n + 4) ≤
        (1 + 22 * stateCard M) * P := by
    have hTwo : 2 * stateCard M ≤ 2 * stateCard M * P := by
      have := Nat.mul_le_mul_left (2 * stateCard M)
          (one_le_polyBase (c := c) (n := n))
      simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this
    have hFive : 1 ≤ P := hP
    have := Nat.add_le_add hFive hTwo
    have := Nat.add_le_add this hTerm
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
      using this
  have hCube :
      P ≤ P * P * P := by
    have hPP : P ≤ P * P := polyBase_le_sq (c := c) (n := n)
    have hPPP := Nat.mul_le_mul_left P hPP
    exact Nat.le_trans hPP
      (by
        simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using hPPP)
  have := Nat.mul_le_mul_left (stateCard M * (1 + 22 * stateCard M)) hCube
  have hProd :
      stateCard M *
          (1 + 2 * stateCard M +
            (2 * stateCard M) *
              (2 * M.tapeLength (M := M) n + 4)) ≤
        stateCard M * (1 + 22 * stateCard M) * P := by
    have := Nat.mul_le_mul_left (stateCard M) hBase
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  exact Nat.le_trans hProd
    (by
      simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this)

/-- Cubic polynomial domination for the full `affineOffset`. -/
lemma affineOffset_le_poly {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    affineOffset (M := M) (n := n) ≤
      affineOffsetPolyCoeff M *
        (polyBase (c := c) n * polyBase (c := c) n * polyBase (c := c) n) := by
  classical
  set P := polyBase (c := c) n
  have h₁ := affineOffset_first_bound
    (M := M) (c := c) (n := n) hRun
  have h₂ := affineOffset_second_bound
    (M := M) (c := c) (n := n) hRun
  have h₃ := affineOffset_third_bound
    (M := M) (c := c) (n := n) hRun
  have hSum := Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃
  simpa [affineOffset, affineOffsetPolyCoeff, P, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Nat.mul_add, Nat.add_mul]
    using hSum

lemma totalBound_initial_le_poly {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    totalBound (initialBounds (M := M) (n := n)) ≤
      initialPolyCoeff M * polyBase (c := c) n := by
  classical
  set P := polyBase (c := c) n
  have hTape := tapeLength_le_polyBase (M := M) (c := c) (n := n) hRun
  have hP : 1 ≤ P := one_le_polyBase (c := c) (n := n)
  have hDouble :
      2 * M.tapeLength (M := M) n ≤ 6 * P := by
    have := Nat.mul_le_mul_left (2) hTape
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hState : stateCard M ≤ stateCard M * P := by
    have := Nat.mul_le_mul_left (stateCard M) hP
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hSum := Nat.add_le_add hDouble hState
  have hTotal :
      totalBound (initialBounds (M := M) (n := n)) ≤
        6 * P + stateCard M * P := by
    simpa [totalBound, initialBounds, P, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hSum
  have hRewrite :
      6 * P + stateCard M * P = initialPolyCoeff M * P := by
    simp [initialPolyCoeff, P, Nat.mul_add, Nat.add_mul, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
  have hGoal :
      6 * P + stateCard M * P ≤ initialPolyCoeff M * P := by
    simpa [hRewrite]
  exact Nat.le_trans hTotal hGoal

end AffinePolynomialBounds

/-!
### Exponential-form bounds for the affine recurrence

The closed form obtained for `affineIter` expresses the iterate as a combination
of the initial gate bound and a geometric series in `affineFactor`.  For later
estimates it is convenient to turn this into a single product bounded by
`affineFactor ^ t`.  The following lemmas isolate this transformation and
record a few coarse inequalities relating the run-time parameter to the helper
polynomial `polyBase`.
-/

section AffineIterBounds

open Complexity

variable {M : TM} {n c : ℕ}

/--
`affineIter` is dominated by the product of `affineFactor ^ t` and a linear
combination of the initial and offset bounds.  The inequality merely packages
the closed form with the elementary estimate on the geometric series.
-/
lemma affineIter_le_pow (t : ℕ) :
    affineIter (M := M) (n := n) t ≤
      (totalBound (initialBounds (M := M) (n := n)) +
          (t + 1) * affineOffset (M := M) (n := n)) *
        (affineFactor (M := M) (n := n)) ^ t := by
  classical
  have hgeom :=
    geomSum_le_mul_pow
      (affineFactor (M := M) (n := n))
      t (one_le_affineFactor (M := M) (n := n))
  have hmul :
      affineOffset (M := M) (n := n) *
          geomSum (affineFactor (M := M) (n := n)) t ≤
        affineOffset (M := M) (n := n) *
          ((t + 1) * (affineFactor (M := M) (n := n)) ^ t) := by
    exact Nat.mul_le_mul_left _ hgeom
  have hsum :=
    Nat.add_le_add_left hmul
      ((affineFactor (M := M) (n := n)) ^ t *
        totalBound (initialBounds (M := M) (n := n)))
  have hcalc :
      affineIter (M := M) (n := n) t ≤
        (affineFactor (M := M) (n := n)) ^ t *
            totalBound (initialBounds (M := M) (n := n)) +
          affineOffset (M := M) (n := n) *
            ((t + 1) * (affineFactor (M := M) (n := n)) ^ t) := by
    simpa [affineIter_closed_form] using hsum
  have hrewrite :
      (affineFactor (M := M) (n := n)) ^ t *
          totalBound (initialBounds (M := M) (n := n)) +
        affineOffset (M := M) (n := n) *
          ((t + 1) * (affineFactor (M := M) (n := n)) ^ t) =
        (totalBound (initialBounds (M := M) (n := n)) +
            (t + 1) * affineOffset (M := M) (n := n)) *
          (affineFactor (M := M) (n := n)) ^ t := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  simpa [hrewrite] using hcalc

/--
The polynomial run-time hypothesis bounds `runTime n` itself by the helper
polynomial `polyBase`.  This reformulates the estimate `runTime n ≤ n^c + c`
while eliminating the exponent `c` in favour of the uniform choice
`runtimeExponent c`.
-/
lemma runTime_le_polyBase {n : ℕ}
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    M.runTime n ≤ polyBase (M := M) (c := c) n := by
  classical
  have hk : c ≤ runtimeExponent c := le_runtimeExponent (c := c)
  have hbound := hRun n
  cases n with
  | zero =>
      cases c with
      | zero =>
          have hkpos : 1 ≤ runtimeExponent 0 := one_le_runtimeExponent (c := 0)
          have htotal : 0 ^ 0 + 0 ≤
              0 ^ runtimeExponent 0 + runtimeExponent 0 := by
            simp [Nat.pow_zero, runtimeExponent, hkpos]
          simpa [polyBase, runtimeExponent] using
            Nat.le_trans hbound htotal
      | succ c =>
          have htotal :
              0 ^ Nat.succ c + Nat.succ c ≤
                0 ^ runtimeExponent (Nat.succ c) +
                  runtimeExponent (Nat.succ c) := by
            simp [runtimeExponent, Nat.pow_succ]
          simpa [polyBase, runtimeExponent]
            using Nat.le_trans hbound htotal
  | succ m =>
      have hpos : 1 ≤ Nat.succ m := Nat.succ_le_succ (Nat.zero_le m)
      have hpow :=
        Nat.pow_le_pow_of_le_left hpos hk
      have := Nat.add_le_add hpow hk
      have htotal := Nat.le_trans hbound this
      simpa [polyBase, runtimeExponent]
        using htotal

end AffineIterBounds

/--
Helper coefficient absorbing the linear contribution of the initial gate-count
vector together with the (scaled) affine offset.  Keeping the quantity
explicit simplifies the book-keeping in later bounds.-/
def affineIterLeadCoeff (M : TM) : ℕ :=
  initialPolyCoeff M + 2 * affineOffsetPolyCoeff M

lemma one_le_affineFactorPolyCoeff (M : TM) : 1 ≤ affineFactorPolyCoeff M := by
  have hLinear : 1 ≤ affineFactorLinearCoeff M := by
    have h15 : 1 ≤ 3 * 5 := by decide
    have hAdd : 5 ≤ 5 + 4 * stateCard M := Nat.le_add_right _ _
    have hMul := Nat.mul_le_mul_left (3) hAdd
    exact
      (by
        simpa [affineFactorLinearCoeff]
          using Nat.le_trans h15 hMul)
  have hLe : affineFactorLinearCoeff M ≤ affineFactorPolyCoeff M := by
    have :=
      Nat.le_add_left (affineFactorLinearCoeff M)
        (affineFactorQuadraticCoeff M + affineFactorConstantCoeff M)
    simpa [affineFactorPolyCoeff, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  exact Nat.le_trans hLinear hLe

lemma one_le_affineIterLeadCoeff (M : TM) : 1 ≤ affineIterLeadCoeff M := by
  have hInit : 1 ≤ initialPolyCoeff M := by
    have : 1 ≤ 6 := by decide
    have hState : 0 ≤ stateCard M := Nat.zero_le _
    have hSum : 6 ≤ 6 + stateCard M := Nat.le_add_right _ _
    exact
      (by
        simpa [initialPolyCoeff]
          using Nat.le_trans this hSum)
  have hLe : initialPolyCoeff M ≤ affineIterLeadCoeff M := by
    have := Nat.le_add_left (initialPolyCoeff M) (2 * affineOffsetPolyCoeff M)
    simpa [affineIterLeadCoeff]
      using this
  exact Nat.le_trans hInit hLe

lemma succ_le_two_mul_of_le {t P : ℕ} (h : t ≤ P) (hP : 1 ≤ P) : t + 1 ≤ 2 * P := by
  have ht : t + 1 ≤ P + 1 := Nat.succ_le_succ h
  have hDouble : P + 1 ≤ P + P := by
    have := Nat.add_le_add_left hP P
    simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  exact Nat.le_trans ht (by simpa [two_mul, Nat.add_comm] using hDouble)

lemma le_pow_four_of_one_le {P : ℕ} (hP : 1 ≤ P) : P ≤ P ^ 4 := by
  have h₁ : P ≤ P * P := by
    have := Nat.mul_le_mul_left P hP
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have h₂ : P * P ≤ P * P * P := by
    have := Nat.mul_le_mul_left (P * P) hP
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have h₃ : P * P * P ≤ P * P * P * P := by
    have := Nat.mul_le_mul_left (P * P * P) hP
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have := Nat.le_trans h₁ (Nat.le_trans h₂ h₃)
  simpa [Nat.pow_succ, Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]
    using this

lemma affineIter_linear_factor_le_poly
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    totalBound (initialBounds (M := M) (n := n)) +
        (M.runTime n + 1) * affineOffset (M := M) (n := n) ≤
      affineIterLeadCoeff M *
        (polyBase (M := M) (c := c) n) ^ 4 := by
  classical
  set P := polyBase (M := M) (c := c) n
  have hP : 1 ≤ P := one_le_polyBase (M := M) (c := c) (n := n)
  have hRunBound := runTime_le_polyBase (M := M) (c := c) (n := n) hRun
  have hInit := totalBound_initial_le_poly (M := M) (c := c) (n := n) hRun
  have hOffset := affineOffset_le_poly (M := M) (c := c) (n := n) hRun
  have hSucc : M.runTime n + 1 ≤ 2 * P :=
    succ_le_two_mul_of_le (t := M.runTime n) (P := P) hRunBound hP
  have hOffset' :
      (M.runTime n + 1) * affineOffset (M := M) (n := n) ≤
        (2 * P) * (affineOffsetPolyCoeff M * P ^ 3) := by
    have := Nat.mul_le_mul hSucc hOffset
    simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.pow_succ, Nat.pow_two]
      using this
  have hOffsetBound :
      (M.runTime n + 1) * affineOffset (M := M) (n := n) ≤
        (2 * affineOffsetPolyCoeff M) * P ^ 4 := by
    have := hOffset'
    simpa [P, Nat.pow_succ, Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc]
      using this
  have hInitPow :
      initialPolyCoeff M * P ≤ initialPolyCoeff M * P ^ 4 := by
    have := le_pow_four_of_one_le (P := P) hP
    exact Nat.mul_le_mul_left _ this
  have hInitBound :
      totalBound (initialBounds (M := M) (n := n)) ≤
        initialPolyCoeff M * P ^ 4 :=
    Nat.le_trans hInit hInitPow
  have hSum :=
    Nat.add_le_add hInitBound hOffsetBound
  have hRewrite :
      initialPolyCoeff M * P ^ 4 +
          (2 * affineOffsetPolyCoeff M) * P ^ 4 =
        affineIterLeadCoeff M * P ^ 4 := by
    simp [affineIterLeadCoeff, Nat.mul_add, Nat.add_mul, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc]
  simpa [P, hRewrite]
    using hSum

lemma pow_le_pow_of_le_base {a b : ℕ} (h : a ≤ b) (t : ℕ) : a ^ t ≤ b ^ t := by
  induction t with
  | zero => simpa
  | succ t ih =>
      have h₁ : a ^ t * a ≤ a ^ t * b := Nat.mul_le_mul_left _ h
      have h₂ : a ^ t * b ≤ b ^ t * b := Nat.mul_le_mul_right _ ih
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using Nat.le_trans h₁ h₂

lemma affineFactor_pow_le_poly
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    (affineFactor (M := M) (n := n)) ^ (M.runTime n) ≤
      (affineFactorPolyCoeff M *
          (polyBase (M := M) (c := c) n) ^ 2) ^
        (polyBase (M := M) (c := c) n) := by
  classical
  set P := polyBase (M := M) (c := c) n
  have hBase :
      affineFactor (M := M) (n := n) ≤
        affineFactorPolyCoeff M * P ^ 2 :=
    affineFactor_le_poly (M := M) (c := c) (n := n) hRun
  have hPow :=
    pow_le_pow_of_le_base hBase (M.runTime n)
  have hRunBound := runTime_le_polyBase (M := M) (c := c) (n := n) hRun
  have hCoeffPos : 0 < affineFactorPolyCoeff M := by
    have h := one_le_affineFactorPolyCoeff M
    exact Nat.succ_le_iff.mp (by simpa using h)
  have hPpos : 0 < P :=
    Nat.succ_le_iff.mp (by simpa [P] using one_le_polyBase (M := M) (c := c) (n := n))
  have hBasePos : 0 < affineFactorPolyCoeff M * P ^ 2 :=
    Nat.mul_pos hCoeffPos (Nat.pow_pos hPpos _)
  have hExp :=
    Nat.pow_le_pow_right hBasePos hRunBound
  exact Nat.le_trans hPow hExp

lemma affineIter_runTime_le_pre
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    affineIter (M := M) (n := n) (M.runTime n) ≤
      affineIterLeadCoeff M *
          (polyBase (M := M) (c := c) n) ^ 4 *
        (affineFactorPolyCoeff M *
            (polyBase (M := M) (c := c) n) ^ 2) ^
          (polyBase (M := M) (c := c) n) := by
  classical
  set P := polyBase (M := M) (c := c) n
  have hTotal :=
    affineIter_le_pow (M := M) (n := n)
      (t := M.runTime n)
  have hFactor :=
    affineIter_linear_factor_le_poly (M := M) (n := n) (c := c) hRun
  have hPower :=
    affineFactor_pow_le_poly (M := M) (n := n) (c := c) hRun
  have hStep₁ :
      (totalBound (initialBounds (M := M) (n := n)) +
          (M.runTime n + 1) * affineOffset (M := M) (n := n)) *
        (affineFactor (M := M) (n := n)) ^ (M.runTime n) ≤
      (affineIterLeadCoeff M * P ^ 4) *
        (affineFactor (M := M) (n := n)) ^ (M.runTime n) := by
    exact Nat.mul_le_mul_right _ hFactor
  have hStep₂ :
      (affineIterLeadCoeff M * P ^ 4) *
          (affineFactor (M := M) (n := n)) ^ (M.runTime n) ≤
        (affineIterLeadCoeff M * P ^ 4) *
          (affineFactorPolyCoeff M * P ^ 2) ^ P := by
    exact Nat.mul_le_mul_left _ hPower
  have hComb := Nat.le_trans hStep₁ hStep₂
  have :=
    Nat.le_trans hTotal hComb
  simpa [P]
    using this

lemma sizeOf_acceptCircuit_le_pre
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    sizeOf (acceptCircuit (M := M) (n := n)) ≤
      affineIterLeadCoeff M *
          (polyBase (M := M) (c := c) n) ^ 4 *
        (affineFactorPolyCoeff M *
            (polyBase (M := M) (c := c) n) ^ 2) ^
          (polyBase (M := M) (c := c) n) :=
  Nat.le_trans (sizeOf_acceptCircuit_le_affine (M := M) (n := n))
    (affineIter_runTime_le_pre (M := M) (n := n) (c := c) hRun)

/--
Helper statement: a natural number is always bounded by an exponential with
base `2`.  We phrase the inequality using `k + 1` on the right-hand side to
avoid tedious special cases for zero.-/
lemma le_two_pow_succ (k : ℕ) : k ≤ 2 ^ (k + 1) := by
  have hSucc : k + 1 ≤ 2 ^ (k + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
        -- The induction hypothesis yields `k + 1 ≤ 2^(k + 1)`.
        -- Adding the same quantity to both sides preserves the inequality,
        -- giving `(k + 1) + 1 ≤ 2^(k + 1) + 2^(k + 1) = 2^(k + 2)`.
        have hstep := Nat.add_le_add ih ih
        simpa [two_mul, Nat.pow_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hstep
  exact Nat.le_trans (Nat.le_succ _) hSucc

/--
Monotonicity of exponentiation with respect to the base.
-/
lemma pow_le_pow_of_le_base {a b k : ℕ} (h : a ≤ b) : a ^ k ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      -- Multiply both sides of the inductive inequality by the base bound.
      have := Nat.mul_le_mul ih h
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this

/--
Auxiliary inequality packaging the previous two lemmas for the concrete base
`max P 2`.  This base is convenient later on because it uniformly dominates
both `polyBase` and the constant `2`.
-/
lemma const_le_pow_max (P c : ℕ) :
    c ≤ (max P 2) ^ (c + 1) := by
  have hTwo : c ≤ 2 ^ (c + 1) := le_two_pow_succ c
  have hBase : 2 ≤ max P 2 := Nat.le_max_right _ _
  have hmono := pow_le_pow_of_le_base (a := 2) (b := max P 2)
    (k := c + 1) hBase
  exact Nat.le_trans hTwo hmono

/--
The base used in the final polynomial bound; taking the maximum with `2`
avoids vacuous corner cases where `polyBase` becomes `1` on very small
inputs.-/
def gateBoundBase (M : TM) (c n : ℕ) : ℕ :=
  max (polyBase (M := M) (c := c) n) 2

/-- Exponent coefficient controlling the main growth of the accepting circuit. -/
def gateBoundExponent (M : TM) : ℕ := affineFactorPolyCoeff M + 3

/-- Constant offset appearing in the exponent of the final bound. -/
def gateBoundOffset (M : TM) : ℕ := affineIterLeadCoeff M + 5

lemma sizeOf_acceptCircuit_le_poly
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    sizeOf (acceptCircuit (M := M) (n := n)) ≤
      (gateBoundBase (M := M) (c := c) (n := n)) ^
        (gateBoundExponent M *
            polyBase (M := M) (c := c) n + gateBoundOffset M) := by
  classical
  set P := polyBase (M := M) (c := c) n
  set B := gateBoundBase (M := M) (c := c) (n := n)
  have hBase_ge : P ≤ B := by
    unfold B gateBoundBase
    exact Nat.le_max_left _ _
  have hLead : affineIterLeadCoeff M ≤ B ^ (affineIterLeadCoeff M + 1) := by
    unfold B gateBoundBase
    exact const_le_pow_max P (affineIterLeadCoeff M)
  have hPow4 : P ^ 4 ≤ B ^ 4 :=
    pow_le_pow_of_le_base (a := P) (b := B) (k := 4) hBase_ge
  have hCoeff : affineFactorPolyCoeff M ≤ B ^ (affineFactorPolyCoeff M + 1) := by
    unfold B gateBoundBase
    exact const_le_pow_max P (affineFactorPolyCoeff M)
  have hP_sq : P ^ 2 ≤ B ^ 2 :=
    pow_le_pow_of_le_base (a := P) (b := B) (k := 2) hBase_ge
  have hCoeffMul : affineFactorPolyCoeff M * P ^ 2 ≤
      B ^ (affineFactorPolyCoeff M + 3) := by
    have hmul := Nat.mul_le_mul hCoeff hP_sq
    -- Simplify the product using the standard power rules.
    simpa [B, gateBoundBase, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc, Nat.pow_succ, Nat.pow_two]
      using hmul
  have hPowCoeff :
      (affineFactorPolyCoeff M * P ^ 2) ^ P ≤
        B ^ ((affineFactorPolyCoeff M + 3) * P) := by
    have := pow_le_pow_of_le_base (a := affineFactorPolyCoeff M * P ^ 2)
      (b := B ^ (affineFactorPolyCoeff M + 3)) (k := P) hCoeffMul
    simpa [Nat.pow_mul] using this
  have hpre := sizeOf_acceptCircuit_le_pre
    (M := M) (n := n) (c := c) hRun
  -- Combine all auxiliary estimates: replace each factor of the preliminary
  -- bound with its counterpart expressed solely in terms of `B`.
  have hstep₁ :
      sizeOf (acceptCircuit (M := M) (n := n)) ≤
        B ^ (affineIterLeadCoeff M + 1) * (P ^ 4) *
          (affineFactorPolyCoeff M * P ^ 2) ^ P := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hLead (Nat.le_refl _))
      (Nat.le_refl _)
    exact Nat.le_trans hpre this
  have hstep₂ :
      sizeOf (acceptCircuit (M := M) (n := n)) ≤
        B ^ (affineIterLeadCoeff M + 1) * B ^ 4 *
          (affineFactorPolyCoeff M * P ^ 2) ^ P := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _ ) hPow4)
      (Nat.le_refl _)
    exact Nat.le_trans hstep₁ this
  have hstep₃ :
      sizeOf (acceptCircuit (M := M) (n := n)) ≤
        B ^ (affineIterLeadCoeff M + 1) * B ^ 4 *
          B ^ ((affineFactorPolyCoeff M + 3) * P) := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) (Nat.le_refl _))
      hPowCoeff
    exact Nat.le_trans hstep₂ this
  -- Finish by collecting the exponents.
  simpa [B, gateBoundBase, gateBoundExponent, gateBoundOffset, P,
    Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.pow_add,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hstep₃

/--
Convenient packaging of the final bound on the accepting circuit.  The
definition mirrors the right-hand side of
`sizeOf_acceptCircuit_le_poly` and will be reused when constructing the
`InPpoly` witness associated with a polynomial-time Turing machine.
-/
def gatePolyBound (M : TM) (c n : ℕ) : ℕ :=
  (gateBoundBase (M := M) (c := c) n) ^
    (gateBoundExponent M *
        polyBase (M := M) (c := c) n + gateBoundOffset M)

@[simp] lemma gatePolyBound_def (M : TM) (c n : ℕ) :
    gatePolyBound (M := M) (c := c) n =
      (gateBoundBase (M := M) (c := c) n) ^
        (gateBoundExponent M *
            polyBase (M := M) (c := c) n + gateBoundOffset M) := rfl

/--
Restatement of `sizeOf_acceptCircuit_le_poly` using the packaged definition
`gatePolyBound`.  The lemma emphasises that the complicated expression bounding
the accepting circuit will be treated as an opaque polynomial candidate in the
final construction.
-/
lemma sizeOf_acceptCircuit_le_gatePolyBound
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) :
    sizeOf (acceptCircuit (M := M) (n := n)) ≤
      gatePolyBound (M := M) (c := c) n :=
  sizeOf_acceptCircuit_le_poly (M := M) (n := n) (c := c) hRun

/--
The gate-count bound `gatePolyBound` is controlled by an explicit function of
`n`.  While the resulting estimate is not yet in the canonical `n^k + k`
format required by `InPpoly`, it already replaces all occurrences of the
auxiliary quantities (`polyBase`, `gateBoundBase`) with straightforward
polynomials in `n`.  Subsequent lemmas will normalise this expression further.
-/
lemma gatePolyBound_le_explicit (M : TM) (c n : ℕ) :
    gatePolyBound (M := M) (c := c) n ≤
      ((n + 1) ^ runtimeExponent c * (n + runtimeExponent c + 1) + 2) ^
        (gateBoundExponent M *
            ((n + 1) ^ runtimeExponent c * (n + runtimeExponent c + 1)) +
          gateBoundOffset M) := by
  classical
  set B := gateBoundBase (M := M) (c := c) n
  set P :=
    (n + 1) ^ runtimeExponent c * (n + runtimeExponent c + 1) + 2
  set Q :=
    (n + 1) ^ runtimeExponent c * (n + runtimeExponent c + 1)
  have hBase : B ≤ P :=
    gateBoundBase_le_poly (M := M) (c := c) (n := n)
  -- First enlarge the base of the power using monotonicity.
  have hBasePow :
      B ^ (gateBoundExponent M * polyBase (M := M) (c := c) n +
          gateBoundOffset M) ≤
        P ^ (gateBoundExponent M * polyBase (M := M) (c := c) n +
          gateBoundOffset M) :=
    Nat.pow_le_pow_of_le_base (a := B) (b := P)
      (k := gateBoundExponent M * polyBase (M := M) (c := c) n +
          gateBoundOffset M) hBase
  have hPoly :
      polyBase (M := M) (c := c) n ≤ Q := by
    simpa [Q]
      using polyBase_le_mul_pow (M := M) (c := c) (n := n)
  -- Upgrade the exponent to the simplified expression.
  have hExp :
      gateBoundExponent M * polyBase (M := M) (c := c) n +
          gateBoundOffset M ≤
        gateBoundExponent M * Q + gateBoundOffset M := by
    have hMul :=
      Nat.mul_le_mul_left (gateBoundExponent M) hPoly
    exact Nat.add_le_add hMul (Nat.le_refl _)
  have hPos : 1 ≤ P := by
    have : 2 ≤ P := by
      have : (2 : ℕ) ≤ 2 + Q := by
        exact Nat.le_add_left _ _
      simpa [P, Q, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    exact Nat.succ_le_succ (Nat.le_trans (Nat.zero_le _) this)
  have hExpPow :
      P ^ (gateBoundExponent M * polyBase (M := M) (c := c) n +
          gateBoundOffset M) ≤
        P ^ (gateBoundExponent M * Q + gateBoundOffset M) :=
    Nat.pow_le_pow_of_le_right hPos hExp
  have :=
    Nat.le_trans hBasePow hExpPow
  simpa [gatePolyBound_def, B, P, Q]
    using this

/--
Auxiliary polynomial dominating both `polyBase` and the constant `2` required
by `gateBoundBase`.  The expression grows like `(n + runtimeExponent c + 2)` to
the power `runtimeExponent c + 1`, which will later be convenient when
normalising the final size bounds.-/
def dominantBase (c n : ℕ) : ℕ :=
  2 * (n + runtimeExponent c + 2) ^ (runtimeExponent c + 1)

/--
The auxiliary base is always at least one.  We record the slightly stronger
fact that it actually dominates the constant `2`, which will be handy when
applying monotonicity properties of exponentiation.
-/
lemma one_le_dominantBase (c n : ℕ) : 1 ≤ dominantBase c n := by
  classical
  unfold dominantBase
  have hpowpos :
      0 < (n + runtimeExponent c + 2) ^ (runtimeExponent c + 1) := by
    have hbase : 0 < n + runtimeExponent c + 2 := Nat.succ_pos _
    exact Nat.pow_pos hbase _
  have hpow :
      1 ≤ (n + runtimeExponent c + 2) ^ (runtimeExponent c + 1) :=
    Nat.succ_le_of_lt hpowpos
  have hMul :
      2 ≤
        2 * (n + runtimeExponent c + 2) ^ (runtimeExponent c + 1) := by
    have :=
      Nat.mul_le_mul_left (2)
        hpow
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  exact Nat.le_trans (by decide : 1 ≤ 2) hMul

/--
`polyBase` is bounded by the auxiliary polynomial `dominantBase`.
-/
lemma polyBase_le_dominantBase (c n : ℕ) :
    polyBase (c := c) n ≤ dominantBase c n := by
  classical
  set R := runtimeExponent c
  set B := n + R + 2
  have hPow : n ^ R ≤ B ^ (R + 1) := by
    have hLe : n ≤ B := by
      have := Nat.le_add_right n (R + 2)
      simpa [B, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have hMono := pow_le_pow_of_le_base (a := n) (b := B) (k := R) hLe
    have hPos : 1 ≤ B := by
      have : (0 : ℕ) ≤ n := Nat.zero_le _
      exact Nat.succ_le_succ (Nat.add_le_add this (Nat.zero_le _))
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using Nat.mul_le_mul_right _ hMono
  have hConst : R ≤ B ^ (R + 1) := by
    have hLe : R ≤ B := by
      have := Nat.le_add_right R (n + 2)
      simpa [B, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have : B ≤ B ^ (R + 1) := by
      have := Nat.mul_le_mul_left B
        (pow_le_pow_of_le_base (a := B) (b := B) (k := R)
          (Nat.le_refl _))
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this
    exact Nat.le_trans hLe this
  have hBound : n ^ R + R ≤ 2 * B ^ (R + 1) := by
    have h₁ : n ^ R ≤ B ^ (R + 1) := hPow
    have h₂ : R ≤ B ^ (R + 1) := hConst
    have := Nat.add_le_add h₁ h₂
    simpa [two_mul, dominantBase, B, R] using this
  simpa [polyBase, dominantBase, B, R, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hBound

/--
`gateBoundBase` is dominated by the auxiliary polynomial `dominantBase`.
-/
lemma gateBoundBase_le_dominantBase (M : TM) (c n : ℕ) :
    gateBoundBase (M := M) (c := c) n ≤ dominantBase c n := by
  classical
  have hpoly : polyBase (c := c) n ≤ dominantBase c n :=
    polyBase_le_dominantBase (c := c) (n := n)
  have htwo : 2 ≤ dominantBase c n := by
    have hpos : 0 < (n + runtimeExponent c + 2) ^ (runtimeExponent c + 1) := by
      have : 0 < n + runtimeExponent c + 2 := Nat.succ_pos _
      exact Nat.pow_pos this _
    have : 2 ≤ 2 * (n + runtimeExponent c + 2) ^ (runtimeExponent c + 1) := by
      have := Nat.mul_le_mul_left (2)
        (Nat.succ_le_of_lt hpos)
      simpa [two_mul] using this
    simpa [dominantBase, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  exact (max_le_iff.mpr ⟨hpoly, htwo⟩)

/--
The packaged gate bound `gatePolyBound` can be controlled entirely through the
auxiliary base `dominantBase`.  This lemma upgrades both the base and the
exponent appearing in `gatePolyBound` to the dominating polynomial expression,
streamlining later normalisation steps.
-/
lemma gatePolyBound_le_dominantBase_pow (M : TM) (c n : ℕ) :
    gatePolyBound (M := M) (c := c) n ≤
      (dominantBase c n) ^
        (gateBoundExponent M * dominantBase c n + gateBoundOffset M) := by
  classical
  set B := gateBoundBase (M := M) (c := c) n
  set D := dominantBase c n
  have hBase : B ≤ D :=
    gateBoundBase_le_dominantBase (M := M) (c := c) (n := n)
  have hPowBase :
      B ^
          (gateBoundExponent M *
              polyBase (M := M) (c := c) n + gateBoundOffset M) ≤
        D ^
          (gateBoundExponent M *
              polyBase (M := M) (c := c) n + gateBoundOffset M) :=
    pow_le_pow_of_le_base (a := B) (b := D)
      (k := gateBoundExponent M *
              polyBase (M := M) (c := c) n + gateBoundOffset M) hBase
  have hPoly : polyBase (c := c) n ≤ D :=
    polyBase_le_dominantBase (c := c) (n := n)
  have hExp :
      gateBoundExponent M * polyBase (M := M) (c := c) n + gateBoundOffset M ≤
        gateBoundExponent M * D + gateBoundOffset M := by
    have hMul := Nat.mul_le_mul_left (gateBoundExponent M) hPoly
    exact Nat.add_le_add hMul (Nat.le_refl _)
  have hPos : 1 ≤ D := one_le_dominantBase (c := c) (n := n)
  have hPowExp :
      D ^
          (gateBoundExponent M * polyBase (M := M) (c := c) n +
            gateBoundOffset M) ≤
        D ^
          (gateBoundExponent M * D + gateBoundOffset M) :=
    Nat.pow_le_pow_of_le_right hPos hExp
  have := Nat.le_trans hPowBase hPowExp
  simpa [gatePolyBound_def, B, D]
    using this

/--
Helper lemma translating the specification of the accepting circuit into the
language-level predicate used by `InPpoly`.
-/
lemma acceptCircuit_correct_language (M : TM) (n : ℕ)
    (x : Boolcube.Bitstring n) :
    Circuit.eval (acceptCircuit (M := M) (n := n)) x =
      (Complexity.TM.accepts (M := M) (n := n) x) :=
  acceptCircuit_spec (M := M) (n := n) x

/--
Given a polynomial bound for `gatePolyBound`, we can extract an `InPpoly`
witness for the language decided by a polynomial-time Turing machine.  The
explicit polynomial domination is postponed to dedicated lemmas below, so that
the combinatorial part of the construction is isolated from the heavy
arithmetic manipulations.
-/
noncomputable def inPpoly_of_polyBound
    {L : Complexity.Language} {M : TM} {c : ℕ}
    (hRun : ∀ n, M.runTime n ≤ n ^ c + c)
    (hCorrect : ∀ n (x : Boolcube.Bitstring n),
      Complexity.TM.accepts (M := M) (n := n) x = L n x)
    (hPoly : ∃ k, ∀ n, gatePolyBound (M := M) (c := c) n ≤ n ^ k + k) :
    Complexity.InPpoly L := by
  classical
  refine
    { polyBound := fun n => gatePolyBound (M := M) (c := c) n
      , polyBound_poly := hPoly
      , circuits := fun n => acceptCircuit (M := M) (n := n)
      , size_ok := ?_, correct := ?_ }
  · intro n
    simpa [gatePolyBound_def]
      using sizeOf_acceptCircuit_le_gatePolyBound (M := M) (n := n) (c := c)
        hRun
  · intro n x
    simpa [hCorrect n x]
      using acceptCircuit_correct_language (M := M) (n := n) x



end Complexity

