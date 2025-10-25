import Proof.Complexity.Interfaces
import Proof.Circuit.Family
import Proof.Circuit.StraightLine
import Proof.Turing.Encoding

/-!
# Configuration encodings for the `P ⊆ P/poly` simulation

This module collects the basic combinatorial lemmas, indicator functions, and
circuit encodings that describe single Turing-machine configurations.  It
provides both tree-style circuit families (`ConfigCircuits`) and their
straight-line counterparts (`StraightConfig`), together with the translation
lemmas needed by the main simulation.

As part of the integration clean-up we deliberately work inside
`Facts.PsubsetPpoly`.  This ensures that the numerous helper structures from the
standalone fact never collide with the homonymous ones in `Pnp2`.
-/

namespace Facts
namespace PsubsetPpoly

open Boolcube
open TM

open scoped BigOperators

namespace List

lemma foldl_or_eq_any {α} (l : List α) (f : α → Bool) :
    l.foldl (fun acc x => acc || f x) false = List.any l f := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [List.any, ih, Bool.or_left_comm, Bool.or_assoc]

lemma foldl_filter_or_eq_any {α} (l : List α) (p f : α → Bool) :
    l.foldl (fun acc x => if p x then acc || f x else acc) false =
      List.any l (fun x => p x && f x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases hp : p a
      · simp [List.any, hp, Bool.or_left_comm, Bool.or_assoc, ih]
      · simp [List.any, hp, Bool.and_eq_false_left, ih]

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
Reinterpret a straight-line configuration as an ordinary family of Boolean
circuits by unfolding every stored wire through
`StraightLineCircuit.toCircuitWire`.  This translation provides the missing
bridge between the sharing-aware straight-line world and the tree-based
interface used in the remainder of the development.-/
def toConfigCircuits (sc : StraightConfig M n) : ConfigCircuits M n where
  tape := fun i => StraightLineCircuit.toCircuitWire (C := sc.circuit) (sc.tape i)
  head := fun i => StraightLineCircuit.toCircuitWire (C := sc.circuit) (sc.head i)
  state := fun i => StraightLineCircuit.toCircuitWire (C := sc.circuit) (sc.state i)

/--
Semantic compatibility between the straight-line and tree-based encodings of a
configuration.  The statement follows immediately from the translation lemma
`StraightLineCircuit.eval_toCircuitWire`.
-/
lemma Spec.toConfigCircuits {sc : StraightConfig M n}
    {f : Point n → TM.Configuration M n}
    (h : Spec (M := M) (n := n) sc f) :
    ConfigCircuits.Spec (M := M) (n := n)
      (StraightConfig.toConfigCircuits (M := M) (n := n) sc) f := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    have := h.tape_eq (x := x) (i := i)
    simpa [toConfigCircuits, evalTape,
      StraightLineCircuit.eval_toCircuitWire]
      using this
  · intro x i
    have := h.head_eq (x := x) (i := i)
    simpa [toConfigCircuits, evalHead,
      StraightLineCircuit.eval_toCircuitWire]
      using this
  · intro x i
    have := h.state_eq (x := x) (i := i)
    simpa [toConfigCircuits, evalState,
      StraightLineCircuit.eval_toCircuitWire]
      using this

/-- Recover a straight-line specification from the corresponding tree-style
translation.  The statement is the converse of `Spec.toConfigCircuits` and
follows immediately from `StraightLineCircuit.eval_toCircuitWire`. -/
lemma Spec.ofConfigCircuits {sc : StraightConfig M n}
    {f : Point n → TM.Configuration M n}
    (h : ConfigCircuits.Spec (M := M) (n := n)
      (StraightConfig.toConfigCircuits (M := M) (n := n) sc) f) :
    Spec (M := M) (n := n) sc f := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    have := h.tape_eq (x := x) (i := i)
    simpa [toConfigCircuits, evalTape,
      StraightLineCircuit.eval_toCircuitWire]
      using this
  · intro x i
    have := h.head_eq (x := x) (i := i)
    simpa [toConfigCircuits, evalHead,
      StraightLineCircuit.eval_toCircuitWire]
      using this
  · intro x i
    have := h.state_eq (x := x) (i := i)
    simpa [toConfigCircuits, evalState,
      StraightLineCircuit.eval_toCircuitWire]
      using this

/--
Auxiliary gate-count estimates for the translation to tree circuits.  We prove
simultaneously that every translated wire uses at most `4 ^ (g + 3)` gates while
the concrete gates reconstructed during the recursion stay below
`4 ^ (g + 4)`.  The slightly offset exponents provide the slack needed to absorb
the additional gate contributed by the Boolean operator at the current layer.
-/
mutual
  lemma toCircuitWireAux_gateCount_le_pow (C : StraightLineCircuit n) :
      ∀ {g : ℕ} {hg : g ≤ C.gates} {i : Fin (n + g)},
        Circuit.gateCount
            (StraightLineCircuit.toCircuitWireAux (C := C) (g := g) (hg := hg) i)
          ≤ 4 ^ (g + 3)
    | g, hg, i => by
        classical
        by_cases h : (i : ℕ) < n
        · have : Circuit.gateCount (Circuit.var ⟨i, h⟩ : Circuit n) = 1 := by simp
          have hpow : (1 : ℕ) ≤ 4 ^ (g + 3) := by
            have : 0 < 4 := by decide
            exact Nat.succ_le_of_lt (Nat.pow_pos this (g + 3))
          simpa [StraightLineCircuit.toCircuitWireAux, h, Circuit.gateCount]
            using hpow
        · set j : ℕ := (i : ℕ) - n with hj
          have hInputs : n ≤ (i : ℕ) := Nat.le_of_not_lt h
          have hj_lt : j < g := by
            have := i.is_lt
            have := Nat.sub_lt_of_le_of_lt hInputs (by simpa [hj] using this)
            simpa [hj] using this
          have hj_total : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          have hGate := toCircuitGateAux_gateCount_le_pow (C := C)
            (g := j) (hg := hj_total)
          have hj_le : j + 4 ≤ g + 3 := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using Nat.succ_le_succ
                (Nat.succ_le_succ
                  (Nat.succ_le_succ (Nat.succ_le_of_lt hj_lt)))
          have hPow :=
            Nat.pow_le_pow_of_le_right (by decide : 0 < 4) hj_le
          exact Nat.le_trans hGate hPow

  lemma toCircuitGateAux_gateCount_le_pow (C : StraightLineCircuit n) :
      ∀ {g : ℕ} {hg : g < C.gates},
        Circuit.gateCount
            (StraightLineCircuit.toCircuitGateAux (C := C) (g := g) hg)
          ≤ 4 ^ (g + 4)
    | g, hg => by
        classical
        cases hOp : C.gate ⟨g, hg⟩ with
        | const b =>
            have : Circuit.gateCount (Circuit.const b : Circuit n) = 1 := by simp
            have hpow : (1 : ℕ) ≤ 4 ^ (g + 4) := by
              have : 0 < 4 := by decide
              exact Nat.succ_le_of_lt (Nat.pow_pos this (g + 4))
            simpa [StraightLineCircuit.toCircuitGateAux, hOp, Circuit.gateCount]
              using hpow
        | not i =>
            set child :=
              Circuit.gateCount
                (StraightLineCircuit.toCircuitWireAux (C := C) (g := g)
                  (hg := Nat.le_of_lt hg) i)
              with hchild_def
            have hchild_le : child ≤ 4 ^ (g + 3) := by
              simpa [child, hchild_def] using
                toCircuitWireAux_gateCount_le_pow (C := C)
                  (g := g) (hg := Nat.le_of_lt hg) (i := i)
            have hsum : child + 1 ≤ 4 ^ (g + 3) + 1 :=
              Nat.add_le_add_right hchild_le 1
            have hpos : 1 ≤ 4 ^ (g + 3) :=
              Nat.succ_le_of_lt (Nat.pow_pos (by decide) (g + 3))
            have hle : 4 ^ (g + 3) + 1 ≤ 2 * 4 ^ (g + 3) := by
              simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                using Nat.add_le_add_left hpos (4 ^ (g + 3))
            have hmul : 2 * 4 ^ (g + 3) ≤ 4 ^ (g + 4) := by
              have : 2 ≤ 4 := by decide
              simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
                Nat.mul_assoc] using Nat.mul_le_mul_right (4 ^ (g + 3)) this
            have : child + 1 ≤ 4 ^ (g + 4) :=
              Nat.le_trans (Nat.le_trans hsum hle) hmul
            simpa [child, hchild_def, StraightLineCircuit.toCircuitGateAux,
              hOp, Circuit.gateCount, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using this
        | and i j =>
            set ci :=
              Circuit.gateCount
                (StraightLineCircuit.toCircuitWireAux (C := C) (g := g)
                  (hg := Nat.le_of_lt hg) i)
              with hci_def
            set cj :=
              Circuit.gateCount
                (StraightLineCircuit.toCircuitWireAux (C := C) (g := g)
                  (hg := Nat.le_of_lt hg) j)
              with hcj_def
            have hi_le : ci ≤ 4 ^ (g + 3) := by
              simpa [ci, hci_def] using
                toCircuitWireAux_gateCount_le_pow (C := C)
                  (g := g) (hg := Nat.le_of_lt hg) (i := i)
            have hj_le : cj ≤ 4 ^ (g + 3) := by
              simpa [cj, hcj_def] using
                toCircuitWireAux_gateCount_le_pow (C := C)
                  (g := g) (hg := Nat.le_of_lt hg) (i := j)
            have hsum : ci + cj ≤ 2 * 4 ^ (g + 3) := by
              have := Nat.add_le_add hi_le hj_le
              simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                using this
            have hsum' : ci + cj + 1 ≤ 2 * 4 ^ (g + 3) + 1 :=
              Nat.add_le_add_right hsum 1
            have hpos : 1 ≤ 4 ^ (g + 3) :=
              Nat.succ_le_of_lt (Nat.pow_pos (by decide) (g + 3))
            have hTwo : 2 * 4 ^ (g + 3) + 1 ≤ 3 * 4 ^ (g + 3) := by
              simpa [two_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc]
                using Nat.add_le_add_left hpos (2 * 4 ^ (g + 3))
            have hThree : 3 * 4 ^ (g + 3) ≤ 4 ^ (g + 4) := by
              have : 3 ≤ 4 := by decide
              simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
                using Nat.mul_le_mul_right (4 ^ (g + 3)) this
            have : ci + cj + 1 ≤ 4 ^ (g + 4) :=
              Nat.le_trans (Nat.le_trans hsum' hTwo) hThree
            simpa [ci, hci_def, cj, hcj_def, StraightLineCircuit.toCircuitGateAux,
              hOp, Circuit.gateCount, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using this
        | or i j =>
            set ci :=
              Circuit.gateCount
                (StraightLineCircuit.toCircuitWireAux (C := C) (g := g)
                  (hg := Nat.le_of_lt hg) i)
              with hci_def
            set cj :=
              Circuit.gateCount
                (StraightLineCircuit.toCircuitWireAux (C := C) (g := g)
                  (hg := Nat.le_of_lt hg) j)
              with hcj_def
            have hi_le : ci ≤ 4 ^ (g + 3) := by
              simpa [ci, hci_def] using
                toCircuitWireAux_gateCount_le_pow (C := C)
                  (g := g) (hg := Nat.le_of_lt hg) (i := i)
            have hj_le : cj ≤ 4 ^ (g + 3) := by
              simpa [cj, hcj_def] using
                toCircuitWireAux_gateCount_le_pow (C := C)
                  (g := g) (hg := Nat.le_of_lt hg) (i := j)
            have hsum : ci + cj ≤ 2 * 4 ^ (g + 3) := by
              have := Nat.add_le_add hi_le hj_le
              simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                using this
            have hsum' : ci + cj + 1 ≤ 2 * 4 ^ (g + 3) + 1 :=
              Nat.add_le_add_right hsum 1
            have hpos : 1 ≤ 4 ^ (g + 3) :=
              Nat.succ_le_of_lt (Nat.pow_pos (by decide) (g + 3))
            have hTwo : 2 * 4 ^ (g + 3) + 1 ≤ 3 * 4 ^ (g + 3) := by
              simpa [two_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc]
                using Nat.add_le_add_left hpos (2 * 4 ^ (g + 3))
            have hThree : 3 * 4 ^ (g + 3) ≤ 4 ^ (g + 4) := by
              have : 3 ≤ 4 := by decide
              simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
                using Nat.mul_le_mul_right (4 ^ (g + 3)) this
            have : ci + cj + 1 ≤ 4 ^ (g + 4) :=
              Nat.le_trans (Nat.le_trans hsum' hTwo) hThree
            simpa [ci, hci_def, cj, hcj_def, StraightLineCircuit.toCircuitGateAux,
              hOp, Circuit.gateCount, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using this
end

lemma toCircuitWire_gateCount_le (C : StraightLineCircuit n)
    (i : Fin (n + C.gates)) :
    Circuit.gateCount (StraightLineCircuit.toCircuitWire (C := C) i) ≤
      4 ^ (C.gates + 3) :=
  toCircuitWireAux_gateCount_le_pow (C := C) (hg := le_rfl) (i := i)

/--
Translate a straight-line configuration into tree circuits without blowing up the
gate count more than exponentially in the number of straight-line gates.  Each
wire becomes a tree circuit of size at most `4 ^ (straightTotalGateCount sc + 3)`.
Consequently the total gate count of the induced `ConfigCircuits` is controlled
by the number of tracked tape cells and states.-/
lemma totalGateCount_toConfigCircuits_le (sc : StraightConfig M n) :
    totalGateCount (M := M) (n := n)
        (StraightConfig.toConfigCircuits (M := M) (n := n) sc) ≤
      ((2 * M.tapeLength n) + stateCard M) *
        4 ^ (straightTotalGateCount (M := M) (n := n) sc + 3) := by
  classical
  -- The exponential factor bounding every translated wire.
  set B := 4 ^ (straightTotalGateCount (M := M) (n := n) sc + 3)
  -- Tape portion: each cell circuit is bounded by `B`.
  have htape_sum :
      tapeGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        ≤ ∑ _ : Fin (M.tapeLength n), B := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa [B, straightTotalGateCount, StraightConfig.toConfigCircuits]
      using StraightLineCircuit.toCircuitWire_gateCount_le
        (C := sc.circuit) (i := sc.tape i)
  have htape_const :
      (∑ _ : Fin (M.tapeLength n), B) = M.tapeLength n * B := by
    simp [B, Finset.card_univ, Nat.smul_def]
  have htape :
      tapeGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        ≤ M.tapeLength n * B := by
    simpa [htape_const] using htape_sum
  -- Head portion obeys the same bound, sharing the tape index set.
  have hhead_sum :
      headGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        ≤ ∑ _ : Fin (M.tapeLength n), B := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa [B, straightTotalGateCount, StraightConfig.toConfigCircuits]
      using StraightLineCircuit.toCircuitWire_gateCount_le
        (C := sc.circuit) (i := sc.head i)
  have hhead :
      headGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        ≤ M.tapeLength n * B := by
    simpa [htape_const] using hhead_sum
  -- State portion: the index set has size `stateCard M`.
  have hstate_sum :
      stateGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        ≤ ∑ _ : Fin (stateCard M), B := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa [B, straightTotalGateCount, StraightConfig.toConfigCircuits]
      using StraightLineCircuit.toCircuitWire_gateCount_le
        (C := sc.circuit) (i := sc.state i)
  have hstate_const :
      (∑ _ : Fin (stateCard M), B) = stateCard M * B := by
    simp [B, Finset.card_univ, Nat.smul_def]
  have hstate :
      stateGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        ≤ stateCard M * B := by
    simpa [hstate_const] using hstate_sum
  -- Combine the three bounds.
  have htotal :=
    Nat.add_le_add (Nat.add_le_add htape hhead) hstate
  have hLHS :
      tapeGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        +
        headGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        +
        stateGateCount (M := M) (n := n)
          (StraightConfig.toConfigCircuits (M := M) (n := n) sc)
        = totalGateCount (M := M) (n := n)
            (StraightConfig.toConfigCircuits (M := M) (n := n) sc) := rfl
  have hRHS :
      M.tapeLength n * B + M.tapeLength n * B + stateCard M * B =
        ((2 * M.tapeLength n) + stateCard M) * B := by
    have htape_eq : M.tapeLength n * B + M.tapeLength n * B =
        (2 * M.tapeLength n) * B := by
      simp [two_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    calc
      M.tapeLength n * B + M.tapeLength n * B + stateCard M * B
          = (2 * M.tapeLength n) * B + stateCard M * B := by
            simpa [htape_eq]
      _ = ((2 * M.tapeLength n) + stateCard M) * B := by
            simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
              Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  simpa [hLHS, hRHS, B, straightTotalGateCount] using htotal

/--
Total number of gates appearing in a straight-line configuration.  Since all
components share the same underlying circuit, this is simply the gate count of
`sc.circuit`.  The wrapper keeps the intended quantity explicit in subsequent
lemmas and mirrors the notation used for tree-style configurations.-/
def straightTotalGateCount (sc : StraightConfig M n) : ℕ :=
  sc.circuit.gates

/--
Gate count of the straight-line initial configuration.  The construction starts
from a one-gate circuit producing the constant `false` and appends a second gate
realising `true`, hence the overall size equals two.
-/
@[simp] lemma straightTotalGateCount_initial (M : TM) (n : ℕ) :
    straightTotalGateCount (StraightConfig.initial (M := M) n) = 2 := by
  -- By definition the initial circuit arises from a single `snoc` above the
  -- one-gate `constCircuit false`.
  simp [StraightConfig.initial, straightTotalGateCount, StraightLineCircuit.size,
    StraightLineCircuit.snoc, constCircuit]

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
Appending a branch via `branchBuilderFrom` does not alter the value of an
existing wire.  The statement is phrased for an arbitrary predicate `g` so that
it can be instantiated with the semantic description of the symbol wire in the
snapshot lemmas below.-/
lemma branchBuilderFrom_preserves_eval (sc : StraightConfig M n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (symbol : StraightLineCircuit.Wire n)
    (symbolWire : Fin (n + b.circuit.gates))
    (hSymbol : symbol.bound ≤ b.circuit.gates)
    (g : Point n → Bool)
    (hsymbolEval : ∀ x,
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
          (symbol.toFin (n := n) (g := b.circuit.gates) hSymbol) = g x)
    (qs : M.state × Bool) :
    ∀ x,
      let result := branchBuilderFrom (M := M) (n := n) (sc := sc)
          (b := b) (symbolWire := symbolWire) qs
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
          (symbol.toFin (n := n) (g := result.fst.circuit.gates)
            (Nat.le_trans hSymbol
              (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
                (b := b) (symbolWire := symbolWire) (qs := qs))))
        = g x := by
  classical
  intro x
  cases hqs : qs.2 with
  | false =>
      -- The `false` branch appends a negation followed by a conjunction.
      set negResult := StraightLineCircuit.EvalBuilder.appendNotFin
        (b := b) symbolWire with hneg
      have hSymbolNeg : symbol.bound ≤ negResult.fst.circuit.gates := by
        have hmono : b.circuit.gates ≤ negResult.fst.circuit.gates := by
          have := Nat.le_succ b.circuit.gates
          simpa [hneg, StraightLineCircuit.EvalBuilder.appendNotFin,
            Nat.succ_eq_add_one] using this
        exact Nat.le_trans hSymbol hmono
      have hEvalNeg :=
        StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
          (b := b) (op := StraightOp.not symbolWire)
          (w := symbol) (hw := hSymbol) (x := x)
      have hEvalNeg' :
          StraightLineCircuit.evalWire (C := negResult.fst.circuit) (x := x)
              (symbol.toFin (n := n) (g := negResult.fst.circuit.gates)
                hSymbolNeg) = g x := by
        have := hEvalNeg
        -- Rewrite the right-hand side using the supplied semantic description.
        have hbase := hsymbolEval x
        simpa [hneg, StraightLineCircuit.EvalBuilder.appendNotFin, hbase]
          using this
      set liftedSymbol :=
        (StraightLineCircuit.EvalBuilder.appendFin_lift
          (b := b) (op := StraightOp.not symbolWire)) symbolWire with hlift
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := negResult.fst) liftedSymbol negResult.snd with hand
      have hSymbolAnd : symbol.bound ≤ andResult.fst.circuit.gates := by
        have hmono : negResult.fst.circuit.gates ≤ andResult.fst.circuit.gates := by
          have := Nat.le_succ negResult.fst.circuit.gates
          simpa [hand, StraightLineCircuit.EvalBuilder.appendAndFin,
            Nat.succ_eq_add_one] using this
        exact Nat.le_trans hSymbolNeg hmono
      have hEvalAnd :=
        StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
          (b := negResult.fst)
          (op := StraightOp.and liftedSymbol negResult.snd)
          (w := symbol) (hw := hSymbolNeg) (x := x)
      have hEvalAnd' :
          StraightLineCircuit.evalWire (C := andResult.fst.circuit) (x := x)
              (symbol.toFin (n := n) (g := andResult.fst.circuit.gates)
                hSymbolAnd) = g x := by
        have := hEvalAnd
        have hbase := hEvalNeg'
        -- Replace the intermediate evaluation using the previous step.
        simpa [hand, StraightLineCircuit.EvalBuilder.appendAndFin, hbase]
          using this
      simpa [branchBuilderFrom, hqs, hneg, hand] using hEvalAnd'
  | true =>
      -- The `true` branch introduces a single conjunction gate.
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := b) (b.liftBase (sc.state (stateIndex M qs.1))) symbolWire with hand
      have hmono : b.circuit.gates ≤ andResult.fst.circuit.gates := by
        have := Nat.le_succ b.circuit.gates
        simpa [hand, StraightLineCircuit.EvalBuilder.appendAndFin,
          Nat.succ_eq_add_one] using this
      have hSymbolAnd : symbol.bound ≤ andResult.fst.circuit.gates :=
        Nat.le_trans hSymbol hmono
      have hEvalAnd :=
        StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
          (b := b)
          (op := StraightOp.and
            (b.liftBase (sc.state (stateIndex M qs.1))) symbolWire)
          (w := symbol) (hw := hSymbol) (x := x)
      have hEvalAnd' :
          StraightLineCircuit.evalWire (C := andResult.fst.circuit) (x := x)
              (symbol.toFin (n := n) (g := andResult.fst.circuit.gates)
                hSymbolAnd) = g x := by
        have := hEvalAnd
        have hbase := hsymbolEval x
        simpa [hand, StraightLineCircuit.EvalBuilder.appendAndFin, hbase]
          using this
      simpa [branchBuilderFrom, hqs, hand] using hEvalAnd'

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
Each iteration of `symbolBuilderStep` appends precisely two gates: one AND
combining the current head and tape wires, and one OR merging the result into
the running accumulator.  Consequently the gate count of the builder increases
by at most two per processed cell.-/
lemma symbolBuilderStep_gate_le (sc : StraightConfig M n)
    (acc : Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
        Fin (n + b.circuit.gates)) (i : Fin (M.tapeLength n)) :
    (symbolBuilderStep (M := M) (n := n) sc acc i).fst.circuit.gates ≤
      acc.fst.circuit.gates + 2 := by
  classical
  rcases acc with ⟨b, accWire⟩
  unfold symbolBuilderStep
  -- The intermediate conjunction introduces a single gate.
  set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
    (b := b) (b.liftBase (sc.head i)) (b.liftBase (sc.tape i)) with hand
  have handGate : andResult.fst.circuit.gates = b.circuit.gates + 1 := by
    simpa [andResult, StraightLineCircuit.EvalBuilder.appendAndFin]
      using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
        (b := b)
        (op := StraightOp.and (b.liftBase (sc.head i))
            (b.liftBase (sc.tape i)))
  -- The final OR also contributes one gate, yielding the required bound.
  set accLift :=
    (StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and (b.liftBase (sc.head i))
          (b.liftBase (sc.tape i)))) accWire with hlift
  set orResult := StraightLineCircuit.EvalBuilder.appendOrFin
    (b := andResult.fst) accLift andResult.snd with hor
  have horGate : orResult.fst.circuit.gates = andResult.fst.circuit.gates + 1 := by
    simpa [orResult, StraightLineCircuit.EvalBuilder.appendOrFin, handGate]
      using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
        (b := andResult.fst)
        (op := StraightOp.or accLift andResult.snd)
  have hEq : orResult.fst.circuit.gates = b.circuit.gates + 2 := calc
    orResult.fst.circuit.gates
        = andResult.fst.circuit.gates + 1 := by
            simpa [horGate, Nat.succ_eq_add_one]
    _ = (b.circuit.gates + 1) + 1 := by simpa [handGate, Nat.succ_eq_add_one]
    _ = b.circuit.gates + 2 := by
          simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hle : orResult.fst.circuit.gates ≤ b.circuit.gates + 2 := by
    simpa [hEq] using (Nat.le_refl (b.circuit.gates + 2))
  simpa [symbolBuilderStep, andResult, orResult] using hle

/--
Helper for `symbolBuilder_gate_le`: folding over a list of tape indices increases
the gate count by at most two per processed element once the initial accumulator
is accounted for.-/
lemma symbolBuilder_fold_gate_le (sc : StraightConfig M n)
    (cells : List (Fin (M.tapeLength n)))
    (acc : Σ' (b : StraightLineCircuit.EvalBuilder n sc.circuit),
        Fin (n + b.circuit.gates)) (k : ℕ)
    (hacc : acc.fst.circuit.gates ≤ sc.circuit.gates + 1 + 2 * k) :
    ((cells.foldl
        (fun acc i => symbolBuilderStep (M := M) (n := n) sc acc i)
        acc).fst.circuit.gates) ≤
      sc.circuit.gates + 1 + 2 * (k + cells.length) := by
  classical
  induction cells generalizing acc k with
  | nil =>
      simp [List.foldl_nil, hacc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | cons i cells ih =>
      -- Process the current cell and apply the inductive hypothesis to the rest.
      have hstep :=
        symbolBuilderStep_gate_le (M := M) (n := n) (sc := sc)
          (acc := acc) (i := i)
      set acc' := symbolBuilderStep (M := M) (n := n) sc acc i with hacc'
      have hacc' : acc'.fst.circuit.gates ≤
          sc.circuit.gates + 1 + 2 * (k + 1) := by
        have : acc'.fst.circuit.gates ≤ sc.circuit.gates + 1 + 2 * k + 2 :=
          Nat.le_trans hstep (Nat.add_le_add_right hacc 2)
        simpa [acc', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          two_mul, Nat.succ_eq_add_one] using this
      have := ih acc' (k + 1) hacc'
      have hlen : (k + 1) + cells.length = k + (cells.length + 1) := by
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [List.foldl_cons, acc', Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, Nat.mul_add, Nat.add_right_comm, hlen]
        using this

/--
The builder returned by `symbolBuilder` introduces at most one constant gate
plus two gates per tape cell.  This linear bound is the starting point for the
global straight-line size analysis.-/
lemma symbolBuilder_gate_le (sc : StraightConfig M n) :
    (symbolBuilder (M := M) (n := n) sc).fst.circuit.gates ≤
      sc.circuit.gates + 1 + 2 * M.tapeLength n := by
  classical
  unfold symbolBuilder
  set cells := tapeIndexList (M := M) n with hcells
  have hlen : cells.length = M.tapeLength n := by
    subst cells
    simp [tapeIndexList]
  set start := StraightLineCircuit.EvalBuilder.appendConstFin
      (b := StraightLineCircuit.EvalBuilder.mk sc.circuit) false with hstart
  have hstartGate : start.fst.circuit.gates = sc.circuit.gates + 1 := by
    simpa [start, StraightLineCircuit.EvalBuilder.appendConstFin]
      using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
        (b := StraightLineCircuit.EvalBuilder.mk sc.circuit)
        (op := StraightOp.const false)
  have hacc : start.fst.circuit.gates ≤ sc.circuit.gates + 1 + 2 * 0 := by
    simpa [hstartGate] using
      (Nat.le_of_eq (rfl : sc.circuit.gates + 1 = sc.circuit.gates + 1))
  have := symbolBuilder_fold_gate_le (M := M) (n := n) (sc := sc)
      (cells := cells) (acc := ⟨start.fst, start.snd⟩) (k := 0) hacc
  simpa [cells, hcells, start, hstartGate, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using this

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
Each invocation of `branchBuilderFrom` introduces at most two new gates.  The
case analysis mirrors the proof of `branchBuilderFrom_gate_le` but keeps track
of the exact increments contributed by the intermediate negation and
conjunction gates.-/
lemma branchBuilderFrom_gate_growth (sc : StraightConfig M n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (symbolWire : Fin (n + b.circuit.gates)) (qs : M.state × Bool) :
    let result := branchBuilderFrom (M := M) (n := n) (sc := sc)
        (b := b) (symbolWire := symbolWire) qs
    result.fst.circuit.gates ≤ b.circuit.gates + 2 := by
  classical
  -- Discharge the two cases depending on the desired symbol.
  cases hqs : qs.2 with
  | false =>
      -- The `false` branch appends a negation followed by a conjunction, hence
      -- the gate count grows by two.
      set negResult := StraightLineCircuit.EvalBuilder.appendNotFin
        (b := b) symbolWire with hneg
      set liftedState :=
        (StraightLineCircuit.EvalBuilder.appendFin_lift
          (b := b) (op := StraightOp.not symbolWire))
          (b.liftBase (sc.state (stateIndex M qs.1))) with hlift
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := negResult.fst) liftedState negResult.snd with hand
      have hnegGate :
          negResult.fst.circuit.gates = b.circuit.gates + 1 := by
        simpa [negResult, StraightLineCircuit.EvalBuilder.appendNotFin]
          using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
            (b := b) (op := StraightOp.not symbolWire)
      have handGate :
          andResult.fst.circuit.gates = negResult.fst.circuit.gates + 1 := by
        simpa [andResult, StraightLineCircuit.EvalBuilder.appendAndFin,
          hnegGate]
          using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
            (b := negResult.fst)
            (op := StraightOp.and liftedState negResult.snd)
      have htotal : andResult.fst.circuit.gates = b.circuit.gates + 2 := by
        simpa [handGate, hnegGate, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc, Nat.succ_eq_add_one]
      simpa [branchBuilderFrom, hqs, negResult, andResult]
        using (Nat.le_of_eq htotal)
  | true =>
      -- The `true` branch only appends a single conjunction gate.
      set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
        (b := b) (b.liftBase (sc.state (stateIndex M qs.1))) symbolWire
        with hand
      have handGate : andResult.fst.circuit.gates = b.circuit.gates + 1 := by
        simpa [andResult, StraightLineCircuit.EvalBuilder.appendAndFin]
          using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
            (b := b)
            (op := StraightOp.and
              (b.liftBase (sc.state (stateIndex M qs.1))) symbolWire)
      have hle : andResult.fst.circuit.gates ≤ b.circuit.gates + 2 := by
        have := Nat.le_of_eq handGate
        exact Nat.le_trans this (Nat.le_of_lt (Nat.lt_succ_self _))
      simpa [branchBuilderFrom, hqs, andResult]
        using hle

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
Appending further branches never alters the Boolean value of an existing wire.
The lemma performs the induction hidden inside `branchSnapshotAux`, making it
available as a reusable tool when analysing semantic invariants of the straight-
line snapshots.
-/
lemma branchSnapshotAux_preserves_wire (sc : StraightConfig M n)
    (symbol : StraightLineCircuit.Wire n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hSymbol : symbol.bound ≤ b.circuit.gates)
    (pairs : List (M.state × Bool))
    (w : StraightLineCircuit.Wire n)
    (hw : w.bound ≤ b.circuit.gates)
    (g : Point n → Bool)
    (hwEval : ∀ x,
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
          (w.toFin (n := n) (g := b.circuit.gates) hw) = g x) :
    let result := branchSnapshotAux (M := M) (n := n) (sc := sc)
        symbol b hSymbol pairs
    ∀ x,
      StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
          (w.toFin (n := n) (g := result.fst.circuit.gates)
            (Nat.le_trans hw result.snd.snd.fst)) = g x := by
  classical
  induction pairs generalizing b hSymbol with
  | nil =>
      intro b hSymbol x
      -- The helper returned the original builder, so the evaluation is unchanged.
      simp [branchSnapshotAux, hwEval]
  | cons qs rest ih =>
      intro b hSymbol x
      -- Interpret the wire in the current builder before appending the branch.
      set wireFin := w.toFin (n := n) (g := b.circuit.gates) hw with hwire
      -- Extend the builder by the branch `(qs.1, qs.2)` and note that the new
      -- gate count still bounds the original wire.
      have hMono : w.bound ≤
          (branchBuilderFrom (M := M) (n := n) (sc := sc)
              (b := b) (symbolWire := wireFin) qs).fst.circuit.gates := by
        exact Nat.le_trans hw
          (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
            (b := b) (symbolWire := wireFin) (qs := qs))
      -- One application of `branchBuilderFrom` preserves the evaluation of `w`.
      have hSingle : ∀ x',
          let result := branchBuilderFrom (M := M) (n := n) (sc := sc)
              (b := b) (symbolWire := wireFin) qs
          StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x')
              (w.toFin (n := n) (g := result.fst.circuit.gates) hMono) = g x' := by
        intro x'
        have := branchBuilderFrom_preserves_eval (M := M) (n := n) (sc := sc)
            (b := b) (symbol := w) (symbolWire := wireFin)
            (hSymbol := hw) (g := g) (hsymbolEval := hwEval)
            (qs := qs) x'
        simpa [wireFin] using this
      -- Peel one layer of the recursion and invoke the induction hypothesis.
      set result := branchBuilderFrom (M := M) (n := n) (sc := sc)
        (b := b) (symbolWire := wireFin) qs with hresult
      have hRec := ih result.fst
        (Nat.le_trans hSymbol
          (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
            (b := b) (symbolWire := wireFin) (qs := qs)))
        rest
        (by exact hMono)
        g
        (by
          intro x'
          have := hSingle x'
          simpa [result, hresult] using this)
      simpa [branchSnapshotAux, hresult] using hRec x

/--
Helper lemma tracking the first components of the branch list produced by
`branchSnapshotAux`.  The construction processes a prescribed list of
state/symbol pairs without reordering, hence projecting the stored wires back
to their transition identifiers simply recovers the original input list.  The
statement will later let us relate folds over the recorded wires to folds over
`stateSymbolPairs`.-/
lemma branchSnapshotAux_branches_pairs (sc : StraightConfig M n)
    (symbol : StraightLineCircuit.Wire n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hSymbol : symbol.bound ≤ b.circuit.gates)
    (pairs : List (M.state × Bool)) :
    let result := branchSnapshotAux (M := M) (n := n) (sc := sc)
        symbol b hSymbol pairs
    result.snd.snd.snd.val.map Prod.fst = pairs := by
  classical
  induction pairs generalizing b hSymbol with
  | nil =>
      intro b hSymbol
      simp [branchSnapshotAux]
  | cons qs rest ih =>
      intro b hSymbol
      -- Process the head of the list and expose the recursive tail.
      set symbolFin :=
        symbol.toFin (n := n) (g := b.circuit.gates) hSymbol with hsymbolFin
      set result := branchBuilderFrom (M := M) (n := n) (sc := sc)
        (b := b) (symbolWire := symbolFin) qs with hresult
      have hSymbolNext : symbol.bound ≤ result.fst.circuit.gates := by
        exact Nat.le_trans hSymbol
          (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
            (b := b) (symbolWire := symbolFin) (qs := qs))
      obtain ⟨bRest, _hSym, _hMono, restList⟩ :=
        branchSnapshotAux (M := M) (n := n) (sc := sc)
          symbol result.fst hSymbolNext rest
      -- Reconstruct the final list and apply the inductive hypothesis on the
      -- tail to conclude that the projection matches the input sequence.
      simp [branchSnapshotAux, hresult, ih, symbolFin, hsymbolFin]

/--
Specialisation of `branchSnapshotAux_branches_pairs` to the concrete branch
snapshot.  Every recorded wire is paired with the transition `(q, b)` that gave
rise to it, and the list of pairs follows the order of
`stateSymbolPairs` exactly.-/
lemma branchSnapshot_branches_pairs (sc : StraightConfig M n) :
    (branchSnapshot (M := M) (n := n) sc).branches.map Prod.fst =
      stateSymbolPairs M := by
  classical
  unfold branchSnapshot
  set symbolResult := symbolBuilderWire (M := M) (n := n) sc with hsymbol
  have hSymbol : symbolResult.snd.bound ≤ symbolResult.fst.circuit.gates := by
    have := (by
      simp [symbolResult] : symbolResult.snd.bound = symbolResult.fst.circuit.gates)
    exact le_of_eq this
  obtain ⟨bFinal, _hsym, _hmono, restList⟩ :=
    branchSnapshotAux (M := M) (n := n) (sc := sc)
      symbolResult.snd symbolResult.fst hSymbol (stateSymbolPairs M)
  simpa [symbolResult]
    using branchSnapshotAux_branches_pairs (M := M) (n := n) (sc := sc)
      (symbol := symbolResult.snd) (b := symbolResult.fst)
      (hSymbol := hSymbol) (pairs := stateSymbolPairs M)

/--
Semantic counterpart to `branchSnapshotAux`: every recorded branch wire
evaluates to the Boolean guard checking whether the machine is currently in the
designated state and scans the designated symbol.  The lemma proceeds in lock
step with the recursion defining `branchSnapshotAux` and reuses the semantic
description of `branchBuilderFrom` established earlier.-/
lemma branchSnapshotAux_branches_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f)
    (symbol : StraightLineCircuit.Wire n)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hSymbol : symbol.bound ≤ b.circuit.gates)
    (hsymbolEval : ∀ x,
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
          (symbol.toFin (n := n) (g := b.circuit.gates) hSymbol) =
        (f x).tape (f x).head)
    (pairs : List (M.state × Bool)) :
    let result := branchSnapshotAux (M := M) (n := n) (sc := sc)
        symbol b hSymbol pairs
    ∀ x {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
      (hmem : (qs, w) ∈ result.snd.snd.snd.val) →
        let hbound := result.snd.snd.snd.property (by simpa using hmem)
        StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
            (w.toFin (n := n) (g := result.fst.circuit.gates) hbound) =
          branchGuard (M := M) (conf := f x) qs := by
  classical
  induction pairs generalizing b hSymbol hsymbolEval with
  | nil =>
      intro b hSymbol hsymbolEval x qs w hmem
      cases hmem
  | cons qs rest ih =>
      intro b hSymbol hsymbolEval x qs' w hmem
      -- Interpret the cached symbol wire inside the current builder.
      set symbolFin :=
        symbol.toFin (n := n) (g := b.circuit.gates) hSymbol with hsymbolFin
      set result := branchBuilderFrom (M := M) (n := n) (sc := sc)
        (b := b) (symbolWire := symbolFin) qs with hresult
      have hSymbolNext : symbol.bound ≤ result.fst.circuit.gates := by
        exact Nat.le_trans hSymbol
          (branchBuilderFrom_gate_le (M := M) (n := n) (sc := sc)
            (b := b) (symbolWire := symbolFin) (qs := qs))
      -- The semantic description of the symbol wire persists across the step.
      have hsymbolEval' : ∀ x,
          StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
              (symbol.toFin (n := n) (g := result.fst.circuit.gates)
                hSymbolNext) = (f x).tape (f x).head := by
        intro x'
        have := branchBuilderFrom_preserves_eval (M := M) (n := n) (sc := sc)
            (b := b) (symbol := symbol) (symbolWire := symbolFin)
            (hSymbol := hSymbol) (g := fun x => (f x).tape (f x).head)
            (hsymbolEval := hsymbolEval) (qs := qs) x'
        simpa [symbolFin, hresult]
          using this
      -- Decompose the recursion and analyse the membership proof.
      obtain ⟨bRest, hSymbolRest, _hmono, restList⟩ :=
        branchSnapshotAux (M := M) (n := n) (sc := sc)
          symbol result.fst hSymbolNext rest
      have hmem' := List.mem_cons.1 hmem
      cases hmem' with
      | inl hhead =>
          -- The current element corresponds to the freshly appended wire.
          cases hhead with
          | rfl =>
              have hbranch := branchBuilderFrom_spec (M := M) (n := n) (sc := sc)
                (f := f) hsc (b := b) (symbolWire := symbolFin)
                (hsymbol := hsymbolEval) (x := x) (qs := qs)
              simpa [branchSnapshotAux, hresult, symbolFin, hsymbolFin,
                restList, branchGuard] using hbranch
      | inr htail =>
          -- Remaining elements come from the recursive call; invoke the IH.
          have htail' : (qs', w) ∈ restList.val := htail
          have hrec := ih (b := result.fst) (hSymbol := hSymbolNext)
            (hsymbolEval := hsymbolEval') (x := x) (qs := qs') (w := w) htail'
          -- Rewrite the ambient circuit to match the result of the recursion.
          simpa [branchSnapshotAux, hresult]
            using hrec

/--
Straightforward corollary packaging the semantic information carried by the
full branch snapshot.  The reusable symbol wire computes the tape bit underneath
the head, and every stored branch wire coincides with the Boolean guard
`branchGuard` for its corresponding transition.-/
lemma branchSnapshot_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    let snapshot := branchSnapshot (M := M) (n := n) sc
    (∀ x,
        StraightLineCircuit.evalWire (C := snapshot.builder.circuit) (x := x)
          (snapshot.symbol.toFin (n := n)
            (g := snapshot.builder.circuit.gates) snapshot.symbol_le) =
          (f x).tape (f x).head) ∧
      ∀ x {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
        (hmem : (qs, w) ∈ snapshot.branches) →
          let hbound := snapshot.branches_le hmem
          StraightLineCircuit.evalWire (C := snapshot.builder.circuit) (x := x)
              (w.toFin (n := n) (g := snapshot.builder.circuit.gates) hbound) =
            branchGuard (M := M) (conf := f x) qs := by
  classical
  -- Expand the definition to expose the auxiliary builder returned by the
  -- branch snapshot helper.
  unfold branchSnapshot
  set symbolResult := symbolBuilderWire (M := M) (n := n) sc with hsymbol
  have hSymbolBound : symbolResult.snd.bound ≤ symbolResult.fst.circuit.gates := by
    have := (by
      simp [symbolResult] : symbolResult.snd.bound = symbolResult.fst.circuit.gates)
    exact le_of_eq this
  have hSymbolEval : ∀ x,
      StraightLineCircuit.evalWire (C := symbolResult.fst.circuit) (x := x)
          (symbolResult.snd.toFin (n := n)
            (g := symbolResult.fst.circuit.gates) hSymbolBound) =
        (f x).tape (f x).head := by
    intro x
    simpa [symbolResult]
      using symbolBuilderWire_spec (M := M) (n := n) (sc := sc) (f := f) hsc (x := x)
  obtain ⟨bFinal, hSymbolFinal, hMono, restList⟩ :=
    branchSnapshotAux (M := M) (n := n) (sc := sc)
      symbolResult.snd symbolResult.fst hSymbolBound (stateSymbolPairs M)
  have hSymbolPres := branchSnapshotAux_preserves_wire (M := M) (n := n)
      (sc := sc) (symbol := symbolResult.snd) (b := symbolResult.fst)
      (hSymbol := hSymbolBound) (pairs := stateSymbolPairs M)
      (w := symbolResult.snd) (hw := hSymbolBound)
      (g := fun x => (f x).tape (f x).head) (hwEval := hSymbolEval)
  -- Collect the two requested statements: one for the symbol wire, one for the
  -- individual branch guards.
  constructor
  · intro x
    have := hSymbolPres (x := x)
    -- Rewrite the sigma components to match the concrete snapshot fields.
    simpa [symbolResult, snapshot, branchSnapshot, Nat.le_trans, hMono]
      using this
  · intro x qs w hmem
    have hbranch := branchSnapshotAux_branches_spec (M := M) (n := n)
        (sc := sc) (f := f) hsc (symbol := symbolResult.snd)
        (b := symbolResult.fst) (hSymbol := hSymbolBound)
        (hsymbolEval := hSymbolEval) (pairs := stateSymbolPairs M)
    -- Interpret the membership proof in terms of the helper output.
    have := hbranch (x := x) (qs := qs) (w := w)
    have hmem' : (qs, w) ∈ restList.val := by simpa [symbolResult] using hmem
    -- Evaluate the guard and rewrite the resulting indices.
    have hresult := this hmem'
    simpa [symbolResult]
      using hresult

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
Augmented snapshot containing, in addition to the branch and write information,
the straight-line wires computing the tape contents after one transition.
-/
structure TapeSnapshot (sc : StraightConfig M n)
    extends WriteSnapshot (M := M) (n := n) sc where
  tapes : List (Fin (M.tapeLength n) × StraightLineCircuit.Wire n)
  tapes_le :
    ∀ {i : Fin (M.tapeLength n)} {w : StraightLineCircuit.Wire n},
      (i, w) ∈ tapes → w.bound ≤ builder.circuit.gates

/-- Helper used to collect the indices of write-contributing wires.  The
definition mirrors the recursive helper appearing in `writeSnapshot`. -/
def writeIndexList (sc : StraightConfig M n)
    (snapshot : BranchSnapshot (M := M) (n := n) sc) :
    List (Fin (n + snapshot.builder.circuit.gates)) := by
  classical
  let rec collect
      (branches : List ((M.state × Bool) × StraightLineCircuit.Wire n)) :
      (∀ {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
          (qs, w) ∈ branches → w.bound ≤ snapshot.builder.circuit.gates) →
        List (Fin (n + snapshot.builder.circuit.gates))
    | [], _ => []
    | (qs, w) :: rest, h =>
        let restList := collect rest (fun {qs'} {w'} hmem =>
          h (by exact List.mem_cons_of_mem _ hmem))
        let hbound : w.bound ≤ snapshot.builder.circuit.gates :=
          h (by exact List.mem_cons_self _ _)
        if (M.step qs.1 qs.2).2 then
          (w.toFin (n := n) (g := snapshot.builder.circuit.gates) hbound) ::
            restList
        else
          restList
  termination_by collect branches _ => branches.length
  exact collect snapshot.branches snapshot.branches_le

/--
Evaluate the list of indices returned by `writeIndexList`.  The result is the
Boolean OR of precisely those branch wires whose transitions request writing a
`true` bit.  The statement is phrased using `StraightLineCircuit.evalList`, which
matches the helper employed by `appendBigOr`.-/
lemma writeIndexList_eval (sc : StraightConfig M n)
    (snapshot : BranchSnapshot (M := M) (n := n) sc)
    (x : Point n) :
    StraightLineCircuit.evalList (C := snapshot.builder.circuit) (x := x)
        (writeIndexList (M := M) (n := n) (sc := sc) snapshot) =
      snapshot.branches.foldl (fun acc (qs, w) =>
        if (M.step qs.1 qs.2).2 then
          acc ||
            StraightLineCircuit.evalWire (C := snapshot.builder.circuit)
              (x := x)
              (w.toFin (n := n) (g := snapshot.builder.circuit.gates)
                (snapshot.branches_le (by simpa)))
        else acc) false := by
  classical
  -- Destructure the snapshot to expose its branch list explicitly.
  cases snapshot with
  | mk builder symbol symbol_le branches branches_le =>
      revert branches_le
      -- Perform induction on the list of recorded branches.
      induction branches with
      | nil =>
          intro _
          simp [writeIndexList, StraightLineCircuit.evalList]
      | cons head tail ih =>
          intro hle
          rcases head with ⟨qs, w⟩
          have hTail : ∀ {qs' : M.state × Bool} {w' : StraightLineCircuit.Wire n},
              (qs', w') ∈ tail → w'.bound ≤ builder.circuit.gates := by
            intro qs' w' hmem
            exact hle (by exact List.mem_cons_of_mem _ hmem)
          -- Expand the recursive definition of `writeIndexList` on the current
          -- branch list.
          simp [writeIndexList, hTail] at ih ⊢
          -- Distinguish the cases depending on the write bit prescribed by the
          -- transition.
          by_cases hwrite : (M.step qs.1 qs.2).2
          · simp [hwrite, StraightLineCircuit.evalList, List.foldl_cons, ih hTail]
          · simp [hwrite, StraightLineCircuit.evalList, List.foldl_cons, ih hTail]

/-- Length of `writeIndexList` is bounded by the number of processed branches. -/
lemma writeIndexList_length_le (sc : StraightConfig M n)
    (snapshot : BranchSnapshot (M := M) (n := n) sc) :
    (writeIndexList (M := M) (n := n) (sc := sc) snapshot).length ≤
      snapshot.branches.length := by
  classical
  unfold writeIndexList
  -- We prove a slightly stronger statement by induction on the branch list.
  let rec collectLength
      (branches : List ((M.state × Bool) × StraightLineCircuit.Wire n)) :
      (∀ {qs : M.state × Bool} {w : StraightLineCircuit.Wire n},
          (qs, w) ∈ branches → w.bound ≤ snapshot.builder.circuit.gates) →
        (collect branches ?_).length ≤ branches.length := by
    intro h
    cases branches with
    | nil => simp
    | cons head rest =>
        cases head with
        | mk qs w =>
            dsimp at h ⊢
            have hTail := collectLength rest (fun {qs'} {w'} hmem =>
              h (by exact List.mem_cons_of_mem _ hmem))
            by_cases hwrite : (M.step qs.1 qs.2).2
            · simp [hwrite, hTail, Nat.succ_eq_add_one]
            · have : (collect rest
                  (fun {qs'} {w'} hmem =>
                    h (by exact List.mem_cons_of_mem _ hmem))).length ≤
                rest.length := hTail
              simpa [hwrite, Nat.succ_eq_add_one] using this
  simpa using collectLength snapshot.branches snapshot.branches_le

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
  -- Instantiate the helper collecting all write-contributing wires.
  let writeIndices := writeIndexList (M := M) (n := n) (sc := sc) base
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

/-- Gate-count bound for the complete write snapshot.  The resulting circuit
extends the branch snapshot by an additional `bigOr` whose size is controlled by
the number of relevant branches.-/
lemma writeSnapshot_gate_le (sc : StraightConfig M n) :
    (writeSnapshot (M := M) (n := n) sc).builder.circuit.gates ≤
      sc.circuit.gates + 2 * M.tapeLength n + 8 * stateCard M + 2 := by
  classical
  unfold writeSnapshot
  set base := branchSnapshot (M := M) (n := n) sc with hbase
  set writeIndices := writeIndexList (M := M) (n := n) (sc := sc) base
    with hindices
  have hBase := branchSnapshot_gate_le (M := M) (n := n) (sc := sc)
  have hLenBranches := branchSnapshot_branches_length (M := M) (n := n) (sc := sc)
  have hIndices := writeIndexList_length_le (M := M) (n := n) (sc := sc) base
  have hPairs : (stateSymbolPairs M).length = 2 * stateCard M :=
    length_stateSymbolPairs (M := M)
  have hLen' := Nat.le_trans hIndices
      (by simpa [hbase, hindices] using Nat.le_of_eq hLenBranches)
  have hLen : writeIndices.length ≤ 2 * stateCard M := by
    simpa [hPairs] using hLen'
  have hAppend := StraightLineCircuit.EvalBuilder.appendBigOr_gate_le_linear
    (b := base.builder) (ws := writeIndices)
  have hStep := Nat.le_trans hAppend
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hLen) _)
  have hTotal := Nat.le_trans hStep
    (Nat.add_le_add_left hBase (2 * writeIndices.length + 1))
  have hConst : 2 * writeIndices.length ≤ 8 * stateCard M := by
    have := Nat.mul_le_mul_left 2 hLen
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using Nat.le_trans this (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Nat.lt_succ_self _)))
  have hFinal := Nat.add_le_add hBase (Nat.add_le_add hConst (by decide))
  have hRewrite :
      base.builder.circuit.gates + (2 * writeIndices.length + 1) ≤
        sc.circuit.gates + 2 * M.tapeLength n + 8 * stateCard M + 2 := by
    simpa [hbase, hindices, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      two_mul]
      using hFinal
  simpa [hRewrite, hbase, hindices, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]
    using hTotal

/--
Semantic characterisation of the write snapshot.  The aggregated write wire
computes the Boolean predicate `writeAccumulator` capturing the effect of all
transition branches on the tape cell located under the head.-/
lemma writeSnapshot_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    let snapshot := writeSnapshot (M := M) (n := n) sc
    ∀ x,
      StraightLineCircuit.evalWire (C := snapshot.builder.circuit) (x := x)
          (snapshot.write.toFin (n := n)
            (g := snapshot.builder.circuit.gates) snapshot.write_le) =
        writeAccumulator (M := M) (pairs := stateSymbolPairs M) (f x) := by
  classical
  -- Expose the underlying branch snapshot and its semantic guarantees.
  set base := branchSnapshot (M := M) (n := n) sc with hbase
  have hBaseSpec := branchSnapshot_spec (M := M) (n := n) (sc := sc) (f := f) hsc
  -- Shorthand for the list of write-contributing wires.
  set writeIndices := writeIndexList (M := M) (n := n) (sc := sc) base
    with hindices
  -- Evaluate the big OR produced by `writeSnapshot` via the helper lemma on
  -- `appendBigOr`.
  intro x
  have hEval := StraightLineCircuit.EvalBuilder.appendBigOr_eval
      (b := base.builder) (ws := writeIndices) (x := x)
  -- The evaluation of `writeIndices` expands to the fold over the recorded
  -- branches, which in turn reduces to the semantic write accumulator.
  have hFold := writeIndexList_eval (M := M) (n := n) (sc := sc)
      (snapshot := base) (x := x)
  -- Translate evaluation of branch wires into semantic branch guards.
  have hBranches := hBaseSpec.2
  -- Rewrite the fold to align with `writeAccumulator`.
  have hList := branchSnapshot_branches_pairs (M := M) (n := n) (sc := sc)
  -- Assemble the final identity, unpacking the structure created by
  -- `writeSnapshot`.
  -- Replace the evaluation of the `bigOr` by the explicit fold over indices.
  have hEvalWire :
      StraightLineCircuit.evalWire
          (C := (StraightLineCircuit.EvalBuilder.appendBigOr
            (b := base.builder) writeIndices).fst.circuit) (x := x)
          ((StraightLineCircuit.Wire.ofFin (n := n)
              (g := (StraightLineCircuit.EvalBuilder.appendBigOr
                (b := base.builder) writeIndices).fst.circuit.gates)
              (StraightLineCircuit.EvalBuilder.appendBigOr
                (b := base.builder) writeIndices).snd).toFin
            (n := n)
            (g := (StraightLineCircuit.EvalBuilder.appendBigOr
              (b := base.builder) writeIndices).fst.circuit.gates)
            (by
              have := StraightLineCircuit.Wire.ofFin_bound
                (n := n)
                (g := (StraightLineCircuit.EvalBuilder.appendBigOr
                  (b := base.builder) writeIndices).fst.circuit.gates)
                (StraightLineCircuit.EvalBuilder.appendBigOr
                  (b := base.builder) writeIndices).snd
              simpa using le_of_eq this)) =
        StraightLineCircuit.evalList (C := base.builder.circuit) (x := x)
          writeIndices := by
    simpa [writeSnapshot, hbase, hindices,
      StraightLineCircuit.Wire.toFin_ofFin]
      using hEval
  -- Evaluate the fold over recorded branches.
  have hFold' := hFold
  -- Replace the evaluation of branch wires by their semantic guards.
  have hEvalBranches :
      base.branches.foldl (fun acc (qs, w) =>
          if (M.step qs.1 qs.2).2 then
            acc ||
              StraightLineCircuit.evalWire (C := base.builder.circuit) (x := x)
                (w.toFin (n := n) (g := base.builder.circuit.gates)
                  (base.branches_le (by simpa [hbase] using
                    (List.mem_cons_self (qs, w) base.branches))))
          else acc) false =
        base.branches.foldl (fun acc (qs, w) =>
          if (M.step qs.1 qs.2).2 then
            acc || branchGuard (M := M) (conf := f x) qs
          else acc) false := by
    revert hBranches
    revert x
    refine List.rec ?baseCase ?stepCase (l := base.branches)
    · intro x hBranches; simp
    · intro head tail ih x hBranches
      rcases head with ⟨qs, w⟩
      have hHead := hBranches (by simpa [hbase] using List.mem_cons_self (qs, w) tail)
      have hTail : ∀ {qs' : M.state × Bool} {w' : StraightLineCircuit.Wire n},
          (qs', w') ∈ tail →
            StraightLineCircuit.evalWire (C := base.builder.circuit) (x := x)
              (w'.toFin (n := n) (g := base.builder.circuit.gates)
                (base.branches_le (by
                  have := List.mem_cons_of_mem (a := (qs, w)) (l := tail) hmem
                  simpa [hbase] using this))) =
              branchGuard (M := M) (conf := f x) qs' := by
        intro qs' w' hmem
        exact hBranches (by
          have := List.mem_cons_of_mem (a := (qs, w)) hmem
          simpa [hbase] using this)
      have hTailFold := ih x hTail
      by_cases hwrite : (M.step qs.1 qs.2).2
      · simp [List.foldl_cons, hwrite, hHead, hTailFold]
      · simp [List.foldl_cons, hwrite, hHead, hTailFold]
  -- Combine the previous equalities to express the evaluation purely in terms of
  -- branch guards.
  have hEvalListGuard :
      StraightLineCircuit.evalList (C := base.builder.circuit) (x := x)
          writeIndices =
        base.branches.foldl (fun acc (qs, w) =>
          if (M.step qs.1 qs.2).2 then
            acc || branchGuard (M := M) (conf := f x) qs
          else acc) false := hFold'.trans hEvalBranches
  have hEvalOr :
      StraightLineCircuit.evalWire (C := snapshot.builder.circuit) (x := x)
          (snapshot.write.toFin (n := n)
            (g := snapshot.builder.circuit.gates) snapshot.write_le) =
        base.branches.foldl (fun acc (qs, w) =>
          if (M.step qs.1 qs.2).2 then
            acc || branchGuard (M := M) (conf := f x) qs
          else acc) false := by
    simpa [writeSnapshot, hbase, hindices,
      StraightLineCircuit.Wire.toFin_ofFin]
      using (hEvalWire.trans hEvalListGuard)
  -- Rewrite the fold as a Boolean `any` to appeal to the existing lemmas about
  -- `writeAccumulator`.
  have hAny : base.branches.foldl (fun acc (qs, w) =>
        if (M.step qs.1 qs.2).2 then acc || branchGuard (M := M) (conf := f x) qs
        else acc) false =
      List.any base.branches (fun pair =>
        if (M.step pair.1.1 pair.1.2).2 then
          branchGuard (M := M) (conf := f x) pair.1
        else false) := by
    simpa using (foldl_or_eq_any (l := base.branches)
      (f := fun pair =>
        if (M.step pair.1.1 pair.1.2).2 then
          branchGuard (M := M) (conf := f x) pair.1
        else false))
  have hAnyPairs :
      List.any base.branches (fun pair =>
        if (M.step pair.1.1 pair.1.2).2 then
          branchGuard (M := M) (conf := f x) pair.1
        else false) =
        List.any (stateSymbolPairs M) (fun qs =>
          if (M.step qs.1 qs.2).2 then
            branchGuard (M := M) (conf := f x) qs
          else false) := by
    simpa [List.map] using congrArg (fun l =>
      List.any l (fun qs =>
        if (M.step qs.1 qs.2).2 then branchGuard (M := M) (conf := f x) qs
        else false)) hList
  -- Conclude using the specification of the write accumulator.
  have hAccumulator := writeAccumulator_eq_any (M := M) (n := n)
      (conf := f x) (pairs := stateSymbolPairs M)
  simpa [writeSnapshot, hbase, hindices, hAny, hAnyPairs,
    writeContribution, branchGuard]
    using (hEvalOr.trans (by simpa using hAccumulator.symm))

/-- The write wire recorded in the snapshot realises the exact transition bit of
the Turing machine. -/
lemma writeSnapshot_step_spec (sc : StraightConfig M n)
    {f : Point n → TM.Configuration M n}
    (hsc : Spec (M := M) (n := n) sc f) :
    let snapshot := writeSnapshot (M := M) (n := n) sc
    ∀ x,
      StraightLineCircuit.evalWire (C := snapshot.builder.circuit) (x := x)
          (snapshot.write.toFin (n := n)
            (g := snapshot.builder.circuit.gates) snapshot.write_le) =
        let sym := (f x).tape (f x).head
        let (_, bit, _) := M.step (f x).state sym
        bit := by
  classical
  intro snapshot x
  have hSnap := writeSnapshot_spec (M := M) (n := n) (sc := sc) (f := f) hsc
  dsimp [snapshot] at hSnap
  have hEval := hSnap x
  have hAcc := writeAccumulator_spec (M := M) (n := n) (conf := f x)
  simpa [hAcc]
    using hEval

/--
Single-cell update used when constructing the straight-line representation of
the successor tape.  Starting from a builder that already contains the guard and
write information recorded by `writeSnapshot`, the helper appends a fixed
sequence of gates realising the Boolean expression
`(head ∧ write) ∨ (!head ∧ tape)` for the cell `i`.
-/
def tapeBuilderStep (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hWrite : snapshot.write.bound ≤ b.circuit.gates)
    (i : Fin (M.tapeLength n)) :
    Σ' (b' : StraightLineCircuit.EvalBuilder n sc.circuit),
        (snapshot.write.bound ≤ b'.circuit.gates) ×
        StraightLineCircuit.Wire n :=
  by
    classical
    -- Reinterpret the head, tape and aggregated write wires inside the current
    -- builder.
    let headWire := b.liftBase (sc.head i)
    let tapeWire := b.liftBase (sc.tape i)
    let writeWire := snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite
    -- First append the conjunction `head ∧ write`.
    let andResult := StraightLineCircuit.EvalBuilder.appendAndFin
      (b := b) headWire writeWire
    have hWrite₁ : snapshot.write.bound ≤ andResult.fst.circuit.gates := by
      have hmono : b.circuit.gates ≤ andResult.fst.circuit.gates := by
        have := Nat.le_succ b.circuit.gates
        simpa [StraightLineCircuit.EvalBuilder.appendAndFin,
          StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
          StraightLineCircuit.snoc, Nat.succ_eq_add_one]
          using this
      exact Nat.le_trans hWrite hmono
    -- Lift the head and tape wires through the newly appended gate.
    let headLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) headWire
    let tapeLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) tapeWire
    let andLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) andResult.snd
    -- Append the negation `¬ head`.
    let notResult := StraightLineCircuit.EvalBuilder.appendNotFin
      (b := andResult.fst) headLift
    have hWrite₂ : snapshot.write.bound ≤ notResult.fst.circuit.gates := by
      have hmono : andResult.fst.circuit.gates ≤ notResult.fst.circuit.gates := by
        have := Nat.le_succ andResult.fst.circuit.gates
        simpa [StraightLineCircuit.EvalBuilder.appendNotFin,
          StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
          StraightLineCircuit.snoc, Nat.succ_eq_add_one]
          using this
      exact Nat.le_trans hWrite₁ hmono
    -- Lift the accumulated wires across the negation gate.
    let tapeLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) tapeLift
    let andLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) andResult.snd
    -- Combine `¬ head` with the original tape bit.
    let keepResult := StraightLineCircuit.EvalBuilder.appendAndFin
      (b := notResult.fst) notResult.snd tapeLift'
    have hWrite₃ : snapshot.write.bound ≤ keepResult.fst.circuit.gates := by
      have hmono : notResult.fst.circuit.gates ≤ keepResult.fst.circuit.gates := by
        have := Nat.le_succ notResult.fst.circuit.gates
        simpa [StraightLineCircuit.EvalBuilder.appendAndFin,
          StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
          StraightLineCircuit.snoc, Nat.succ_eq_add_one]
          using this
      exact Nat.le_trans hWrite₂ hmono
    -- Transport `head ∧ write` to the current builder and append the final OR.
    let andLift'' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := notResult.fst)
      (op := StraightOp.and notResult.snd tapeLift') andLift'
    let final := StraightLineCircuit.EvalBuilder.appendOrFin
      (b := keepResult.fst) andLift'' keepResult.snd
    have hWrite₄ : snapshot.write.bound ≤ final.fst.circuit.gates := by
      have hmono : keepResult.fst.circuit.gates ≤ final.fst.circuit.gates := by
        have := Nat.le_succ keepResult.fst.circuit.gates
        simpa [StraightLineCircuit.EvalBuilder.appendOrFin,
          StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
          StraightLineCircuit.snoc, Nat.succ_eq_add_one]
          using this
      exact Nat.le_trans hWrite₃ hmono
    refine ⟨ final.fst, hWrite₄,
      StraightLineCircuit.Wire.ofFin (n := n)
        (g := final.fst.circuit.gates) final.snd ⟩

/--
Each invocation of `tapeBuilderStep` appends exactly four gates to the current
builder.  The newly created circuit therefore contains the previous gates plus
the contributions of one AND, one NOT, one AND and one OR gate.
-/
lemma tapeBuilderStep_gate_eq (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hWrite : snapshot.write.bound ≤ b.circuit.gates)
    (i : Fin (M.tapeLength n)) :
    let result := tapeBuilderStep (M := M) (n := n) (sc := sc)
        (snapshot := snapshot) (b := b) (hWrite := hWrite) i
    result.fst.circuit.gates = b.circuit.gates + 4 :=
  by
    classical
    -- Unfold the helper and expose the intermediate builders.
    unfold tapeBuilderStep
    -- Introduce shorthand for the successive builders arising in the
    -- construction.
    set headWire := b.liftBase (sc.head i)
    set tapeWire := b.liftBase (sc.tape i)
    set writeWire := snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite
    set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
      (b := b) headWire writeWire
    set headLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) headWire
    set tapeLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) tapeWire
    set andLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) andResult.snd
    set notResult := StraightLineCircuit.EvalBuilder.appendNotFin
      (b := andResult.fst) headLift
    set tapeLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) tapeLift
    set andLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) andResult.snd
    set keepResult := StraightLineCircuit.EvalBuilder.appendAndFin
      (b := notResult.fst) notResult.snd tapeLift'
    set andLift'' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := notResult.fst)
      (op := StraightOp.and notResult.snd tapeLift') andLift'
    set final := StraightLineCircuit.EvalBuilder.appendOrFin
      (b := keepResult.fst) andLift'' keepResult.snd
    -- Replace the goal with the corresponding arithmetic statement.
    have hAnd : andResult.fst.circuit.gates = b.circuit.gates + 1 := by
      simpa [andResult, StraightLineCircuit.EvalBuilder.appendAndFin]
        using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
          (b := b) (op := StraightOp.and headWire writeWire)
    have hNot : notResult.fst.circuit.gates = andResult.fst.circuit.gates + 1 := by
      simpa [notResult, StraightLineCircuit.EvalBuilder.appendNotFin]
        using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
          (b := andResult.fst) (op := StraightOp.not headLift)
    have hKeep : keepResult.fst.circuit.gates = notResult.fst.circuit.gates + 1 := by
      simpa [keepResult, StraightLineCircuit.EvalBuilder.appendAndFin]
        using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
          (b := notResult.fst)
          (op := StraightOp.and notResult.snd tapeLift')
    have hFinal : final.fst.circuit.gates = keepResult.fst.circuit.gates + 1 := by
      simpa [final, StraightLineCircuit.EvalBuilder.appendOrFin]
        using StraightLineCircuit.EvalBuilder.appendFin_gate_eq
          (b := keepResult.fst)
          (op := StraightOp.or andLift'' keepResult.snd)
    -- Combine the four increments into the stated equality.
    simp [hAnd, hNot, hKeep, hFinal, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

/--
Semantic description of the wire produced by `tapeBuilderStep`.  The resulting
gate realises the Boolean expression `(head ∧ write) ∨ (!head ∧ tape)` where the
three input wires are interpreted in the original straight-line configuration.
-/
lemma tapeBuilderStep_eval (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hWrite : snapshot.write.bound ≤ b.circuit.gates)
    (i : Fin (M.tapeLength n))
    (x : Point n) :
    let result := tapeBuilderStep (M := M) (n := n) (sc := sc)
        (snapshot := snapshot) (b := b) (hWrite := hWrite) i
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (result.snd.toFin (n := n) (g := result.fst.circuit.gates)
          (by
            -- For wires created via `Wire.ofFin` the bound coincides with the
            -- ambient gate count, hence the coercion is immediate.
            have := StraightLineCircuit.Wire.ofFin_bound (n := n)
              (g := final.fst.circuit.gates) final.snd
            simpa [result, tapeBuilderStep, final] using
              (le_of_eq this))) =
      let headVal := StraightLineCircuit.evalWire (C := sc.circuit) (x := x)
          (sc.head i)
      let tapeVal := StraightLineCircuit.evalWire (C := sc.circuit) (x := x)
          (sc.tape i)
      let writeVal := StraightLineCircuit.evalWire (C := b.circuit) (x := x)
          (snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite)
      in
        (headVal && writeVal) || (!headVal && tapeVal) :=
  by
    classical
    -- Expand the helper and record the intermediate builders.
    unfold tapeBuilderStep
    set headWire := b.liftBase (sc.head i)
    set tapeWire := b.liftBase (sc.tape i)
    set writeWire := snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite
    set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
      (b := b) headWire writeWire
    set headLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) headWire
    set tapeLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) tapeWire
    set andLift := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := b) (op := StraightOp.and headWire writeWire) andResult.snd
    set notResult := StraightLineCircuit.EvalBuilder.appendNotFin
      (b := andResult.fst) headLift
    set tapeLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) tapeLift
    set andLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) andResult.snd
    set keepResult := StraightLineCircuit.EvalBuilder.appendAndFin
      (b := notResult.fst) notResult.snd tapeLift'
    set andLift'' := StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := notResult.fst)
      (op := StraightOp.and notResult.snd tapeLift') andLift'
    set final := StraightLineCircuit.EvalBuilder.appendOrFin
      (b := keepResult.fst) andLift'' keepResult.snd
    -- Evaluate the intermediate gates step by step.
    have hHeadEval :
        StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.head i) =
          StraightLineCircuit.evalWire (C := b.circuit) (x := x) headWire := by
      rfl
    have hTapeEval :
        StraightLineCircuit.evalWire (C := sc.circuit) (x := x) (sc.tape i) =
          StraightLineCircuit.evalWire (C := b.circuit) (x := x) tapeWire := by
      rfl
    have hAndEval := StraightLineCircuit.EvalBuilder.appendAndFin_eval
      (b := b) (u := headWire) (v := writeWire) (x := x)
    have hHeadLift := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
      (b := b) (op := StraightOp.and headWire writeWire) (x := x)
      (w := sc.head i)
    have hTapeLift := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
      (b := b) (op := StraightOp.and headWire writeWire) (x := x)
      (w := sc.tape i)
    have hAndLift := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
      (b := b) (op := StraightOp.and headWire writeWire) (x := x)
      (w := andResult.snd)
    have hNotEval := StraightLineCircuit.EvalBuilder.appendFin_eval
      (b := andResult.fst) (op := StraightOp.not headLift) (x := x)
    have hTapeLift' := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
      (b := andResult.fst) (op := StraightOp.not headLift) (x := x)
      (w := tapeWire)
    have hAndLift' := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
      (b := andResult.fst) (op := StraightOp.not headLift) (x := x)
      (w := andResult.snd)
    have hKeepEval := StraightLineCircuit.EvalBuilder.appendAndFin_eval
      (b := notResult.fst) (u := notResult.snd) (v := tapeLift') (x := x)
    have hAndLift'' := StraightLineCircuit.EvalBuilder.appendFin_lift_eval
      (b := notResult.fst)
      (op := StraightOp.and notResult.snd tapeLift') (x := x)
      (w := andResult.snd)
    have hFinalEval := StraightLineCircuit.EvalBuilder.appendOrFin_eval
      (b := keepResult.fst) (u := andLift'') (v := keepResult.snd) (x := x)
    -- Simplify the collected equalities.
    simp [headWire, tapeWire, writeWire, andResult, notResult, keepResult,
      andLift, andLift', andLift'', tapeLift, tapeLift', headLift, final,
      StraightLineCircuit.Wire.toFin_ofFin, hHeadEval, hTapeEval,
      hAndEval, hHeadLift, hTapeLift, hAndLift, hNotEval, hTapeLift',
      hAndLift', hKeepEval, hAndLift'', hFinalEval, Bool.or_left_comm,
      Bool.or_assoc, Bool.or_comm, Bool.and_left_comm, Bool.and_assoc,
      Bool.and_comm]

/--
The wire produced by `tapeBuilderStep` always refers to an existing gate of the
resulting builder.  This convenience lemma packages the bound witnessed by
`Wire.ofFin_bound` so that subsequent constructions can reuse it without
unfolding the helper from scratch.-/
lemma tapeBuilderStep_wire_le (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hWrite : snapshot.write.bound ≤ b.circuit.gates)
    (i : Fin (M.tapeLength n)) :
    let result := tapeBuilderStep (M := M) (n := n) (sc := sc)
        (snapshot := snapshot) (b := b) (hWrite := hWrite) i
    result.snd.snd.bound ≤ result.fst.circuit.gates := by
  classical
  -- Expand the helper and expose the intermediate definitions.
  unfold tapeBuilderStep
  set headWire := b.liftBase (sc.head i)
  set tapeWire := b.liftBase (sc.tape i)
  set writeWire := snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite
  set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
    (b := b) headWire writeWire
  let headLift := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := b) (op := StraightOp.and headWire writeWire) headWire
  let tapeLift := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := b) (op := StraightOp.and headWire writeWire) tapeWire
  set notResult := StraightLineCircuit.EvalBuilder.appendNotFin
    (b := andResult.fst) headLift
  let tapeLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := andResult.fst) (op := StraightOp.not headLift) tapeLift
  set keepResult := StraightLineCircuit.EvalBuilder.appendAndFin
    (b := notResult.fst) notResult.snd tapeLift'
  let andLift'' := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := notResult.fst)
    (op := StraightOp.and notResult.snd tapeLift')
    (StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) andResult.snd)
  set final := StraightLineCircuit.EvalBuilder.appendOrFin
    (b := keepResult.fst) andLift'' keepResult.snd
  -- The returned wire is produced via `Wire.ofFin`, hence its bound coincides
  -- with the gate count of the ambient builder.
  have := StraightLineCircuit.Wire.ofFin_bound (n := n)
    (g := final.fst.circuit.gates) final.snd
  simpa [result, headWire, tapeWire, writeWire, andResult, headLift, tapeLift,
    tapeLift', keepResult, andLift'', notResult, final]
    using (le_of_eq this)

/--
The single-cell tape gadget preserves the value of any pre-existing wire.
This general statement will let us reuse the lemma for both the aggregated
write bit and all intermediate invariants tracked by the tape snapshot.
-/
lemma tapeBuilderStep_preserves_eval (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hWrite : snapshot.write.bound ≤ b.circuit.gates)
    (i : Fin (M.tapeLength n))
    (w : StraightLineCircuit.Wire n)
    (hw : w.bound ≤ b.circuit.gates)
    (x : Point n) :
    let step := tapeBuilderStep (M := M) (n := n) (sc := sc)
        (snapshot := snapshot) (b := b) (hWrite := hWrite) i
    StraightLineCircuit.evalWire (C := step.fst.circuit) (x := x)
        (w.toFin (n := n) (g := step.fst.circuit.gates)
          (Nat.le_trans hw (by
            have heq := tapeBuilderStep_gate_eq (M := M) (n := n) (sc := sc)
              (snapshot := snapshot) (b := b) (hWrite := hWrite) (i := i)
            have := Nat.le_add_right b.circuit.gates 4
            simpa [step, tapeBuilderStep, heq, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using this))) =
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
        (w.toFin (n := n) (g := b.circuit.gates) hw) := by
  classical
  -- Expand the helper and record the intermediate builders appearing in the
  -- construction.
  unfold tapeBuilderStep
  set headWire := b.liftBase (sc.head i)
  set tapeWire := b.liftBase (sc.tape i)
  set writeWire := snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite
  set andResult := StraightLineCircuit.EvalBuilder.appendAndFin
    (b := b) headWire writeWire
  have hMono₁ : b.circuit.gates ≤ andResult.fst.circuit.gates := by
    have := Nat.le_succ b.circuit.gates
    simpa [StraightLineCircuit.EvalBuilder.appendAndFin,
      StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
      StraightLineCircuit.snoc, Nat.succ_eq_add_one] using this
  have hw₁ : w.bound ≤ andResult.fst.circuit.gates := Nat.le_trans hw hMono₁
  let headLift := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := b) (op := StraightOp.and headWire writeWire) headWire
  let tapeLift := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := b) (op := StraightOp.and headWire writeWire) tapeWire
  set notResult := StraightLineCircuit.EvalBuilder.appendNotFin
    (b := andResult.fst) headLift
  have hMono₂ : andResult.fst.circuit.gates ≤ notResult.fst.circuit.gates := by
    have := Nat.le_succ andResult.fst.circuit.gates
    simpa [StraightLineCircuit.EvalBuilder.appendNotFin,
      StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
      StraightLineCircuit.snoc, Nat.succ_eq_add_one] using this
  have hw₂ : w.bound ≤ notResult.fst.circuit.gates :=
    Nat.le_trans hw₁ hMono₂
  let tapeLift' := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := andResult.fst) (op := StraightOp.not headLift) tapeLift
  set keepResult := StraightLineCircuit.EvalBuilder.appendAndFin
    (b := notResult.fst) notResult.snd tapeLift'
  have hMono₃ : notResult.fst.circuit.gates ≤ keepResult.fst.circuit.gates := by
    have := Nat.le_succ notResult.fst.circuit.gates
    simpa [StraightLineCircuit.EvalBuilder.appendAndFin,
      StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
      StraightLineCircuit.snoc, Nat.succ_eq_add_one] using this
  have hw₃ : w.bound ≤ keepResult.fst.circuit.gates :=
    Nat.le_trans hw₂ hMono₃
  let andLift'' := StraightLineCircuit.EvalBuilder.appendFin_lift
    (b := notResult.fst)
    (op := StraightOp.and notResult.snd tapeLift')
    (StraightLineCircuit.EvalBuilder.appendFin_lift
      (b := andResult.fst) (op := StraightOp.not headLift) andResult.snd)
  set final := StraightLineCircuit.EvalBuilder.appendOrFin
    (b := keepResult.fst) andLift'' keepResult.snd
  have hMono₄ : keepResult.fst.circuit.gates ≤ final.fst.circuit.gates := by
    have := Nat.le_succ keepResult.fst.circuit.gates
    simpa [StraightLineCircuit.EvalBuilder.appendOrFin,
      StraightLineCircuit.EvalBuilder.appendFin_gate_eq,
      StraightLineCircuit.snoc, Nat.succ_eq_add_one] using this
  have hw₄ : w.bound ≤ final.fst.circuit.gates := Nat.le_trans hw₃ hMono₄
  -- Apply the preservation lemma for each appended gate in sequence.
  have h₁ := StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
    (b := b) (op := StraightOp.and headWire writeWire)
    (w := w) (hw := hw) (x := x)
  have h₂ := StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
    (b := andResult.fst) (op := StraightOp.not headLift)
    (w := w) (hw := hw₁) (x := x)
  have h₃ := StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
    (b := notResult.fst)
    (op := StraightOp.and notResult.snd tapeLift')
    (w := w) (hw := hw₂) (x := x)
  have h₄ := StraightLineCircuit.EvalBuilder.appendFin_evalWire_preserved
    (b := keepResult.fst)
    (op := StraightOp.or andLift'' keepResult.snd)
    (w := w) (hw := hw₃) (x := x)
  -- Assemble the chain of equalities.
  have hchain := h₄.trans (h₃.trans (h₂.trans h₁)).symm
  -- Simplify the coercions introduced by the successive lifts.
  simpa [step, tapeBuilderStep, headWire, tapeWire, writeWire, andResult,
    headLift, tapeLift, tapeLift', keepResult, andLift'', notResult, final,
    StraightLineCircuit.Wire.toFin_ofFin] using hchain

lemma tapeBuilderStep_preserves_write_eval (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc)
    (b : StraightLineCircuit.EvalBuilder n sc.circuit)
    (hWrite : snapshot.write.bound ≤ b.circuit.gates)
    (i : Fin (M.tapeLength n))
    (x : Point n) :
    let step := tapeBuilderStep (M := M) (n := n) (sc := sc)
        (snapshot := snapshot) (b := b) (hWrite := hWrite) i
    StraightLineCircuit.evalWire (C := step.fst.circuit) (x := x)
        (snapshot.write.toFin (n := n) (g := step.fst.circuit.gates)
          (Nat.le_trans hWrite (by
            have heq := tapeBuilderStep_gate_eq (M := M) (n := n) (sc := sc)
              (snapshot := snapshot) (b := b) (hWrite := hWrite) (i := i)
            have := Nat.le_add_right b.circuit.gates 4
            simpa [step, tapeBuilderStep, heq, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using this))) =
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
        (snapshot.write.toFin (n := n) (g := b.circuit.gates) hWrite) :=
  by
    classical
    -- Immediate corollary of the general preservation lemma.
    have := tapeBuilderStep_preserves_eval (M := M) (n := n) (sc := sc)
      (snapshot := snapshot) (b := b) (hWrite := hWrite)
      (i := i) (w := snapshot.write) (hw := hWrite) (x := x)
    simpa [step, tapeBuilderStep]
      using this

/--
Recursive helper constructing the list of updated tape wires.  The auxiliary
sigma-packages keep track of the extended builder together with the fact that
all previously recorded wires remain in range.-/
def tapeSnapshotAux (sc : StraightConfig M n)
    (snapshot : WriteSnapshot (M := M) (n := n) sc) :
    ∀ (indices : List (Fin (M.tapeLength n)))
      (b : StraightLineCircuit.EvalBuilder n sc.circuit)
      (hWrite : snapshot.write.bound ≤ b.circuit.gates),
        Σ' (b' : StraightLineCircuit.EvalBuilder n sc.circuit),
            (snapshot.write.bound ≤ b'.circuit.gates) ×
            (b.circuit.gates ≤ b'.circuit.gates) ×
            { tapes : List (Fin (M.tapeLength n) × StraightLineCircuit.Wire n) //
                ∀ {i : Fin (M.tapeLength n)} {w : StraightLineCircuit.Wire n},
                  (i, w) ∈ tapes → w.bound ≤ b'.circuit.gates }
  | [], b, hWrite =>
      ⟨ b, hWrite, le_rfl, ⟨[], by intro i w h; cases h⟩ ⟩
  | i :: rest, b, hWrite =>
      by
        -- Process the current cell via `tapeBuilderStep`.
        have step := tapeBuilderStep (M := M) (n := n) (sc := sc)
          (snapshot := snapshot) (b := b) (hWrite := hWrite) i
        obtain ⟨bNext, hWriteNext, wire⟩ := step
        have hMonoStep : b.circuit.gates ≤ bNext.circuit.gates := by
          have heq := tapeBuilderStep_gate_eq (M := M) (n := n) (sc := sc)
            (snapshot := snapshot) (b := b) (hWrite := hWrite) (i := i)
          have := Nat.le_add_right b.circuit.gates 4
          simpa [step, tapeBuilderStep, heq, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using this
        have hWireBound : wire.bound ≤ bNext.circuit.gates := by
          simpa [step] using tapeBuilderStep_wire_le (M := M) (n := n) (sc := sc)
            (snapshot := snapshot) (b := b) (hWrite := hWrite) (i := i)
        -- Recurse on the remaining indices.
        obtain ⟨bRest, hWriteRest, hMonoRest, restList⟩ :=
          tapeSnapshotAux (M := M) (n := n) (sc := sc) (snapshot := snapshot)
            rest bNext hWriteNext
        refine ⟨ bRest
               , hWriteRest
               , Nat.le_trans hMonoStep hMonoRest
               , ⟨ (i, wire) :: restList.val, ?_ ⟩ ⟩
        intro j w hmem
        have hmem' := List.mem_cons.1 hmem
        cases hmem' with
        | inl hhead =>
            cases hhead with
            | rfl =>
                exact Nat.le_trans hWireBound hMonoRest
        | inr htail =>
            exact restList.property htail

end StraightConfig

end Complexity

end PsubsetPpoly
end Facts
