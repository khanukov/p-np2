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

namespace List

lemma any_map {α β} (l : List α) (f : α → β) (p : β → Bool) :
    List.any (l.map f) p = List.any l (fun a => p (f a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [List.map, List.any, ih]

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

lemma pair_mem_stateSymbolPairs (M : TM) (q : M.state) (b : Bool) :
    (q, b) ∈ stateSymbolPairs M := by
  classical
  refine List.mem_bind.2 ?_
  refine ⟨q, state_mem_stateList (M := M) q, ?_⟩
  cases b <;> simp

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

end ConfigCircuits

end Complexity

