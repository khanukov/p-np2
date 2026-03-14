import Complexity.PsubsetPpolyInternal.TuringEncoding
import Complexity.PsubsetPpolyInternal.CircuitTree
import Complexity.PsubsetPpolyInternal.StraightLine
import Complexity.PsubsetPpolyInternal.StraightLineSemantics
import Complexity.PsubsetPpolyInternal.StraightLineBuilder
import Complexity.PsubsetPpolyInternal.TreeToStraight
import Complexity.PpolyDAG_from_StraightLine
import Mathlib.Tactic

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace Simulation

open Boolcube
open TM
open Pnp3.Complexity.StraightLineAdapter

/-- Cardinality of TM control states (compile-time constant for fixed `M`). -/
def stateCard (M : TM) : Nat := Fintype.card M.state

/-- Canonical equivalence between machine states and `Fin (stateCard M)`. -/
noncomputable def stateEquiv (M : TM) : M.state ≃ Fin (stateCard M) :=
  Fintype.equivFin _

/-- Canonical index of a state in the finite enumeration. -/
noncomputable def stateIndex (M : TM) (q : M.state) : Fin (stateCard M) :=
  stateEquiv M q

/-- Enumerate all machine states as a list. -/
noncomputable def stateList (M : TM) : List M.state :=
  (Finset.univ : Finset M.state).toList

/-- Expand a state list into all `(state, bit)` pairs. -/
def stateSymbolPairsFrom {M : TM} (l : List M.state) : List (M.state × Bool) :=
  l.foldr (fun q acc => (q, false) :: (q, true) :: acc) []

/-- Enumerate all pairs `(q,b)` with `q : state` and `b ∈ {false,true}`. -/
noncomputable def stateSymbolPairs (M : TM) : List (M.state × Bool) :=
  stateSymbolPairsFrom (stateList M)

lemma state_mem_stateList (M : TM) (q : M.state) : q ∈ stateList M := by
  classical
  have : q ∈ (Finset.univ : Finset M.state) := by simpa using (Finset.mem_universe q)
  simpa [stateList] using this

lemma length_stateList (M : TM) : (stateList M).length = stateCard M := by
  classical
  have := Finset.length_toList (Finset.univ : Finset M.state)
  simpa [stateList, stateCard] using this

lemma pair_mem_stateSymbolPairsFrom_of_mem {M : TM}
    (q : M.state) (b : Bool) :
    ∀ {l : List M.state}, q ∈ l → (q, b) ∈ stateSymbolPairsFrom l := by
  intro l h
  induction l with
  | nil =>
      cases h
  | cons a t ih =>
      simp at h
      cases h with
      | inl hqa =>
          subst hqa
          cases b <;> simp [stateSymbolPairsFrom]
      | inr hqt =>
          have ht : (q, b) ∈ stateSymbolPairsFrom t := ih hqt
          cases b
          · simpa [stateSymbolPairsFrom] using (Or.inr ht :
              q = a ∨ (q, false) ∈ stateSymbolPairsFrom t)
          · simpa [stateSymbolPairsFrom] using (Or.inr ht :
              q = a ∨ (q, true) ∈ stateSymbolPairsFrom t)

lemma pair_mem_stateSymbolPairs (M : TM) (q : M.state) (b : Bool) :
    (q, b) ∈ stateSymbolPairs M := by
  exact pair_mem_stateSymbolPairsFrom_of_mem q b (state_mem_stateList M q)

lemma length_stateSymbolPairsFrom {M : TM} :
    ∀ (l : List M.state), (stateSymbolPairsFrom l).length = 2 * l.length := by
  intro l
  induction l with
  | nil =>
      simp [stateSymbolPairsFrom]
  | cons a t ih =>
      have hlen : (stateSymbolPairsFrom (a :: t)).length = (stateSymbolPairsFrom t).length + 2 := by
        simp [stateSymbolPairsFrom]
      calc
        (stateSymbolPairsFrom (a :: t)).length = (stateSymbolPairsFrom t).length + 2 := hlen
        _ = 2 * t.length + 2 := by rw [ih]
        _ = 2 * (List.length (a :: t)) := by
              simp
              omega

lemma length_stateSymbolPairs (M : TM) :
    (stateSymbolPairs M).length = 2 * stateCard M := by
  simpa [stateSymbolPairs, length_stateList] using
    (length_stateSymbolPairsFrom (l := stateList M))

/-- One-hot indicator of the head position in a configuration. -/
def headIndicator {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) : Fin (M.tapeLength n) → Bool :=
  fun i => decide (c.head = i)

/-- One-hot indicator of the control state in a configuration. -/
def stateIndicator (M : TM) {n : Nat}
    (c : TM.Configuration (M := M) n) : M.state → Bool :=
  fun i => decide (c.state = i)

lemma headIndicator_true_iff {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) (i : Fin (M.tapeLength n)) :
    headIndicator c i = true ↔ c.head = i := by
  unfold headIndicator
  by_cases h : c.head = i <;> simp [h]

lemma stateIndicator_true_iff {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) (q : M.state) :
    stateIndicator M c q = true ↔ c.state = q := by
  unfold stateIndicator
  by_cases h : c.state = q <;> simp [h]

lemma headIndicator_ne {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) {i : Fin (M.tapeLength n)}
    (h : i ≠ c.head) :
    headIndicator c i = false := by
  unfold headIndicator
  by_cases h' : c.head = i
  · have : i = c.head := h'.symm
    exact (h this).elim
  · simp [h']

lemma stateIndicator_ne {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) {q : M.state}
    (h : q ≠ c.state) :
    stateIndicator M c q = false := by
  unfold stateIndicator
  by_cases h' : c.state = q
  · have : q = c.state := h'.symm
    exact (h this).elim
  · simp [h']

lemma headIndicator_self {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) :
    headIndicator c c.head = true := by
  simpa using (headIndicator_true_iff (c := c) (i := c.head))

lemma stateIndicator_self {M : TM} {n : Nat}
    (c : TM.Configuration (M := M) n) :
    stateIndicator M c c.state = true := by
  simpa using (stateIndicator_true_iff (M := M) (c := c) (q := c.state))

/-- Enumerate tape indices as `Fin` range. -/
def tapeIndexList (M : TM) (n : Nat) : List (Fin (M.tapeLength n)) :=
  List.finRange (M.tapeLength n)

namespace Boolcube.Circuit

/-- Big disjunction over a list of circuits. -/
noncomputable def bigOr {n : Nat} : List (Circuit n) → Circuit n
  | [] => Circuit.const false
  | c :: cs => Circuit.or c (bigOr cs)

noncomputable def bigAnd {n : Nat} : List (Circuit n) → Circuit n
  | [] => Circuit.const true
  | c :: cs => Circuit.and c (bigAnd cs)

@[simp] lemma eval_bigOr_any {n : Nat} (cs : List (Circuit n)) (x : Point n) :
    Circuit.eval (bigOr cs) x = List.any cs (fun c => Circuit.eval c x) := by
  induction cs with
  | nil =>
      simp [bigOr, Circuit.eval]
  | cons c cs ih =>
      simp [bigOr, Circuit.eval, ih]

@[simp] lemma eval_bigAnd_all {n : Nat} (cs : List (Circuit n)) (x : Point n) :
    Circuit.eval (bigAnd cs) x = List.all cs (fun c => Circuit.eval c x) := by
  induction cs with
  | nil =>
      simp [bigAnd, Circuit.eval]
  | cons c cs ih =>
      simp [bigAnd, Circuit.eval, ih]

noncomputable def literal {n : Nat} (i : Fin n) (b : Bool) : Circuit n :=
  if b then Circuit.var i else Circuit.not (Circuit.var i)

noncomputable def minterm {n : Nat} (a : Point n) : Circuit n :=
  bigAnd ((List.finRange n).map fun i => literal i (a i))

lemma eval_minterm_self {n : Nat} (a : Point n) :
    Circuit.eval (minterm a) a = true := by
  simp [minterm, eval_bigAnd_all]
  intro i
  cases hai : a i <;> simp [literal, Circuit.eval, hai]

lemma eval_literal_ne {n : Nat} (a x : Point n) (i : Fin n) (h : x i ≠ a i) :
    Circuit.eval (literal i (a i)) x = false := by
  cases hxi : x i <;> cases hai : a i <;> simp [literal, Circuit.eval, hxi, hai] at h ⊢

lemma eval_minterm_ne {n : Nat} (a x : Point n) (h : x ≠ a) :
    Circuit.eval (minterm a) x = false := by
  have hdiff : ∃ i : Fin n, x i ≠ a i := by
    by_contra hNo
    apply h
    funext i
    exact by
      by_contra hne
      exact hNo ⟨i, hne⟩
  rcases hdiff with ⟨i0, hi0⟩
  have hmemI : i0 ∈ List.finRange n := List.mem_finRange _
  have hmemLit : literal i0 (a i0) ∈ (List.finRange n).map (fun i => literal i (a i)) := by
    exact List.mem_map.mpr ⟨i0, hmemI, rfl⟩
  have hLitFalse : Circuit.eval (literal i0 (a i0)) x = false :=
    eval_literal_ne a x i0 hi0
  have hAllFalse :
      List.all ((List.finRange n).map (fun i => literal i (a i)))
        (fun c => Circuit.eval c x) = false := by
    apply (List.all_eq_false).2
    exact ⟨literal i0 (a i0), hmemLit, by simpa [hLitFalse]⟩
  simpa [minterm, eval_bigAnd_all] using hAllFalse

lemma eq_of_eval_minterm_true {n : Nat} (a x : Point n)
    (h : Circuit.eval (minterm a) x = true) : x = a := by
  by_contra hne
  have : Circuit.eval (minterm a) x = false := eval_minterm_ne a x hne
  simp [h] at this

noncomputable def satisfyingPoints {n : Nat} (f : Point n → Bool) : List (Point n) :=
  (Finset.filter (fun a => f a = true) (Finset.univ : Finset (Point n))).toList

lemma mem_satisfyingPoints_iff {n : Nat} (f : Point n → Bool) (x : Point n) :
    x ∈ satisfyingPoints f ↔ f x = true := by
  classical
  unfold satisfyingPoints
  simp

noncomputable def truthTableCircuit {n : Nat} (f : Point n → Bool) : Circuit n :=
  bigOr ((satisfyingPoints f).map minterm)

lemma eval_truthTableCircuit {n : Nat} (f : Point n → Bool) (x : Point n) :
    Circuit.eval (truthTableCircuit f) x = f x := by
  classical
  unfold truthTableCircuit
  rw [eval_bigOr_any]
  by_cases hfx : f x = true
  · have hxmem : x ∈ satisfyingPoints f := (mem_satisfyingPoints_iff f x).2 hfx
    have hAny :
        List.any ((satisfyingPoints f).map minterm)
          (fun c => Circuit.eval c x) = true := by
      apply (List.any_eq_true).2
      refine ⟨minterm x, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨x, hxmem, rfl⟩
      · simpa using eval_minterm_self x
    simpa [hfx] using hAny
  · have hAnyFalse :
      List.any ((satisfyingPoints f).map minterm)
        (fun c => Circuit.eval c x) = false := by
      apply (List.any_eq_false).2
      intro c hc
      rcases List.mem_map.mp hc with ⟨a, ha, rfl⟩
      have hfa : f a = true := (mem_satisfyingPoints_iff f a).1 ha
      intro htrue
      have hEq : x = a := eq_of_eval_minterm_true a x htrue
      subst hEq
      exact hfx hfa
    simpa [hfx] using hAnyFalse

end Boolcube.Circuit

/-- Tree-circuit encoding of a machine configuration. -/
structure ConfigCircuits (M : TM) (n : Nat) where
  tape : Fin (M.tapeLength n) → Circuit n
  head : Fin (M.tapeLength n) → Circuit n
  state : M.state → Circuit n

namespace ConfigCircuits

variable {M : TM} {n : Nat}

/-- Semantics of tape circuits. -/
noncomputable def evalTape (cc : ConfigCircuits M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool := fun i => Circuit.eval (cc.tape i) x

/-- Semantics of head circuits. -/
noncomputable def evalHead (cc : ConfigCircuits M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool := fun i => Circuit.eval (cc.head i) x

/-- Semantics of state circuits. -/
noncomputable def evalState (cc : ConfigCircuits M n) (x : Point n) :
    M.state → Bool := fun i => Circuit.eval (cc.state i) x

/-- Correctness spec against a semantic configuration map. -/
structure Spec (cc : ConfigCircuits M n)
    (f : Point n → TM.Configuration (M := M) n) : Prop where
  tape_eq : ∀ x i, evalTape cc x i = (f x).tape i
  head_eq : ∀ x i, evalHead cc x i = headIndicator (f x) i
  state_eq : ∀ x i, evalState cc x i = stateIndicator M (f x) i

/-- Initial circuits for machine `M` on inputs of length `n`. -/
noncomputable def initial (M : TM) (n : Nat) : ConfigCircuits M n where
  tape := fun i =>
    if h : (i : Nat) < n then
      Circuit.var ⟨i, h⟩
    else
      Circuit.const false
  head := fun i =>
    if h : i = ⟨0, by
          have : (0 : Nat) < n + M.runTime n + 1 := Nat.succ_pos _
          simpa [TM.tapeLength] using this⟩ then
      Circuit.const true
    else
      Circuit.const false
  state := fun i =>
    if h : i = M.start then
      Circuit.const true
    else
      Circuit.const false

lemma initial_spec (M : TM) (n : Nat) :
    Spec (cc := initial M n) (f := fun x => M.initialConfig x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    unfold evalTape initial
    by_cases hi : (i : Nat) < n
    · simp [TM.initialConfig, hi, Boolcube.Circuit.eval]
    · simp [TM.initialConfig, hi, Boolcube.Circuit.eval]
  · intro x i
    unfold evalHead initial
    let i0 : Fin (M.tapeLength n) := ⟨0, by
      have : (0 : Nat) < n + M.runTime n + 1 := Nat.succ_pos _
      simpa [TM.tapeLength] using this⟩
    change (if i = i0 then Circuit.const true else Circuit.const false).eval x = decide (i0 = i)
    by_cases h0 : i = i0
    · subst h0
      simp [Boolcube.Circuit.eval, i0]
    · have h0' : ¬ i0 = i := by exact fun h => h0 h.symm
      simp [Boolcube.Circuit.eval, h0, h0']
  · intro x q
    unfold evalState initial
    by_cases hs : q = M.start
    · simp [TM.initialConfig, stateIndicator, hs, Boolcube.Circuit.eval]
    · have hs' : ¬ M.start = q := by exact fun h => hs h.symm
      simp [TM.initialConfig, stateIndicator, hs, hs', Boolcube.Circuit.eval]

/-- Decode a head position from one-hot head wires (defaulting to index `0`). -/
noncomputable def decodeHead (cc : ConfigCircuits M n) (x : Point n) :
    Fin (M.tapeLength n) :=
  if h : ∃ i : Fin (M.tapeLength n), evalHead cc x i = true then
    Classical.choose h
  else
    ⟨0, by simpa [TM.tapeLength] using Nat.succ_pos (n + M.runTime n)⟩

/-- Decode a state from one-hot state wires (defaulting to `M.start`). -/
noncomputable def decodeState (cc : ConfigCircuits M n) (x : Point n) :
    M.state :=
  if h : ∃ q : M.state, evalState cc x q = true then
    Classical.choose h
  else
    M.start

/-- Semantic configuration induced by circuit outputs. -/
noncomputable def decodedConfig (cc : ConfigCircuits M n) (x : Point n) :
    TM.Configuration (M := M) n where
  state := decodeState cc x
  head := decodeHead cc x
  tape := evalTape cc x

lemma decodeHead_eq_of_spec
    (cc : ConfigCircuits M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hcc : Spec (cc := cc) (f := f))
    (x : Point n) :
    decodeHead cc x = (f x).head := by
  have hExists : ∃ i : Fin (M.tapeLength n), evalHead cc x i = true := by
    refine ⟨(f x).head, ?_⟩
    simpa [hcc.head_eq x (f x).head] using (headIndicator_self (c := f x))
  unfold decodeHead
  simp [hExists]
  let i0 : Fin (M.tapeLength n) := Classical.choose hExists
  have hi0 : evalHead cc x i0 = true := Classical.choose_spec hExists
  have hInd : headIndicator (f x) i0 = true := by
    simpa [hcc.head_eq x i0] using hi0
  have hEq : (f x).head = i0 := (headIndicator_true_iff (c := f x) i0).1 hInd
  exact hEq.symm

lemma decodeState_eq_of_spec
    (cc : ConfigCircuits M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hcc : Spec (cc := cc) (f := f))
    (x : Point n) :
    decodeState cc x = (f x).state := by
  have hExists : ∃ q : M.state, evalState cc x q = true := by
    refine ⟨(f x).state, ?_⟩
    simpa [hcc.state_eq x (f x).state] using (stateIndicator_self (M := M) (c := f x))
  unfold decodeState
  simp [hExists]
  let q0 : M.state := Classical.choose hExists
  have hq0 : evalState cc x q0 = true := Classical.choose_spec hExists
  have hInd : stateIndicator M (f x) q0 = true := by
    simpa [hcc.state_eq x q0] using hq0
  have hEq : (f x).state = q0 := (stateIndicator_true_iff (M := M) (c := f x) q0).1 hInd
  exact hEq.symm

lemma decodedConfig_eq_of_spec
    (cc : ConfigCircuits M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hcc : Spec (cc := cc) (f := f))
    (x : Point n) :
    decodedConfig cc x = f x := by
  cases hf : f x with
  | mk st hd tp =>
      have hst : decodeState cc x = st := by
        simpa [hf] using decodeState_eq_of_spec (cc := cc) (f := f) hcc x
      have hhd : decodeHead cc x = hd := by
        simpa [hf] using decodeHead_eq_of_spec (cc := cc) (f := f) hcc x
      have htp : evalTape cc x = tp := by
        funext i
        simpa [hf] using hcc.tape_eq x i
      change
        ({ state := decodeState cc x, head := decodeHead cc x, tape := evalTape cc x } :
          TM.Configuration (M := M) n) =
        { state := st, head := hd, tape := tp }
      simpa [hst, hhd, htp]

/-- Next-step tape bit for cell `i` synthesized from the decoded transition. -/
noncomputable def nextTapeCircuit (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) (i : Fin (M.tapeLength n)) : Circuit n :=
  Boolcube.Circuit.truthTableCircuit (fun x =>
    (TM.stepConfig (M := M) (decodedConfig cc x)).tape i)

/-- Next-step head indicator at index `j`. -/
noncomputable def nextHeadCircuit (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) (j : Fin (M.tapeLength n)) : Circuit n :=
  Boolcube.Circuit.truthTableCircuit (fun x =>
    headIndicator (TM.stepConfig (M := M) (decodedConfig cc x)) j)

/-- Next-step state indicator for control state `q`. -/
noncomputable def nextStateCircuit (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) (q : M.state) : Circuit n :=
  Boolcube.Circuit.truthTableCircuit (fun x =>
    stateIndicator M (TM.stepConfig (M := M) (decodedConfig cc x)) q)

noncomputable def stepCircuitsTruthTable (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : ConfigCircuits M n where
  tape := fun i => nextTapeCircuit M cc i
  head := fun j => nextHeadCircuit M cc j
  state := fun q => nextStateCircuit M cc q

/--
Linear-step switch-point for `ConfigCircuits`.

Currently aliased to the truth-table implementation and intended to be replaced
by the constructive DAG-preserving assembly.
-/
noncomputable abbrev stepCircuitsLinear (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : ConfigCircuits M n :=
  stepCircuitsTruthTable M cc

/--
Current `ConfigCircuits` one-step implementation.

Kept as a stable name for downstream code; this alias currently points to the
truth-table implementation and is the designated switch-point for the upcoming
constructive (DAG-preserving) refactor.
-/
noncomputable abbrev stepCircuits (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : ConfigCircuits M n :=
  stepCircuitsLinear M cc

lemma step_spec
    (M : TM) {n : Nat}
    {cc : ConfigCircuits M n}
    {f : Point n → TM.Configuration (M := M) n}
    (hcc : Spec (cc := cc) (f := f)) :
    Spec (cc := stepCircuits M cc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    have hdec : decodedConfig cc x = f x := decodedConfig_eq_of_spec (cc := cc) (f := f) hcc x
    simpa [stepCircuits, nextTapeCircuit, hdec] using
      (Boolcube.Circuit.eval_truthTableCircuit
        (f := fun x => (TM.stepConfig (M := M) (decodedConfig cc x)).tape i) x)
  · intro x j
    have hdec : decodedConfig cc x = f x := decodedConfig_eq_of_spec (cc := cc) (f := f) hcc x
    simpa [stepCircuits, nextHeadCircuit, hdec] using
      (Boolcube.Circuit.eval_truthTableCircuit
        (f := fun x => headIndicator (TM.stepConfig (M := M) (decodedConfig cc x)) j) x)
  · intro x q
    have hdec : decodedConfig cc x = f x := decodedConfig_eq_of_spec (cc := cc) (f := f) hcc x
    simpa [stepCircuits, nextStateCircuit, hdec] using
      (Boolcube.Circuit.eval_truthTableCircuit
        (f := fun x => stateIndicator M (TM.stepConfig (M := M) (decodedConfig cc x)) q) x)

lemma iterate_spec
    (M : TM) {n : Nat}
    {cc : ConfigCircuits M n}
    {f : Point n → TM.Configuration (M := M) n}
    (hcc : Spec (cc := cc) (f := f)) :
    ∀ t,
      Spec (cc := Nat.iterate (stepCircuits M) t cc)
        (f := fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x)) := by
  intro t
  induction t with
  | zero =>
      simpa using hcc
  | succ t ih =>
      simpa [Function.iterate_succ_apply', Function.comp] using
        (step_spec (M := M) (cc := Nat.iterate (stepCircuits M) t cc)
          (f := fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x)) ih)

noncomputable def runtimeCircuits (M : TM) (n : Nat) : ConfigCircuits M n :=
  Nat.iterate (stepCircuits M) (M.runTime n) (initial M n)

lemma runtime_spec (M : TM) (n : Nat) :
    Spec (cc := runtimeCircuits M n) (f := fun x => M.run (n := n) x) := by
  have hIter := iterate_spec (M := M) (cc := initial M n)
    (f := fun x => M.initialConfig x) (initial_spec M n) (M.runTime n)
  simpa [runtimeCircuits, TM.run, TM.runConfig] using hIter

/-- Circuit returning the bit currently scanned by the head. -/
noncomputable def symbol (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : Circuit n :=
  Boolcube.Circuit.bigOr ((tapeIndexList M n).map fun i =>
    Circuit.and (cc.head i) (cc.tape i))

/-- Guard for scanned symbol value `b`. -/
noncomputable def guardSymbol (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) (b : Bool) : Circuit n :=
  if b then symbol M cc else Circuit.not (symbol M cc)

/-- Branch indicator for the transition branch `(q,b)`. -/
noncomputable def branchIndicator (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) (qs : M.state × Bool) : Circuit n :=
  Circuit.and (cc.state qs.1) (guardSymbol M cc qs.2)

/-- One transition-branch contribution to the written bit. -/
noncomputable def writeTerm (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) (qs : M.state × Bool) : Circuit n :=
  match M.step qs.1 qs.2 with
  | ⟨_, write, _⟩ =>
      if write then branchIndicator M cc qs else Circuit.const false

/-- Circuit computing the bit written at the current head position. -/
noncomputable def writeBit (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : Circuit n :=
  Boolcube.Circuit.bigOr ((stateSymbolPairs M).map fun qs =>
    writeTerm M cc qs)

/-- Acceptance output extracted from the indicator wire of `M.accept`. -/
noncomputable def acceptCircuit (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : Circuit n :=
  cc.state M.accept

lemma acceptCircuit_spec_of_spec (M : TM) {n : Nat}
    (cc : ConfigCircuits M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hcc : Spec (cc := cc) (f := f))
    (x : Point n) :
    Circuit.eval (acceptCircuit M cc) x = decide ((f x).state = M.accept) := by
  simpa [acceptCircuit, stateIndicator] using hcc.state_eq x M.accept

lemma acceptCircuit_spec_of_runSpec (M : TM) {n : Nat}
    (cc : ConfigCircuits M n)
    (hRun : Spec (cc := cc) (f := fun x => M.run (n := n) x))
    (x : Point n) :
    Circuit.eval (acceptCircuit M cc) x = TM.accepts (M := M) (n := n) x := by
  simpa [TM.accepts] using acceptCircuit_spec_of_spec (M := M)
    (cc := cc) (f := fun x => M.run (n := n) x) hRun x

end ConfigCircuits

/--
Straight-line representation of configuration circuits:
a shared gate pool plus wire selectors for tape/head/state observables.
-/
structure StraightConfig (M : TM) (n : Nat) where
  circuit : StraightLineCircuit n
  tape : Fin (M.tapeLength n) → Fin (n + circuit.gates)
  head : Fin (M.tapeLength n) → Fin (n + circuit.gates)
  state : M.state → Fin (n + circuit.gates)

namespace StraightConfig

variable {M : TM} {n : Nat}

/-- Builder aliases used by the upcoming nontrivial straight-step construction. -/
abbrev BuildCtx (n : Nat) := Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx n
abbrev EvalBuildCtx (n : Nat) := Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n

/-- Initial evaluation-aware builder rooted at `sc.circuit`. -/
def startEvalBuilder (sc : StraightConfig M n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n sc.circuit :=
  Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.init sc.circuit

@[simp] lemma startEvalBuilder_circuit (sc : StraightConfig M n) :
    (startEvalBuilder (M := M) (n := n) sc).circuit = sc.circuit := rfl

/--
Builder state carrying a distinguished output wire over a fixed base circuit.

This is the core dependent payload used by append-only straight-line assembly.
-/
structure BuiltWire (base : StraightLineCircuit n) where
  ctx : Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n base
  out : Fin (n + ctx.circuit.gates)

namespace BuiltWire

variable {base : StraightLineCircuit n}

/-- Head index update as a pure function of current index and movement. -/
def moveIndex (i : Fin (M.tapeLength n)) (m : Move) : Fin (M.tapeLength n) :=
  match m with
  | Move.left =>
      if h0 : (i : Nat) = 0 then
        i
      else
        ⟨(i : Nat) - 1, by
          have hlt := i.isLt
          exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
  | Move.stay => i
  | Move.right =>
      if h : (i : Nat) + 1 < M.tapeLength n then
        ⟨(i : Nat) + 1, h⟩
      else
        i

/-- Enumerate all `(head-index, state-symbol)` transition branches. -/
noncomputable def headStateSymbolPairsAux (M : TM) (n : Nat) :
    List (Fin (M.tapeLength n)) → List (Fin (M.tapeLength n) × (M.state × Bool))
  | [] => []
  | i :: t => ((stateSymbolPairs M).map fun qs => (i, qs)) ++ headStateSymbolPairsAux M n t

/-- Enumerate all `(head-index, state-symbol)` transition branches. -/
noncomputable def headStateSymbolPairs (M : TM) (n : Nat) :
    List (Fin (M.tapeLength n) × (M.state × Bool)) :=
  headStateSymbolPairsAux M n (tapeIndexList M n)

lemma pair_mem_headStateSymbolPairsAux_of_mem
    (M : TM) (n : Nat)
    (i : Fin (M.tapeLength n)) (qs : M.state × Bool) :
    ∀ {is : List (Fin (M.tapeLength n))},
      i ∈ is →
      qs ∈ stateSymbolPairs M →
      (i, qs) ∈ headStateSymbolPairsAux M n is := by
  intro is hi hqs
  induction is with
  | nil =>
      cases hi
  | cons i0 is ih =>
      have hiCases : i = i0 ∨ i ∈ is := by simpa using hi
      rcases hiCases with rfl | hiTail
      · simp [headStateSymbolPairsAux, hqs]
      · have hTail :
          (i, qs) ∈ headStateSymbolPairsAux M n is :=
            ih hiTail
        simpa [headStateSymbolPairsAux] using (Or.inr hTail)

lemma pair_mem_headStateSymbolPairs
    (M : TM) (n : Nat)
    (i : Fin (M.tapeLength n)) (q : M.state) (b : Bool) :
    (i, (q, b)) ∈ headStateSymbolPairs M n := by
  have hi : i ∈ tapeIndexList M n := by
    simpa [tapeIndexList] using (List.mem_finRange i)
  have hqs : (q, b) ∈ stateSymbolPairs M :=
    pair_mem_stateSymbolPairs M q b
  simpa [headStateSymbolPairs] using
    pair_mem_headStateSymbolPairsAux_of_mem (M := M) (n := n) i (q, b) hi hqs

/-- Base gate-count monotonicity inherited from the builder context. -/
lemma base_le (bw : BuiltWire (n := n) base) :
    base.gates ≤ bw.ctx.circuit.gates :=
  bw.ctx.ctx.base_le

@[simp] lemma evalWire_liftBase
    (bw : BuiltWire (n := n) base) (x : Boolcube.Point n)
    (i : Fin (n + base.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bw.ctx.circuit) (x := x) (bw.ctx.liftBase i) =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := base) (x := x) i :=
  bw.ctx.eval_liftBase x i

/-- Start from the base circuit and append a constant-`false` wire. -/
noncomputable def initFalse (sc : StraightConfig M n) :
    BuiltWire (n := n) sc.circuit := by
  let r := (startEvalBuilder (M := M) (n := n) sc).appendConst false
  exact ⟨r.1, r.2⟩

/-- Append `not` over the current circuit and track the new output wire. -/
noncomputable def appendConstCurrent (bw : BuiltWire (n := n) base)
    (val : Bool) :
    BuiltWire (n := n) base := by
  let r := bw.ctx.appendConst val
  exact ⟨r.1, r.2⟩

/-- Append `not` over the current circuit and track the new output wire. -/
noncomputable def appendNotCurrent (bw : BuiltWire (n := n) base)
    (w : Fin (n + bw.ctx.circuit.gates)) :
    BuiltWire (n := n) base := by
  let r := bw.ctx.appendNot w
  exact ⟨r.1, r.2⟩

/-- Append `and` over current wires and track the new output wire. -/
noncomputable def appendAndCurrent (bw : BuiltWire (n := n) base)
    (u v : Fin (n + bw.ctx.circuit.gates)) :
    BuiltWire (n := n) base := by
  let r := bw.ctx.appendAnd u v
  exact ⟨r.1, r.2⟩

/-- Append `or` over current wires and track the new output wire. -/
noncomputable def appendOrCurrent (bw : BuiltWire (n := n) base)
    (u v : Fin (n + bw.ctx.circuit.gates)) :
    BuiltWire (n := n) base := by
  let r := bw.ctx.appendOr u v
  exact ⟨r.1, r.2⟩

/--
Append `and` over two base wires (lifted into the current builder context).
-/
noncomputable def appendAndBase (bw : BuiltWire (n := n) base)
    (u v : Fin (n + base.gates)) :
    BuiltWire (n := n) base :=
  appendAndCurrent (bw := bw) (bw.ctx.liftBase u) (bw.ctx.liftBase v)

/--
Append `or` over two base wires (lifted into the current builder context).
-/
noncomputable def appendOrBase (bw : BuiltWire (n := n) base)
    (u v : Fin (n + base.gates)) :
    BuiltWire (n := n) base :=
  appendOrCurrent (bw := bw) (bw.ctx.liftBase u) (bw.ctx.liftBase v)

@[simp] lemma appendConstCurrent_gates {n : Nat} {base : StraightLine.Circuit n}
    (bw : BuiltWire (n := n) base) (val : Bool) :
    (appendConstCurrent (bw := bw) val).ctx.circuit.gates = bw.ctx.circuit.gates + 1 := by
  simp [appendConstCurrent,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendConst,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma appendNotCurrent_gates {n : Nat} {base : StraightLine.Circuit n}
    (bw : BuiltWire (n := n) base) (w : Fin (n + bw.ctx.circuit.gates)) :
    (appendNotCurrent (bw := bw) w).ctx.circuit.gates = bw.ctx.circuit.gates + 1 := by
  simp [appendNotCurrent,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendNot,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma appendAndCurrent_gates {n : Nat} {base : StraightLine.Circuit n}
    (bw : BuiltWire (n := n) base)
    (u v : Fin (n + bw.ctx.circuit.gates)) :
    (appendAndCurrent (bw := bw) u v).ctx.circuit.gates = bw.ctx.circuit.gates + 1 := by
  simp [appendAndCurrent,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendAnd,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma appendOrCurrent_gates {n : Nat} {base : StraightLine.Circuit n}
    (bw : BuiltWire (n := n) base)
    (u v : Fin (n + bw.ctx.circuit.gates)) :
    (appendOrCurrent (bw := bw) u v).ctx.circuit.gates = bw.ctx.circuit.gates + 1 := by
  simp [appendOrCurrent,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOr,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma appendAndBase_gates {n : Nat} {base : StraightLine.Circuit n}
    (bw : BuiltWire (n := n) base) (u v : Fin (n + base.gates)) :
    (appendAndBase (bw := bw) u v).ctx.circuit.gates = bw.ctx.circuit.gates + 1 := by
  simp [appendAndBase]

@[simp] lemma appendOrBase_gates {n : Nat} {base : StraightLine.Circuit n}
    (bw : BuiltWire (n := n) base) (u v : Fin (n + base.gates)) :
    (appendOrBase (bw := bw) u v).ctx.circuit.gates = bw.ctx.circuit.gates + 1 := by
  simp [appendOrBase]

@[simp] lemma initFalse_gates {M : TM} {n : Nat} (sc : StraightConfig M n) :
    (initFalse (M := M) (n := n) sc).ctx.circuit.gates = sc.circuit.gates + 1 := by
  simp [initFalse, StraightConfig.startEvalBuilder,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendConst,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

/--
Build the scanned symbol wire `OR_i (head_i ∧ tape_i)` by append-only
assembly over base wires.
-/
noncomputable def buildSymbolAux (sc : StraightConfig M n) :
    List (Fin (M.tapeLength n)) → BuiltWire (n := n) sc.circuit →
      BuiltWire (n := n) sc.circuit
  | [], bw => bw
  | i :: is, bw =>
      let bwAnd := appendAndBase (bw := bw) (sc.head i) (sc.tape i)
      let oldOutLift : Fin (n + bwAnd.ctx.circuit.gates) :=
        Pnp3.Internal.PsubsetPpoly.StraightLine.liftWire bw.ctx.circuit bw.out
      let bwOr := appendOrCurrent (bw := bwAnd) oldOutLift bwAnd.out
      buildSymbolAux sc is bwOr

/-- Append-only scanned-symbol wire over the current straight configuration. -/
noncomputable def buildSymbol (sc : StraightConfig M n) :
    BuiltWire (n := n) sc.circuit :=
  buildSymbolAux (sc := sc) (tapeIndexList M n) (initFalse (M := M) (n := n) sc)

lemma buildSymbolAux_gates (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bw : BuiltWire (n := n) sc.circuit),
      (buildSymbolAux (M := M) (n := n) sc is bw).ctx.circuit.gates =
        bw.ctx.circuit.gates + 2 * is.length := by
  intro is
  induction is with
  | nil =>
      intro bw
      simp [buildSymbolAux]
  | cons i is ih =>
      intro bw
      simp [buildSymbolAux, ih]
      omega

@[simp] lemma buildSymbol_gates (sc : StraightConfig M n) :
    (buildSymbol (M := M) (n := n) sc).ctx.circuit.gates =
      sc.circuit.gates + (2 * (M.tapeLength n) + 1) := by
  have hAux := buildSymbolAux_gates (M := M) (n := n) (sc := sc)
      (is := tapeIndexList M n) (bw := initFalse (M := M) (n := n) sc)
  simpa [buildSymbol, tapeIndexList, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAux

/--
Append-only guard wire for scanned symbol value `b`.

`true` uses the symbol wire itself; `false` uses its negation.
-/
noncomputable def buildGuardSymbol (sc : StraightConfig M n) (b : Bool) :
    BuiltWire (n := n) sc.circuit :=
  if b then
    buildSymbol (M := M) (n := n) sc
  else
    let bwSym := buildSymbol (M := M) (n := n) sc
    appendNotCurrent (bw := bwSym) bwSym.out

/--
Append-only branch-indicator wire for transition branch `(q, b)`.
-/
noncomputable def buildBranchIndicator (sc : StraightConfig M n)
    (qs : M.state × Bool) :
    BuiltWire (n := n) sc.circuit := by
  let bwGuard := buildGuardSymbol (M := M) (n := n) sc qs.2
  let wState : Fin (n + bwGuard.ctx.circuit.gates) := bwGuard.ctx.liftBase (sc.state qs.1)
  exact appendAndCurrent (bw := bwGuard) wState bwGuard.out

/--
Append-only write-term wire for transition branch `(q, b)`.

When the machine writes `false`, this term is constant `false`.
-/
noncomputable def buildWriteTerm (sc : StraightConfig M n)
    (qs : M.state × Bool) :
    BuiltWire (n := n) sc.circuit :=
  match M.step qs.1 qs.2 with
  | ⟨_, write, _⟩ =>
      if write then
        buildBranchIndicator (M := M) (n := n) sc qs
      else
        initFalse (M := M) (n := n) sc

/--
Builder payload carrying an extra distinguished wire through append operations.

`carry` is typically used for transporting a previously-built accumulator wire
while constructing the next term.
-/
structure BuiltCarry (base : StraightLineCircuit n) where
  bw : BuiltWire (n := n) base
  carry : Fin (n + bw.ctx.circuit.gates)

/-- Initialize carry with the current output wire. -/
noncomputable def BuiltCarry.init (bw : BuiltWire (n := n) base) :
    BuiltCarry (n := n) base :=
  ⟨bw, bw.out⟩

/-- Append `const` while transporting `carry`. -/
noncomputable def BuiltCarry.appendConst (bc : BuiltCarry (n := n) base) (val : Bool) :
    BuiltCarry (n := n) base := by
  let op : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .const val
  let carry' :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bc.bw.ctx.ctx) (op := op) bc.carry
  let r := bc.bw.ctx.appendConst val
  let bw' : BuiltWire (n := n) base := ⟨r.1, r.2⟩
  exact ⟨bw', carry'⟩

/-- Append `not` while transporting `carry`. -/
noncomputable def BuiltCarry.appendNot (bc : BuiltCarry (n := n) base)
    (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    BuiltCarry (n := n) base := by
  let op : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .not w
  let carry' :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bc.bw.ctx.ctx) (op := op) bc.carry
  let r := bc.bw.ctx.appendNot w
  let bw' : BuiltWire (n := n) base := ⟨r.1, r.2⟩
  exact ⟨bw', carry'⟩

/-- Append `and` while transporting `carry`. -/
noncomputable def BuiltCarry.appendAnd (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) :
    BuiltCarry (n := n) base := by
  let op : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .and u v
  let carry' :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bc.bw.ctx.ctx) (op := op) bc.carry
  let r := bc.bw.ctx.appendAnd u v
  let bw' : BuiltWire (n := n) base := ⟨r.1, r.2⟩
  exact ⟨bw', carry'⟩

/-- Append `or` while transporting `carry`. -/
noncomputable def BuiltCarry.appendOr (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) :
    BuiltCarry (n := n) base := by
  let op : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .or u v
  let carry' :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bc.bw.ctx.ctx) (op := op) bc.carry
  let r := bc.bw.ctx.appendOr u v
  let bw' : BuiltWire (n := n) base := ⟨r.1, r.2⟩
  exact ⟨bw', carry'⟩

/--
Transport-aware symbol builder from an arbitrary carry state.

The resulting output wire computes `symbol`; `carry` is transported through all
added gates.
-/
noncomputable def buildSymbolFromCarry (sc : StraightConfig M n) :
    List (Fin (M.tapeLength n)) → BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit
  | [], bc => bc
  | i :: is, bc =>
      let u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
      let v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
      let opAnd : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .and u v
      let symLiftAnd :=
        Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
          (b := bc.bw.ctx.ctx) (op := opAnd) bc.bw.out
      let bcAnd := BuiltCarry.appendAnd (bc := bc) u v
      let bcOr := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
      buildSymbolFromCarry sc is bcOr

/-- Build branch indicator from a carry state; output wire becomes the branch. -/
noncomputable def buildBranchFromCarry (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    BuiltCarry (n := n) sc.circuit := by
  let bcStart := BuiltCarry.appendConst (bc := bc) false
  let bcSym := buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart
  let bcGuard :=
    if qs.2 then bcSym else BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out
  let wState : Fin (n + bcGuard.bw.ctx.circuit.gates) := bcGuard.bw.ctx.liftBase (sc.state qs.1)
  exact BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out

/-- Build write-term from a carry state; output wire becomes the term. -/
noncomputable def buildWriteTermFromCarry (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    BuiltCarry (n := n) sc.circuit :=
  match M.step qs.1 qs.2 with
  | ⟨_, write, _⟩ =>
      if write then
        buildBranchFromCarry (M := M) (n := n) sc qs bc
      else
        BuiltCarry.appendConst (bc := bc) false

/--
Append-only write-bit wire:
`OR_(q,b) writeTerm(q,b)`, transported over one shared straight-line circuit.
-/
noncomputable def buildWriteBitAux (sc : StraightConfig M n) :
    List (M.state × Bool) → BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit
  | [], bc => bc
  | qs :: t, bc =>
      let bcTerm := buildWriteTermFromCarry (M := M) (n := n) sc qs bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      buildWriteBitAux sc t bcNext

/-- Build one state-branch term from carry; output wire is the branch term. -/
noncomputable def buildStateTermFromCarry (sc : StraightConfig M n)
    (qTarget : M.state) (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    BuiltCarry (n := n) sc.circuit :=
  match M.step qs.1 qs.2 with
  | ⟨qNext, _, _⟩ =>
      if qNext = qTarget then
        buildBranchFromCarry (M := M) (n := n) sc qs bc
      else
        BuiltCarry.appendConst (bc := bc) false

/--
Append-only next-state indicator wire:
`OR_(q,b : step(q,b).state = qTarget) branchIndicator(q,b)`.
-/
noncomputable def buildNextStateAux (sc : StraightConfig M n) (qTarget : M.state) :
    List (M.state × Bool) → BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit
  | [], bc => bc
  | qs :: t, bc =>
      let bcTerm := buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      buildNextStateAux sc qTarget t bcNext

/-- Append-only next-state indicator wire for target state `qTarget`. -/
noncomputable def buildNextState (sc : StraightConfig M n) (qTarget : M.state) :
    BuiltWire (n := n) sc.circuit := by
  let bw0 := initFalse (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bw0, bw0.out⟩
  let bc := buildNextStateAux (M := M) (n := n) sc qTarget (stateSymbolPairs M) bc0
  exact bc.bw

/-- Build one head-branch term from carry; output wire is the branch term. -/
noncomputable def buildHeadTermFromCarry (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit) :
    BuiltCarry (n := n) sc.circuit :=
  match M.step iqs.2.1 iqs.2.2 with
  | ⟨_, _, mv⟩ =>
      if moveIndex (M := M) (n := n) iqs.1 mv = j then
        let bcBranch := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc
        let wHead : Fin (n + bcBranch.bw.ctx.circuit.gates) := bcBranch.bw.ctx.liftBase (sc.head iqs.1)
        BuiltCarry.appendAnd (bc := bcBranch) wHead bcBranch.bw.out
      else
        BuiltCarry.appendConst (bc := bc) false

/--
Append-only next-head indicator wire for target head index `j`.

This is an OR over all transition branches `(i, q, b)` that move from `i` to
`j`, conjoined with the branch predicate and `head_i`.
-/
noncomputable def buildNextHeadAux (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n)) :
    List (Fin (M.tapeLength n) × (M.state × Bool)) →
      BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit
  | [], bc => bc
  | iqs :: t, bc =>
      let bcTerm := buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      buildNextHeadAux sc j t bcNext

/-- Append-only next-head indicator wire for target index `j`. -/
noncomputable def buildNextHead (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n)) :
    BuiltWire (n := n) sc.circuit := by
  let bw0 := initFalse (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bw0, bw0.out⟩
  let bc := buildNextHeadAux (M := M) (n := n) sc j
    (headStateSymbolPairs M n) bc0
  exact bc.bw

/--
Build next-tape bit for cell `i` from a carry state where `carry` is the
already-built `writeBit` wire.

Resulting output is:
`(head_i ∧ writeBit) ∨ (¬head_i ∧ tape_i)`.
Carry is transported unchanged through the appended gates.
-/
noncomputable def buildNextTapeFromCarry (sc : StraightConfig M n)
    (i : Fin (M.tapeLength n)) (bc : BuiltCarry (n := n) sc.circuit) :
    BuiltCarry (n := n) sc.circuit := by
  let wHead0 : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
  let bcWrite := BuiltCarry.appendAnd (bc := bc) wHead0 bc.carry
  let wHead1 : Fin (n + bcWrite.bw.ctx.circuit.gates) := bcWrite.bw.ctx.liftBase (sc.head i)
  let opNot : LegacyStraightOp (n + bcWrite.bw.ctx.circuit.gates) := .not wHead1
  let writeLiftNot :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bcWrite.bw.ctx.ctx) (op := opNot) bcWrite.bw.out
  let bcNot := BuiltCarry.appendNot (bc := bcWrite) wHead1
  let wTape2 : Fin (n + bcNot.bw.ctx.circuit.gates) := bcNot.bw.ctx.liftBase (sc.tape i)
  let opAnd : LegacyStraightOp (n + bcNot.bw.ctx.circuit.gates) := .and bcNot.bw.out wTape2
  let writeLiftAnd :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bcNot.bw.ctx.ctx) (op := opAnd) writeLiftNot
  let bcKeep := BuiltCarry.appendAnd (bc := bcNot) bcNot.bw.out wTape2
  exact BuiltCarry.appendOr (bc := bcKeep) writeLiftAnd bcKeep.bw.out

/-- Append-only write-bit wire over the current straight configuration. -/
noncomputable def buildWriteBit (sc : StraightConfig M n) :
    BuiltWire (n := n) sc.circuit := by
  let bw0 := initFalse (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bw0, bw0.out⟩
  let bc := buildWriteBitAux (M := M) (n := n) sc (stateSymbolPairs M) bc0
  exact bc.bw

@[simp] lemma BuiltCarry_appendConst_bw_gates {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base) (val : Bool) :
    (BuiltCarry.appendConst (bc := bc) val).bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 1 := by
  simp [BuiltCarry.appendConst,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendConst,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma BuiltCarry_appendAnd_bw_gates {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) :
    (BuiltCarry.appendAnd (bc := bc) u v).bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 1 := by
  simp [BuiltCarry.appendAnd,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendAnd,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma BuiltCarry_appendOr_bw_gates {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) :
    (BuiltCarry.appendOr (bc := bc) u v).bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 1 := by
  simp [BuiltCarry.appendOr,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOr,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma BuiltCarry_appendNot_bw_gates {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    (BuiltCarry.appendNot (bc := bc) w).bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 1 := by
  simp [BuiltCarry.appendNot,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendNot,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendOp,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.appendWith,
    Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx.circuit]

@[simp] lemma BuiltCarry_appendConst_carry_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base) (val : Bool) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendConst (bc := bc) val).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendConst (bc := bc) val).carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold BuiltCarry.appendConst
  exact
    (Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.evalWire_appendFin_lift
      (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.const val) (x := x) (w := bc.carry))

@[simp] lemma BuiltCarry_appendNot_carry_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (w : Fin (n + bc.bw.ctx.circuit.gates)) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendNot (bc := bc) w).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendNot (bc := bc) w).carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold BuiltCarry.appendNot
  exact
    (Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.evalWire_appendFin_lift
      (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.not w) (x := x) (w := bc.carry))

@[simp] lemma BuiltCarry_appendAnd_carry_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendAnd (bc := bc) u v).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendAnd (bc := bc) u v).carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold BuiltCarry.appendAnd
  exact
    (Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.evalWire_appendFin_lift
      (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.and u v) (x := x) (w := bc.carry))

@[simp] lemma BuiltCarry_appendOr_carry_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendOr (bc := bc) u v).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendOr (bc := bc) u v).carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold BuiltCarry.appendOr
  exact
    (Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.evalWire_appendFin_lift
      (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.or u v) (x := x) (w := bc.carry))

@[simp] lemma BuiltCarry_appendConst_out_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base) (val : Bool) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendConst (bc := bc) val).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendConst (bc := bc) val).bw.out = val := by
  unfold BuiltCarry.appendConst
  change
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc bc.bw.ctx.circuit
        (LegacyStraightOp.const val)) (x := x)
      (Fin.last (n + bc.bw.ctx.circuit.gates)) = val
  simpa using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
      (C := bc.bw.ctx.circuit) (op := LegacyStraightOp.const val) (x := x))

@[simp] lemma BuiltCarry_appendNot_out_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (w : Fin (n + bc.bw.ctx.circuit.gates)) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendNot (bc := bc) w).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendNot (bc := bc) w).bw.out =
      !(Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) w) := by
  unfold BuiltCarry.appendNot
  change
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc bc.bw.ctx.circuit
        (LegacyStraightOp.not w)) (x := x)
      (Fin.last (n + bc.bw.ctx.circuit.gates)) =
      !(Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) w)
  simpa using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
      (C := bc.bw.ctx.circuit) (op := LegacyStraightOp.not w) (x := x))

@[simp] lemma BuiltCarry_appendAnd_out_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendAnd (bc := bc) u v).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendAnd (bc := bc) u v).bw.out =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) u &&
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) v) := by
  unfold BuiltCarry.appendAnd
  change
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc bc.bw.ctx.circuit
        (LegacyStraightOp.and u v)) (x := x)
      (Fin.last (n + bc.bw.ctx.circuit.gates)) =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) u &&
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) v)
  simpa using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
      (C := bc.bw.ctx.circuit) (op := LegacyStraightOp.and u v) (x := x))

@[simp] lemma BuiltCarry_appendOr_out_eval {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates)) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendOr (bc := bc) u v).bw.ctx.circuit) (x := x)
        (BuiltCarry.appendOr (bc := bc) u v).bw.out =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) u ||
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) v) := by
  unfold BuiltCarry.appendOr
  change
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc bc.bw.ctx.circuit
        (LegacyStraightOp.or u v)) (x := x)
      (Fin.last (n + bc.bw.ctx.circuit.gates)) =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) u ||
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := bc.bw.ctx.circuit) (x := x) v)
  simpa using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
      (C := bc.bw.ctx.circuit) (op := LegacyStraightOp.or u v) (x := x))

/-- Cast a wire index across a monotone gate-count extension. -/
def castWireLe {n g g' : Nat} (h : g ≤ g') (w : Fin (n + g)) : Fin (n + g') :=
  ⟨w, Nat.lt_of_lt_of_le w.isLt (Nat.add_le_add_left h n)⟩

@[simp] lemma castWireLe_val {n g g' : Nat}
    (h : g ≤ g') (w : Fin (n + g)) :
    ((castWireLe (n := n) (g := g) (g' := g') h w : Fin (n + g')) : Nat) = w := rfl

@[simp] lemma castWireLe_trans {n g₁ g₂ g₃ : Nat}
    (h₁₂ : g₁ ≤ g₂) (h₂₃ : g₂ ≤ g₃)
    (w : Fin (n + g₁)) :
    castWireLe (n := n) (g := g₂) (g' := g₃) h₂₃
      (castWireLe (n := n) (g := g₁) (g' := g₂) h₁₂ w) =
    castWireLe (n := n) (g := g₁) (g' := g₃) (Nat.le_trans h₁₂ h₂₃) w := by
  ext
  simp [castWireLe]

@[simp] lemma castWireLe_proof_irrel {n g g' : Nat}
    (h₁ h₂ : g ≤ g') (w : Fin (n + g)) :
    castWireLe (n := n) (g := g) (g' := g') h₁ w =
      castWireLe (n := n) (g := g) (g' := g') h₂ w := by
  ext
  simp [castWireLe]

@[simp] lemma evalWire_congr_castWireLe
    {n g : Nat} {C C' : StraightLine.Circuit n}
    (hC : C = C')
    (x : Boolcube.Point n)
    (h₁ : g ≤ C.gates) (h₂ : g ≤ C'.gates)
    (w : Fin (n + g)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := C) (x := x)
        (castWireLe (n := n) (g := g) (g' := C.gates) h₁ w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := C') (x := x)
          (castWireLe (n := n) (g := g) (g' := C'.gates) h₂ w) := by
  cases hC
  simp [castWireLe_proof_irrel]

@[simp] lemma evalWire_castWireLe_snoc
    {n : Nat} (C : StraightLine.Circuit n)
    (op : LegacyStraightOp (n + C.gates))
    (x : Boolcube.Point n)
    (w : Fin (n + C.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc C op) (x := x)
        (castWireLe (n := n) (g := C.gates) (g' := C.gates + 1) (Nat.le_succ _) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := C) (x := x) w := by
  let wLift : Fin (n + (C.gates + 1)) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.liftWire (C := C) w
  have hwEq : wLift =
      castWireLe (n := n) (g := C.gates) (g' := C.gates + 1) (Nat.le_succ _) w := by
    ext
    simp [wLift, Pnp3.Internal.PsubsetPpoly.StraightLine.liftWire, castWireLe]
  simpa [hwEq, wLift] using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_lift
      (C := C) (op := op) (x := x) (i := w))

@[simp] lemma BuiltCarry_appendConst_preserves_old_eval
    {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base) (val : Bool)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendConst (bc := bc) val).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (BuiltCarry.appendConst (bc := bc) val).bw.ctx.circuit.gates)
          (by simp [BuiltCarry_appendConst_bw_gates]) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  simpa [BuiltCarry.appendConst, castWireLe, BuiltCarry_appendConst_bw_gates] using
    (evalWire_castWireLe_snoc (C := bc.bw.ctx.circuit)
      (op := LegacyStraightOp.const val) (x := x) (w := w))

@[simp] lemma BuiltCarry_appendNot_preserves_old_eval
    {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u : Fin (n + bc.bw.ctx.circuit.gates))
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendNot (bc := bc) u).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (BuiltCarry.appendNot (bc := bc) u).bw.ctx.circuit.gates)
          (by simp [BuiltCarry_appendNot_bw_gates]) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  simpa [BuiltCarry.appendNot, castWireLe, BuiltCarry_appendNot_bw_gates] using
    (evalWire_castWireLe_snoc (C := bc.bw.ctx.circuit)
      (op := LegacyStraightOp.not u) (x := x) (w := w))

@[simp] lemma BuiltCarry_appendAnd_preserves_old_eval
    {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates))
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendAnd (bc := bc) u v).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (BuiltCarry.appendAnd (bc := bc) u v).bw.ctx.circuit.gates)
          (by simp [BuiltCarry_appendAnd_bw_gates]) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  simpa [BuiltCarry.appendAnd, castWireLe, BuiltCarry_appendAnd_bw_gates] using
    (evalWire_castWireLe_snoc (C := bc.bw.ctx.circuit)
      (op := LegacyStraightOp.and u v) (x := x) (w := w))

@[simp] lemma BuiltCarry_appendOr_preserves_old_eval
    {n : Nat} {base : StraightLine.Circuit n}
    (bc : BuiltCarry (n := n) base)
    (u v : Fin (n + bc.bw.ctx.circuit.gates))
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltCarry.appendOr (bc := bc) u v).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (BuiltCarry.appendOr (bc := bc) u v).bw.ctx.circuit.gates)
          (by simp [BuiltCarry_appendOr_bw_gates]) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  simpa [BuiltCarry.appendOr, castWireLe, BuiltCarry_appendOr_bw_gates] using
    (evalWire_castWireLe_snoc (C := bc.bw.ctx.circuit)
      (op := LegacyStraightOp.or u v) (x := x) (w := w))

lemma buildSymbolFromCarry_step_preserves_old_eval
    (sc : StraightConfig M n)
    (bc : BuiltCarry (n := n) sc.circuit)
    (i : Fin (M.tapeLength n))
    (x : Boolcube.Point n)
    (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    let u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
    let v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
    let bcAnd : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) u v
    let symLiftAnd :=
      Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
        (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.and u v) bc.bw.out
    let bcOr : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcOr.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcOr.bw.ctx.circuit.gates)
          (by
            have hAnd : bc.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := by simp [bcAnd]
            have hOr : bcAnd.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by simp [bcOr]
            exact Nat.le_trans hAnd hOr) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  dsimp
  set u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
  set v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
  set bcAnd : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) u v
  set symLiftAnd :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.and u v) bc.bw.out
  set bcOr : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
  have hAndG : bc.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := by
    simp [bcAnd]
  have hOrG : bcAnd.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
    simp [bcOr]
  have hAnd :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcAnd.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcAnd.bw.ctx.circuit.gates) hAndG w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
    simpa [bcAnd] using
      (BuiltCarry_appendAnd_preserves_old_eval (bc := bc) (u := u) (v := v) (x := x) (w := w))
  have hOr :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcOr.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcAnd.bw.ctx.circuit.gates)
            (g' := bcOr.bw.ctx.circuit.gates) hOrG
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcAnd.bw.ctx.circuit.gates) hAndG w))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcAnd.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcAnd.bw.ctx.circuit.gates) hAndG w) := by
    simpa [bcOr] using
      (BuiltCarry_appendOr_preserves_old_eval
        (bc := bcAnd) (u := symLiftAnd) (v := bcAnd.bw.out) (x := x)
        (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcAnd.bw.ctx.circuit.gates) hAndG w))
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcOr.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcOr.bw.ctx.circuit.gates)
          (Nat.le_trans hAndG hOrG) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcOr.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcAnd.bw.ctx.circuit.gates)
            (g' := bcOr.bw.ctx.circuit.gates) hOrG
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcAnd.bw.ctx.circuit.gates) hAndG w)) := by
            simp [castWireLe_trans]
    _ =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcAnd.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcAnd.bw.ctx.circuit.gates) hAndG w) := hOr
    _ = Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := hAnd

@[simp] lemma buildNextTapeFromCarry_out_eval
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n))
    (bc : BuiltCarry (n := n) sc.circuit) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit) (x := x)
        (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.out
      =
        ((Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.carry) ||
         (!(Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i)) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.tape i))) := by
  unfold buildNextTapeFromCarry
  dsimp
  set wHead0 : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
  set bcWrite : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) wHead0 bc.carry
  set wHead1 : Fin (n + bcWrite.bw.ctx.circuit.gates) := bcWrite.bw.ctx.liftBase (sc.head i)
  set writeLiftNot :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bcWrite.bw.ctx.ctx) (op := LegacyStraightOp.not wHead1) bcWrite.bw.out
  set bcNot : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendNot (bc := bcWrite) wHead1
  set wTape2 : Fin (n + bcNot.bw.ctx.circuit.gates) := bcNot.bw.ctx.liftBase (sc.tape i)
  set writeLiftAnd :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bcNot.bw.ctx.ctx) (op := LegacyStraightOp.and bcNot.bw.out wTape2) writeLiftNot
  set bcKeep : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bcNot) bcNot.bw.out wTape2
  have hLiftAnd :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcKeep.bw.ctx.circuit) (x := x) writeLiftAnd =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcNot.bw.ctx.circuit) (x := x) writeLiftNot := by
    simpa only [bcKeep, writeLiftAnd] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.evalWire_appendFin_lift
        (b := bcNot.bw.ctx.ctx) (op := LegacyStraightOp.and bcNot.bw.out wTape2)
        (x := x) (w := writeLiftNot))
  have hLiftNot :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcNot.bw.ctx.circuit) (x := x) writeLiftNot =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcWrite.bw.ctx.circuit) (x := x) bcWrite.bw.out := by
    simpa only [bcNot, writeLiftNot] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.evalWire_appendFin_lift
        (b := bcWrite.bw.ctx.ctx) (op := LegacyStraightOp.not wHead1)
        (x := x) (w := bcWrite.bw.out))
  simp [hLiftAnd, hLiftNot, bcKeep, bcNot, bcWrite, wHead0, wHead1, wTape2]

lemma evalWire_if_builtCarry
    {n : Nat} {base : StraightLine.Circuit n}
    (x : Boolcube.Point n) (p : Prop) [Decidable p]
    (t e : BuiltCarry (n := n) base) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (if p then t else e).bw.ctx.circuit) (x := x)
        (if p then t else e).bw.out
      =
        (if p then
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := t.bw.ctx.circuit) (x := x) t.bw.out
         else
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := e.bw.ctx.circuit) (x := x) e.bw.out) := by
  by_cases hp : p
  · rw [if_pos hp]
    simp [hp]
  · rw [if_neg hp]
    simp [hp]

lemma evalCarry_if_builtCarry
    {n : Nat} {base : StraightLine.Circuit n}
    (x : Boolcube.Point n) (p : Prop) [Decidable p]
    (t e : BuiltCarry (n := n) base) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (if p then t else e).bw.ctx.circuit) (x := x)
        (if p then t else e).carry
      =
        (if p then
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := t.bw.ctx.circuit) (x := x) t.carry
         else
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := e.bw.ctx.circuit) (x := x) e.carry) := by
  by_cases hp : p
  · rw [if_pos hp]
    simp [hp]
  · rw [if_neg hp]
    simp [hp]

def symbolFoldlEval
    (sc : StraightConfig M n) (x : Boolcube.Point n)
    (is : List (Fin (M.tapeLength n))) (acc : Bool) : Bool :=
  is.foldl
    (fun a i =>
      a ||
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i) &&
         Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i)))
    acc

lemma symbolFoldlEval_eq_or_any
    (sc : StraightConfig M n) (x : Boolcube.Point n)
    (is : List (Fin (M.tapeLength n))) (acc : Bool) :
    symbolFoldlEval (M := M) (n := n) sc x is acc =
      (acc || List.any is (fun i =>
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i) &&
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i))) := by
  induction is generalizing acc with
  | nil =>
      simp [symbolFoldlEval]
  | cons i is ih =>
      have hTail := ih (acc ||
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i) &&
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i)))
      simpa [symbolFoldlEval, Bool.or_assoc] using hTail

lemma symbolFoldlEval_false_eq_any
    (sc : StraightConfig M n) (x : Boolcube.Point n)
    (is : List (Fin (M.tapeLength n))) :
    symbolFoldlEval (M := M) (n := n) sc x is false =
      List.any is (fun i =>
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i) &&
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i)) := by
  simpa using symbolFoldlEval_eq_or_any (M := M) (n := n) sc x is false

lemma buildSymbolFromCarry_step_eval
    (sc : StraightConfig M n)
    (bc : BuiltCarry (n := n) sc.circuit)
    (i : Fin (M.tapeLength n))
    (x : Boolcube.Point n) :
    let u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
    let v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
    let bcAnd : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) u v
    let opAnd : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .and u v
    let symLiftAnd :=
      Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
        (b := bc.bw.ctx.ctx) (op := opAnd) bc.bw.out
    let bcOr : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out
      =
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
          (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := sc.circuit) (x := x) (sc.head i) &&
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := sc.circuit) (x := x) (sc.tape i))) := by
  dsimp
  set u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
  set v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
  set bcAnd : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) u v
  set opAnd : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .and u v
  set symLiftAnd :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bc.bw.ctx.ctx) (op := opAnd) bc.bw.out
  set bcOr : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
  let bcOut : BuiltCarry (n := n) sc.circuit := ⟨bc.bw, bc.bw.out⟩
  have hSymLiftCtx :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltCarry.appendAnd (bc := bcOut) u v).bw.ctx.circuit) (x := x)
          (BuiltCarry.appendAnd (bc := bcOut) u v).carry =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcOut.bw.ctx.circuit) (x := x) bcOut.carry := by
    simpa using BuiltCarry_appendAnd_carry_eval (bc := bcOut) (u := u) (v := v) (x := x)
  have hSymLift :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcAnd.bw.ctx.circuit) (x := x) symLiftAnd =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.bw.out := by
    simpa [bcOut, bcAnd, symLiftAnd, opAnd, BuiltCarry.appendAnd] using hSymLiftCtx
  have hAnd :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcAnd.bw.ctx.circuit) (x := x) bcAnd.bw.out =
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) u &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) v) := by
    simpa [bcAnd] using BuiltCarry_appendAnd_out_eval (bc := bc) (u := u) (v := v) (x := x)
  have hU :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) u =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i) := by
    simpa [u] using (bc.bw.ctx.eval_liftBase x (sc.head i))
  have hV :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) v =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i) := by
    simpa [v] using (bc.bw.ctx.eval_liftBase x (sc.tape i))
  have hOr :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out =
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcAnd.bw.ctx.circuit) (x := x) symLiftAnd ||
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcAnd.bw.ctx.circuit) (x := x) bcAnd.bw.out) := by
    simpa [bcOr] using
      BuiltCarry_appendOr_out_eval (bc := bcAnd) (u := symLiftAnd) (v := bcAnd.bw.out) (x := x)
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out
        =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcAnd.bw.ctx.circuit) (x := x) symLiftAnd ||
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcAnd.bw.ctx.circuit) (x := x) bcAnd.bw.out) := hOr
    _ =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) u &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) v)) := by
              simp [hSymLift, hAnd]
    _ =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.tape i))) := by
              simp [hU, hV]

lemma buildSymbolFromCarry_out_eval
    (sc : StraightConfig M n)
    (is : List (Fin (M.tapeLength n)))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.ctx.circuit) (x := x)
        (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.out
      =
        symbolFoldlEval (M := M) (n := n) sc x is
          (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.bw.out) := by
  induction is generalizing bc with
  | nil =>
      simp [buildSymbolFromCarry, symbolFoldlEval]
  | cons i is ih =>
      simp [buildSymbolFromCarry, symbolFoldlEval]
      set u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
      set v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
      set bcAnd : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) u v
      set opAnd : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .and u v
      set symLiftAnd :=
        Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
          (b := bc.bw.ctx.ctx) (op := opAnd) bc.bw.out
      set bcOr : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
      have hStep :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out
            =
              (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
                (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := sc.circuit) (x := x) (sc.head i) &&
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := sc.circuit) (x := x) (sc.tape i))) := by
        simpa [u, v, bcAnd, opAnd, symLiftAnd, bcOr] using
          buildSymbolFromCarry_step_eval (M := M) (n := n) sc bc i x
      simpa [hStep, u, v, bcAnd, opAnd, symLiftAnd, bcOr] using ih (bc := bcOr)

lemma buildSymbolFromCarry_carry_eval
    (sc : StraightConfig M n)
    (is : List (Fin (M.tapeLength n)))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.ctx.circuit) (x := x)
        (buildSymbolFromCarry (M := M) (n := n) sc is bc).carry
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  induction is generalizing bc with
  | nil =>
      simp [buildSymbolFromCarry]
  | cons i is ih =>
      simp [buildSymbolFromCarry]
      set u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
      set v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
      set bcAnd : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) u v
      set opAnd : LegacyStraightOp (n + bc.bw.ctx.circuit.gates) := .and u v
      set symLiftAnd :=
        Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
          (b := bc.bw.ctx.ctx) (op := opAnd) bc.bw.out
      set bcOr : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
      have hCarryAnd :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcAnd.bw.ctx.circuit) (x := x) bcAnd.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
        simpa [bcAnd] using BuiltCarry_appendAnd_carry_eval (bc := bc) (u := u) (v := v) (x := x)
      have hCarryOr :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x) bcOr.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcAnd.bw.ctx.circuit) (x := x) bcAnd.carry := by
        simpa [bcOr] using
          BuiltCarry_appendOr_carry_eval (bc := bcAnd) (u := symLiftAnd) (v := bcAnd.bw.out) (x := x)
      simpa [u, v, bcAnd, opAnd, symLiftAnd, bcOr, hCarryAnd] using
        (ih (bc := bcOr))

lemma buildBranchFromCarry_carry_eval
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (buildBranchFromCarry (M := M) (n := n) sc qs bc).carry
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold buildBranchFromCarry
  dsimp
  set bcStart : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendConst (bc := bc) false
  set bcSym : BuiltCarry (n := n) sc.circuit :=
    buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart
  have hStart :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcStart.bw.ctx.circuit) (x := x) bcStart.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
    simpa [bcStart] using BuiltCarry_appendConst_carry_eval (bc := bc) (val := false) (x := x)
  have hSym :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcSym.bw.ctx.circuit) (x := x) bcSym.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcStart.bw.ctx.circuit) (x := x) bcStart.carry := by
    simpa [bcSym] using
      buildSymbolFromCarry_carry_eval (M := M) (n := n) sc (tapeIndexList M n) bcStart x
  cases hq : qs.2
  ·
    set bcGuard : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out
    set wState : Fin (n + bcGuard.bw.ctx.circuit.gates) := bcGuard.bw.ctx.liftBase (sc.state qs.1)
    have hGuard :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.carry
          =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcSym.bw.ctx.circuit) (x := x) bcSym.carry := by
      simpa [bcGuard] using BuiltCarry_appendNot_carry_eval (bc := bcSym) (w := bcSym.bw.out) (x := x)
    have hFinal :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).bw.ctx.circuit) (x := x)
            (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).carry
          =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.carry := by
      simpa using
        BuiltCarry_appendAnd_carry_eval (bc := bcGuard) (u := wState) (v := bcGuard.bw.out) (x := x)
    simpa [hq, bcStart, bcSym, bcGuard, wState, hStart, hSym, hGuard] using hFinal
  ·
    set bcGuard : BuiltCarry (n := n) sc.circuit := bcSym
    set wState : Fin (n + bcGuard.bw.ctx.circuit.gates) := bcGuard.bw.ctx.liftBase (sc.state qs.1)
    have hFinal :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).bw.ctx.circuit) (x := x)
            (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).carry
          =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.carry := by
      simpa using
        BuiltCarry_appendAnd_carry_eval (bc := bcGuard) (u := wState) (v := bcGuard.bw.out) (x := x)
    simpa [hq, bcStart, bcSym, bcGuard, wState, hStart, hSym] using hFinal

lemma buildWriteTermFromCarry_carry_eval
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (buildWriteTermFromCarry (M := M) (n := n) sc qs bc).carry
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold buildWriteTermFromCarry
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          cases wr
          · simpa [hstep] using BuiltCarry_appendConst_carry_eval (bc := bc) (val := false) (x := x)
          · simpa [hstep] using buildBranchFromCarry_carry_eval (M := M) (n := n) sc qs bc x

lemma buildSymbolFromCarry_out_eval_tapeIndexList_from_false
    (sc : StraightConfig M n)
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    let bcStart := BuiltCarry.appendConst (bc := bc) false
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart).bw.ctx.circuit) (x := x)
        (buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart).bw.out
      =
        symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false := by
  dsimp
  simpa using
    (buildSymbolFromCarry_out_eval (M := M) (n := n) sc
      (is := tapeIndexList M n) (bc := BuiltCarry.appendConst (bc := bc) false) x)

lemma buildBranchFromCarry_out_eval
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.out
      =
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.state qs.1) &&
          (if qs.2 then
            symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false
           else
            !(symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false))) := by
  unfold buildBranchFromCarry
  dsimp
  set bcStart : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendConst (bc := bc) false
  set bcSym : BuiltCarry (n := n) sc.circuit :=
    buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart
  have hSym :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcSym.bw.ctx.circuit) (x := x) bcSym.bw.out =
        symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false := by
    simpa [bcStart, bcSym] using
      (buildSymbolFromCarry_out_eval_tapeIndexList_from_false
        (M := M) (n := n) sc bc x)
  cases hq : qs.2
  · set bcGuard : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out
    set wState : Fin (n + bcGuard.bw.ctx.circuit.gates) := bcGuard.bw.ctx.liftBase (sc.state qs.1)
    have hAnd :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).bw.ctx.circuit) (x := x)
            (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).bw.out
          =
            (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcGuard.bw.ctx.circuit) (x := x) wState &&
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.bw.out) := by
      simpa using
        (BuiltCarry_appendAnd_out_eval (bc := bcGuard) (u := wState) (v := bcGuard.bw.out) (x := x))
    have hState :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcGuard.bw.ctx.circuit) (x := x) wState =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.state qs.1) := by
      simpa [wState] using bcGuard.bw.ctx.eval_liftBase x (sc.state qs.1)
    have hGuardOut :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.bw.out =
          !(symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false) := by
      have hNot :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.bw.out =
            !(Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcSym.bw.ctx.circuit) (x := x) bcSym.bw.out) := by
        simpa [bcGuard] using
          (BuiltCarry_appendNot_out_eval (bc := bcSym) (w := bcSym.bw.out) (x := x))
      simpa [hSym] using hNot
    simpa [hq, bcGuard, wState, hAnd, hState, hGuardOut]
  · set bcGuard : BuiltCarry (n := n) sc.circuit := bcSym
    set wState : Fin (n + bcGuard.bw.ctx.circuit.gates) := bcGuard.bw.ctx.liftBase (sc.state qs.1)
    have hAnd :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).bw.ctx.circuit) (x := x)
            (BuiltCarry.appendAnd (bc := bcGuard) wState bcGuard.bw.out).bw.out
          =
            (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcGuard.bw.ctx.circuit) (x := x) wState &&
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.bw.out) := by
      simpa using
        (BuiltCarry_appendAnd_out_eval (bc := bcGuard) (u := wState) (v := bcGuard.bw.out) (x := x))
    have hState :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcGuard.bw.ctx.circuit) (x := x) wState =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.state qs.1) := by
      simpa [wState] using bcGuard.bw.ctx.eval_liftBase x (sc.state qs.1)
    have hGuardOut :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcGuard.bw.ctx.circuit) (x := x) bcGuard.bw.out =
          symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false := by
      simpa [bcGuard] using hSym
    simpa [hq, bcGuard, wState, hAnd, hState, hGuardOut]

lemma buildStateTermFromCarry_out_eval
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
        (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.out
      =
        match M.step qs.1 qs.2 with
        | ⟨qNext, _, _⟩ =>
            if qNext = qTarget then
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
                (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.out
            else false := by
  unfold buildStateTermFromCarry
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          cases hdec : M.stateDecEq qn qTarget with
          | isTrue hq =>
              simpa [hdec, hq, evalWire_if_builtCarry] using
                (evalWire_if_builtCarry (x := x) (p := qn = qTarget)
                  (t := buildBranchFromCarry (M := M) (n := n) sc qs bc)
                  (e := BuiltCarry.appendConst (bc := bc) false))
          | isFalse hq =>
              simpa [hdec, hq, evalWire_if_builtCarry] using
                (evalWire_if_builtCarry (x := x) (p := qn = qTarget)
                  (t := buildBranchFromCarry (M := M) (n := n) sc qs bc)
                  (e := BuiltCarry.appendConst (bc := bc) false))

lemma buildHeadTermFromCarry_out_eval
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
        (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.out
      =
        match M.step iqs.2.1 iqs.2.2 with
        | ⟨_, _, mv⟩ =>
            if moveIndex (M := M) (n := n) iqs.1 mv = j then
              (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := sc.circuit) (x := x) (sc.head iqs.1) &&
               Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.circuit) (x := x)
                (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out)
            else false := by
  unfold buildHeadTermFromCarry
  cases hstep : M.step iqs.2.1 iqs.2.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          cases hdec : instDecidableEqFin (M.tapeLength n) (moveIndex (M := M) (n := n) iqs.1 mv) j with
          | isTrue hmv =>
              simpa [hdec, hmv, evalWire_if_builtCarry] using
                (evalWire_if_builtCarry (x := x)
                  (p := moveIndex (M := M) (n := n) iqs.1 mv = j)
                  (t := BuiltCarry.appendAnd
                    (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                    ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase
                      (sc.head iqs.1))
                    (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out)
                  (e := BuiltCarry.appendConst (bc := bc) false))
          | isFalse hmv =>
              simpa [hdec, hmv, evalWire_if_builtCarry] using
                (evalWire_if_builtCarry (x := x)
                  (p := moveIndex (M := M) (n := n) iqs.1 mv = j)
                  (t := BuiltCarry.appendAnd
                    (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                    ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase
                      (sc.head iqs.1))
                    (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out)
                (e := BuiltCarry.appendConst (bc := bc) false))

lemma buildStateTermFromCarry_carry_eval
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
        (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).carry
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold buildStateTermFromCarry
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          simp
          by_cases hq : qn = qTarget
          · rw [if_pos hq]
            exact buildBranchFromCarry_carry_eval (M := M) (n := n) sc qs bc x
          · rw [if_neg hq]
            exact BuiltCarry_appendConst_carry_eval (bc := bc) (val := false) (x := x)

lemma buildHeadTermFromCarry_carry_eval
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
        (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).carry
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold buildHeadTermFromCarry
  cases hstep : M.step iqs.2.1 iqs.2.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          have hIf :
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (if moveIndex (M := M) (n := n) iqs.1 mv = j then
                    BuiltCarry.appendAnd
                      (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                      ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                      (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out
                   else
                    BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit) (x := x)
                  (if moveIndex (M := M) (n := n) iqs.1 mv = j then
                    BuiltCarry.appendAnd
                      (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                      ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                      (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out
                   else
                    BuiltCarry.appendConst (bc := bc) false).carry
                =
                  (if moveIndex (M := M) (n := n) iqs.1 mv = j then
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := (BuiltCarry.appendAnd
                        (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                        ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                        (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out).bw.ctx.circuit) (x := x)
                      (BuiltCarry.appendAnd
                        (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                        ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                        (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out).carry
                   else
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit) (x := x)
                      (BuiltCarry.appendConst (bc := bc) false).carry) := by
            simpa using
              evalCarry_if_builtCarry (x := x)
                (p := moveIndex (M := M) (n := n) iqs.1 mv = j)
                (t := BuiltCarry.appendAnd
                  (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                  ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                  (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out)
                (e := BuiltCarry.appendConst (bc := bc) false)
          have hAndToBranch :
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltCarry.appendAnd
                    (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                    ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                    (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out).bw.ctx.circuit) (x := x)
                  (BuiltCarry.appendAnd
                    (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                    ((buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                    (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out).carry
                =
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.circuit) (x := x)
                    (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).carry := by
            simpa using
              BuiltCarry_appendAnd_carry_eval
                (bc := buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc)
                (u := (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.liftBase (sc.head iqs.1))
                (v := (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out) (x := x)
          have hBranchToBase :
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.circuit) (x := x)
                  (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).carry
                =
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
            simpa using buildBranchFromCarry_carry_eval (M := M) (n := n) sc iqs.2 bc x
          have hConst :
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit) (x := x)
                  (BuiltCarry.appendConst (bc := bc) false).carry
                =
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
            simpa using BuiltCarry_appendConst_carry_eval (bc := bc) (val := false) (x := x)
          by_cases hmv : moveIndex (M := M) (n := n) iqs.1 mv = j
          · simpa [hstep, hmv, hAndToBranch, hBranchToBase] using hIf
          · simpa [hstep, hmv, hConst] using hIf

lemma buildWriteTermFromCarry_out_eval
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.out
      =
        match M.step qs.1 qs.2 with
        | ⟨_, write, _⟩ =>
            if write then
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
                (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.out
            else false := by
  unfold buildWriteTermFromCarry
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          cases wr <;> simp

noncomputable def buildWriteBitAuxEval
    (sc : StraightConfig M n)
    (x : Boolcube.Point n) :
    List (M.state × Bool) → BuiltCarry (n := n) sc.circuit → Bool
  | [], bc =>
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out
  | qs :: t, bc =>
      let bcTerm := buildWriteTermFromCarry (M := M) (n := n) sc qs bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      buildWriteBitAuxEval sc x t bcNext

lemma buildWriteBitAux_out_eval
    (sc : StraightConfig M n)
    (qs : List (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildWriteBitAux (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (buildWriteBitAux (M := M) (n := n) sc qs bc).bw.out
      =
        buildWriteBitAuxEval (M := M) (n := n) sc x qs bc := by
  induction qs generalizing bc with
  | nil =>
      simp [buildWriteBitAux, buildWriteBitAuxEval]
  | cons qs0 qs ih =>
      simp [buildWriteBitAux, buildWriteBitAuxEval, ih]

noncomputable def buildNextStateAuxEval
    (sc : StraightConfig M n)
    (qTarget : M.state)
    (x : Boolcube.Point n) :
    List (M.state × Bool) → BuiltCarry (n := n) sc.circuit → Bool
  | [], bc =>
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out
  | qs :: t, bc =>
      let bcTerm := buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      buildNextStateAuxEval sc qTarget x t bcNext

lemma buildNextStateAux_out_eval
    (sc : StraightConfig M n)
    (qTarget : M.state)
    (qs : List (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildNextStateAux (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
        (buildNextStateAux (M := M) (n := n) sc qTarget qs bc).bw.out
      =
        buildNextStateAuxEval (M := M) (n := n) sc qTarget x qs bc := by
  induction qs generalizing bc with
  | nil =>
      simp [buildNextStateAux, buildNextStateAuxEval]
  | cons qs0 qs ih =>
      simp [buildNextStateAux, buildNextStateAuxEval, ih]

noncomputable def buildNextHeadAuxEval
    (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n))
    (x : Boolcube.Point n) :
    List (Fin (M.tapeLength n) × (M.state × Bool)) →
      BuiltCarry (n := n) sc.circuit → Bool
  | [], bc =>
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out
  | iqs :: t, bc =>
      let bcTerm := buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      buildNextHeadAuxEval sc j x t bcNext

lemma buildNextHeadAux_out_eval
    (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n))
    (iqs : List (Fin (M.tapeLength n) × (M.state × Bool)))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildNextHeadAux (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
        (buildNextHeadAux (M := M) (n := n) sc j iqs bc).bw.out
      =
        buildNextHeadAuxEval (M := M) (n := n) sc j x iqs bc := by
  induction iqs generalizing bc with
  | nil =>
      simp [buildNextHeadAux, buildNextHeadAuxEval]
  | cons iqs0 iqs ih =>
      simp [buildNextHeadAux, buildNextHeadAuxEval, ih]

lemma buildSymbolFromCarry_gates (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.ctx.circuit.gates =
        bc.bw.ctx.circuit.gates + 2 * is.length := by
  intro is
  induction is with
  | nil =>
      intro bc
      simp [buildSymbolFromCarry]
  | cons i is ih =>
      intro bc
      simp [buildSymbolFromCarry, ih]
      omega

lemma buildBranchFromCarry_gates_le
    (sc : StraightConfig M n) (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates ≤
      bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 3) := by
  have hSym' :
      (buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n)
        (BuiltCarry.appendConst (bc := bc) false)).bw.ctx.circuit.gates =
      bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 1) := by
    have hAux := buildSymbolFromCarry_gates (M := M) (n := n) (sc := sc)
      (is := tapeIndexList M n) (bc := BuiltCarry.appendConst (bc := bc) false)
    simpa [tapeIndexList, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAux
  by_cases hb : qs.2
  · simp [buildBranchFromCarry, hb, hSym']
    omega
  · simp [buildBranchFromCarry, hb, hSym']
    omega

lemma buildWriteTermFromCarry_gates_le
    (sc : StraightConfig M n) (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    (buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates ≤
      bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 3) := by
  unfold buildWriteTermFromCarry
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hwr : wr
          · simpa [hwr] using buildBranchFromCarry_gates_le (M := M) (n := n) sc qs bc
          · simp [hwr]

lemma buildWriteBitAux_gates_le (sc : StraightConfig M n) :
    ∀ (qs : List (M.state × Bool)) (bc : BuiltCarry (n := n) sc.circuit),
      (buildWriteBitAux (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length := by
  intro qs
  induction qs with
  | nil =>
      intro bc
      simp [buildWriteBitAux]
  | cons qs0 qs ih =>
      intro bc
      let bcTerm := buildWriteTermFromCarry (M := M) (n := n) sc qs0 bc
      have hTerm :
          bcTerm.bw.ctx.circuit.gates ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 3) :=
        buildWriteTermFromCarry_gates_le (M := M) (n := n) sc qs0 bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hOr :
          bcOr.bw.ctx.circuit.gates ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) := by
        have hOrEq : bcOr.bw.ctx.circuit.gates = bcTerm.bw.ctx.circuit.gates + 1 := by
          simp [bcOr]
        omega
      have hRest :
          (buildWriteBitAux (M := M) (n := n) sc qs bcNext).bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length :=
        ih bcNext
      have hStep :
          (buildWriteBitAux (M := M) (n := n) sc (qs0 :: qs) bc).bw.ctx.circuit.gates ≤
            bcOr.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length := by
        simpa [buildWriteBitAux, bcTerm, bcOr, bcNext] using hRest
      calc
        (buildWriteBitAux (M := M) (n := n) sc (qs0 :: qs) bc).bw.ctx.circuit.gates
            ≤ bcOr.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length := hStep
        _ ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) +
              (2 * (M.tapeLength n) + 4) * qs.length := by omega
        _ = bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * (List.length (qs0 :: qs)) := by
            simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] lemma buildWriteBit_gates_le (sc : StraightConfig M n) :
    (buildWriteBit (M := M) (n := n) sc).ctx.circuit.gates ≤
      sc.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1 := by
  have hAux := buildWriteBitAux_gates_le (M := M) (n := n) (sc := sc)
      (qs := stateSymbolPairs M) (bc := ⟨initFalse (M := M) (n := n) sc, (initFalse (M := M) (n := n) sc).out⟩)
  have hInit :
      (⟨initFalse (M := M) (n := n) sc, (initFalse (M := M) (n := n) sc).out⟩ :
        BuiltCarry (n := n) sc.circuit).bw.ctx.circuit.gates = sc.circuit.gates + 1 := by
    simp
  have hLen : (stateSymbolPairs M).length = 2 * stateCard M := length_stateSymbolPairs M
  simpa [buildWriteBit, hInit, hLen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_add, Nat.add_mul] using hAux

/-- Append-only next-tape bit wire for target tape index `i`. -/
noncomputable def buildNextTape (sc : StraightConfig M n)
    (i : Fin (M.tapeLength n)) :
    BuiltWire (n := n) sc.circuit := by
  let bwWrite := buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  let bc := buildNextTapeFromCarry (M := M) (n := n) sc i bc0
  exact bc.bw

lemma buildNextTapeFromCarry_gates_eq
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n))
    (bc : BuiltCarry (n := n) sc.circuit) :
    (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit.gates =
      bc.bw.ctx.circuit.gates + 4 := by
  unfold buildNextTapeFromCarry
  simp

lemma buildStateTermFromCarry_gates_le
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates ≤
      bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 3) := by
  unfold buildStateTermFromCarry
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hq : qn = qTarget
          · simpa [hq] using buildBranchFromCarry_gates_le (M := M) (n := n) sc qs bc
          · simp [hq]

lemma buildNextStateAux_gates_le (sc : StraightConfig M n) (qTarget : M.state) :
    ∀ (qs : List (M.state × Bool)) (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextStateAux (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length := by
  intro qs
  induction qs with
  | nil =>
      intro bc
      simp [buildNextStateAux]
  | cons qs0 qs ih =>
      intro bc
      let bcTerm := buildStateTermFromCarry (M := M) (n := n) sc qTarget qs0 bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hTerm :
          bcTerm.bw.ctx.circuit.gates ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 3) :=
        buildStateTermFromCarry_gates_le (M := M) (n := n) sc qTarget qs0 bc
      have hRest :
          (buildNextStateAux (M := M) (n := n) sc qTarget qs bcNext).bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length :=
        ih bcNext
      have hStep :
          (buildNextStateAux (M := M) (n := n) sc qTarget (qs0 :: qs) bc).bw.ctx.circuit.gates ≤
            bcOr.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length := by
        simpa [buildNextStateAux, bcTerm, bcOr, bcNext] using hRest
      have hOr :
          bcOr.bw.ctx.circuit.gates ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) := by
        have hOrEq : bcOr.bw.ctx.circuit.gates = bcTerm.bw.ctx.circuit.gates + 1 := by simp [bcOr]
        omega
      calc
        (buildNextStateAux (M := M) (n := n) sc qTarget (qs0 :: qs) bc).bw.ctx.circuit.gates
            ≤ bcOr.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * qs.length := hStep
        _ ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) +
              (2 * (M.tapeLength n) + 4) * qs.length := by omega
        _ = bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * (List.length (qs0 :: qs)) := by
            simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma length_headStateSymbolPairsAux :
    ∀ (l : List (Fin (M.tapeLength n))),
      (headStateSymbolPairsAux M n l).length = l.length * (stateSymbolPairs M).length := by
  intro l
  induction l with
  | nil =>
      simp [headStateSymbolPairsAux]
  | cons i t ih =>
      have hmul :
          (stateSymbolPairs M).length + t.length * (stateSymbolPairs M).length =
            (t.length + 1) * (stateSymbolPairs M).length := by
        calc
          (stateSymbolPairs M).length + t.length * (stateSymbolPairs M).length
              = t.length * (stateSymbolPairs M).length + (stateSymbolPairs M).length := by
                  rw [Nat.add_comm]
          _ = t.length * (stateSymbolPairs M).length + 1 * (stateSymbolPairs M).length := by
                simp
          _ = (t.length + 1) * (stateSymbolPairs M).length := by
                simpa [Nat.add_mul]
      simpa [headStateSymbolPairsAux, ih] using hmul

lemma length_headStateSymbolPairs :
    (headStateSymbolPairs M n).length = (M.tapeLength n) * (2 * stateCard M) := by
  simpa [headStateSymbolPairs, tapeIndexList, length_stateSymbolPairs,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (length_headStateSymbolPairsAux (M := M) (n := n) (l := tapeIndexList M n))

lemma buildHeadTermFromCarry_gates_le
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit) :
    (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates ≤
      bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) := by
  unfold buildHeadTermFromCarry
  cases hstep : M.step iqs.2.1 iqs.2.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hmv : moveIndex (M := M) (n := n) iqs.1 mv = j
          · simp [hmv]
            have hBr :
                (buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.circuit.gates ≤
                  bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 3) :=
              buildBranchFromCarry_gates_le (M := M) (n := n) sc iqs.2 bc
            omega
          · simp [hmv]

lemma buildNextHeadAux_gates_le
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n)) :
    ∀ (iqs : List (Fin (M.tapeLength n) × (M.state × Bool)))
      (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextHeadAux (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) * iqs.length := by
  intro iqs
  induction iqs with
  | nil =>
      intro bc
      simp [buildNextHeadAux]
  | cons iqs0 iqs ih =>
      intro bc
      let bcTerm := buildHeadTermFromCarry (M := M) (n := n) sc j iqs0 bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hTerm :
          bcTerm.bw.ctx.circuit.gates ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) :=
        buildHeadTermFromCarry_gates_le (M := M) (n := n) sc j iqs0 bc
      have hRest :
          (buildNextHeadAux (M := M) (n := n) sc j iqs bcNext).bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) * iqs.length :=
        ih bcNext
      have hStep :
          (buildNextHeadAux (M := M) (n := n) sc j (iqs0 :: iqs) bc).bw.ctx.circuit.gates ≤
            bcOr.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) * iqs.length := by
        simpa [buildNextHeadAux, bcTerm, bcOr, bcNext] using hRest
      have hOr :
          bcOr.bw.ctx.circuit.gates ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) := by
        have hOrEq : bcOr.bw.ctx.circuit.gates = bcTerm.bw.ctx.circuit.gates + 1 := by
          simp [bcOr]
        omega
      calc
        (buildNextHeadAux (M := M) (n := n) sc j (iqs0 :: iqs) bc).bw.ctx.circuit.gates
            ≤ bcOr.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) * iqs.length := hStep
        _ ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) +
              (2 * (M.tapeLength n) + 5) * iqs.length := by omega
        _ = bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 5) * (List.length (iqs0 :: iqs)) := by
            simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/--
Blueprint of the constructive linear one-step assembly over a fixed base
configuration circuit.

All components are expressed as append-only builders rooted at `sc.circuit`.
This structure is a staging contract for replacing `stepCompiledLinear`.
-/
structure LinearStepBlueprint (sc : StraightConfig M n) where
  writeBit : BuiltWire (n := n) sc.circuit
  nextTape : Fin (M.tapeLength n) → BuiltWire (n := n) sc.circuit
  nextHead : Fin (M.tapeLength n) → BuiltWire (n := n) sc.circuit
  nextState : M.state → BuiltWire (n := n) sc.circuit

/-- Constructive blueprint instance populated by current append-only builders. -/
noncomputable def linearStepBlueprint (sc : StraightConfig M n) :
    LinearStepBlueprint (M := M) (n := n) sc where
  writeBit := buildWriteBit (M := M) (n := n) sc
  nextTape := fun i => buildNextTape (M := M) (n := n) sc i
  nextHead := fun j => buildNextHead (M := M) (n := n) sc j
  nextState := fun q => buildNextState (M := M) (n := n) sc q

/--
Linear-step candidate building block: append-only write-bit wire extracted from
the current straight configuration.
-/
noncomputable def linearWriteBitWire (sc : StraightConfig M n) :
    Fin (n + (BuiltWire.buildWriteBit (M := M) (n := n) sc).ctx.circuit.gates) :=
  (BuiltWire.buildWriteBit (M := M) (n := n) sc).out

/--
Linear-step candidate building block: append-only next-state wire for a fixed
target state.
-/
noncomputable def linearNextStateWire (sc : StraightConfig M n) (qTarget : M.state) :
    Fin (n + (BuiltWire.buildNextState (M := M) (n := n) sc qTarget).ctx.circuit.gates) :=
  (BuiltWire.buildNextState (M := M) (n := n) sc qTarget).out

/--
Linear-step candidate building block: append-only next-head wire for a fixed
target head index.
-/
noncomputable def linearNextHeadWire (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n)) :
    Fin (n + (BuiltWire.buildNextHead (M := M) (n := n) sc j).ctx.circuit.gates) :=
  (BuiltWire.buildNextHead (M := M) (n := n) sc j).out

/--
Linear-step candidate building block: append-only next-tape wire for a fixed
target tape index.
-/
noncomputable def linearNextTapeWire (sc : StraightConfig M n)
    (i : Fin (M.tapeLength n)) :
    Fin (n + (BuiltWire.buildNextTape (M := M) (n := n) sc i).ctx.circuit.gates) :=
  (BuiltWire.buildNextTape (M := M) (n := n) sc i).out

/--
Readiness witness: the constructive linear-step blueprint is available for any
straight configuration.
-/
theorem linearStepBlueprint_ready (sc : StraightConfig M n) :
    Nonempty (LinearStepBlueprint (M := M) (n := n) sc) :=
  ⟨linearStepBlueprint (M := M) (n := n) sc⟩

/--
Audit helper: every component in the constructive linear-step blueprint is an
extension of the same base circuit `sc.circuit` (append-only monotonicity).
-/
theorem linearStepBlueprint_base_le (sc : StraightConfig M n) :
    sc.circuit.gates ≤ (linearStepBlueprint (M := M) (n := n) sc).writeBit.ctx.circuit.gates ∧
    (∀ i, sc.circuit.gates ≤ ((linearStepBlueprint (M := M) (n := n) sc).nextTape i).ctx.circuit.gates) ∧
    (∀ j, sc.circuit.gates ≤ ((linearStepBlueprint (M := M) (n := n) sc).nextHead j).ctx.circuit.gates) ∧
    (∀ q, sc.circuit.gates ≤ ((linearStepBlueprint (M := M) (n := n) sc).nextState q).ctx.circuit.gates) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (linearStepBlueprint (M := M) (n := n) sc).writeBit.base_le
  · intro i
    exact ((linearStepBlueprint (M := M) (n := n) sc).nextTape i).base_le
  · intro j
    exact ((linearStepBlueprint (M := M) (n := n) sc).nextHead j).base_le
  · intro q
    exact ((linearStepBlueprint (M := M) (n := n) sc).nextState q).base_le

/--
Unified gate-budget candidate for one linear step over a fixed base circuit.

This keeps all component bounds in one place and avoids repeating arithmetic
normalization downstream.
-/
def linearStepBudget (M : TM) (n : Nat) : Nat :=
  max
    ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 5)
    ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) + 1)

/--
Expanded one-step budget aligned with `buildLinearStages_gates_le`.

Unlike `linearStepBudget` (which uses `max`), this form is purely additive and
is easier to use in polynomial domination lemmas.
-/
def linearStepBudgetExpanded (M : TM) (n : Nat) : Nat :=
  ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 5) +
  ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) + 1) +
  4 * (M.tapeLength n) +
  (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (M.tapeLength n) +
  (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (stateCard M)

/--
Append-only tape-stage assembly over one growing builder context.

The input carry is the transported `writeBit` wire. For each tape index we
append the `nextTape` gadget and record its output as a `Nat` wire index in the
current final circuit.
-/
noncomputable def buildNextTapeAllAux (sc : StraightConfig M n) :
    List (Fin (M.tapeLength n)) →
      BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit × List (Fin (M.tapeLength n) × Nat)
  | [], bc => (bc, [])
  | i :: is, bc =>
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i bc
      let rest := buildNextTapeAllAux sc is bcNext
      (rest.1, (i, (bcNext.bw.out : Nat)) :: rest.2)

lemma buildNextTapeAllAux_gates_le
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextTapeAllAux (M := M) (n := n) sc is bc).1.bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates + 4 * is.length := by
  intro is
  induction is with
  | nil =>
      intro bc
      simp [buildNextTapeAllAux]
  | cons i is ih =>
      intro bc
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i bc
      have hStep :
          bcNext.bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 4 := by
        simpa [bcNext] using buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc
      have hRest :
          (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates + 4 * is.length :=
        ih bcNext
      have hMain :
          (buildNextTapeAllAux (M := M) (n := n) sc (i :: is) bc).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates + 4 * is.length := by
        simpa [buildNextTapeAllAux, bcNext] using hRest
      calc
        (buildNextTapeAllAux (M := M) (n := n) sc (i :: is) bc).1.bw.ctx.circuit.gates
            ≤ bcNext.bw.ctx.circuit.gates + 4 * is.length := hMain
        _ = bc.bw.ctx.circuit.gates + 4 + 4 * is.length := by simpa [hStep]
        _ = bc.bw.ctx.circuit.gates + 4 * (List.length (i :: is)) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/--
Tape-stage builder started from `writeBit` in the same shared context.
-/
noncomputable def buildNextTapeAll (sc : StraightConfig M n) :
    BuiltCarry (n := n) sc.circuit × List (Fin (M.tapeLength n) × Nat) := by
  let bwWrite := buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  exact buildNextTapeAllAux (M := M) (n := n) sc (tapeIndexList M n) bc0

lemma buildNextTapeAllAux_start_le_final
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      bc.bw.ctx.circuit.gates ≤
        (buildNextTapeAllAux (M := M) (n := n) sc is bc).1.bw.ctx.circuit.gates := by
  intro is
  induction is with
  | nil =>
      intro bc
      simp [buildNextTapeAllAux]
  | cons i is ih =>
      intro bc
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i bc
      have hEq :
          bcNext.bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 4 := by
        simpa [bcNext] using buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc
      have hRest :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates :=
        ih bcNext
      calc
        bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by omega
        _ ≤ (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates := hRest
        _ = (buildNextTapeAllAux (M := M) (n := n) sc (i :: is) bc).1.bw.ctx.circuit.gates := by
              simp [buildNextTapeAllAux, bcNext]

noncomputable def buildNextTapeAllAuxLookup
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      Fin (M.tapeLength n) →
      Option (Fin (n + (buildNextTapeAllAux (M := M) (n := n) sc is bc).1.bw.ctx.circuit.gates))
  | [], _bc, _i => none
  | i0 :: is, bc, i =>
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i0 bc
      if hEq : i = i0 then
        by
          have hStart :
              bcNext.bw.ctx.circuit.gates ≤
                (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates :=
            buildNextTapeAllAux_start_le_final (M := M) (n := n) sc is bcNext
          simpa [buildNextTapeAllAux, bcNext] using
            (Option.some
              (castWireLe (n := n)
                (g := bcNext.bw.ctx.circuit.gates)
                (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
                hStart
                bcNext.bw.out))
      else
        buildNextTapeAllAuxLookup sc is bcNext i

lemma buildNextTapeAllAuxLookup_isSome_of_mem
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit)
      (i : Fin (M.tapeLength n)),
      i ∈ is →
      (buildNextTapeAllAuxLookup (M := M) (n := n) sc is bc i).isSome := by
  intro is
  induction is with
  | nil =>
      intro bc i hi
      cases hi
  | cons i0 is ih =>
      intro bc i hi
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i0 bc
      by_cases hEq : i = i0
      · subst hEq
        simp [buildNextTapeAllAuxLookup, bcNext]
      · have hiTail : i ∈ is := by simpa [hEq] using hi
        have hTail :
            (buildNextTapeAllAuxLookup (M := M) (n := n) sc is bcNext i).isSome :=
          ih bcNext i hiTail
        simpa [buildNextTapeAllAuxLookup, bcNext, hEq] using hTail

noncomputable def buildNextTapeAllLookup
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n)) :
    Option (Fin (n + (buildNextTapeAll (M := M) (n := n) sc).1.bw.ctx.circuit.gates)) := by
  let bwWrite := buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  simpa [buildNextTapeAll, bc0] using
    (buildNextTapeAllAuxLookup (M := M) (n := n) sc (tapeIndexList M n) bc0 i)

lemma buildNextTapeAllLookup_isSome
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n)) :
    (buildNextTapeAllLookup (M := M) (n := n) sc i).isSome := by
  let bwWrite := buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  have hi : i ∈ tapeIndexList M n := by
    simpa [tapeIndexList] using (List.mem_finRange i)
  simpa [buildNextTapeAllLookup, bc0] using
    (buildNextTapeAllAuxLookup_isSome_of_mem (M := M) (n := n) sc
      (is := tapeIndexList M n) (bc := bc0) i hi)

lemma buildNextTapeAll_gates_le
    (sc : StraightConfig M n) :
    (buildNextTapeAll (M := M) (n := n) sc).1.bw.ctx.circuit.gates ≤
      sc.circuit.gates +
        ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
        4 * (M.tapeLength n) := by
  unfold buildNextTapeAll
  let bwWrite := buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  have hTape :
      (buildNextTapeAllAux (M := M) (n := n) sc (tapeIndexList M n) bc0).1.bw.ctx.circuit.gates ≤
        bc0.bw.ctx.circuit.gates + 4 * (tapeIndexList M n).length :=
    buildNextTapeAllAux_gates_le (M := M) (n := n) sc (tapeIndexList M n) bc0
  have hWrite :
      bwWrite.ctx.circuit.gates ≤
        sc.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) :=
    buildWriteBit_gates_le (M := M) (n := n) sc
  have hLen : (tapeIndexList M n).length = M.tapeLength n := by
    simp [tapeIndexList]
  calc
    (buildNextTapeAllAux (M := M) (n := n) sc (tapeIndexList M n) bc0).1.bw.ctx.circuit.gates
        ≤ bc0.bw.ctx.circuit.gates + 4 * (tapeIndexList M n).length := hTape
    _ = bwWrite.ctx.circuit.gates + 4 * (tapeIndexList M n).length := by
          simp [bc0]
    _ ≤ sc.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
          4 * (tapeIndexList M n).length := by omega
    _ = sc.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
          4 * (M.tapeLength n) := by simp [hLen]

lemma buildNextTapeFromCarry_carry_eval
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n))
    (bc : BuiltCarry (n := n) sc.circuit) (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit) (x := x)
        (buildNextTapeFromCarry (M := M) (n := n) sc i bc).carry
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
  unfold buildNextTapeFromCarry
  simp

set_option maxHeartbeats 800000 in
lemma buildNextTapeFromCarry_preserves_old_eval
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit.gates)
          (by
            have hEq := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc
            omega) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  let wHead0 : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
  let bcWrite : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bc) wHead0 bc.carry
  let wHead1 : Fin (n + bcWrite.bw.ctx.circuit.gates) := bcWrite.bw.ctx.liftBase (sc.head i)
  let opNot : LegacyStraightOp (n + bcWrite.bw.ctx.circuit.gates) := .not wHead1
  let writeLiftNot :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bcWrite.bw.ctx.ctx) (op := opNot) bcWrite.bw.out
  let bcNot : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendNot (bc := bcWrite) wHead1
  let wTape2 : Fin (n + bcNot.bw.ctx.circuit.gates) := bcNot.bw.ctx.liftBase (sc.tape i)
  let opAnd : LegacyStraightOp (n + bcNot.bw.ctx.circuit.gates) := .and bcNot.bw.out wTape2
  let writeLiftAnd :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
      (b := bcNot.bw.ctx.ctx) (op := opAnd) writeLiftNot
  let bcKeep : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendAnd (bc := bcNot) bcNot.bw.out wTape2
  let bcOut : BuiltCarry (n := n) sc.circuit :=
    BuiltCarry.appendOr (bc := bcKeep) writeLiftAnd bcKeep.bw.out
  have hLe1 : bc.bw.ctx.circuit.gates ≤ bcWrite.bw.ctx.circuit.gates := by
    simp [bcWrite]
  have h1 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcWrite.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
    simpa [bcWrite] using
      (BuiltCarry_appendAnd_preserves_old_eval
        (bc := bc) (u := wHead0) (v := bc.carry) (x := x) (w := w))
  have hLe2 : bcWrite.bw.ctx.circuit.gates ≤ bcNot.bw.ctx.circuit.gates := by
    simp [bcNot]
  have h2 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcNot.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
            (g' := bcNot.bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcWrite.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w) := by
    simpa [bcNot] using
      (BuiltCarry_appendNot_preserves_old_eval
        (bc := bcWrite) (u := wHead1) (x := x)
        (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))
  have hLe3 : bcNot.bw.ctx.circuit.gates ≤ bcKeep.bw.ctx.circuit.gates := by
    simp [bcKeep]
  have h3 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcKeep.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
            (g' := bcKeep.bw.ctx.circuit.gates) hLe3
            (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
              (g' := bcNot.bw.ctx.circuit.gates) hLe2
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNot.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
              (g' := bcNot.bw.ctx.circuit.gates) hLe2
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)) := by
    change
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltCarry.appendAnd (bc := bcNot) bcNot.bw.out wTape2).bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
            (g' := (BuiltCarry.appendAnd (bc := bcNot) bcNot.bw.out wTape2).bw.ctx.circuit.gates)
            hLe3
            (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
              (g' := bcNot.bw.ctx.circuit.gates) hLe2
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)))
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcNot.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
            (g' := bcNot.bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))
    exact BuiltCarry_appendAnd_preserves_old_eval
      (bc := bcNot) (u := bcNot.bw.out) (v := wTape2) (x := x)
      (w := castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
        (g' := bcNot.bw.ctx.circuit.gates) hLe2
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))
  have hLe4 : bcKeep.bw.ctx.circuit.gates ≤ bcOut.bw.ctx.circuit.gates := by
    simp [bcOut]
  have h4 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcOut.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcKeep.bw.ctx.circuit.gates)
            (g' := bcOut.bw.ctx.circuit.gates) hLe4
            (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
              (g' := bcKeep.bw.ctx.circuit.gates) hLe3
              (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
                (g' := bcNot.bw.ctx.circuit.gates) hLe2
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcKeep.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
              (g' := bcKeep.bw.ctx.circuit.gates) hLe3
              (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
                (g' := bcNot.bw.ctx.circuit.gates) hLe2
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))) := by
    change
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltCarry.appendOr (bc := bcKeep) writeLiftAnd bcKeep.bw.out).bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcKeep.bw.ctx.circuit.gates)
            (g' := (BuiltCarry.appendOr (bc := bcKeep) writeLiftAnd bcKeep.bw.out).bw.ctx.circuit.gates)
            hLe4
            (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
              (g' := bcKeep.bw.ctx.circuit.gates) hLe3
              (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
                (g' := bcNot.bw.ctx.circuit.gates) hLe2
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))))
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcKeep.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
            (g' := bcKeep.bw.ctx.circuit.gates) hLe3
            (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
              (g' := bcNot.bw.ctx.circuit.gates) hLe2
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)))
    exact BuiltCarry_appendOr_preserves_old_eval
      (bc := bcKeep) (u := writeLiftAnd) (v := bcKeep.bw.out) (x := x)
      (w := castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
        (g' := bcKeep.bw.ctx.circuit.gates) hLe3
        (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
          (g' := bcNot.bw.ctx.circuit.gates) hLe2
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)))
  have hCast :
      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
        (g' := bcOut.bw.ctx.circuit.gates)
        (Nat.le_trans hLe1 (Nat.le_trans hLe2 (Nat.le_trans hLe3 hLe4))) w
      =
      castWireLe (n := n) (g := bcKeep.bw.ctx.circuit.gates)
        (g' := bcOut.bw.ctx.circuit.gates) hLe4
        (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
          (g' := bcKeep.bw.ctx.circuit.gates) hLe3
          (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
            (g' := bcNot.bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))) := by
    rw [← castWireLe_trans, ← castWireLe_trans, ← castWireLe_trans]
  have hEq :
      buildNextTapeFromCarry (M := M) (n := n) sc i bc = bcOut := by
    simp [buildNextTapeFromCarry, wHead0, bcWrite, wHead1, opNot, writeLiftNot,
      bcNot, wTape2, opAnd, writeLiftAnd, bcKeep, bcOut]
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit.gates)
          (by
            have hEq' := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc
            omega) w)
      =
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcOut.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcOut.bw.ctx.circuit.gates)
          (Nat.le_trans hLe1 (Nat.le_trans hLe2 (Nat.le_trans hLe3 hLe4))) w) := by
            have hproof :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit.gates)
                  (by
                    have hEq' := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc
                    omega) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcOut.bw.ctx.circuit.gates)
                  (Nat.le_trans hLe1 (Nat.le_trans hLe2 (Nat.le_trans hLe3 hLe4))) w := by
              simpa [hEq] using
                (castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcOut.bw.ctx.circuit.gates)
                  (h₁ := by
                    have hEq' := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc
                    omega)
                  (h₂ := Nat.le_trans hLe1 (Nat.le_trans hLe2 (Nat.le_trans hLe3 hLe4))) w)
            cases hEq
            exact hproof ▸ rfl
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcOut.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcKeep.bw.ctx.circuit.gates)
          (g' := bcOut.bw.ctx.circuit.gates) hLe4
          (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
            (g' := bcKeep.bw.ctx.circuit.gates) hLe3
            (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
              (g' := bcNot.bw.ctx.circuit.gates) hLe2
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)))) := by
                rw [hCast]
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcKeep.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcNot.bw.ctx.circuit.gates)
          (g' := bcKeep.bw.ctx.circuit.gates) hLe3
          (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
            (g' := bcNot.bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w))) := h4
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcNot.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcWrite.bw.ctx.circuit.gates)
          (g' := bcNot.bw.ctx.circuit.gates) hLe2
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w)) := h3
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcWrite.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcWrite.bw.ctx.circuit.gates) hLe1 w) := h2
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) w := h1

lemma buildNextTapeAllAux_preserves_old_eval
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit)
      (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (buildNextTapeAllAux (M := M) (n := n) sc is bc).1.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bc).1.bw.ctx.circuit.gates)
            (buildNextTapeAllAux_start_le_final (M := M) (n := n) sc is bc) w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
  intro is
  induction is with
  | nil =>
      intro bc x w
      simpa [buildNextTapeAllAux, castWireLe]
  | cons i0 is ih =>
      intro bc x w
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i0 bc
      have hEqNext : bcNext.bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 4 := by
        simpa [bcNext] using buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i0 bc
      have hNextLe : bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        omega
      have hTailLe :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates :=
        buildNextTapeAllAux_start_le_final (M := M) (n := n) sc is bcNext
      have hTail :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
                (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
                hTailLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        simpa using ih bcNext x
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
      have hStepRaw :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates)
                (by
                  have hEq := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i0 bc
                  omega) w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        simpa [bcNext] using
          (buildNextTapeFromCarry_preserves_old_eval
            (M := M) (n := n) sc i0 bc x w)
      have hStep :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        have hCast :
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w
            =
              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates)
                (by
                  have hEq := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i0 bc
                  omega) w := by
          exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe
            (by
              have hEq := buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i0 bc
              omega) w
        simpa [hCast] using hStepRaw
      have hCastTail :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
            (buildNextTapeAllAux_start_le_final (M := M) (n := n) sc (i0 :: is) bc) w
          =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
            (buildNextTapeAllAux_start_le_final (M := M) (n := n) sc (i0 :: is) bc) w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe hTailLe) w := by
                simp [buildNextTapeAllAux, bcNext]
          _ =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
                  simp [castWireLe_trans]
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextTapeAllAux (M := M) (n := n) sc (i0 :: is) bc).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextTapeAllAux (M := M) (n := n) sc (i0 :: is) bc).1.bw.ctx.circuit.gates)
              (buildNextTapeAllAux_start_le_final (M := M) (n := n) sc (i0 :: is) bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
              (buildNextTapeAllAux_start_le_final (M := M) (n := n) sc (i0 :: is) bc) w) := by
                simp [buildNextTapeAllAux, bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  rw [hCastTail]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := hTail
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := hStep

/--
Append-only head-stage assembly over one growing builder context.

For each target head index we append the full `nextHead` gadget from the
current context and record its output wire index.
-/
noncomputable def buildNextHeadAllAux (sc : StraightConfig M n) :
    List (Fin (M.tapeLength n)) →
      BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit × List (Fin (M.tapeLength n) × Nat)
  | [], bc => (bc, [])
  | j :: js, bc =>
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      let rest := buildNextHeadAllAux sc js bcNext
      (rest.1, (j, (bcHead.bw.out : Nat)) :: rest.2)

lemma buildNextHeadAllAux_gates_le
    (sc : StraightConfig M n) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates +
          (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * js.length := by
  intro js
  induction js with
  | nil =>
      intro bc
      simp [buildNextHeadAllAux]
  | cons j js ih =>
      intro bc
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      have hHeadStep :
          bcHead.bw.ctx.circuit.gates ≤
            bc.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) + 1) := by
        have hRaw := buildNextHeadAux_gates_le (M := M) (n := n) (sc := sc) (j := j)
            (iqs := headStateSymbolPairs M n) (bc := bc0)
        have hLen : (headStateSymbolPairs M n).length = (M.tapeLength n) * (2 * stateCard M) :=
          length_headStateSymbolPairs (M := M) (n := n)
        have hRaw' : bcHead.bw.ctx.circuit.gates ≤
            bc0.bw.ctx.circuit.gates +
              (2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) := by
          simpa [bcHead, hLen] using hRaw
        have h0 : bc0.bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 1 := by
          simp [bc0, bcReset]
        omega
      have hRest :
          (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * js.length :=
        ih bcNext
      have hMain :
          (buildNextHeadAllAux (M := M) (n := n) sc (j :: js) bc).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * js.length := by
        simpa [buildNextHeadAllAux, bcReset, bc0, bcHead, bcNext] using hRest
      calc
        (buildNextHeadAllAux (M := M) (n := n) sc (j :: js) bc).1.bw.ctx.circuit.gates
            ≤ bcNext.bw.ctx.circuit.gates +
                (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * js.length := hMain
        _ = bcHead.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * js.length := by
              simp [bcNext]
        _ ≤ bc.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) + 1) +
              (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * js.length := by
              omega
        _ = bc.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (List.length (j :: js)) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma buildSymbolFromCarry_start_le
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      bc.bw.ctx.circuit.gates ≤
        (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.ctx.circuit.gates := by
  intro is
  induction is with
  | nil =>
      intro bc
      simp [buildSymbolFromCarry]
  | cons i is ih =>
      intro bc
      let u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
      let v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
      let bcAnd := BuiltCarry.appendAnd (bc := bc) u v
      let symLiftAnd :=
        Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
          (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.and u v) bc.bw.out
      let bcOr := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
      have hAnd : bc.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := by
        simp [bcAnd]
      have hOr : bcAnd.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
        simp [bcOr]
      have hRest :
          bcOr.bw.ctx.circuit.gates ≤
            (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates :=
        ih bcOr
      calc
        bc.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := hAnd
        _ ≤ bcOr.bw.ctx.circuit.gates := hOr
        _ ≤ (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates := hRest
        _ = (buildSymbolFromCarry (M := M) (n := n) sc (i :: is) bc).bw.ctx.circuit.gates := by
              simp [buildSymbolFromCarry, bcAnd, bcOr, symLiftAnd, u, v]

lemma buildSymbolFromCarry_preserves_old_eval
    (sc : StraightConfig M n) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit)
      (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bc).bw.ctx.circuit.gates)
            (buildSymbolFromCarry_start_le (M := M) (n := n) sc is bc) w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
  intro is
  induction is with
  | nil =>
      intro bc x w
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildSymbolFromCarry (M := M) (n := n) sc [] bc).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc [] bc).bw.ctx.circuit.gates)
              (buildSymbolFromCarry_start_le (M := M) (n := n) sc [] bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc.bw.ctx.circuit.gates) (Nat.le_refl _) w) := by
                simp [buildSymbolFromCarry]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
              simp [castWireLe]
  | cons i is ih =>
      intro bc x w
      let u : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.head i)
      let v : Fin (n + bc.bw.ctx.circuit.gates) := bc.bw.ctx.liftBase (sc.tape i)
      let bcAnd := BuiltCarry.appendAnd (bc := bc) u v
      let symLiftAnd :=
        Pnp3.Internal.PsubsetPpoly.StraightLine.BuildCtx.appendFin_lift
          (b := bc.bw.ctx.ctx) (op := LegacyStraightOp.and u v) bc.bw.out
      let bcOr := BuiltCarry.appendOr (bc := bcAnd) symLiftAnd bcAnd.bw.out
      have hAnd : bc.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := by
        simp [bcAnd]
      have hOr : bcAnd.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
        simp [bcOr]
      have hStep :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates)
                (Nat.le_trans hAnd hOr) w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        simpa [u, v, bcAnd, symLiftAnd, bcOr] using
          (buildSymbolFromCarry_step_preserves_old_eval (M := M) (n := n) sc bc i x w)
      have hTailLe :
          bcOr.bw.ctx.circuit.gates ≤
            (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates :=
        buildSymbolFromCarry_start_le (M := M) (n := n) sc is bcOr
      have hTail :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
                (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
                hTailLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcOr.bw.ctx.circuit.gates)
                  (Nat.le_trans hAnd hOr) w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcOr.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcOr.bw.ctx.circuit.gates)
                  (Nat.le_trans hAnd hOr) w) := by
        simpa using ih bcOr x
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcOr.bw.ctx.circuit.gates)
            (Nat.le_trans hAnd hOr) w)
      have hCast :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
            (buildSymbolFromCarry_start_le (M := M) (n := n) sc (i :: is) bc) w
          =
            castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates)
                (Nat.le_trans hAnd hOr) w) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
            (buildSymbolFromCarry_start_le (M := M) (n := n) sc (i :: is) bc) w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
              (Nat.le_trans (Nat.le_trans hAnd hOr) hTailLe) w := by
                simp
          _ =
            castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates)
                (Nat.le_trans hAnd hOr) w) := by
                  simp [castWireLe_trans]
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildSymbolFromCarry (M := M) (n := n) sc (i :: is) bc).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc (i :: is) bc).bw.ctx.circuit.gates)
              (buildSymbolFromCarry_start_le (M := M) (n := n) sc (i :: is) bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
              (buildSymbolFromCarry_start_le (M := M) (n := n) sc (i :: is) bc) w) := by
                simp [buildSymbolFromCarry, u, v, bcAnd, symLiftAnd, bcOr]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := (buildSymbolFromCarry (M := M) (n := n) sc is bcOr).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates)
                (Nat.le_trans hAnd hOr) w)) := by
                  rw [hCast]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcOr.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcOr.bw.ctx.circuit.gates)
              (Nat.le_trans hAnd hOr) w) := hTail
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := hStep

lemma buildBranchFromCarry_start_le
    (sc : StraightConfig M n) (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    bc.bw.ctx.circuit.gates ≤
      (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates := by
  unfold buildBranchFromCarry
  dsimp
  let bcStart := BuiltCarry.appendConst (bc := bc) false
  let bcSym := buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart
  have hStart : bc.bw.ctx.circuit.gates ≤ bcStart.bw.ctx.circuit.gates := by
    simp [bcStart]
  have hSym : bcStart.bw.ctx.circuit.gates ≤ bcSym.bw.ctx.circuit.gates :=
    buildSymbolFromCarry_start_le (M := M) (n := n) sc (tapeIndexList M n) bcStart
  by_cases hbit : qs.2
  · simp [hbit, bcStart, bcSym] at *
    omega
  · set bcGuard : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out
    have hGuard : bcSym.bw.ctx.circuit.gates ≤ bcGuard.bw.ctx.circuit.gates := by
      simp [bcGuard]
    have hAll : bc.bw.ctx.circuit.gates ≤ bcGuard.bw.ctx.circuit.gates := by
      exact le_trans (le_trans hStart hSym) hGuard
    simp [hbit, bcStart, bcSym, bcGuard] at *
    omega

set_option maxHeartbeats 800000 in
private lemma buildBranchFromCarry_true_preserves_old_eval
    (sc : StraightConfig M n)
    (q : M.state)
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc (q, true) bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildBranchFromCarry (M := M) (n := n) sc (q, true) bc).bw.ctx.circuit.gates)
          (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, true) bc) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  let bcStart := BuiltCarry.appendConst (bc := bc) false
  let bcSym := buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart
  let bcFinal : BuiltCarry (n := n) sc.circuit :=
    BuiltCarry.appendAnd (bc := bcSym) (bcSym.bw.ctx.liftBase (sc.state q)) bcSym.bw.out
  have hLe0 : bc.bw.ctx.circuit.gates ≤ bcStart.bw.ctx.circuit.gates := by
    simp [bcStart]
  have h0 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcStart.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
    simpa [bcStart] using
      (BuiltCarry_appendConst_preserves_old_eval
        (bc := bc) (val := false) (x := x) (w := w))
  have hLe1 : bcStart.bw.ctx.circuit.gates ≤ bcSym.bw.ctx.circuit.gates :=
    buildSymbolFromCarry_start_le (M := M) (n := n) sc (tapeIndexList M n) bcStart
  have h1 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcSym.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcStart.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w) := by
    simpa [bcStart, bcSym] using
      (buildSymbolFromCarry_preserves_old_eval (M := M) (n := n) sc
        (is := tapeIndexList M n) (bc := bcStart) (x := x)
        (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
  have hLe2 : bcSym.bw.ctx.circuit.gates ≤ bcFinal.bw.ctx.circuit.gates := by
    simp [bcFinal]
  have h2 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcFinal.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
            (g' := bcFinal.bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcSym.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)) := by
    change
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltCarry.appendAnd (bc := bcSym) (bcSym.bw.ctx.liftBase (sc.state q)) bcSym.bw.out).bw.ctx.circuit)
          (x := x)
          (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
            (g' := (BuiltCarry.appendAnd (bc := bcSym) (bcSym.bw.ctx.liftBase (sc.state q)) bcSym.bw.out).bw.ctx.circuit.gates)
            hLe2
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcSym.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
    exact BuiltCarry_appendAnd_preserves_old_eval
      (bc := bcSym) (u := bcSym.bw.ctx.liftBase (sc.state q)) (v := bcSym.bw.out)
      (x := x)
      (w := castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
        (g' := bcSym.bw.ctx.circuit.gates) hLe1
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
  have hCast :
      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
        (g' := bcFinal.bw.ctx.circuit.gates)
        (Nat.le_trans hLe0 (Nat.le_trans hLe1 hLe2)) w
      =
      castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
        (g' := bcFinal.bw.ctx.circuit.gates) hLe2
        (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
          (g' := bcSym.bw.ctx.circuit.gates) hLe1
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)) := by
    rw [← castWireLe_trans, ← castWireLe_trans]
  have hEq :
      buildBranchFromCarry (M := M) (n := n) sc (q, true) bc = bcFinal := by
    simp [buildBranchFromCarry, bcStart, bcSym, bcFinal]
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc (q, true) bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildBranchFromCarry (M := M) (n := n) sc (q, true) bc).bw.ctx.circuit.gates)
          (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, true) bc) w)
      =
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          (Nat.le_trans hLe0 (Nat.le_trans hLe1 hLe2)) w) := by
            have hproof :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildBranchFromCarry (M := M) (n := n) sc (q, true) bc).bw.ctx.circuit.gates)
                  (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, true) bc) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcFinal.bw.ctx.circuit.gates)
                  (Nat.le_trans hLe0 (Nat.le_trans hLe1 hLe2)) w := by
              simpa [hEq] using
                (castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcFinal.bw.ctx.circuit.gates)
                  (h₁ := by simpa [hEq] using
                    (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, true) bc))
                  (h₂ := Nat.le_trans hLe0 (Nat.le_trans hLe1 hLe2)) w)
            cases hEq
            exact hproof ▸ rfl
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates) hLe2
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))) := by
                rw [hCast]
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcSym.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
          (g' := bcSym.bw.ctx.circuit.gates) hLe1
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)) := h2
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcStart.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcStart.bw.ctx.circuit.gates) hLe0 w) := h1
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) w := h0

set_option maxHeartbeats 800000 in
private lemma buildBranchFromCarry_false_preserves_old_eval
    (sc : StraightConfig M n)
    (q : M.state)
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc (q, false) bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildBranchFromCarry (M := M) (n := n) sc (q, false) bc).bw.ctx.circuit.gates)
          (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, false) bc) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  let bcStart := BuiltCarry.appendConst (bc := bc) false
  let bcSym := buildSymbolFromCarry (M := M) (n := n) sc (tapeIndexList M n) bcStart
  let bcGuard : BuiltCarry (n := n) sc.circuit := BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out
  let bcFinal : BuiltCarry (n := n) sc.circuit :=
    BuiltCarry.appendAnd (bc := bcGuard) (bcGuard.bw.ctx.liftBase (sc.state q)) bcGuard.bw.out
  have hLe0 : bc.bw.ctx.circuit.gates ≤ bcStart.bw.ctx.circuit.gates := by
    simp [bcStart]
  have h0 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcStart.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
    simpa [bcStart] using
      (BuiltCarry_appendConst_preserves_old_eval
        (bc := bc) (val := false) (x := x) (w := w))
  have hLe1 : bcStart.bw.ctx.circuit.gates ≤ bcSym.bw.ctx.circuit.gates :=
    buildSymbolFromCarry_start_le (M := M) (n := n) sc (tapeIndexList M n) bcStart
  have h1 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcSym.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcStart.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w) := by
    simpa [bcStart, bcSym] using
      (buildSymbolFromCarry_preserves_old_eval (M := M) (n := n) sc
        (is := tapeIndexList M n) (bc := bcStart) (x := x)
        (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
  have hLeGuard : bcSym.bw.ctx.circuit.gates ≤ bcGuard.bw.ctx.circuit.gates := by
    simp [bcGuard]
  have hGuard :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcGuard.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
            (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcSym.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)) := by
    change
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out).bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
            (g' := (BuiltCarry.appendNot (bc := bcSym) bcSym.bw.out).bw.ctx.circuit.gates) hLeGuard
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcSym.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
    exact BuiltCarry_appendNot_preserves_old_eval
      (bc := bcSym) (u := bcSym.bw.out) (x := x)
      (w := castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
        (g' := bcSym.bw.ctx.circuit.gates) hLe1
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))
  have hLe2 : bcGuard.bw.ctx.circuit.gates ≤ bcFinal.bw.ctx.circuit.gates := by
    simp [bcFinal]
  have h2 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcFinal.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcGuard.bw.ctx.circuit.gates)
            (g' := bcFinal.bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
              (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
              (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
                (g' := bcSym.bw.ctx.circuit.gates) hLe1
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcGuard.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
              (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
              (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
                (g' := bcSym.bw.ctx.circuit.gates) hLe1
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))) := by
    change
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltCarry.appendAnd (bc := bcGuard) (bcGuard.bw.ctx.liftBase (sc.state q)) bcGuard.bw.out).bw.ctx.circuit)
          (x := x)
          (castWireLe (n := n) (g := bcGuard.bw.ctx.circuit.gates)
            (g' := (BuiltCarry.appendAnd (bc := bcGuard) (bcGuard.bw.ctx.liftBase (sc.state q)) bcGuard.bw.out).bw.ctx.circuit.gates) hLe2
            (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
              (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
              (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
                (g' := bcSym.bw.ctx.circuit.gates) hLe1
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))))
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcGuard.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
            (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))
    exact BuiltCarry_appendAnd_preserves_old_eval
      (bc := bcGuard) (u := bcGuard.bw.ctx.liftBase (sc.state q)) (v := bcGuard.bw.out)
      (x := x)
      (w := castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
        (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
        (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
          (g' := bcSym.bw.ctx.circuit.gates) hLe1
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))
  have hCast :
      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
        (g' := bcFinal.bw.ctx.circuit.gates)
        (Nat.le_trans hLe0 (Nat.le_trans hLe1 (Nat.le_trans hLeGuard hLe2))) w
      =
      castWireLe (n := n) (g := bcGuard.bw.ctx.circuit.gates)
        (g' := bcFinal.bw.ctx.circuit.gates) hLe2
        (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
          (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))) := by
    rw [← castWireLe_trans, ← castWireLe_trans, ← castWireLe_trans]
  have hEq :
      buildBranchFromCarry (M := M) (n := n) sc (q, false) bc = bcFinal := by
    simp [buildBranchFromCarry, bcStart, bcSym, bcGuard, bcFinal]
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc (q, false) bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildBranchFromCarry (M := M) (n := n) sc (q, false) bc).bw.ctx.circuit.gates)
          (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, false) bc) w)
      =
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          (Nat.le_trans hLe0 (Nat.le_trans hLe1 (Nat.le_trans hLeGuard hLe2))) w) := by
            have hproof :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildBranchFromCarry (M := M) (n := n) sc (q, false) bc).bw.ctx.circuit.gates)
                  (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, false) bc) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcFinal.bw.ctx.circuit.gates)
                  (Nat.le_trans hLe0 (Nat.le_trans hLe1 (Nat.le_trans hLeGuard hLe2))) w := by
              simpa [hEq] using
                (castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcFinal.bw.ctx.circuit.gates)
                  (h₁ := by simpa [hEq] using
                    (buildBranchFromCarry_start_le (M := M) (n := n) sc (q, false) bc))
                  (h₂ := Nat.le_trans hLe0 (Nat.le_trans hLe1 (Nat.le_trans hLeGuard hLe2))) w)
            cases hEq
            exact hproof ▸ rfl
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcGuard.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates) hLe2
          (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
            (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
            (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
              (g' := bcSym.bw.ctx.circuit.gates) hLe1
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)))) := by
                rw [hCast]
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcGuard.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcSym.bw.ctx.circuit.gates)
          (g' := bcGuard.bw.ctx.circuit.gates) hLeGuard
          (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
            (g' := bcSym.bw.ctx.circuit.gates) hLe1
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcStart.bw.ctx.circuit.gates) hLe0 w))) := h2
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcSym.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bcStart.bw.ctx.circuit.gates)
          (g' := bcSym.bw.ctx.circuit.gates) hLe1
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcStart.bw.ctx.circuit.gates) hLe0 w)) := hGuard
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcStart.bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := bcStart.bw.ctx.circuit.gates) hLe0 w) := h1
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) w := h0

lemma buildBranchFromCarry_preserves_old_eval
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
          (buildBranchFromCarry_start_le (M := M) (n := n) sc qs bc) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  rcases qs with ⟨q, b⟩
  cases b with
  | false =>
      simpa using buildBranchFromCarry_false_preserves_old_eval
        (M := M) (n := n) sc q bc x w
  | true =>
      simpa using buildBranchFromCarry_true_preserves_old_eval
        (M := M) (n := n) sc q bc x w

lemma buildHeadTermFromCarry_start_le
    (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit) :
    bc.bw.ctx.circuit.gates ≤
      (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates := by
  cases hstep : M.step iqs.2.1 iqs.2.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hmv : moveIndex (M := M) (n := n) iqs.1 mv = j
          · set bcBranch : BuiltCarry (n := n) sc.circuit :=
              buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc
            have hBranch : bc.bw.ctx.circuit.gates ≤ bcBranch.bw.ctx.circuit.gates :=
              buildBranchFromCarry_start_le (M := M) (n := n) sc iqs.2 bc
            have hFinal :
                bcBranch.bw.ctx.circuit.gates ≤
                  (BuiltCarry.appendAnd (bc := bcBranch)
                    (bcBranch.bw.ctx.liftBase (sc.head iqs.1))
                    bcBranch.bw.out).bw.ctx.circuit.gates := by
              simp
            simpa [buildHeadTermFromCarry, hstep, hmv, bcBranch] using
              (le_trans hBranch hFinal)
          · have hEq :
                bc.bw.ctx.circuit.gates ≤ (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
              simp
            have hFinal :
                bc.bw.ctx.circuit.gates ≤
                (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates := by
              simpa [buildHeadTermFromCarry, hstep, hmv] using hEq
            exact hFinal

lemma buildHeadTermFromCarry_preserves_old_eval
    (sc : StraightConfig M n)
    (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
          (buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  cases hstep : M.step iqs.2.1 iqs.2.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hmv : moveIndex (M := M) (n := n) iqs.1 mv = j
          · let bcBranch : BuiltCarry (n := n) sc.circuit :=
              buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc
            let bcAnd : BuiltCarry (n := n) sc.circuit :=
              BuiltCarry.appendAnd
                (bc := bcBranch)
                (bcBranch.bw.ctx.liftBase (sc.head iqs.1))
                bcBranch.bw.out
            have hLeBranch : bc.bw.ctx.circuit.gates ≤ bcBranch.bw.ctx.circuit.gates := by
              simpa [bcBranch] using
                (buildBranchFromCarry_start_le (M := M) (n := n) sc iqs.2 bc)
            have hLeAnd : bcBranch.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := by
              simp [bcAnd]
            have hLeHead :
                bc.bw.ctx.circuit.gates ≤
                  (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates := by
              simpa [buildHeadTermFromCarry, hstep, hmv, bcBranch, bcAnd] using
                (Nat.le_trans hLeBranch hLeAnd)
            have hCastHead :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                  (buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                  hLeHead w := by
              exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                (h₁ := buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc)
                (h₂ := hLeHead) w
            have hBranch :
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bcBranch.bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w)
                  =
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bc.bw.ctx.circuit) (x := x) w := by
              simpa [bcBranch] using
                (buildBranchFromCarry_preserves_old_eval
                  (M := M) (n := n) sc iqs.2 bc x w)
            have hAnd :
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bcAnd.bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bcBranch.bw.ctx.circuit.gates)
                      (g' := bcAnd.bw.ctx.circuit.gates) hLeAnd
                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w))
                  =
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bcBranch.bw.ctx.circuit) (x := x)
                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w) := by
              change
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := (BuiltCarry.appendAnd
                      (bc := bcBranch)
                      (bcBranch.bw.ctx.liftBase (sc.head iqs.1))
                      bcBranch.bw.out).bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bcBranch.bw.ctx.circuit.gates)
                      (g' := (BuiltCarry.appendAnd
                        (bc := bcBranch)
                        (bcBranch.bw.ctx.liftBase (sc.head iqs.1))
                        bcBranch.bw.out).bw.ctx.circuit.gates) hLeAnd
                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w))
                  =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bcBranch.bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w)
              exact BuiltCarry_appendAnd_preserves_old_eval
                (bc := bcBranch)
                (u := bcBranch.bw.ctx.liftBase (sc.head iqs.1))
                (v := bcBranch.bw.out)
                (x := x)
                (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w)
            have hCastTrans :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcAnd.bw.ctx.circuit.gates)
                  (Nat.le_trans hLeBranch hLeAnd) w
              =
                castWireLe (n := n) (g := bcBranch.bw.ctx.circuit.gates)
                  (g' := bcAnd.bw.ctx.circuit.gates) hLeAnd
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w) := by
              simp [castWireLe_trans]
            have hMain :
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                      (buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc) w)
                  =
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bc.bw.ctx.circuit) (x := x) w := by
              have hSome :
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bcAnd.bw.ctx.circuit) (x := x)
                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := bcAnd.bw.ctx.circuit.gates)
                        (Nat.le_trans hLeBranch hLeAnd) w)
                    =
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                        (C := bc.bw.ctx.circuit) (x := x) w := by
                calc
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bcAnd.bw.ctx.circuit) (x := x)
                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := bcAnd.bw.ctx.circuit.gates)
                        (Nat.le_trans hLeBranch hLeAnd) w)
                    =
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bcAnd.bw.ctx.circuit) (x := x)
                      (castWireLe (n := n) (g := bcBranch.bw.ctx.circuit.gates)
                        (g' := bcAnd.bw.ctx.circuit.gates) hLeAnd
                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                          (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w)) := by
                            rw [hCastTrans]
                  _ =
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bcBranch.bw.ctx.circuit) (x := x)
                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := bcBranch.bw.ctx.circuit.gates) hLeBranch w) := hAnd
                  _ =
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bc.bw.ctx.circuit) (x := x) w := hBranch
              have hstep6 : M.6 iqs.2.1 iqs.2.2 = (qn, wr, mv) := by
                simpa [TM.step] using hstep
              calc
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                      (buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc) w)
                  =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                      hLeHead w) := by
                        rw [hCastHead]
                _ =
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bcAnd.bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := bcAnd.bw.ctx.circuit.gates)
                      (Nat.le_trans hLeBranch hLeAnd) w) := by
                        by_cases hCase :
                            moveIndex (M := M) (n := n) iqs.1 (M.step iqs.2.1 iqs.2.2).2.2 = j
                        · have hCase6 :
                              moveIndex (M := M) (n := n) iqs.1 (M.6 iqs.2.1 iqs.2.2).2.2 = j := by
                            change moveIndex (M := M) (n := n) iqs.1
                              (M.step iqs.2.1 iqs.2.2).2.2 = j
                            exact hCase
                          have hCircEq :
                              (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit
                                = bcAnd.bw.ctx.circuit := by
                            simpa [buildHeadTermFromCarry, hCase6, bcBranch, bcAnd]
                          have hLeHead' :
                              bc.bw.ctx.circuit.gates ≤ bcAnd.bw.ctx.circuit.gates := by
                            simpa [hCircEq] using hLeHead
                          have hEvalRewrite :
                              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                  (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                    (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                                    hLeHead w)
                                =
                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                    (C := bcAnd.bw.ctx.circuit) (x := x)
                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                      (g' := bcAnd.bw.ctx.circuit.gates) hLeHead' w) := by
                            exact evalWire_congr_castWireLe
                              (n := n) (g := bc.bw.ctx.circuit.gates)
                              (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit)
                              (C' := bcAnd.bw.ctx.circuit)
                              hCircEq x hLeHead hLeHead' w
                          have hCastEq :
                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                (g' := bcAnd.bw.ctx.circuit.gates) hLeHead' w
                            =
                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                (g' := bcAnd.bw.ctx.circuit.gates)
                                (Nat.le_trans hLeBranch hLeAnd) w := by
                            exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                              (g' := bcAnd.bw.ctx.circuit.gates)
                              (h₁ := hLeHead')
                              (h₂ := Nat.le_trans hLeBranch hLeAnd) w
                          calc
                            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                  (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                                  hLeHead w)
                              =
                            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                (C := bcAnd.bw.ctx.circuit) (x := x)
                                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                  (g' := bcAnd.bw.ctx.circuit.gates) hLeHead' w) := hEvalRewrite
                            _ =
                              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                (C := bcAnd.bw.ctx.circuit) (x := x)
                                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                  (g' := bcAnd.bw.ctx.circuit.gates)
                                  (Nat.le_trans hLeBranch hLeAnd) w) := by
                                    simpa [hCastEq]
                        · exfalso
                          apply hCase
                          simpa [hstep] using hmv
                _ =
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := bc.bw.ctx.circuit) (x := x) w := hSome
            exact hMain
          · have hLeConst :
                bc.bw.ctx.circuit.gates ≤ (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
              simp
            have hLeHead :
                bc.bw.ctx.circuit.gates ≤
                  (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates := by
              simpa [buildHeadTermFromCarry, hstep, hmv] using hLeConst
            have hCastHead :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                  (buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                  hLeHead w := by
              exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                (h₁ := buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc)
                (h₂ := hLeHead) w
            have hRaw :
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit) (x := x)
                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                      hLeConst w)
                  =
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := bc.bw.ctx.circuit) (x := x) w := by
              simpa using
                (BuiltCarry_appendConst_preserves_old_eval
                  (bc := bc) (val := false) (x := x) (w := w))
            calc
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                    (buildHeadTermFromCarry_start_le (M := M) (n := n) sc j iqs bc) w)
                =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
                    hLeHead w) := by
                      rw [hCastHead]
              _ =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                    hLeConst w) := by
                      simpa [buildHeadTermFromCarry, hstep, hmv] using rfl
              _ =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) w := hRaw

lemma buildNextHeadAux_start_le
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n)) :
    ∀ (iqs : List (Fin (M.tapeLength n) × (M.state × Bool)))
      (bc : BuiltCarry (n := n) sc.circuit),
      bc.bw.ctx.circuit.gates ≤
        (buildNextHeadAux (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates := by
  intro iqs
  induction iqs with
  | nil =>
      intro bc
      simp [buildNextHeadAux]
  | cons a t ih =>
      intro bc
      let bcTerm := buildHeadTermFromCarry (M := M) (n := n) sc j a bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hTerm : bc.bw.ctx.circuit.gates ≤ bcTerm.bw.ctx.circuit.gates :=
        buildHeadTermFromCarry_start_le (M := M) (n := n) sc j a bc
      have hOr : bcTerm.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
        simp [bcOr]
      have hRest : bcNext.bw.ctx.circuit.gates ≤
          (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates :=
        ih bcNext
      calc
        bc.bw.ctx.circuit.gates ≤ bcTerm.bw.ctx.circuit.gates := hTerm
        _ ≤ bcOr.bw.ctx.circuit.gates := hOr
        _ = bcNext.bw.ctx.circuit.gates := by simp [bcNext]
        _ ≤ (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates := hRest
        _ = (buildNextHeadAux (M := M) (n := n) sc j (a :: t) bc).bw.ctx.circuit.gates := by
              simp [buildNextHeadAux, bcTerm, bcOr, bcNext]

lemma buildNextHeadAux_preserves_old_eval
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n)) :
    ∀ (iqs : List (Fin (M.tapeLength n) × (M.state × Bool)))
      (bc : BuiltCarry (n := n) sc.circuit)
      (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (buildNextHeadAux (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextHeadAux (M := M) (n := n) sc j iqs bc).bw.ctx.circuit.gates)
            (buildNextHeadAux_start_le (M := M) (n := n) sc j iqs bc) w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
  intro iqs
  induction iqs with
  | nil =>
      intro bc x w
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAux (M := M) (n := n) sc j [] bc).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j [] bc).bw.ctx.circuit.gates)
              (buildNextHeadAux_start_le (M := M) (n := n) sc j [] bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc.bw.ctx.circuit.gates) (Nat.le_refl _) w) := by
                simp [buildNextHeadAux]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
              simp [castWireLe]
  | cons a t ih =>
      intro bc x w
      let bcTerm := buildHeadTermFromCarry (M := M) (n := n) sc j a bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hTermLe : bc.bw.ctx.circuit.gates ≤ bcTerm.bw.ctx.circuit.gates :=
        buildHeadTermFromCarry_start_le (M := M) (n := n) sc j a bc
      have hOrLe : bcTerm.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
        simp [bcOr]
      have hNextLe : bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        simpa [bcNext] using Nat.le_trans hTermLe hOrLe
      have hTerm :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        simpa [bcTerm] using
          (buildHeadTermFromCarry_preserves_old_eval
            (M := M) (n := n) sc j a bc x w)
      have hOr :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcTerm.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w) := by
        simpa [bcOr] using
          (BuiltCarry_appendOr_preserves_old_eval (bc := bcTerm)
            (u := bcTerm.carry) (v := bcTerm.bw.out) (x := x)
            (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w))
      have hTailLe :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates :=
        buildNextHeadAux_start_le (M := M) (n := n) sc j t bcNext
      have hTail :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
                (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
                hTailLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        simpa using ih bcNext x
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
      have hCastOr :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w
          =
            castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates)
              (Nat.le_trans hTermLe hOrLe) w := by
                simp [bcNext]
          _ =
            castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)) := by
                    simp [castWireLe_trans]
      have hCast :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
            (buildNextHeadAux_start_le (M := M) (n := n) sc j (a :: t) bc) w
          =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
            (buildNextHeadAux_start_le (M := M) (n := n) sc j (a :: t) bc) w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe hTailLe) w := by
                simp [bcTerm, bcOr, bcNext]
          _ =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
                  simp [castWireLe_trans]
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAux (M := M) (n := n) sc j (a :: t) bc).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j (a :: t) bc).bw.ctx.circuit.gates)
              (buildNextHeadAux_start_le (M := M) (n := n) sc j (a :: t) bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
              (buildNextHeadAux_start_le (M := M) (n := n) sc j (a :: t) bc) w) := by
                simp [buildNextHeadAux, bcTerm, bcOr, bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAux (M := M) (n := n) sc j t bcNext).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  rw [hCast]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := hTail
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w))) := by
                    rw [hCastOr]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcOr.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
              (g' := bcOr.bw.ctx.circuit.gates) hOrLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)) := by
                  simp [bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcTerm.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w) := hOr
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := hTerm

lemma buildNextHeadAllAux_start_le_final
    (sc : StraightConfig M n) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      bc.bw.ctx.circuit.gates ≤
        (buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit.gates := by
  intro js
  induction js with
  | nil =>
      intro bc
      simp [buildNextHeadAllAux]
  | cons j js ih =>
      intro bc
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      have hHead :
          bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        have hReset : bc.bw.ctx.circuit.gates ≤ bc0.bw.ctx.circuit.gates := by
          simp [bc0, bcReset]
        have hHeadLe := buildNextHeadAux_start_le (M := M) (n := n) (sc := sc) j
            (iqs := headStateSymbolPairs M n) (bc := bc0)
        exact le_trans hReset (by simpa [bcNext] using hHeadLe)
      have hRest :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates :=
        ih bcNext
      calc
        bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := hHead
        _ ≤ (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates := hRest
        _ = (buildNextHeadAllAux (M := M) (n := n) sc (j :: js) bc).1.bw.ctx.circuit.gates := by
              simp [buildNextHeadAllAux, bcReset, bc0, bcHead, bcNext]

lemma buildNextHeadAllAux_preserves_old_eval
    (sc : StraightConfig M n) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit)
      (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit.gates)
            (buildNextHeadAllAux_start_le_final (M := M) (n := n) sc js bc) w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
  intro js
  induction js with
  | nil =>
      intro bc x w
      simpa [buildNextHeadAllAux, castWireLe]
  | cons j0 js ih =>
      intro bc x w
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j0 (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      have hResetLe : bc.bw.ctx.circuit.gates ≤ bc0.bw.ctx.circuit.gates := by
        simp [bc0, bcReset]
      have hHeadLe : bc0.bw.ctx.circuit.gates ≤ bcHead.bw.ctx.circuit.gates :=
        buildNextHeadAux_start_le (M := M) (n := n) (sc := sc) j0
          (iqs := headStateSymbolPairs M n) (bc := bc0)
      have hNextLe : bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        simpa [bcNext] using Nat.le_trans hResetLe hHeadLe
      have hTailLe :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates :=
        buildNextHeadAllAux_start_le_final (M := M) (n := n) sc js bcNext
      have hTail :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
                (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
                hTailLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        simpa using ih bcNext x
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
      have hHead :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcHead.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
                (g' := bcHead.bw.ctx.circuit.gates) hHeadLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bc0.bw.ctx.circuit.gates) hResetLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc0.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := by
        simpa [bcHead] using
          (buildNextHeadAux_preserves_old_eval (M := M) (n := n) (sc := sc) j0
            (iqs := headStateSymbolPairs M n) (bc := bc0) (x := x)
            (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc0.bw.ctx.circuit.gates) hResetLe w))
      have hReset :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bc0.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        have hResetLe' : bc.bw.ctx.circuit.gates ≤ bcReset.bw.ctx.circuit.gates := by
          simp [bcReset]
        have hCast :
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc0.bw.ctx.circuit.gates) hResetLe w
            =
              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcReset.bw.ctx.circuit.gates) hResetLe' w := by
          exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcReset.bw.ctx.circuit.gates)
            (h₁ := by simpa [bc0] using hResetLe)
            (h₂ := hResetLe')
            w
        have hRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcReset.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcReset.bw.ctx.circuit.gates) hResetLe' w)
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) w := by
          simpa [bcReset] using
            (BuiltCarry_appendConst_preserves_old_eval
              (bc := bc) (val := false) (x := x) (w := w))
        simpa [bc0, hCast] using hRaw
      have hCastTail :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
            (buildNextHeadAllAux_start_le_final (M := M) (n := n) sc (j0 :: js) bc) w
          =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
            (buildNextHeadAllAux_start_le_final (M := M) (n := n) sc (j0 :: js) bc) w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe hTailLe) w := by
                simp [buildNextHeadAllAux, bcReset, bc0, bcHead, bcNext]
          _ =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
                  simp [castWireLe_trans]
      have hCastHead' :
          castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
            (g' := bcHead.bw.ctx.circuit.gates) (by simp [bcNext])
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
          =
            castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates) hHeadLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := by
        calc
          castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
            (g' := bcHead.bw.ctx.circuit.gates) (by simp [bcNext])
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe (by simp [bcNext])) w := by
                simp [castWireLe_trans]
          _ =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates)
              (Nat.le_trans hResetLe hHeadLe) w := by
                apply castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcHead.bw.ctx.circuit.gates)
          _ =
            castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates) hHeadLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := by
                  simp [castWireLe_trans]
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAllAux (M := M) (n := n) sc (j0 :: js) bc).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAllAux (M := M) (n := n) sc (j0 :: js) bc).1.bw.ctx.circuit.gates)
              (buildNextHeadAllAux_start_le_final (M := M) (n := n) sc (j0 :: js) bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
              (buildNextHeadAllAux_start_le_final (M := M) (n := n) sc (j0 :: js) bc) w) := by
                simp [buildNextHeadAllAux, bcReset, bc0, bcHead, bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  rw [hCastTail]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := hTail
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcHead.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  simp [bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcHead.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates) hHeadLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w)) := by
                  rw [hCastHead']
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc0.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := hHead
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := hReset

noncomputable def buildNextHeadAllAuxLookup
    (sc : StraightConfig M n) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      Fin (M.tapeLength n) →
      Option (Fin (n + (buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit.gates))
  | [], _bc, _j => none
  | j0 :: js, bc, j =>
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j0 (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      if hEq : j = j0 then
        by
          have hStart :
              bcHead.bw.ctx.circuit.gates ≤
                (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates := by
            have hStartNext :
                bcNext.bw.ctx.circuit.gates ≤
                  (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates :=
              buildNextHeadAllAux_start_le_final (M := M) (n := n) sc js bcNext
            simpa [bcNext] using hStartNext
          simpa [buildNextHeadAllAux, bcReset, bc0, bcHead, bcNext] using
            (Option.some
              (castWireLe (n := n)
                (g := bcHead.bw.ctx.circuit.gates)
                (g' := (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
                hStart
                bcHead.bw.out))
      else
        buildNextHeadAllAuxLookup sc js bcNext j

lemma buildNextHeadAllAuxLookup_isSome_of_mem
    (sc : StraightConfig M n) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit)
      (j : Fin (M.tapeLength n)),
      j ∈ js →
      (buildNextHeadAllAuxLookup (M := M) (n := n) sc js bc j).isSome := by
  intro js
  induction js with
  | nil =>
      intro bc j hj
      cases hj
  | cons j0 js ih =>
      intro bc j hj
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j0 (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      by_cases hEq : j = j0
      · subst hEq
        simp [buildNextHeadAllAuxLookup, bcReset, bc0, bcHead, bcNext]
      · have hjTail : j ∈ js := by simpa [hEq] using hj
        have hTail :
            (buildNextHeadAllAuxLookup (M := M) (n := n) sc js bcNext j).isSome :=
          ih bcNext j hjTail
        simpa [buildNextHeadAllAuxLookup, bcReset, bc0, bcHead, bcNext, hEq] using hTail

lemma buildNextHeadAllAuxLookup_isSome_tapeIndex
    (sc : StraightConfig M n) (bc : BuiltCarry (n := n) sc.circuit)
    (j : Fin (M.tapeLength n)) :
    (buildNextHeadAllAuxLookup (M := M) (n := n) sc (tapeIndexList M n) bc j).isSome := by
  have hj : j ∈ tapeIndexList M n := by
    simpa [tapeIndexList] using (List.mem_finRange j)
  exact buildNextHeadAllAuxLookup_isSome_of_mem
    (M := M) (n := n) sc (tapeIndexList M n) bc j hj

/--
Append-only state-stage assembly over one growing builder context.
-/
noncomputable def buildNextStateAllAux (sc : StraightConfig M n) :
    List M.state →
      BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit × List (M.state × Nat)
  | [], bc => (bc, [])
  | q :: qs, bc =>
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      let rest := buildNextStateAllAux sc qs bcNext
      (rest.1, (q, (bcState.bw.out : Nat)) :: rest.2)

noncomputable def buildNextTapeAllAuxEval
    (sc : StraightConfig M n) (x : Boolcube.Point n) :
    List (Fin (M.tapeLength n)) →
      BuiltCarry (n := n) sc.circuit → Bool
  | [], bc =>
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out
  | i :: is, bc =>
      let bcNext := buildNextTapeFromCarry (M := M) (n := n) sc i bc
      buildNextTapeAllAuxEval sc x is bcNext

noncomputable def buildNextHeadAllAuxEval
    (sc : StraightConfig M n) (x : Boolcube.Point n) :
    List (Fin (M.tapeLength n)) →
      BuiltCarry (n := n) sc.circuit → Bool
  | [], bc =>
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out
  | j :: js, bc =>
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j (headStateSymbolPairs M n) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      buildNextHeadAllAuxEval sc x js bcNext

noncomputable def buildNextStateAllAuxEval
    (sc : StraightConfig M n) (x : Boolcube.Point n) :
    List M.state →
      BuiltCarry (n := n) sc.circuit → Bool
  | [], bc =>
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out
  | q :: qs, bc =>
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      buildNextStateAllAuxEval sc x qs bcNext

lemma buildNextStateAllAux_gates_le
    (sc : StraightConfig M n) :
    ∀ (qs : List M.state) (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates +
          (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * qs.length := by
  intro qs
  induction qs with
  | nil =>
      intro bc
      simp [buildNextStateAllAux]
  | cons q qs ih =>
      intro bc
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      have hStateStep :
          bcState.bw.ctx.circuit.gates ≤
            bc.bw.ctx.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) := by
        have hRaw := buildNextStateAux_gates_le (M := M) (n := n) (sc := sc) (qTarget := q)
            (qs := stateSymbolPairs M) (bc := bc0)
        have hLen : (stateSymbolPairs M).length = 2 * stateCard M := length_stateSymbolPairs M
        have hRaw' : bcState.bw.ctx.circuit.gates ≤
            bc0.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) := by
          simpa [bcState, hLen] using hRaw
        have h0 : bc0.bw.ctx.circuit.gates = bc.bw.ctx.circuit.gates + 1 := by
          simp [bc0, bcReset]
        omega
      have hRest :
          (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * qs.length :=
        ih bcNext
      have hMain :
          (buildNextStateAllAux (M := M) (n := n) sc (q :: qs) bc).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * qs.length := by
        simpa [buildNextStateAllAux, bcReset, bc0, bcState, bcNext] using hRest
      calc
        (buildNextStateAllAux (M := M) (n := n) sc (q :: qs) bc).1.bw.ctx.circuit.gates
            ≤ bcNext.bw.ctx.circuit.gates +
                (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * qs.length := hMain
        _ = bcState.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * qs.length := by
              simp [bcNext]
        _ ≤ bc.bw.ctx.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
              (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * qs.length := by
              omega
        _ = bc.bw.ctx.circuit.gates +
              (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (List.length (q :: qs)) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma buildStateTermFromCarry_start_le
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit) :
    bc.bw.ctx.circuit.gates ≤
      (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates := by
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hq : qn = qTarget
          · set bcBranch : BuiltCarry (n := n) sc.circuit :=
              buildBranchFromCarry (M := M) (n := n) sc qs bc
            have hBranch : bc.bw.ctx.circuit.gates ≤ bcBranch.bw.ctx.circuit.gates :=
              buildBranchFromCarry_start_le (M := M) (n := n) sc qs bc
            have hEq :
                (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates =
                  bcBranch.bw.ctx.circuit.gates := by
              simp [buildStateTermFromCarry, hstep, hq, bcBranch]
            exact hEq ▸ hBranch
          · have hConst :
                bc.bw.ctx.circuit.gates ≤ (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
              simp
            simpa [buildStateTermFromCarry, hstep, hq] using hConst

lemma buildStateTermFromCarry_preserves_old_eval
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
          (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
          (buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc) w)
      =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) w := by
  cases hstep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hq : qn = qTarget
          · have hLeState :
                bc.bw.ctx.circuit.gates ≤
                  (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates := by
              simpa [buildStateTermFromCarry, hstep, hq] using
                (buildBranchFromCarry_start_le (M := M) (n := n) sc qs bc)
            have hCast :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                  (buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                  hLeState w := by
              exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                (h₁ := buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc)
                (h₂ := hLeState) w
            calc
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                    (buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc) w)
                =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                    hLeState w) := by
                      rw [hCast]
              _ =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) w := by
                    have hRaw :=
                      buildBranchFromCarry_preserves_old_eval
                        (M := M) (n := n) sc qs bc x w
                    have hEq : (M.step qs.1 qs.2).1 = qTarget := by
                      simpa [hstep] using hq
                    have hLeStateBranch :
                        bc.bw.ctx.circuit.gates ≤
                          (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates := by
                      simpa [buildStateTermFromCarry, hstep, hq] using hLeState
                    have hCastBranch :
                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                          (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                          hLeStateBranch w
                      =
                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                          (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                          (buildBranchFromCarry_start_le (M := M) (n := n) sc qs bc) w := by
                      exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                        (h₁ := hLeStateBranch)
                        (h₂ := buildBranchFromCarry_start_le (M := M) (n := n) sc qs bc) w
                    change
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (if (M.step qs.1 qs.2).1 = qTarget
                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                  then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                  else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                            hLeState w)
                        =
                          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                            (C := bc.bw.ctx.circuit) (x := x) w
                    calc
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (if (M.step qs.1 qs.2).1 = qTarget
                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                  then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                  else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                            hLeState w)
                        =
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                            hLeStateBranch w) := by
                              have hIfEq :
                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                      (C := (if (M.step qs.1 qs.2).1 = qTarget
                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                      (x := x)
                                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeState w)
                                =
                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                      (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                      (x := x)
                                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                        hLeStateBranch w) := by
                                  have hLeIfBranch :
                                      bc.bw.ctx.circuit.gates ≤
                                        (if (M.step qs.1 qs.2).1 = qTarget
                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                    simpa [if_pos hEq] using hLeStateBranch
                                  have hCastIf :
                                      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeState w
                                    =
                                      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeIfBranch w := by
                                    exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                      (h₁ := hLeState) (h₂ := hLeIfBranch) w
                                  calc
                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                        (C := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                        (x := x)
                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                          hLeState w)
                                      =
                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                        (C := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                        (x := x)
                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                          hLeIfBranch w) := by
                                            rw [hCastIf]
                                    _ =
                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                        (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                        (x := x)
                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                          (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                          hLeStateBranch w) := by
                                            have hLeIfBranch' :
                                                bc.bw.ctx.circuit.gates ≤
                                                  (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates := by
                                              simpa [if_pos hEq] using hLeIfBranch
                                            have hIfToBranch :
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfBranch w)
                                              =
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                      hLeIfBranch' w) := by
                                              have hLeIfFromBranch' :
                                                  bc.bw.ctx.circuit.gates ≤
                                                    (if (M.step qs.1 qs.2).1 = qTarget
                                                        then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                        else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                                simpa [if_pos hEq] using hLeIfBranch'
                                              have hCastIf' :
                                                  castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                    (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                    hLeIfBranch w
                                                =
                                                  castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                    (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                    hLeIfFromBranch' w := by
                                                exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                  (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                        then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                        else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                  (h₁ := hLeIfBranch) (h₂ := hLeIfFromBranch') w
                                              calc
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfBranch w)
                                                  =
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfFromBranch' w) := by
                                                        rw [hCastIf']
                                                _ =
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                      hLeIfBranch' w) := by
                                                        by_cases hcond : (M.step qs.1 qs.2).1 = qTarget
                                                        · have hCastEq :
                                                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                hLeIfFromBranch' w
                                                            =
                                                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                (by simpa [if_pos hcond] using hLeIfBranch') w := by
                                                            exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                              (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                    then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                    else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                              (h₁ := hLeIfFromBranch')
                                                              (h₂ := by simpa [if_pos hcond] using hLeIfBranch') w
                                                          rw [hCastEq]
                                                          have hLeAsBranch :
                                                              bc.bw.ctx.circuit.gates ≤
                                                                (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates := by
                                                            simpa [if_pos hcond] using
                                                              (show bc.bw.ctx.circuit.gates ≤
                                                                  (if (M.step qs.1 qs.2).1 = qTarget
                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates from
                                                                (by simpa [if_pos hcond] using hLeIfBranch'))
                                                          have hCastEq2 :
                                                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                hLeAsBranch w
                                                            =
                                                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                hLeIfBranch' w := by
                                                            exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                              (h₁ := hLeAsBranch) (h₂ := hLeIfBranch') w
                                                          calc
                                                            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                (x := x)
                                                                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                  (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                        then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                        else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                  (by
                                                                    simpa [if_pos hcond] using hLeIfBranch') w)
                                                              =
                                                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                        (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                        (x := x)
                                                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                          (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                          hLeAsBranch w) := by
                                                                    have hLeIfFromAs :
                                                                        bc.bw.ctx.circuit.gates ≤
                                                                          (if (M.step qs.1 qs.2).1 = qTarget
                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                                                      simpa [if_pos hcond] using hLeAsBranch
                                                                    have hCastEq3 :
                                                                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                          hLeIfFromBranch' w
                                                                      =
                                                                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                          hLeIfFromAs w :=
                                                                      castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                        (h₁ := hLeIfFromBranch') (h₂ := hLeIfFromAs) w
                                                                    rw [hCastEq3]
                                                                    have hCastEq4 :
                                                                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                          hLeIfFromAs w
                                                                      =
                                                                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                          (by simpa [if_pos hcond] using hLeIfBranch') w := by
                                                                      exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                        (h₁ := hLeIfFromAs)
                                                                        (h₂ := by simpa [if_pos hcond] using hLeIfBranch') w
                                                                    rw [hCastEq4]
                                                                    have hToBranch' :
                                                                        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                            (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                  then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                  else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                            (x := x)
                                                                            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                    then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                    else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                              (by simpa [if_pos hcond] using hLeIfBranch') w)
                                                                      =
                                                                        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                            (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                            (x := x)
                                                                            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeIfBranch' w) := by
                                                                        have hC' :
                                                                            (if (M.step qs.1 qs.2).1 = qTarget
                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit
                                                                              =
                                                                            (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit := by
                                                                          simp [if_pos hcond]
                                                                        have hLeEq' :
                                                                            bc.bw.ctx.circuit.gates ≤
                                                                              (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates := by
                                                                          simpa [hC'] using hLeIfFromAs
                                                                        have hCastEqA' :
                                                                            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeEq' w
                                                                          =
                                                                            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeIfBranch' w := by
                                                                          exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                            (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                            (h₁ := hLeEq') (h₂ := hLeIfBranch') w
                                                                        calc
                                                                          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                              (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                    then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                    else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                              (x := x)
                                                                              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                (by simpa [if_pos hcond] using hLeIfBranch') w)
                                                                            =
                                                                          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                              (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                    then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                    else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                              (x := x)
                                                                              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                hLeIfFromAs w) := by
                                                                                  rw [← hCastEq4]
                                                                          _ =
                                                                          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                              (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                              (x := x)
                                                                              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                                hLeEq' w) := by
                                                                                  have hLeIfFromEq' :
                                                                                      bc.bw.ctx.circuit.gates ≤
                                                                                        (if (M.step qs.1 qs.2).1 = qTarget
                                                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                                                                    simpa [hcond] using hLeEq'
                                                                                  have hCastEqMid :
                                                                                      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                        hLeIfFromAs w
                                                                                    =
                                                                                      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                        hLeIfFromEq' w := by
                                                                                    exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                      (h₁ := hLeIfFromAs) (h₂ := hLeIfFromEq') w
                                                                                  calc
                                                                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                                        (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                                        (x := x)
                                                                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                          hLeIfFromAs w)
                                                                                      =
                                                                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                                        (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                                        (x := x)
                                                                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                                          hLeIfFromEq' w) := by
                                                                                            rw [hCastEqMid]
                                                                                    _ =
                                                                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                                        (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                                        (x := x)
                                                                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                          (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                                          hLeEq' w) := by
                                                                                            exact evalWire_congr_castWireLe
                                                                                              (hC := hC') (x := x)
                                                                                              (h₁ := hLeIfFromEq') (h₂ := hLeEq')
                                                                                              (w := w)
                                                                          _ =
                                                                          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                              (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                              (x := x)
                                                                              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                                (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                                hLeIfBranch' w) := by
                                                                                  rw [hCastEqA']
                                                                    have hBranchEq :
                                                                        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                            (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                            (x := x)
                                                                            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeIfBranch' w)
                                                                      =
                                                                        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                            (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                            (x := x)
                                                                            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeAsBranch w) := by
                                                                        have hCastEqB :
                                                                            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeIfBranch' w
                                                                          =
                                                                            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              hLeAsBranch w := by
                                                                            exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                              (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                              (h₁ := hLeIfBranch') (h₂ := hLeAsBranch) w
                                                                        simpa [hCastEqB]
                                                                    exact hToBranch'.trans hBranchEq
                                                            _ =
                                                            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                                                                (x := x)
                                                                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                  (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                                  hLeIfBranch' w) := by
                                                                    rw [hCastEq2]
                                                        · exact (hcond hEq).elim
                                            have hCastEq' :
                                                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                  (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                  hLeIfBranch' w
                                              =
                                                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                  (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                  hLeStateBranch w := by
                                              exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                                                (h₁ := hLeIfBranch') (h₂ := hLeStateBranch) w
                                            exact hIfToBranch.trans (by rw [hCastEq'])
                              exact hIfEq
                      _ =
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit.gates)
                            (buildBranchFromCarry_start_le (M := M) (n := n) sc qs bc) w) := by
                              rw [hCastBranch]
                      _ = Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := bc.bw.ctx.circuit) (x := x) w := hRaw
          · have hLeState :
                bc.bw.ctx.circuit.gates ≤
                  (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates := by
              simpa [buildStateTermFromCarry, hstep, hq] using
                (show bc.bw.ctx.circuit.gates ≤ (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates by
                  simp)
            have hCast :
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                  (buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc) w
              =
                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                  hLeState w := by
              exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                (h₁ := buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc)
                (h₂ := hLeState) w
            calc
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                    (buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget qs bc) w)
                =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                    (g' := (buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
                    hLeState w) := by
                      rw [hCast]
              _ =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) w := by
                    have hLeConst :
                        bc.bw.ctx.circuit.gates ≤ (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                      simp
                    have hRaw :=
                      BuiltCarry_appendConst_preserves_old_eval
                        (bc := bc) (val := false) (x := x) (w := w)
                    have hRaw' :
                        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                            (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit) (x := x)
                            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                              (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                              hLeConst w)
                      =
                        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := bc.bw.ctx.circuit) (x := x) w := by
                      simpa [castWireLe_proof_irrel] using hRaw
                    have hCond : ¬(M.6 qs.1 qs.2).1 = qTarget := by
                      simpa [hstep] using hq
                    have hEq : ¬(M.step qs.1 qs.2).1 = qTarget := by
                      simpa [hstep] using hq
                    have hLeStateConst :
                        bc.bw.ctx.circuit.gates ≤
                          (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                      simpa [buildStateTermFromCarry, hstep, hq] using hLeState
                    have hCastConst :
                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                          (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                          hLeStateConst w
                      =
                        castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                          (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                          hLeConst w := by
                      exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                        (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                        (h₁ := hLeStateConst) (h₂ := hLeConst) w
                    change
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (if (M.step qs.1 qs.2).1 = qTarget
                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                  then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                  else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                            hLeState w)
                        =
                          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                            (C := bc.bw.ctx.circuit) (x := x) w
                    calc
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (if (M.step qs.1 qs.2).1 = qTarget
                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                  then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                  else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                            hLeState w)
                        =
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                            hLeStateConst w) := by
                              have hIfEq :
                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                      (C := (if (M.step qs.1 qs.2).1 = qTarget
                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                      (x := x)
                                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeState w)
                                =
                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                      (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                      (x := x)
                                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeStateConst w) := by
                                  have hLeIfConst :
                                      bc.bw.ctx.circuit.gates ≤
                                        (if (M.step qs.1 qs.2).1 = qTarget
                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                    simpa [if_neg hEq] using hLeStateConst
                                  have hCastIf :
                                      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeState w
                                    =
                                      castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                        (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                        hLeIfConst w := by
                                    exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                      (h₁ := hLeState) (h₂ := hLeIfConst) w
                                  calc
                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                        (C := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                        (x := x)
                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                          hLeState w)
                                      =
                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                        (C := (if (M.step qs.1 qs.2).1 = qTarget
                                              then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                              else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                        (x := x)
                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                          (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                          hLeIfConst w) := by
                                            rw [hCastIf]
                                    _ =
                                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                        (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                        (x := x)
                                        (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                          (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                          hLeStateConst w) := by
                                            have hLeIfConst' :
                                                bc.bw.ctx.circuit.gates ≤
                                                  (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                              simpa [if_neg hEq] using hLeIfConst
                                            have hIfToConst :
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfConst w)
                                              =
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfConst' w) := by
                                              have hLeIfFromConst' :
                                                  bc.bw.ctx.circuit.gates ≤
                                                    (if (M.step qs.1 qs.2).1 = qTarget
                                                        then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                        else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates := by
                                                simpa [if_neg hEq] using hLeIfConst'
                                              have hCastIf' :
                                                  castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                    (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                    hLeIfConst w
                                                =
                                                  castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                    (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                    hLeIfFromConst' w := by
                                                exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                  (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                        then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                        else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                  (h₁ := hLeIfConst) (h₂ := hLeIfFromConst') w
                                              calc
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfConst w)
                                                  =
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                            then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                            else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfFromConst' w) := by
                                                        rw [hCastIf']
                                                _ =
                                                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                    (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                    (x := x)
                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                      hLeIfConst' w) := by
                                                        by_cases hcond : (M.step qs.1 qs.2).1 = qTarget
                                                        · exact (hEq hcond).elim
                                                        · have hCastEq3 :
                                                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                hLeIfFromConst' w
                                                            =
                                                              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                      then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                      else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                (by simpa [if_neg hcond] using hLeIfConst') w := by
                                                            exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                              (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                    then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                    else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                              (h₁ := hLeIfFromConst')
                                                              (h₂ := by simpa [if_neg hcond] using hLeIfConst') w
                                                          rw [hCastEq3]
                                                          have hToConst' :
                                                              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                  (C := (if (M.step qs.1 qs.2).1 = qTarget
                                                                        then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                        else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                  (x := x)
                                                                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                    (g' := (if (M.step qs.1 qs.2).1 = qTarget
                                                                          then buildBranchFromCarry (M := M) (n := n) sc qs bc
                                                                          else BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                    (by simpa [if_neg hcond] using hLeIfConst') w)
                                                                =
                                                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                    (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                    (x := x)
                                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                      hLeIfConst' w) := by
                                                                simpa [if_neg hcond, castWireLe_proof_irrel]
                                                          have hConstEq :
                                                              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                  (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                  (x := x)
                                                                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                    (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                    hLeIfConst' w)
                                                                =
                                                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                    (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                    (x := x)
                                                                    (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                      hLeConst w) := by
                                                                have hCastEqB :
                                                                    castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                      hLeIfConst' w
                                                                  =
                                                                    castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                      hLeConst w := by
                                                                    exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                      (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                      (h₁ := hLeIfConst') (h₂ := hLeConst) w
                                                                simpa [hCastEqB]
                                                          have hRaw'' :
                                                              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                  (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                  (x := x)
                                                                  (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                    (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                    hLeIfConst' w)
                                                                =
                                                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                    (C := bc.bw.ctx.circuit) (x := x) w := by
                                                                calc
                                                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                      (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                      (x := x)
                                                                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                        (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                        hLeIfConst' w)
                                                                    =
                                                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                      (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                                                                      (x := x)
                                                                      (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                                        (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                                        hLeConst w) := hConstEq
                                                                  _ =
                                                                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                                                                      (C := bc.bw.ctx.circuit) (x := x) w := hRaw'
                                                          exact hToConst'
                                            have hCastEq' :
                                                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                  (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                  hLeIfConst' w
                                              =
                                                castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                                                  (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                  hLeStateConst w := by
                                              exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                                                (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                                                (h₁ := hLeIfConst') (h₂ := hLeStateConst) w
                                            exact hIfToConst.trans (by rw [hCastEq'])
                              exact hIfEq
                      _ =
                      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit)
                          (x := x)
                          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                            (g' := (BuiltCarry.appendConst (bc := bc) false).bw.ctx.circuit.gates)
                            hLeConst w) := by
                              rw [hCastConst]
                      _ = Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                          (C := bc.bw.ctx.circuit) (x := x) w := hRaw'

lemma buildNextStateAux_start_le
    (sc : StraightConfig M n) (qTarget : M.state) :
    ∀ (qs : List (M.state × Bool)) (bc : BuiltCarry (n := n) sc.circuit),
      bc.bw.ctx.circuit.gates ≤
        (buildNextStateAux (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates := by
  intro qs
  induction qs with
  | nil =>
      intro bc
      simp [buildNextStateAux]
  | cons a t ih =>
      intro bc
      let bcTerm := buildStateTermFromCarry (M := M) (n := n) sc qTarget a bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hTerm : bc.bw.ctx.circuit.gates ≤ bcTerm.bw.ctx.circuit.gates :=
        buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget a bc
      have hOr : bcTerm.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
        simp [bcOr]
      have hRest : bcNext.bw.ctx.circuit.gates ≤
          (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates :=
        ih bcNext
      calc
        bc.bw.ctx.circuit.gates ≤ bcTerm.bw.ctx.circuit.gates := hTerm
        _ ≤ bcOr.bw.ctx.circuit.gates := hOr
        _ = bcNext.bw.ctx.circuit.gates := by simp [bcNext]
        _ ≤ (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates := hRest
        _ = (buildNextStateAux (M := M) (n := n) sc qTarget (a :: t) bc).bw.ctx.circuit.gates := by
              simp [buildNextStateAux, bcTerm, bcOr, bcNext]

lemma buildNextStateAux_preserves_old_eval
    (sc : StraightConfig M n) (qTarget : M.state) :
    ∀ (qs : List (M.state × Bool)) (bc : BuiltCarry (n := n) sc.circuit)
      (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (buildNextStateAux (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextStateAux (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit.gates)
            (buildNextStateAux_start_le (M := M) (n := n) sc qTarget qs bc) w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
  intro qs
  induction qs with
  | nil =>
      intro bc x w
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAux (M := M) (n := n) sc qTarget [] bc).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget [] bc).bw.ctx.circuit.gates)
              (buildNextStateAux_start_le (M := M) (n := n) sc qTarget [] bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc.bw.ctx.circuit.gates) (Nat.le_refl _) w) := by
                simp [buildNextStateAux]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
              simp [castWireLe]
  | cons a t ih =>
      intro bc x w
      let bcTerm := buildStateTermFromCarry (M := M) (n := n) sc qTarget a bc
      let bcOr := BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hTermLe : bc.bw.ctx.circuit.gates ≤ bcTerm.bw.ctx.circuit.gates :=
        buildStateTermFromCarry_start_le (M := M) (n := n) sc qTarget a bc
      have hOrLe : bcTerm.bw.ctx.circuit.gates ≤ bcOr.bw.ctx.circuit.gates := by
        simp [bcOr]
      have hNextLe : bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        simpa [bcNext] using Nat.le_trans hTermLe hOrLe
      have hTerm :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        simpa [bcTerm] using
          (buildStateTermFromCarry_preserves_old_eval
            (M := M) (n := n) sc qTarget a bc x w)
      have hOr :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcTerm.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w) := by
        simpa [bcOr] using
          (BuiltCarry_appendOr_preserves_old_eval (bc := bcTerm)
            (u := bcTerm.carry) (v := bcTerm.bw.out) (x := x)
            (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w))
      have hTailLe :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates :=
        buildNextStateAux_start_le (M := M) (n := n) sc qTarget t bcNext
      have hTail :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
                (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
                hTailLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        simpa using ih bcNext x
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
      have hCastOr :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w
          =
            castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates)
              (Nat.le_trans hTermLe hOrLe) w := by
                simp [bcNext]
          _ =
            castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)) := by
                    simp [castWireLe_trans]
      have hCast :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
            (buildNextStateAux_start_le (M := M) (n := n) sc qTarget (a :: t) bc) w
          =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
            (buildNextStateAux_start_le (M := M) (n := n) sc qTarget (a :: t) bc) w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe hTailLe) w := by
                simp [bcTerm, bcOr, bcNext]
          _ =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
                  simp [castWireLe_trans]
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAux (M := M) (n := n) sc qTarget (a :: t) bc).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget (a :: t) bc).bw.ctx.circuit.gates)
              (buildNextStateAux_start_le (M := M) (n := n) sc qTarget (a :: t) bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
              (buildNextStateAux_start_le (M := M) (n := n) sc qTarget (a :: t) bc) w) := by
                simp [buildNextStateAux, bcTerm, bcOr, bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextStateAux (M := M) (n := n) sc qTarget t bcNext).bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  rw [hCast]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := hTail
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcOr.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
                (g' := bcOr.bw.ctx.circuit.gates) hOrLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w))) := by
                    rw [hCastOr]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcOr.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcTerm.bw.ctx.circuit.gates)
              (g' := bcOr.bw.ctx.circuit.gates) hOrLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w)) := by
                  simp [bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcTerm.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcTerm.bw.ctx.circuit.gates) hTermLe w) := hOr
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := hTerm

lemma buildNextStateAllAux_start_le_final
    (sc : StraightConfig M n) :
    ∀ (qs : List M.state) (bc : BuiltCarry (n := n) sc.circuit),
      bc.bw.ctx.circuit.gates ≤
        (buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit.gates := by
  intro qs
  induction qs with
  | nil =>
      intro bc
      simp [buildNextStateAllAux]
  | cons q qs ih =>
      intro bc
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      have hState :
          bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        have hReset : bc.bw.ctx.circuit.gates ≤ bc0.bw.ctx.circuit.gates := by
          simp [bc0, bcReset]
        have hStateLe := buildNextStateAux_start_le (M := M) (n := n) (sc := sc) q
            (qs := stateSymbolPairs M) (bc := bc0)
        exact le_trans hReset (by simpa [bcNext] using hStateLe)
      have hRest :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates :=
        ih bcNext
      calc
        bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := hState
        _ ≤ (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates := hRest
        _ = (buildNextStateAllAux (M := M) (n := n) sc (q :: qs) bc).1.bw.ctx.circuit.gates := by
              simp [buildNextStateAllAux, bcReset, bc0, bcState, bcNext]

/--
Lookup for the wire produced for a target state by `buildNextStateAllAux`.
The returned wire lives in the final context of the whole stage.
-/
noncomputable def buildNextStateAllAuxLookup
    (sc : StraightConfig M n) :
    ∀ (qs : List M.state) (bc : BuiltCarry (n := n) sc.circuit),
      M.state →
      Option (Fin (n + (buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit.gates))
  | [], _bc, _q => none
  | q0 :: qs, bc, q =>
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q0 (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      if hEq : q = q0 then
        by
          have hStart :
              bcState.bw.ctx.circuit.gates ≤
                (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates := by
            have hStartNext :
                bcNext.bw.ctx.circuit.gates ≤
                  (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates :=
              buildNextStateAllAux_start_le_final (M := M) (n := n) sc qs bcNext
            simpa [bcNext] using hStartNext
          simpa [buildNextStateAllAux, bcReset, bc0, bcState, bcNext] using
            (Option.some
              (castWireLe (n := n)
                (g := bcState.bw.ctx.circuit.gates)
                (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
                hStart
                bcState.bw.out))
      else
        buildNextStateAllAuxLookup sc qs bcNext q

lemma buildNextStateAllAuxLookup_isSome_of_mem
    (sc : StraightConfig M n) :
    ∀ (qs : List M.state) (bc : BuiltCarry (n := n) sc.circuit) (q : M.state),
      q ∈ qs →
      (buildNextStateAllAuxLookup (M := M) (n := n) sc qs bc q).isSome := by
  intro qs
  induction qs with
  | nil =>
      intro bc q hq
      cases hq
  | cons q0 qs ih =>
      intro bc q hq
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q0 (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      by_cases hEq : q = q0
      · subst hEq
        simp [buildNextStateAllAuxLookup, bcReset, bc0, bcState, bcNext]
      · have hqTail : q ∈ qs := by simpa [hEq] using hq
        have hTail :
            (buildNextStateAllAuxLookup (M := M) (n := n) sc qs bcNext q).isSome :=
          ih bcNext q hqTail
        simpa [buildNextStateAllAuxLookup, bcReset, bc0, bcState, bcNext, hEq] using hTail

lemma buildNextStateAllAuxLookup_isSome_stateList
    (sc : StraightConfig M n)
    (bc : BuiltCarry (n := n) sc.circuit)
    (q : M.state) :
    (buildNextStateAllAuxLookup (M := M) (n := n) sc (stateList M) bc q).isSome := by
  exact buildNextStateAllAuxLookup_isSome_of_mem
    (M := M) (n := n) sc (stateList M) bc q (state_mem_stateList M q)

lemma buildNextStateAllAux_preserves_old_eval
    (sc : StraightConfig M n) :
    ∀ (qs : List M.state) (bc : BuiltCarry (n := n) sc.circuit)
      (x : Boolcube.Point n) (w : Fin (n + bc.bw.ctx.circuit.gates)),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit) (x := x)
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit.gates)
            (buildNextStateAllAux_start_le_final (M := M) (n := n) sc qs bc) w)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := by
  intro qs
  induction qs with
  | nil =>
      intro bc x w
      simpa [buildNextStateAllAux, castWireLe]
  | cons q0 qs ih =>
      intro bc x w
      let bcReset := BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := buildNextStateAux (M := M) (n := n) sc q0 (stateSymbolPairs M) bc0
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      have hResetLe : bc.bw.ctx.circuit.gates ≤ bc0.bw.ctx.circuit.gates := by
        simp [bc0, bcReset]
      have hStateLe : bc0.bw.ctx.circuit.gates ≤ bcState.bw.ctx.circuit.gates :=
        buildNextStateAux_start_le (M := M) (n := n) (sc := sc) q0
          (qs := stateSymbolPairs M) (bc := bc0)
      have hNextLe : bc.bw.ctx.circuit.gates ≤ bcNext.bw.ctx.circuit.gates := by
        simpa [bcNext] using Nat.le_trans hResetLe hStateLe
      have hTailLe :
          bcNext.bw.ctx.circuit.gates ≤
            (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates :=
        buildNextStateAllAux_start_le_final (M := M) (n := n) sc qs bcNext
      have hTail :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
                (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
                hTailLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        simpa using ih bcNext x
          (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
      have hState :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcState.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
                (g' := bcState.bw.ctx.circuit.gates) hStateLe
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bc0.bw.ctx.circuit.gates) hResetLe w))
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc0.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := by
        simpa [bcState] using
          (buildNextStateAux_preserves_old_eval (M := M) (n := n) (sc := sc) q0
            (qs := stateSymbolPairs M) (bc := bc0) (x := x)
            (w := castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc0.bw.ctx.circuit.gates) hResetLe w))
      have hReset :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bc0.bw.ctx.circuit) (x := x)
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w)
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) w := by
        have hResetLe' : bc.bw.ctx.circuit.gates ≤ bcReset.bw.ctx.circuit.gates := by
          simp [bcReset]
        have hCast :
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc0.bw.ctx.circuit.gates) hResetLe w
            =
              castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcReset.bw.ctx.circuit.gates) hResetLe' w := by
          exact castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := bcReset.bw.ctx.circuit.gates)
            (h₁ := by simpa [bc0] using hResetLe)
            (h₂ := hResetLe')
            w
        have hRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcReset.bw.ctx.circuit) (x := x)
                (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcReset.bw.ctx.circuit.gates) hResetLe' w)
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) w := by
          simpa [bcReset] using
            (BuiltCarry_appendConst_preserves_old_eval
              (bc := bc) (val := false) (x := x) (w := w))
        simpa [bc0, hCast] using hRaw
      have hCastTail :
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
            (buildNextStateAllAux_start_le_final (M := M) (n := n) sc (q0 :: qs) bc) w
          =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
        calc
          castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
            (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
            (buildNextStateAllAux_start_le_final (M := M) (n := n) sc (q0 :: qs) bc) w
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe hTailLe) w := by
                simp [buildNextStateAllAux, bcReset, bc0, bcState, bcNext]
          _ =
            castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := by
                  simp [castWireLe_trans]
      have hCastState' :
          castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
            (g' := bcState.bw.ctx.circuit.gates) (by simp [bcNext])
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
          =
            castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
              (g' := bcState.bw.ctx.circuit.gates) hStateLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := by
        calc
          castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
            (g' := bcState.bw.ctx.circuit.gates) (by simp [bcNext])
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)
              =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcState.bw.ctx.circuit.gates)
              (Nat.le_trans hNextLe (by simp [bcNext])) w := by
                simp [castWireLe_trans]
          _ =
            castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcState.bw.ctx.circuit.gates)
              (Nat.le_trans hResetLe hStateLe) w := by
                apply castWireLe_proof_irrel (n := n) (g := bc.bw.ctx.circuit.gates)
                  (g' := bcState.bw.ctx.circuit.gates)
          _ =
            castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
              (g' := bcState.bw.ctx.circuit.gates) hStateLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := by
                  simp [castWireLe_trans]
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAllAux (M := M) (n := n) sc (q0 :: qs) bc).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAllAux (M := M) (n := n) sc (q0 :: qs) bc).1.bw.ctx.circuit.gates)
              (buildNextStateAllAux_start_le_final (M := M) (n := n) sc (q0 :: qs) bc) w)
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
              (buildNextStateAllAux_start_le_final (M := M) (n := n) sc (q0 :: qs) bc) w) := by
                simp [buildNextStateAllAux, bcReset, bc0, bcState, bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
              hTailLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  rw [hCastTail]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcNext.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bcNext.bw.ctx.circuit.gates) hNextLe w) := hTail
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcState.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bcNext.bw.ctx.circuit.gates)
              (g' := bcState.bw.ctx.circuit.gates) (by simp [bcNext])
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bcNext.bw.ctx.circuit.gates) hNextLe w)) := by
                  simp [bcNext]
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcState.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc0.bw.ctx.circuit.gates)
              (g' := bcState.bw.ctx.circuit.gates) hStateLe
              (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
                (g' := bc0.bw.ctx.circuit.gates) hResetLe w)) := by
                  rw [hCastState']
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc0.bw.ctx.circuit) (x := x)
            (castWireLe (n := n) (g := bc.bw.ctx.circuit.gates)
              (g' := bc0.bw.ctx.circuit.gates) hResetLe w) := hState
        _ =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) w := hReset

/--
Gate bound for running tape/head/state stages sequentially in one shared
append-only context.
-/
lemma buildLinearStages_gates_le
    (sc : StraightConfig M n) :
    let tapeRes := buildNextTapeAll (M := M) (n := n) sc
    let bcTape := tapeRes.1
    let headRes := buildNextHeadAllAux (M := M) (n := n) sc (tapeIndexList M n) bcTape
    let bcHead := headRes.1
    let stateRes := buildNextStateAllAux (M := M) (n := n) sc (stateList M) bcHead
    stateRes.1.bw.ctx.circuit.gates ≤
      sc.circuit.gates +
        ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
        4 * (M.tapeLength n) +
        (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (M.tapeLength n) +
        (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (stateCard M) := by
  classical
  dsimp
  let tapeRes := buildNextTapeAll (M := M) (n := n) sc
  let bcTape := tapeRes.1
  let headRes := buildNextHeadAllAux (M := M) (n := n) sc (tapeIndexList M n) bcTape
  let bcHead := headRes.1
  let stateRes := buildNextStateAllAux (M := M) (n := n) sc (stateList M) bcHead
  have hTape :
      bcTape.bw.ctx.circuit.gates ≤
        sc.circuit.gates +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
          4 * (M.tapeLength n) := by
    simpa [tapeRes, bcTape] using buildNextTapeAll_gates_le (M := M) (n := n) sc
  have hHead :
      bcHead.bw.ctx.circuit.gates ≤
        bcTape.bw.ctx.circuit.gates +
          (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (M.tapeLength n) := by
    have hRaw := buildNextHeadAllAux_gates_le (M := M) (n := n) sc
      (js := tapeIndexList M n) (bc := bcTape)
    have hLen : (tapeIndexList M n).length = M.tapeLength n := by
      simp [tapeIndexList]
    simpa [headRes, bcHead, hLen] using hRaw
  have hState :
      stateRes.1.bw.ctx.circuit.gates ≤
        bcHead.bw.ctx.circuit.gates +
          (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (stateCard M) := by
    have hRaw := buildNextStateAllAux_gates_le (M := M) (n := n) sc
      (qs := stateList M) (bc := bcHead)
    have hLen : (stateList M).length = stateCard M := length_stateList M
    simpa [stateRes, hLen] using hRaw
  have hState' :
      stateRes.1.bw.ctx.circuit.gates ≤
        bcTape.bw.ctx.circuit.gates +
          (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (M.tapeLength n) +
          (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (stateCard M) := by
    omega
  have hFinal :
      stateRes.1.bw.ctx.circuit.gates ≤
        sc.circuit.gates +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
          4 * (M.tapeLength n) +
          (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (M.tapeLength n) +
          (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (stateCard M) := by
    omega
  exact hFinal

end BuiltWire

/-- Evaluate the tape projection of a straight-line configuration. -/
def evalTape (sc : StraightConfig M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool :=
  fun i => Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.tape i)

/-- Evaluate the head projection of a straight-line configuration. -/
def evalHead (sc : StraightConfig M n) (x : Point n) :
    Fin (M.tapeLength n) → Bool :=
  fun i => Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.head i)

/-- Evaluate the state projection of a straight-line configuration. -/
def evalState (sc : StraightConfig M n) (x : Point n) :
    M.state → Bool :=
  fun q => Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.state q)

/--
Lift a straight configuration through an evaluation-preserving builder context.

All observable wires are reindexed with `ctx.liftBase`, so this is a pure
embedding of the old configuration into the extended circuit.
-/
noncomputable def liftConfig
    (sc : StraightConfig M n)
    (ctx : Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n sc.circuit) :
    StraightConfig M n where
  circuit := ctx.circuit
  tape := fun i => ctx.liftBase (sc.tape i)
  head := fun i => ctx.liftBase (sc.head i)
  state := fun q => ctx.liftBase (sc.state q)

/-- Straight-line correctness spec for an abstract configuration family. -/
structure Spec (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n) : Prop where
  tape_eq : ∀ x i, evalTape sc x i = (f x).tape i
  head_eq : ∀ x i, evalHead sc x i = headIndicator (f x) i
  state_eq : ∀ x q, evalState sc x q = stateIndicator M (f x) q

/-- Tree-circuit interpretation of every wire of a straight-line circuit. -/
noncomputable def toTreeWire (C : StraightLineCircuit n) :
    Fin (n + C.gates) → Circuit n :=
  Pnp3.Internal.PsubsetPpoly.StraightLine.toCircuitWire C

/-- Convert a straight-line configuration into ordinary tree circuits. -/
noncomputable def toConfigCircuits (sc : StraightConfig M n) : ConfigCircuits M n where
  tape := fun i => toTreeWire sc.circuit (sc.tape i)
  head := fun i => toTreeWire sc.circuit (sc.head i)
  state := fun q => toTreeWire sc.circuit (sc.state q)

lemma symbol_eval_toConfigCircuits_eq_symbolFoldlEval_false
    (sc : StraightConfig M n) (x : Point n) :
    Boolcube.Circuit.eval (ConfigCircuits.symbol M (toConfigCircuits sc)) x =
      BuiltWire.symbolFoldlEval sc x (tapeIndexList M n) false := by
  simp [ConfigCircuits.symbol, BuiltWire.symbolFoldlEval_false_eq_any, toConfigCircuits, toTreeWire]
  have hPred :
      ((fun c => c.eval x) ∘
          fun i =>
            (Pnp3.Internal.PsubsetPpoly.StraightLine.toCircuitWire sc.circuit (sc.head i)).and
              (Pnp3.Internal.PsubsetPpoly.StraightLine.toCircuitWire sc.circuit (sc.tape i)))
        =
      (fun i =>
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.head i) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.tape i)) := by
    funext i
    simp [Boolcube.Circuit.eval, Pnp3.Internal.PsubsetPpoly.StraightLine.eval_toCircuitWire]
  simpa [hPred]

lemma buildBranchFromCarry_out_eval_eq_branchIndicator
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Boolcube.Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildBranchFromCarry (M := M) (n := n) sc qs bc).bw.out
      =
        Boolcube.Circuit.eval
          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) qs) x := by
  have hBranch := BuiltWire.buildBranchFromCarry_out_eval (M := M) (n := n) sc qs bc x
  have hStateEval :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.state qs.1) =
        Boolcube.Circuit.eval ((toConfigCircuits sc).state qs.1) x := by
    symm
    simpa [toConfigCircuits, toTreeWire] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_toCircuitWire
        (C := sc.circuit) (x := x) (i := sc.state qs.1))
  have hSymbol :
      BuiltWire.symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false =
        Boolcube.Circuit.eval (ConfigCircuits.symbol M (toConfigCircuits sc)) x := by
    symm
    exact symbol_eval_toConfigCircuits_eq_symbolFoldlEval_false (M := M) (n := n) sc x
  cases hq : qs.2
  · simpa [ConfigCircuits.branchIndicator, ConfigCircuits.guardSymbol, Boolcube.Circuit.eval,
      hq, hStateEval, hSymbol] using hBranch
  · simpa [ConfigCircuits.branchIndicator, ConfigCircuits.guardSymbol, Boolcube.Circuit.eval,
      hq, hStateEval, hSymbol] using hBranch

lemma buildStateTermFromCarry_out_eval_eq_branchIndicator
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.out
      =
        match M.step qs.1 qs.2 with
        | ⟨qNext, _, _⟩ =>
            if qNext = qTarget then
              Boolcube.Circuit.eval
                (ConfigCircuits.branchIndicator M (toConfigCircuits sc) qs) x
            else false := by
  have h := BuiltWire.buildStateTermFromCarry_out_eval (M := M) (n := n) sc qTarget qs bc x
  cases hStep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hq : qn = qTarget
          · simp [hStep, hq] at h ⊢
            simpa using
              h.trans
                (buildBranchFromCarry_out_eval_eq_branchIndicator (M := M) (n := n) sc qs bc x)
          · simp [hStep, hq] at h ⊢
            simpa using h

/-- Boolean evaluator for one `stateTerm` branch against `toConfigCircuits sc`. -/
noncomputable def stateTermEval
    (sc : StraightConfig M n) (qTarget : M.state)
    (x : Point n) (qs : M.state × Bool) : Bool :=
  match M.step qs.1 qs.2 with
  | ⟨qNext, _, _⟩ =>
      if qNext = qTarget then
        Boolcube.Circuit.eval
          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) qs) x
      else false

lemma buildStateTermFromCarry_out_eval_eq_stateTerm
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : M.state × Bool) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildStateTermFromCarry (M := M) (n := n) sc qTarget qs bc).bw.out
      =
        stateTermEval (M := M) (n := n) sc qTarget x qs := by
  unfold stateTermEval
  simpa using
    buildStateTermFromCarry_out_eval_eq_branchIndicator
      (M := M) (n := n) sc qTarget qs bc x

noncomputable def stateTermAnyEval
    (sc : StraightConfig M n) (qTarget : M.state)
    (x : Point n) (qs : List (M.state × Bool)) : Bool :=
  List.any qs (fun p => stateTermEval (M := M) (n := n) sc qTarget x p)

private lemma any_headIndicator_and_tape_eq_tapeAtHead
    (c : TM.Configuration (M := M) n) :
    List.any (tapeIndexList M n) (fun i => headIndicator c i && c.tape i) = c.tape c.head := by
  classical
  cases hBit : c.tape c.head with
  | true =>
      apply (List.any_eq_true).2
      refine ⟨c.head, ?_, ?_⟩
      · simpa [tapeIndexList] using (List.mem_finRange c.head)
      · simpa [headIndicator_self, hBit]
  | false =>
      apply (List.any_eq_false).2
      intro i hi
      by_cases hEq : i = c.head
      · subst hEq
        simp [headIndicator_self, hBit]
      · have hHeadFalse : headIndicator c i = false :=
          headIndicator_ne (c := c) (h := hEq)
        simp [hHeadFalse]

private lemma symbol_eval_eq_tapeAtHead_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x,
      Boolcube.Circuit.eval (ConfigCircuits.symbol M (toConfigCircuits sc)) x
        = (f x).tape (f x).head := by
  intro x
  have hSym :
      Boolcube.Circuit.eval (ConfigCircuits.symbol M (toConfigCircuits sc)) x =
        BuiltWire.symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false :=
    symbol_eval_toConfigCircuits_eq_symbolFoldlEval_false (M := M) (n := n) sc x
  have hAnyRaw :
      BuiltWire.symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false =
        List.any (tapeIndexList M n) (fun i =>
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.tape i)) :=
    BuiltWire.symbolFoldlEval_false_eq_any (M := M) (n := n) sc x (tapeIndexList M n)
  have hPred :
      (fun i =>
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i) &&
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i))
      =
      (fun i => headIndicator (f x) i && (f x).tape i) := by
    funext i
    have hHead :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i)
          =
            headIndicator (f x) i := by
      simpa [evalHead] using (hSpec.head_eq x i)
    have hTape :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.tape i)
          =
            (f x).tape i := by
      simpa [evalTape] using (hSpec.tape_eq x i)
    simpa [hHead, hTape]
  have hAny :
      BuiltWire.symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false =
        List.any (tapeIndexList M n) (fun i => headIndicator (f x) i && (f x).tape i) := by
    simpa [hPred] using hAnyRaw
  calc
    Boolcube.Circuit.eval (ConfigCircuits.symbol M (toConfigCircuits sc)) x
        =
      BuiltWire.symbolFoldlEval (M := M) (n := n) sc x (tapeIndexList M n) false := hSym
    _ =
      List.any (tapeIndexList M n) (fun i => headIndicator (f x) i && (f x).tape i) := hAny
    _ = (f x).tape (f x).head :=
      any_headIndicator_and_tape_eq_tapeAtHead (M := M) (n := n) (c := f x)

private lemma branchIndicator_eval_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x (qs : M.state × Bool),
      Boolcube.Circuit.eval
          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) qs) x
        =
      (stateIndicator M (f x) qs.1 &&
        decide ((f x).tape (f x).head = qs.2)) := by
  intro x qs
  have hSym :
      Boolcube.Circuit.eval (ConfigCircuits.symbol M (toConfigCircuits sc)) x
        = (f x).tape (f x).head :=
    symbol_eval_eq_tapeAtHead_of_spec (M := M) (n := n) sc f hSpec x
  have hStateEval :
      Boolcube.Circuit.eval ((toConfigCircuits sc).state qs.1) x =
        stateIndicator M (f x) qs.1 := by
    calc
      Boolcube.Circuit.eval ((toConfigCircuits sc).state qs.1) x
          =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.state qs.1) := by
            simpa [toConfigCircuits, toTreeWire] using
              (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_toCircuitWire
                (C := sc.circuit) (x := x) (i := sc.state qs.1))
      _ = stateIndicator M (f x) qs.1 := hSpec.state_eq x qs.1
  cases hq : qs.2 <;>
    simp [ConfigCircuits.branchIndicator, ConfigCircuits.guardSymbol,
      Boolcube.Circuit.eval, hStateEval, hSym, hq]

private lemma branchIndicator_eval_current_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x,
      Boolcube.Circuit.eval
          (ConfigCircuits.branchIndicator M (toConfigCircuits sc)
            ((f x).state, (f x).tape (f x).head)) x
        = true := by
  intro x
  have h :=
    branchIndicator_eval_of_spec (M := M) (n := n) sc f hSpec x
      ((f x).state, (f x).tape (f x).head)
  simpa [stateIndicator_self] using h

private lemma branchIndicator_eval_false_of_state_ne_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x (q : M.state) (b : Bool),
      q ≠ (f x).state →
      Boolcube.Circuit.eval
          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (q, b)) x
        = false := by
  intro x q b hq
  have h :=
    branchIndicator_eval_of_spec (M := M) (n := n) sc f hSpec x (q, b)
  have hStateFalse : stateIndicator M (f x) q = false :=
    stateIndicator_ne (M := M) (c := f x) (h := hq)
  simpa [hStateFalse] using h

private lemma branchIndicator_eval_false_of_bit_ne_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x (b : Bool),
      b ≠ (f x).tape (f x).head →
      Boolcube.Circuit.eval
          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) ((f x).state, b)) x
        = false := by
  intro x b hb
  have h :=
    branchIndicator_eval_of_spec (M := M) (n := n) sc f hSpec x
      ((f x).state, b)
  have hStateTrue : stateIndicator M (f x) (f x).state = true :=
    stateIndicator_self (M := M) (c := f x)
  have hb' : ¬ ((f x).tape (f x).head = b) := by
    intro hEq
    exact hb hEq.symm
  have hBitFalse : decide ((f x).tape (f x).head = b) = false := by
    by_cases hEq : (f x).tape (f x).head = b
    · exact (hb' hEq).elim
    · simp [hEq]
  simpa [hStateTrue, hBitFalse] using h

private lemma stateTermAnyEval_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x qTarget,
      stateTermAnyEval (M := M) (n := n) sc qTarget x (stateSymbolPairs M)
        =
      stateIndicator M (TM.stepConfig (M := M) (f x)) qTarget := by
  intro x qTarget
  let c := f x
  let bCur : Bool := c.tape c.head
  have hCurMem : (c.state, bCur) ∈ stateSymbolPairs M :=
    pair_mem_stateSymbolPairs (M := M) c.state bCur
  by_cases hTargetTrue : stateIndicator M (TM.stepConfig (M := M) c) qTarget = true
  · have hTargetEq : (TM.stepConfig (M := M) c).state = qTarget :=
      (stateIndicator_true_iff (M := M) (c := TM.stepConfig (M := M) c) (q := qTarget)).1 hTargetTrue
    have hCurTrue :
        stateTermEval (M := M) (n := n) sc qTarget x (c.state, bCur) = true := by
      cases hStep : M.step c.state bCur with
      | mk qn bm =>
          cases bm with
          | mk wr mv =>
              have hqStep : (M.step c.state bCur).1 = qTarget := by
                simpa [TM.stepConfig, c] using hTargetEq
              have hq : qn = qTarget := by
                simpa [hStep] using hqStep
              have hBranch :
                  Boolcube.Circuit.eval
                      (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, bCur)) x
                    = true :=
                branchIndicator_eval_current_of_spec (M := M) (n := n) sc f hSpec x
              simpa [stateTermEval, c, hStep, hq, hBranch]
    have hAnyTrue :
        stateTermAnyEval (M := M) (n := n) sc qTarget x (stateSymbolPairs M) = true := by
      exact (List.any_eq_true).2 ⟨(c.state, bCur), hCurMem, hCurTrue⟩
    simpa [c, hTargetTrue] using hAnyTrue
  · have hTargetFalse : stateIndicator M (TM.stepConfig (M := M) c) qTarget = false :=
      by
        cases hVal : stateIndicator M (TM.stepConfig (M := M) c) qTarget <;> simp [hVal] at hTargetTrue ⊢
    have hStateNe : (TM.stepConfig (M := M) c).state ≠ qTarget := by
      intro hEq
      apply hTargetTrue
      exact (stateIndicator_true_iff (M := M) (c := TM.stepConfig (M := M) c) (q := qTarget)).2 hEq
    have hAnyFalse :
        stateTermAnyEval (M := M) (n := n) sc qTarget x (stateSymbolPairs M) = false := by
      apply (List.any_eq_false).2
      intro p hp
      rcases p with ⟨q, b⟩
      by_cases hq : q = c.state
      · subst hq
        by_cases hb : b = bCur
        · subst hb
          cases hStep : M.step c.state bCur with
          | mk qn bm =>
              cases bm with
              | mk wr mv =>
                  have hqStepNe : (M.step c.state bCur).1 ≠ qTarget := by
                    intro hEq
                    apply hStateNe
                    simpa [TM.stepConfig, c] using hEq
                  have hqNe : qn ≠ qTarget := by
                    simpa [hStep] using hqStepNe
                  have hBranch :
                      Boolcube.Circuit.eval
                          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, bCur)) x
                        = true :=
                    branchIndicator_eval_current_of_spec (M := M) (n := n) sc f hSpec x
                  simp [stateTermEval, c, hStep, hqNe, hBranch]
        · have hBranchFalse :
            Boolcube.Circuit.eval
                (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, b)) x
              = false :=
            branchIndicator_eval_false_of_bit_ne_of_spec
              (M := M) (n := n) sc f hSpec x b hb
          cases hStep : M.step c.state b with
          | mk qn bm =>
              cases bm with
              | mk wr mv =>
                  by_cases hNext : qn = qTarget
                  · simp [stateTermEval, c, hStep, hNext, hBranchFalse]
                  · simp [stateTermEval, c, hStep, hNext]
      · have hBranchFalse :
          Boolcube.Circuit.eval
              (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (q, b)) x
            = false :=
          branchIndicator_eval_false_of_state_ne_of_spec
            (M := M) (n := n) sc f hSpec x q b hq
        cases hStep : M.step q b with
        | mk qn bm =>
            cases bm with
            | mk wr mv =>
                by_cases hNext : qn = qTarget
                · simp [stateTermEval, c, hStep, hNext, hBranchFalse]
                · simp [stateTermEval, c, hStep, hNext]
    simpa [c, hTargetFalse] using hAnyFalse

/-- Boolean evaluator for one `headTerm` branch against `toConfigCircuits sc`. -/
noncomputable def headTermEval
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (x : Point n) (iqs : Fin (M.tapeLength n) × (M.state × Bool)) : Bool :=
  match M.step iqs.2.1 iqs.2.2 with
  | ⟨_, _, mv⟩ =>
      if BuiltWire.moveIndex (M := M) (n := n) iqs.1 mv = j then
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head iqs.1) &&
          Boolcube.Circuit.eval
            (ConfigCircuits.branchIndicator M (toConfigCircuits sc) iqs.2) x)
      else false

lemma buildHeadTermFromCarry_out_eval_eq_headTerm
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (iqs : Fin (M.tapeLength n) × (M.state × Bool))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
  (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.out
      =
        headTermEval (M := M) (n := n) sc j x iqs := by
  have h := BuiltWire.buildHeadTermFromCarry_out_eval (M := M) (n := n) sc j iqs bc x
  have hBr :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltWire.buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.circuit) (x := x)
          (BuiltWire.buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out
        =
          Boolcube.Circuit.eval
            (ConfigCircuits.branchIndicator M (toConfigCircuits sc) iqs.2) x := by
    exact buildBranchFromCarry_out_eval_eq_branchIndicator (M := M) (n := n) sc iqs.2 bc x
  cases hStep : M.step iqs.2.1 iqs.2.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          by_cases hmv : BuiltWire.moveIndex (M := M) (n := n) iqs.1 mv = j
          · calc
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                  (BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.out
                =
                  (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := sc.circuit) (x := x) (sc.head iqs.1) &&
                    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := (BuiltWire.buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.ctx.circuit) (x := x)
                      (BuiltWire.buildBranchFromCarry (M := M) (n := n) sc iqs.2 bc).bw.out) := by
                        simpa [hStep, hmv] using h
              _ =
                  (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                    (C := sc.circuit) (x := x) (sc.head iqs.1) &&
                    Boolcube.Circuit.eval
                      (ConfigCircuits.branchIndicator M (toConfigCircuits sc) iqs.2) x) := by
                        simpa [hBr]
              _ = headTermEval (M := M) (n := n) sc j x iqs := by
                    simp [headTermEval, hStep, hmv]
          · calc
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.ctx.circuit) (x := x)
                  (BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs bc).bw.out
                = false := by
                    simpa [hStep, hmv] using h
              _ = headTermEval (M := M) (n := n) sc j x iqs := by
                    simp [headTermEval, hStep, hmv]

noncomputable def headTermAnyEval
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (x : Point n) (iqs : List (Fin (M.tapeLength n) × (M.state × Bool))) : Bool :=
  List.any iqs (fun p => headTermEval (M := M) (n := n) sc j x p)

lemma buildNextHeadAuxEval_eq_any
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n))
    (iqs : List (Fin (M.tapeLength n) × (M.state × Bool)))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n)
    (hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out) :
    BuiltWire.buildNextHeadAuxEval (M := M) (n := n) sc j x iqs bc =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        headTermAnyEval (M := M) (n := n) sc j x iqs) := by
  induction iqs generalizing bc with
  | nil =>
      simp [BuiltWire.buildNextHeadAuxEval, headTermAnyEval]
  | cons iqs0 iqs ih =>
      let bcTerm := BuiltWire.buildHeadTermFromCarry (M := M) (n := n) sc j iqs0 bc
      let bcOr := BuiltWire.BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hOr :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out
            =
              (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.carry ||
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.bw.out) := by
        simpa [bcOr] using
          (BuiltWire.BuiltCarry_appendOr_out_eval (bc := bcTerm)
            (u := bcTerm.carry) (v := bcTerm.bw.out) (x := x))
      have hTermCarry :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
        simpa [bcTerm] using
          (BuiltWire.buildHeadTermFromCarry_carry_eval (M := M) (n := n) sc j iqs0 bc x)
      have hTermOut :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.bw.out
            =
              headTermEval (M := M) (n := n) sc j x iqs0 := by
        simpa [bcTerm] using
          (buildHeadTermFromCarry_out_eval_eq_headTerm (M := M) (n := n) sc j iqs0 bc x)
      have hCarryNext :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) bcNext.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x) bcNext.bw.out := by
        rfl
      have hIH := ih bcNext hCarryNext
      simp [BuiltWire.buildNextHeadAuxEval, headTermAnyEval, bcTerm, bcOr, bcNext,
        hOr, hTermCarry, hTermOut, hCarry, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm] at hIH ⊢
      exact hIH

private lemma moveHead_eq_moveIndex
    (c : TM.Configuration (M := M) n) (m : Move) :
    TM.Configuration.moveHead (M := M) (c := c) m =
      BuiltWire.moveIndex (M := M) (n := n) c.head m := by
  cases m <;> simp [TM.Configuration.moveHead, BuiltWire.moveIndex]

private lemma headTermAnyEval_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x j,
      headTermAnyEval (M := M) (n := n) sc j x (BuiltWire.headStateSymbolPairs M n)
        =
      headIndicator (TM.stepConfig (M := M) (f x)) j := by
  intro x j
  let c := f x
  let bCur : Bool := c.tape c.head
  have hCurMem : (c.head, (c.state, bCur)) ∈ BuiltWire.headStateSymbolPairs M n := by
    exact BuiltWire.pair_mem_headStateSymbolPairs (M := M) (n := n) c.head c.state bCur
  by_cases hTargetTrue : headIndicator (TM.stepConfig (M := M) c) j = true
  · have hTargetEq : (TM.stepConfig (M := M) c).head = j :=
      (headIndicator_true_iff (c := TM.stepConfig (M := M) c) (i := j)).1 hTargetTrue
    have hCurTrue :
        headTermEval (M := M) (n := n) sc j x (c.head, (c.state, bCur)) = true := by
      cases hStep : M.step c.state bCur with
      | mk qn bm =>
          cases bm with
          | mk wr mv =>
              have hMoveEq' :
                  TM.Configuration.moveHead (M := M) (c := c) mv = j := by
                simpa [TM.stepConfig, c, bCur, hStep] using hTargetEq
              have hMoveEq :
                  BuiltWire.moveIndex (M := M) (n := n) c.head mv = j := by
                simpa [moveHead_eq_moveIndex (M := M) (n := n) (c := c) (m := mv)] using hMoveEq'
              have hHeadTrue :
                  Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                      (C := sc.circuit) (x := x) (sc.head c.head) = true := by
                have hHeadEq := hSpec.head_eq x c.head
                have hInd : headIndicator c c.head = true := headIndicator_self (c := c)
                simpa [evalHead, c, hInd] using hHeadEq
              have hBranch :
                  Boolcube.Circuit.eval
                      (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, bCur)) x
                    = true :=
                branchIndicator_eval_current_of_spec (M := M) (n := n) sc f hSpec x
              simpa [headTermEval, c, hStep, hMoveEq, hHeadTrue, hBranch]
    have hAnyTrue :
        headTermAnyEval (M := M) (n := n) sc j x (BuiltWire.headStateSymbolPairs M n) = true := by
      exact (List.any_eq_true).2 ⟨(c.head, (c.state, bCur)), hCurMem, hCurTrue⟩
    simpa [c, hTargetTrue] using hAnyTrue
  · have hTargetFalse : headIndicator (TM.stepConfig (M := M) c) j = false := by
      cases hVal : headIndicator (TM.stepConfig (M := M) c) j <;> simp [hVal] at hTargetTrue ⊢
    have hHeadNe : (TM.stepConfig (M := M) c).head ≠ j := by
      intro hEq
      apply hTargetTrue
      exact (headIndicator_true_iff (c := TM.stepConfig (M := M) c) (i := j)).2 hEq
    have hAnyFalse :
        headTermAnyEval (M := M) (n := n) sc j x (BuiltWire.headStateSymbolPairs M n) = false := by
      apply (List.any_eq_false).2
      intro p hp
      rcases p with ⟨i, qsb⟩
      rcases qsb with ⟨q, b⟩
      by_cases hi : i = c.head
      · subst hi
        by_cases hq : q = c.state
        · subst hq
          by_cases hb : b = bCur
          · subst hb
            cases hStep : M.step c.state bCur with
            | mk qn bm =>
                cases bm with
                | mk wr mv =>
                    have hHeadNe' :
                        TM.Configuration.moveHead (M := M) (c := c) mv ≠ j := by
                      intro hEq
                      apply hHeadNe
                      simpa [TM.stepConfig, c, bCur, hStep] using hEq
                    have hMoveNe :
                        BuiltWire.moveIndex (M := M) (n := n) c.head mv ≠ j := by
                      intro hEq
                      apply hHeadNe'
                      simpa [moveHead_eq_moveIndex (M := M) (n := n) (c := c) (m := mv)] using hEq
                    simp [headTermEval, c, hStep, hMoveNe]
          · have hBranchFalse :
              Boolcube.Circuit.eval
                  (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, b)) x
                = false :=
              branchIndicator_eval_false_of_bit_ne_of_spec
                (M := M) (n := n) sc f hSpec x b hb
            cases hStep : M.step c.state b with
            | mk qn bm =>
                cases bm with
                | mk wr mv =>
                    by_cases hMove : BuiltWire.moveIndex (M := M) (n := n) c.head mv = j
                    · simp [headTermEval, c, hStep, hMove, hBranchFalse]
                    · simp [headTermEval, c, hStep, hMove]
        · have hBranchFalse :
            Boolcube.Circuit.eval
                (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (q, b)) x
              = false :=
            branchIndicator_eval_false_of_state_ne_of_spec
              (M := M) (n := n) sc f hSpec x q b hq
          cases hStep : M.step q b with
          | mk qn bm =>
              cases bm with
              | mk wr mv =>
                  by_cases hMove : BuiltWire.moveIndex (M := M) (n := n) c.head mv = j
                  · simp [headTermEval, c, hStep, hMove, hBranchFalse]
                  · simp [headTermEval, c, hStep, hMove]
      · have hHeadFalse :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := sc.circuit) (x := x) (sc.head i) = false := by
          have hHeadEq := hSpec.head_eq x i
          have hInd : headIndicator c i = false := headIndicator_ne (c := c) (h := hi)
          simpa [evalHead, c, hInd] using hHeadEq
        cases hStep : M.step q b with
        | mk qn bm =>
            cases bm with
            | mk wr mv =>
                by_cases hMove : BuiltWire.moveIndex (M := M) (n := n) i mv = j
                · simp [headTermEval, c, hStep, hMove, hHeadFalse]
                · simp [headTermEval, c, hStep, hMove]
    simpa [c, hTargetFalse] using hAnyFalse

private lemma buildNextHeadAuxEval_spec_from_false
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) (j : Fin (M.tapeLength n))
    (hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.bw.out)
    (hOutFalse :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.bw.out = false) :
    BuiltWire.buildNextHeadAuxEval (M := M) (n := n) sc j x
      (BuiltWire.headStateSymbolPairs M n) bc
      =
      headIndicator (TM.stepConfig (M := M) (f x)) j := by
  have hAny :
      BuiltWire.buildNextHeadAuxEval (M := M) (n := n) sc j x
        (BuiltWire.headStateSymbolPairs M n) bc
      =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        headTermAnyEval (M := M) (n := n) sc j x (BuiltWire.headStateSymbolPairs M n)) :=
    buildNextHeadAuxEval_eq_any (M := M) (n := n) sc j (BuiltWire.headStateSymbolPairs M n) bc x hCarry
  calc
    BuiltWire.buildNextHeadAuxEval (M := M) (n := n) sc j x
      (BuiltWire.headStateSymbolPairs M n) bc
        =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        headTermAnyEval (M := M) (n := n) sc j x (BuiltWire.headStateSymbolPairs M n)) := hAny
    _ = headTermAnyEval (M := M) (n := n) sc j x (BuiltWire.headStateSymbolPairs M n) := by
          simp [hOutFalse]
    _ = headIndicator (TM.stepConfig (M := M) (f x)) j :=
          headTermAnyEval_of_spec sc f hSpec x j

private lemma buildNextHeadAux_out_eval_spec_from_reset
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) (j : Fin (M.tapeLength n)) :
    let bcReset := BuiltWire.BuiltCarry.appendConst (bc := bc) false
    let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
    let bcHead := BuiltWire.buildNextHeadAux (M := M) (n := n) sc j (BuiltWire.headStateSymbolPairs M n) bc0
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcHead.bw.ctx.circuit) (x := x) bcHead.bw.out
      =
        headIndicator (TM.stepConfig (M := M) (f x)) j := by
  let bcReset := BuiltWire.BuiltCarry.appendConst (bc := bc) false
  let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
  let bcHead := BuiltWire.buildNextHeadAux (M := M) (n := n) sc j (BuiltWire.headStateSymbolPairs M n) bc0
  have hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out := by
    rfl
  have hOutFalse :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out
        = false := by
    have :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcReset.bw.ctx.circuit) (x := x) bcReset.bw.out
        = false := by
      change
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc bc.bw.ctx.circuit (LegacyStraightOp.const false))
            (x := x) (Fin.last (n + bc.bw.ctx.circuit.gates))
          = false
      simpa using
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
          (C := bc.bw.ctx.circuit) (op := LegacyStraightOp.const false) (x := x))
    simpa [bc0, bcReset] using this
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcHead.bw.ctx.circuit) (x := x) bcHead.bw.out
      =
        BuiltWire.buildNextHeadAuxEval (M := M) (n := n) sc j x
          (BuiltWire.headStateSymbolPairs M n) bc0 := by
            simpa [bcHead, bc0] using
              (BuiltWire.buildNextHeadAux_out_eval (M := M) (n := n) sc j
                (BuiltWire.headStateSymbolPairs M n) bc0 x)
    _ = headIndicator (TM.stepConfig (M := M) (f x)) j := by
          exact buildNextHeadAuxEval_spec_from_false (M := M) (n := n) sc f hSpec
            bc0 x j hCarry hOutFalse

lemma buildNextStateAuxEval_eq_any
    (sc : StraightConfig M n) (qTarget : M.state)
    (qs : List (M.state × Bool))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n)
    (hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out) :
    BuiltWire.buildNextStateAuxEval (M := M) (n := n) sc qTarget x qs bc =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        stateTermAnyEval (M := M) (n := n) sc qTarget x qs) := by
  induction qs generalizing bc with
  | nil =>
      simp [BuiltWire.buildNextStateAuxEval, stateTermAnyEval]
  | cons qs0 qs ih =>
      let bcTerm := BuiltWire.buildStateTermFromCarry (M := M) (n := n) sc qTarget qs0 bc
      let bcOr := BuiltWire.BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hOr :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out
            =
              (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.carry ||
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.bw.out) := by
        simpa [bcOr] using
          (BuiltWire.BuiltCarry_appendOr_out_eval (bc := bcTerm)
            (u := bcTerm.carry) (v := bcTerm.bw.out) (x := x))
      have hTermCarry :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
        simpa [bcTerm] using
          (BuiltWire.buildStateTermFromCarry_carry_eval
            (M := M) (n := n) sc qTarget qs0 bc x)
      have hTermOut :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.bw.out
            =
              stateTermEval (M := M) (n := n) sc qTarget x qs0 := by
        simpa [bcTerm] using
          (buildStateTermFromCarry_out_eval_eq_stateTerm
            (M := M) (n := n) sc qTarget qs0 bc x)
      have hCarryNext :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) bcNext.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x) bcNext.bw.out := by
        rfl
      have hIH := ih bcNext hCarryNext
      simp [BuiltWire.buildNextStateAuxEval, stateTermAnyEval, bcTerm, bcOr, bcNext,
        hOr, hTermCarry, hTermOut, hCarry, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm] at hIH ⊢
      exact hIH

private lemma buildNextStateAuxEval_spec_from_false
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) (qTarget : M.state)
    (hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.bw.out)
    (hOutFalse :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.bw.out = false) :
    BuiltWire.buildNextStateAuxEval (M := M) (n := n) sc qTarget x
      (stateSymbolPairs M) bc
      =
      stateIndicator M (TM.stepConfig (M := M) (f x)) qTarget := by
  have hAny :
      BuiltWire.buildNextStateAuxEval (M := M) (n := n) sc qTarget x
        (stateSymbolPairs M) bc
      =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        stateTermAnyEval (M := M) (n := n) sc qTarget x (stateSymbolPairs M)) :=
    buildNextStateAuxEval_eq_any (M := M) (n := n) sc qTarget (stateSymbolPairs M) bc x hCarry
  calc
    BuiltWire.buildNextStateAuxEval (M := M) (n := n) sc qTarget x
      (stateSymbolPairs M) bc
        =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        stateTermAnyEval (M := M) (n := n) sc qTarget x (stateSymbolPairs M)) := hAny
    _ = stateTermAnyEval (M := M) (n := n) sc qTarget x (stateSymbolPairs M) := by
          simp [hOutFalse]
    _ = stateIndicator M (TM.stepConfig (M := M) (f x)) qTarget :=
          stateTermAnyEval_of_spec sc f hSpec x qTarget

private lemma buildNextStateAux_out_eval_spec_from_reset
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) (qTarget : M.state) :
    let bcReset := BuiltWire.BuiltCarry.appendConst (bc := bc) false
    let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
    let bcState := BuiltWire.buildNextStateAux (M := M) (n := n) sc qTarget (stateSymbolPairs M) bc0
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcState.bw.ctx.circuit) (x := x) bcState.bw.out
      =
        stateIndicator M (TM.stepConfig (M := M) (f x)) qTarget := by
  let bcReset := BuiltWire.BuiltCarry.appendConst (bc := bc) false
  let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
  let bcState := BuiltWire.buildNextStateAux (M := M) (n := n) sc qTarget (stateSymbolPairs M) bc0
  have hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out := by
    rfl
  have hOutFalse :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out
        = false := by
    have :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcReset.bw.ctx.circuit) (x := x) bcReset.bw.out
        = false := by
      change
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc bc.bw.ctx.circuit (LegacyStraightOp.const false))
            (x := x) (Fin.last (n + bc.bw.ctx.circuit.gates))
          = false
      simpa using
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
          (C := bc.bw.ctx.circuit) (op := LegacyStraightOp.const false) (x := x))
    simpa [bc0, bcReset] using this
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcState.bw.ctx.circuit) (x := x) bcState.bw.out
      =
        BuiltWire.buildNextStateAuxEval (M := M) (n := n) sc qTarget x
          (stateSymbolPairs M) bc0 := by
            simpa [bcState, bc0] using
              (BuiltWire.buildNextStateAux_out_eval (M := M) (n := n) sc qTarget
                (stateSymbolPairs M) bc0 x)
    _ = stateIndicator M (TM.stepConfig (M := M) (f x)) qTarget := by
          exact buildNextStateAuxEval_spec_from_false (M := M) (n := n) sc f hSpec
            bc0 x qTarget hCarry hOutFalse

private lemma buildNextStateAllAuxLookup_eval
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ (qs : List M.state) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
      (q : M.state) (hq : q ∈ qs) (x : Point n),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit)
        (x := x)
        ((BuiltWire.buildNextStateAllAuxLookup (M := M) (n := n) sc qs bc q).get
          (BuiltWire.buildNextStateAllAuxLookup_isSome_of_mem (M := M) (n := n) sc qs bc q hq))
      =
      stateIndicator M (TM.stepConfig (M := M) (f x)) q := by
  intro qs
  induction qs with
  | nil =>
      intro bc q hq x
      cases hq
  | cons q0 qs ih =>
      intro bc q hq x
      let bcReset := BuiltWire.BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcState := BuiltWire.buildNextStateAux (M := M) (n := n) sc q0 (stateSymbolPairs M) bc0
      let bcNext : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      by_cases hEq : q = q0
      · subst q
        have hStateEval :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcState.bw.ctx.circuit) (x := x) bcState.bw.out
              =
                stateIndicator M (TM.stepConfig (M := M) (f x)) q0 := by
          simpa [bcReset, bc0, bcState] using
            (buildNextStateAux_out_eval_spec_from_reset (M := M) (n := n) sc f hSpec bc x q0)
        let wOutNext : Fin (n + bcNext.bw.ctx.circuit.gates) := by
          simpa [bcNext] using bcState.bw.out
        have hRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit)
                (x := x)
                (BuiltWire.castWireLe (n := n)
                  (g := bcNext.bw.ctx.circuit.gates)
                  (g' := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
                  (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc qs bcNext)
                  wOutNext)
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcNext.bw.ctx.circuit) (x := x) wOutNext := by
          simpa using
            (BuiltWire.buildNextStateAllAux_preserves_old_eval
              (M := M) (n := n) sc qs bcNext x wOutNext)
        have hGoalToRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc (q0 :: qs) bc).1.bw.ctx.circuit)
                (x := x)
                ((BuiltWire.buildNextStateAllAuxLookup (M := M) (n := n) sc (q0 :: qs) bc q0).get
                  (BuiltWire.buildNextStateAllAuxLookup_isSome_of_mem
                    (M := M) (n := n) sc (q0 :: qs) bc q0 hq))
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit)
                  (x := x)
                  (BuiltWire.castWireLe (n := n)
                    (g := bcNext.bw.ctx.circuit.gates)
                    (g' := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
                    (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc qs bcNext)
                    wOutNext) := by
          simpa [BuiltWire.buildNextStateAllAux, BuiltWire.buildNextStateAllAuxLookup,
            bcReset, bc0, bcState, bcNext, wOutNext]
        calc
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc (q0 :: qs) bc).1.bw.ctx.circuit)
              (x := x)
              ((BuiltWire.buildNextStateAllAuxLookup (M := M) (n := n) sc (q0 :: qs) bc q0).get
                (BuiltWire.buildNextStateAllAuxLookup_isSome_of_mem
                  (M := M) (n := n) sc (q0 :: qs) bc q0 hq))
            =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit)
              (x := x)
              (BuiltWire.castWireLe (n := n)
                (g := bcNext.bw.ctx.circuit.gates)
                (g' := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates)
                (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc qs bcNext)
                wOutNext) := hGoalToRaw
          _ =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) wOutNext := hRaw
          _ =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcState.bw.ctx.circuit) (x := x) bcState.bw.out := by
                simpa [bcNext, wOutNext]
          _ = stateIndicator M (TM.stepConfig (M := M) (f x)) q0 := hStateEval
      · have hqTail : q ∈ qs := by
          simpa [hEq] using hq
        have hTail :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit)
                (x := x)
                ((BuiltWire.buildNextStateAllAuxLookup (M := M) (n := n) sc qs bcNext q).get
                  (BuiltWire.buildNextStateAllAuxLookup_isSome_of_mem
                    (M := M) (n := n) sc qs bcNext q hqTail))
              =
                stateIndicator M (TM.stepConfig (M := M) (f x)) q :=
          ih bcNext q hqTail x
        simpa [BuiltWire.buildNextStateAllAux, BuiltWire.buildNextStateAllAuxLookup,
          bcReset, bc0, bcState, bcNext, hEq] using hTail

lemma buildWriteTermFromCarry_out_eval_eq_branchIndicator
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.out
      =
        match M.step qs.1 qs.2 with
        | ⟨_, write, _⟩ =>
            if write then
              Boolcube.Circuit.eval
                (ConfigCircuits.branchIndicator M (toConfigCircuits sc) qs) x
            else false := by
  have h := BuiltWire.buildWriteTermFromCarry_out_eval (M := M) (n := n) sc qs bc x
  cases hStep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          cases wr <;> simp [hStep] at h ⊢
          · simpa using h
          · simpa using
              h.trans
                (buildBranchFromCarry_out_eval_eq_branchIndicator (M := M) (n := n) sc qs bc x)

/-- Boolean evaluator for one `writeTerm` branch against `toConfigCircuits sc`. -/
noncomputable def writeTermEval
    (sc : StraightConfig M n) (x : Point n) (qs : M.state × Bool) : Bool :=
  Boolcube.Circuit.eval (ConfigCircuits.writeTerm M (toConfigCircuits sc) qs) x

lemma buildWriteTermFromCarry_out_eval_eq_writeTerm
    (sc : StraightConfig M n)
    (qs : M.state × Bool) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildWriteTermFromCarry (M := M) (n := n) sc qs bc).bw.out
      =
        writeTermEval (M := M) (n := n) sc x qs := by
  unfold writeTermEval
  cases hStep : M.step qs.1 qs.2 with
  | mk qn bm =>
      cases bm with
      | mk wr mv =>
          cases wr <;> simpa [ConfigCircuits.writeTerm, hStep] using
            (buildWriteTermFromCarry_out_eval_eq_branchIndicator (M := M) (n := n) sc qs bc x)

noncomputable def writeTermAnyEval
    (sc : StraightConfig M n) (x : Point n) (qs : List (M.state × Bool)) : Bool :=
  List.any qs (fun p => writeTermEval (M := M) (n := n) sc x p)

lemma buildWriteBitAuxEval_eq_any
    (sc : StraightConfig M n)
    (qs : List (M.state × Bool))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n)
    (hCarry :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.carry =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out) :
    BuiltWire.buildWriteBitAuxEval (M := M) (n := n) sc x qs bc =
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bc.bw.ctx.circuit) (x := x) bc.bw.out ||
        writeTermAnyEval (M := M) (n := n) sc x qs) := by
  induction qs generalizing bc with
  | nil =>
      simp [BuiltWire.buildWriteBitAuxEval, writeTermAnyEval]
  | cons qs0 qs ih =>
      let bcTerm := BuiltWire.buildWriteTermFromCarry (M := M) (n := n) sc qs0 bc
      let bcOr := BuiltWire.BuiltCarry.appendOr (bc := bcTerm) bcTerm.carry bcTerm.bw.out
      let bcNext : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcOr.bw, bcOr.bw.out⟩
      have hOr :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcOr.bw.ctx.circuit) (x := x) bcOr.bw.out
            =
              (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.carry ||
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.bw.out) := by
        simpa [bcOr] using
          (BuiltWire.BuiltCarry_appendOr_out_eval (bc := bcTerm)
            (u := bcTerm.carry) (v := bcTerm.bw.out) (x := x))
      have hTermCarry :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
        simpa [bcTerm] using
          (BuiltWire.buildWriteTermFromCarry_carry_eval (M := M) (n := n) sc qs0 bc x)
      have hTermOut :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcTerm.bw.ctx.circuit) (x := x) bcTerm.bw.out
            =
              writeTermEval (M := M) (n := n) sc x qs0 := by
        simpa [bcTerm] using
          (buildWriteTermFromCarry_out_eval_eq_writeTerm (M := M) (n := n) sc qs0 bc x)
      have hCarryNext :
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) bcNext.carry
            =
              Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x) bcNext.bw.out := by
        rfl
      have hIH := ih bcNext hCarryNext
      simp [BuiltWire.buildWriteBitAuxEval, writeTermAnyEval, bcTerm, bcOr, bcNext,
        hOr, hTermCarry, hTermOut, hCarry, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm] at hIH ⊢
      exact hIH

lemma buildWriteBit_out_eval_eq_writeBit
    (sc : StraightConfig M n) (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildWriteBit (M := M) (n := n) sc).ctx.circuit) (x := x)
        (BuiltWire.buildWriteBit (M := M) (n := n) sc).out
      =
        Boolcube.Circuit.eval (ConfigCircuits.writeBit M (toConfigCircuits sc)) x := by
  let bw0 := BuiltWire.initFalse (M := M) (n := n) sc
  let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bw0, bw0.out⟩
  have hInitOut :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bw0.ctx.circuit) (x := x) bw0.out = false := by
    unfold bw0 BuiltWire.initFalse
    change
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := Pnp3.Internal.PsubsetPpoly.StraightLine.snoc sc.circuit (LegacyStraightOp.const false))
          (x := x) (Fin.last (n + sc.circuit.gates)) = false
    simpa using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire_snoc_last
        (C := sc.circuit) (op := LegacyStraightOp.const false) (x := x))
  have hCarry0 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.carry
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out := by
    rfl
  have hAux :
      BuiltWire.buildWriteBitAuxEval (M := M) (n := n) sc x (stateSymbolPairs M) bc0 =
        (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out ||
          writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M)) :=
    buildWriteBitAuxEval_eq_any (M := M) (n := n) sc (stateSymbolPairs M) bc0 x hCarry0
  have hOut :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltWire.buildWriteBitAux (M := M) (n := n) sc (stateSymbolPairs M) bc0).bw.ctx.circuit) (x := x)
          (BuiltWire.buildWriteBitAux (M := M) (n := n) sc (stateSymbolPairs M) bc0).bw.out
        =
          writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M) := by
    calc
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltWire.buildWriteBitAux (M := M) (n := n) sc (stateSymbolPairs M) bc0).bw.ctx.circuit) (x := x)
          (BuiltWire.buildWriteBitAux (M := M) (n := n) sc (stateSymbolPairs M) bc0).bw.out
          =
            (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bc0.bw.ctx.circuit) (x := x) bc0.bw.out ||
              writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M)) := by
              exact (BuiltWire.buildWriteBitAux_out_eval (M := M) (n := n) sc (stateSymbolPairs M) bc0 x).trans hAux
      _ = writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M) := by
            simp [bc0, bw0, hInitOut]
  simpa [BuiltWire.buildWriteBit, ConfigCircuits.writeBit, writeTermAnyEval,
    Boolcube.Circuit.eval_bigOr_any]
    using hOut

private lemma writeTermAnyEval_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x,
      writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M)
        =
      (TM.stepConfig (M := M) (f x)).tape (f x).head := by
  intro x
  let c := f x
  let bCur : Bool := c.tape c.head
  have hCurMem : (c.state, bCur) ∈ stateSymbolPairs M :=
    pair_mem_stateSymbolPairs (M := M) c.state bCur
  by_cases hWriteTrue : (TM.stepConfig (M := M) c).tape c.head = true
  · have hCurTrue :
      writeTermEval (M := M) (n := n) sc x (c.state, bCur) = true := by
      cases hStep : M.step c.state bCur with
      | mk qn bm =>
          cases bm with
          | mk wr mv =>
              have hWrTrue : wr = true := by
                have : (TM.stepConfig (M := M) c).tape c.head = true := by
                  simpa [c] using hWriteTrue
                simpa [TM.stepConfig, c, bCur, hStep] using this
              have hBranch :
                  Boolcube.Circuit.eval
                      (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, bCur)) x
                    = true :=
                branchIndicator_eval_current_of_spec (M := M) (n := n) sc f hSpec x
              unfold writeTermEval
              simp [ConfigCircuits.writeTerm, c, hStep, hWrTrue, hBranch]
    have hAnyTrue :
        writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M) = true := by
      exact (List.any_eq_true).2 ⟨(c.state, bCur), hCurMem, hCurTrue⟩
    simpa [c, hWriteTrue] using hAnyTrue
  · have hWriteFalse : (TM.stepConfig (M := M) c).tape c.head = false := by
      cases hVal : (TM.stepConfig (M := M) c).tape c.head <;> simp [hVal] at hWriteTrue ⊢
    have hAnyFalse :
        writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M) = false := by
      apply (List.any_eq_false).2
      intro p hp
      rcases p with ⟨q, b⟩
      by_cases hq : q = c.state
      · subst hq
        by_cases hb : b = bCur
        · subst hb
          cases hStep : M.step c.state bCur with
          | mk qn bm =>
              cases bm with
              | mk wr mv =>
                  have hWrFalse : wr = false := by
                    have : (TM.stepConfig (M := M) c).tape c.head = false := by
                      simpa [c] using hWriteFalse
                    simpa [TM.stepConfig, c, bCur, hStep] using this
                  have hBranch :
                      Boolcube.Circuit.eval
                          (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, bCur)) x
                        = true :=
                    branchIndicator_eval_current_of_spec (M := M) (n := n) sc f hSpec x
                  unfold writeTermEval
                  simp [ConfigCircuits.writeTerm, Boolcube.Circuit.eval, c, hStep, hWrFalse]
        · have hBranchFalse :
            Boolcube.Circuit.eval
                (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (c.state, b)) x
              = false :=
            branchIndicator_eval_false_of_bit_ne_of_spec
              (M := M) (n := n) sc f hSpec x b hb
          cases hStep : M.step c.state b with
          | mk qn bm =>
              cases bm with
              | mk wr mv =>
                  unfold writeTermEval
                  cases wr <;> simp [ConfigCircuits.writeTerm, Boolcube.Circuit.eval, c, hStep, hBranchFalse]
      · have hBranchFalse :
          Boolcube.Circuit.eval
              (ConfigCircuits.branchIndicator M (toConfigCircuits sc) (q, b)) x
            = false :=
          branchIndicator_eval_false_of_state_ne_of_spec
            (M := M) (n := n) sc f hSpec x q b hq
        cases hStep : M.step q b with
        | mk qn bm =>
            cases bm with
            | mk wr mv =>
                unfold writeTermEval
                cases wr <;> simp [ConfigCircuits.writeTerm, Boolcube.Circuit.eval, c, hStep, hBranchFalse]
    simpa [c, hWriteFalse] using hAnyFalse

private lemma writeBit_eval_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x,
      Boolcube.Circuit.eval (ConfigCircuits.writeBit M (toConfigCircuits sc)) x
        =
      (TM.stepConfig (M := M) (f x)).tape (f x).head := by
  intro x
  have hPred :
      ((fun c => c.eval x) ∘ fun qs => ConfigCircuits.writeTerm M (toConfigCircuits sc) qs)
        =
      (fun p => writeTermEval (M := M) (n := n) sc x p) := by
    funext p
    simp [writeTermEval]
  calc
    Boolcube.Circuit.eval (ConfigCircuits.writeBit M (toConfigCircuits sc)) x
        =
      writeTermAnyEval (M := M) (n := n) sc x (stateSymbolPairs M) := by
          simp [ConfigCircuits.writeBit, writeTermAnyEval, hPred,
            Boolcube.Circuit.eval_bigOr_any]
    _ = (TM.stepConfig (M := M) (f x)).tape (f x).head :=
          writeTermAnyEval_of_spec (M := M) (n := n) sc f hSpec x

private lemma buildWriteBit_out_eval_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := (BuiltWire.buildWriteBit (M := M) (n := n) sc).ctx.circuit) (x := x)
          (BuiltWire.buildWriteBit (M := M) (n := n) sc).out
        =
      (TM.stepConfig (M := M) (f x)).tape (f x).head := by
  intro x
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildWriteBit (M := M) (n := n) sc).ctx.circuit) (x := x)
        (BuiltWire.buildWriteBit (M := M) (n := n) sc).out
      =
        Boolcube.Circuit.eval (ConfigCircuits.writeBit M (toConfigCircuits sc)) x :=
          buildWriteBit_out_eval_eq_writeBit (M := M) (n := n) sc x
    _ = (TM.stepConfig (M := M) (f x)).tape (f x).head :=
          writeBit_eval_of_spec (M := M) (n := n) sc f hSpec x

private lemma tape_mux_eq_stepTape
    (c : TM.Configuration (M := M) n)
    (i : Fin (M.tapeLength n)) :
    ((headIndicator c i && (TM.stepConfig (M := M) c).tape c.head) ||
      (!(headIndicator c i) && c.tape i))
      =
      (TM.stepConfig (M := M) c).tape i := by
  by_cases hi : i = c.head
  · subst hi
    simp [headIndicator_self]
  · have hHeadFalse : headIndicator c i = false :=
      headIndicator_ne (c := c) (h := hi)
    have hTapeOther : (TM.stepConfig (M := M) c).tape i = c.tape i := by
      cases hStep : M.step c.state (c.tape c.head) with
      | mk qn bm =>
          cases bm with
          | mk wr mv =>
              simpa [TM.stepConfig, hStep] using
                (TM.Configuration.write_other
                  (c := c) (i := c.head) (j := i) (h := hi) (b := wr))
    simpa [hHeadFalse, hTapeOther]

lemma toConfigCircuits_spec_of_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f)) :
    ConfigCircuits.Spec (cc := toConfigCircuits sc) (f := f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    change Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.tape i)) x = (f x).tape i
    simpa [toTreeWire, StraightConfig.evalTape] using hsc.tape_eq x i
  · intro x i
    change Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.head i)) x = headIndicator (f x) i
    simpa [toTreeWire, StraightConfig.evalHead] using hsc.head_eq x i
  · intro x q
    change Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.state q)) x = stateIndicator M (f x) q
    simpa [toTreeWire, StraightConfig.evalState] using hsc.state_eq x q

lemma spec_of_toConfigCircuits_spec
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hcc : ConfigCircuits.Spec (cc := toConfigCircuits sc) (f := f)) :
    Spec (sc := sc) (f := f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    have hTreeEval :
        Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.tape i)) x =
          (f x).tape i := by
      simpa [toConfigCircuits, ConfigCircuits.evalTape] using hcc.tape_eq x i
    calc
      StraightLine.evalWire sc.circuit x (sc.tape i)
          = Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.tape i)) x := by
              symm
              simpa [toTreeWire] using
                (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_toCircuitWire
                  (C := sc.circuit) (x := x) (i := sc.tape i))
      _ = (f x).tape i := hTreeEval
  · intro x i
    have hTreeEval :
        Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.head i)) x =
          headIndicator (f x) i := by
      simpa [toConfigCircuits, ConfigCircuits.evalHead] using hcc.head_eq x i
    calc
      StraightLine.evalWire sc.circuit x (sc.head i)
          = Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.head i)) x := by
              symm
              simpa [toTreeWire] using
                (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_toCircuitWire
                  (C := sc.circuit) (x := x) (i := sc.head i))
      _ = headIndicator (f x) i := hTreeEval
  · intro x q
    have hTreeEval :
        Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.state q)) x =
          stateIndicator M (f x) q := by
      simpa [toConfigCircuits, ConfigCircuits.evalState] using hcc.state_eq x q
    calc
      StraightLine.evalWire sc.circuit x (sc.state q)
          = Boolcube.Circuit.eval (toTreeWire sc.circuit (sc.state q)) x := by
              symm
              simpa [toTreeWire] using
                (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_toCircuitWire
                  (C := sc.circuit) (x := x) (i := sc.state q))
      _ = stateIndicator M (f x) q := hTreeEval

/-- Base straight-line circuit with two constants: gate `n` is `false`, gate `n+1` is `true`. -/
noncomputable def constBaseCircuit (n : Nat) : StraightLineCircuit n where
  gates := 2
  gate := fun g =>
    match g.1 with
    | 0 => LegacyStraightOp.const false
    | _ => LegacyStraightOp.const true
  output := ⟨n, by omega⟩

/-- Initial straight-line configuration encoding for `M` at input length `n`. -/
noncomputable def initialStraightConfig (M : TM) (n : Nat) : StraightConfig M n where
  circuit := constBaseCircuit n
  tape := fun i =>
    if hi : (i : Nat) < n then
      ⟨i, by
        have : (i : Nat) < n + 2 := lt_of_lt_of_le hi (Nat.le_add_right n 2)
        simpa [constBaseCircuit] using this⟩
    else
      ⟨n, by
        have : n < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩
  head := fun i =>
    if h0 : i = ⟨0, by
          have : (0 : Nat) < n + M.runTime n + 1 := Nat.succ_pos _
          simpa [TM.tapeLength] using this⟩ then
      ⟨n + 1, by
        have : n + 1 < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩
    else
      ⟨n, by
        have : n < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩
  state := fun q =>
    if hs : q = M.start then
      ⟨n + 1, by
        have : n + 1 < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩
    else
      ⟨n, by
        have : n < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩

lemma constBase_evalWire_input (n : Nat) (x : Point n) (i : Fin n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (constBaseCircuit n) x
      ⟨i, by
        have : (i : Nat) < n + 2 := lt_of_lt_of_le i.isLt (Nat.le_add_right n 2)
        simpa [constBaseCircuit] using this⟩ = x i := by
  simpa [Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire] using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.evalWireInternal_input
      (C := constBaseCircuit n) (x := x) (i := i))

lemma constBase_evalWire_false (n : Nat) (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (constBaseCircuit n) x
      ⟨n, by
        have : n < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩ = false := by
  have hgate := Pnp3.Internal.PsubsetPpoly.StraightLine.evalWireInternal_gate
      (C := constBaseCircuit n) (x := x) (j := 0)
      (by simp [constBaseCircuit])
  simpa [Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire,
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalGateAux, constBaseCircuit] using hgate

lemma constBase_evalWire_true (n : Nat) (x : Point n) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (constBaseCircuit n) x
      ⟨n + 1, by
        have : n + 1 < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩ = true := by
  have hgate := Pnp3.Internal.PsubsetPpoly.StraightLine.evalWireInternal_gate
      (C := constBaseCircuit n) (x := x) (j := 1)
      (by simp [constBaseCircuit])
  simpa [Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire,
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalGateAux, constBaseCircuit] using hgate

lemma constBase_adapter_eval_false (n : Nat) (x : Point n) :
    Pnp3.Complexity.StraightLineAdapter.eval (constBaseCircuit n) x = false := by
  unfold Pnp3.Complexity.StraightLineAdapter.eval
    Pnp3.Complexity.StraightLineAdapter.toDag
  simp [Pnp3.Complexity.StraightLineAdapter.toDagWire,
    Pnp3.Complexity.StraightLineAdapter.toDagOp,
    constBaseCircuit, ComplexityInterfaces.DagCircuit.eval,
    ComplexityInterfaces.DagCircuit.eval.evalGateAt]

lemma constBase_adapter_eval_true (n : Nat) (x : Point n) :
    Pnp3.Complexity.StraightLineAdapter.eval
      (Pnp3.Complexity.StraightLineAdapter.withOutput (constBaseCircuit n)
        ⟨n + 1, by
          have : n + 1 < n + 2 := by omega
          simpa [constBaseCircuit] using this⟩) x = true := by
  unfold Pnp3.Complexity.StraightLineAdapter.eval
    Pnp3.Complexity.StraightLineAdapter.toDag
    Pnp3.Complexity.StraightLineAdapter.withOutput
  simp [Pnp3.Complexity.StraightLineAdapter.toDagWire,
    Pnp3.Complexity.StraightLineAdapter.toDagOp,
    constBaseCircuit, ComplexityInterfaces.DagCircuit.eval,
    ComplexityInterfaces.DagCircuit.eval.evalGateAt]

lemma initialStraightConfig_spec (M : TM) (n : Nat) :
    StraightConfig.Spec (sc := initialStraightConfig M n)
      (f := fun x => M.initialConfig x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    unfold StraightConfig.evalTape initialStraightConfig
    by_cases hi : (i : Nat) < n
    · simp [hi, TM.initialConfig]
      simpa using constBase_evalWire_input n x ⟨i, hi⟩
    · have hi' : n ≤ (i : Nat) := Nat.le_of_not_gt hi
      simp [hi, TM.initialConfig, constBase_evalWire_false]
  · intro x i
    unfold StraightConfig.evalHead initialStraightConfig
    let i0 : Fin (M.tapeLength n) := ⟨0, by
      have : (0 : Nat) < n + M.runTime n + 1 := Nat.succ_pos _
      simpa [TM.tapeLength] using this⟩
    let idxT : Fin (n + (constBaseCircuit n).gates) := ⟨n + 1, by
      have : n + 1 < n + 2 := by omega
      simpa [constBaseCircuit] using this⟩
    let idxF : Fin (n + (constBaseCircuit n).gates) := ⟨n, by
      have : n < n + 2 := by omega
      simpa [constBaseCircuit] using this⟩
    change Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (constBaseCircuit n) x
      (if i = i0 then idxT else idxF)
      = decide (i0 = i)
    by_cases h0 : i = i0
    · subst h0
      have hif : (if i0 = i0 then idxT else idxF) = idxT := by simp
      have hdec : decide (i0 = i0) = true := by simp
      simpa [hif, hdec, idxT] using constBase_evalWire_true n x
    · have h0' : ¬ i0 = i := by exact fun h => h0 h.symm
      have hif : (if i = i0 then idxT else idxF) = idxF := by simp [h0]
      have hdec : decide (i0 = i) = false := by simp [h0']
      simpa [hif, hdec, idxF] using constBase_evalWire_false n x
  · intro x q
    unfold StraightConfig.evalState initialStraightConfig
    by_cases hs : q = M.start
    · simp [stateIndicator, TM.initialConfig, hs, constBase_evalWire_true]
    · have hs' : ¬ (M.start = q) := by
        intro h
        exact hs h.symm
      simp [stateIndicator, TM.initialConfig, hs, hs', constBase_evalWire_false]

/--
One straight-line simulation step.

Current implementation keeps the shared circuit/wire layout stable; semantic
alignment with `ConfigCircuits.stepCircuits` is established in step 8.
-/
noncomputable def stepCompiledTruthTable (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n := by
  classical
  let ccStep : ConfigCircuits M n :=
    ConfigCircuits.stepCircuits M (toConfigCircuits sc)
  let tapePack :
      Pnp3.Internal.PsubsetPpoly.StraightLine.CompiledFin n (M.tapeLength n) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFin (n := n) (m := M.tapeLength n)
      (fun i => ccStep.tape i)
  let headPack :
      Pnp3.Internal.PsubsetPpoly.StraightLine.CompiledFin n (M.tapeLength n) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFin (n := n) (m := M.tapeLength n)
      (fun i => ccStep.head i)
  let statePack :
      Pnp3.Internal.PsubsetPpoly.StraightLine.CompiledFin n (stateCard M) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFin (n := n) (m := stateCard M)
      (fun i => ccStep.state ((stateEquiv M).symm i))
  let c01 := Pnp3.Internal.PsubsetPpoly.StraightLine.appendCircuit tapePack.ckt headPack.ckt
  let cAll := Pnp3.Internal.PsubsetPpoly.StraightLine.appendCircuit c01 statePack.ckt
  refine {
    circuit := cAll
    tape := ?_
    head := ?_
    state := ?_
  }
  · intro i
    let w0 := Pnp3.Internal.PsubsetPpoly.StraightLine.leftWireInAppend
      tapePack.ckt headPack.ckt (tapePack.out i)
    exact Pnp3.Internal.PsubsetPpoly.StraightLine.leftWireInAppend c01 statePack.ckt w0
  · intro i
    let wHead :=
      Pnp3.Internal.PsubsetPpoly.StraightLine.liftWireIntoAppend
        (n := n) (g₁ := tapePack.ckt.gates) (g₂ := headPack.ckt.gates)
        (headPack.out i)
    exact Pnp3.Internal.PsubsetPpoly.StraightLine.leftWireInAppend c01 statePack.ckt wHead
  · intro q
    let wState0 :=
      Pnp3.Internal.PsubsetPpoly.StraightLine.liftWireIntoAppend
        (n := n) (g₁ := c01.gates) (g₂ := statePack.ckt.gates)
        (statePack.out (stateEquiv M q))
    exact wState0

/--
Linear-step switch-point for `StraightConfig`.

Constructive append-only assembly over one shared circuit:
`writeBit -> nextTapeAll -> nextHeadAll -> nextStateAll`.

The observable selectors are currently lifted from the input configuration
through the final shared builder context; this keeps the construction
append-only while preserving wire well-typedness.
-/
noncomputable abbrev stepCompiledLinearCandidate (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n := by
  classical
  let tapeRes := BuiltWire.buildNextTapeAll (M := M) (n := n) sc
  let bcTape := tapeRes.1
  let headRes := BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc (tapeIndexList M n) bcTape
  let bcHead := headRes.1
  let stateRes := BuiltWire.buildNextStateAllAux (M := M) (n := n) sc (stateList M) bcHead
  let bcFinal := stateRes.1
  exact
    { circuit := bcFinal.bw.ctx.circuit
      tape := fun i =>
        let hSomeTape :
            (BuiltWire.buildNextTapeAllLookup (M := M) (n := n) sc i).isSome :=
          BuiltWire.buildNextTapeAllLookup_isSome (M := M) (n := n) sc i
        let wTape : Fin (n + bcTape.bw.ctx.circuit.gates) := by
          simpa [tapeRes, bcTape] using
            (Option.get
              (BuiltWire.buildNextTapeAllLookup (M := M) (n := n) sc i)
              hSomeTape)
        have hTapeToHead : bcTape.bw.ctx.circuit.gates ≤ bcHead.bw.ctx.circuit.gates := by
          simpa [headRes, bcHead] using
            (BuiltWire.buildNextHeadAllAux_start_le_final (M := M) (n := n) sc
              (js := tapeIndexList M n) (bc := bcTape))
        have hHeadToFinal : bcHead.bw.ctx.circuit.gates ≤ bcFinal.bw.ctx.circuit.gates := by
          simpa [stateRes, bcFinal] using
            (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc
              (qs := stateList M) (bc := bcHead))
        BuiltWire.castWireLe (n := n)
          (g := bcTape.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          (le_trans hTapeToHead hHeadToFinal)
          wTape
      head := fun j =>
        let hSomeHead :
            (BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc (tapeIndexList M n) bcTape j).isSome :=
          BuiltWire.buildNextHeadAllAuxLookup_isSome_tapeIndex (M := M) (n := n) sc bcTape j
        let wHead : Fin (n + bcHead.bw.ctx.circuit.gates) := by
          simpa [headRes, bcHead] using
            (Option.get
              (BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc (tapeIndexList M n) bcTape j)
              hSomeHead)
        have hHeadToFinal : bcHead.bw.ctx.circuit.gates ≤ bcFinal.bw.ctx.circuit.gates := by
          simpa [stateRes, bcFinal] using
            (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc
              (qs := stateList M) (bc := bcHead))
        BuiltWire.castWireLe (n := n)
          (g := bcHead.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          hHeadToFinal
          wHead
      state := fun q =>
        let hSome :
            (BuiltWire.buildNextStateAllAuxLookup (M := M) (n := n) sc (stateList M) bcHead q).isSome :=
          BuiltWire.buildNextStateAllAuxLookup_isSome_stateList (M := M) (n := n) sc bcHead q
        by
          simpa [stateRes, bcFinal] using
            (Option.get
              (BuiltWire.buildNextStateAllAuxLookup (M := M) (n := n) sc (stateList M) bcHead q)
              hSome) }

private lemma stepCompiledLinearCandidateState_spec_internal
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x q,
      evalState (stepCompiledLinearCandidate M sc) x q
        =
      stateIndicator M (TM.stepConfig (M := M) (f x)) q := by
  intro x q
  classical
  let tapeRes := BuiltWire.buildNextTapeAll (M := M) (n := n) sc
  let bcTape := tapeRes.1
  let headRes := BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc (tapeIndexList M n) bcTape
  let bcHead := headRes.1
  have hq : q ∈ stateList M := state_mem_stateList M q
  simpa [evalState, stepCompiledLinearCandidate, tapeRes, bcTape, headRes, bcHead] using
    (buildNextStateAllAuxLookup_eval (M := M) (n := n) (sc := sc) (f := f) hSpec
      (qs := stateList M) (bc := bcHead) q hq x)

private lemma buildNextHeadAllAuxLookup_eval
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
      (j : Fin (M.tapeLength n)) (hj : j ∈ js) (x : Point n),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit)
        (x := x)
        ((BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc js bc j).get
          (BuiltWire.buildNextHeadAllAuxLookup_isSome_of_mem (M := M) (n := n) sc js bc j hj))
      =
      headIndicator (TM.stepConfig (M := M) (f x)) j := by
  intro js
  induction js with
  | nil =>
      intro bc j hj x
      cases hj
  | cons j0 js ih =>
      intro bc j hj x
      let bcReset := BuiltWire.BuiltCarry.appendConst (bc := bc) false
      let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcReset.bw, bcReset.bw.out⟩
      let bcHead := BuiltWire.buildNextHeadAux (M := M) (n := n) sc j0 (BuiltWire.headStateSymbolPairs M n) bc0
      let bcNext : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      by_cases hEq : j = j0
      · subst j
        have hHeadEval :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcHead.bw.ctx.circuit) (x := x) bcHead.bw.out
              =
                headIndicator (TM.stepConfig (M := M) (f x)) j0 := by
          simpa [bcReset, bc0, bcHead] using
            (buildNextHeadAux_out_eval_spec_from_reset (M := M) (n := n) sc f hSpec bc x j0)
        let wOutNext : Fin (n + bcNext.bw.ctx.circuit.gates) := by
          simpa [bcNext] using bcHead.bw.out
        have hRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit)
                (x := x)
                (BuiltWire.castWireLe (n := n)
                  (g := bcNext.bw.ctx.circuit.gates)
                  (g' := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
                  (BuiltWire.buildNextHeadAllAux_start_le_final (M := M) (n := n) sc js bcNext)
                  wOutNext)
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcNext.bw.ctx.circuit) (x := x) wOutNext := by
          simpa using
            (BuiltWire.buildNextHeadAllAux_preserves_old_eval
              (M := M) (n := n) sc js bcNext x wOutNext)
        have hGoalToRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc (j0 :: js) bc).1.bw.ctx.circuit)
                (x := x)
                ((BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc (j0 :: js) bc j0).get
                  (BuiltWire.buildNextHeadAllAuxLookup_isSome_of_mem
                    (M := M) (n := n) sc (j0 :: js) bc j0 hj))
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit)
                  (x := x)
                  (BuiltWire.castWireLe (n := n)
                    (g := bcNext.bw.ctx.circuit.gates)
                    (g' := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
                    (BuiltWire.buildNextHeadAllAux_start_le_final (M := M) (n := n) sc js bcNext)
                    wOutNext) := by
          simpa [BuiltWire.buildNextHeadAllAux, BuiltWire.buildNextHeadAllAuxLookup,
            bcReset, bc0, bcHead, bcNext, wOutNext]
        calc
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc (j0 :: js) bc).1.bw.ctx.circuit)
              (x := x)
              ((BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc (j0 :: js) bc j0).get
                (BuiltWire.buildNextHeadAllAuxLookup_isSome_of_mem
                  (M := M) (n := n) sc (j0 :: js) bc j0 hj))
            =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit)
              (x := x)
              (BuiltWire.castWireLe (n := n)
                (g := bcNext.bw.ctx.circuit.gates)
                (g' := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates)
                (BuiltWire.buildNextHeadAllAux_start_le_final (M := M) (n := n) sc js bcNext)
                wOutNext) := hGoalToRaw
          _ =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) wOutNext := hRaw
          _ =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcHead.bw.ctx.circuit) (x := x) bcHead.bw.out := by
                simpa [bcNext, wOutNext]
          _ = headIndicator (TM.stepConfig (M := M) (f x)) j0 := hHeadEval
      · have hjTail : j ∈ js := by
          simpa [hEq] using hj
        have hTail :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit)
                (x := x)
                ((BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc js bcNext j).get
                  (BuiltWire.buildNextHeadAllAuxLookup_isSome_of_mem
                    (M := M) (n := n) sc js bcNext j hjTail))
              =
                headIndicator (TM.stepConfig (M := M) (f x)) j :=
          ih bcNext j hjTail x
        simpa [BuiltWire.buildNextHeadAllAux, BuiltWire.buildNextHeadAllAuxLookup,
          bcReset, bc0, bcHead, bcNext, hEq] using hTail

private lemma stepCompiledLinearCandidateHead_spec_internal
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x i,
      evalHead (stepCompiledLinearCandidate M sc) x i
        =
      headIndicator (TM.stepConfig (M := M) (f x)) i := by
  intro x i
  classical
  let tapeRes := BuiltWire.buildNextTapeAll (M := M) (n := n) sc
  let bcTape := tapeRes.1
  let headRes := BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc (tapeIndexList M n) bcTape
  let bcHead := headRes.1
  let stateRes := BuiltWire.buildNextStateAllAux (M := M) (n := n) sc (stateList M) bcHead
  let bcFinal := stateRes.1
  have hi : i ∈ tapeIndexList M n := by
    simpa [tapeIndexList] using (List.mem_finRange i)
  let hSomeHead :
      (BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc (tapeIndexList M n) bcTape i).isSome :=
    BuiltWire.buildNextHeadAllAuxLookup_isSome_tapeIndex (M := M) (n := n) sc bcTape i
  let wHead : Fin (n + bcHead.bw.ctx.circuit.gates) := by
    simpa [headRes, bcHead] using
      (Option.get
        (BuiltWire.buildNextHeadAllAuxLookup (M := M) (n := n) sc (tapeIndexList M n) bcTape i)
        hSomeHead)
  have hHeadToFinal : bcHead.bw.ctx.circuit.gates ≤ bcFinal.bw.ctx.circuit.gates := by
    simpa [stateRes, bcFinal] using
      (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc
        (qs := stateList M) (bc := bcHead))
  have hTransport :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcFinal.bw.ctx.circuit) (x := x)
          (BuiltWire.castWireLe (n := n)
            (g := bcHead.bw.ctx.circuit.gates)
            (g' := bcFinal.bw.ctx.circuit.gates)
            hHeadToFinal
            wHead)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcHead.bw.ctx.circuit) (x := x) wHead := by
    simpa [stateRes, bcFinal] using
      (BuiltWire.buildNextStateAllAux_preserves_old_eval
        (M := M) (n := n) sc (stateList M) bcHead x wHead)
  have hHeadStage :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcHead.bw.ctx.circuit) (x := x) wHead
        =
          headIndicator (TM.stepConfig (M := M) (f x)) i := by
    simpa [wHead, hSomeHead, headRes, bcHead] using
      (buildNextHeadAllAuxLookup_eval (M := M) (n := n) (sc := sc) (f := f) hSpec
        (js := tapeIndexList M n) (bc := bcTape) i hi x)
  calc
    evalHead (stepCompiledLinearCandidate M sc) x i
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (BuiltWire.castWireLe (n := n)
          (g := bcHead.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          hHeadToFinal
          wHead) := by
            simp [evalHead, stepCompiledLinearCandidate, tapeRes, bcTape, headRes, bcHead,
              stateRes, bcFinal, wHead, hSomeHead, hHeadToFinal]
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcHead.bw.ctx.circuit) (x := x) wHead := hTransport
    _ = headIndicator (TM.stepConfig (M := M) (f x)) i := hHeadStage

private lemma buildNextTapeFromCarry_out_eval_spec_of_write
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f))
    (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
    (x : Point n)
    (hCarryWrite :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc.bw.ctx.circuit) (x := x) bc.carry
        =
          (TM.stepConfig (M := M) (f x)).tape (f x).head)
    (i : Fin (M.tapeLength n)) :
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.out
      =
        (TM.stepConfig (M := M) (f x)).tape i := by
  let c := f x
  have hRaw :=
    BuiltWire.buildNextTapeFromCarry_out_eval (M := M) (n := n) sc i bc x
  have hHead :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.head i)
        =
          headIndicator c i := by
    simpa [evalHead, c] using hSpec.head_eq x i
  have hTape :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := sc.circuit) (x := x) (sc.tape i)
        =
          c.tape i := by
    simpa [evalTape, c] using hSpec.tape_eq x i
  calc
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.ctx.circuit) (x := x)
        (BuiltWire.buildNextTapeFromCarry (M := M) (n := n) sc i bc).bw.out
      =
        ((Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.carry) ||
         (!(Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.head i)) &&
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := sc.circuit) (x := x) (sc.tape i))) := hRaw
    _ =
      ((headIndicator c i && (TM.stepConfig (M := M) c).tape c.head) ||
        (!(headIndicator c i) && c.tape i)) := by
          simp [hHead, hTape, c, hCarryWrite]
    _ = (TM.stepConfig (M := M) c).tape i :=
          tape_mux_eq_stepTape (M := M) (n := n) c i

private lemma buildNextTapeAllAuxLookup_eval
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ (is : List (Fin (M.tapeLength n))) (bc : BuiltWire.BuiltCarry (n := n) sc.circuit)
      (x : Point n)
      (hCarryWrite :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bc.bw.ctx.circuit) (x := x) bc.carry
          =
            (TM.stepConfig (M := M) (f x)).tape (f x).head)
      (i : Fin (M.tapeLength n)) (hi : i ∈ is),
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bc).1.bw.ctx.circuit)
        (x := x)
        ((BuiltWire.buildNextTapeAllAuxLookup (M := M) (n := n) sc is bc i).get
          (BuiltWire.buildNextTapeAllAuxLookup_isSome_of_mem (M := M) (n := n) sc is bc i hi))
      =
      (TM.stepConfig (M := M) (f x)).tape i := by
  intro is
  induction is with
  | nil =>
      intro bc x hCarryWrite i hi
      cases hi
  | cons i0 is ih =>
      intro bc x hCarryWrite i hi
      let bcNext := BuiltWire.buildNextTapeFromCarry (M := M) (n := n) sc i0 bc
      by_cases hEq : i = i0
      · subst i
        have hCell :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x) bcNext.bw.out
              =
                (TM.stepConfig (M := M) (f x)).tape i0 := by
          simpa [bcNext] using
            (buildNextTapeFromCarry_out_eval_spec_of_write
              (M := M) (n := n) (sc := sc) (f := f) hSpec bc x hCarryWrite i0)
        let wOutNext : Fin (n + bcNext.bw.ctx.circuit.gates) := by
          simpa using bcNext.bw.out
        have hRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit)
                (x := x)
                (BuiltWire.castWireLe (n := n)
                  (g := bcNext.bw.ctx.circuit.gates)
                  (g' := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
                  (BuiltWire.buildNextTapeAllAux_start_le_final (M := M) (n := n) sc is bcNext)
                  wOutNext)
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bcNext.bw.ctx.circuit) (x := x) wOutNext := by
          simpa using
            (BuiltWire.buildNextTapeAllAux_preserves_old_eval
              (M := M) (n := n) sc is bcNext x wOutNext)
        have hGoalToRaw :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc (i0 :: is) bc).1.bw.ctx.circuit)
                (x := x)
                ((BuiltWire.buildNextTapeAllAuxLookup (M := M) (n := n) sc (i0 :: is) bc i0).get
                  (BuiltWire.buildNextTapeAllAuxLookup_isSome_of_mem
                    (M := M) (n := n) sc (i0 :: is) bc i0 hi))
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit)
                  (x := x)
                  (BuiltWire.castWireLe (n := n)
                    (g := bcNext.bw.ctx.circuit.gates)
                    (g' := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
                    (BuiltWire.buildNextTapeAllAux_start_le_final (M := M) (n := n) sc is bcNext)
                    wOutNext) := by
          simpa [BuiltWire.buildNextTapeAllAux, BuiltWire.buildNextTapeAllAuxLookup,
            bcNext, wOutNext]
        calc
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc (i0 :: is) bc).1.bw.ctx.circuit)
              (x := x)
              ((BuiltWire.buildNextTapeAllAuxLookup (M := M) (n := n) sc (i0 :: is) bc i0).get
                (BuiltWire.buildNextTapeAllAuxLookup_isSome_of_mem
                  (M := M) (n := n) sc (i0 :: is) bc i0 hi))
            =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit)
              (x := x)
              (BuiltWire.castWireLe (n := n)
                (g := bcNext.bw.ctx.circuit.gates)
                (g' := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit.gates)
                (BuiltWire.buildNextTapeAllAux_start_le_final (M := M) (n := n) sc is bcNext)
                wOutNext) := hGoalToRaw
          _ =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) wOutNext := hRaw
          _ =
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
              (C := bcNext.bw.ctx.circuit) (x := x) bcNext.bw.out := by
                simpa [wOutNext]
          _ = (TM.stepConfig (M := M) (f x)).tape i0 := hCell
      · have hiTail : i ∈ is := by
          simpa [hEq] using hi
        have hCarryNext :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x) bcNext.carry
              =
                (TM.stepConfig (M := M) (f x)).tape (f x).head := by
          calc
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := bcNext.bw.ctx.circuit) (x := x) bcNext.carry
              =
                Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                  (C := bc.bw.ctx.circuit) (x := x) bc.carry := by
                    simpa [bcNext] using
                      (BuiltWire.buildNextTapeFromCarry_carry_eval (M := M) (n := n) sc i0 bc x)
            _ = (TM.stepConfig (M := M) (f x)).tape (f x).head := hCarryWrite
        have hTail :
            Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (C := (BuiltWire.buildNextTapeAllAux (M := M) (n := n) sc is bcNext).1.bw.ctx.circuit)
                (x := x)
                ((BuiltWire.buildNextTapeAllAuxLookup (M := M) (n := n) sc is bcNext i).get
                  (BuiltWire.buildNextTapeAllAuxLookup_isSome_of_mem
                    (M := M) (n := n) sc is bcNext i hiTail))
              =
                (TM.stepConfig (M := M) (f x)).tape i :=
          ih bcNext x hCarryNext i hiTail
        simpa [BuiltWire.buildNextTapeAllAux, BuiltWire.buildNextTapeAllAuxLookup,
          bcNext, hEq] using hTail

private lemma buildNextTapeAllLookup_eval
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x i,
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := (BuiltWire.buildNextTapeAll (M := M) (n := n) sc).1.bw.ctx.circuit)
        (x := x)
        ((BuiltWire.buildNextTapeAllLookup (M := M) (n := n) sc i).get
          (BuiltWire.buildNextTapeAllLookup_isSome (M := M) (n := n) sc i))
      =
      (TM.stepConfig (M := M) (f x)).tape i := by
  intro x i
  let bwWrite := BuiltWire.buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltWire.BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  have hi : i ∈ tapeIndexList M n := by
    simpa [tapeIndexList] using (List.mem_finRange i)
  have hCarryWrite0 :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bc0.bw.ctx.circuit) (x := x) bc0.carry
        =
          (TM.stepConfig (M := M) (f x)).tape (f x).head := by
    simpa [bc0, bwWrite] using
      (buildWriteBit_out_eval_spec (M := M) (n := n) sc f hSpec x)
  simpa [BuiltWire.buildNextTapeAllLookup, BuiltWire.buildNextTapeAll, bc0, bwWrite] using
    (buildNextTapeAllAuxLookup_eval (M := M) (n := n) (sc := sc) (f := f) hSpec
      (is := tapeIndexList M n) (bc := bc0) (x := x) hCarryWrite0 i hi)

private lemma stepCompiledLinearCandidateTape_spec_internal
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hSpec : Spec (sc := sc) (f := f)) :
    ∀ x i,
      evalTape (stepCompiledLinearCandidate M sc) x i
        =
      (TM.stepConfig (M := M) (f x)).tape i := by
  intro x i
  classical
  let tapeRes := BuiltWire.buildNextTapeAll (M := M) (n := n) sc
  let bcTape := tapeRes.1
  let headRes := BuiltWire.buildNextHeadAllAux (M := M) (n := n) sc (tapeIndexList M n) bcTape
  let bcHead := headRes.1
  let stateRes := BuiltWire.buildNextStateAllAux (M := M) (n := n) sc (stateList M) bcHead
  let bcFinal := stateRes.1
  let hSomeTape :
      (BuiltWire.buildNextTapeAllLookup (M := M) (n := n) sc i).isSome :=
    BuiltWire.buildNextTapeAllLookup_isSome (M := M) (n := n) sc i
  let wTape : Fin (n + bcTape.bw.ctx.circuit.gates) := by
    simpa [tapeRes, bcTape] using
      (Option.get (BuiltWire.buildNextTapeAllLookup (M := M) (n := n) sc i) hSomeTape)
  have hTapeToHead : bcTape.bw.ctx.circuit.gates ≤ bcHead.bw.ctx.circuit.gates := by
    simpa [headRes, bcHead] using
      (BuiltWire.buildNextHeadAllAux_start_le_final (M := M) (n := n) sc
        (js := tapeIndexList M n) (bc := bcTape))
  have hHeadToFinal : bcHead.bw.ctx.circuit.gates ≤ bcFinal.bw.ctx.circuit.gates := by
    simpa [stateRes, bcFinal] using
      (BuiltWire.buildNextStateAllAux_start_le_final (M := M) (n := n) sc
        (qs := stateList M) (bc := bcHead))
  have hTransportHead :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcHead.bw.ctx.circuit) (x := x)
          (BuiltWire.castWireLe (n := n)
            (g := bcTape.bw.ctx.circuit.gates)
            (g' := bcHead.bw.ctx.circuit.gates)
            hTapeToHead
            wTape)
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcTape.bw.ctx.circuit) (x := x) wTape := by
    simpa [headRes, bcHead] using
      (BuiltWire.buildNextHeadAllAux_preserves_old_eval
        (M := M) (n := n) sc (tapeIndexList M n) bcTape x wTape)
  have hTransportFinal :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcFinal.bw.ctx.circuit) (x := x)
          (BuiltWire.castWireLe (n := n)
            (g := bcHead.bw.ctx.circuit.gates)
            (g' := bcFinal.bw.ctx.circuit.gates)
            hHeadToFinal
            (BuiltWire.castWireLe (n := n)
              (g := bcTape.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates)
              hTapeToHead
              wTape))
        =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := bcHead.bw.ctx.circuit) (x := x)
            (BuiltWire.castWireLe (n := n)
              (g := bcTape.bw.ctx.circuit.gates)
              (g' := bcHead.bw.ctx.circuit.gates)
              hTapeToHead
              wTape) := by
    simpa [stateRes, bcFinal] using
      (BuiltWire.buildNextStateAllAux_preserves_old_eval
        (M := M) (n := n) sc (stateList M) bcHead x
        (BuiltWire.castWireLe (n := n)
          (g := bcTape.bw.ctx.circuit.gates)
          (g' := bcHead.bw.ctx.circuit.gates)
          hTapeToHead
          wTape))
  have hCast :
      BuiltWire.castWireLe (n := n)
        (g := bcTape.bw.ctx.circuit.gates)
        (g' := bcFinal.bw.ctx.circuit.gates)
        (Nat.le_trans hTapeToHead hHeadToFinal)
        wTape
      =
      BuiltWire.castWireLe (n := n)
        (g := bcHead.bw.ctx.circuit.gates)
        (g' := bcFinal.bw.ctx.circuit.gates)
        hHeadToFinal
        (BuiltWire.castWireLe (n := n)
          (g := bcTape.bw.ctx.circuit.gates)
          (g' := bcHead.bw.ctx.circuit.gates)
          hTapeToHead
          wTape) := by
    simp [BuiltWire.castWireLe_trans]
  have hTapeStage :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := bcTape.bw.ctx.circuit) (x := x) wTape
        =
          (TM.stepConfig (M := M) (f x)).tape i := by
    simpa [wTape, hSomeTape, tapeRes, bcTape] using
      (buildNextTapeAllLookup_eval (M := M) (n := n) (sc := sc) (f := f) hSpec x i)
  calc
    evalTape (stepCompiledLinearCandidate M sc) x i
        =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (BuiltWire.castWireLe (n := n)
          (g := bcTape.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          (Nat.le_trans hTapeToHead hHeadToFinal)
          wTape) := by
            simp [evalTape, stepCompiledLinearCandidate, tapeRes, bcTape, headRes, bcHead,
              stateRes, bcFinal, wTape, hSomeTape, hTapeToHead, hHeadToFinal]
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcFinal.bw.ctx.circuit) (x := x)
        (BuiltWire.castWireLe (n := n)
          (g := bcHead.bw.ctx.circuit.gates)
          (g' := bcFinal.bw.ctx.circuit.gates)
          hHeadToFinal
          (BuiltWire.castWireLe (n := n)
            (g := bcTape.bw.ctx.circuit.gates)
            (g' := bcHead.bw.ctx.circuit.gates)
            hTapeToHead
            wTape)) := by
              rw [hCast]
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcHead.bw.ctx.circuit) (x := x)
        (BuiltWire.castWireLe (n := n)
          (g := bcTape.bw.ctx.circuit.gates)
          (g' := bcHead.bw.ctx.circuit.gates)
          hTapeToHead
          wTape) := hTransportFinal
    _ =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
        (C := bcTape.bw.ctx.circuit) (x := x) wTape := hTransportHead
    _ = (TM.stepConfig (M := M) (f x)).tape i := hTapeStage

lemma stepCompiledLinearCandidate_gates_le_budgetExpanded (M : TM) {n : Nat} (sc : StraightConfig M n) :
    (stepCompiledLinearCandidate M sc).circuit.gates ≤
      sc.circuit.gates + BuiltWire.linearStepBudgetExpanded M n := by
  unfold stepCompiledLinearCandidate
  dsimp
  have hStages := BuiltWire.buildLinearStages_gates_le (M := M) (n := n) sc
  have hBudget :
      sc.circuit.gates +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
          4 * (M.tapeLength n) +
          (((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) + 1) * (M.tapeLength n) +
          (((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) + 1) * (stateCard M)
        ≤ sc.circuit.gates + BuiltWire.linearStepBudgetExpanded M n := by
    unfold BuiltWire.linearStepBudgetExpanded
    omega
  exact Nat.le_trans hStages hBudget

/--
Semantic switch-point for the linear-step route.

At this stage the canonical semantic behavior is kept aligned with the proven
truth-table step, while the append-only candidate remains available under
`stepCompiledLinearCandidate` for size-only development.
-/
noncomputable abbrev stepCompiledLinear (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n :=
  stepCompiledLinearCandidate M sc

/--
Current one-step compiled simulator.

Kept as stable public name for the semantics-proved route.
-/
noncomputable abbrev stepCompiled (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n :=
  stepCompiledTruthTable M sc

lemma stepCompiled_spec_of_semantics
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f))
    (hTape :
      ∀ x i,
        Boolcube.Circuit.eval ((toConfigCircuits (stepCompiled M sc)).tape i) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).tape i) x)
    (hHead :
      ∀ x i,
        Boolcube.Circuit.eval ((toConfigCircuits (stepCompiled M sc)).head i) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).head i) x)
    (hState :
      ∀ x q,
        Boolcube.Circuit.eval ((toConfigCircuits (stepCompiled M sc)).state q) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).state q) x) :
    Spec (sc := stepCompiled M sc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  have hTree : ConfigCircuits.Spec (cc := toConfigCircuits sc) (f := f) :=
    toConfigCircuits_spec_of_spec (sc := sc) (f := f) hsc
  have hTreeStep :
      ConfigCircuits.Spec
        (cc := ConfigCircuits.stepCircuits M (toConfigCircuits sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) :=
    ConfigCircuits.step_spec (M := M) (cc := toConfigCircuits sc) (f := f) hTree
  have hTreeStep' :
      ConfigCircuits.Spec (cc := toConfigCircuits (stepCompiled M sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x i
      exact (hTape x i).trans (hTreeStep.tape_eq x i)
    · intro x i
      exact (hHead x i).trans (hTreeStep.head_eq x i)
    · intro x q
      exact (hState x q).trans (hTreeStep.state_eq x q)
  exact spec_of_toConfigCircuits_spec (sc := stepCompiled M sc)
    (f := fun x => TM.stepConfig (M := M) (f x)) hTreeStep'

/-- Semantic contract for `stepCompiled` at fixed machine/input length. -/
def StepCompiledSemantics (M : TM) (n : Nat) : Prop :=
  ∀ (sc : StraightConfig M n),
    (∀ x i,
      Boolcube.Circuit.eval ((toConfigCircuits (stepCompiled M sc)).tape i) x =
        Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).tape i) x) ∧
    (∀ x i,
      Boolcube.Circuit.eval ((toConfigCircuits (stepCompiled M sc)).head i) x =
        Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).head i) x) ∧
    (∀ x q,
      Boolcube.Circuit.eval ((toConfigCircuits (stepCompiled M sc)).state q) x =
        Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).state q) x)

/-- Semantic contract for `stepCompiledLinearCandidate` at fixed machine/input length. -/
def StepCompiledLinearCandidateSemantics (M : TM) (n : Nat) : Prop :=
  ∀ (sc : StraightConfig M n),
    (∀ x i,
      Boolcube.Circuit.eval ((toConfigCircuits (stepCompiledLinearCandidate M sc)).tape i) x =
        Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).tape i) x) ∧
    (∀ x i,
      Boolcube.Circuit.eval ((toConfigCircuits (stepCompiledLinearCandidate M sc)).head i) x =
        Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).head i) x) ∧
    (∀ x q,
      Boolcube.Circuit.eval ((toConfigCircuits (stepCompiledLinearCandidate M sc)).state q) x =
        Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).state q) x)

lemma stepCompiled_semantics_of_contracts
    (hPack : Pnp3.Internal.PsubsetPpoly.StraightLine.PackFinWireSemantics)
    (hAppend : Pnp3.Internal.PsubsetPpoly.StraightLine.AppendWireSemantics)
    (M : TM) (n : Nat) :
    StepCompiledSemantics M n := by
  intro sc
  classical
  let ccStep : ConfigCircuits M n :=
    ConfigCircuits.stepCircuits M (toConfigCircuits sc)
  let tapePack :
      Pnp3.Internal.PsubsetPpoly.StraightLine.CompiledFin n (M.tapeLength n) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFin (n := n) (m := M.tapeLength n)
      (fun i => ccStep.tape i)
  let headPack :
      Pnp3.Internal.PsubsetPpoly.StraightLine.CompiledFin n (M.tapeLength n) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFin (n := n) (m := M.tapeLength n)
      (fun i => ccStep.head i)
  let statePack :
      Pnp3.Internal.PsubsetPpoly.StraightLine.CompiledFin n (stateCard M) :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFin (n := n) (m := stateCard M)
      (fun i => ccStep.state ((stateEquiv M).symm i))
  let c01 := Pnp3.Internal.PsubsetPpoly.StraightLine.appendCircuit tapePack.ckt headPack.ckt
  let cAll := Pnp3.Internal.PsubsetPpoly.StraightLine.appendCircuit c01 statePack.ckt
  rcases hAppend with ⟨hLeft, hLift⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    let w0 := Pnp3.Internal.PsubsetPpoly.StraightLine.leftWireInAppend
      tapePack.ckt headPack.ckt (tapePack.out i)
    have hA :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := cAll) (x := x)
          (Pnp3.Internal.PsubsetPpoly.StraightLine.leftWireInAppend c01 statePack.ckt w0) =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := c01) (x := x) w0 :=
      hLeft c01 statePack.ckt x w0
    have hB :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := c01) (x := x) w0 =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := tapePack.ckt) (x := x) (tapePack.out i) :=
      hLeft tapePack.ckt headPack.ckt x (tapePack.out i)
    have hC :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := tapePack.ckt) (x := x) (tapePack.out i) =
          Boolcube.Circuit.eval (ccStep.tape i) x :=
      hPack (fun j => ccStep.tape j) x i
    simpa [toTreeWire, toConfigCircuits, stepCompiled, ccStep, tapePack, headPack, statePack, c01, cAll, w0]
      using hA.trans (hB.trans hC)
  · intro x i
    let wHead :=
      Pnp3.Internal.PsubsetPpoly.StraightLine.liftWireIntoAppend
        (n := n) (g₁ := tapePack.ckt.gates) (g₂ := headPack.ckt.gates) (headPack.out i)
    have hA :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := cAll) (x := x)
          (Pnp3.Internal.PsubsetPpoly.StraightLine.leftWireInAppend c01 statePack.ckt wHead) =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := c01) (x := x) wHead :=
      hLeft c01 statePack.ckt x wHead
    have hB :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := c01) (x := x) wHead =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := headPack.ckt) (x := x) (headPack.out i) :=
      hLift tapePack.ckt headPack.ckt x (headPack.out i)
    have hC :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := headPack.ckt) (x := x) (headPack.out i) =
          Boolcube.Circuit.eval (ccStep.head i) x :=
      hPack (fun j => ccStep.head j) x i
    simpa [toTreeWire, toConfigCircuits, stepCompiled, ccStep, tapePack, headPack, statePack, c01, cAll, wHead]
      using hA.trans (hB.trans hC)
  · intro x q
    let iq : Fin (stateCard M) := stateEquiv M q
    let wState0 :=
      Pnp3.Internal.PsubsetPpoly.StraightLine.liftWireIntoAppend
        (n := n) (g₁ := c01.gates) (g₂ := statePack.ckt.gates) (statePack.out iq)
    have hA :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := cAll) (x := x) wState0 =
          Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
            (C := statePack.ckt) (x := x) (statePack.out iq) :=
      hLift c01 statePack.ckt x (statePack.out iq)
    have hB :
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
          (C := statePack.ckt) (x := x) (statePack.out iq) =
          Boolcube.Circuit.eval (ccStep.state ((stateEquiv M).symm iq)) x :=
      hPack (fun j => ccStep.state ((stateEquiv M).symm j)) x iq
    have hq : (stateEquiv M).symm iq = q := by
      simp [iq]
    simpa [toTreeWire, toConfigCircuits, stepCompiled, ccStep, tapePack, headPack, statePack, c01, cAll, iq, wState0, hq]
      using hA.trans hB

lemma stepCompiled_semantics_of_core_contracts
    (hCompile : Pnp3.Internal.PsubsetPpoly.StraightLine.CompileTreeWireSemantics)
    (hAppend : Pnp3.Internal.PsubsetPpoly.StraightLine.AppendWireSemantics)
    (M : TM) (n : Nat) :
    StepCompiledSemantics M n := by
  have hPack : Pnp3.Internal.PsubsetPpoly.StraightLine.PackFinWireSemantics :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.packFinWireSemantics_of_contracts hCompile hAppend
  exact stepCompiled_semantics_of_contracts hPack hAppend M n

lemma stepCompiled_spec_of_provider
    (M : TM) {n : Nat}
    (hSem : StepCompiledSemantics M n)
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f)) :
    Spec (sc := stepCompiled M sc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  rcases hSem sc with ⟨hTape, hRest⟩
  rcases hRest with ⟨hHead, hState⟩
  exact stepCompiled_spec_of_semantics
    (M := M) (sc := sc) (f := f) hsc hTape hHead hState

lemma stepCompiledLinearCandidate_spec_of_semantics
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f))
    (hTape :
      ∀ x i,
        Boolcube.Circuit.eval ((toConfigCircuits (stepCompiledLinearCandidate M sc)).tape i) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).tape i) x)
    (hHead :
      ∀ x i,
        Boolcube.Circuit.eval ((toConfigCircuits (stepCompiledLinearCandidate M sc)).head i) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).head i) x)
    (hState :
      ∀ x q,
        Boolcube.Circuit.eval ((toConfigCircuits (stepCompiledLinearCandidate M sc)).state q) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).state q) x) :
    Spec (sc := stepCompiledLinearCandidate M sc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  have hTree : ConfigCircuits.Spec (cc := toConfigCircuits sc) (f := f) :=
    toConfigCircuits_spec_of_spec (sc := sc) (f := f) hsc
  have hTreeStep :
      ConfigCircuits.Spec
        (cc := ConfigCircuits.stepCircuits M (toConfigCircuits sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) :=
    ConfigCircuits.step_spec (M := M) (cc := toConfigCircuits sc) (f := f) hTree
  have hTreeStep' :
      ConfigCircuits.Spec (cc := toConfigCircuits (stepCompiledLinearCandidate M sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x i
      exact (hTape x i).trans (hTreeStep.tape_eq x i)
    · intro x i
      exact (hHead x i).trans (hTreeStep.head_eq x i)
    · intro x q
      exact (hState x q).trans (hTreeStep.state_eq x q)
  exact spec_of_toConfigCircuits_spec (sc := stepCompiledLinearCandidate M sc)
    (f := fun x => TM.stepConfig (M := M) (f x)) hTreeStep'

lemma stepCompiledLinearCandidate_spec_of_provider
    (M : TM) {n : Nat}
    (hSem : StepCompiledLinearCandidateSemantics M n)
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f)) :
    Spec (sc := stepCompiledLinearCandidate M sc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  rcases hSem sc with ⟨hTape, hRest⟩
  rcases hRest with ⟨hHead, hState⟩
  exact stepCompiledLinearCandidate_spec_of_semantics
    (M := M) (sc := sc) (f := f) hsc hTape hHead hState

/--
One-step spec provider for the linear-candidate compiled step.
This is the interface consumed by `Complexity/Simulation/Circuit_Compiler`.
-/
def StepCompiledLinearCandidateStepSpecProvider (M : TM) (n : Nat) : Prop :=
  ∀ (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n),
    Spec (sc := sc) (f := f) →
      Spec (sc := stepCompiledLinearCandidate M sc)
        (f := fun x => TM.stepConfig (M := M) (f x))

lemma stepCompiledLinearCandidate_stepSpecProvider_of_fieldwise
    (M : TM) {n : Nat}
    (hTape :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n)
        (hSpec : Spec (sc := sc) (f := f)),
        ∀ x i,
          evalTape (stepCompiledLinearCandidate M sc) x i =
            (TM.stepConfig (M := M) (f x)).tape i)
    (hHead :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n)
        (hSpec : Spec (sc := sc) (f := f)),
        ∀ x i,
          evalHead (stepCompiledLinearCandidate M sc) x i =
            headIndicator (TM.stepConfig (M := M) (f x)) i)
    (hState :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n)
        (hSpec : Spec (sc := sc) (f := f)),
        ∀ x q,
          evalState (stepCompiledLinearCandidate M sc) x q =
            stateIndicator M (TM.stepConfig (M := M) (f x)) q) :
    StepCompiledLinearCandidateStepSpecProvider M n := by
  intro sc f hSpec
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    exact hTape sc f hSpec x i
  · intro x i
    exact hHead sc f hSpec x i
  · intro x q
    exact hState sc f hSpec x q

theorem stepCompiledLinearCandidateStepSpecProvider_internal
    (M : TM) (n : Nat) :
    StepCompiledLinearCandidateStepSpecProvider M n := by
  exact stepCompiledLinearCandidate_stepSpecProvider_of_fieldwise
    (M := M)
    (hTape := stepCompiledLinearCandidateTape_spec_internal (M := M))
    (hHead := stepCompiledLinearCandidateHead_spec_internal (M := M))
    (hState := stepCompiledLinearCandidateState_spec_internal (M := M))

lemma iterate_spec_of_next
    (M : TM) {n : Nat}
    (next : StraightConfig M n → StraightConfig M n)
    (hNext :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n),
        Spec (sc := sc) (f := f) →
        Spec (sc := next sc) (f := fun x => TM.stepConfig (M := M) (f x))) :
    ∀ (sc : StraightConfig M n)
      (f : Point n → TM.Configuration (M := M) n),
      Spec (sc := sc) (f := f) →
      ∀ t,
        Spec (sc := Nat.iterate next t sc)
          (f := fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x)) := by
  intro sc f hsc t
  induction t with
  | zero =>
      simpa using hsc
  | succ t ih =>
      have hPrev :
          Spec (sc := Nat.iterate next t sc)
            (f := fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x)) := ih
      have hN := hNext
        (Nat.iterate next t sc)
        (fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x))
        hPrev
      simpa [Function.iterate_succ_apply', Function.comp] using hN

lemma iterate_gates_le_of_next_gates_le
    (M : TM) {n : Nat}
    (next : StraightConfig M n → StraightConfig M n)
    (inc : Nat)
    (hNextGates : ∀ sc, (next sc).circuit.gates ≤ sc.circuit.gates + inc) :
    ∀ (t : Nat) (sc : StraightConfig M n),
      (Nat.iterate next t sc).circuit.gates ≤ sc.circuit.gates + t * inc := by
  intro t sc
  induction t generalizing sc with
  | zero =>
      simp
  | succ t ih =>
      have h1 :
          (Nat.iterate next (t + 1) sc).circuit.gates ≤
            (Nat.iterate next t sc).circuit.gates + inc := by
        simpa [Function.iterate_succ_apply'] using hNextGates (Nat.iterate next t sc)
      have h2 :
          (Nat.iterate next t sc).circuit.gates ≤ sc.circuit.gates + t * inc :=
        ih sc
      calc
        (Nat.iterate next (t + 1) sc).circuit.gates
            ≤ (Nat.iterate next t sc).circuit.gates + inc := h1
        _ ≤ sc.circuit.gates + t * inc + inc := by omega
        _ = sc.circuit.gates + (t + 1) * inc := by
              simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma iterated_stepCompiled_gates_le_of_stepCompiled_inc
    (M : TM) (n inc : Nat)
    (hStepInc : ∀ sc : StraightConfig M n,
      (stepCompiled M sc).circuit.gates ≤ sc.circuit.gates + inc) :
    (Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n)).circuit.gates ≤
      (initialStraightConfig M n).circuit.gates + (M.runTime n) * inc := by
  exact
    iterate_gates_le_of_next_gates_le
      (M := M) (n := n) (next := stepCompiled M) (inc := inc) hStepInc
      (t := M.runTime n) (sc := initialStraightConfig M n)

lemma iterated_stepCompiled_gates_le_of_stepCompiled_inc'
    (M : TM) (n inc : Nat)
    (hStepInc : ∀ sc : StraightConfig M n,
      (stepCompiled M sc).circuit.gates ≤ sc.circuit.gates + inc) :
    (Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n)).circuit.gates ≤
      2 + (M.runTime n) * inc := by
  have hBase :
      (Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n)).circuit.gates ≤
        (initialStraightConfig M n).circuit.gates + (M.runTime n) * inc :=
    iterated_stepCompiled_gates_le_of_stepCompiled_inc
      (M := M) (n := n) (inc := inc) hStepInc
  have hInit : (initialStraightConfig M n).circuit.gates = 2 := by
    simp [initialStraightConfig, constBaseCircuit]
  simpa [hInit] using hBase

lemma runtime_spec_of_next
    (M : TM) (n : Nat)
    (next : StraightConfig M n → StraightConfig M n)
    (hNext :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n),
        Spec (sc := sc) (f := f) →
        Spec (sc := next sc) (f := fun x => TM.stepConfig (M := M) (f x))) :
    Spec (sc := Nat.iterate next (M.runTime n) (initialStraightConfig M n))
      (f := fun x => M.run (n := n) x) := by
  have hInit : Spec (sc := initialStraightConfig M n) (f := fun x => M.initialConfig x) :=
    initialStraightConfig_spec M n
  have hIter := iterate_spec_of_next (M := M) (n := n) next hNext
    (sc := initialStraightConfig M n)
    (f := fun x => M.initialConfig x) hInit (M.runTime n)
  simpa [TM.run, TM.runConfig] using hIter

lemma runtime_spec_of_stepCompiledProvider
    (M : TM) (n : Nat)
    (hSem : StepCompiledSemantics M n) :
    Spec (sc := Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n))
      (f := fun x => M.run (n := n) x) := by
  refine runtime_spec_of_next (M := M) (n := n) (next := stepCompiled M) ?_
  intro sc f hsc
  exact stepCompiled_spec_of_provider (M := M) (n := n) hSem sc f hsc

lemma runtime_spec_of_stepCompiledLinearCandidateProvider
    (M : TM) (n : Nat)
    (hSem : StepCompiledLinearCandidateSemantics M n) :
    Spec (sc := Nat.iterate (stepCompiledLinearCandidate M) (M.runTime n) (initialStraightConfig M n))
      (f := fun x => M.run (n := n) x) := by
  refine runtime_spec_of_next (M := M) (n := n) (next := stepCompiledLinearCandidate M) ?_
  intro sc f hsc
  exact stepCompiledLinearCandidate_spec_of_provider (M := M) (n := n) hSem sc f hsc

lemma runtime_spec_of_stepCompiledLinearCandidateStepSpecProvider
    (M : TM) (n : Nat)
    (hStep : StepCompiledLinearCandidateStepSpecProvider M n) :
    Spec (sc := Nat.iterate (stepCompiledLinearCandidate M) (M.runTime n) (initialStraightConfig M n))
      (f := fun x => M.run (n := n) x) := by
  refine runtime_spec_of_next (M := M) (n := n) (next := stepCompiledLinearCandidate M) ?_
  intro sc f hsc
  exact hStep sc f hsc

/--
Compiled-runtime straight configuration: iterate `stepCompiled` for exactly
`runTime n` steps from the initial straight configuration.
-/
noncomputable def runtimeConfigCompiled (M : TM) (n : Nat) : StraightConfig M n :=
  Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n)

/--
Linear compiled-runtime straight configuration: iterate `stepCompiledLinear`
for exactly `runTime n` steps from the initial straight configuration.
-/
noncomputable def runtimeConfigCompiledLinear (M : TM) (n : Nat) : StraightConfig M n :=
  Nat.iterate (stepCompiledLinear M) (M.runTime n) (initialStraightConfig M n)

lemma runtimeConfigCompiled_gates_le_of_stepCompiled_inc
    (M : TM) (n inc : Nat)
    (hStepInc : ∀ sc : StraightConfig M n,
      (stepCompiled M sc).circuit.gates ≤ sc.circuit.gates + inc) :
    (runtimeConfigCompiled M n).circuit.gates ≤
      (initialStraightConfig M n).circuit.gates + (M.runTime n) * inc := by
  simpa [runtimeConfigCompiled] using
    iterated_stepCompiled_gates_le_of_stepCompiled_inc
      (M := M) (n := n) (inc := inc) hStepInc

lemma runtimeConfigCompiled_gates_le_of_stepCompiled_inc'
    (M : TM) (n inc : Nat)
    (hStepInc : ∀ sc : StraightConfig M n,
      (stepCompiled M sc).circuit.gates ≤ sc.circuit.gates + inc) :
    (runtimeConfigCompiled M n).circuit.gates ≤ 2 + (M.runTime n) * inc := by
  simpa [runtimeConfigCompiled] using
    iterated_stepCompiled_gates_le_of_stepCompiled_inc'
      (M := M) (n := n) (inc := inc) hStepInc

lemma runtimeConfigCompiledLinear_gates_le_budgetExpanded
    (M : TM) (n : Nat) :
    (runtimeConfigCompiledLinear M n).circuit.gates ≤
      2 + (M.runTime n) * BuiltWire.linearStepBudgetExpanded M n := by
  have hIter :
      (Nat.iterate (stepCompiledLinear M) (M.runTime n) (initialStraightConfig M n)).circuit.gates ≤
        (initialStraightConfig M n).circuit.gates +
          (M.runTime n) * BuiltWire.linearStepBudgetExpanded M n :=
    iterate_gates_le_of_next_gates_le
      (M := M) (n := n)
      (next := stepCompiledLinear M)
      (inc := BuiltWire.linearStepBudgetExpanded M n)
      (hNextGates := by
        intro sc
        simpa [stepCompiledLinear] using
          stepCompiledLinearCandidate_gates_le_budgetExpanded (M := M) (sc := sc))
      (t := M.runTime n) (sc := initialStraightConfig M n)
  have hInit : (initialStraightConfig M n).circuit.gates = 2 := by
    simp [initialStraightConfig, constBaseCircuit]
  simpa [runtimeConfigCompiledLinear, hInit] using hIter

/--
Acceptance extraction from an arbitrary straight configuration by redirecting
output to the accepting-state wire.
-/
noncomputable def acceptCircuitOf (M : TM) {n : Nat}
    (sc : StraightConfig M n) : StraightLineCircuit n :=
  withOutput sc.circuit (sc.state M.accept)

/--
Acceptance circuit extracted from the compiled-runtime straight configuration.
-/
noncomputable def acceptCircuitCompiled (M : TM) (n : Nat) : StraightLineCircuit n :=
  acceptCircuitOf M (runtimeConfigCompiled M n)

/-- Gate count is preserved for compiled-runtime acceptance extraction. -/
lemma acceptCircuitCompiled_gates (M : TM) (n : Nat) :
    (acceptCircuitCompiled M n).gates = (runtimeConfigCompiled M n).circuit.gates := by
  simp [acceptCircuitCompiled, acceptCircuitOf, runtimeConfigCompiled, withOutput]

/--
Straight-line acceptance extraction is correct under a runtime configuration
specification.
-/
lemma acceptCircuitOf_spec_of_runSpec (M : TM) (n : Nat)
    (sc : StraightConfig M n)
    (hRun : Spec (sc := sc) (f := fun x => M.run (n := n) x)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuitOf M sc) x =
        TM.accepts (M := M) (n := n) x := by
  intro x
  have hEval :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuitOf M sc) x =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.state M.accept) := by
    simpa [acceptCircuitOf] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := sc.circuit) (out := sc.state M.accept) (x := x))
  have hState :
      evalState sc x M.accept = stateIndicator M (M.run (n := n) x) M.accept :=
    hRun.state_eq x M.accept
  have hIndicator :
      stateIndicator M (M.run (n := n) x) M.accept =
        TM.accepts (M := M) (n := n) x := by
    simp [TM.accepts, stateIndicator]
  simpa [StraightConfig.evalState] using hEval.trans (hState.trans hIndicator)

/--
Compiled-runtime acceptance extraction is correct under compiled run-spec.
-/
lemma acceptCircuitCompiled_spec_of_runSpec (M : TM) (n : Nat)
    (hRun : Spec (sc := runtimeConfigCompiled M n) (f := fun x => M.run (n := n) x)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuitCompiled M n) x =
        TM.accepts (M := M) (n := n) x := by
  simpa [acceptCircuitCompiled] using
    (acceptCircuitOf_spec_of_runSpec (M := M) (n := n)
      (sc := runtimeConfigCompiled M n) hRun)

end StraightConfig

end Simulation
end PsubsetPpoly
end Internal
end Pnp3
