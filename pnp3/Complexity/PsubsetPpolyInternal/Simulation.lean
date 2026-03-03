import Complexity.PsubsetPpolyInternal.TuringEncoding
import Complexity.PsubsetPpolyInternal.CircuitTree
import Complexity.PsubsetPpolyInternal.StraightLine
import Complexity.PsubsetPpolyInternal.StraightLineSemantics
import Complexity.PsubsetPpolyInternal.StraightLineBuilder
import Complexity.PsubsetPpolyInternal.TreeToStraight
import Complexity.PpolyDAG_from_ArchiveStraightLine
import Mathlib.Tactic

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace Simulation

open Boolcube
open TM
open Pnp3.Complexity.ArchiveStraightLineAdapter

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

/-- Base gate-count monotonicity inherited from the builder context. -/
lemma base_le (bw : BuiltWire (n := n) base) :
    base.gates ≤ bw.ctx.circuit.gates :=
  bw.ctx.ctx.base_le

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

lemma buildNextTape_gates_le
    (sc : StraightConfig M n) (i : Fin (M.tapeLength n)) :
    (buildNextTape (M := M) (n := n) sc i).ctx.circuit.gates ≤
      sc.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 5 := by
  unfold buildNextTape
  let bwWrite := buildWriteBit (M := M) (n := n) sc
  let bc0 : BuiltCarry (n := n) sc.circuit := ⟨bwWrite, bwWrite.out⟩
  have hWrite :
      bwWrite.ctx.circuit.gates ≤ sc.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1 :=
    buildWriteBit_gates_le (M := M) (n := n) sc
  have hNext :
      (buildNextTapeFromCarry (M := M) (n := n) sc i bc0).bw.ctx.circuit.gates =
        bwWrite.ctx.circuit.gates + 4 := by
    simpa [bc0] using buildNextTapeFromCarry_gates_eq (M := M) (n := n) sc i bc0
  calc
    (buildNextTapeFromCarry (M := M) (n := n) sc i bc0).bw.ctx.circuit.gates = bwWrite.ctx.circuit.gates + 4 := hNext
    _ ≤ sc.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1 + 4 := by omega
    _ = sc.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 5 := by omega

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

lemma buildNextState_gates_le
    (sc : StraightConfig M n) (qTarget : M.state) :
    (buildNextState (M := M) (n := n) sc qTarget).ctx.circuit.gates ≤
      sc.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1 := by
  have hAux := buildNextStateAux_gates_le (M := M) (n := n) (sc := sc) (qTarget := qTarget)
      (qs := stateSymbolPairs M) (bc := ⟨initFalse (M := M) (n := n) sc, (initFalse (M := M) (n := n) sc).out⟩)
  have hInit :
      (⟨initFalse (M := M) (n := n) sc, (initFalse (M := M) (n := n) sc).out⟩ :
        BuiltCarry (n := n) sc.circuit).bw.ctx.circuit.gates = sc.circuit.gates + 1 := by
    simp
  have hLen : (stateSymbolPairs M).length = 2 * stateCard M := length_stateSymbolPairs M
  simpa [buildNextState, hInit, hLen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_add, Nat.add_mul] using hAux

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

lemma buildNextHead_gates_le
    (sc : StraightConfig M n) (j : Fin (M.tapeLength n)) :
    (buildNextHead (M := M) (n := n) sc j).ctx.circuit.gates ≤
      sc.circuit.gates + (2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) + 1 := by
  have hAux := buildNextHeadAux_gates_le (M := M) (n := n) (sc := sc) (j := j)
      (iqs := headStateSymbolPairs M n) (bc := ⟨initFalse (M := M) (n := n) sc, (initFalse (M := M) (n := n) sc).out⟩)
  have hInit :
      (⟨initFalse (M := M) (n := n) sc, (initFalse (M := M) (n := n) sc).out⟩ :
        BuiltCarry (n := n) sc.circuit).bw.ctx.circuit.gates = sc.circuit.gates + 1 := by
    simp
  have hLen : (headStateSymbolPairs M n).length = (M.tapeLength n) * (2 * stateCard M) :=
    length_headStateSymbolPairs (M := M) (n := n)
  simpa [buildNextHead, hInit, hLen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_add, Nat.add_mul] using hAux

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
  ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * (M.tapeLength n) +
  ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * (stateCard M)

lemma linearStepBudget_le_expanded (M : TM) (n : Nat) :
    linearStepBudget M n ≤ linearStepBudgetExpanded M n := by
  unfold linearStepBudget linearStepBudgetExpanded
  refine max_le ?_ ?_
  · omega
  · omega

theorem linearStepBlueprint_gates_le_budget (sc : StraightConfig M n) :
    ((linearStepBlueprint (M := M) (n := n) sc).writeBit.ctx.circuit.gates ≤
      sc.circuit.gates + linearStepBudget M n) ∧
    (∀ i, ((linearStepBlueprint (M := M) (n := n) sc).nextTape i).ctx.circuit.gates ≤
      sc.circuit.gates + linearStepBudget M n) ∧
    (∀ j, ((linearStepBlueprint (M := M) (n := n) sc).nextHead j).ctx.circuit.gates ≤
      sc.circuit.gates + linearStepBudget M n) ∧
    (∀ q, ((linearStepBlueprint (M := M) (n := n) sc).nextState q).ctx.circuit.gates ≤
      sc.circuit.gates + linearStepBudget M n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hWrite :
      (buildWriteBit (M := M) (n := n) sc).ctx.circuit.gates ≤
        sc.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 5) := by
      have hWrite' := buildWriteBit_gates_le (M := M) (n := n) sc
      exact le_trans hWrite' (by omega)
    exact le_trans hWrite (by
      simp [linearStepBlueprint, linearStepBudget, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.le_max_left])
  · intro i
    have hTape := buildNextTape_gates_le (M := M) (n := n) sc i
    exact le_trans hTape (by
      simp [linearStepBlueprint, linearStepBudget, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.le_max_left])
  · intro j
    have hHead := buildNextHead_gates_le (M := M) (n := n) sc j
    exact le_trans hHead (by
      simp [linearStepBlueprint, linearStepBudget, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.le_max_right])
  · intro q
    have hState' := buildNextState_gates_le (M := M) (n := n) sc q
    have hState :
      (buildNextState (M := M) (n := n) sc q).ctx.circuit.gates ≤
        sc.circuit.gates + ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 5) := by
      exact le_trans hState' (by omega)
    exact le_trans hState (by
      simp [linearStepBlueprint, linearStepBudget, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.le_max_left])

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
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j (headStateSymbolPairs M n) bc
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      let rest := buildNextHeadAllAux sc js bcNext
      (rest.1, (j, (bcHead.bw.out : Nat)) :: rest.2)

lemma buildNextHeadAllAux_gates_le
    (sc : StraightConfig M n) :
    ∀ (js : List (Fin (M.tapeLength n))) (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextHeadAllAux (M := M) (n := n) sc js bc).1.bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates +
          ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * js.length := by
  intro js
  induction js with
  | nil =>
      intro bc
      simp [buildNextHeadAllAux]
  | cons j js ih =>
      intro bc
      let bcHead := buildNextHeadAux (M := M) (n := n) sc j (headStateSymbolPairs M n) bc
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcHead.bw, bcHead.bw.out⟩
      have hHeadStep :
          bcHead.bw.ctx.circuit.gates ≤
            bc.bw.ctx.circuit.gates +
              (2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) := by
        have hRaw := buildNextHeadAux_gates_le (M := M) (n := n) (sc := sc) (j := j)
            (iqs := headStateSymbolPairs M n) (bc := bc)
        have hLen : (headStateSymbolPairs M n).length = (M.tapeLength n) * (2 * stateCard M) :=
          length_headStateSymbolPairs (M := M) (n := n)
        simpa [hLen] using hRaw
      have hRest :
          (buildNextHeadAllAux (M := M) (n := n) sc js bcNext).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * js.length :=
        ih bcNext
      have hMain :
          (buildNextHeadAllAux (M := M) (n := n) sc (j :: js) bc).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * js.length := by
        simpa [buildNextHeadAllAux, bcHead, bcNext] using hRest
      calc
        (buildNextHeadAllAux (M := M) (n := n) sc (j :: js) bc).1.bw.ctx.circuit.gates
            ≤ bcNext.bw.ctx.circuit.gates +
                ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * js.length := hMain
        _ = bcHead.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * js.length := by
              simp [bcNext]
        _ ≤ bc.bw.ctx.circuit.gates +
              (2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M)) +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * js.length := by
              omega
        _ = bc.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * (List.length (j :: js)) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/--
Append-only state-stage assembly over one growing builder context.
-/
noncomputable def buildNextStateAllAux (sc : StraightConfig M n) :
    List M.state →
      BuiltCarry (n := n) sc.circuit →
      BuiltCarry (n := n) sc.circuit × List (M.state × Nat)
  | [], bc => (bc, [])
  | q :: qs, bc =>
      let bcState := buildNextStateAux (M := M) (n := n) sc q (stateSymbolPairs M) bc
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      let rest := buildNextStateAllAux sc qs bcNext
      (rest.1, (q, (bcState.bw.out : Nat)) :: rest.2)

lemma buildNextStateAllAux_gates_le
    (sc : StraightConfig M n) :
    ∀ (qs : List M.state) (bc : BuiltCarry (n := n) sc.circuit),
      (buildNextStateAllAux (M := M) (n := n) sc qs bc).1.bw.ctx.circuit.gates ≤
        bc.bw.ctx.circuit.gates +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * qs.length := by
  intro qs
  induction qs with
  | nil =>
      intro bc
      simp [buildNextStateAllAux]
  | cons q qs ih =>
      intro bc
      let bcState := buildNextStateAux (M := M) (n := n) sc q (stateSymbolPairs M) bc
      let bcNext : BuiltCarry (n := n) sc.circuit := ⟨bcState.bw, bcState.bw.out⟩
      have hStateStep :
          bcState.bw.ctx.circuit.gates ≤
            bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) := by
        have hRaw := buildNextStateAux_gates_le (M := M) (n := n) (sc := sc) (qTarget := q)
            (qs := stateSymbolPairs M) (bc := bc)
        have hLen : (stateSymbolPairs M).length = 2 * stateCard M := length_stateSymbolPairs M
        simpa [hLen] using hRaw
      have hRest :
          (buildNextStateAllAux (M := M) (n := n) sc qs bcNext).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * qs.length :=
        ih bcNext
      have hMain :
          (buildNextStateAllAux (M := M) (n := n) sc (q :: qs) bc).1.bw.ctx.circuit.gates ≤
            bcNext.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * qs.length := by
        simpa [buildNextStateAllAux, bcState, bcNext] using hRest
      calc
        (buildNextStateAllAux (M := M) (n := n) sc (q :: qs) bc).1.bw.ctx.circuit.gates
            ≤ bcNext.bw.ctx.circuit.gates +
                ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * qs.length := hMain
        _ = bcState.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * qs.length := by
              simp [bcNext]
        _ ≤ bc.bw.ctx.circuit.gates + (2 * (M.tapeLength n) + 4) * (2 * stateCard M) +
              ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * qs.length := by
              omega
        _ = bc.bw.ctx.circuit.gates +
              ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * (List.length (q :: qs)) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

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
        ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * (M.tapeLength n) +
        ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * (stateCard M) := by
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
          ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * (M.tapeLength n) := by
    have hRaw := buildNextHeadAllAux_gates_le (M := M) (n := n) sc
      (js := tapeIndexList M n) (bc := bcTape)
    have hLen : (tapeIndexList M n).length = M.tapeLength n := by
      simp [tapeIndexList]
    simpa [headRes, bcHead, hLen] using hRaw
  have hState :
      stateRes.1.bw.ctx.circuit.gates ≤
        bcHead.bw.ctx.circuit.gates +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * (stateCard M) := by
    have hRaw := buildNextStateAllAux_gates_le (M := M) (n := n) sc
      (qs := stateList M) (bc := bcHead)
    have hLen : (stateList M).length = stateCard M := length_stateList M
    simpa [stateRes, hLen] using hRaw
  have hState' :
      stateRes.1.bw.ctx.circuit.gates ≤
        bcTape.bw.ctx.circuit.gates +
          ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * (M.tapeLength n) +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * (stateCard M) := by
    omega
  have hFinal :
      stateRes.1.bw.ctx.circuit.gates ≤
        sc.circuit.gates +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M) + 1) +
          4 * (M.tapeLength n) +
          ((2 * (M.tapeLength n) + 5) * ((M.tapeLength n) * (2 * stateCard M))) * (M.tapeLength n) +
          ((2 * (M.tapeLength n) + 4) * (2 * stateCard M)) * (stateCard M) := by
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

/--
`liftConfig` preserves all observable evaluations pointwise.
-/
lemma evalTape_liftConfig
    (sc : StraightConfig M n)
    (ctx : Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n sc.circuit)
    (x : Point n) (i : Fin (M.tapeLength n)) :
    evalTape (liftConfig (M := M) (n := n) sc ctx) x i = evalTape sc x i := by
  unfold evalTape liftConfig
  simpa using ctx.eval_liftBase x (sc.tape i)

lemma evalHead_liftConfig
    (sc : StraightConfig M n)
    (ctx : Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n sc.circuit)
    (x : Point n) (i : Fin (M.tapeLength n)) :
    evalHead (liftConfig (M := M) (n := n) sc ctx) x i = evalHead sc x i := by
  unfold evalHead liftConfig
  simpa using ctx.eval_liftBase x (sc.head i)

lemma evalState_liftConfig
    (sc : StraightConfig M n)
    (ctx : Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n sc.circuit)
    (x : Point n) (q : M.state) :
    evalState (liftConfig (M := M) (n := n) sc ctx) x q = evalState sc x q := by
  unfold evalState liftConfig
  simpa using ctx.eval_liftBase x (sc.state q)

/-- Straight-line correctness spec for an abstract configuration family. -/
structure Spec (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n) : Prop where
  tape_eq : ∀ x i, evalTape sc x i = (f x).tape i
  head_eq : ∀ x i, evalHead sc x i = headIndicator (f x) i
  state_eq : ∀ x q, evalState sc x q = stateIndicator M (f x) q

lemma spec_liftConfig
    (sc : StraightConfig M n)
    (ctx : Pnp3.Internal.PsubsetPpoly.StraightLine.EvalBuildCtx n sc.circuit)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f)) :
    Spec (sc := liftConfig (M := M) (n := n) sc ctx) (f := f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    exact (evalTape_liftConfig (M := M) (n := n) sc ctx x i).trans (hsc.tape_eq x i)
  · intro x i
    exact (evalHead_liftConfig (M := M) (n := n) sc ctx x i).trans (hsc.head_eq x i)
  · intro x q
    exact (evalState_liftConfig (M := M) (n := n) sc ctx x q).trans (hsc.state_eq x q)

/-- Tree-circuit interpretation of every wire of a straight-line circuit. -/
noncomputable def toTreeWire (C : StraightLineCircuit n) :
    Fin (n + C.gates) → Circuit n :=
  Pnp3.Internal.PsubsetPpoly.StraightLine.toCircuitWire C

/-- Convert a straight-line configuration into ordinary tree circuits. -/
noncomputable def toConfigCircuits (sc : StraightConfig M n) : ConfigCircuits M n where
  tape := fun i => toTreeWire sc.circuit (sc.tape i)
  head := fun i => toTreeWire sc.circuit (sc.head i)
  state := fun q => toTreeWire sc.circuit (sc.state q)

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

lemma constBase_archive_eval_false (n : Nat) (x : Point n) :
    Pnp3.Complexity.ArchiveStraightLineAdapter.eval (constBaseCircuit n) x = false := by
  unfold Pnp3.Complexity.ArchiveStraightLineAdapter.eval
    Pnp3.Complexity.ArchiveStraightLineAdapter.toDag
  simp [Pnp3.Complexity.ArchiveStraightLineAdapter.toDagWire,
    Pnp3.Complexity.ArchiveStraightLineAdapter.toDagOp,
    constBaseCircuit, ComplexityInterfaces.DagCircuit.eval,
    ComplexityInterfaces.DagCircuit.eval.evalGateAt]

lemma constBase_archive_eval_true (n : Nat) (x : Point n) :
    Pnp3.Complexity.ArchiveStraightLineAdapter.eval
      (Pnp3.Complexity.ArchiveStraightLineAdapter.withOutput (constBaseCircuit n)
        ⟨n + 1, by
          have : n + 1 < n + 2 := by omega
          simpa [constBaseCircuit] using this⟩) x = true := by
  unfold Pnp3.Complexity.ArchiveStraightLineAdapter.eval
    Pnp3.Complexity.ArchiveStraightLineAdapter.toDag
    Pnp3.Complexity.ArchiveStraightLineAdapter.withOutput
  simp [Pnp3.Complexity.ArchiveStraightLineAdapter.toDagWire,
    Pnp3.Complexity.ArchiveStraightLineAdapter.toDagOp,
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

Currently aliased to the truth-table-based assembly and intended to be replaced
by append-only constructive assembly.
-/
noncomputable abbrev stepCompiledLinear (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n :=
  stepCompiledTruthTable M sc

/--
Current one-step compiled simulator.

Kept as stable public name and currently aliased to the truth-table assembly.
This is the switch-point for the upcoming linear/DAG-preserving step builder.
-/
noncomputable abbrev stepCompiled (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n :=
  stepCompiledLinear M sc

noncomputable def step (M : TM) {n : Nat} (sc : StraightConfig M n) :
    StraightConfig M n :=
  sc

lemma step_spec_of_toConfig_step_eq
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f))
    (hStep :
      toConfigCircuits (step M sc) = ConfigCircuits.stepCircuits M (toConfigCircuits sc)) :
    Spec (sc := step M sc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  have hTree : ConfigCircuits.Spec (cc := toConfigCircuits sc) (f := f) :=
    toConfigCircuits_spec_of_spec (sc := sc) (f := f) hsc
  have hTreeStep :
      ConfigCircuits.Spec
        (cc := ConfigCircuits.stepCircuits M (toConfigCircuits sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) :=
    ConfigCircuits.step_spec (M := M) (cc := toConfigCircuits sc) (f := f) hTree
  have hTreeStep' :
      ConfigCircuits.Spec (cc := toConfigCircuits (step M sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) := by
    simpa [hStep] using hTreeStep
  exact spec_of_toConfigCircuits_spec (sc := step M sc)
    (f := fun x => TM.stepConfig (M := M) (f x)) hTreeStep'

lemma step_spec_of_toConfig_step_semantics
    (M : TM) {n : Nat}
    (sc : StraightConfig M n)
    (f : Point n → TM.Configuration (M := M) n)
    (hsc : Spec (sc := sc) (f := f))
    (hTape :
      ∀ x i,
        Boolcube.Circuit.eval ((toConfigCircuits (step M sc)).tape i) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).tape i) x)
    (hHead :
      ∀ x i,
        Boolcube.Circuit.eval ((toConfigCircuits (step M sc)).head i) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).head i) x)
    (hState :
      ∀ x q,
        Boolcube.Circuit.eval ((toConfigCircuits (step M sc)).state q) x =
          Boolcube.Circuit.eval ((ConfigCircuits.stepCircuits M (toConfigCircuits sc)).state q) x) :
    Spec (sc := step M sc) (f := fun x => TM.stepConfig (M := M) (f x)) := by
  have hTree : ConfigCircuits.Spec (cc := toConfigCircuits sc) (f := f) :=
    toConfigCircuits_spec_of_spec (sc := sc) (f := f) hsc
  have hTreeStep :
      ConfigCircuits.Spec
        (cc := ConfigCircuits.stepCircuits M (toConfigCircuits sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) :=
    ConfigCircuits.step_spec (M := M) (cc := toConfigCircuits sc) (f := f) hTree
  have hTreeStep' :
      ConfigCircuits.Spec (cc := toConfigCircuits (step M sc))
        (f := fun x => TM.stepConfig (M := M) (f x)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x i
      exact (hTape x i).trans (hTreeStep.tape_eq x i)
    · intro x i
      exact (hHead x i).trans (hTreeStep.head_eq x i)
    · intro x q
      exact (hState x q).trans (hTreeStep.state_eq x q)
  exact spec_of_toConfigCircuits_spec (sc := step M sc)
    (f := fun x => TM.stepConfig (M := M) (f x)) hTreeStep'

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


lemma iterate_spec_of_step_spec
    (M : TM) {n : Nat}
    (hStep :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n),
        Spec (sc := sc) (f := f) →
        Spec (sc := step M sc) (f := fun x => TM.stepConfig (M := M) (f x))) :
    ∀ (sc : StraightConfig M n)
      (f : Point n → TM.Configuration (M := M) n),
      Spec (sc := sc) (f := f) →
      ∀ t,
        Spec (sc := Nat.iterate (step M) t sc)
          (f := fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x)) := by
  intro sc f hsc t
  induction t with
  | zero =>
      simpa using hsc
  | succ t ih =>
      have hPrev :
          Spec (sc := Nat.iterate (step M) t sc)
            (f := fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x)) := ih
      have hNext := hStep
        (Nat.iterate (step M) t sc)
        (fun x => Nat.iterate (TM.stepConfig (M := M)) t (f x))
        hPrev
      simpa [Function.iterate_succ_apply', Function.comp] using hNext

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

lemma runtime_spec_of_stepCompiledSpec
    (M : TM) (n : Nat)
    (hStep :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n),
        Spec (sc := sc) (f := f) →
          Spec (sc := stepCompiled M sc) (f := fun x => TM.stepConfig (M := M) (f x))) :
    Spec (sc := Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n))
      (f := fun x => M.run (n := n) x) := by
  exact runtime_spec_of_next (M := M) (n := n) (next := stepCompiled M) (hNext := hStep)

lemma runtime_spec_of_stepCompiledProvider
    (M : TM) (n : Nat)
    (hSem : StepCompiledSemantics M n) :
    Spec (sc := Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n))
      (f := fun x => M.run (n := n) x) := by
  refine runtime_spec_of_next (M := M) (n := n) (next := stepCompiled M) ?_
  intro sc f hsc
  exact stepCompiled_spec_of_provider (M := M) (n := n) hSem sc f hsc

/-- Iterate `step` exactly `t` times starting from `sc`. -/
noncomputable def runConfig (M : TM) {n : Nat}
    (sc : StraightConfig M n) (t : Nat) : StraightConfig M n :=
  Nat.iterate (step M) t sc

/-- With the current straight layer (`step = id`), iteration is stable. -/
@[simp] lemma runConfig_eq (M : TM) {n : Nat}
    (sc : StraightConfig M n) (t : Nat) :
    runConfig M sc t = sc := by
  induction t with
  | zero =>
      simp [runConfig]
  | succ t ih =>
      simpa [runConfig, step, Nat.iterate, ih]

lemma runtime_spec_of_step_spec
    (M : TM) (n : Nat)
    (hStep :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n),
        Spec (sc := sc) (f := f) →
        Spec (sc := step M sc) (f := fun x => TM.stepConfig (M := M) (f x))) :
    Spec (sc := runConfig M (initialStraightConfig M n) (M.runTime n))
      (f := fun x => M.run (n := n) x) := by
  have hInit : Spec (sc := initialStraightConfig M n) (f := fun x => M.initialConfig x) :=
    initialStraightConfig_spec M n
  have hIter := iterate_spec_of_step_spec (M := M) (n := n) hStep
    (sc := initialStraightConfig M n)
    (f := fun x => M.initialConfig x)
    hInit
    (M.runTime n)
  simpa [runConfig, TM.run, TM.runConfig] using hIter

/-- Straight-line configuration after simulating for `runTime n` steps. -/
noncomputable def runtimeConfig (M : TM) (n : Nat) : StraightConfig M n :=
  runConfig M (initialStraightConfig M n) (M.runTime n)

/--
Compiled-runtime straight configuration: iterate `stepCompiled` for exactly
`runTime n` steps from the initial straight configuration.
-/
noncomputable def runtimeConfigCompiled (M : TM) (n : Nat) : StraightConfig M n :=
  Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n)

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

lemma runtimeConfig_spec_of_step_spec
    (M : TM) (n : Nat)
    (hStep :
      ∀ (sc : StraightConfig M n)
        (f : Point n → TM.Configuration (M := M) n),
        Spec (sc := sc) (f := f) →
        Spec (sc := step M sc) (f := fun x => TM.stepConfig (M := M) (f x))) :
    Spec (sc := runtimeConfig M n) (f := fun x => M.run (n := n) x) := by
  simpa [runtimeConfig] using runtime_spec_of_step_spec (M := M) (n := n) hStep

/-- Runtime straight configuration is currently the initial straight config. -/
@[simp] lemma runtimeConfig_eq_initial (M : TM) (n : Nat) :
    runtimeConfig M n = initialStraightConfig M n := by
  simp [runtimeConfig, runConfig_eq]

/--
Acceptance extraction from an arbitrary straight configuration by redirecting
output to the accepting-state wire.
-/
noncomputable def acceptCircuitOf (M : TM) {n : Nat}
    (sc : StraightConfig M n) : StraightLineCircuit n :=
  withOutput sc.circuit (sc.state M.accept)

/--
Acceptance circuit extracted from the runtime straight configuration by
redirecting output to the accepting-state wire.
-/
noncomputable def acceptCircuit (M : TM) (n : Nat) : StraightLineCircuit n :=
  let cfg := runtimeConfig M n
  withOutput cfg.circuit (cfg.state M.accept)

/--
Acceptance circuit extracted from the compiled-runtime straight configuration.
-/
noncomputable def acceptCircuitCompiled (M : TM) (n : Nat) : StraightLineCircuit n :=
  acceptCircuitOf M (runtimeConfigCompiled M n)

/-- Gate count is preserved when only output redirection is applied. -/
lemma acceptCircuit_gates (M : TM) (n : Nat) :
    (acceptCircuit M n).gates = (runtimeConfig M n).circuit.gates := by
  simp [acceptCircuit, runtimeConfig, withOutput]

/-- Gate count is preserved for compiled-runtime acceptance extraction. -/
lemma acceptCircuitCompiled_gates (M : TM) (n : Nat) :
    (acceptCircuitCompiled M n).gates = (runtimeConfigCompiled M n).circuit.gates := by
  simp [acceptCircuitCompiled, acceptCircuitOf, runtimeConfigCompiled, withOutput]

/-- In the current straight layer, acceptance extraction keeps the base gate count. -/
@[simp] lemma straightAcceptCircuit_gates (M : TM) (n : Nat) :
    (acceptCircuit M n).gates = 2 := by
  simp [acceptCircuit_gates, runtimeConfig_eq_initial, initialStraightConfig, constBaseCircuit]

/--
Polynomial gate bound used by the straight-line compiler packaging.
The shape is intentionally normalized to `n^k + k`.
-/
def gatePolyBound (_M : TM) (c n : Nat) : Nat :=
  n ^ (c + 4) + (c + 4)

/--
Gate count of the straight acceptance circuit is polynomially bounded.
`hRun` is carried for interface compatibility with the final compiler API.
-/
lemma straightAcceptCircuit_le_gatePolyBound
    (M : TM) (c : Nat)
    (_hRun : ∀ m, M.runTime m ≤ m ^ c + c) (n : Nat) :
    (acceptCircuit M n).gates ≤ gatePolyBound M c n := by
  have h2 : 2 ≤ c + 4 := by omega
  have hLift : c + 4 ≤ n ^ (c + 4) + (c + 4) := by
    exact Nat.le_add_left (c + 4) (n ^ (c + 4))
  calc
    (acceptCircuit M n).gates = 2 := straightAcceptCircuit_gates M n
    _ ≤ c + 4 := h2
    _ ≤ n ^ (c + 4) + (c + 4) := hLift
    _ = gatePolyBound M c n := rfl

/-- The packaged straight gate bound is itself of the form `n^k + k`. -/
lemma gatePolyBound_poly (M : TM) (c : Nat) :
    ∃ k, ∀ n, gatePolyBound M c n ≤ n ^ k + k := by
  refine ⟨c + 4, ?_⟩
  intro n
  simp [gatePolyBound]

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
Straight-line acceptance extraction is correct under a runtime configuration
specification.
-/
lemma acceptCircuit_spec_of_runSpec (M : TM) (n : Nat)
    (hRun : Spec (sc := runtimeConfig M n) (f := fun x => M.run (n := n) x)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuit M n) x =
        TM.accepts (M := M) (n := n) x := by
  simpa [acceptCircuit, acceptCircuitOf, -runtimeConfig_eq_initial] using
    (acceptCircuitOf_spec_of_runSpec (M := M) (n := n)
      (sc := runtimeConfig M n) hRun)

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

/-- Alias with the expected final naming in the straight-line block. -/
lemma straightAcceptCircuit_spec (M : TM) (n : Nat)
    (hRun : Spec (sc := runtimeConfig M n) (f := fun x => M.run (n := n) x)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuit M n) x =
        TM.accepts (M := M) (n := n) x :=
  acceptCircuit_spec_of_runSpec M n hRun

/--
Specialized evaluator agreement on the acceptance-circuit shape used by the
current internal compiler route.
-/
lemma acceptCircuit_archive_eval_eq_internal (M : TM) (n : Nat) (x : Point n) :
    Pnp3.Complexity.ArchiveStraightLineAdapter.eval (acceptCircuit M n) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuit M n) x := by
  unfold acceptCircuit
  rw [runtimeConfig_eq_initial]
  by_cases hs : M.accept = M.start
  · let idxT : Fin (n + (constBaseCircuit n).gates) := ⟨n + 1, by
        have : n + 1 < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩
    have hArch :
        Pnp3.Complexity.ArchiveStraightLineAdapter.eval
          (withOutput (constBaseCircuit n) idxT) x = true := by
      simpa [idxT] using constBase_archive_eval_true n x
    have hInt :
        Pnp3.Internal.PsubsetPpoly.StraightLine.eval
          (withOutput (constBaseCircuit n) idxT) x = true := by
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.eval
            (withOutput (constBaseCircuit n) idxT) x
            = Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (constBaseCircuit n) x idxT := by
                  simpa [idxT] using
                    (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
                      (C := constBaseCircuit n) (out := idxT) (x := x))
        _ = true := by
              simpa [idxT] using constBase_evalWire_true n x
    simpa [initialStraightConfig, hs, idxT] using hArch.trans hInt.symm
  · let idxF : Fin (n + (constBaseCircuit n).gates) := ⟨n, by
        have : n < n + 2 := by omega
        simpa [constBaseCircuit] using this⟩
    have hArch :
        Pnp3.Complexity.ArchiveStraightLineAdapter.eval
          (withOutput (constBaseCircuit n) idxF) x = false := by
      simpa [idxF] using constBase_archive_eval_false n x
    have hInt :
        Pnp3.Internal.PsubsetPpoly.StraightLine.eval
          (withOutput (constBaseCircuit n) idxF) x = false := by
      calc
        Pnp3.Internal.PsubsetPpoly.StraightLine.eval
            (withOutput (constBaseCircuit n) idxF) x
            = Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
                (constBaseCircuit n) x idxF := by
                  simpa [idxF] using
                    (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
                      (C := constBaseCircuit n) (out := idxF) (x := x))
        _ = false := by
              simpa [idxF] using constBase_evalWire_false n x
    simpa [initialStraightConfig, hs, idxF] using hArch.trans hInt.symm

end StraightConfig

end Simulation
end PsubsetPpoly
end Internal
end Pnp3
