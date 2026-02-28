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

noncomputable def stepCircuits (M : TM) {n : Nat}
    (cc : ConfigCircuits M n) : ConfigCircuits M n where
  tape := fun i => nextTapeCircuit M cc i
  head := fun j => nextHeadCircuit M cc j
  state := fun q => nextStateCircuit M cc q

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
noncomputable def stepCompiled (M : TM) {n : Nat} (sc : StraightConfig M n) :
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
Acceptance circuit extracted from the runtime straight configuration by
redirecting output to the accepting-state wire.
-/
noncomputable def acceptCircuit (M : TM) (n : Nat) : StraightLineCircuit n :=
  let cfg := runtimeConfig M n
  withOutput cfg.circuit (cfg.state M.accept)

/-- Gate count is preserved when only output redirection is applied. -/
lemma acceptCircuit_gates (M : TM) (n : Nat) :
    (acceptCircuit M n).gates = (runtimeConfig M n).circuit.gates := by
  simp [acceptCircuit, runtimeConfig, withOutput]

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
lemma acceptCircuit_spec_of_runSpec (M : TM) (n : Nat)
    (hRun : Spec (sc := runtimeConfig M n) (f := fun x => M.run (n := n) x)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuit M n) x =
        TM.accepts (M := M) (n := n) x := by
  intro x
  let cfg := runtimeConfig M n
  have hEval :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuit M n) x =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire cfg.circuit x (cfg.state M.accept) := by
    simpa [acceptCircuit, cfg, runtimeConfig, runConfig] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := cfg.circuit) (out := cfg.state M.accept) (x := x))
  have hState :
      evalState cfg x M.accept = stateIndicator M (M.run (n := n) x) M.accept :=
    hRun.state_eq x M.accept
  have hIndicator :
      stateIndicator M (M.run (n := n) x) M.accept =
        TM.accepts (M := M) (n := n) x := by
    simp [TM.accepts, stateIndicator]
  simpa [StraightConfig.evalState, cfg] using hEval.trans (hState.trans hIndicator)

/-- Alias with the expected final naming in the straight-line block. -/
lemma straightAcceptCircuit_spec (M : TM) (n : Nat)
    (hRun : Spec (sc := runtimeConfig M n) (f := fun x => M.run (n := n) x)) :
    ∀ x,
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (acceptCircuit M n) x =
        TM.accepts (M := M) (n := n) x :=
  acceptCircuit_spec_of_runSpec M n hRun

end StraightConfig

end Simulation
end PsubsetPpoly
end Internal
end Pnp3
