import Pnp4.AlgorithmsToLowerBounds.SymmetricWitnessPruning

/-!
# An `NP` language with an unconditional linear DAG lower bound

This module proves the first theorem in the repository whose *statement
shape* is exactly that of the final research gap (`input 1 =
NP_not_subset_PpolyDAG = ∃ L, NP L ∧ ¬ PpolyDAG L`), with the
superpolynomial requirement honestly weakened to a linear one:

* `exists_NP_language_with_linear_dag_lower_bound`:
  there is a language `L` with `NP L` such that **every** correct
  `DagCircuit` for slice `n` has at least `(n - 1) / 2` gates.

The witness is the even-parity language.  Both halves are new for the
repository:

1. **The first concrete `NP_TM` membership proof.**  No language had ever
   been placed in the strict verifier class `NP_TM` before (the pnp4
   TM-verifier programme is still in progress).  The key observation is
   that the `runTime : ℕ → ℕ` field of the strict machine model may
   depend on the input length, so a verifier can stop exactly at the
   instance/certificate boundary without any end-marker gymnastics: the
   two-state parity automaton `parityTM` sweeps the instance bits and
   ignores the certificate entirely.  This unlocks cheap `NP_TM`
   membership for every one-pass finite-state language and is reusable
   infrastructure for the verifier programme.

2. **A support-counting lower bound at the endpoint model.**  A
   `DagCircuit` with `g` gates reads at most `2g` input coordinates
   (`card_support_le`), while any circuit computing parity must read all
   `n` of them (`support_full_of_computes_evenParity`, via the in-repo
   `eval_eq_of_eq_on_support`).  Hence `n ≤ 2g + 1` for every correct
   circuit.

Honest scope: linear is astronomically far from superpolynomial — the
quantitative gap between this theorem and input 1 *is* the open problem.
The pair is sharp in kind: by `PpolyDAG_of_weightDetermined` the very same
language also has `O(n²)`-size circuits (`evenParityLanguage_in_PpolyDAG`),
so parity itself can never witness input 1; what this module contributes
is the statement shape, the first `NP_TM` witness, and the reusable
support-counting layer.
-/

namespace Pnp4
namespace AlgorithmsToLowerBounds

open Pnp3.ComplexityInterfaces
open Pnp3.Internal.PsubsetPpoly

/-! ### The even-parity language -/

/-- The even-parity language: accept iff the Hamming weight is even. -/
def evenParityLanguage : Language := fun _ x => decide (hammingWeight x % 2 = 0)

/-- Even parity is weight-determined. -/
theorem evenParityLanguage_weightDetermined :
    WeightDetermined evenParityLanguage := by
  intro n x y h
  simp [evenParityLanguage, h]

/-- Upper bound companion: even parity lies in `PpolyDAG` (so parity can
never witness the research gap; the lower bound below is linear, not
superpolynomial). -/
theorem evenParityLanguage_in_PpolyDAG : PpolyDAG evenParityLanguage :=
  PpolyDAG_of_weightDetermined evenParityLanguage_weightDetermined

/-! ### The verifier machine -/

/-- The two-state parity automaton: sweep right, XOR-ing the read bits
into the control state.  Its `runTime m = m - 1` stops the sweep exactly
at the instance/certificate boundary when run on `instance ++ certificate`
inputs of total length `m = n + 1`. -/
def parityTM : TM where
  state := Bool
  start := false
  accept := false
  step := fun q b => (xor q b, b, Move.right)
  runTime := fun m => m - 1

@[simp] lemma parityTM_runTime (m : Nat) : parityTM.runTime m = m - 1 := rfl

lemma parityTM_tapeLength (m : Nat) :
    parityTM.tapeLength m = m + (m - 1) + 1 := rfl

/-! ### Single-step analysis -/

lemma parity_step_state {m : Nat} (c : TM.Configuration (M := parityTM) m) :
    (TM.stepConfig (M := parityTM) c).state = xor c.state (c.tape c.head) := rfl

lemma parity_step_head {m : Nat} (c : TM.Configuration (M := parityTM) m) :
    (TM.stepConfig (M := parityTM) c).head
      = TM.Configuration.moveHead (c := c) Move.right := rfl

lemma decide_mod_two_xor (W : Nat) (b : Bool) :
    decide ((W + if b then 1 else 0) % 2 = 1)
      = xor (decide (W % 2 = 1)) b := by
  cases b
  · simp
  · rcases Nat.mod_two_eq_zero_or_one W with hpar | hpar
    · simp [Nat.add_mod, hpar]
    · simp [Nat.add_mod, hpar]

lemma moveHead_right_val {m : Nat} (c : TM.Configuration (M := parityTM) m)
    (h : (c.head : Nat) + 1 < parityTM.tapeLength m) :
    ((TM.Configuration.moveHead (c := c) Move.right : Fin _) : Nat)
      = (c.head : Nat) + 1 := by
  have hd : TM.Configuration.moveHead (c := c) Move.right
      = ⟨(c.head : Nat) + 1, h⟩ := by
    show (if h' : (c.head : Nat) + 1 < parityTM.tapeLength m
        then (⟨(c.head : Nat) + 1, h'⟩ : Fin (parityTM.tapeLength m))
        else c.head)
      = ⟨(c.head : Nat) + 1, h⟩
    rw [dif_pos h]
  rw [hd]

lemma parity_step_tape {m : Nat} (c : TM.Configuration (M := parityTM) m)
    (p : Fin (parityTM.tapeLength m)) :
    (TM.stepConfig (M := parityTM) c).tape p = c.tape p := by
  show TM.Configuration.write c c.head (c.tape c.head) p = c.tape p
  by_cases hp : p = c.head
  · subst hp
    rw [TM.Configuration.write_self]
  · rw [TM.Configuration.write_other c hp]

/-! ### The run invariant -/

/--
Invariant of the parity sweep after `t ≤ m` steps on input `y`:
the control state is the parity of the first `t` bits, the head sits at
cell `t`, and the tape is untouched.
-/
lemma parity_run_invariant (m : Nat) (y : Bitstring m) :
    ∀ t : Nat, t ≤ m →
      ((TM.runConfig (M := parityTM) (parityTM.initialConfig y) t).state
          = decide (prefixWeight y t % 2 = 1))
      ∧ (((TM.runConfig (M := parityTM) (parityTM.initialConfig y) t).head : Nat)
          = t)
      ∧ (∀ p, (TM.runConfig (M := parityTM) (parityTM.initialConfig y) t).tape p
          = (parityTM.initialConfig y).tape p) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · show (parityTM.initialConfig y).state = _
        rw [TM.initial_state]
        show false = decide (prefixWeight y 0 % 2 = 1)
        simp [prefixWeight]
      · show ((parityTM.initialConfig y).head : Nat) = 0
        rw [TM.initial_head]
      · intro p
        rfl
  | succ t ih =>
      intro ht
      have htm : t < m := by omega
      obtain ⟨hstate, hhead, htape⟩ := ih (by omega)
      set c : TM.Configuration (M := parityTM) m :=
        TM.runConfig (M := parityTM) (parityTM.initialConfig y) t with hc
      have hrun : TM.runConfig (M := parityTM) (parityTM.initialConfig y) (t + 1)
          = TM.stepConfig (M := parityTM) c := by
        rw [hc]
        show (TM.stepConfig (M := parityTM))^[t + 1] (parityTM.initialConfig y)
          = TM.stepConfig (M := parityTM)
              ((TM.stepConfig (M := parityTM))^[t] (parityTM.initialConfig y))
        exact Function.iterate_succ_apply' _ _ _
      have hheadFin : c.head
          = ⟨t, by show t < m + (m - 1) + 1; omega⟩ := by
        apply Fin.ext
        rw [hhead]
      have hsymbol : c.tape c.head = y ⟨t, htm⟩ := by
        rw [hheadFin, htape]
        exact TM.initial_tape_input (M := parityTM) y htm
      refine ⟨?_, ?_, ?_⟩
      · rw [hrun, parity_step_state, hstate, hsymbol,
          prefixWeight_succ y t htm, decide_mod_two_xor]
      · rw [hrun, parity_step_head]
        rw [moveHead_right_val c
          (by rw [hhead]; show t + 1 < m + (m - 1) + 1; omega)]
        rw [hhead]
      · intro p
        rw [hrun, parity_step_tape, htape]

/-! ### Acceptance characterization -/

lemma parityTM_accepts_eq (m : Nat) (y : Bitstring m) :
    TM.accepts (M := parityTM) m y
      = decide (prefixWeight y (m - 1) % 2 = 0) := by
  have hinv := (parity_run_invariant m y (m - 1) (by omega)).1
  show decide ((TM.run (M := parityTM) (n := m) y).state = parityTM.accept) = _
  unfold TM.run
  rw [parityTM_runTime, hinv]
  show decide ((decide (prefixWeight y (m - 1) % 2 = 1)) = false) = _
  rcases Nat.mod_two_eq_zero_or_one (prefixWeight y (m - 1)) with hpar | hpar
  · simp [hpar]
  · simp [hpar]

/-- Locally re-derived left projection of `concatBitstring`. -/
lemma concatBitstring_left_proj {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Fin (n + m)) (h : (i : Nat) < n) :
    concatBitstring x w i = x ⟨(i : Nat), h⟩ := by
  unfold concatBitstring
  rw [dif_pos h]

/-- The prefix weight of a concatenation, within the left block, is the
prefix weight of the left block. -/
lemma prefixWeight_concat {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    ∀ t : Nat, t ≤ n →
      prefixWeight (concatBitstring x w) t = prefixWeight x t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have htn : t < n := by omega
      have htm : t < n + m := by omega
      rw [prefixWeight_succ _ t htm, prefixWeight_succ x t htn, ih (by omega)]
      rw [concatBitstring_left_proj x w ⟨t, htm⟩ htn]

/-! ### The first concrete `NP_TM` membership -/

/-- **Even parity is in the strict verifier class `NP`** — the first
concrete `NP_TM` membership in the repository. -/
theorem evenParityLanguage_NP : NP evenParityLanguage := by
  refine ⟨parityTM, 1, 0, ?_, ?_⟩
  · intro n
    rw [parityTM_runTime]
    have h : (n + certificateLength n 0) ^ 1 = n + certificateLength n 0 :=
      Nat.pow_one _
    omega
  · intro n x
    have hcert : certificateLength n 0 = 1 := by
      simp [certificateLength]
    constructor
    · intro hLx
      refine ⟨fun _ => false, ?_⟩
      rw [parityTM_accepts_eq]
      have hsub : n + certificateLength n 0 - 1 = n := by omega
      rw [hsub, prefixWeight_concat x _ n (Nat.le_refl _),
        prefixWeight_n_eq_hammingWeight]
      exact hLx
    · rintro ⟨w, hw⟩
      rw [parityTM_accepts_eq] at hw
      have hsub : n + certificateLength n 0 - 1 = n := by omega
      rw [hsub, prefixWeight_concat x _ n (Nat.le_refl _),
        prefixWeight_n_eq_hammingWeight] at hw
      exact hw


/-! ### Support counting: a circuit with `g` gates reads at most `2g + 1` inputs -/

/-- Input coordinates read directly by one wire. -/
def wireInputSet {n k : Nat} : DagWire n k → Finset (Fin n)
  | .input j => {j}
  | .gate _ => ∅

/-- Input coordinates read directly by one gate. -/
def gateInputSet {n k : Nat} : DagGate n k → Finset (Fin n)
  | .const _ => ∅
  | .not w => wireInputSet w
  | .and w₁ w₂ => wireInputSet w₁ ∪ wireInputSet w₂
  | .or w₁ w₂ => wireInputSet w₁ ∪ wireInputSet w₂

/-- All input coordinates read by any gate of the circuit. -/
def allGateInputs {n : Nat} (C : DagCircuit n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun t : Fin C.gates => gateInputSet (C.gate t))

lemma card_wireInputSet_le {n k : Nat} (w : DagWire n k) :
    (wireInputSet w).card ≤ 1 := by
  cases w <;> simp [wireInputSet]

lemma card_gateInputSet_le {n k : Nat} (g : DagGate n k) :
    (gateInputSet g).card ≤ 2 := by
  cases g with
  | const b => simp [gateInputSet]
  | not w =>
      have := card_wireInputSet_le w
      simp only [gateInputSet]
      omega
  | and w₁ w₂ =>
      have h1 := card_wireInputSet_le w₁
      have h2 := card_wireInputSet_le w₂
      have hu := Finset.card_union_le (wireInputSet w₁) (wireInputSet w₂)
      simp only [gateInputSet]
      omega
  | or w₁ w₂ =>
      have h1 := card_wireInputSet_le w₁
      have h2 := card_wireInputSet_le w₂
      have hu := Finset.card_union_le (wireInputSet w₁) (wireInputSet w₂)
      simp only [gateInputSet]
      omega

lemma card_allGateInputs_le {n : Nat} (C : DagCircuit n) :
    (allGateInputs C).card ≤ 2 * C.gates := by
  calc (allGateInputs C).card
      ≤ ∑ t : Fin C.gates, (gateInputSet (C.gate t)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t : Fin C.gates, 2 :=
        Finset.sum_le_sum (fun t _ => card_gateInputSet_le (C.gate t))
    _ = 2 * C.gates := by
        simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]

lemma supportAt_subset_allGateInputs {n : Nat} (C : DagCircuit n) :
    ∀ (i : Nat) (hi : i < C.gates),
      DagCircuit.supportAt C i hi ⊆ allGateInputs C
  | i, hi => by
      intro a ha
      rw [DagCircuit.supportAt] at ha
      cases hg : C.gate ⟨i, hi⟩ with
      | const b =>
          rw [hg] at ha
          simp at ha
      | not w =>
          rw [hg] at ha
          cases w with
          | input j =>
              simp at ha
              refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
              rw [hg]
              simp [gateInputSet, wireInputSet, ha]
          | gate j =>
              exact supportAt_subset_allGateInputs C j.1 (Nat.lt_trans j.2 hi) ha
      | and w₁ w₂ =>
          rw [hg] at ha
          rcases Finset.mem_union.mp ha with ha1 | ha1
          · cases w₁ with
            | input j =>
                simp at ha1
                refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
                rw [hg]
                simp [gateInputSet, wireInputSet, ha1]
            | gate j =>
                exact supportAt_subset_allGateInputs C j.1 (Nat.lt_trans j.2 hi) ha1
          · cases w₂ with
            | input j =>
                simp at ha1
                refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
                rw [hg]
                simp [gateInputSet, wireInputSet, ha1]
            | gate j =>
                exact supportAt_subset_allGateInputs C j.1 (Nat.lt_trans j.2 hi) ha1
      | or w₁ w₂ =>
          rw [hg] at ha
          rcases Finset.mem_union.mp ha with ha1 | ha1
          · cases w₁ with
            | input j =>
                simp at ha1
                refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
                rw [hg]
                simp [gateInputSet, wireInputSet, ha1]
            | gate j =>
                exact supportAt_subset_allGateInputs C j.1 (Nat.lt_trans j.2 hi) ha1
          · cases w₂ with
            | input j =>
                simp at ha1
                refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
                rw [hg]
                simp [gateInputSet, wireInputSet, ha1]
            | gate j =>
                exact supportAt_subset_allGateInputs C j.1 (Nat.lt_trans j.2 hi) ha1
  termination_by i _ => i

/-- **Support-counting bound**: a `DagCircuit` with `g` gates reads at most
`2g + 1` input coordinates. -/
lemma card_support_le {n : Nat} (C : DagCircuit n) :
    (DagCircuit.support C).card ≤ 2 * C.gates + 1 := by
  cases hout : C.output with
  | input j =>
      have hs : DagCircuit.support C = {j} := by
        rw [DagCircuit.support, hout]
      rw [hs]
      simp
  | gate j =>
      have hsub : DagCircuit.support C ⊆ allGateInputs C := by
        intro a ha
        rw [DagCircuit.support, hout] at ha
        exact supportAt_subset_allGateInputs C j.1 j.2 ha
      have h1 := Finset.card_le_card hsub
      have h2 := card_allGateInputs_le C
      omega

/-! ### Parity reads every coordinate -/

lemma hammingWeight_allFalse (n : Nat) :
    hammingWeight (fun _ : Fin n => false) = 0 := by
  simp [hammingWeight]

lemma hammingWeight_update_true (n : Nat) (i : Fin n) :
    hammingWeight (Function.update (fun _ : Fin n => false) i true) = 1 := by
  unfold hammingWeight
  have hset :
      (Finset.univ.filter
        (fun t : Fin n => Function.update (fun _ : Fin n => false) i true t = true))
        = {i} := by
    ext t
    simp [Function.update_apply]
  rw [hset]
  simp

lemma support_full_of_computes_evenParity {n : Nat} (C : DagCircuit n)
    (hC : ∀ x, DagCircuit.eval C x = evenParityLanguage n x) :
    ∀ i : Fin n, i ∈ DagCircuit.support C := by
  intro i
  by_contra hmem
  have hagree : ∀ j ∈ DagCircuit.support C,
      (fun _ : Fin n => false) j
        = Function.update (fun _ : Fin n => false) i true j := by
    intro j hj
    have hne : j ≠ i := fun h => hmem (h ▸ hj)
    rw [Function.update_apply, if_neg hne]
  have heval := DagCircuit.eval_eq_of_eq_on_support C hagree
  rw [hC, hC] at heval
  unfold evenParityLanguage at heval
  rw [hammingWeight_allFalse, hammingWeight_update_true] at heval
  simp at heval

/-! ### The strike-shaped theorems -/

/-- **Linear DAG lower bound for even parity**: every correct circuit for
slice `n` satisfies `n ≤ 2 · gates + 1`. -/
theorem evenParity_linear_dag_lower_bound {n : Nat} (C : DagCircuit n)
    (hC : ∀ x, DagCircuit.eval C x = evenParityLanguage n x) :
    n ≤ 2 * C.gates + 1 := by
  have hfull : (Finset.univ : Finset (Fin n)) ⊆ DagCircuit.support C :=
    fun i _ => support_full_of_computes_evenParity C hC i
  have hn : n ≤ (DagCircuit.support C).card := by
    have h := Finset.card_le_card hfull
    simpa using h
  have hcard := card_support_le C
  omega

/-- Size form: every correct circuit has size at least `(n + 1) / 2`. -/
theorem evenParity_size_lower_bound {n : Nat} (C : DagCircuit n)
    (hC : ∀ x, DagCircuit.eval C x = evenParityLanguage n x) :
    (n + 1) / 2 ≤ DagCircuit.size C := by
  have h := evenParity_linear_dag_lower_bound C hC
  have hsz : DagCircuit.size C = C.gates + 1 := rfl
  omega

/--
**The statement shape of input 1, with a linear (not superpolynomial)
bound — unconditional**: there is an `NP` language all of whose correct
DAG circuits have at least `(n - 1) / 2` gates.

This is the first theorem in the repository combining a concrete `NP`
membership with an unconditional circuit lower bound at the endpoint
model.  The remaining distance to `NP_not_subset_PpolyDAG` is exactly
quantitative: replace linear by superpolynomial.
-/
theorem exists_NP_language_with_linear_dag_lower_bound :
    ∃ L : Language, NP L ∧
      ∀ (n : Nat) (C : DagCircuit n),
        (∀ x : Bitstring n, DagCircuit.eval C x = L n x) →
          n ≤ 2 * C.gates + 1 :=
  ⟨evenParityLanguage, evenParityLanguage_NP,
    fun _ C hC => evenParity_linear_dag_lower_bound C hC⟩

end AlgorithmsToLowerBounds
end Pnp4
