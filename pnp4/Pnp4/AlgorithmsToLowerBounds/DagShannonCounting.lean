import Complexity.Interfaces
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find

/-!
# Unconditional Shannon counting against `PpolyDAG`

This module proves the first fully unconditional lower-bound statement at the
exact `PpolyDAG` endpoint used by the final `P != NP` bridge:

* `exists_language_not_PpolyDAG : ∃ L, ¬ PpolyDAG L`

together with the quantitative engine behind it:

* `exists_hard_function_for_dag_gates`: if the explicit code count
  `dagCodeBound n g` is below `2 ^ (2 ^ n)`, then some `n`-input Boolean
  function is not computed by any `DagCircuit` with at most `g` gates;
* `dagHardBudget_superPolynomial`: the self-calibrating per-length hardness
  budget `dagHardBudget n` eventually dominates every polynomial schedule
  `n ^ c + c`.

## Method

Shannon's counting argument (1949), carried out against the strict in-repo
DAG model `Pnp3.ComplexityInterfaces.DagCircuit`:

1. every DAG circuit with at most `g` gates is *simulated* by a flat
   description (`DagCode`): `g` gate codes over a wire alphabet
   `Fin (n + g + 1)` plus an output wire, evaluated by a fuel-indexed
   sequential interpreter that reads forward references as `false`;
2. the description type is a `Fintype` of cardinality
   `(8 * (n+g+1)^2)^g * (n+g+1)`, so at most that many distinct Boolean
   functions are computed by DAG circuits with at most `g` gates;
3. for each input length `n`, a function escaping every circuit of
   `dagHardBudget n` gates exists once the count is below `2 ^ (2 ^ n)`;
   the diagonal language `dagHardLanguage` is assembled from classical
   choices of such functions;
4. `dagHardBudget n` is defined by `Nat.findGreatest`, so the per-length
   budget automatically tracks the strongest bound the counting supports;
   an explicit arithmetic estimate shows it eventually exceeds every
   `n ^ c + c`.

## Honest scope statement

This file does **not** reduce the `NP`-membership half of the research gap
`ComplexityInterfaces.NP_not_subset_PpolyDAG` (the single remaining input of
`P_ne_NP_final`).  The diagonal witness `dagHardLanguage` is obtained by
classical choice against the counting bound; it has no verifier and there is
no reason to expect `NP dagHardLanguage` to hold.  What the file contributes:

* the hardness half `¬ PpolyDAG L` is now witnessed unconditionally in-repo,
  at the exact final endpoint class (`DagCircuit`, not tree formulas);
* the remaining research gap is isolated *exactly* as: produce a language
  that is simultaneously `NP` and outside `PpolyDAG`.  The closing remark
  `NP_not_subset_PpolyDAG_of_NP_dagHardLanguage` records this interface
  fact; it is an honesty marker, not a proposed closure route.

The proof surface is axiom-clean and hole-free (standard kernel axioms only).
-/

namespace Pnp4
namespace AlgorithmsToLowerBounds

open Pnp3.ComplexityInterfaces

/-! ### Flat circuit descriptions -/

/--
Flat gate descriptor over `n` inputs and `g` gate slots.

The first component is a two-bit opcode (`(false,false) = const`,
`(false,true) = not`, `(true,false) = and`, `(true,true) = or`), the second
is the constant bit (used by `const` only), and the last two are wire
indices into `Fin (n + g + 1)`: values `< n` denote inputs, values `n + j`
denote gate slot `j`, and the spare top index is a harmless default.
-/
abbrev GateCode (n g : Nat) : Type :=
  (Bool × Bool) × Bool × Fin (n + g + 1) × Fin (n + g + 1)

/-- Flat circuit descriptor: `g` gate codes plus an output wire. -/
abbrev DagCode (n g : Nat) : Type :=
  (Fin g → GateCode n g) × Fin (n + g + 1)

/-- Two-bit opcode dispatch for the flat interpreter. -/
def opEval (op : Bool × Bool) (constBit v₁ v₂ : Bool) : Bool :=
  match op with
  | (false, false) => constBit
  | (false, true) => !v₁
  | (true, false) => v₁ && v₂
  | (true, true) => v₁ || v₂

/--
Read one wire during sequential evaluation of gate slot `i`: wires `< n`
read the input, wires `n + j` with `j < i` read an already-computed gate
value through `rec`, and everything else (forward references and the spare
top index) reads as `false`.
-/
def wireRead {n g : Nat} (x : Bitstring n) (rec : Nat → Bool) (i : Nat)
    (w : Fin (n + g + 1)) : Bool :=
  if hw : (w : Nat) < n then x ⟨(w : Nat), hw⟩
  else if (w : Nat) - n < i then rec ((w : Nat) - n)
  else false

/--
Fuel-indexed sequential interpreter for flat gate codes.  With fuel at
least `i + 1` it computes the value of gate slot `i` under the convention
that forward references read as `false`.
-/
def gateValueFuel {n g : Nat} (code : Fin g → GateCode n g) (x : Bitstring n) :
    Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if hig : i < g then
      opEval (code ⟨i, hig⟩).1 (code ⟨i, hig⟩).2.1
        (wireRead (g := g) x (gateValueFuel code x fuel) i (code ⟨i, hig⟩).2.2.1)
        (wireRead (g := g) x (gateValueFuel code x fuel) i (code ⟨i, hig⟩).2.2.2)
    else false

/-- Output semantics of a flat circuit description. -/
def codeEval {n g : Nat} (d : DagCode n g) (x : Bitstring n) : Bool :=
  wireRead (g := g) x (gateValueFuel d.1 x g) g d.2

/-! ### Reading helper wires -/

lemma wireRead_input {n g : Nat} (x : Bitstring n) (rec : Nat → Bool)
    (i : Nat) (j : Fin n) (h : (j : Nat) < n + g + 1) :
    wireRead (g := g) x rec i ⟨(j : Nat), h⟩ = x j := by
  have hval : ((⟨(j : Nat), h⟩ : Fin (n + g + 1)) : Nat) = (j : Nat) := rfl
  unfold wireRead
  rw [hval, dif_pos j.isLt]

lemma wireRead_gate {n g : Nat} (x : Bitstring n) (rec : Nat → Bool)
    (i j : Nat) (hj : j < i) (h : n + j < n + g + 1) :
    wireRead (g := g) x rec i ⟨n + j, h⟩ = rec j := by
  have hval : ((⟨n + j, h⟩ : Fin (n + g + 1)) : Nat) = n + j := rfl
  unfold wireRead
  rw [hval]
  rw [dif_neg (by omega)]
  rw [if_pos (by omega : n + j - n < i)]
  congr 1
  omega

/-! ### Encoding actual DAG circuits into flat descriptions -/

/-- Wire embedding: inputs keep their index, gate `j` becomes `n + j`. -/
def encodeWire {n k g : Nat} (hk : k ≤ g) : DagWire n k → Fin (n + g + 1)
  | .input j => ⟨(j : Nat), by have := j.isLt; omega⟩
  | .gate j => ⟨n + (j : Nat), by have := j.isLt; omega⟩

/-- Gate embedding into the flat gate-code alphabet. -/
def encodeGate {n k g : Nat} (hk : k ≤ g) : DagGate n k → GateCode n g
  | .const b => ((false, false), b, ⟨0, by omega⟩, ⟨0, by omega⟩)
  | .not w => ((false, true), false, encodeWire hk w, encodeWire hk w)
  | .and w₁ w₂ => ((true, false), false, encodeWire hk w₁, encodeWire hk w₂)
  | .or w₁ w₂ => ((true, true), false, encodeWire hk w₁, encodeWire hk w₂)

/--
Embed a DAG circuit with at most `g` gates into a flat description with
exactly `g` gate slots; unused slots become constant-`false` gates.
-/
def encodeCircuit {n : Nat} (C : DagCircuit n) {g : Nat} (hg : C.gates ≤ g) :
    DagCode n g :=
  ⟨fun i =>
      if hi : (i : Nat) < C.gates then
        encodeGate (Nat.le_of_lt i.isLt) (C.gate ⟨(i : Nat), hi⟩)
      else ((false, false), false, ⟨0, by omega⟩, ⟨0, by omega⟩),
    encodeWire hg C.output⟩

/--
Keystone simulation lemma: with enough fuel, the flat interpreter computes
exactly the in-repo DAG gate semantics on the encoded circuit.
-/
theorem gateValueFuel_encodeCircuit {n : Nat} (C : DagCircuit n) {g : Nat}
    (hg : C.gates ≤ g) (x : Bitstring n) :
    ∀ (fuel i : Nat) (hiC : i < C.gates), i < fuel →
      gateValueFuel (encodeCircuit C hg).1 x fuel i =
        DagCircuit.eval.evalGateAt (C := C) (x := x) i hiC := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hiC hfuel
    omega
  | succ fuel ih =>
    intro i hiC hfuel
    have hig : i < g := Nat.lt_of_lt_of_le hiC hg
    have hcode : (encodeCircuit C hg).1 ⟨i, hig⟩ =
        encodeGate (Nat.le_of_lt hig) (C.gate ⟨i, hiC⟩) := by
      simp only [encodeCircuit]
      rw [dif_pos hiC]
    simp only [gateValueFuel]
    rw [dif_pos hig, hcode]
    cases hOp : C.gate ⟨i, hiC⟩ with
    | const b =>
        rw [DagCircuit.eval.evalGateAt, hOp]
        simp only [encodeGate, opEval]
    | not w =>
        rw [DagCircuit.eval.evalGateAt, hOp]
        simp only [encodeGate, opEval]
        cases w with
        | input j =>
            simp only [encodeWire]
            rw [wireRead_input]
        | gate j =>
            simp only [encodeWire]
            rw [wireRead_gate (hj := j.isLt)]
            rw [ih (j : Nat) (Nat.lt_trans j.isLt hiC) (by have hj : (j : Nat) < i := j.isLt; omega)]
    | and w₁ w₂ =>
        rw [DagCircuit.eval.evalGateAt, hOp]
        simp only [encodeGate, opEval]
        cases w₁ with
        | input j₁ =>
            cases w₂ with
            | input j₂ =>
                simp only [encodeWire]
                rw [wireRead_input, wireRead_input]
            | gate j₂ =>
                simp only [encodeWire]
                rw [wireRead_input, wireRead_gate (hj := j₂.isLt)]
                rw [ih (j₂ : Nat) (Nat.lt_trans j₂.isLt hiC) (by have hj : (j₂ : Nat) < i := j₂.isLt; omega)]
        | gate j₁ =>
            cases w₂ with
            | input j₂ =>
                simp only [encodeWire]
                rw [wireRead_gate (hj := j₁.isLt), wireRead_input]
                rw [ih (j₁ : Nat) (Nat.lt_trans j₁.isLt hiC) (by have hj : (j₁ : Nat) < i := j₁.isLt; omega)]
            | gate j₂ =>
                simp only [encodeWire]
                rw [wireRead_gate (hj := j₁.isLt), wireRead_gate (hj := j₂.isLt)]
                rw [ih (j₁ : Nat) (Nat.lt_trans j₁.isLt hiC) (by have hj : (j₁ : Nat) < i := j₁.isLt; omega),
                  ih (j₂ : Nat) (Nat.lt_trans j₂.isLt hiC) (by have hj : (j₂ : Nat) < i := j₂.isLt; omega)]
    | or w₁ w₂ =>
        rw [DagCircuit.eval.evalGateAt, hOp]
        simp only [encodeGate, opEval]
        cases w₁ with
        | input j₁ =>
            cases w₂ with
            | input j₂ =>
                simp only [encodeWire]
                rw [wireRead_input, wireRead_input]
            | gate j₂ =>
                simp only [encodeWire]
                rw [wireRead_input, wireRead_gate (hj := j₂.isLt)]
                rw [ih (j₂ : Nat) (Nat.lt_trans j₂.isLt hiC) (by have hj : (j₂ : Nat) < i := j₂.isLt; omega)]
        | gate j₁ =>
            cases w₂ with
            | input j₂ =>
                simp only [encodeWire]
                rw [wireRead_gate (hj := j₁.isLt), wireRead_input]
                rw [ih (j₁ : Nat) (Nat.lt_trans j₁.isLt hiC) (by have hj : (j₁ : Nat) < i := j₁.isLt; omega)]
            | gate j₂ =>
                simp only [encodeWire]
                rw [wireRead_gate (hj := j₁.isLt), wireRead_gate (hj := j₂.isLt)]
                rw [ih (j₁ : Nat) (Nat.lt_trans j₁.isLt hiC) (by have hj : (j₁ : Nat) < i := j₁.isLt; omega),
                  ih (j₂ : Nat) (Nat.lt_trans j₂.isLt hiC) (by have hj : (j₂ : Nat) < i := j₂.isLt; omega)]

/-- Output-level simulation: the encoded description computes `C.eval`. -/
theorem codeEval_encodeCircuit {n : Nat} (C : DagCircuit n) {g : Nat}
    (hg : C.gates ≤ g) (x : Bitstring n) :
    codeEval (encodeCircuit C hg) x = DagCircuit.eval C x := by
  unfold codeEval
  cases hOut : C.output with
  | input j =>
      rw [DagCircuit.eval, hOut]
      have hout2 : (encodeCircuit C hg).2 = encodeWire hg (DagWire.input j) := by
        simp only [encodeCircuit, hOut]
      rw [hout2]
      simp only [encodeWire]
      rw [wireRead_input]
  | gate j =>
      rw [DagCircuit.eval, hOut]
      have hout2 : (encodeCircuit C hg).2 = encodeWire hg (DagWire.gate j) := by
        simp only [encodeCircuit, hOut]
      rw [hout2]
      simp only [encodeWire]
      rw [wireRead_gate (hj := Nat.lt_of_lt_of_le j.isLt hg)]
      exact gateValueFuel_encodeCircuit C hg x g (j : Nat) j.isLt
        (Nat.lt_of_lt_of_le j.isLt hg)

/-! ### Counting -/

/--
Explicit upper bound on the number of flat descriptions, hence on the
number of distinct Boolean functions computed by DAG circuits with at most
`g` gates over `n` inputs.
-/
def dagCodeBound (n g : Nat) : Nat :=
  (8 * ((n + g + 1) * (n + g + 1))) ^ g * (n + g + 1)

lemma card_gateCode (n g : Nat) :
    Fintype.card (GateCode n g) = 8 * ((n + g + 1) * (n + g + 1)) := by
  simp only [GateCode, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  generalize (n + g + 1) = m
  omega

lemma card_dagCode (n g : Nat) :
    Fintype.card (DagCode n g) = dagCodeBound n g := by
  have hbase : ∀ q : Nat, 2 * 2 * (2 * q) = 8 * q := by
    intro q
    omega
  simp only [DagCode, GateCode, dagCodeBound, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, hbase]

/-- The functions computed by flat descriptions with `g` gate slots. -/
noncomputable def dagComputableFuns (n g : Nat) :
    Finset (Bitstring n → Bool) := by
  classical
  exact Finset.univ.image (fun d : DagCode n g => fun x => codeEval d x)

lemma card_dagComputableFuns_le (n g : Nat) :
    (dagComputableFuns n g).card ≤ dagCodeBound n g := by
  classical
  calc (dagComputableFuns n g).card
      ≤ (Finset.univ : Finset (DagCode n g)).card := by
        simpa [dagComputableFuns] using
          Finset.card_image_le
            (s := (Finset.univ : Finset (DagCode n g)))
            (f := fun d : DagCode n g => fun x => codeEval d x)
    _ = Fintype.card (DagCode n g) := Finset.card_univ
    _ = dagCodeBound n g := card_dagCode n g

lemma mem_dagComputableFuns {n g : Nat} (C : DagCircuit n)
    (hg : C.gates ≤ g) :
    DagCircuit.eval C ∈ dagComputableFuns n g := by
  classical
  refine Finset.mem_image.mpr ⟨encodeCircuit C hg, Finset.mem_univ _, ?_⟩
  funext x
  exact codeEval_encodeCircuit C hg x

lemma card_bitstring_fun (n : Nat) :
    Fintype.card (Bitstring n → Bool) = 2 ^ (2 ^ n) := by
  show Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/--
Shannon escape: if the code count is below the number of all `n`-input
Boolean functions, some function is not computed by any DAG circuit with at
most `g` gates.
-/
theorem exists_hard_function_for_dag_gates (n g : Nat)
    (hcount : dagCodeBound n g < 2 ^ (2 ^ n)) :
    ∃ f : Bitstring n → Bool,
      ∀ C : DagCircuit n, C.gates ≤ g → DagCircuit.eval C ≠ f := by
  classical
  by_contra hAll
  have hmem : ∀ f : Bitstring n → Bool, f ∈ dagComputableFuns n g := by
    intro f
    have hf : ¬ ∀ C : DagCircuit n, C.gates ≤ g → DagCircuit.eval C ≠ f :=
      fun h => hAll ⟨f, h⟩
    rcases Classical.not_forall.mp hf with ⟨C, hC⟩
    have hgates : C.gates ≤ g := by
      by_contra hng
      exact hC (fun h => absurd h hng)
    have heval : DagCircuit.eval C = f := by
      by_contra hne
      exact hC (fun _ => hne)
    exact heval ▸ mem_dagComputableFuns C hgates
  have hsub : (Finset.univ : Finset (Bitstring n → Bool)) ⊆
      dagComputableFuns n g := fun f _ => hmem f
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, card_bitstring_fun] at hcard
  have := Nat.le_trans hcard (card_dagComputableFuns_le n g)
  omega

/-! ### The self-calibrating hardness budget -/

/--
Largest gate budget `g ≤ 2 ^ n` for which the counting bound certifies the
existence of a function that is hard for all `g`-gate DAG circuits.
-/
def dagHardBudget (n : Nat) : Nat :=
  Nat.findGreatest (fun g => dagCodeBound n g < 2 ^ (2 ^ n)) (2 ^ n)

lemma dagCodeBound_zero_lt (n : Nat) : dagCodeBound n 0 < 2 ^ (2 ^ n) := by
  have h1 : dagCodeBound n 0 = n + 1 := by
    simp [dagCodeBound]
  have h2 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h3 : 2 ^ n < 2 ^ (2 ^ n) :=
    Nat.pow_lt_pow_right (by decide) Nat.lt_two_pow_self
  omega

lemma dagHardBudget_spec (n : Nat) :
    dagCodeBound n (dagHardBudget n) < 2 ^ (2 ^ n) :=
  Nat.findGreatest_spec (P := fun g => dagCodeBound n g < 2 ^ (2 ^ n))
    (Nat.zero_le _) (dagCodeBound_zero_lt n)

lemma le_dagHardBudget {n s : Nat} (hcap : s ≤ 2 ^ n)
    (hs : dagCodeBound n s < 2 ^ (2 ^ n)) : s ≤ dagHardBudget n :=
  Nat.le_findGreatest hcap hs

/-! ### The diagonal hard language -/

/-- A per-length hard function, chosen classically against the budget. -/
noncomputable def dagHardFunction (n : Nat) : Bitstring n → Bool :=
  Classical.choose
    (exists_hard_function_for_dag_gates n (dagHardBudget n) (dagHardBudget_spec n))

lemma dagHardFunction_spec (n : Nat) :
    ∀ C : DagCircuit n, C.gates ≤ dagHardBudget n →
      DagCircuit.eval C ≠ dagHardFunction n :=
  Classical.choose_spec
    (exists_hard_function_for_dag_gates n (dagHardBudget n) (dagHardBudget_spec n))

/--
The diagonal language: at every input length it is a function that defeats
all DAG circuits within the per-length hardness budget.
-/
noncomputable def dagHardLanguage : Language := fun n => dagHardFunction n

/-! ### Growth arithmetic -/

/-- Quadratic-versus-exponential seed inequality. -/
lemma sq_succ_add_one_le_two_pow {j : Nat} (hj : 5 ≤ j) :
    j * (j + 1) + 1 ≤ 2 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj5 : 5 ≤ j
    · have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hIH := ih hj5
      have hexp : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by
        have h1 : (j + 1) * (j + 1 + 1) = (j + 1) * (j + 1) + (j + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        have h2 : (j + 1) * (j + 1) = j * (j + 1) + (j + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      have hlin : 3 * j ≤ j * (j + 1) := by
        have h3 : 3 ≤ j + 1 := by omega
        calc 3 * j = j * 3 := Nat.mul_comm 3 j
          _ ≤ j * (j + 1) := Nat.mul_le_mul_left j h3
      omega
    · have hj4 : j = 4 := by omega
      subst hj4
      decide

/--
For every coefficient `a`, exponent `k`, and threshold `lb`, some `n ≥ lb`
satisfies `a * n ^ k < 2 ^ n`.  Witness: a sufficiently large power of two.
-/
lemma exists_mul_pow_lt_two_pow (a k lb : Nat) :
    ∃ n : Nat, lb ≤ n ∧ 2 ≤ n ∧ a * n ^ k < 2 ^ n := by
  set j : Nat := max 5 (max k (max a lb)) with hj
  have hj5 : 5 ≤ j := le_max_left _ _
  have hjk : k ≤ j := le_trans (le_max_left k (max a lb)) (le_max_right _ _)
  have hja : a ≤ j :=
    le_trans (le_trans (le_max_left a lb) (le_max_right k (max a lb)))
      (le_max_right _ _)
  have hjlb : lb ≤ j :=
    le_trans (le_trans (le_max_right a lb) (le_max_right k (max a lb)))
      (le_max_right _ _)
  refine ⟨2 ^ j, ?_, ?_, ?_⟩
  · exact le_trans hjlb (Nat.le_of_lt Nat.lt_two_pow_self)
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
  · have hexp : a + j * k < 2 ^ j := by
      have h1 : j * k ≤ j * j := Nat.mul_le_mul_left j hjk
      have h2 := sq_succ_add_one_le_two_pow hj5
      have h3 : j * (j + 1) = j * j + j := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    calc a * (2 ^ j) ^ k = a * 2 ^ (j * k) := by rw [← Nat.pow_mul]
      _ ≤ 2 ^ a * 2 ^ (j * k) :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ (a + j * k) := (Nat.pow_add 2 a (j * k)).symm
      _ < 2 ^ (2 ^ j) := Nat.pow_lt_pow_right (by decide) hexp

/--
Crude but explicit estimate: the exponent produced by `dagCodeBound` at the
schedule `s = n ^ (c+1) + (c+1)` is at most `26 * n ^ (2 * (c+1))`.
-/
lemma dagCodeBound_le_two_pow (n g : Nat) :
    dagCodeBound n g ≤
      2 ^ (((n + g + 1) + (n + g + 1) + 3) * g + (n + g + 1)) := by
  set m : Nat := n + g + 1 with hm
  have hmle : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
  have hmm : m * m ≤ 2 ^ (m + m) := by
    calc m * m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul hmle hmle
      _ = 2 ^ (m + m) := (Nat.pow_add 2 m m).symm
  have h8 : 8 * (m * m) ≤ 2 ^ (m + m + 3) := by
    have h23 : (8 : Nat) = 2 ^ 3 := rfl
    calc 8 * (m * m) ≤ 8 * 2 ^ (m + m) := Nat.mul_le_mul_left 8 hmm
      _ = 2 ^ 3 * 2 ^ (m + m) := by rw [h23]
      _ = 2 ^ (3 + (m + m)) := (Nat.pow_add 2 3 (m + m)).symm
      _ = 2 ^ (m + m + 3) := by rw [Nat.add_comm 3 (m + m)]
  calc dagCodeBound n g = (8 * (m * m)) ^ g * m := rfl
    _ ≤ (2 ^ (m + m + 3)) ^ g * 2 ^ m :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h8 g) hmle
    _ = 2 ^ ((m + m + 3) * g) * 2 ^ m := by rw [← Nat.pow_mul]
    _ = 2 ^ ((m + m + 3) * g + m) := (Nat.pow_add 2 _ m).symm

/--
Arithmetic core of superpolynomial coverage: at the schedule
`s = n ^ (c+1) + (c+1)` the `dagCodeBound` exponent is at most
`26 * n ^ (2 * (c + 1))`, provided `2 ≤ n`.
-/
lemma exponent_le_poly {n c : Nat} (hn : 2 ≤ n) :
    ((n + (n ^ (c + 1) + (c + 1)) + 1) + (n + (n ^ (c + 1) + (c + 1)) + 1) + 3)
        * (n ^ (c + 1) + (c + 1))
      + (n + (n ^ (c + 1) + (c + 1)) + 1)
      ≤ 26 * n ^ (2 * (c + 1)) := by
  set P : Nat := n ^ (c + 1) with hP
  set Q : Nat := n ^ (2 * (c + 1)) with hQ
  have hPQ : Q = P * P := by
    rw [hQ, hP, ← Nat.pow_add]
    congr 1
    omega
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hnP : n ≤ P := by
    calc n = n ^ 1 := (Nat.pow_one n).symm
      _ ≤ n ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcP : c + 1 ≤ P := by
    calc c + 1 ≤ 2 ^ (c + 1) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ n ^ (c + 1) := Nat.pow_le_pow_left hn (c + 1)
  -- abbreviations for the schedule and wire count
  set s : Nat := P + (c + 1) with hs
  set m : Nat := n + s + 1 with hmdef
  have hsP : s ≤ 2 * P := by omega
  have hmP : m ≤ 4 * P := by omega
  have hA : m + m + 3 ≤ 11 * P := by omega
  -- (m + m + 3) * s ≤ 11 P * (2 P) = 22 (P * P)
  have hAs : (m + m + 3) * s ≤ 22 * (P * P) := by
    calc (m + m + 3) * s ≤ (11 * P) * (2 * P) := Nat.mul_le_mul hA hsP
      _ = 11 * (P * (2 * P)) := by rw [Nat.mul_assoc]
      _ = 11 * (2 * (P * P)) := by rw [← Nat.mul_assoc P 2 P, Nat.mul_comm P 2,
            Nat.mul_assoc]
      _ = 22 * (P * P) := by rw [← Nat.mul_assoc]
  have hPPQ : P ≤ P * P := by
    calc P = P * 1 := (Nat.mul_one P).symm
      _ ≤ P * P := Nat.mul_le_mul_left P hP1
  -- assemble; the goal is exactly (m+m+3)*s + m ≤ 26 Q
  have hgoal : (m + m + 3) * s + m ≤ 26 * (P * P) := by
    have hm4 : m ≤ 4 * (P * P) := by
      calc m ≤ 4 * P := hmP
        _ ≤ 4 * (P * P) := Nat.mul_le_mul_left 4 hPPQ
    omega
  calc (m + m + 3) * s + m ≤ 26 * (P * P) := hgoal
    _ = 26 * Q := by rw [hPQ]

/--
Superpolynomial coverage of the hardness budget: for every exponent `c`
some length `n ≥ 2` has `n ^ (c+1) + (c+1) ≤ dagHardBudget n`.
-/
lemma exists_good_length (c : Nat) :
    ∃ n : Nat, 2 ≤ n ∧ n ^ (c + 1) + (c + 1) ≤ dagHardBudget n := by
  obtain ⟨n, -, hn2, hgrow⟩ :=
    exists_mul_pow_lt_two_pow 26 (2 * (c + 1)) 2
  refine ⟨n, hn2, ?_⟩
  set s : Nat := n ^ (c + 1) + (c + 1) with hs
  have hexp : ((n + s + 1) + (n + s + 1) + 3) * s + (n + s + 1)
      ≤ 26 * n ^ (2 * (c + 1)) := exponent_le_poly hn2
  have hcount : dagCodeBound n s < 2 ^ (2 ^ n) := by
    have h1 := dagCodeBound_le_two_pow n s
    have h2 : ((n + s + 1) + (n + s + 1) + 3) * s + (n + s + 1) < 2 ^ n := by
      omega
    have h3 : 2 ^ (((n + s + 1) + (n + s + 1) + 3) * s + (n + s + 1))
        < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by decide) h2
    omega
  have hcap : s ≤ 2 ^ n := by
    have hsQ : s ≤ 26 * n ^ (2 * (c + 1)) := by
      have hP1 : 1 ≤ n ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      have hcP : c + 1 ≤ n ^ (c + 1) := by
        calc c + 1 ≤ 2 ^ (c + 1) := Nat.le_of_lt Nat.lt_two_pow_self
          _ ≤ n ^ (c + 1) := Nat.pow_le_pow_left hn2 (c + 1)
      have hPQ : n ^ (c + 1) ≤ n ^ (2 * (c + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega
  exact le_dagHardBudget hcap hcount

/-! ### Main theorems -/

/--
**Unconditional DAG lower bound for the diagonal language**: no polynomial
size DAG circuit family computes `dagHardLanguage`.
-/
theorem dagHardLanguage_not_PpolyDAG : ¬ PpolyDAG dagHardLanguage := by
  intro hP
  rcases hP with ⟨W, -⟩
  rcases W.polyBound_poly with ⟨c, hc⟩
  obtain ⟨n, hn2, hbudget⟩ := exists_good_length c
  have hsize := W.family_size_le n
  have hpb := hc n
  have hmono : n ^ c + c ≤ n ^ (c + 1) + (c + 1) := by
    have hpow : n ^ c ≤ n ^ (c + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_succ c)
    omega
  have hgates : (W.family n).gates ≤ dagHardBudget n := by
    have hsz : DagCircuit.size (W.family n) = (W.family n).gates + 1 := rfl
    omega
  have hne := dagHardFunction_spec n (W.family n) hgates
  apply hne
  funext x
  exact W.correct n x

/--
**Unconditional existence of a language outside `PpolyDAG`** — the hardness
half of the final research gap, at the exact endpoint class of the
`P != NP` bridge.
-/
theorem exists_language_not_PpolyDAG : ∃ L : Language, ¬ PpolyDAG L :=
  ⟨dagHardLanguage, dagHardLanguage_not_PpolyDAG⟩

/--
Quantitative form of the frontier: the per-length hardness budget
eventually dominates every polynomial schedule `n ^ c + c`.
-/
theorem dagHardBudget_superPolynomial (c : Nat) :
    ∃ n : Nat, 2 ≤ n ∧ n ^ c + c ≤ dagHardBudget n := by
  obtain ⟨n, hn2, hbudget⟩ := exists_good_length c
  refine ⟨n, hn2, ?_⟩
  have hmono : n ^ c + c ≤ n ^ (c + 1) + (c + 1) := by
    have hpow : n ^ c ≤ n ^ (c + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_succ c)
    omega
  omega

/--
Honesty marker for the remaining research gap (`Checklist` input 1): the
hardness half is unconditional, so `NP_not_subset_PpolyDAG` reduces to the
`NP`-membership of a hard language.  For the specific diagonal witness
`dagHardLanguage` there is no reason to expect the hypothesis to hold, and
this statement is *not* a proposed closure route; it documents the exact
interface of what is still missing.
-/
theorem NP_not_subset_PpolyDAG_of_NP_dagHardLanguage
    (h : NP dagHardLanguage) : NP_not_subset_PpolyDAG :=
  ⟨dagHardLanguage, h, dagHardLanguage_not_PpolyDAG⟩

end AlgorithmsToLowerBounds
end Pnp4
