import Complexity.DagCompose
import Pnp4.AlgorithmsToLowerBounds.DagShannonCounting
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG

/-!
# Sparse witness pruning: polynomially sparse languages lie in `PpolyDAG`

Self-contained attack note (this session works without external sources):
the remaining research gap asks for a language that is simultaneously `NP`
and outside `PpolyDAG`.  A natural family of candidate witnesses are
"thin" languages — unary/tally encodings, languages with few accepted
strings per length, or complements of such.  This module formally
*refutes* every candidate in that family, by proving the corresponding
upper bound at the exact endpoint class:

* `PpolyDAG_of_polySparse`: a language with at most `n ^ c + c` accepted
  strings at every length lies in `PpolyDAG` (DNF of accepted strings);
* `PpolyDAG_of_polyCosparse`: dually for at most `n ^ c + c` rejected
  strings (negated DNF of rejected strings);
* `VerifiedNPDAGLowerBoundSource.not_polySparse` /
  `.not_polyCosparse`: therefore any valid source witness for
  `NP_not_subset_PpolyDAG` must be dense and co-dense — formally pruning
  the sparse corner of the witness search space;
* `dagHardLanguage_not_polySparse` / `dagHardLanguage_not_polyCosparse`:
  the unconditional diagonal witness of `DagShannonCounting` is provably
  dense on both sides, a structural sanity check on the counting layer.

The constructive half builds on the `DagCompose` composition layer
(`substInputs`, `inputProj`, `constCircuit`) and adds the reusable
combinators `notC`, `andC`, `orC`, `andList`, `orList`, `literalCircuit`,
`eqCircuit`, `dnfCircuit` with full `eval`/`size` lemmas — generic DAG
plumbing that future constructions can reuse.

Honest scope: these are upper bounds and route-pruning facts.  They do
not construct the missing dense witness; they narrow where it can live.
-/

namespace Pnp4
namespace AlgorithmsToLowerBounds

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-! ### Binary and unary circuit combinators -/

/-- Two-input AND template: a single gate reading both inputs. -/
def and2 : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.and (DagWire.input 0) (DagWire.input 1)
  output := DagWire.gate ⟨0, by omega⟩

/-- Two-input OR template. -/
def or2 : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.or (DagWire.input 0) (DagWire.input 1)
  output := DagWire.gate ⟨0, by omega⟩

/-- One-input NOT template. -/
def not1 : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input 0)
  output := DagWire.gate ⟨0, by omega⟩

@[simp] theorem eval_and2 (y : Bitstring 2) : eval and2 y = (y 0 && y 1) := by
  unfold eval
  unfold DagCircuit.eval.evalGateAt
  rfl

@[simp] theorem eval_or2 (y : Bitstring 2) : eval or2 y = (y 0 || y 1) := by
  unfold eval
  unfold DagCircuit.eval.evalGateAt
  rfl

@[simp] theorem eval_not1 (y : Bitstring 1) : eval not1 y = !(y 0) := by
  unfold eval
  unfold DagCircuit.eval.evalGateAt
  rfl

@[simp] theorem size_and2 : size and2 = 2 := rfl
@[simp] theorem size_or2 : size or2 = 2 := rfl
@[simp] theorem size_not1 : size not1 = 2 := rfl

/-- Negation combinator. -/
def notC {n : Nat} (C : DagCircuit n) : DagCircuit n :=
  substInputs not1 (fun _ => C)

/-- Conjunction combinator. -/
def andC {n : Nat} (C₁ C₂ : DagCircuit n) : DagCircuit n :=
  substInputs and2 ![C₁, C₂]

/-- Disjunction combinator. -/
def orC {n : Nat} (C₁ C₂ : DagCircuit n) : DagCircuit n :=
  substInputs or2 ![C₁, C₂]

@[simp] theorem eval_notC {n : Nat} (C : DagCircuit n) (x : Bitstring n) :
    eval (notC C) x = !(eval C x) := by
  simp [notC]

@[simp] theorem eval_andC {n : Nat} (C₁ C₂ : DagCircuit n) (x : Bitstring n) :
    eval (andC C₁ C₂) x = (eval C₁ x && eval C₂ x) := by
  simp [andC]

@[simp] theorem eval_orC {n : Nat} (C₁ C₂ : DagCircuit n) (x : Bitstring n) :
    eval (orC C₁ C₂) x = (eval C₁ x || eval C₂ x) := by
  simp [orC]

theorem size_notC_le {n : Nat} (C : DagCircuit n) :
    size (notC C) ≤ 2 + size C := by
  have h := size_substInputs_le not1 (fun _ : Fin 1 => C)
  simpa [notC] using h

theorem size_andC_le {n : Nat} (C₁ C₂ : DagCircuit n) :
    size (andC C₁ C₂) ≤ 2 + size C₁ + size C₂ := by
  have h := size_substInputs_le and2 ![C₁, C₂]
  simp only [size_and2, Fin.sum_univ_two] at h
  simpa [andC, Nat.add_assoc] using h

theorem size_orC_le {n : Nat} (C₁ C₂ : DagCircuit n) :
    size (orC C₁ C₂) ≤ 2 + size C₁ + size C₂ := by
  have h := size_substInputs_le or2 ![C₁, C₂]
  simp only [size_or2, Fin.sum_univ_two] at h
  simpa [orC, Nat.add_assoc] using h

/-! ### List folds -/

/-- Conjunction of a list of circuits (empty list = constant `true`). -/
def andList {n : Nat} : List (DagCircuit n) → DagCircuit n
  | [] => constCircuit n true
  | C :: rest => andC C (andList rest)

/-- Disjunction of a list of circuits (empty list = constant `false`). -/
def orList {n : Nat} : List (DagCircuit n) → DagCircuit n
  | [] => constCircuit n false
  | C :: rest => orC C (orList rest)

@[simp] theorem eval_andList {n : Nat} (l : List (DagCircuit n)) (x : Bitstring n) :
    eval (andList l) x = l.all (fun C => eval C x) := by
  induction l with
  | nil => simp [andList]
  | cons C rest ih => simp [andList, ih]

@[simp] theorem eval_orList {n : Nat} (l : List (DagCircuit n)) (x : Bitstring n) :
    eval (orList l) x = l.any (fun C => eval C x) := by
  induction l with
  | nil => simp [orList]
  | cons C rest ih => simp [orList, ih]

theorem size_andList_le {n : Nat} (l : List (DagCircuit n)) :
    size (andList l) ≤ 2 + (l.map (fun C => size C + 2)).sum := by
  induction l with
  | nil => simp [andList]
  | cons C rest ih =>
      have h := size_andC_le C (andList rest)
      simp only [andList, List.map_cons, List.sum_cons]
      omega

theorem size_orList_le {n : Nat} (l : List (DagCircuit n)) :
    size (orList l) ≤ 2 + (l.map (fun C => size C + 2)).sum := by
  induction l with
  | nil => simp [orList]
  | cons C rest ih =>
      have h := size_orC_le C (orList rest)
      simp only [orList, List.map_cons, List.sum_cons]
      omega

/-- Sum of a mapped list under a uniform per-element bound. -/
lemma sum_map_le_of_forall_le {α : Type*} (l : List α) (f : α → Nat)
    (b : Nat) (h : ∀ a ∈ l, f a ≤ b) : (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ha := h a List.mem_cons_self
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hexp : (t.length + 1) * b = t.length * b + b := by ring
      omega

/-! ### Literals, point indicators, DNFs -/

/-- Literal circuit: tests `x i = b`. -/
def literalCircuit {n : Nat} (i : Fin n) (b : Bool) : DagCircuit n :=
  if b then inputProj i else notC (inputProj i)

@[simp] theorem eval_literalCircuit {n : Nat} (i : Fin n) (b : Bool)
    (x : Bitstring n) :
    eval (literalCircuit i b) x = (x i == b) := by
  cases b with
  | false =>
      simp [literalCircuit]
  | true =>
      simp [literalCircuit]

theorem size_literalCircuit_le {n : Nat} (i : Fin n) (b : Bool) :
    size (literalCircuit i b) ≤ 3 := by
  cases b with
  | false =>
      have h := size_notC_le (inputProj i)
      simpa [literalCircuit] using h
  | true =>
      simp [literalCircuit]

/-- Point indicator: tests `x = a` as the conjunction of all literals. -/
def eqCircuit {n : Nat} (a : Bitstring n) : DagCircuit n :=
  andList ((List.finRange n).map (fun i => literalCircuit i (a i)))

theorem eval_eqCircuit_iff {n : Nat} (a : Bitstring n) (x : Bitstring n) :
    eval (eqCircuit a) x = true ↔ x = a := by
  simp only [eqCircuit, eval_andList, List.all_map, List.all_eq_true,
    Function.comp, eval_literalCircuit, beq_iff_eq]
  constructor
  · intro h
    funext i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact congrFun h i

theorem size_eqCircuit_le {n : Nat} (a : Bitstring n) :
    size (eqCircuit a) ≤ 5 * n + 2 := by
  have hsum :
      (((List.finRange n).map (fun i => literalCircuit i (a i))).map
        (fun C => size C + 2)).sum ≤ 5 * n := by
    rw [List.map_map]
    have hbound : ∀ i ∈ List.finRange n,
        ((fun C => size C + 2) ∘ fun i => literalCircuit i (a i)) i ≤ 5 := by
      intro i _
      have := size_literalCircuit_le i (a i)
      simp only [Function.comp_apply]
      omega
    have h := sum_map_le_of_forall_le (List.finRange n)
      ((fun C => size C + 2) ∘ fun i => literalCircuit i (a i)) 5 hbound
    rw [List.length_finRange] at h
    omega
  have h := size_andList_le ((List.finRange n).map (fun i => literalCircuit i (a i)))
  simp only [eqCircuit]
  omega

/-- DNF over a finite set of accepted strings. -/
noncomputable def dnfCircuit {n : Nat} (A : Finset (Bitstring n)) : DagCircuit n :=
  orList (A.toList.map eqCircuit)

theorem eval_dnfCircuit_iff {n : Nat} (A : Finset (Bitstring n)) (x : Bitstring n) :
    eval (dnfCircuit A) x = true ↔ x ∈ A := by
  simp only [dnfCircuit, eval_orList, List.any_map, List.any_eq_true,
    Function.comp]
  constructor
  · rintro ⟨a, ha, hx⟩
    have hxa : x = a := (eval_eqCircuit_iff a x).mp hx
    subst hxa
    exact (Finset.mem_toList).mp ha
  · intro hx
    exact ⟨x, (Finset.mem_toList).mpr hx, (eval_eqCircuit_iff x x).mpr rfl⟩

theorem size_dnfCircuit_le {n : Nat} (A : Finset (Bitstring n)) :
    size (dnfCircuit A) ≤ 2 + A.card * (5 * n + 4) := by
  have hsum :
      ((A.toList.map eqCircuit).map (fun C => size C + 2)).sum
        ≤ A.card * (5 * n + 4) := by
    rw [List.map_map]
    have hbound : ∀ a ∈ A.toList,
        ((fun C => size C + 2) ∘ eqCircuit) a ≤ 5 * n + 4 := by
      intro a _
      have := size_eqCircuit_le a
      simp only [Function.comp_apply]
      omega
    have h := sum_map_le_of_forall_le A.toList
      ((fun C => size C + 2) ∘ eqCircuit) (5 * n + 4) hbound
    rw [Finset.length_toList] at h
    exact h
  have h := size_orList_le (A.toList.map eqCircuit)
  simp only [dnfCircuit]
  omega

/-! ### Sparsity -/

/-- Accepted slice of a language at length `n`. -/
def acceptedSet (L : Language) (n : Nat) : Finset (Bitstring n) :=
  Finset.univ.filter (fun x => L n x = true)

/-- Rejected slice of a language at length `n`. -/
def rejectedSet (L : Language) (n : Nat) : Finset (Bitstring n) :=
  Finset.univ.filter (fun x => L n x = false)

@[simp] theorem mem_acceptedSet {L : Language} {n : Nat} {x : Bitstring n} :
    x ∈ acceptedSet L n ↔ L n x = true := by
  simp [acceptedSet]

@[simp] theorem mem_rejectedSet {L : Language} {n : Nat} {x : Bitstring n} :
    x ∈ rejectedSet L n ↔ L n x = false := by
  simp [rejectedSet]

/-- Polynomially sparse: at most `n ^ c + c` accepted strings per length. -/
def PolySparse (L : Language) : Prop :=
  ∃ c : Nat, ∀ n : Nat, (acceptedSet L n).card ≤ n ^ c + c

/-- Polynomially co-sparse: at most `n ^ c + c` rejected strings per length. -/
def PolyCosparse (L : Language) : Prop :=
  ∃ c : Nat, ∀ n : Nat, (rejectedSet L n).card ≤ n ^ c + c

/-! ### The master polynomial estimate -/

/--
Master size estimate: the DNF (or negated DNF) of a `n ^ c + c`-thin slice,
with all combinator overhead, fits below the single polynomial schedule
`n ^ (9c + 13) + (9c + 13)`.
-/
lemma master_poly_bound (c n : Nat) :
    4 + (n ^ c + c) * (5 * n + 4) ≤ n ^ (9 * c + 13) + (9 * c + 13) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · -- n = 0
      have h1 : (0 : Nat) ^ (9 * c + 13) = 0 := Nat.zero_pow (by omega)
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc
        decide
      · have h2 : (0 : Nat) ^ c = 0 := Nat.zero_pow hc
        rw [h1, h2]
        omega
    · -- n = 1
      simp only [Nat.one_pow]
      omega
  · -- n ≥ 2
    have hc_le : c ≤ n ^ c := by
      calc c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ n ^ c := Nat.pow_le_pow_left hn c
    have hP1 : 1 ≤ n ^ c := Nat.one_le_pow _ _ (by omega)
    -- (n^c + c)(5n + 4) ≤ 2 n^c · 9 n = 18 n^(c+1)
    have hstep1 : (n ^ c + c) * (5 * n + 4) ≤ 18 * n ^ (c + 1) := by
      have h1 : n ^ c + c ≤ 2 * n ^ c := by omega
      have h2 : 5 * n + 4 ≤ 9 * n := by omega
      calc (n ^ c + c) * (5 * n + 4) ≤ (2 * n ^ c) * (9 * n) :=
            Nat.mul_le_mul h1 h2
        _ = 18 * (n ^ c * n) := by ring
        _ = 18 * n ^ (c + 1) := by rw [Nat.pow_succ]
    -- 18 n^(c+1) + 4 ≤ 22 n^(c+1) ≤ n^5 n^(c+1) ≤ n^(c+13)
    have hstep2 : 18 * n ^ (c + 1) + 4 ≤ n ^ (c + 13) := by
      have h2pow : (2 : Nat) ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left hn 5
      have h22 : (22 : Nat) ≤ n ^ 5 := by
        have h32 : (2 : Nat) ^ 5 = 32 := by norm_num
        omega
      have hPc1 : 1 ≤ n ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      have hmul : 22 * n ^ (c + 1) ≤ n ^ 5 * n ^ (c + 1) :=
        Nat.mul_le_mul_right _ h22
      have hcomb : n ^ 5 * n ^ (c + 1) ≤ n ^ (c + 13) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hmono : n ^ (c + 13) ≤ n ^ (9 * c + 13) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ### Main theorems: thin languages are in `PpolyDAG` -/

/--
**Sparse upper bound**: a polynomially sparse language lies in `PpolyDAG`
— its slices are DNFs of the few accepted strings.
-/
theorem PpolyDAG_of_polySparse {L : Language} (h : PolySparse L) :
    PpolyDAG L := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨⟨fun n => n ^ (9 * c + 13) + (9 * c + 13),
          ⟨9 * c + 13, fun n => Nat.le_refl _⟩,
          fun n => dnfCircuit (acceptedSet L n), ?_, ?_⟩, trivial⟩
  · intro n
    show size (dnfCircuit (acceptedSet L n)) ≤ n ^ (9 * c + 13) + (9 * c + 13)
    have hsize := size_dnfCircuit_le (acceptedSet L n)
    have hcard := Nat.mul_le_mul_right (5 * n + 4) (hc n)
    have hmaster := master_poly_bound c n
    omega
  · intro n x
    have hiff := eval_dnfCircuit_iff (acceptedSet L n) x
    rw [mem_acceptedSet] at hiff
    cases hLx : L n x with
    | false =>
        cases hEval : eval (dnfCircuit (acceptedSet L n)) x with
        | false => rfl
        | true =>
            exact absurd (hiff.mp hEval) (by simp [hLx])
    | true =>
        exact hiff.mpr hLx

/--
**Co-sparse upper bound**: a polynomially co-sparse language lies in
`PpolyDAG` — its slices are negated DNFs of the few rejected strings.
-/
theorem PpolyDAG_of_polyCosparse {L : Language} (h : PolyCosparse L) :
    PpolyDAG L := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨⟨fun n => n ^ (9 * c + 13) + (9 * c + 13),
          ⟨9 * c + 13, fun n => Nat.le_refl _⟩,
          fun n => notC (dnfCircuit (rejectedSet L n)), ?_, ?_⟩, trivial⟩
  · intro n
    show size (notC (dnfCircuit (rejectedSet L n))) ≤ n ^ (9 * c + 13) + (9 * c + 13)
    have hsize := size_dnfCircuit_le (rejectedSet L n)
    have hnot := size_notC_le (dnfCircuit (rejectedSet L n))
    have hcard := Nat.mul_le_mul_right (5 * n + 4) (hc n)
    have hmaster := master_poly_bound c n
    omega
  · intro n x
    have hiff := eval_dnfCircuit_iff (rejectedSet L n) x
    rw [mem_rejectedSet] at hiff
    rw [eval_notC]
    cases hLx : L n x with
    | false =>
        have : eval (dnfCircuit (rejectedSet L n)) x = true := hiff.mpr hLx
        rw [this]
        rfl
    | true =>
        cases hEval : eval (dnfCircuit (rejectedSet L n)) x with
        | false => rfl
        | true =>
            exact absurd (hiff.mp hEval) (by simp [hLx])

/-! ### Route pruning corollaries -/

/--
**Witness density (accepted side)**: any language witnessing
`¬ PpolyDAG` — in particular any valid `VerifiedNPDAGLowerBoundSource`
witness — must have superpolynomially many accepted strings at infinitely
many lengths.  Formally: it is not polynomially sparse.

This prunes all unary/tally-style witness proposals.
-/
theorem not_polySparse_of_not_PpolyDAG {L : Language}
    (h : ¬ PpolyDAG L) : ¬ PolySparse L :=
  fun hs => h (PpolyDAG_of_polySparse hs)

/-- **Witness density (rejected side)**: dually, not polynomially co-sparse. -/
theorem not_polyCosparse_of_not_PpolyDAG {L : Language}
    (h : ¬ PpolyDAG L) : ¬ PolyCosparse L :=
  fun hs => h (PpolyDAG_of_polyCosparse hs)

/-- Any valid source witness language is dense on the accepted side. -/
theorem VerifiedNPDAGLowerBoundSource.not_polySparse
    (src : VerifiedNPDAGLowerBoundSource) : ¬ PolySparse src.L :=
  not_polySparse_of_not_PpolyDAG src.notInPpolyDAG

/-- Any valid source witness language is dense on the rejected side. -/
theorem VerifiedNPDAGLowerBoundSource.not_polyCosparse
    (src : VerifiedNPDAGLowerBoundSource) : ¬ PolyCosparse src.L :=
  not_polyCosparse_of_not_PpolyDAG src.notInPpolyDAG

/-- The unconditional diagonal witness is dense on the accepted side. -/
theorem dagHardLanguage_not_polySparse : ¬ PolySparse dagHardLanguage :=
  not_polySparse_of_not_PpolyDAG dagHardLanguage_not_PpolyDAG

/-- The unconditional diagonal witness is dense on the rejected side. -/
theorem dagHardLanguage_not_polyCosparse : ¬ PolyCosparse dagHardLanguage :=
  not_polyCosparse_of_not_PpolyDAG dagHardLanguage_not_PpolyDAG

end AlgorithmsToLowerBounds
end Pnp4
