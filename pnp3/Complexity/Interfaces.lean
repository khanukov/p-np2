import Complexity.PsubsetPpolyInternal.ComplexityInterfaces
import Mathlib.Data.Finset.Card
/-!
  pnp3/Complexity/Interfaces.lean

  Strict interface for the active in-repo route.

  This file exposes:
  * canonical `NP := NP_TM` (TM-verifier based);
  * strict non-uniform classes (`PpolyFormula`, `PpolyReal`, `PpolyDAG`);
  * strict separation/inclusion statements and `P_ne_NP` consequences.

  Legacy lightweight compatibility APIs are intentionally excluded from the
  active build to keep this interface aligned with the strict route only.
-/

namespace Pnp3
namespace ComplexityInterfaces

/-!
### Базовые определения

Мы переиспользуем минимальные структуры из внутреннего модуля
`P ⊆ P/poly`. Это сохраняет совместимость интерфейса и позволяет
безболезненно расширять его при необходимости.
-/

/-- Тип языков внутреннего модуля `P ⊆ P/poly`. -/
abbrev Language := Internal.PsubsetPpoly.Complexity.Language

/-- Битовые строки фиксированной длины внутреннего модуля. -/
abbrev Bitstring := Internal.PsubsetPpoly.Complexity.Bitstring

/--
Semantic decider model for fixed input length `n`.

`Carrier` is an explicit computational witness type, `eval` is its semantics.
Using this wrapper prevents solver interfaces from depending on a bare opaque
`Bitstring n → Bool` field only.
-/
structure SemanticDecider (n : Nat) where
  Carrier : Type
  eval : Carrier → Bitstring n → Bool

namespace SemanticDecider

/-- Canonical semantic model where the witness is the function itself. -/
@[simp] def ofFunction (n : Nat) : SemanticDecider n where
  Carrier := Bitstring n → Bool
  eval := fun f x => f x

end SemanticDecider

/-- Класс `P` из внутренней формализации. -/
abbrev P : Language → Prop := Internal.PsubsetPpoly.Complexity.P.{0}

/-!
### Non-trivial structured circuit interface

For switching-based arguments we need fixed syntax/semantics, otherwise locality
claims become vacuous. The declarations below provide that strict interface.
-/

/-- Fixed Boolean circuit syntax used in the strict structured interface. -/
inductive FormulaCircuit : Nat → Type
  | const  {n : Nat} : Bool → FormulaCircuit n
  | input  {n : Nat} : Fin n → FormulaCircuit n
  | not    {n : Nat} : FormulaCircuit n → FormulaCircuit n
  | and    {n : Nat} : FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  | or     {n : Nat} : FormulaCircuit n → FormulaCircuit n → FormulaCircuit n

namespace FormulaCircuit

/-- Semantics of `FormulaCircuit`. -/
def eval {n : Nat} : FormulaCircuit n → Bitstring n → Bool
  | const b, _ => b
  | input i, x => x i
  | not c, x => !(eval c x)
  | and c₁ c₂, x => eval c₁ x && eval c₂ x
  | or c₁ c₂, x => eval c₁ x || eval c₂ x

/-- Syntactic size of `FormulaCircuit`. -/
def size {n : Nat} : FormulaCircuit n → Nat
  | const _ => 1
  | input _ => 1
  | not c => size c + 1
  | and c₁ c₂ => size c₁ + size c₂ + 1
  | or c₁ c₂ => size c₁ + size c₂ + 1

/-- Syntactic depth of `FormulaCircuit` (gate layers). -/
def depth {n : Nat} : FormulaCircuit n → Nat
  | const _ => 0
  | input _ => 0
  | not c => depth c + 1
  | and c₁ c₂ => Nat.max (depth c₁) (depth c₂) + 1
  | or c₁ c₂ => Nat.max (depth c₁) (depth c₂) + 1

/-- Set of input coordinates that syntactically occur in the formula. -/
def support {n : Nat} : FormulaCircuit n → Finset (Fin n)
  | const _ => ∅
  | input i => {i}
  | not c => support c
  | and c₁ c₂ => support c₁ ∪ support c₂
  | or c₁ c₂ => support c₁ ∪ support c₂

/--
If two inputs agree on all coordinates from `support c`, then `c` evaluates
to the same value on both.
-/
lemma eval_eq_of_eq_on_support
    {n : Nat} (c : FormulaCircuit n) {x y : Bitstring n}
    (hxy : ∀ i ∈ support c, x i = y i) :
    eval c x = eval c y := by
  induction c with
  | const b =>
      simp [eval]
  | input i =>
      have hEq : x i = y i := hxy i (by simp [support])
      simpa [eval] using hEq
  | not c ih =>
      have hEq : eval c x = eval c y := ih hxy
      simp [eval, hEq]
  | and c₁ c₂ ih₁ ih₂ =>
      have hEq₁ : eval c₁ x = eval c₁ y := ih₁ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      have hEq₂ : eval c₂ x = eval c₂ y := ih₂ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      simp [eval, hEq₁, hEq₂]
  | or c₁ c₂ ih₁ ih₂ =>
      have hEq₁ : eval c₁ x = eval c₁ y := ih₁ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      have hEq₂ : eval c₂ x = eval c₂ y := ih₂ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      simp [eval, hEq₁, hEq₂]

/-- The number of support coordinates is bounded by formula size. -/
lemma support_card_le_size {n : Nat} (c : FormulaCircuit n) :
    (support c).card ≤ size c := by
  induction c with
  | const b =>
      simp [support, size]
  | input i =>
      simp [support, size]
  | not c ih =>
      simpa [support, size] using Nat.le_trans ih (Nat.le_add_right _ _)
  | and c₁ c₂ ih₁ ih₂ =>
      calc
        (support (FormulaCircuit.and c₁ c₂)).card
            = (support c₁ ∪ support c₂).card := by simp [support]
        _ ≤ (support c₁).card + (support c₂).card :=
          Finset.card_union_le (support c₁) (support c₂)
        _ ≤ size c₁ + size c₂ := Nat.add_le_add ih₁ ih₂
        _ ≤ size (FormulaCircuit.and c₁ c₂) := by simp [size]
  | or c₁ c₂ ih₁ ih₂ =>
      calc
        (support (FormulaCircuit.or c₁ c₂)).card
            = (support c₁ ∪ support c₂).card := by simp [support]
        _ ≤ (support c₁).card + (support c₂).card :=
          Finset.card_union_le (support c₁) (support c₂)
        _ ≤ size c₁ + size c₂ := Nat.add_le_add ih₁ ih₂
        _ ≤ size (FormulaCircuit.or c₁ c₂) := by simp [size]

end FormulaCircuit

/-- Input-or-gate wire in a DAG circuit with `n` inputs and `k` internal gates. -/
inductive DagWire (n k : Nat) : Type
  | input : Fin n → DagWire n k
  | gate : Fin k → DagWire n k

/-- Gate operation using wires from a previously built prefix of the DAG. -/
inductive DagGate (n k : Nat) : Type
  | const : Bool → DagGate n k
  | not : DagWire n k → DagGate n k
  | and : DagWire n k → DagWire n k → DagGate n k
  | or : DagWire n k → DagWire n k → DagGate n k

/--
Acyclic DAG circuit with `n` inputs.

`gate i` may only reference input wires and earlier gates (`< i`), enforced by
the dependent index in `DagGate n i.1`.
-/
structure DagCircuit (n : Nat) where
  gates : Nat
  gate : (i : Fin gates) → DagGate n i.1
  output : DagWire n gates

namespace DagCircuit

/-- Syntactic DAG size (gate count plus one for output accounting). -/
def size {n : Nat} (C : DagCircuit n) : Nat := C.gates + 1

/-- Semantics of an acyclic DAG circuit. -/
def eval {n : Nat} (C : DagCircuit n) (x : Bitstring n) : Bool :=
  let rec evalGateAt (i : Nat) (hi : i < C.gates) : Bool :=
    let evalWire : DagWire n i → Bool := fun w =>
      match w with
      | .input j => x j
      | .gate j => evalGateAt j.1 (Nat.lt_trans j.2 hi)
    match C.gate ⟨i, hi⟩ with
    | .const b => b
    | .not w => !(evalWire w)
    | .and w1 w2 => evalWire w1 && evalWire w2
    | .or w1 w2 => evalWire w1 || evalWire w2
  termination_by i
  match C.output with
  | .input j => x j
  | .gate j => evalGateAt j.1 j.2

end DagCircuit

/-- Strict non-uniform witness with fixed circuit syntax/semantics. -/
structure InPpolyFormula (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, FormulaCircuit n
  family_size_le : ∀ n, FormulaCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x

/-- Strict structured class: polynomial-size fixed-syntax formula families. -/
def PpolyFormula (L : Language) : Prop := ∃ _ : InPpolyFormula L, True

/--
Depth-bounded strict formula witness.

`d` is a global depth cap for every family member `witness.family n`.
-/
structure InPpolyFormulaDepth (L : Language) (d : Nat) where
  witness : InPpolyFormula L
  family_depth_le : ∀ n, FormulaCircuit.depth (witness.family n) ≤ d

/-- Strict structured class with explicit global depth bound `d`. -/
def PpolyFormulaDepth (L : Language) (d : Nat) : Prop :=
  ∃ _ : InPpolyFormulaDepth L d, True

/--
Strict non-uniform witness with fixed acyclic DAG syntax/semantics.

This is the canonical in-repo target corresponding to standard non-uniform
circuits (`P/poly`-style DAG families), as opposed to tree formulas.
-/
structure InPpolyDAG (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, DagCircuit n
  family_size_le : ∀ n, DagCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), DagCircuit.eval (family n) x = L n x

/-- Strict DAG-based non-uniform class. -/
def PpolyDAG (L : Language) : Prop := ∃ _ : InPpolyDAG L, True

/--
Non-trivial non-uniform witness used by the active magnification bridge.

Unlike the lightweight imported `InPpoly`, this interface fixes concrete
syntax/semantics (`FormulaCircuit.eval`) and concrete size
(`FormulaCircuit.size`) rather than allowing a witness-defined evaluator.
-/
structure InPpolyReal (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, FormulaCircuit n
  family_size_le : ∀ n, FormulaCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x

/-- Non-trivial non-uniform class used in place of legacy lightweight witnesses. -/
def PpolyReal (L : Language) : Prop := ∃ _ : InPpolyReal L, True

/-- Any strict formula witness is a `PpolyReal` witness. -/
theorem PpolyReal_of_PpolyFormula {L : Language} :
    PpolyFormula L → PpolyReal L := by
  intro h
  rcases h with ⟨w, _⟩
  exact ⟨{ polyBound := w.polyBound
           polyBound_poly := w.polyBound_poly
           family := w.family
           family_size_le := w.family_size_le
           correct := w.correct }, trivial⟩

/--
Any `PpolyReal` witness is already a strict formula witness in the current
interface, because both classes share the same concrete carrier
(`FormulaCircuit`) and size semantics.
-/
theorem PpolyFormula_of_PpolyReal {L : Language} :
    PpolyReal L → PpolyFormula L := by
  intro h
  rcases h with ⟨w, _⟩
  exact ⟨{ polyBound := w.polyBound
           polyBound_poly := w.polyBound_poly
           family := w.family
           family_size_le := w.family_size_le
           correct := w.correct }, trivial⟩

/--
Current-interface equivalence: `PpolyReal` and `PpolyFormula` coincide.

This theorem is intentionally explicit to keep downstream obligations honest:
closing `P_subset_PpolyReal` currently means closing `P_subset_PpolyFormula`.
-/
theorem ppolyReal_iff_ppolyFormula {L : Language} :
    PpolyReal L ↔ PpolyFormula L := by
  constructor
  · exact PpolyFormula_of_PpolyReal
  · exact PpolyReal_of_PpolyFormula

/-- Any depth-bounded strict formula witness is a strict formula witness. -/
theorem PpolyFormula_of_PpolyFormulaDepth {L : Language} {d : Nat} :
    PpolyFormulaDepth L d → PpolyFormula L := by
  intro h
  rcases h with ⟨wd, _⟩
  exact ⟨wd.witness, trivial⟩

/-!
### Canonical NP encoding utilities

`NP_TM` below uses verifier TMs that read input and certificate as a single
concatenated bitstring. The helper definitions in this section build that
encoding.
-/

/-- Полиномиальный предел длины сертификата для входа длины `n`. -/
def certificateLength (n k : Nat) : Nat := n ^ k + k

/--
Склейка двух битовых строк. Первые `n` позиций берём из `x`,
оставшиеся `m` — из `w`. Такая кодировка позволяет передать вход и
сертификат в одном слове для верификатора.
-/
noncomputable def concatBitstring {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    Bitstring (n + m) := fun i =>
  by
    classical
    by_cases h : (i : Nat) < n
    · exact x ⟨i, h⟩
    · have hge : n ≤ (i : Nat) := Nat.le_of_not_gt h
      let t := Classical.choose (Nat.exists_eq_add_of_le hge)
      have ht : (i : Nat) = n + t :=
        Classical.choose_spec (Nat.exists_eq_add_of_le hge)
      have ht_lt : t < m := by
        have : n + t < n + m := by
          simpa [ht] using i.isLt
        exact (Nat.add_lt_add_iff_left).1 this
      exact w ⟨t, ht_lt⟩

/-!
### TM-мост для `NP`

Иногда удобнее иметь формулировку NP прямо через Turing-машины из
внутреннего модуля `PsubsetPpolyInternal`. Ниже мы добавляем определение
`NP_TM` и лемму, которая переводит такое TM-свидетельство в абстрактное
`NP`-свидетельство в TM-терминах.
-/

/--
`NP_TM`: версия `NP`, сформулированная через верификатор-TM из внешнего
пакета. Машина читает вход и сертификат, склеенные в одну строку.

Эта формулировка является канонической: далее в файле мы фиксируем
`NP := NP_TM`.
-/
def NP_TM (L : Language) : Prop :=
  ∃ (M : Internal.PsubsetPpoly.TM.{0}) (c k : Nat),
    (∀ n,
      M.runTime (n + certificateLength n k) ≤
        (n + certificateLength n k) ^ c + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (certificateLength n k),
          Internal.PsubsetPpoly.TM.accepts
              (M := M)
              (n := n + certificateLength n k)
              (concatBitstring x w) = true)

/-!
### Canonical NP track (TM-faithful)

From this point onward we expose canonical `NP := NP_TM`.
-/

/-- Canonical NP class: TM verifier with polynomial runtime. -/
abbrev NP (L : Language) : Prop := NP_TM L

/-- Runtime-faithful NP track, defined directly via verifier TMs. -/
abbrev NP_strict (L : Language) : Prop := NP_TM L

/-- Strict-track counterpart of `NP ⊄ PpolyFormula`. -/
def NP_strict_not_subset_PpolyFormula : Prop := ∃ L, NP_strict L ∧ ¬ PpolyFormula L

/--
Strict-track counterpart of depth-bounded formula separation:
`NP_TM ⊄ PpolyFormulaDepth d`.
-/
def NP_strict_not_subset_PpolyFormulaDepth (d : Nat) : Prop :=
  ∃ L, NP_strict L ∧ ¬ PpolyFormulaDepth L d

/-- Strict-track counterpart of `NP ⊄ PpolyReal`. -/
def NP_strict_not_subset_PpolyReal : Prop := ∃ L, NP_strict L ∧ ¬ PpolyReal L

/-!
### Формулировки целевых утверждений
-/

/-- Strict structured separation: there exists `L ∈ NP` with `L ∉ PpolyFormula`. -/
def NP_not_subset_PpolyFormula : Prop := ∃ L, NP L ∧ ¬ PpolyFormula L

/--
Depth-bounded strict structured separation:
there exists `L ∈ NP` with `L ∉ PpolyFormulaDepth d`.
-/
def NP_not_subset_PpolyFormulaDepth (d : Nat) : Prop :=
  ∃ L, NP L ∧ ¬ PpolyFormulaDepth L d

/-- Separation against the non-trivial non-uniform class `PpolyReal`. -/
def NP_not_subset_PpolyReal : Prop := ∃ L, NP L ∧ ¬ PpolyReal L

/-- Separation against strict DAG non-uniform class. -/
def NP_not_subset_PpolyDAG : Prop := ∃ L, NP L ∧ ¬ PpolyDAG L

/-- Any strict-track formula separation implies canonical formula separation. -/
theorem NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula :
    NP_strict_not_subset_PpolyFormula → NP_not_subset_PpolyFormula := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩

/--
Any strict-track depth-bounded formula separation implies canonical
depth-bounded formula separation.
-/
theorem NP_not_subset_PpolyFormulaDepth_of_NP_strict_not_subset_PpolyFormulaDepth
    {d : Nat} :
    NP_strict_not_subset_PpolyFormulaDepth d →
      NP_not_subset_PpolyFormulaDepth d := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩

/-- Any strict-track `PpolyReal` separation implies canonical one. -/
theorem NP_not_subset_PpolyReal_of_NP_strict_not_subset_PpolyReal :
    NP_strict_not_subset_PpolyReal → NP_not_subset_PpolyReal := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩

/-- Strict non-uniform inclusion target: `P ⊆ PpolyReal`. -/
def P_subset_PpolyReal : Prop :=
  ∀ L : Language, P L → PpolyReal L

/-- Strict DAG non-uniform inclusion target: `P ⊆ PpolyDAG`. -/
def P_subset_PpolyDAG : Prop :=
  ∀ L : Language, P L → PpolyDAG L

/-- Strict formula-track inclusion target: `P ⊆ PpolyFormula`. -/
def P_subset_PpolyFormula : Prop :=
  ∀ L : Language, P L → PpolyFormula L

/--
In the current interface, proving `P ⊆ PpolyReal` is equivalent to proving
`P ⊆ PpolyFormula`.
-/
theorem P_subset_PpolyFormula_of_P_subset_PpolyReal :
    P_subset_PpolyReal → P_subset_PpolyFormula := by
  intro hReal L hPL
  exact (ppolyReal_iff_ppolyFormula).mp (hReal L hPL)

/--
Conversely, `P ⊆ PpolyFormula` implies `P ⊆ PpolyReal` in the current
interface.
-/
theorem P_subset_PpolyReal_of_P_subset_PpolyFormula :
    P_subset_PpolyFormula → P_subset_PpolyReal := by
  intro hFormula L hPL
  exact (ppolyReal_iff_ppolyFormula).mpr (hFormula L hPL)

/-- Итоговое целевое утверждение `P ≠ NP`. -/
def P_ne_NP : Prop := P ≠ NP

/--
Concrete real-track version:
if some `NP` language is outside `PpolyReal` and `P ⊆ PpolyReal`, then `P ≠ NP`.
-/
theorem P_ne_NP_of_nonuniform_real_separation_concrete
    (hNP : NP_not_subset_PpolyReal) (hP : P_subset_PpolyReal) :
    P_ne_NP := by
  classical
  refine fun hEq => ?_
  have hNP_subset_P : ∀ {L : Language}, NP L → P L := by
    intro L hL
    have hEq_pointwise : P L = NP L := congrArg (fun f => f L) hEq
    exact hEq_pointwise.symm ▸ hL
  rcases hNP with ⟨L₀, hL₀_NP, hL₀_not_PpolyReal⟩
  exact hL₀_not_PpolyReal (hP L₀ (hNP_subset_P hL₀_NP))

/-- Compatibility wrapper for the strict real-track non-uniform route. -/
theorem P_ne_NP_of_nonuniform_real_separation
    (hNP : NP_not_subset_PpolyReal) (hP : P_subset_PpolyReal) :
    P_ne_NP :=
  P_ne_NP_of_nonuniform_real_separation_concrete hNP hP

/--
Concrete DAG-track version:
if some `NP` language is outside `PpolyDAG` and `P ⊆ PpolyDAG`, then `P ≠ NP`.
-/
theorem P_ne_NP_of_nonuniform_dag_separation_concrete
    (hNP : NP_not_subset_PpolyDAG) (hP : P_subset_PpolyDAG) :
    P_ne_NP := by
  classical
  refine fun hEq => ?_
  have hNP_subset_P : ∀ {L : Language}, NP L → P L := by
    intro L hL
    have hEq_pointwise : P L = NP L := congrArg (fun f => f L) hEq
    exact hEq_pointwise.symm ▸ hL
  rcases hNP with ⟨L₀, hL₀_NP, hL₀_notPpolyDAG⟩
  exact hL₀_notPpolyDAG (hP L₀ (hNP_subset_P hL₀_NP))

/-- Compatibility wrapper for the strict DAG-track non-uniform route. -/
theorem P_ne_NP_of_nonuniform_dag_separation
    (hNP : NP_not_subset_PpolyDAG) (hP : P_subset_PpolyDAG) :
    P_ne_NP :=
  P_ne_NP_of_nonuniform_dag_separation_concrete hNP hP

/--
Convenience wrapper for the current interface state:
`NP ⊄ PpolyReal` plus `P ⊆ PpolyFormula` implies `P ≠ NP`.
-/
theorem P_ne_NP_of_real_separation_and_formula_inclusion
    (hNP : NP_not_subset_PpolyReal)
    (hFormulaInclusion : P_subset_PpolyFormula) :
    P_ne_NP := by
  exact P_ne_NP_of_nonuniform_real_separation
    hNP
    (P_subset_PpolyReal_of_P_subset_PpolyFormula hFormulaInclusion)

/-- Contra form for the strict structured class `PpolyFormula`. -/
theorem NP_not_subset_PpolyFormula_of_contra
    (hContra : (∀ L : Language, NP L → PpolyFormula L) → False) :
    NP_not_subset_PpolyFormula := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP L → PpolyFormula L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP L := by
    by_contra hNP
    have hImp : NP L → PpolyFormula L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyFormula : ¬ PpolyFormula L := by
    intro hPpolyFormula
    have hImp : NP L → PpolyFormula L := by
      intro _hL
      exact hPpolyFormula
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyFormula⟩

/-- Contra form for `PpolyReal`. -/
theorem NP_not_subset_PpolyReal_of_contra
    (hContra : (∀ L : Language, NP L → PpolyReal L) → False) :
    NP_not_subset_PpolyReal := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP L → PpolyReal L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP L := by
    by_contra hNP
    have hImp : NP L → PpolyReal L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyReal : ¬ PpolyReal L := by
    intro hPpolyReal
    have hImp : NP L → PpolyReal L := by
      intro _hL
      exact hPpolyReal
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyReal⟩

/-- `NP ⊄ PpolyFormula` immediately yields `NP ⊄ PpolyReal`. -/
theorem NP_not_subset_PpolyReal_of_PpolyFormula
    (hSep : NP_not_subset_PpolyFormula) :
    NP_not_subset_PpolyReal := by
  rcases hSep with ⟨L, hNP, hNotFormula⟩
  refine ⟨L, hNP, ?_⟩
  intro hReal
  exact hNotFormula (PpolyFormula_of_PpolyReal hReal)

/-- `NP ⊄ PpolyReal` immediately yields `NP ⊄ PpolyFormula`. -/
theorem NP_not_subset_PpolyFormula_of_PpolyReal
    (hSep : NP_not_subset_PpolyReal) :
    NP_not_subset_PpolyFormula := by
  rcases hSep with ⟨L, hNP, hNotReal⟩
  refine ⟨L, hNP, ?_⟩
  intro hFormula
  exact hNotReal (PpolyReal_of_PpolyFormula hFormula)

/--
Separation against the larger class `PpolyFormula` implies separation against
every depth-bounded subclass `PpolyFormulaDepth d`.
-/
theorem NP_not_subset_PpolyFormulaDepth_of_NP_not_subset_PpolyFormula
    {d : Nat}
    (hSep : NP_not_subset_PpolyFormula) :
    NP_not_subset_PpolyFormulaDepth d := by
  rcases hSep with ⟨L, hNP, hNotFormula⟩
  refine ⟨L, hNP, ?_⟩
  intro hDepth
  exact hNotFormula (PpolyFormula_of_PpolyFormulaDepth hDepth)

/-! ### Strict-track contra forms -/

/-- Contra form for strict formula separation (`NP_TM ⊄ PpolyFormula`). -/
theorem NP_strict_not_subset_PpolyFormula_of_contra
    (hContra : (∀ L : Language, NP_strict L → PpolyFormula L) → False) :
    NP_strict_not_subset_PpolyFormula := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP_strict L → PpolyFormula L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP_strict L := by
    by_contra hNP
    have hImp : NP_strict L → PpolyFormula L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyFormula : ¬ PpolyFormula L := by
    intro hPpolyFormula
    have hImp : NP_strict L → PpolyFormula L := by
      intro _hL
      exact hPpolyFormula
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyFormula⟩

/-- Contra form for strict `PpolyReal` separation (`NP_TM ⊄ PpolyReal`). -/
theorem NP_strict_not_subset_PpolyReal_of_contra
    (hContra : (∀ L : Language, NP_strict L → PpolyReal L) → False) :
    NP_strict_not_subset_PpolyReal := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP_strict L → PpolyReal L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP_strict L := by
    by_contra hNP
    have hImp : NP_strict L → PpolyReal L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyReal : ¬ PpolyReal L := by
    intro hPpolyReal
    have hImp : NP_strict L → PpolyReal L := by
      intro _hL
      exact hPpolyReal
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyReal⟩

end ComplexityInterfaces
