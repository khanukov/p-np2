import AC0.MultiSwitching.Trace
import AC0.MultiSwitching.AC0FormulaAtom
import AC0.MultiSwitching.FuncCNF
import AC0.AC0FormulaRestrict
import AC0.AC0FormulaFamily
import Mathlib.Data.List.MinMax
import Mathlib.Data.Vector.Basic

/-!
  pnp3/AC0/MultiSwitching/DepthInduction.lean

  Минимальные «скелетные» определения для будущей индукции по глубине.
  Этот файл НЕ доказывает multi‑switching для depth>2, но фиксирует типы
  и простейшие комбинаторы, которые понадобятся при формализации CCDT‑индукции.

  Почему этот файл полезен уже сейчас:
  * он даёт явный тип «трасса по уровням глубины»;
  * позволяет аккуратно собирать информацию по длинам трасс
    (например, суммарная длина или максимум по уровням);
  * служит интерфейсом для будущих лемм «склейки» shrinkage.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-!
### IH witness interface (compile-first)

We parameterize the induction step by a per-formula IH witness that provides
an exact deciding tree for each subformula of depth `d`.
-/

/-- IH witness for formulas at depth `d`. -/
structure IHWitness (n d : Nat) where
  witness : AC0Formula n d → AtomTailWitness n
  witness_eval_eq :
    ∀ f : AC0Formula n d, (witness f).eval = AC0Formula.eval n d f

namespace IHWitness

def atomOf {n d : Nat} (W : IHWitness n d) (f : AC0Formula n d) : AC0FormulaAtom d n :=
  { formula := f
    witness := W.witness f
    witness_eval_eq := W.witness_eval_eq f }

def litOf {n d : Nat} (W : IHWitness n d) (f : AC0Formula n d) : AtomLit n :=
  { atom := (W.atomOf f).toAtom
    neg := false }

def clauseOf {n d : Nat} (W : IHWitness n d) (f : AC0Formula n d) : FuncClause n :=
  { lits := [W.litOf f] }

def termOf {n d : Nat} (W : IHWitness n d) (f : AC0Formula n d) : FuncTerm n :=
  { lits := [W.litOf f] }

def litNegOf {n d : Nat} (W : IHWitness n d) (f : AC0Formula n d) : AtomLit n :=
  { atom := (W.atomOf f).toAtom
    neg := true }

def clauseNegOf {n d : Nat} (W : IHWitness n d) (f : AC0Formula n d) : FuncClause n :=
  { lits := [W.litNegOf f] }

def funcCNF_of_andList {n d : Nat} (W : IHWitness n d) :
    AC0FormulaList n d → FuncCNF n
  | AC0FormulaList.nil => { clauses := [] }
  | AC0FormulaList.cons f fs =>
      let C := W.clauseOf f
      let F := funcCNF_of_andList W fs
      { clauses := C :: F.clauses }

def funcCNF_of_andList_neg {n d : Nat} (W : IHWitness n d) :
    AC0FormulaList n d → FuncCNF n
  | AC0FormulaList.nil => { clauses := [] }
  | AC0FormulaList.cons f fs =>
      let C := W.clauseNegOf f
      let F := funcCNF_of_andList_neg W fs
      { clauses := C :: F.clauses }

def funcDNF_of_orList {n d : Nat} (W : IHWitness n d) :
    AC0FormulaList n d → FuncDNF n
  | AC0FormulaList.nil => { terms := [] }
  | AC0FormulaList.cons f fs =>
      let T := W.termOf f
      let F := funcDNF_of_orList W fs
      { terms := T :: F.terms }

@[simp] lemma eval_litOf {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n d) (x : Core.BitVec n) :
    AtomLit.eval (W.litOf f) x = AC0Formula.eval n d f x := by
  calc
    AtomLit.eval (W.litOf f) x = (W.witness f).eval x := by
      simp [IHWitness.litOf, AtomLit.eval, IHWitness.atomOf, AC0FormulaAtom.toAtom,
        AtomTailWitness.toAtom]
    _ = AC0Formula.eval n d f x := by
      have h := congrArg (fun g => g x) (W.witness_eval_eq f)
      simpa using h

@[simp] lemma eval_litOf_if {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n d) (x : Core.BitVec n) :
    (if (W.litOf f).neg = true then !(W.litOf f).atom.eval x
     else (W.litOf f).atom.eval x) = AC0Formula.eval n d f x := by
  simpa [AtomLit.eval] using (eval_litOf (W := W) (f := f) (x := x))

@[simp] lemma eval_clauseOf {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n d) (x : Core.BitVec n) :
    FuncClause.eval (W.clauseOf f) x = AC0Formula.eval n d f x := by
  simpa [IHWitness.clauseOf, FuncClause.eval] using
    (eval_litOf (W := W) (f := f) (x := x))

@[simp] lemma eval_termOf {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n d) (x : Core.BitVec n) :
    FuncTerm.eval (W.termOf f) x = AC0Formula.eval n d f x := by
  simpa [IHWitness.termOf, FuncTerm.eval] using
    (eval_litOf (W := W) (f := f) (x := x))

@[simp] lemma eval_litNegOf {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n d) (x : Core.BitVec n) :
    AtomLit.eval (W.litNegOf f) x = ! AC0Formula.eval n d f x := by
  simp [IHWitness.litNegOf, AtomLit.eval, IHWitness.atomOf, AC0FormulaAtom.toAtom,
    AtomTailWitness.toAtom, W.witness_eval_eq f]

@[simp] lemma eval_clauseNegOf {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n d) (x : Core.BitVec n) :
    FuncClause.eval (W.clauseNegOf f) x = ! AC0Formula.eval n d f x := by
  simpa [IHWitness.clauseNegOf, FuncClause.eval] using
    (eval_litNegOf (W := W) (f := f) (x := x))

@[simp] lemma eval_funcCNF_of_andList {n d : Nat} (W : IHWitness n d) :
    ∀ fs : AC0FormulaList n d, ∀ x,
      FuncCNF.eval (IHWitness.funcCNF_of_andList W fs) x =
        AC0Formula.evalAll n d fs x
  | AC0FormulaList.nil, x => by
      simp [IHWitness.funcCNF_of_andList, FuncCNF.eval, AC0Formula.evalAll,
        AC0Formula.evalCore]
  | AC0FormulaList.cons f fs, x => by
      have hclause :
          (W.clauseOf f).lits.any (fun ℓ => if ℓ.neg = true then !ℓ.atom.eval x else ℓ.atom.eval x) =
            AC0Formula.eval n d f x := by
        simp [IHWitness.clauseOf, IHWitness.litOf, AtomLit.eval, IHWitness.atomOf,
          AC0FormulaAtom.toAtom, AtomTailWitness.toAtom, W.witness_eval_eq]
      have hclause' :
          (W.clauseOf f).lits.any (fun ℓ => if ℓ.neg = true then !ℓ.atom.eval x else ℓ.atom.eval x) =
            AC0Formula.evalCore n (AC0Formula.EvalArg.form f) x := by
        simpa [AC0Formula.eval] using hclause
      have htail := eval_funcCNF_of_andList (W := W) (fs := fs) (x := x)
      -- reduce to tail evaluation and apply IH
      simp [IHWitness.funcCNF_of_andList, FuncCNF.eval, hclause'] at *
      simp [htail, AC0Formula.evalAll, AC0Formula.evalCore]

def evalAllNeg {n d : Nat} : AC0FormulaList n d → Core.BitVec n → Bool
  | AC0FormulaList.nil => fun _ => true
  | AC0FormulaList.cons f fs => fun x => (! AC0Formula.eval n d f x) && evalAllNeg fs x

lemma evalAllNeg_eq_not_evalAny {n d : Nat} :
    ∀ fs : AC0FormulaList n d, ∀ x,
      evalAllNeg (n := n) (d := d) fs x = ! AC0Formula.evalAny n d fs x
  | AC0FormulaList.nil, x => by
      simp [evalAllNeg, AC0Formula.evalAny, AC0Formula.evalCore]
  | AC0FormulaList.cons f fs, x => by
      have ih := evalAllNeg_eq_not_evalAny (n := n) (d := d) fs x
      -- Boolean De Morgan: (!a && !b) = !(a || b)
      have hdemorgan (a b : Bool) : (!a && !b) = !(a || b) := by
        cases a <;> cases b <;> rfl
      dsimp [evalAllNeg]
      rw [ih]
      set a := AC0Formula.eval n d f x
      set b := AC0Formula.evalAny n d fs x
      have h' : AC0Formula.evalAny n d (AC0FormulaList.cons f fs) x = (a || b) := by
        simp [AC0Formula.evalAny, AC0Formula.evalCore, a, b, AC0Formula.eval]
      -- rewrite RHS and apply De Morgan
      simpa [h'] using (hdemorgan a b)

@[simp] lemma eval_funcCNF_of_andList_neg {n d : Nat} (W : IHWitness n d) :
    ∀ fs : AC0FormulaList n d, ∀ x,
      FuncCNF.eval (IHWitness.funcCNF_of_andList_neg W fs) x =
        evalAllNeg (n := n) (d := d) fs x
  | AC0FormulaList.nil, x => by
      simp [IHWitness.funcCNF_of_andList_neg, FuncCNF.eval, evalAllNeg]
  | AC0FormulaList.cons f fs, x => by
      have hclause :
          (W.clauseNegOf f).lits.any (fun ℓ => if ℓ.neg = true then !ℓ.atom.eval x else ℓ.atom.eval x) =
            ! AC0Formula.eval n d f x := by
        simp [IHWitness.clauseNegOf, IHWitness.litNegOf, AtomLit.eval, IHWitness.atomOf,
          AC0FormulaAtom.toAtom, AtomTailWitness.toAtom, W.witness_eval_eq]
      have hclause' :
          (W.clauseNegOf f).lits.any (fun ℓ => if ℓ.neg = true then !ℓ.atom.eval x else ℓ.atom.eval x) =
            ! AC0Formula.evalCore n (AC0Formula.EvalArg.form f) x := by
        simpa [AC0Formula.eval] using hclause
      have htail := eval_funcCNF_of_andList_neg (W := W) (fs := fs) (x := x)
      -- reduce to tail evaluation and apply IH
      simp [IHWitness.funcCNF_of_andList_neg, FuncCNF.eval, hclause'] at *
      simp [htail, evalAllNeg, hclause]

@[simp] lemma eval_funcCNF_of_orList_via_neg {n d : Nat} (W : IHWitness n d) :
    ∀ fs : AC0FormulaList n d, ∀ x,
      FuncCNF.eval (IHWitness.funcCNF_of_andList_neg W fs) x =
        ! AC0Formula.evalAny n d fs x
  | fs, x => by
      have h1 := eval_funcCNF_of_andList_neg (W := W) (fs := fs) (x := x)
      have h2 := evalAllNeg_eq_not_evalAny (n := n) (d := d) fs x
      simpa [h2] using h1

end IHWitness

/-!
### Induction skeleton (compile-first)

We package the IH as a family of exact deciding trees with a uniform depth bound.
This is the object that later plugs into trunk+tail composition.
-/

structure DepthIHResult (n d : Nat) where
  witness : ∀ f : AC0Formula n d, DecidingTreeWitness n (AC0Formula.eval n d f)
  depthBound : Nat
  depth_le : ∀ f : AC0Formula n d, PDT.depth (witness f).tree ≤ depthBound

def DepthIHResult.toIHWitness {n d : Nat} (R : DepthIHResult n d) : IHWitness n d :=
  { witness := fun f => AtomTailWitness.ofDecidingTree (R.witness f)
    witness_eval_eq := fun f => rfl }


/-!
### Top-layer extraction

For a depth-(d+1) formula, expose the top layer as a functional CNF or DNF
over IH-atoms. This is a compile-first bridge for the induction step.
-/

def topLayer {n d : Nat} (W : IHWitness n d) :
    AC0Formula n (Nat.succ d) → Sum (FuncCNF n) (FuncDNF n)
  | AC0Formula.and fs => Sum.inl (IHWitness.funcCNF_of_andList W fs)
  | AC0Formula.or fs => Sum.inr (IHWitness.funcDNF_of_orList W fs)

-- CNF-only view of the top layer (OR handled via negation).
def topLayerCNF {n d : Nat} (W : IHWitness n d) :
    AC0Formula n (Nat.succ d) → FuncCNF n
  | AC0Formula.and fs => IHWitness.funcCNF_of_andList W fs
  | AC0Formula.or fs => IHWitness.funcCNF_of_andList_neg W fs

lemma eval_topLayerCNF {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n (Nat.succ d)) (x : Core.BitVec n) :
    FuncCNF.eval (topLayerCNF (W := W) f) x =
      match f with
      | AC0Formula.and fs => AC0Formula.evalAll n d fs x
      | AC0Formula.or fs => ! AC0Formula.evalAny n d fs x := by
  cases f with
  | and fs =>
      have h := IHWitness.eval_funcCNF_of_andList (W := W) (fs := fs) (x := x)
      simpa [topLayerCNF, FuncCNF.eval, AC0Formula.evalAll, AC0Formula.evalCore] using h
  | or fs =>
      have h := IHWitness.eval_funcCNF_of_orList_via_neg (W := W) (fs := fs) (x := x)
      simpa [topLayerCNF, FuncCNF.eval] using h

def decidingTree_topLayer_to_formula {n d : Nat} (W : IHWitness n d)
    (f : AC0Formula n (Nat.succ d)) :
    DecidingTreeWitness n (FuncCNF.eval (topLayerCNF (W := W) f)) →
      DecidingTreeWitness n
        (match f with
        | AC0Formula.and fs => AC0Formula.evalAll n d fs
        | AC0Formula.or fs => AC0Formula.evalAny n d fs) := by
  intro WT
  cases f with
  | and fs =>
      have h :
          FuncCNF.eval (topLayerCNF (W := W) (AC0Formula.and fs)) =
            AC0Formula.evalAll n d fs := by
        funext x
        simpa using (eval_topLayerCNF (W := W) (f := AC0Formula.and fs) (x := x))
      have WT' : DecidingTreeWitness n (AC0Formula.evalAll n d fs) := by
        simpa [h] using WT
      exact WT'
  | or fs =>
      have h :
          FuncCNF.eval (topLayerCNF (W := W) (AC0Formula.or fs)) =
            (fun x => ! AC0Formula.evalAny n d fs x) := by
        funext x
        simpa using (eval_topLayerCNF (W := W) (f := AC0Formula.or fs) (x := x))
      have WT' : DecidingTreeWitness n (fun x => ! AC0Formula.evalAny n d fs x) := by
        simpa [h] using WT
      have WT'' : DecidingTreeWitness n (fun x => !! AC0Formula.evalAny n d fs x) :=
        DecidingTreeWitness.neg WT'
      have hdouble : (fun x => !! AC0Formula.evalAny n d fs x) =
          (fun x => AC0Formula.evalAny n d fs x) := by
        funext x
        cases hval : AC0Formula.evalAny n d fs x <;> simp [hval]
      simpa [hdouble] using WT''

def topLayerFromIH {n d : Nat} (R : DepthIHResult n d) :
    AC0Formula n (Nat.succ d) → Sum (FuncCNF n) (FuncDNF n) :=
  topLayer (W := R.toIHWitness)

def topLayerFamily {n d : Nat} (W : IHWitness n d) :
    AC0FormulaFamily (Nat.succ d) n → List (Sum (FuncCNF n) (FuncDNF n)) :=
  List.map (topLayer (W := W))

def topLayerFamilyCNF {n d : Nat} (W : IHWitness n d) :
    AC0FormulaFamily (Nat.succ d) n → List (FuncCNF n) :=
  List.map (topLayerCNF (W := W))

/-!
### Трасса одного уровня

`LevelTrace` фиксирует формулу, длину трассы и саму трассу.
Мы сознательно держим это в «локальной» форме (CNF на одном уровне),
чтобы потом в индукции по глубине было легко составлять список таких шагов.
-/

structure LevelTrace (n w : Nat) where
  /-- Формула уровня (k‑CNF). -/
  F : kCNF n w
  /-- Длина трассы. -/
  t : Nat
  /-- Каноническая трасса фиксированной длины. -/
  trace : Trace (F := F) t

/-!
### Трасса по глубине

`DepthTrace` — это вектор `LevelTrace` длины `d`.
Он фиксирует «цепочку» трасс по уровням глубины и позволяет
сформулировать суммарные оценки на длину.
-/

structure DepthTrace (n w : Nat) (d : Nat) where
  /-- Список трасс по уровням (ровно `d` штук). -/
  levels : Vector (LevelTrace n w) d

/--
Список длин по уровням глубины.

Вынесен в отдельное определение, чтобы не дублировать в доказательствах
одно и то же выражение `T.levels.toList.map (fun L => L.t)`.
-/
def DepthTrace.stepLengths {n w d : Nat} (T : DepthTrace n w d) : List Nat :=
  T.levels.toList.map (fun L => L.t)

namespace DepthTrace

/-! ### Вспомогательные леммы о списках натуральных -/

/-!
### Суммарная длина трасс

`totalSteps` — сумма всех длин `t` по уровням.
Эта величина будет участвовать в будущих оценках глубины
и в формулировках «склейки» shrinkage.
-/

def totalSteps {n w d : Nat} (T : DepthTrace n w d) : Nat :=
  T.stepLengths.sum

@[simp] lemma totalSteps_zero {n w : Nat} (T : DepthTrace n w 0) :
    totalSteps T = 0 := by
  rcases T with ⟨levels⟩
  have hsize : levels.toArray.size = 0 := by
    simpa using (Vector.size_toArray levels)
  have harray : levels.toArray = #[] := (Array.size_eq_zero).1 hsize
  have hnil : levels.toArray.toList = [] := (Array.toList_eq_nil_iff).2 harray
  have hnil' : levels.toList = [] := by
    simpa [Vector.toList_toArray] using hnil
  simp [totalSteps, DepthTrace.stepLengths, hnil']

/-!
### Максимальная длина уровня

`maxSteps` — максимум по всем `t` на уровнях.
Эта величина пригодится, если будем оценивать глубину через
максимальную длину шага (вместо суммы).
-/

def maxSteps {n w d : Nat} (T : DepthTrace n w d) : Nat :=
  T.stepLengths.foldr Nat.max 0

@[simp] lemma maxSteps_zero {n w : Nat} (T : DepthTrace n w 0) :
    maxSteps T = 0 := by
  rcases T with ⟨levels⟩
  have hsize : levels.toArray.size = 0 := by
    simpa using (Vector.size_toArray levels)
  have harray : levels.toArray = #[] := (Array.size_eq_zero).1 hsize
  have hnil : levels.toArray.toList = [] := (Array.toList_eq_nil_iff).2 harray
  have hnil' : levels.toList = [] := by
    simpa [Vector.toList_toArray] using hnil
  simp [maxSteps, DepthTrace.stepLengths, hnil']

/-- Если каждый уровень ограничен сверху `B`, то и максимум уровней ≤ `B`. -/
lemma maxSteps_le_of_forall_level_le {n w d : Nat} (T : DepthTrace n w d)
    {B : Nat}
    (h : ∀ L ∈ T.levels.toList, L.t ≤ B) :
    maxSteps T ≤ B := by
  have h' : ∀ x ∈ T.stepLengths, x ≤ B := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨L, hLmem, rfl⟩
    exact h L hLmem
  simpa [maxSteps] using
    (List.max_le_of_forall_le (l := T.stepLengths) (a := B) h')

/-- Если каждый уровень ограничен сверху `B`, то сумма ≤ `d * B`. -/
lemma totalSteps_le_of_forall_level_le {n w d : Nat} (T : DepthTrace n w d)
    {B : Nat}
    (h : ∀ L ∈ T.levels.toList, L.t ≤ B) :
    totalSteps T ≤ d * B := by
  have h' : ∀ x ∈ T.stepLengths, x ≤ B := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨L, hLmem, rfl⟩
    exact h L hLmem
  have hsum : T.stepLengths.sum ≤ T.stepLengths.length * B := by
    -- Используем стандартную лемму `sum_le_card_nsmul` и
    -- специализируем `•` для `Nat` в обычное умножение.
    simpa [nsmul_eq_mul] using List.sum_le_card_nsmul T.stepLengths B h'
  have hlen : T.stepLengths.length = d := by
    simp [DepthTrace.stepLengths]
  simpa [totalSteps, hlen] using hsum

/-- Любой уровень ограничен сверху общим максимумом `maxSteps`. -/
lemma level_le_maxSteps {n w d : Nat} (T : DepthTrace n w d)
    (L : LevelTrace n w) (hL : L ∈ T.levels.toList) :
    L.t ≤ maxSteps T := by
  unfold maxSteps
  exact List.le_max_of_le
    (hx := by simpa [DepthTrace.stepLengths] using (List.mem_map.mpr ⟨L, hL, rfl⟩))
    (h := le_rfl)

/-- Верхняя оценка суммы через максимум по уровням: `sum ≤ d * max`. -/
lemma totalSteps_le_mul_maxSteps {n w d : Nat} (T : DepthTrace n w d) :
    totalSteps T ≤ d * maxSteps T := by
  refine totalSteps_le_of_forall_level_le (T := T) (B := maxSteps T) ?_
  intro L hL
  exact level_le_maxSteps (T := T) L hL

/-- Нижняя оценка: максимум уровней не превосходит суммарного числа шагов. -/
lemma maxSteps_le_totalSteps {n w d : Nat} (T : DepthTrace n w d) :
    maxSteps T ≤ totalSteps T := by
  have hmax : T.stepLengths.foldr Nat.max 0 ≤ T.stepLengths.sum := by
    apply List.max_le_of_forall_le
    intro x hx
    exact List.le_sum_of_mem hx
  simpa [maxSteps, totalSteps] using hmax

/--
Если длина каждого уровня ограничена `B^d`, а число уровней `d` не превосходит `B`,
то суммарная длина также ограничена `B^(d+1)`.

Это полезная «арифметическая склейка» для шага глубинной индукции:
мы превращаем локальную оценку на каждом уровне в единую глобальную оценку.
-/
lemma totalSteps_le_pow_succ_of_forall_level_le_pow {n w d B : Nat}
    (T : DepthTrace n w d)
    (hdepth : d ≤ B)
    (h : ∀ L ∈ T.levels.toList, L.t ≤ Nat.pow B d) :
    totalSteps T ≤ Nat.pow B (d + 1) := by
  have hsum : totalSteps T ≤ d * Nat.pow B d :=
    totalSteps_le_of_forall_level_le (T := T) (B := Nat.pow B d) h
  have hmul : d * Nat.pow B d ≤ B * Nat.pow B d :=
    Nat.mul_le_mul_right (Nat.pow B d) hdepth
  calc
    totalSteps T ≤ d * Nat.pow B d := hsum
    _ ≤ B * Nat.pow B d := hmul
    _ = Nat.pow B (d + 1) := by
      simp [Nat.pow_succ, Nat.mul_comm]

end DepthTrace

/-!
### Комментарий о дальнейшем использовании

* Индукционный шаг по глубине будет строить `DepthTrace` длины `d+1`,
  где каждый уровень — результат применения CCDT/encoding к подформулам.
* На основе `totalSteps`/`maxSteps` мы будем формулировать и доказывать
  неравенства типа `t ≤ (log₂(M+2))^(d+1)`.
-/

end MultiSwitching
end AC0
end Pnp3
