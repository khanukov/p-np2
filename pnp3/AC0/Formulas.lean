/-
  pnp3/AC0/Formulas.lean

  Формализация базовых булевых формул, появляющихся в классических
  switching-леммах: конъюнктивные и дизъюнктивные термы, а также их
  ограничение случайными подкубами.  Этот модуль служит подготовительным
  этапом к устранению внешних аксиом `shrinkage_for_AC0` и
  `shrinkage_for_localCircuit`: после определения синтаксиса формул можно
  строить непосредственные деревья решений и проводить оценку ошибок.

  Основная идея — работать с произвольными списками литералов.  Мы не
  накладываем немедленно ограничений на ширину, поэтому подход применим
  и в более сложных сценариях (например, при анализе локальных схем).
-/

import Core.BooleanBasics
import Core.PDT
import Core.ShrinkageWitness
import Core.SAL_Core

namespace Pnp3
namespace AC0

open Core

/-! ### Литералы -/

/-- Литерал — указание индекса входной переменной и требуемого булевого
    значения.  В ДНФ термы строятся как конъюнкции литералов, а в КНФ
    клаузы — как дизъюнкции. -/
structure Literal (n : Nat) where
  idx : Fin n
  val : Bool
  deriving DecidableEq, Repr

namespace Literal

variable {n : Nat}

/-- Истинность литерала на данном входе в булевой форме.  Мы явно
    используем `decide`, чтобы без труда подключать `List.any` и
    `List.all`. -/
@[simp] def holds (ℓ : Literal n) (x : Core.BitVec n) : Bool :=
  decide (x ℓ.idx = ℓ.val)

/-- Удобное представление литерала как пары `BitFix`. -/
@[simp] def toBitFix (ℓ : Literal n) : BitFix n :=
  (ℓ.idx, ℓ.val)

/-- Построение литерала из пары индекса и значения. -/
@[simp] def ofBitFix (pair : BitFix n) : Literal n :=
  ⟨pair.1, pair.2⟩

@[simp] lemma ofBitFix_toBitFix (ℓ : Literal n) :
    ofBitFix (toBitFix ℓ) = ℓ := by
  cases ℓ
  rfl

@[simp] lemma toBitFix_ofBitFix (pair : BitFix n) :
    toBitFix (ofBitFix pair) = pair := by
  cases pair
  rfl

end Literal

/-! ### Клаузы (дизъюнкции литералов) -/

/-- Клауза в КНФ: дизъюнкция литералов. -/
structure Clause (n : Nat) where
  lits : List (Literal n)
  deriving DecidableEq, Repr

namespace Clause

variable {n : Nat}

/-- Удобная оболочка вокруг `List.any`: значение списка литералов на входе. -/
@[simp] def evalList (lits : List (Literal n)) (x : Core.BitVec n) : Bool :=
  lits.any (fun ℓ => Literal.holds ℓ x)

@[simp] lemma evalList_nil (x : Core.BitVec n) : evalList ([] : List (Literal n)) x = false := by
  unfold evalList
  simp

@[simp] lemma evalList_singleton (ℓ : Literal n) (x : Core.BitVec n) :
    evalList [ℓ] x = Literal.holds ℓ x := by
  unfold evalList
  simp

/-- Значение клаузы на входе `x`.  Используем `List.any`, который
    возвращает `true`, если хотя бы один литерал удовлетворён. -/
@[simp] def eval (C : Clause n) (x : Core.BitVec n) : Bool :=
  evalList C.lits x

/-- Результат ограничения клаузы подкубом: `satisfied` означает, что
    дизъюнкция стала тождественно истинной; `falsified` — тождественно
    ложной; `pending lits` — клауза, зависящая только от оставшихся
    литералов. -/
inductive RestrictResult (n : Nat)
| satisfied : RestrictResult n
| falsified : RestrictResult n
| pending   : List (Literal n) → RestrictResult n
  deriving Repr

namespace RestrictResult

variable {n : Nat}

@[simp] def toClause : RestrictResult n → Option (Clause n)
  | RestrictResult.satisfied    => none
  | RestrictResult.falsified    => some ⟨[]⟩
  | RestrictResult.pending lits => some ⟨lits⟩

end RestrictResult

/-- Вспомогательная функция, реализующая ограничение списка литералов. -/
private def restrictList (β : Subcube n) :
    List (Literal n) → RestrictResult n
  | [] => RestrictResult.falsified
  | ℓ :: rest =>
    match β ℓ.idx with
    | some b =>
        if b = ℓ.val then
          RestrictResult.satisfied
        else
          restrictList β rest
    | none =>
        match restrictList β rest with
        | RestrictResult.satisfied => RestrictResult.satisfied
        | RestrictResult.falsified => RestrictResult.pending [ℓ]
        | RestrictResult.pending L => RestrictResult.pending (ℓ :: L)

/-- Ограничение клаузы подкубом. -/
@[simp] def restrict (C : Clause n) (β : Subcube n) : RestrictResult n :=
  restrictList (β := β) C.lits

namespace RestrictResult

variable {n : Nat}

/-- Интерпретация результата ограничения: для удовлетворённой/опровержённой
    клаузы возвращаем константы, в противном случае оцениваем остаток. -/
@[simp] def eval (res : RestrictResult n) (x : Core.BitVec n) : Bool :=
  match res with
  | RestrictResult.satisfied => true
  | RestrictResult.falsified => false
  | RestrictResult.pending lits => Clause.evalList lits x

end RestrictResult

end Clause

/-! ### Термы (конъюнкции литералов) -/

/-- Терм в ДНФ: конъюнкция литералов. -/
structure Term (n : Nat) where
  lits : List (Literal n)
  deriving DecidableEq, Repr

namespace Term

variable {n : Nat}

/-- Значение терма на входе `x`: все литералы должны выполняться. -/
@[simp] def eval (T : Term n) (x : Core.BitVec n) : Bool :=
  T.lits.all (fun ℓ => Literal.holds ℓ x)

/-- Результат ограничения терма: `satisfied` — терм стал тождественно
    истинным; `falsified` — ложным; `pending lits` — остаточный терм. -/
inductive RestrictResult (n : Nat)
| satisfied : RestrictResult n
| falsified : RestrictResult n
| pending   : List (Literal n) → RestrictResult n
  deriving Repr

namespace RestrictResult

variable {n : Nat}

@[simp] def toTerm : RestrictResult n → Option (Term n)
  | RestrictResult.satisfied    => some ⟨[]⟩
  | RestrictResult.falsified    => none
  | RestrictResult.pending lits => some ⟨lits⟩

end RestrictResult

private def restrictList (β : Subcube n) :
    List (Literal n) → RestrictResult n
  | [] => RestrictResult.satisfied
  | ℓ :: rest =>
    match β ℓ.idx with
    | some b =>
        if b = ℓ.val then
          restrictList β rest
        else
          RestrictResult.falsified
    | none =>
        match restrictList β rest with
        | RestrictResult.satisfied => RestrictResult.satisfied
        | RestrictResult.falsified => RestrictResult.falsified
        | RestrictResult.pending L => RestrictResult.pending (ℓ :: L)

@[simp] def restrict (T : Term n) (β : Subcube n) : RestrictResult n :=
  restrictList (β := β) T.lits

namespace RestrictResult

variable {n : Nat}

/-- Интерпретация результата ограничения для термов. -/
@[simp] def eval (res : RestrictResult n) (x : Core.BitVec n) : Bool :=
  match res with
  | RestrictResult.satisfied => true
  | RestrictResult.falsified => false
  | RestrictResult.pending lits => Term.eval ⟨lits⟩ x

end RestrictResult

end Term

/-! ### Полные формулы -/

/-- КНФ-формула как список клауз. -/
structure CNF (n : Nat) where
  clauses : List (Clause n)
  deriving Repr

/-- ДНФ-формула как список термов. -/
structure DNF (n : Nat) where
  terms : List (Term n)
  deriving Repr

namespace CNF

variable {n : Nat}

@[simp] def eval (F : CNF n) (x : Core.BitVec n) : Bool :=
  F.clauses.all (fun C => Clause.eval C x)

end CNF

namespace DNF

variable {n : Nat}

@[simp] def eval (F : DNF n) (x : Core.BitVec n) : Bool :=
  F.terms.any (fun T => Term.eval T x)

end DNF

/-! ### Полные деревья решений и точные сертификаты -/

open Core

namespace DecisionTree

variable {n : Nat}

@[simp] def setBit (β : Core.Subcube n) (i : Fin n) (b : Bool) : Core.Subcube n :=
  fun j => if j = i then some b else β j

@[simp] lemma setBit_same (β : Core.Subcube n) (i : Fin n) (b : Bool) :
    setBit β i b i = some b := by simp [setBit]

@[simp] lemma setBit_ne (β : Core.Subcube n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    setBit β i b j = β j := by simp [setBit, h]

def build (β : Core.Subcube n) : List (Fin n) → Core.PDT n
  | [] => Core.PDT.leaf β
  | i :: rest =>
      Core.PDT.node i (build (setBit β i false) rest)
        (build (setBit β i true) rest)

def leavesList (β : Core.Subcube n) : List (Fin n) → List (Core.Subcube n)
  | [] => [β]
  | i :: rest =>
      leavesList (setBit β i false) rest ++
      leavesList (setBit β i true) rest

@[simp] lemma leaves_build (β : Core.Subcube n) (order : List (Fin n)) :
    Core.PDT.leaves (build β order) = leavesList β order := by
  induction order generalizing β with
  | nil =>
      simp [build, leavesList, Core.PDT.leaves]
  | cons i rest ih =>
      simp [build, leavesList, ih, Core.PDT.leaves]

@[simp] lemma depth_build (β : Core.Subcube n) (order : List (Fin n)) :
    Core.PDT.depth (build β order) = order.length := by
  induction order generalizing β with
  | nil =>
      simp [build, Core.PDT.depth]
  | cons i rest ih =>
      simp [build, ih, Core.PDT.depth, List.length_cons]

def full (n : Nat) : Core.PDT n :=
  build (fun _ => none) (List.finRange n)

@[simp] lemma full_depth : Core.PDT.depth (full n) = n := by
  simpa [full] using
    depth_build (β := fun _ => (none : Option Bool))
      (order := List.finRange n)

def follow (β : Core.Subcube n) (x : Core.BitVec n) :
    List (Fin n) → Core.Subcube n
  | [] => β
  | i :: rest =>
      if x i then follow (setBit β i true) x rest
      else follow (setBit β i false) x rest

@[simp] lemma follow_mem (β : Core.Subcube n) (x : Core.BitVec n)
    (order : List (Fin n)) :
    follow β x order ∈ leavesList β order := by
  induction order generalizing β with
  | nil => simp [follow, leavesList]
  | cons i rest ih =>
      by_cases hx : x i
      · simp [follow, leavesList, hx, ih]
      · simp [follow, leavesList, hx, ih]

lemma setBit_preserve_none {β : Core.Subcube n} {i : Fin n}
    {rest : List (Fin n)} (hnot : i ∉ rest)
    (hnone : ∀ j ∈ rest, β j = none) (b : Bool) :
    ∀ j ∈ rest, setBit β i b j = none := by
  intro j hj
  have hne : j ≠ i := by
    intro h; exact hnot (by simpa [h] using hj)
  have := hnone j hj
  simpa [setBit_ne (β := β) (i := i) (j := j) hne (b := b), this]

lemma follow_value (β : Core.Subcube n) (x : Core.BitVec n)
    (order : List (Fin n)) (hnd : order.Nodup)
    (hbase : ∀ j ∈ order, β j = none) :
    ∀ j, follow β x order j =
      if j ∈ order then some (x j) else β j := by
  classical
  induction order generalizing β with
  | nil =>
      intro j; simp [follow]
  | cons i rest ih =>
      have hnot : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hrest := (List.nodup_cons.mp hnd).2
      have hβi : β i = none := hbase i (by simp)
      have hβrest : ∀ j ∈ rest, β j = none := by
        intro j hj; exact hbase j (by simp [hj])
      have hfalse := ih (setBit β i false) hrest
        (setBit_preserve_none (β := β) (i := i) (rest := rest)
          (hnot := hnot) (hnone := hβrest) (b := false))
      have htrue := ih (setBit β i true) hrest
        (setBit_preserve_none (β := β) (i := i) (rest := rest)
          (hnot := hnot) (hnone := hβrest) (b := true))
      intro j
      cases hxi : x i with
      | false =>
          have hcalc := hfalse j
          by_cases hji : j = i
          · subst hji
            have hnot' : j ∉ rest := by simpa using hnot
            have hβj : β j = none := by simpa using hβi
            simp [follow, hxi, hcalc, hβj, hnot', List.mem_cons]
          · by_cases hjrest : j ∈ rest
            · simp [follow, hxi, hcalc, hjrest, List.mem_cons, hji]
            · simp [follow, hxi, hcalc, hjrest, List.mem_cons, hji]
      | true =>
          have hcalc := htrue j
          by_cases hji : j = i
          · subst hji
            have hnot' : j ∉ rest := by simpa using hnot
            have hβj : β j = none := by simpa using hβi
            simp [follow, hxi, hcalc, hβj, hnot', List.mem_cons]
          · by_cases hjrest : j ∈ rest
            · simp [follow, hxi, hcalc, hjrest, List.mem_cons, hji]
            · simp [follow, hxi, hcalc, hjrest, List.mem_cons, hji]

lemma follow_full (x : Core.BitVec n) :
    follow (β := fun _ => (none : Option Bool)) x (List.finRange n)
      = Core.pointSubcube x := by
  funext j
  have hnd := (List.nodup_finRange n)
  have hbase : ∀ k ∈ List.finRange n, (fun _ => (none : Option Bool)) k = none := by
    intro k hk; simp
  have hval := follow_value (β := fun _ => (none : Option Bool))
      (x := x) (order := List.finRange n) hnd hbase j
  have hj : j ∈ List.finRange n := List.mem_finRange j
  have : follow (β := fun _ => (none : Option Bool)) x (List.finRange n) j = some (x j) := by
    simpa [hj] using hval
  simpa [Core.pointSubcube, this]

lemma point_mem_full_leaves (x : Core.BitVec n) :
    Core.pointSubcube x ∈ Core.PDT.leaves (full n) := by
  have hmem := follow_mem (β := fun _ => (none : Option Bool))
      (x := x) (order := List.finRange n)
  have := hmem
  simpa [full, leaves_build, follow_full (n := n) (x := x)]

lemma leavesList_preserve_value
    {b : Bool} (i : Fin n) :
    ∀ {β : Core.Subcube n} {order : List (Fin n)},
      i ∉ order → β i = some b →
        ∀ {βleaf : Core.Subcube n},
          βleaf ∈ leavesList β order →
          βleaf i = some b := by
  classical
  intro β order
  induction order generalizing β with
  | nil =>
      intro _ hβi βleaf hleaf
      have : βleaf = β := by simpa [leavesList] using hleaf
      simpa [this, hβi]
  | cons j rest ih =>
      intro hnot hβi βleaf hleaf
      have hne : j ≠ i := by
        intro hji; apply hnot; simp [hji]
      have hnot' : i ∉ rest := by
        intro hi; apply hnot; simp [hi]
      have hsplit := List.mem_append.mp hleaf
      cases hsplit with
      | inl hleft =>
          have hβi' : (setBit β j false) i = some b := by
            have hneq : i ≠ j := hne.symm
            simpa [setBit, hneq, hβi]
          exact ih (β := setBit β j false) hnot' hβi' hleft
      | inr hright =>
          have hβi' : (setBit β j true) i = some b := by
            have hneq : i ≠ j := hne.symm
            simpa [setBit, hneq, hβi]
          exact ih (β := setBit β j true) hnot' hβi' hright

lemma follow_eq_of_mem_aux :
    ∀ (order : List (Fin n)) (β : Core.Subcube n),
      order.Nodup →
      (∀ j ∈ order, β j = none) →
      ∀ {βleaf : Core.Subcube n},
        βleaf ∈ leavesList β order →
        ∀ {x : Core.BitVec n}, Core.mem βleaf x →
          βleaf = follow β x order := by
  classical
  intro order
  induction order with
  | nil =>
      intro β _ _ βleaf hleaf x _
      have : βleaf = β := by simpa [leavesList] using hleaf
      subst this
      simp [follow]
  | cons i rest ih =>
      intro β hnd hbase βleaf hleaf x hmem
      have hnot : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hβi : β i = none := hbase i (by simp)
      have hβrest : ∀ j ∈ rest, β j = none := by
        intro j hj
        exact hbase j (by simp [hj])
      have hsplit := List.mem_append.mp hleaf
      cases hsplit with
      | inl hleft =>
          have hβleaf_i : βleaf i = some false :=
            leavesList_preserve_value (n := n) (i := i)
              (β := setBit β i false) (order := rest)
              hnot (by simp [setBit]) hleft
          have hxfalse : x i = false := by
            have hprop := (Core.mem_iff (β := βleaf) (x := x)).mp hmem
            have hx := hprop i false hβleaf_i
            simpa using hx
          have hbaseFalse :=
            setBit_preserve_none (β := β) (i := i) (rest := rest)
              (hnot := hnot) (hnone := hβrest) (b := false)
          have hrec :=
            ih (setBit β i false) hrest hbaseFalse
              (βleaf := βleaf) hleft (x := x) hmem
          have hfollow : follow β x (i :: rest)
              = follow (setBit β i false) x rest := by
            simp [follow, hxfalse]
          simpa [hfollow] using hrec
      | inr hright =>
          have hβleaf_i : βleaf i = some true :=
            leavesList_preserve_value (n := n) (i := i)
              (β := setBit β i true) (order := rest)
              hnot (by simp [setBit]) hright
          have hxtrue : x i = true := by
            have hprop := (Core.mem_iff (β := βleaf) (x := x)).mp hmem
            have hx := hprop i true hβleaf_i
            simpa using hx
          have hbaseTrue :=
            setBit_preserve_none (β := β) (i := i) (rest := rest)
              (hnot := hnot) (hnone := hβrest) (b := true)
          have hrec :=
            ih (setBit β i true) hrest hbaseTrue
              (βleaf := βleaf) hright (x := x) hmem
          have hfollow : follow β x (i :: rest)
              = follow (setBit β i true) x rest := by
            simp [follow, hxtrue]
          simpa [hfollow] using hrec

lemma follow_eq_of_mem
    (β : Core.Subcube n) (order : List (Fin n))
    (hnd : order.Nodup)
    (hbase : ∀ j ∈ order, β j = none) :
    ∀ {βleaf : Core.Subcube n},
      βleaf ∈ leavesList β order →
      ∀ {x : Core.BitVec n}, Core.mem βleaf x →
        βleaf = follow β x order :=
  follow_eq_of_mem_aux (n := n) order β hnd hbase

theorem full_wellFormed :
    Core.PDT.WellFormed (full n) := by
  classical
  refine And.intro ?_ ?_
  · intro β γ hβ hγ hne
    intro x hβx hγx
    have hβlist : β ∈ leavesList (fun _ => (none : Option Bool)) (List.finRange n) := by
      simpa [full, leaves_build] using hβ
    have hγlist : γ ∈ leavesList (fun _ => (none : Option Bool)) (List.finRange n) := by
      simpa [full, leaves_build] using hγ
    have hβeq :=
      follow_eq_of_mem (n := n) (β := fun _ => (none : Option Bool))
        (List.finRange n) (List.nodup_finRange n)
        (by intro j hj; simp) hβlist (x := x) hβx
    have hγeq :=
      follow_eq_of_mem (n := n) (β := fun _ => (none : Option Bool))
        (List.finRange n) (List.nodup_finRange n)
        (by intro j hj; simp) hγlist (x := x) hγx
    have hfollow := follow_full (n := n) (x := x)
    have hβpoint : β = Core.pointSubcube x := by
      simpa [full, hfollow] using hβeq
    have hγpoint : γ = Core.pointSubcube x := by
      simpa [full, hfollow] using hγeq
    have : β = γ := by simpa [hβpoint, hγpoint]
    exact (hne this).elim
  · intro x
    refine ⟨Core.pointSubcube x, ?_, ?_⟩
    · exact point_mem_full_leaves (n := n) x
    · exact Core.mem_pointSubcube_self (n := n) x

end DecisionTree

open DecisionTree

section Certificate

variable {n : Nat}

noncomputable def selectorsFor (f : Core.BitVec n → Bool) :
    List (Core.Subcube n) :=
  (((Finset.univ : Finset (Core.BitVec n)).filter
      (fun x => f x = true)).toList.map (fun x => Core.pointSubcube x))

lemma selectors_mem (f : Core.BitVec n → Bool)
    {β : Core.Subcube n} (hβ : β ∈ selectorsFor (n := n) f) :
    ∃ x, f x = true ∧ β = Core.pointSubcube x := by
  classical
  unfold selectorsFor at hβ
  rcases List.mem_map.mp hβ with ⟨x, hx, rfl⟩
  have hxset := Finset.mem_toList.mp hx
  rcases Finset.mem_filter.mp hxset with ⟨_, hxtrue⟩
  exact ⟨x, hxtrue, rfl⟩

lemma selectors_mem_leaves (f : Core.BitVec n → Bool)
    {β : Core.Subcube n} (hβ : β ∈ selectorsFor (n := n) f) :
    β ∈ Core.PDT.leaves (full n) := by
  classical
  rcases selectors_mem (n := n) (f := f) hβ with ⟨x, hxtrue, rfl⟩
  exact point_mem_full_leaves (n := n) x

lemma selectors_contains (f : Core.BitVec n → Bool)
    (x : Core.BitVec n) (hx : f x = true) :
    Core.pointSubcube x ∈ selectorsFor (n := n) f := by
  classical
  unfold selectorsFor
  have hxset : x ∈ ((Finset.univ : Finset (Core.BitVec n)).filter
      fun y => f y = true).toList := by
    apply Finset.mem_toList.mpr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  exact List.mem_map.mpr ⟨x, hxset, rfl⟩

lemma covered_selectors_eq (f : Core.BitVec n → Bool) :
    ∀ x, Core.coveredB (selectorsFor (n := n) f) x = f x := by
  classical
  intro x
  by_cases hx : f x = true
  · have hβ : Core.pointSubcube x ∈ selectorsFor (n := n) f :=
      selectors_contains (n := n) (f := f) x hx
    have hmemB : Core.memB (Core.pointSubcube x) x = true := by
      simpa [Core.mem] using
        (Core.mem_pointSubcube_self (n := n) (x := x))
    have hcov : Core.coveredB (selectorsFor (n := n) f) x = true :=
      List.any_eq_true.mpr ⟨_, hβ, hmemB⟩
    simpa [hx] using hcov
  · have hxfalse : f x = false := by
      cases hval : f x <;> simp [hval] at hx
      simpa [hval]
    have hcov : Core.coveredB (selectorsFor (n := n) f) x = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      rcases List.any_eq_true.mp htrue with ⟨β, hβ, hmemB⟩
      rcases selectors_mem (n := n) (f := f) hβ with ⟨y, hytrue, rfl⟩
      have hyx : y = x := by
        have : Core.mem (Core.pointSubcube y) x := by
          simpa [Core.mem] using hmemB
        simpa using
          (Core.mem_pointSubcube_iff (x := y) (y := x)).1 this
      subst hyx
      exact hx hytrue
    simpa [hxfalse] using hcov

lemma selectors_err_zero (f : Core.BitVec n → Bool) :
    Core.errU f (selectorsFor (n := n) f) = 0 := by
  apply Core.errU_eq_zero_of_agree
  intro x
  simpa using (covered_selectors_eq (n := n) (f := f) x).symm

noncomputable def perfectCertificate (F : Family n) :
    Core.PartialCertificate n 0 F :=
  { witness := Core.PartialDT.ofPDT (full n)
    depthBound := n
    epsilon := 0
    trunk_depth_le := by
      simpa [Core.PartialDT.ofPDT, full_depth]
    selectors := fun f => selectorsFor (n := n) f
    selectors_sub := by
      intro f β hf hβ
      have hmem := selectors_mem_leaves (n := n) (f := f) (β := β) hβ
      simpa [Core.PartialDT.realize_ofPDT, full] using hmem
    err_le := by
      intro f hf
      have herr := selectors_err_zero (n := n) (f := f)
      simpa [herr] }

@[simp] lemma perfectCertificate_depth (F : Family n) :
    (perfectCertificate (n := n) F).depthBound = n := rfl

@[simp] lemma perfectCertificate_epsilon (F : Family n) :
    (perfectCertificate (n := n) F).epsilon = 0 := rfl

end Certificate

end AC0
end Pnp3
