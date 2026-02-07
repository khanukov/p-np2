import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.CanonicalTrace

/-!
  pnp3/AC0/MultiSwitching/CanonicalDT.lean

  Канонические DT/CCDT в виде `PDT` и базовые инварианты.
  Здесь мы реализуем детерминированный (но грубый) вариант канонического
  дерева решений для CNF, используя правило "первая pending‑клауза и первый
  свободный литерал". Это даёт честный `PDT` и предсказуемые верхние оценки
  на глубину.

  Важно: это *инженерный* вариант канонического дерева. Он не заявляет
  оптимальности, но достаточно структурирован, чтобы служить опорой
  для дальнейшего proof-by-encoding.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-!
### Выбор первого свободного литерала

Для любой pending‑клаузы можно выбрать первый свободный литерал из списка `w.free`.
Это детерминизирует построение канонического дерева.
-/

noncomputable def chooseFreeLiteral
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) : Literal n :=
  Classical.choose (List.exists_cons_of_ne_nil w.nonempty)

lemma chooseFreeLiteral_mem
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) :
    chooseFreeLiteral (w := w) ∈ w.free := by
  classical
  rcases Classical.choose_spec (List.exists_cons_of_ne_nil w.nonempty) with ⟨tail, hspec⟩
  -- Подставляем описание списка `w.free` из `choose_spec`.
  have hmem :
      chooseFreeLiteral (w := w) ∈ chooseFreeLiteral (w := w) :: tail := by
    exact List.mem_cons_self (a := chooseFreeLiteral (w := w)) (l := tail)
  rw [hspec]
  exact hmem

/-!
### Каноническое DT для CNF

`canonicalDT_CNF_aux` строится по топ‑даун правилу:
* если нет pending‑клаузы, возвращаем лист;
* иначе выбираем первый свободный литерал и ветвимся по его значению.
-/

noncomputable def canonicalDT_CNF_aux
    {n w : Nat} (F : CNF n w) :
    Nat → Restriction n → PDT n
  | 0, ρ => PDT.leaf ρ.mask
  | Nat.succ fuel, ρ =>
      match Restriction.firstPendingClause? ρ F.clauses with
      | none => PDT.leaf ρ.mask
      | some selection =>
          let ℓ := chooseFreeLiteral (w := selection.witness)
          have hmem : ℓ ∈ selection.witness.free :=
            chooseFreeLiteral_mem (w := selection.witness)
          have hfree :
              ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
          -- обе ветви назначают значение переменной `ℓ.idx`.
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          PDT.node ℓ.idx
            (canonicalDT_CNF_aux F fuel ρ0)
            (canonicalDT_CNF_aux F fuel ρ1)

/-!
#### Корректность ветвления (CNF)

Проверяем два ключевых факта:
* выбранный литерал действительно свободен;
* присваивание уменьшает число свободных координат ровно на единицу.

Эти леммы используются как «санити‑чеки» для дальнейших оценок глубины и
согласования с `freeCount`.
-/

lemma canonicalDT_CNF_aux_branch_freeCount
    {n w : Nat} {F : CNF n w} {_fuel : Nat} {ρ : Restriction n}
    {selection : Restriction.PendingClauseSelection (ρ := ρ) F.clauses}
    (_hsel : Restriction.firstPendingClause? ρ F.clauses = some selection) :
    let ℓ := chooseFreeLiteral (w := selection.witness)
    let hmem : ℓ ∈ selection.witness.free :=
      chooseFreeLiteral_mem (w := selection.witness)
    let hfree :
        ℓ.idx ∈ ρ.freeIndicesList :=
      Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
        (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
    let ρ0 := Classical.choose
      (Restriction.assign_some_of_mem_freeIndicesList
        (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
    let ρ1 := Classical.choose
      (Restriction.assign_some_of_mem_freeIndicesList
        (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
    ρ0.freeCount = ρ.freeCount - 1 ∧ ρ1.freeCount = ρ.freeCount - 1 := by
  classical
  intro ℓ hmem hfree ρ0 ρ1
  -- Получаем факт о присваивании из конструктора `assign_some_of_mem_freeIndicesList`.
  have hassign0 :
      ρ.assign ℓ.idx false = some ρ0 := by
    simpa [ρ0] using
      (Classical.choose_spec
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
  have hassign1 :
      ρ.assign ℓ.idx true = some ρ1 := by
    simpa [ρ1] using
      (Classical.choose_spec
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
  have hcount0 :=
    Restriction.freeCount_assign_of_mem
      (ρ := ρ) (i := ℓ.idx) (b := false) (ρ' := ρ0) hfree hassign0
  have hcount1 :=
    Restriction.freeCount_assign_of_mem
      (ρ := ρ) (i := ℓ.idx) (b := true) (ρ' := ρ1) hfree hassign1
  exact ⟨hcount0, hcount1⟩

/-- Каноническое DT с «естественным» запасом топлива `ρ.freeCount`. -/
noncomputable def canonicalDT_CNF
    {n w : Nat} (F : CNF n w) (ρ : Restriction n) : PDT n :=
  canonicalDT_CNF_aux F ρ.freeCount ρ

/-- Глубина `canonicalDT_CNF_aux` не превосходит топлива. -/
lemma canonicalDT_CNF_aux_depth_le
    {n w : Nat} (F : CNF n w) :
    ∀ fuel ρ, PDT.depth (canonicalDT_CNF_aux F fuel ρ) ≤ fuel
  | 0, ρ => by
      simp [canonicalDT_CNF_aux, PDT.depth]
  | Nat.succ fuel, ρ => by
      classical
      cases hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          simp [canonicalDT_CNF_aux, hsel, PDT.depth]
      | some selection =>
          let ℓ := chooseFreeLiteral (w := selection.witness)
          have hmem : ℓ ∈ selection.witness.free :=
            chooseFreeLiteral_mem (w := selection.witness)
          have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          have h0 : PDT.depth (canonicalDT_CNF_aux F fuel ρ0) ≤ fuel := by
            simpa [ρ0] using
              canonicalDT_CNF_aux_depth_le (F := F) (fuel := fuel) (ρ := ρ0)
          have h1 : PDT.depth (canonicalDT_CNF_aux F fuel ρ1) ≤ fuel := by
            simpa [ρ1] using
              canonicalDT_CNF_aux_depth_le (F := F) (fuel := fuel) (ρ := ρ1)
          have hmax :
              Nat.max (PDT.depth (canonicalDT_CNF_aux F fuel ρ0))
                (PDT.depth (canonicalDT_CNF_aux F fuel ρ1)) ≤ fuel := by
            exact (max_le_iff).2 ⟨h0, h1⟩
          have hsucc :
              Nat.succ (Nat.max (PDT.depth (canonicalDT_CNF_aux F fuel ρ0))
                (PDT.depth (canonicalDT_CNF_aux F fuel ρ1)))
                ≤ Nat.succ fuel := Nat.succ_le_succ hmax
          have hdepth :
              PDT.depth (canonicalDT_CNF_aux F (Nat.succ fuel) ρ) =
                Nat.succ (Nat.max (PDT.depth (canonicalDT_CNF_aux F fuel ρ0))
                  (PDT.depth (canonicalDT_CNF_aux F fuel ρ1))) := by
            simp [canonicalDT_CNF_aux, hsel, PDT.depth, ℓ, ρ0, ρ1]
          simpa [hdepth] using hsucc

lemma canonicalDT_CNF_depth_le
    {n w : Nat} (F : CNF n w) (ρ : Restriction n) :
    PDT.depth (canonicalDT_CNF F ρ) ≤ ρ.freeCount := by
  simpa [canonicalDT_CNF] using
    canonicalDT_CNF_aux_depth_le (F := F) (fuel := ρ.freeCount) (ρ := ρ)

lemma canonicalDT_CNF_aux_depth_monotone_fuel
    {n w : Nat} (F : CNF n w) (ρ : Restriction n) :
    ∀ {fuel1 fuel2 : Nat}, fuel1 ≤ fuel2 →
      PDT.depth (canonicalDT_CNF_aux F fuel1 ρ) ≤
      PDT.depth (canonicalDT_CNF_aux F fuel2 ρ) := by
  intro fuel1 fuel2 hle
  induction fuel2 generalizing fuel1 ρ with
  | zero =>
      have h0 : fuel1 = 0 := Nat.eq_zero_of_le_zero hle
      simp [h0]
  | succ fuel2 ih =>
      cases fuel1 with
      | zero =>
          simp [canonicalDT_CNF_aux, PDT.depth]
      | succ fuel1 =>
          -- Both > 0.
          have hle' : fuel1 ≤ fuel2 := Nat.le_of_succ_le_succ hle
          unfold canonicalDT_CNF_aux
          cases hsel : Restriction.firstPendingClause? ρ F.clauses with
          | none =>
              simp
          | some selection =>
              classical
              let ℓ := chooseFreeLiteral (w := selection.witness)
              have hmem : ℓ ∈ selection.witness.free :=
                chooseFreeLiteral_mem (w := selection.witness)
              have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
                Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
              let ρ0 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
              let ρ1 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
              have h0 : PDT.depth (canonicalDT_CNF_aux F fuel1 ρ0) ≤
                        PDT.depth (canonicalDT_CNF_aux F fuel2 ρ0) :=
                  ih ρ0 hle'
              have h1 : PDT.depth (canonicalDT_CNF_aux F fuel1 ρ1) ≤
                        PDT.depth (canonicalDT_CNF_aux F fuel2 ρ1) :=
                  ih ρ1 hle'
              simp only [PDT.depth]
              apply Nat.succ_le_succ
              apply max_le
              · exact Nat.le_trans h0 (Nat.le_max_left _ _)
              · exact Nat.le_trans h1 (Nat.le_max_right _ _)

/-!
### Каноническое DT для DNF (симметрия CNF)

Мы выбираем **первый** терм, который не фальсифицирован ограничением.
Если свободных литералов нет, формула постоянна на данной ветви (либо true,
либо false), и мы возвращаем лист. Иначе ветвимся по первому свободному
литералу терма.
-/

def termFalsified {n : Nat} (ρ : Restriction n) (T : DnfTerm n) : Prop :=
  ∃ ℓ ∈ T.literals, ρ.literalStatus ℓ = LiteralStatus.falsified

noncomputable def firstLiveTerm? {n : Nat} (ρ : Restriction n) :
    List (DnfTerm n) → Option (DnfTerm n)
  | [] => none
  | T :: rest =>
      by
        classical
        exact if termFalsified ρ T then firstLiveTerm? (ρ := ρ) rest else some T

noncomputable def chooseFirstLiteral
    {n : Nat} {free : List (Literal n)} (hfree : free ≠ []) : Literal n :=
  Classical.choose (List.exists_cons_of_ne_nil hfree)

lemma chooseFirstLiteral_mem
    {n : Nat} {free : List (Literal n)} (hfree : free ≠ []) :
    chooseFirstLiteral (free := free) hfree ∈ free := by
  classical
  rcases Classical.choose_spec (List.exists_cons_of_ne_nil hfree) with ⟨tail, hspec⟩
  have hmem :
      chooseFirstLiteral (free := free) hfree ∈
        chooseFirstLiteral (free := free) hfree :: tail := by
    exact List.mem_cons_self (a := chooseFirstLiteral (free := free) hfree) (l := tail)
  have hspec' :
      (chooseFirstLiteral (free := free) hfree ∈ free)
        = (chooseFirstLiteral (free := free) hfree ∈
          chooseFirstLiteral (free := free) hfree :: tail) :=
    congrArg (fun l => chooseFirstLiteral (free := free) hfree ∈ l) hspec
  exact Eq.mp hspec'.symm hmem

noncomputable def canonicalDT_DNF_aux
    {n w : Nat} (F : DNF n w) :
    Nat → Restriction n → PDT n
  | 0, ρ => PDT.leaf ρ.mask
  | Nat.succ fuel, ρ =>
      match firstLiveTerm? ρ F.terms with
      | none => PDT.leaf ρ.mask
      | some T =>
          let free := ρ.freeLiterals T
          if hfree : free = [] then
            PDT.leaf ρ.mask
          else
            let ℓ := chooseFirstLiteral (free := free) hfree
            have hmem : ℓ ∈ free :=
              chooseFirstLiteral_mem (free := free) hfree
            have hstatus : ρ.literalStatus ℓ = LiteralStatus.unassigned := by
              exact (Restriction.mem_freeLiterals (ρ := ρ) (C := T) (ℓ := ℓ)).1 hmem |>.2
            have hmask : ρ.mask ℓ.idx = none := by
              exact (Restriction.literalStatus_eq_unassigned (ρ := ρ) (ℓ := ℓ)).1 hstatus
            have hfreeIdx : ℓ.idx ∈ ρ.freeIndicesList := by
              exact (Restriction.mem_freeIndicesList (ρ := ρ) (i := ℓ.idx)).2 hmask
            let ρ0 := Classical.choose
              (Restriction.assign_some_of_mem_freeIndicesList
                (ρ := ρ) (i := ℓ.idx) (b := false) hfreeIdx)
            let ρ1 := Classical.choose
              (Restriction.assign_some_of_mem_freeIndicesList
                (ρ := ρ) (i := ℓ.idx) (b := true) hfreeIdx)
            PDT.node ℓ.idx
              (canonicalDT_DNF_aux F fuel ρ0)
              (canonicalDT_DNF_aux F fuel ρ1)

/-!
#### Корректность ветвления (DNF)

Если литерал свободен, то присваивание корректно и снова уменьшает число
свободных координат на 1. Эта лемма нужна, чтобы согласовать выбор литерала
с оценками глубины и подсчётом подкубов.
-/

lemma canonicalDT_DNF_aux_branch_freeCount
    {n w : Nat} {_F : DNF n w} {_fuel : Nat} {ρ : Restriction n}
    {T : DnfTerm n} {free : List (Literal n)} (hfree : free ≠ [])
    (hfreeEq : free = ρ.freeLiterals T) :
    let ℓ := chooseFirstLiteral (free := free) hfree
    let hmem : ℓ ∈ free := chooseFirstLiteral_mem (free := free) hfree
    let hstatus : ρ.literalStatus ℓ = LiteralStatus.unassigned :=
      (Restriction.mem_freeLiterals (ρ := ρ) (C := T) (ℓ := ℓ)).1
        (by simpa [hfreeEq] using hmem) |>.2
    let hmask : ρ.mask ℓ.idx = none :=
      (Restriction.literalStatus_eq_unassigned (ρ := ρ) (ℓ := ℓ)).1 hstatus
    let hfreeIdx : ℓ.idx ∈ ρ.freeIndicesList :=
      (Restriction.mem_freeIndicesList (ρ := ρ) (i := ℓ.idx)).2 hmask
    let ρ0 := Classical.choose
      (Restriction.assign_some_of_mem_freeIndicesList
        (ρ := ρ) (i := ℓ.idx) (b := false) hfreeIdx)
    let ρ1 := Classical.choose
      (Restriction.assign_some_of_mem_freeIndicesList
        (ρ := ρ) (i := ℓ.idx) (b := true) hfreeIdx)
    ρ0.freeCount = ρ.freeCount - 1 ∧ ρ1.freeCount = ρ.freeCount - 1 := by
  classical
  intro ℓ hmem hstatus hmask hfreeIdx ρ0 ρ1
  have hassign0 :
      ρ.assign ℓ.idx false = some ρ0 := by
    simpa [ρ0] using
      (Classical.choose_spec
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := false) hfreeIdx))
  have hassign1 :
      ρ.assign ℓ.idx true = some ρ1 := by
    simpa [ρ1] using
      (Classical.choose_spec
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := true) hfreeIdx))
  have hcount0 :=
    Restriction.freeCount_assign_of_mem
      (ρ := ρ) (i := ℓ.idx) (b := false) (ρ' := ρ0) hfreeIdx hassign0
  have hcount1 :=
    Restriction.freeCount_assign_of_mem
      (ρ := ρ) (i := ℓ.idx) (b := true) (ρ' := ρ1) hfreeIdx hassign1
  exact ⟨hcount0, hcount1⟩

noncomputable def canonicalDT_DNF
    {n w : Nat} (F : DNF n w) (ρ : Restriction n) : PDT n :=
  canonicalDT_DNF_aux F ρ.freeCount ρ

lemma canonicalDT_DNF_aux_depth_le
    {n w : Nat} (F : DNF n w) :
    ∀ fuel ρ, PDT.depth (canonicalDT_DNF_aux F fuel ρ) ≤ fuel
  | 0, ρ => by
      simp [canonicalDT_DNF_aux, PDT.depth]
  | Nat.succ fuel, ρ => by
      classical
      cases hterm : firstLiveTerm? ρ F.terms with
      | none =>
          simp [canonicalDT_DNF_aux, hterm, PDT.depth]
      | some T =>
          cases hfreeList : ρ.freeLiterals T with
          | nil =>
              have hfree : ρ.freeLiterals T = [] := hfreeList
              simp [canonicalDT_DNF_aux, hterm, hfree, PDT.depth, -Restriction.freeLiterals]
          | cons ℓ freeTail =>
              have hfree : ρ.freeLiterals T ≠ [] := by
                intro hnil
                have : (ℓ :: freeTail) = [] := by
                  exact hfreeList ▸ hnil
                cases this
              let ℓ := chooseFirstLiteral (free := ρ.freeLiterals T) hfree
              have hmem : ℓ ∈ ρ.freeLiterals T :=
                chooseFirstLiteral_mem (free := ρ.freeLiterals T) hfree
              have hstatus : ρ.literalStatus ℓ = LiteralStatus.unassigned := by
                exact (Restriction.mem_freeLiterals (ρ := ρ) (C := T) (ℓ := ℓ)).1 hmem |>.2
              have hmask : ρ.mask ℓ.idx = none := by
                exact (Restriction.literalStatus_eq_unassigned (ρ := ρ) (ℓ := ℓ)).1 hstatus
              have hfreeIdx : ℓ.idx ∈ ρ.freeIndicesList := by
                exact (Restriction.mem_freeIndicesList (ρ := ρ) (i := ℓ.idx)).2 hmask
              let ρ0 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfreeIdx)
              let ρ1 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfreeIdx)
              have h0 : PDT.depth (canonicalDT_DNF_aux F fuel ρ0) ≤ fuel := by
                simpa [ρ0] using
                  canonicalDT_DNF_aux_depth_le (F := F) (fuel := fuel) (ρ := ρ0)
              have h1 : PDT.depth (canonicalDT_DNF_aux F fuel ρ1) ≤ fuel := by
                simpa [ρ1] using
                  canonicalDT_DNF_aux_depth_le (F := F) (fuel := fuel) (ρ := ρ1)
              have hmax :
                  Nat.max (PDT.depth (canonicalDT_DNF_aux F fuel ρ0))
                    (PDT.depth (canonicalDT_DNF_aux F fuel ρ1)) ≤ fuel := by
                exact (max_le_iff).2 ⟨h0, h1⟩
              have hsucc :
                  Nat.succ (Nat.max (PDT.depth (canonicalDT_DNF_aux F fuel ρ0))
                    (PDT.depth (canonicalDT_DNF_aux F fuel ρ1)))
                    ≤ Nat.succ fuel := Nat.succ_le_succ hmax
              have hdepth :
                  PDT.depth (canonicalDT_DNF_aux F (Nat.succ fuel) ρ) =
                    Nat.succ (Nat.max (PDT.depth (canonicalDT_DNF_aux F fuel ρ0))
                      (PDT.depth (canonicalDT_DNF_aux F fuel ρ1))) := by
                simp [canonicalDT_DNF_aux, hterm, hfree, PDT.depth, ℓ, ρ0, ρ1,
                  -Restriction.freeLiterals]
              simpa [hdepth] using hsucc

lemma canonicalDT_DNF_depth_le
    {n w : Nat} (F : DNF n w) (ρ : Restriction n) :
    PDT.depth (canonicalDT_DNF F ρ) ≤ ρ.freeCount := by
  simpa [canonicalDT_DNF] using
    canonicalDT_DNF_aux_depth_le (F := F) (fuel := ρ.freeCount) (ρ := ρ)

/-!
### Каноническое CCDT для последовательности CNF

Мы строим дерево для первой формулы и раскрываем его листья по рекурсивному
правилу для хвоста. Глубина оценивается сверху как `fuel * length`.
-/

noncomputable def canonicalCCDT_CNF_aux
    {n w : Nat} :
    List (CNF n w) → Nat → Restriction n → PDT n
  | [], _fuel, ρ => PDT.leaf ρ.mask
  | F :: rest, fuel, ρ =>
      let trunk := canonicalDT_CNF_aux F fuel ρ
      let tails : ∀ β, β ∈ PDT.leaves trunk → PDT n :=
        fun β _ => canonicalCCDT_CNF_aux rest fuel ⟨β⟩
      PDT.refine trunk tails

lemma canonicalCCDT_CNF_aux_depth_le
    {n w : Nat} :
    ∀ (Fs : List (CNF n w)) (fuel : Nat) (ρ : Restriction n),
      PDT.depth (canonicalCCDT_CNF_aux Fs fuel ρ) ≤ fuel * Fs.length
  | [], fuel, ρ => by
      simp [canonicalCCDT_CNF_aux, PDT.depth]
  | F :: rest, fuel, ρ => by
      classical
      -- depth(refine) ≤ depth(trunk) + depth(tails)
      have htrunk : PDT.depth (canonicalDT_CNF_aux F fuel ρ) ≤ fuel := by
        exact canonicalDT_CNF_aux_depth_le (F := F) (fuel := fuel) (ρ := ρ)
      have htail :
          ∀ (β : Subcube n) (hβ : β ∈ PDT.leaves (canonicalDT_CNF_aux F fuel ρ)),
            PDT.depth (canonicalCCDT_CNF_aux rest fuel ⟨β⟩) ≤ fuel * rest.length := by
        intro β hβ
        exact canonicalCCDT_CNF_aux_depth_le (Fs := rest) (fuel := fuel) (ρ := ⟨β⟩)
      have hrefine :=
        PDT.depth_refine_le (t := canonicalDT_CNF_aux F fuel ρ)
          (tails := fun β hβ => canonicalCCDT_CNF_aux rest fuel ⟨β⟩)
          (ℓ := fuel * rest.length) htail
      -- складываем оценку: depth(trunk) + fuel*rest.length ≤ fuel*(rest.length+1)
      have hsum :
          PDT.depth (canonicalDT_CNF_aux F fuel ρ) + fuel * rest.length
            ≤ fuel * (rest.length + 1) := by
        -- подставляем `htrunk` и раскрываем умножение на сумму
        calc
          PDT.depth (canonicalDT_CNF_aux F fuel ρ) + fuel * rest.length
              ≤ fuel + fuel * rest.length := by
                    exact Nat.add_le_add_right htrunk _
          _ = fuel * rest.length + fuel := by
                simp [Nat.add_comm]
          _ = fuel * (rest.length + 1) := by
                simp [Nat.mul_add]
      -- собираем итоговую оценку
      exact Nat.le_trans hrefine hsum

/-!
#### Согласование CCDT с `freeCount`

Если использовать естественное топливо `ρ.freeCount`, глубина CCDT не
превышает `ρ.freeCount * length`. Это важная оценка для последующих
`BadEvent`‑подсчётов.
-/

lemma canonicalCCDT_CNF_depth_le
    {n w : Nat} (Fs : List (CNF n w)) (ρ : Restriction n) :
    PDT.depth (canonicalCCDT_CNF_aux Fs ρ.freeCount ρ)
      ≤ ρ.freeCount * Fs.length := by
  simpa using
    canonicalCCDT_CNF_aux_depth_le (Fs := Fs) (fuel := ρ.freeCount) (ρ := ρ)

end MultiSwitching
end AC0
end Pnp3
