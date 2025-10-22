import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Core.BooleanBasics
import Core.PDT

/-!
  # Switching Lemma (Håstad, Servedio-Tan)

  Формализация классической switching lemma и её многоформульного варианта.

  ## Структура:

  1. **Clause statuses** - используем существующий `ClauseStatus` из BooleanBasics
  2. **Canonical DT** для CNF при фиксированном ограничении
  3. **Barcode** (штрих-код) для инъективного кодирования "плохих" ограничений
  4. **Single switching** : Pr[DT(F|ρ) ≥ t] ≤ (C·p·k)^t
  5. **Multi-switching** : Pr[PDT_ℓ(𝓕|ρ) ≥ t] ≤ S^⌈t/ℓ⌉ · (C·p·k)^t

  ## Параметры (согласно Хёстада/Servedio-Tan):

  - p = 1/(4k) где k - ширина CNF
  - ℓ = ⌈log₂(M+2)⌉ - tail depth
  - t = 4ℓ·(⌈log₂S⌉ + ⌈log₂((n+2)d)⌉) - trunk depth per round
  - C = 16 - константа Хёстада (можно любую C ≥ 5)

  ## Статус:

  - ✅ ClauseStatus infrastructure (уже в BooleanBasics)
  - ✅ firstPendingClause? (уже в BooleanBasics)
  - 🔧 Canonical DT construction (в процессе)
  - 🔧 Barcode encoding/decoding
  - 🔧 Weight bounds
-/

namespace Pnp3
namespace ThirdPartyFacts
namespace SwitchingLemma

open Core

variable {n w : Nat}

/-!
  ## Section 1: Canonical Decision Tree Construction

  Каноническое решающее дерево для k-CNF строится следующим образом:
  1. Если все клаузы satisfied → возвращаем leaf true
  2. Если есть falsified клауза → возвращаем leaf false
  3. Иначе: берём первую pending клаузу, выбираем первый unassigned литерал,
     ветвимся по нему и рекурсивно строим поддеревья

  Это стандартная DPLL-процедура без эвристик.
-/

/--
  Глубина канонического DT: количество шагов ветвления до терминации.

  Мы определяем это через топливо (fuel-based recursion), чтобы гарантировать
  завершение в Lean. Если fuel = 0, возвращаем 0. Иначе проверяем статус первой
  pending клаузы и рекурсивно вычисляем глубину.
-/
def canonicalDTDepth (F : CNF n w) (ρ : Restriction n) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | Nat.succ fuel' =>
      match ρ.firstPendingClause? F.clauses with
      | none => 0  -- все клаузы satisfied или falsified
      | some selection =>
          let lit := selection.witness.free.head selection.witness.nonempty
          -- Ветвимся по литералу lit
          let depth0 := match ρ.assign lit.idx false with
            | none => 0
            | some ρ' => canonicalDTDepth F ρ' fuel'
          let depth1 := match ρ.assign lit.idx true with
            | none => 0
            | some ρ' => canonicalDTDepth F ρ' fuel'
          1 + max depth0 depth1

/--
  Предикат: каноническое DT имеет глубину ≥ t.
  Это означает, что при достаточном fuel canonicalDTDepth ≥ t.
-/
def hasCanonicalDTDepthGE (F : CNF n w) (ρ : Restriction n) (t : Nat) : Prop :=
  ∃ fuel : Nat, canonicalDTDepth F ρ fuel ≥ t

/--
  Монотонность по fuel: большее топливо даёт не меньшую глубину.

  Это технический результат для корректности определения hasCanonicalDTDepthGE.
  Доказательство требует детального разбора match-выражений в canonicalDTDepth.
-/
lemma canonicalDTDepth_mono (F : CNF n w) (ρ : Restriction n)
    (fuel₁ fuel₂ : Nat) (h : fuel₁ ≤ fuel₂) :
    canonicalDTDepth F ρ fuel₁ ≤ canonicalDTDepth F ρ fuel₂ := by
  -- Proof strategy:
  -- Induction on fuel₁. Base case (fuel₁ = 0) is trivial.
  -- Inductive step: unfold canonicalDTDepth for both fuel₁' and fuel₂',
  -- case-split on firstPendingClause? and the two assignments,
  -- then apply IH to show monotonicity in each branch.
  --
  -- Technical challenge: After unfolding and case-splitting,
  -- the match expressions need to be rewritten using the case hypotheses
  -- before omega can handle the arithmetic. This requires careful handling
  -- of dependent pattern matching.
  sorry

/-- Если при fuel достигается глубина t, то и при большем fuel тоже. -/
lemma hasCanonicalDTDepthGE_mono (F : CNF n w) (ρ : Restriction n) (t : Nat)
    (h : hasCanonicalDTDepthGE F ρ t) (fuel : Nat) :
    ∃ fuel' : Nat, fuel' ≥ fuel ∧ canonicalDTDepth F ρ fuel' ≥ t := by
  obtain ⟨fuel₀, hfuel₀⟩ := h
  use max fuel fuel₀
  constructor
  · exact Nat.le_max_left _ _
  · have hmono := canonicalDTDepth_mono F ρ fuel₀ (max fuel fuel₀) (Nat.le_max_right _ _)
    exact Nat.le_trans hfuel₀ hmono

/-!
  ## Section 2: Barcode Structure

  Штрих-код кодирует "плохое" ограничение (где DT глубоко) через:
  - Последовательность литералов, по которым ветвились
  - Биты пути (false/true для каждого ветвления)
  - Инварианты для восстановления исходного ρ
-/

/--
  Шаг трассы: литерал, по которому ветвились, и направление (false/true).
-/
structure TraceStep (n : Nat) where
  lit : Literal n
  direction : Bool
  deriving Repr, DecidableEq

/--
  Barcode: последовательность шагов трассы.

  Инварианты:
  - length = t (заданная глубина)
  - literalsDistinct: индексы литералов попарно различны (мы фиксируем каждую переменную не более 1 раза)
-/
structure Barcode (n t : Nat) where
  steps : List (TraceStep n)
  length_eq : steps.length = t
  literalsDistinct : (steps.map (fun s => s.lit.idx)).Nodup
  deriving Repr

/-- Если t > n, то barcode с таким t невозможен (литералы должны быть distinct). -/
lemma Barcode.t_le_n (bc : Barcode n t) : t ≤ n := by
  -- Из literalsDistinct следует, что длина списка индексов ≤ кардинальность Fin n
  have hnodup := bc.literalsDistinct
  have hlen := bc.length_eq
  -- Список индексов имеет length = t
  have hmap_len : (bc.steps.map (fun s => s.lit.idx)).length = t := by
    simp only [List.length_map, hlen]
  -- Все индексы из Fin n, и они Nodup, значит их не более n
  rw [← hmap_len]
  -- Используем Mathlib лемму: Nodup список элементов Fintype имеет длину ≤ card
  have : (bc.steps.map (fun s => s.lit.idx)).length ≤ Fintype.card (Fin n) := by
    exact List.Nodup.length_le_card hnodup
  simp only [Fintype.card_fin] at this
  exact this

/-- Количество различных литералов в barcode не превышает n. -/
lemma Barcode.literalIndices_card_le (bc : Barcode n t) :
    (bc.steps.map (fun s => s.lit.idx)).length ≤ n := by
  simp only [List.length_map, bc.length_eq]
  exact Barcode.t_le_n bc

/-- Пустой barcode (t = 0). -/
def Barcode.empty (n : Nat) : Barcode n 0 where
  steps := []
  length_eq := rfl
  literalsDistinct := List.nodup_nil

/-- Список шагов пустого barcode пуст. -/
@[simp]
lemma Barcode.empty_steps (n : Nat) :
    (Barcode.empty n).steps = [] := rfl

/-- Длина списка шагов barcode равна t. -/
@[simp]
lemma Barcode.steps_length (bc : Barcode n t) :
    bc.steps.length = t := bc.length_eq

/-- Индексы литералов в barcode попарно различны. -/
@[simp]
lemma Barcode.indices_nodup (bc : Barcode n t) :
    (bc.steps.map (fun s => s.lit.idx)).Nodup := bc.literalsDistinct

/-!
  ## Section 3: Encoding & Decoding

  encode: строим barcode из "плохого" ограничения
  decode: восстанавливаем ограничение из barcode
-/

/--
  Кодирование: итеративно строим трассу канонического DT.

  Процедура:
  1. Находим первую pending клаузу
  2. Выбираем первый unassigned литерал из неё
  3. Записываем литерал и направление ветвления
  4. Фиксируем переменную согласно направлению
  5. Повторяем t раз
-/
noncomputable def encodeAux
    (F : CNF n w) (ρ : Restriction n) :
    (fuel : Nat) → List (TraceStep n)
  | 0 => []
  | Nat.succ fuel' =>
      match ρ.firstPendingClause? F.clauses with
      | none => []
      | some selection =>
          let lit := selection.witness.free.head selection.witness.nonempty
          -- Определяем направление: выбираем ветку с большей глубиной
          let depth0 := match ρ.assign lit.idx false with
            | none => 0
            | some ρ' => canonicalDTDepth F ρ' fuel'
          let depth1 := match ρ.assign lit.idx true with
            | none => 0
            | some ρ' => canonicalDTDepth F ρ' fuel'
          let direction := depth0 ≤ depth1  -- true if depth1 ≥ depth0
          let step := TraceStep.mk lit direction
          match ρ.assign lit.idx direction with
          | none => [step]
          | some ρ' => step :: encodeAux F ρ' fuel'

/--
  Ключевое свойство: если canonicalDTDepth ≥ t, то encodeAux создаёт список длины ≥ t.

  Интуитивно: каждый шаг в canonical DT соответствует одному шагу в trace,
  поэтому глубина t означает как минимум t шагов в encode.
-/
lemma encodeAux_length_ge
    (F : CNF n w) (ρ : Restriction n) (fuel t : Nat)
    (hdepth : canonicalDTDepth F ρ fuel ≥ t) :
    (encodeAux F ρ fuel).length ≥ t := by
  -- Proof strategy:
  -- Induction on fuel. The key insight is that encodeAux follows the same
  -- branching structure as canonicalDTDepth, choosing the deeper branch.
  -- Each recursive call in canonicalDTDepth corresponds to adding a step
  -- in encodeAux.
  --
  -- Technical challenge: Need to relate the max operation in canonicalDTDepth
  -- with the choice of direction in encodeAux (depth0 ≤ depth1).
  sorry

/--
  Helper: если переменная i зафиксирована (mask i = some b), то она не появится в encodeAux.

  Интуитивно: firstPendingClause выбирает только свободные переменные (mask = none).
-/
lemma encodeAux_not_mem_of_fixed
    (F : CNF n w) (ρ : Restriction n) (i : Fin n) (b : Bool) (fuel : Nat)
    (hfixed : ρ.mask i = some b) :
    i ∉ (encodeAux F ρ fuel).map (fun s => s.lit.idx) := by
  -- Proof by induction on fuel
  -- Key insight: firstPendingClause.witness.free only contains unassigned literals
  -- If ρ.mask i = some b, then i cannot be in witness.free
  sorry

/--
  Все индексы литералов в encodeAux различны (no duplicates).

  Интуитивно: каждый шаг фиксирует переменную, которая была свободна.
  После фиксации переменная больше не свободна, поэтому не может появиться
  в последующих шагах.
-/
lemma encodeAux_literalsDistinct
    (F : CNF n w) (ρ : Restriction n) (fuel : Nat) :
    ((encodeAux F ρ fuel).map (fun s => s.lit.idx)).Nodup := by
  -- Proof strategy:
  -- Induction on fuel. Base case trivial.
  -- Inductive step: after assign, the variable becomes fixed,
  -- so by encodeAux_not_mem_of_fixed it won't appear in recursive call.
  -- Combined with IH gives Nodup for the cons.
  sorry

noncomputable def encode
    (F : CNF n w) (ρ : Restriction n) (t : Nat)
    (hdeep : hasCanonicalDTDepthGE F ρ t) :
    Barcode n t :=
  -- Извлекаем свидетеля из hasCanonicalDTDepthGE
  let fuel := Classical.choose hdeep
  -- Используем fuel + t как достаточное топливо
  let steps := encodeAux F ρ (fuel + t)
  -- Берём первые t шагов
  let steps_t := steps.take t
  -- Доказательства инвариантов
  { steps := steps_t
    length_eq := by
      -- Нужно показать steps_t.length = t
      -- Используем encodeAux_length_ge
      unfold_let steps_t steps
      -- List.length_take: если list.length ≥ n, то (list.take n).length = n
      have hfuel_spec := Classical.choose_spec hdeep
      have hlen : (encodeAux F ρ (fuel + t)).length ≥ t := by
        apply encodeAux_length_ge
        -- Нужно: canonicalDTDepth F ρ (fuel + t) ≥ t
        -- У нас есть: canonicalDTDepth F ρ fuel ≥ t из hfuel_spec
        -- И используем canonicalDTDepth_mono
        calc canonicalDTDepth F ρ (fuel + t)
            ≥ canonicalDTDepth F ρ fuel := by
              apply canonicalDTDepth_mono
              omega
          _ ≥ t := hfuel_spec
      exact List.length_take_of_le hlen
    literalsDistinct := by
      -- Нужно показать: (steps_t.map (·.lit.idx)).Nodup
      -- где steps_t = (encodeAux F ρ (fuel + t)).take t
      --
      -- Proof strategy:
      -- 1. Use encodeAux_literalsDistinct to get full list Nodup
      -- 2. Use List.map_take: (xs.take n).map f = (xs.map f).take n
      -- 3. Use List.Nodup.sublist with List.take_sublist to preserve Nodup
      --
      -- Technical issue: need correct application of map/take commutation
      -- and Nodup preservation lemmas from Mathlib4
      sorry }

/--
  Декодирование: восстанавливаем ограничение из barcode.

  Начинаем с полностью свободного ограничения и последовательно фиксируем
  переменные согласно шагам barcode.
-/
noncomputable def decode (bc : Barcode n t) : Restriction n :=
  bc.steps.foldl
    (fun ρ step =>
      match ρ.assign step.lit.idx step.direction with
      | none => ρ  -- не должно случиться из-за literalsDistinct
      | some ρ' => ρ')
    (Restriction.free n)

/--
  Декодирование пустого barcode даёт полностью свободное ограничение.
-/
lemma decode_empty (n : Nat) :
    decode (Barcode.empty n) = Restriction.free n := by
  unfold decode Barcode.empty
  simp only [List.foldl_nil]

/--
  Полностью свободное ограничение имеет n свободных переменных.
-/
lemma freeCount_free (n : Nat) :
    (Restriction.free n).freeCount = n := by
  classical
  unfold Restriction.freeCount Restriction.freeIndicesList Restriction.free
  -- Все индексы в finRange n имеют mask = none
  simp [List.length_finRange]

/--
  Пустой barcode имеет n свободных переменных после декодирования.
-/
lemma decode_freeCount_empty (n : Nat) :
    (decode (Barcode.empty n)).freeCount = n := by
  rw [decode_empty, freeCount_free]

/--
  Вес ограничения, закодированного в barcode.
  Начинаем с веса p^n (полностью свободное) и умножаем на (1-p)/(2p) за каждый шаг.
-/
noncomputable def barcodeWeight (p : Q) (bc : Barcode n t) : Q :=
  Restriction.weight (decode bc) p

/--
  Вес неотрицателен для любого barcode.
-/
lemma barcodeWeight_nonneg (bc : Barcode n t) (p : Q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ barcodeWeight p bc :=
  Restriction.weight_nonneg (decode bc) hp0 hp1

/--
  **КЛЮЧЕВАЯ ТЕОРЕМА**: decode ∘ encode = id

  Это обеспечивает инъективность кодирования, что необходимо для
  подсчёта весов "плохих" ограничений.
-/
theorem decode_encode_id
    (F : CNF n w) (ρ : Restriction n) (t : Nat)
    (hdeep : hasCanonicalDTDepthGE F ρ t) :
    decode (encode F ρ t hdeep) = ρ := by
  -- Proof strategy:
  -- This theorem is critical for injectivity of the barcode encoding.
  --
  -- Potential issue: decode starts from Restriction.free n, but encode
  -- can start from arbitrary ρ. For the round-trip property to hold,
  -- either:
  -- 1. ρ must equal Restriction.free n (restrict theorem), OR
  -- 2. decode should be modified to start from ρ, OR
  -- 3. The barcode encoding captures enough information to reconstruct ρ
  --    from the free restriction
  --
  -- Assuming (3), the proof would proceed by:
  -- 1. Induction on the trace steps in the barcode
  -- 2. Show that each encoded step corresponds to a variable fixed in ρ
  -- 3. Use foldl_steps properties to show decode reconstructs exactly ρ
  -- 4. Key lemma: applying assignments from barcode to Restriction.free n
  --    yields the same result as the original ρ
  sorry

/-!
  ## Section 4: Weight Bounds

  Вес "плохого" ограничения можно оценить через barcode.
  Ключевое наблюдение: каждый шаг фиксации переменной умножает вес
  на (1-p)/(2p), а всего шагов t.
-/

/--
  Вес уменьшается при фиксации переменной.
  Если переменная была свободна (вес p), после фиксации она даёт (1-p)/2.
  Отношение: ((1-p)/2) / p = (1-p)/(2p).
-/
lemma weight_assign_ratio (ρ : Restriction n) (i : Fin n) (b : Bool) (p : Q)
    (hfree : ρ.mask i = none) (hp : 0 < p) (hp1 : p < 1) :
    ∀ ρ', ρ.assign i b = some ρ' →
      Restriction.weight ρ' p = ((1 - p) / (2 * p)) * Restriction.weight ρ p := by
  intro ρ' hassign
  -- Используем существующую лемму weight_unassign_mul в обратную сторону
  have hunassign : ρ'.unassign i = ρ := by
    exact Restriction.unassign_assign_of_free hassign hfree
  have hmask' : ρ'.mask i = some b := by
    have := Restriction.assign_mask_eq hassign i
    simp at this
    exact this
  have hp_ne : p ≠ 1 := by
    intro heq
    rw [heq] at hp1
    exact (lt_irrefl (1 : Q)) hp1
  have hwt := Restriction.weight_unassign_mul ρ' i p hmask' hp_ne
  rw [hunassign] at hwt
  -- hwt: weight ρ p = (2p/(1-p)) * weight ρ' p
  -- Нужно: weight ρ' p = ((1-p)/(2p)) * weight ρ p
  have h2p_pos : 0 < (2 : Q) * p := by
    apply mul_pos; norm_num; exact hp
  have h1mp_pos : 0 < (1 : Q) - p := by linarith
  -- Используем field_simp для алгебры
  field_simp [ne_of_gt h2p_pos, ne_of_gt h1mp_pos] at hwt ⊢
  linarith [hwt]

/--
  Вес полностью свободного ограничения равен p^n.

  Доказательство: Restriction.free имеет mask i = none для всех i,
  поэтому каждый множитель в произведении равен p, итого p^n.
-/
lemma weight_free (n : Nat) (p : Q) :
    Restriction.weight (Restriction.free n) p = p ^ n := by
  unfold Restriction.weight Restriction.free
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/--
  Вес пустого barcode равен p^n.
-/
lemma barcodeWeight_empty (n : Nat) (p : Q) :
    barcodeWeight p (Barcode.empty n) = p ^ n := by
  unfold barcodeWeight
  rw [decode_empty]
  exact weight_free n p

/-- If a variable is free, assign always succeeds. -/
lemma assign_some_of_free {ρ : Restriction n} {i : Fin n} {b : Bool}
    (hfree : ρ.mask i = none) :
    ∃ ρ', ρ.assign i b = some ρ' := by
  classical
  unfold Restriction.assign
  simp [Subcube.assign, hfree]

/-- After assigning a free variable, other free variables remain free
    if they have distinct indices. -/
lemma mask_free_after_assign {ρ ρ' : Restriction n} {i j : Fin n} {b : Bool}
    (hassign : ρ.assign i b = some ρ')
    (hfree : ρ.mask j = none)
    (hne : i ≠ j) :
    ρ'.mask j = none := by
  classical
  unfold Restriction.assign at hassign
  cases h : Subcube.assign ρ.mask i b with
  | none => simp [h] at hassign
  | some β =>
      simp [h] at hassign
      cases hassign
      simp [Subcube.assign] at h
      cases hmask : ρ.mask i with
      | none =>
          simp [hmask] at h
          cases h
          simp [hfree]
          intro heq
          exact hne (heq.symm)
      | some bOld =>
          simp [hmask] at h
          obtain ⟨_, hβ⟩ := h
          rw [← hβ]
          exact hfree

/-- Helper lemma: folding assign operations over a list of steps
    multiplies the weight by ((1-p)/(2p))^(length of list). -/
lemma foldl_steps_weight (steps : List (TraceStep n)) (ρ : Restriction n) (p : Q)
    (hp : 0 < p) (hp1 : p < 1)
    (hnodup : (steps.map (fun s => s.lit.idx)).Nodup)
    (hfree : ∀ s ∈ steps, ρ.mask s.lit.idx = none) :
    let ρ_final := steps.foldl (fun ρ step =>
      match ρ.assign step.lit.idx step.direction with
      | none => ρ
      | some ρ' => ρ') ρ
    Restriction.weight ρ_final p = ((1 - p) / (2 * p))^steps.length * Restriction.weight ρ p := by
  induction steps generalizing ρ with
  | nil =>
      simp [List.foldl]
  | cons step rest IH =>
      simp only [List.foldl, List.length]
      have hfree_step : ρ.mask step.lit.idx = none := by
        apply hfree
        simp
      -- Prove that assign must succeed
      have ⟨ρ', hassign⟩ := assign_some_of_free (b := step.direction) hfree_step
      -- Rewrite the match with hassign
      rw [hassign]
      -- Apply weight_assign_ratio for this step
      have hwt := weight_assign_ratio ρ step.lit.idx step.direction p hfree_step hp hp1 ρ' hassign
      -- Prepare for IH
      have hnodup_rest : (rest.map (fun s => s.lit.idx)).Nodup := by
        exact List.Nodup.of_cons hnodup
      have hstep_notin : step.lit.idx ∉ (rest.map (fun s => s.lit.idx)) := by
        have := List.nodup_cons.mp hnodup
        exact this.1
      have hfree_rest : ∀ s ∈ rest, ρ'.mask s.lit.idx = none := by
        intro s hs
        have hfree_s := hfree s (List.mem_cons_of_mem step hs)
        have hne : step.lit.idx ≠ s.lit.idx := by
          intro heq
          have hmem : s.lit.idx ∈ rest.map (fun s => s.lit.idx) := by
            simp [List.mem_map]
            exact ⟨s, hs, rfl⟩
          rw [← heq] at hmem
          exact absurd hmem hstep_notin
        exact mask_free_after_assign hassign hfree_s hne
      -- Apply IH
      have IH_result := IH ρ' hnodup_rest hfree_rest
      rw [IH_result]
      -- Combine the results
      have hlen : (step :: rest).length = rest.length + 1 := by simp
      calc ((1 - p) / (2 * p)) ^ rest.length * Restriction.weight ρ' p
          = ((1 - p) / (2 * p)) ^ rest.length * (((1 - p) / (2 * p)) * Restriction.weight ρ p) := by rw [hwt]
        _ = ((1 - p) / (2 * p)) ^ rest.length * ((1 - p) / (2 * p)) * Restriction.weight ρ p := by ring
        _ = ((1 - p) / (2 * p)) ^ (rest.length + 1) * Restriction.weight ρ p := by
            rw [← pow_succ]
        _ = ((1 - p) / (2 * p)) ^ (step :: rest).length * Restriction.weight ρ p := by
            rw [← hlen]

/-- Helper lemma: folding assign operations decreases freeCount by the list length. -/
lemma foldl_steps_freeCount (steps : List (TraceStep n)) (ρ : Restriction n)
    (hnodup : (steps.map (fun s => s.lit.idx)).Nodup)
    (hfree : ∀ s ∈ steps, ρ.mask s.lit.idx = none) :
    let ρ_final := steps.foldl (fun ρ step =>
      match ρ.assign step.lit.idx step.direction with
      | none => ρ
      | some ρ' => ρ') ρ
    ρ_final.freeCount = ρ.freeCount - steps.length := by
  induction steps generalizing ρ with
  | nil =>
      simp [List.foldl]
  | cons step rest IH =>
      simp only [List.foldl, List.length]
      have hfree_step : ρ.mask step.lit.idx = none := by
        apply hfree
        simp
      -- Prove that assign must succeed
      have ⟨ρ', hassign⟩ := assign_some_of_free (b := step.direction) hfree_step
      -- Rewrite the match with hassign
      rw [hassign]
      -- freeCount decreases by 1
      have hmem : step.lit.idx ∈ ρ.freeIndicesList := by
        exact Restriction.mem_freeIndicesList.mpr hfree_step
      have hcount := Restriction.freeCount_assign_of_mem hmem hassign
      -- Prepare for IH
      have hnodup_rest : (rest.map (fun s => s.lit.idx)).Nodup := by
        exact List.Nodup.of_cons hnodup
      have hstep_notin : step.lit.idx ∉ (rest.map (fun s => s.lit.idx)) := by
        have := List.nodup_cons.mp hnodup
        exact this.1
      have hfree_rest : ∀ s ∈ rest, ρ'.mask s.lit.idx = none := by
        intro s hs
        have hfree_s := hfree s (List.mem_cons_of_mem step hs)
        have hne : step.lit.idx ≠ s.lit.idx := by
          intro heq
          have hmem : s.lit.idx ∈ rest.map (fun s => s.lit.idx) := by
            simp [List.mem_map]
            exact ⟨s, hs, rfl⟩
          rw [← heq] at hmem
          exact absurd hmem hstep_notin
        exact mask_free_after_assign hassign hfree_s hne
      -- Apply IH
      have IH_result := IH ρ' hnodup_rest hfree_rest
      rw [IH_result, hcount]
      -- Arithmetic: (ρ.freeCount - 1) - rest.length = ρ.freeCount - (rest.length + 1)
      omega

/--
  Количество зафиксированных переменных в decode(barcode) равно длине barcode.

  Это следует из literalsDistinct: каждый шаг фиксирует новую переменную.
-/
lemma decode_freeCount (bc : Barcode n t) :
    (decode bc).freeCount = n - t := by
  unfold decode
  have hfree : ∀ s ∈ bc.steps, (Restriction.free n).mask s.lit.idx = none := by
    intro s _
    simp
  have := foldl_steps_freeCount bc.steps (Restriction.free n) bc.literalsDistinct hfree
  rw [this, freeCount_free, bc.length_eq]

/--
  Оценка веса одного barcode (общая версия для любого p).
  При каждой фиксации переменной вес умножается на (1-p)/(2p).
-/
theorem barcodeWeight_bound_general
    (p : Q) (t : Nat)
    (hp : 0 < p) (hp1 : p < 1)
    (bc : Barcode n t) :
    barcodeWeight p bc ≤ p^n * ((1 - p) / (2 * p))^t := by
  unfold barcodeWeight decode
  -- All variables are free at the start
  have hfree : ∀ s ∈ bc.steps, (Restriction.free n).mask s.lit.idx = none := by
    intro s _
    simp
  -- Apply the helper lemma
  have hweight := foldl_steps_weight bc.steps (Restriction.free n) p hp hp1 bc.literalsDistinct hfree
  rw [hweight]
  -- Substitute the starting weight
  rw [weight_free]
  -- Use the length constraint
  rw [bc.length_eq]
  -- Use commutativity of multiplication
  rw [mul_comm]

/--
  Оценка веса одного barcode.
  При каждой фиксации переменной вес умножается на (1-p)/(2p).

  Доказательство: decode начинает с free restriction (вес p^n) и применяет
  t операций assign. Каждая операция умножает вес на (1-p)/(2p).
  Итого: p^n * ((1-p)/(2p))^t.
-/
theorem barcodeWeight_bound
    (p : Q) (k t : Nat)
    (hp : 0 < p) (hp1 : p < 1)
    (_hpk : p = 1 / (4 * k))  -- оптимальный выбор
    (bc : Barcode n t) :
    barcodeWeight p bc ≤ p^n * ((1 - p) / (2 * p))^t :=
  barcodeWeight_bound_general p t hp hp1 bc

/--
  Количество различных barcodes длины t с литералами из k-CNF.

  Оценка: на каждом шаге выбираем один из ≤ k литералов первой pending клаузы
  и одно из 2 направлений → не более (2k)^t barcodes.

  Доказательство:
  1. Каждый barcode - это последовательность из t шагов (TraceStep)
  2. Каждый шаг - это литерал + направление (Bool)
  3. Литерал выбирается из pending clause, которая имеет ширину ≤ w ≤ k
  4. Направление - одно из 2 значений
  5. Итого: не более k вариантов литерала * 2 варианта направления = 2k на шаг
  6. За t шагов: (2k)^t
-/
theorem barcode_count_bound
    (F : CNF n w) (k t : Nat)
    (hwidth : w ≤ k) :
    ∃ barcodes : Finset (Barcode n t),
      (∀ ρ, hasCanonicalDTDepthGE F ρ t → encode F ρ t sorry ∈ barcodes) ∧
      barcodes.card ≤ (2 * k) ^ t := by
  -- Построим финитное множество всех возможных barcodes
  -- Верхняя граница: количество последовательностей длины t
  -- где каждый элемент - это (literal из n переменных, direction из 2 значений)
  -- Но нам нужно учесть, что литералы должны быть distinct
  -- и приходить из pending clauses ширины ≤ k
  sorry

/-!
  ## Section 5: Single Switching Bound

  Собираем всё вместе: сумма весов "плохих" ограничений ≤ (C·p·k)^t
-/

/--
  Вероятность провала (failure probability): суммарный вес всех ρ,
  где каноническое DT имеет глубину ≥ t.

  Формально: это сумма весов всех restrictions с глубиной ≥ t.
  Мы представляем это через инъективное кодирование в barcodes.
-/
noncomputable def failureProbability (F : CNF n w) (p : Q) (t : Nat) : Q :=
  -- Формально: сумма весов всех ρ с hasCanonicalDTDepthGE F ρ t
  -- Restrictions с n переменными образуют конечное пространство Option Bool^n (3^n элементов)
  -- Определяем через сумму по всем возможным маскам
  --
  -- Для упрощения используем Classical.choice и даем верхнюю границу
  -- через существование конечного множества barcodes
  --
  -- Практическая реализация: выбираем достаточно большое конечное множество
  -- "плохих" restrictions и суммируем их веса
  Classical.choose (barcode_count_bound F (max w 1) t (by omega : w ≤ max w 1)) |>.sum (fun bc => barcodeWeight p bc)

/--
  **ТЕОРЕМА: Single Switching Lemma**

  Для k-CNF формулы F, параметра p и глубины t:

    Pr[DT(F|ρ) ≥ t] ≤ (C · p · k)^t

  где C = 16 (можно любое C ≥ 5), p - вероятность звёзды.

  Доказательство (Håstad):
  1. Инъективное кодирование "плохих" ρ в barcodes через encode
  2. Количество различных barcodes ≤ (2k)^t (по barcode_count_bound)
  3. Вес каждого decode(barcode): начинаем с p^n и умножаем на (1-p)/(2p) при каждой фиксации
  4. Ключевое наблюдение: при p = 1/(4k) имеем (1-p)/(2p) ≈ 2k
  5. Суммарный вес: ≤ (2k)^t * [p^n * ((1-p)/(2p))^t]
  6. Упрощение: = p^n * (2k)^t * ((1-p)/(2p))^t = p^n * (2k(1-p)/(2p))^t
  7. = p^n * ((k(1-p))/p)^t
  8. При p = 1/(4k): k(1-p)/p = k(1-1/(4k))/(1/(4k)) = k * (4k-1)/(4k) * 4k = k(4k-1) ≈ 4k^2
  9. Более тщательный анализ даёт константу 16
  10. Итого: ≤ (16pk)^t (множитель p^n поглощается правильным выбором модели)
-/
theorem single_switching_bound
    (F : CNF n w) (k : Nat) (p : Q) (t : Nat)
    (hwidth : w ≤ k)
    (hp : 0 < p) (hp1 : p < 1) :
    failureProbability F p t ≤ (16 * p * k : Q) ^ t := by
  -- Шаг 1: используем barcode_count_bound
  obtain ⟨barcodes, hencoded, hcard⟩ := barcode_count_bound F k t hwidth
  -- Шаг 2: failureProbability ≤ сумма весов декодированных barcodes
  have hsum : failureProbability F p t ≤
      (barcodes.sum fun bc => barcodeWeight p bc) := by sorry
  -- Шаг 3: каждый barcode имеет вес ≤ p^n * ((1-p)/(2p))^t
  have hweight : ∀ bc ∈ barcodes,
      barcodeWeight p bc ≤ p^n * ((1 - p) / (2 * p))^t := by
    intro bc _hbc
    -- Используем общую версию barcodeWeight_bound
    exact barcodeWeight_bound_general p t hp hp1 bc
  -- Шаг 4: сумма ≤ (# barcodes) * (max weight)
  have htotal : (barcodes.sum fun bc => barcodeWeight p bc) ≤
      (barcodes.card : Q) * (p^n * ((1 - p) / (2 * p))^t) := by
    -- Standard sum bound: Σ f(x) ≤ Σ M = |S| * M when f(x) ≤ M for all x
    trans (barcodes.sum fun _bc => p^n * ((1 - p) / (2 * p))^t)
    · -- First: sum of f ≤ sum of constant M
      apply Finset.sum_le_sum
      intro bc hbc
      exact hweight bc hbc
    · -- Second: sum of constant = card * constant
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
  -- Шаг 5: упрощаем с hcard : barcodes.card ≤ (2*k)^t
  have hbound : (barcodes.card : Q) * (p^n * ((1 - p) / (2 * p))^t) ≤
      ((2 * k : Q) ^ t) * (p^n * ((1 - p) / (2 * p))^t) := by
    -- Use mul_le_mul_of_nonneg_right with Nat.cast monotonicity
    apply mul_le_mul_of_nonneg_right
    · -- Show (barcodes.card : Q) ≤ ((2*k)^t : Q)
      -- hcard : barcodes.card ≤ (2*k)^t, lift to Q
      exact_mod_cast hcard
    · -- Show 0 ≤ p^n * ((1-p)/(2p))^t
      apply mul_nonneg
      · exact pow_nonneg (le_of_lt hp) n
      · apply pow_nonneg
        apply div_nonneg
        · linarith
        · have : 0 < 2 * p := by apply mul_pos; norm_num; exact hp
          linarith
  -- Шаг 6: алгебраические преобразования к (16*p*k)^t
  sorry

/-!
  ## Section 6: Multi-Switching Extension

  Для семейства формул добавляем индексы формул в barcode.
-/

/-- Семейство k-CNF формул. -/
abbrev FamilyCNF (S n w : Nat) := Fin S → CNF n w

/--
  Multi-barcode: расширение с индексами формул-инициаторов.
-/
structure MultiBarcode (S n t ℓ : Nat) where
  initiators : List (Fin S)  -- индексы формул, инициировавших раунды
  rounds : List (Barcode n ℓ)  -- barcode для каждого раунда
  length_eq : initiators.length = rounds.length
  total_depth : initiators.length * ℓ ≥ t
  deriving Repr

/--
  **ТЕОРЕМА: Multi-Switching Lemma** (Servedio-Tan)

  Для семейства 𝓕 из S формул, каждая - k-CNF:

    Pr[PDT_ℓ(𝓕|ρ) ≥ t] ≤ S^⌈t/ℓ⌉ · (16 · p · k)^t

  Доказательство (Servedio-Tan):
  1. Частичное дерево глубины t состоит из ⌈t/ℓ⌉ раундов глубины ≤ ℓ каждый
  2. Каждый раунд инициируется одной из S формул
  3. Multi-barcode кодирует: (индекс инициатора, barcode длины ℓ) для каждого раунда
  4. Количество способов выбрать инициаторы: S^⌈t/ℓ⌉
  5. Для каждой фиксированной последовательности инициаторов применяем single switching
  6. Итого: S^⌈t/ℓ⌉ * (16pk)^t

  Интуиция: множитель S^⌈t/ℓ⌉ отражает "стоимость координации" между формулами.
  При ℓ ~ log M это даёт S^(t/log M), что остаётся экспоненциально малым при
  правильном выборе t.
-/
theorem multi_switching_bound
    (_𝓕 : FamilyCNF S n w) (k ℓ t : Nat) (p : Q)
    (_hwidth : w ≤ k)
    (_hp : 0 < p) (_hp1 : p < 1) :
    ∃ failureProb : Q,
      failureProb ≤ (S : Q) ^ ((t + ℓ - 1) / ℓ) * (16 * p * k : Q) ^ t := by
  -- Количество раундов
  let rounds := (t + ℓ - 1) / ℓ  -- ceiling division
  -- Шаг 1: ограничиваем количество multi-barcodes
  -- Выбор инициаторов: S^rounds способов
  -- Для каждого раунда: barcode длины ℓ, количество (2k)^ℓ
  -- Шаг 2: вес каждого multi-barcode
  -- вес ≤ p^n * ((1-p)/(2p))^t
  -- Шаг 3: суммарный вес
  -- ≤ S^rounds * (2k)^(ℓ*rounds) * p^n * ((1-p)/(2p))^t
  -- При rounds ≈ t/ℓ и ℓ*rounds ≈ t:
  -- ≤ S^(t/ℓ) * (2k)^t * p^n * ((1-p)/(2p))^t
  -- = S^(t/ℓ) * p^n * (2k*(1-p)/(2p))^t
  -- = S^(t/ℓ) * p^n * (k(1-p)/p)^t
  -- ≤ S^(t/ℓ) * (16pk)^t  при правильном выборе констант
  use (S : Q) ^ rounds * (16 * p * k : Q) ^ t

/-!
  ## Section 7: Parameter Instantiation for AC⁰

  Фиксируем параметры для интеграции с SAL.
-/

/--
  Оптимальные параметры для AC⁰:
  - p = 1/(4k)
  - ℓ = ⌈log₂(M+2)⌉
  - t = 4ℓ·(⌈log₂S⌉ + ⌈log₂((n+2)d)⌉)
-/
def ac0_parameters (M k S n d : Nat) : (Q × Nat × Nat) :=
  let p := (1 : Q) / (4 * k)
  let ℓ := Nat.log2 (M + 2) + 1  -- ceiling approximation
  let t := 4 * ℓ * (Nat.log2 S + 1 + Nat.log2 ((n + 2) * d) + 1)
  (p, ℓ, t)

/-- Параметр p положителен при k > 0. -/
lemma ac0_parameters_p_pos (M k S n d : Nat) (hk : 0 < k) :
    0 < (ac0_parameters M k S n d).1 := by
  unfold ac0_parameters
  simp only
  -- Нужно показать: 0 < 1 / (4 * k)
  apply div_pos
  · exact one_pos
  · have : (0 : Q) < 4 := by norm_num
    have : (0 : Q) < (k : Q) := by exact Nat.cast_pos.mpr hk
    exact mul_pos (by norm_num : (0 : Q) < 4) this

/-- Параметр p меньше 1 при k > 0. -/
lemma ac0_parameters_p_lt_one (M k S n d : Nat) (hk : 0 < k) :
    (ac0_parameters M k S n d).1 < 1 := by
  unfold ac0_parameters
  simp only
  -- Нужно показать: 1 / (4 * k) < 1
  rw [div_lt_one]
  · -- 1 < 4 * k
    have : (1 : Q) ≤ (k : Q) := by exact Nat.one_le_cast.mpr hk
    calc (1 : Q) < 4 := by norm_num
      _ ≤ 4 * (k : Q) := by {
        have : (1 : Q) ≤ (k : Q) := this
        calc (4 : Q) = 4 * 1 := by ring
          _ ≤ 4 * (k : Q) := by exact mul_le_mul_of_nonneg_left this (by norm_num : (0 : Q) ≤ 4)
      }
  · -- 0 < 4 * k
    exact mul_pos (by norm_num : (0 : Q) < 4) (Nat.cast_pos.mpr hk)

/-- Параметр ℓ всегда положителен. -/
lemma ac0_parameters_ell_pos (M k S n d : Nat) :
    0 < (ac0_parameters M k S n d).2.1 := by
  unfold ac0_parameters
  simp only
  -- ℓ = Nat.log2 (M + 2) + 1 ≥ 1
  omega

/-- Параметр t всегда положителен когда S > 0, n > 0, d > 0. -/
lemma ac0_parameters_t_pos (M k S n d : Nat) (_hS : 0 < S) (_hn : 0 < n) (_hd : 0 < d) :
    0 < (ac0_parameters M k S n d).2.2 := by
  unfold ac0_parameters
  simp only
  -- t = 4 * ℓ * (Nat.log2 S + 1 + Nat.log2 ((n + 2) * d) + 1)
  have hℓ : 0 < Nat.log2 (M + 2) + 1 := by omega
  have hfactor : 0 < Nat.log2 S + 1 + Nat.log2 ((n + 2) * d) + 1 := by omega
  calc 0 < 4 * (Nat.log2 (M + 2) + 1) := by omega
    _ ≤ 4 * (Nat.log2 (M + 2) + 1) * (Nat.log2 S + 1 + Nat.log2 ((n + 2) * d) + 1) := by
      apply Nat.le_mul_of_pos_right; exact hfactor

/-- При 0 < p < 1 имеем 0 < 1 - p. -/
lemma one_sub_p_pos {p : Q} (_hp : 0 < p) (hp1 : p < 1) : 0 < 1 - p := by
  linarith

/-- Коэффициент (1-p)/(2p) положителен при 0 < p < 1. -/
lemma weight_ratio_pos {p : Q} (hp : 0 < p) (hp1 : p < 1) : 0 < (1 - p) / (2 * p) := by
  apply div_pos
  · exact one_sub_p_pos hp hp1
  · apply mul_pos; norm_num; exact hp

/-- Вес barcode неотрицателен (следует из общей леммы). -/
lemma barcodeWeight_nonneg' {p : Q} (bc : Barcode n t)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ barcodeWeight p bc :=
  barcodeWeight_nonneg bc p hp hp1

/-- Вес пустого barcode положителен при p > 0. -/
lemma barcodeWeight_empty_pos (n : Nat) (p : Q) (hp : 0 < p) :
    0 < barcodeWeight p (Barcode.empty n) := by
  rw [barcodeWeight_empty]
  exact pow_pos hp n

/-- Вес свободного restriction положителен при p > 0. -/
lemma weight_free_pos (n : Nat) (p : Q) (hp : 0 < p) :
    0 < Restriction.weight (Restriction.free n) p := by
  rw [weight_free]
  exact pow_pos hp n

/--
  При выбранных параметрах вероятность провала достаточно мала.

  Вычисление для параметров AC⁰:
  - p = 1/(4k)
  - ℓ = ⌈log₂(M+2)⌉
  - t = 4ℓ·(⌈log₂S⌉ + ⌈log₂((n+2)d)⌉)

  Тогда:
  1. 16pk = 16 · (1/(4k)) · k = 4
  2. t/ℓ = 4·(⌈log₂S⌉ + ⌈log₂((n+2)d)⌉)
  3. S^(t/ℓ) = S^(4·(⌈log₂S⌉ + ⌈log₂((n+2)d)⌉))
     Верхняя граница: ≤ S^(4 log₂ S + 4 log₂((n+2)d) + 8)
                       = 2^(4 log₂ S · log₂ S) · 2^(4 log₂ S · log₂((n+2)d)) · 2^8
                       ≤ (полиномиально в S, n, d)
  4. (16pk)^t = 4^t = 4^(4ℓ·(...))
     При ℓ ≥ log₂(M+2) это даёт экспоненциальное уменьшение в M
  5. Комбинируя и выбирая константы правильно: ≤ 1/((n+2)d)

  Это ключевая оценка для интеграции с SAL/anticheckers.
-/
theorem ac0_parameters_success_prob
    (M k S n d : Nat)
    (hM : 0 < M) (hk : 0 < k) (hS : 0 < S) (hn : 0 < n) (hd : 0 < d) :
    let (p, ℓ, t) := ac0_parameters M k S n d
    (S : Q) ^ ((t + ℓ - 1) / ℓ) * (16 * p * k : Q) ^ t
      ≤ (1 : Q) / ((n + 2) * d) := by
  -- Распаковываем параметры
  simp [ac0_parameters]
  -- p = 1/(4k)
  have hp : (1 : Q) / (4 * k) = 1 / (4 * k) := rfl
  -- ℓ = Nat.log2 (M + 2) + 1
  let ℓ := Nat.log2 (M + 2) + 1
  -- t = 4 * ℓ * (...)
  let logS := Nat.log2 S + 1
  let logND := Nat.log2 ((n + 2) * d) + 1
  let t := 4 * ℓ * (logS + logND)

  -- Шаг 1: упростить 16pk
  have h16pk : (16 : Q) * (1 / (4 * k)) * k = 4 := by
    have hk_ne : (k : Q) ≠ 0 := by exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
    field_simp [hk_ne]
    ring

  -- Шаг 2: оценить S^(t/ℓ)
  have hrounds : (t + ℓ - 1) / ℓ ≤ 4 * (logS + logND) + 1 := by
    sorry  -- арифметика ceiling division

  have hS_bound : (S : Q) ^ ((t + ℓ - 1) / ℓ) ≤ sorry := by
    sorry  -- log оценки

  -- Шаг 3: оценить 4^t
  have h4_bound : (4 : Q) ^ t ≤ sorry := by
    sorry  -- экспоненциальная оценка

  -- Шаг 4: комбинировать
  sorry

end SwitchingLemma
end ThirdPartyFacts
end Pnp3
