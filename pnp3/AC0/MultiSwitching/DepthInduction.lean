import AC0.MultiSwitching.Trace
import Mathlib.Data.List.MinMax

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
  have hnil : levels.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [levels.toList_length]
  simp [totalSteps, hnil]

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
  have hnil : levels.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [levels.toList_length]
  simp [maxSteps, hnil]

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
      rw [Nat.pow_succ]
      simp [Nat.mul_comm]

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
