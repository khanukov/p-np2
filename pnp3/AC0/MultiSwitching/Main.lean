import AC0.MultiSwitching.Encoding
import AC0.MultiSwitching.Trace
import AC0.MultiSwitching.Counting
import AC0.MultiSwitching.Numerics
import AC0.MultiSwitching.Params

/-!
  pnp3/AC0/MultiSwitching/Main.lean

  Центральная точка входа для будущего multi-switching доказательства.

  Сейчас здесь собраны только "комбинаторные" шаги:
  как из encoding получить существование хорошей рестрикции.
  Реальное построение CCDT и глубинная индукция будут добавлены поверх
  этих лемм в следующих итерациях.

  TODO (bridge):
  определить здесь теорему, которую затем будет использовать
  `ThirdPartyFacts.Facts_Switching.ac0AllSubcubes_length_le_polylog_of_multi_switching`.
  Эта теорема должна выдавать polylog‑оценку на `ac0AllSubcubes` на основе
  полного multi‑switching доказательства (CCDT + encoding/injection + counting).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n k ℓ t : Nat} {F : FormulaFamily n k}

/-!
### Существование хорошей рестрикции

Это минимальный шаг "counting → ∃".  Он будет использоваться
после построения реального encoding/injection.
-/

lemma exists_good_restriction_of_aux_encoding_main
    (A : CCDTAlgorithm n k ℓ t F) (s t' k' m : Nat)
    (witness :
      EncodingWitness (A := A) (s := s)
        (codes := (R_s (n := n) t').product (auxCodes n t k' m)))
    (hcodes :
      (R_s (n := n) t').card * (2 * n * k' * m) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadEvent (A := A) ρ := by
  exact exists_good_restriction_of_aux_encoding
    (A := A) (s := s) (t' := t') (k' := k') (m := m) witness hcodes

/-!
## Числовая оценка для большого `n`

`numerical_inequality_3_2` формулируется в терминах базового алфавита
`BParam` и даёт строгое неравенство с дополнительным множителем
`(n - s + 1)^t` в правой части.  Мы фиксируем эту оценку как отдельную
лемму‑обёртку, чтобы в дальнейшем было проще явно состыковать её с
кодами из `Counting.lean` (см. комментарий в proof ниже).
-/

lemma numerical_bound_step3_2
    {n w m : Nat}
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam m n ≤ sParam n w) :
    (R_s (n := n) (sParam n w - tParam m n)).card * (m + 1)
        * (BParam w) ^ (tParam m n)
      < (R_s (n := n) (sParam n w)).card := by
  exact numerical_inequality_3_2_final (n := n) (w := w) (m := m) hN ht

/-!
## Wrapper: Step 3.2 (CNF family)

Мы выполняем разбиение по размеру `n`:

* **малый `n`**: `sParam = 0`, тогда `BadFamily` невозможен при `t > 0`;
* **большой `n`**: используем `numerical_inequality_3_2` и counting‑лемму.
-/

theorem exists_good_restriction_step3_2
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (ht : tParam m n ≤ sParam n w)
    (hbound_counting :
      (R_s (n := n) (sParam n w - tParam m n)).card
          * (F.length + 1) * (2 * n) ^ (tParam m n)
          * (2 * (w + 1)) ^ (tParam m n)
        < (R_s (n := n) (sParam n w)).card) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ¬ BadFamily_deterministic (F := F) (tParam m n) ρ := by
  classical
  by_cases hN : 49 * (w + 1) ≤ n
  · -- Большая `n`: используем числовую оценку.
    -- Числовая оценка для Step 3.2 в финальной форме `< |R_s|`.
    have _hnumeric :
        (R_s (n := n) (sParam n w - tParam m n)).card * (m + 1)
            * (BParam w) ^ (tParam m n)
          < (R_s (n := n) (sParam n w)).card := by
      exact numerical_bound_step3_2 (n := n) (w := w) (m := m) hN ht
    -- Используем детерминированный вариант counting‑леммы с расширенным кодом.
    exact exists_good_restriction_cnf_family_of_bound_det_var (F := F)
      (s := sParam n w) (t := tParam m n) hbound_counting
  · -- Малое `n`: `sParam = 0`, плохая трасса невозможна.
    have hs : sParam n w = 0 := sParam_eq_zero_of_lt (n := n) (w := w)
      (by
        have hlt : n < 49 * (w + 1) := lt_of_not_ge hN
        exact hlt)
    -- Возьмём произвольную рестрикцию из `R_s` с `s=0`.
    have hnonempty : (R_s (n := n) 0).Nonempty := by
      -- `R_s` непусто при `0 ≤ n`.
      exact R_s_nonempty (n := n) (s := 0) (by omega)
    rcases hnonempty with ⟨ρ, hρ⟩
    refine ⟨ρ, ?_, ?_⟩
    · simpa [hs] using hρ
    · intro hbad
      -- Переходим к недетерминированному `BadFamily` и применяем старую лемму.
      have hbad' :
          BadFamily (F := F) (tParam m n) ρ :=
        badFamily_deterministic_implies_badFamily (F := F) (t := tParam m n) (ρ := ρ) hbad
      have hlen := badFamily_length_le_freeCount (F := F) (t := tParam m n) (ρ := ρ) hbad'
      have hzero : ρ.freeCount = 0 := by
        -- Из принадлежности `R_s` получаем `freeCount = 0`.
        simpa using (mem_R_s (n := n) (s := 0)).1 hρ
      have htpos : 0 < tParam m n := by
        simpa [tParam] using
          (Nat.succ_pos (Nat.log2 ((m + 1) * (n + 2))))
      -- Противоречие: `t ≤ 0` и `t > 0`.
      have : tParam m n ≤ 0 := by simpa [hzero] using hlen
      exact (Nat.lt_asymm htpos this).elim

end MultiSwitching
end AC0
end Pnp3
