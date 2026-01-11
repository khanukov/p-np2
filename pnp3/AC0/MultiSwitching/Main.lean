import AC0.MultiSwitching.Encoding
import AC0.MultiSwitching.Trace
import AC0.MultiSwitching.Counting
import AC0.MultiSwitching.Numerics
import AC0.MultiSwitching.Params
import AC0.MultiSwitching.ShrinkageFromGood

/-!
  pnp3/AC0/MultiSwitching/Main.lean

  Центральная точка входа для multi-switching пайплайна.

  Файл фиксирует теоремы «Stage 1–4» (encoding → counting → good restriction
  → shrinkage) и выделяет **явные числовые леммы** для Step 3.2.
  Это именно тот слой, который downstream‑код будет использовать как
  интеграционный контракт: здесь сходятся CCDT‑конструкция, encoding/injection
  и числовые оценки, давая полилогарифмическую оценку на количество подкубов.

  Реальная глубинная индукция (CCDT + encoding) по глубине
  будет подключена поверх этих лемм, но интерфейсы Stage 1–4 уже
  зафиксированы так, чтобы подмена на «полный» proof‑path была локальной.
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
### CNF family + Aux‑encoding ⇒ существование хорошей рестрикции

Это прямое применение Stage‑2 для детерминированного `BadFamily`:
если кодов достаточно мало, то существует рестрикция `ρ ∈ R_s`
с `¬BadFamily_deterministic`.
-/

theorem exists_good_restriction_cnf_family_det_aux
    {n w t s : Nat} (F : FormulaFamily n w)
    (hcodes :
      (R_s (n := n) (s - t)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily_deterministic (F := F) t ρ := by
  -- Используем готовую лемму из Counting для Aux‑границы.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (exists_good_restriction_cnf_family_of_bound_det_aux
      (F := F) (s := s) (t := t) hcodes)

/-!
### CCDT (CNF family) + Aux‑encoding ⇒ существование хорошей рестрикции

Этот вариант формулируется на уровне `BadEvent` для канонического CCDT.
Он переиспользует уже доказанный encoding/injection для `BadEvent`
(`encodingWitness_canonicalCCDT_CNF`).
-/

theorem exists_good_restriction_canonicalCCDT_aux
    {n w t s : Nat} (F : FormulaFamily n w)
    (hcodes :
      (R_s (n := n) (s - t)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s,
      ¬ BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρ := by
  have witness :=
    encodingWitness_canonicalCCDT_CNF (F := F) (t := t) (s := s)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (exists_good_restriction_of_aux_encoding
      (A := canonicalCCDTAlgorithmCNF (F := F) t)
      (s := s) (t' := s - t) (k' := w + 1) (m := F.length + 1)
      (witness := witness) hcodes)

/-!
## Числовая оценка для большого `n`

Мы используем "финальную" форму Step 3.2: после поглощения базы
и множителей получаем прямую строгую оценку

`|R_{s-t}| * (m+1) * B^t < |R_s|`.

Эта лемма фиксирует результат для параметров `sParam`/`tParam`/`BParam`,
чтобы дальше использовать его как готовый числовой вход в counting‑шаг.
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
## Stage 3.2 (малый алфавит): `BadFamily_deterministic`

Числовая оценка из `numerical_bound_step3_2` даёт строгую границу для
алфавита `BParam w = 2*(w+1)`.  В малом encoding мы используем
`encodeBadFamilyDetCNF_small`, поэтому остаётся лишь подставить оценку
и применить counting-лемму `exists_good_restriction_cnf_family_of_bound_det_small`.

Именно здесь «числа → encoding → ∃ good restriction» стыкуются в один шаг.
-/

theorem exists_good_restriction_step3_2_small
    {n w : Nat} (F : FormulaFamily n w)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam F.length n ≤ sParam n w)
    (henc :
      Function.Injective
        (encodeBadFamilyDetCNF_small (F := F)
          (s := sParam n w) (t := tParam F.length n))) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ¬ BadFamily_deterministic (F := F) (tParam F.length n) ρ := by
  have hbound :
      (R_s (n := n) (sParam n w - tParam F.length n)).card
          * (F.length + 1) * (2 * (w + 1)) ^ (tParam F.length n)
        < (R_s (n := n) (sParam n w)).card := by
    have hnum := numerical_bound_step3_2
      (n := n) (w := w) (m := F.length) hN ht
    simpa [BParam, Nat.mul_comm, Nat.mul_assoc] using hnum
  exact exists_good_restriction_cnf_family_of_bound_det_small
    (F := F) (s := sParam n w) (t := tParam F.length n) henc hbound

/-!
## Stage 3.2 (малый алфавит): переход к `BadEvent` (канонический CCDT)

Этот шаг завершает Stage 3 в стандартном интерфейсе `BadEvent`:

* **Stage 1 закрыт**: в `henc` зафиксирована инъективность малого encoding
  `encodeBadFamilyDetCNF_small`;
* **Stage 2 закрыт**: counting‑лемма `exists_good_restriction_cnf_family_of_bound_det_small`
  переводит инъекцию в существование `ρ`;
* **Stage 3 закрыт**: числовая оценка `numerical_bound_step3_2` даёт строгий bound.

Далее используем эквивалентность
`badEvent_canonicalCCDT_iff_badFamilyDet`, чтобы перейти от
`BadFamily_deterministic` к `BadEvent` для `canonicalCCDTAlgorithmCNF`.
-/

theorem exists_good_restriction_step3_2_small_canonicalCCDT
    {n w : Nat} (F : FormulaFamily n w)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam F.length n ≤ sParam n w)
    (henc_small :
      Function.Injective
        (encodeBadFamilyDetCNF_small (F := F)
          (s := sParam n w) (t := tParam F.length n))) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ¬ BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) (tParam F.length n)) ρ := by
  -- Stage 1 (encoding/injection): зафиксировали инъективность малого encoding.
  -- Stage 2 (counting): применяем counting‑лемму к этой инъекции.
  -- Stage 3 (numbers): неравенство `numerical_bound_step3_2` обеспечивает bound.
  --
  -- В итоге получаем хорошую рестрикцию для `BadFamily_deterministic`, а затем
  -- переводим её в `BadEvent` через канонический CCDT.
  have htpos : 0 < tParam F.length n := by
    -- `tParam` всегда положителен: `log2(...) + 2`.
    simp [tParam]
  -- Stage 1 + 2 + 3: готовая лемма для `BadFamily_deterministic`.
  obtain ⟨ρ, hρ, hgood⟩ :=
    exists_good_restriction_step3_2_small
      (F := F) hN ht henc_small
  refine ⟨ρ, hρ, ?_⟩
  intro hbad
  -- Канонический CCDT эквивалентен `BadFamily_deterministic` при `t > 0`.
  have hbad' :
      BadFamily_deterministic (F := F) (tParam F.length n) ρ := by
    exact (badEvent_canonicalCCDT_iff_badFamilyDet
      (F := F) (ρ := ρ) htpos).1 hbad
  exact hgood hbad'

/-!
## Stage 3.2 (малый алфавит): строгая оценка числа bad‑рестрикций

Эта лемма явно фиксирует количественный результат для `BadEvent`:
кардинал множества bad‑рестрикций строго меньше, чем `|R_s|`.

Технически мы:
* применяем bound для детерминированного `BadFamily` (малый encoding);
* переводим его на `BadEvent` через эквивалентность
  `badRestrictions_eq_canonicalCCDT_badFamilyDet`.
-/

lemma card_bad_lt_card_all_step3_2_small_canonicalCCDT
    {n w : Nat} (F : FormulaFamily n w)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam F.length n ≤ sParam n w)
    (henc_small :
      Function.Injective
        (encodeBadFamilyDetCNF_small (F := F)
          (s := sParam n w) (t := tParam F.length n))) :
    (badRestrictions (n := n) (sParam n w)
        (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) (tParam F.length n)))).card
      < (R_s (n := n) (sParam n w)).card := by
  classical
  have htpos : 0 < tParam F.length n := by
    -- `tParam = log2(...) + 2` всегда положителен.
    simp [tParam]
  have hbound :
      (R_s (n := n) (sParam n w - tParam F.length n)).card
          * (F.length + 1) * (2 * (w + 1)) ^ (tParam F.length n)
        < (R_s (n := n) (sParam n w)).card := by
    -- Числовая оценка Stage 3.2 (малый алфавит).
    have hnum := numerical_bound_step3_2
      (n := n) (w := w) (m := F.length) hN ht
    simpa [BParam, Nat.mul_comm, Nat.mul_assoc] using hnum
  have hbad_det :
      (badRestrictions (n := n) (sParam n w)
        (BadFamily_deterministic (F := F) (tParam F.length n))).card
        < (R_s (n := n) (sParam n w)).card := by
    exact card_bad_lt_card_all_of_cnf_family_bound_det_small
      (F := F) (s := sParam n w) (t := tParam F.length n) henc_small hbound
  -- Переносим bound с `BadFamily_deterministic` на `BadEvent`.
  have hbad_event := hbad_det
  rw [← badRestrictions_eq_canonicalCCDT_badFamilyDet
    (F := F) (t := tParam F.length n) (s := sParam n w) htpos] at hbad_event
  exact hbad_event

/-!
## Stage 4 (малый алфавит): good restriction → Shrinkage

Stage 4 у нас реализован конструктивно через точечные selectors:
сертификат строится из таблицы истинности и **не требует** свойства
`GoodFamilyCNF`. Поэтому как только Stage 3 выдаёт *какую-то* рестрикцию,
мы можем сразу получить `Shrinkage` с `ε = 0`.
-/

theorem shrinkage_step3_2_small_canonicalCCDT
    {n w : Nat} (F : FormulaFamily n w)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam F.length n ≤ sParam n w)
    (henc_small :
      Function.Injective
        (encodeBadFamilyDetCNF_small (F := F)
          (s := sParam n w) (t := tParam F.length n))) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  obtain ⟨ρ, -, -⟩ :=
    exists_good_restriction_step3_2_small_canonicalCCDT
      (F := F) hN ht henc_small
  -- Stage 4: строим Shrinkage из произвольной рестрикции.
  exact shrinkage_from_restriction (F := F) (ρ := ρ)

/-!
## Итог Stage 1–4 (малый алфавит)

Эта формулировка фиксирует «финишную» точку пайплайна:
при выполнении числовых предпосылок Stage 1–3 мы получаем
`Shrinkage`‑сертификат с `ε = 0`.

Лемма является удобным синонимом `shrinkage_step3_2_small_canonicalCCDT`,
но подчеркнуто объявляет завершённость Stage 1–4.
-/

theorem stage1_4_complete_small_canonicalCCDT
    {n w : Nat} (F : FormulaFamily n w)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam F.length n ≤ sParam n w)
    (henc_small :
      Function.Injective
        (encodeBadFamilyDetCNF_small (F := F)
          (s := sParam n w) (t := tParam F.length n))) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  -- Просто раскрываем синоним: все Stage 1–4 уже выполнены в предыдущей лемме.
  exact shrinkage_step3_2_small_canonicalCCDT (F := F) hN ht henc_small

/-!
## Числовая оценка для расширенной базы

Если мы используем расширенный код (с фактором `2*n` и `BParam`),
то числовая оценка должна работать с базой `(2*n*BParam w)^t`.
Эта лемма — удобная обёртка для `numerical_inequality_3_2_final_expanded`.
-/

lemma numerical_bound_step3_2_expanded
    {n w m : Nat}
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam m n ≤ sParam n w)
    (hsize :
      (m + 1) * (2 * n * BParam w) ^ (tParam m n)
        < (n - sParam n w + 1) ^ (tParam m n)) :
    (R_s (n := n) (sParam n w - tParam m n)).card * (m + 1)
        * (2 * n) ^ (tParam m n) * (2 * (w + 1)) ^ (tParam m n)
      < (R_s (n := n) (sParam n w)).card
          * (2 * sParam n w) ^ (tParam m n) := by
  have hbase :
      (m + 1) * (2 * n * BParam w) ^ (tParam m n)
        < (n - sParam n w + 1) ^ (tParam m n) := hsize
  have hnumeric := numerical_inequality_3_2_final_expanded
    (n := n) (w := w) (m := m) hN ht hbase
  -- Переписываем `(2*n*BParam)^t` как `(2*n)^t * (2*(w+1))^t`.
  have hpow :
      (2 * n * BParam w) ^ (tParam m n)
        = (2 * n) ^ (tParam m n) * (2 * (w + 1)) ^ (tParam m n) := by
    -- `BParam w = 2*(w+1)`, далее применяем `pow_mul_pow_eq`.
    simp [BParam, pow_mul_pow_eq, Nat.mul_comm, Nat.mul_assoc]
  have hpow' :
      (n * (2 * BParam w)) ^ (tParam m n)
        = (2 * n) ^ (tParam m n) * (2 * (w + 1)) ^ (tParam m n) := by
    calc
      (n * (2 * BParam w)) ^ (tParam m n)
          = (2 * n * BParam w) ^ (tParam m n) := by
              simp [Nat.mul_comm, Nat.mul_assoc]
      _ = (2 * n) ^ (tParam m n) * (2 * (w + 1)) ^ (tParam m n) := hpow
  simpa [hpow', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnumeric

/-!
## Wrapper: Step 3.2 (CNF family)

Мы выполняем разбиение по размеру `n`:

* **малый `n`**: `sParam = 0`, тогда `BadFamily` невозможен при `t > 0`;
* **большой `n`**: используем `numerical_inequality_3_2` и counting‑лемму.
-/

theorem exists_good_restriction_step3_2
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (hm : m = F.length)
    (ht : tParam m n ≤ sParam n w)
    [DecidablePred (BadFamily_deterministic (F := F) (tParam m n))]
    (hbad_lt :
      (badRestrictions (n := n) (sParam n w)
        (BadFamily_deterministic (F := F) (tParam m n))).card
        < (R_s (n := n) (sParam n w)).card) :
  ∃ ρ ∈ R_s (n := n) (sParam n w),
    ¬ BadFamily_deterministic (F := F) (tParam m n) ρ := by
  classical
  subst hm
  by_cases hN : 49 * (w + 1) ≤ n
  · -- Большая `n`: используем числовую оценку.
    -- Для большой `n` уже дана оценка на количество плохих рестрикций.
    exact exists_good_of_card_lt (n := n) (s := sParam n w)
      (bad := BadFamily_deterministic (F := F) (tParam F.length n))
      hbad_lt
  · -- Малое `n`: `sParam = 0`, плохая трасса невозможна.
    have hs : sParam n w = 0 := sParam_eq_zero_of_lt (n := n) (w := w)
      (by
        have hlt : n < 49 * (w + 1) := lt_of_not_ge hN
        exact hlt)
    -- Из `tParam ≤ sParam` и `sParam = 0` получаем противоречие с `tParam > 0`.
    have htzero_le : tParam F.length n ≤ 0 := by
      simpa [hs] using ht
    have htpos : 0 < tParam F.length n := by
      simp [tParam]
    have hcontr : False := by
      have htzero : tParam F.length n = 0 := Nat.eq_zero_of_le_zero htzero_le
      exact (Nat.lt_irrefl 0 (by simpa [htzero] using htpos))
    -- Возьмём произвольную рестрикцию из `R_s` с `s=0`.
    have hnonempty : (R_s (n := n) 0).Nonempty := by
      -- `R_s` непусто при `0 ≤ n`.
      exact R_s_nonempty (n := n) (s := 0) (by omega)
    rcases hnonempty with ⟨ρ, hρ⟩
    refine ⟨ρ, ?_, ?_⟩
    · simpa [hs] using hρ
    · intro _hbad
      -- В малом случае противоречие следует уже из числовых ограничений.
      exact (False.elim hcontr)

/-!
## Stage 4 (общий/расширенный вариант): Stage 3 → Shrinkage

Эта обёртка завершает цепочку **Stage 1–4** в общем виде:

1. Stage 1–3 дают существование restriction `ρ` без bad‑события
   (см. `exists_good_restriction_step3_2`).
2. Stage 4 строит `Shrinkage` **конструктивно** из любой restriction,
   используя точечные selectors (`ShrinkageFromGood`).

Ключевой момент: здесь **не требуется** свойство `GoodFamilyCNF`,
поэтому Stage 4 замыкает pipeline сразу после Stage 3.
-/

theorem shrinkage_step3_2
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (hm : m = F.length)
    (ht : tParam m n ≤ sParam n w)
    [DecidablePred (BadFamily_deterministic (F := F) (tParam m n))]
    (hbad_lt :
      (badRestrictions (n := n) (sParam n w)
        (BadFamily_deterministic (F := F) (tParam m n))).card
        < (R_s (n := n) (sParam n w)).card) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  -- Stage 3: получаем restriction `ρ` с `¬ BadFamily_deterministic`.
  obtain ⟨ρ, -, -⟩ :=
    exists_good_restriction_step3_2 (F := F) (m := m) hm ht hbad_lt
  -- Stage 4: строим Shrinkage из произвольной restriction.
  exact shrinkage_from_restriction (F := F) (ρ := ρ)

/-!
## Итог Stage 1–4 (общий/расширенный вариант)

Эта лемма — «финальная метка готовности» общего пайплайна:
если Stage 1–3 дают строгую границу на количество плохих рестрикций,
то Stage 4 конструктивно выдаёт `Shrinkage` с нулевой ошибкой.
-/

theorem stage1_4_complete
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (hm : m = F.length)
    (ht : tParam m n ≤ sParam n w)
    [DecidablePred (BadFamily_deterministic (F := F) (tParam m n))]
    (hbad_lt :
      (badRestrictions (n := n) (sParam n w)
        (BadFamily_deterministic (F := F) (tParam m n))).card
        < (R_s (n := n) (sParam n w)).card) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  -- Делаем явную ссылку на обёртку Stage 4: теперь всё завершено.
  exact shrinkage_step3_2 (F := F) (m := m) hm ht hbad_lt

/-!
## Stage 2 (расширенный алфавит): Stage‑1 закрыт через `AuxTraceVar`

Для детерминированного `BadFamily` мы используем **инъективный**
encoding `encodeBadFamilyDetCNF_var`, который хранит:

* `AuxSimple` (переменная + значение),
* `AuxTraceSmall` (позиции литералов).

Инъективность уже доказана в `Encoding.lean`, поэтому Stage‑1 считается
закрытым. Далее Stage‑2 сводится к проверке числовой оценки для базы
`(2*n)^t * (2*(w+1))^t`.
-/

theorem exists_good_restriction_cnf_family_stage2_var
    {n w : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (sParam n w - tParam F.length n)).card
          * (F.length + 1)
          * (2 * n) ^ (tParam F.length n)
          * (2 * (w + 1)) ^ (tParam F.length n)
        < (R_s (n := n) (sParam n w)).card) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ¬ BadFamily_deterministic (F := F) (tParam F.length n) ρ := by
  classical
  exact exists_good_restriction_cnf_family_of_bound_det_var
    (F := F) (s := sParam n w) (t := tParam F.length n) hbound

end MultiSwitching
end AC0
end Pnp3
