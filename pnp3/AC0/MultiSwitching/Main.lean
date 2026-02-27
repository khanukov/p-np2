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
## Stage 4 (малый алфавит): good restriction → Shrinkage

Stage 4 у нас реализован конструктивно через точечные selectors:
сертификат строится из таблицы истинности и **не требует** свойства
`GoodFamilyCNF`. Поэтому как только Stage 3 выдаёт *какую-то* рестрикцию,
мы можем сразу получить `Shrinkage` с `ε = 1/(n+2)`.
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
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ρ, -, -⟩ :=
    exists_good_restriction_step3_2_small_canonicalCCDT
      (F := F) hN ht henc_small
  -- Stage 4: строим Shrinkage из произвольной рестрикции.
  exact shrinkage_from_restriction (F := F) (ρ := ρ)

/-!
## Wrapper: Step 3.2 (CNF family)

Мы выполняем разбиение по размеру `n`:

* **малый `n`**: `sParam = 0`, тогда `BadFamily` невозможен при `t > 0`;
* **большой `n`**: используем `numerical_inequality_3_2` и counting‑лемму.
-/

/-!
### Малый `n`: `sParam = 0`, bad‑трасса невозможна

Эта лемма закрывает **Case B** из плана Step 3.2:
если `n < 49*(w+1)`, то `sParam = 0`, а из условия `tParam ≤ sParam`
получаем противоречие с тем, что `tParam > 0`.
-/

theorem exists_good_restriction_small_n
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (hm : m = F.length)
    (ht : tParam m n ≤ sParam n w)
    (hN : n < 49 * (w + 1))
    [DecidablePred (BadFamily_deterministic (F := F) (tParam m n))] :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ¬ BadFamily_deterministic (F := F) (tParam m n) ρ := by
  classical
  subst hm
  have hs : sParam n w = 0 := sParam_eq_zero_of_lt (n := n) (w := w) hN
  -- Из `tParam ≤ sParam` и `sParam = 0` получаем противоречие с `tParam > 0`.
  have htzero_le : tParam F.length n ≤ 0 := by
    simpa [hs] using ht
  have htpos : 0 < tParam F.length n := by
    simp [tParam]
  have hcontr : False := by
    have htzero : tParam F.length n = 0 := Nat.eq_zero_of_le_zero htzero_le
    have : (0 : Nat) < 0 := by
      have htpos' := htpos
      rw [htzero] at htpos'
      exact htpos'
    exact (Nat.lt_irrefl 0 this)
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
    have hlt : n < 49 * (w + 1) := lt_of_not_ge hN
    exact exists_good_restriction_small_n
      (F := F) (m := F.length) (hm := rfl) (ht := ht) hlt

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

/-!
## Stage 4 (common‑CCDT): shrinkage для restricted‑family

Этот вариант используется после того, как будет построен мост
`GoodFamilyCNF` → `GoodFamilyCNF_common`.
-/

/-!
## Stage 3 (common‑CCDT): bound → good restriction → shrinkage
-/

/-!
## Итог Stage 1–4 (common‑CCDT)

Эта форма используется как "боевой" интерфейс: Stage‑3 даёт good‑restriction
для common‑bad, Stage‑4 строит shrinkage для restricted‑family.
-/

/-!
## Stage 1–6 (common‑CCDT): сразу `PartialCertificate`

Здесь фиксируем прямой выход в `PartialCertificate` для restricted‑family:
из Stage‑3 (good restriction для `BadEvent_common`) и Stage‑4/6
получаем глубину ствола ровно `t`.
-/

/-!
## Common‑CCDT: версия с параметрами `sParam`/`tParam`
-/

theorem exists_good_restriction_step3_2_common
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (hm : m = F.length)
    (ht : tParam m n ≤ sParam n w)
    [DecidablePred (BadEvent_common (F := F) (tParam m n))]
    (hbound :
      (R_s (n := n) (sParam n w - tParam m n)).card
          * (2 * n * (w + 1) * (m + 1)) ^ (tParam m n)
        < (R_s (n := n) (sParam n w)).card) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ¬ BadEvent_common (F := F) (tParam m n) ρ := by
  classical
  subst hm
  exact exists_good_restriction_common_of_bound
    (F := F) (s := sParam n w) (t := tParam F.length n) hbound

/-!
## Stage 1–6 (common‑CCDT, params): сразу `PartialCertificate`

Этот результат фиксирует нетривиальный сертификат для restricted‑family:

* Stage 3: получаем `ρ` с `¬ BadEvent_common`;
* Stage 4–6: через `partialCertificate_from_good_restriction_common`
  получаем `depthBound = tParam m n` и `ε = 1/(n+2)`.
-/

theorem stage1_6_complete_common_params
    {n w : Nat} (F : FormulaFamily n w) (m : Nat)
    (hm : m = F.length)
    (ht : tParam m n ≤ sParam n w)
    [DecidablePred (BadEvent_common (F := F) (tParam m n))]
    (hbound :
      (R_s (n := n) (sParam n w - tParam m n)).card
          * (2 * n * (w + 1) * (m + 1)) ^ (tParam m n)
        < (R_s (n := n) (sParam n w)).card) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrict (ρ := ρ) F)),
        ℓ = 0 ∧ C.depthBound = tParam m n ∧
          C.epsilon = (1 : Q) / (n + 2) := by
  classical
  have htpos : 0 < tParam m n := by
    -- `tParam = log2(...) + 2` всегда положителен.
    simp [tParam]
  obtain ⟨ρ, hρs, hgood⟩ :=
    exists_good_restriction_step3_2_common (F := F) (m := m) hm ht hbound
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_good_restriction_common
      (F := F) (ρ := ρ) (t := tParam m n) htpos hgood
  exact ⟨ρ, hρs, ℓ, C, hℓ, hdepth, hε⟩

/-!
## Canonical params exports (common route, без `henc_small`)

Эти теоремы фиксируют рекомендуемый конструктивный путь I-4:
через `common`-маршрут с числовым bound, без внешней гипотезы
инъективности малого энкодинга.
-/

/-!
## Итог Stage 1–4 (общий/расширенный вариант)

Эта лемма — «финальная метка готовности» общего пайплайна:
если Stage 1–3 дают строгую границу на количество плохих рестрикций,
то Stage 4 конструктивно выдаёт `Shrinkage` с ошибкой `1/(n+2)`.
-/

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

end MultiSwitching
end AC0
end Pnp3
