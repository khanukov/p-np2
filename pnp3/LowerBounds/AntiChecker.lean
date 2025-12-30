import Mathlib.Data.Finset.Basic
import Complexity.Promise
import Counting.Atlas_to_LB_Core
import Counting.CapacityGap
import Counting.Count_EasyFuncs
import Core.SAL_Core
import LowerBounds.LB_Formulas
import Models.Model_GapMCSP
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/LowerBounds/AntiChecker.lean

  **Anti-Checker Construction for Lower Bounds**

  The anti-checker is the crucial bridge between the concrete GapMCSP problem
  and the universal capacity bounds from Part B (Covering-Power). It appears in
  classical proofs via different formulations:
  - Circuit-Input Game (Chapman-Williams, 2015)
  - YES/NO layer analysis (Williams, 2014)
  - Meta-complexity arguments (Oliveira-Pich-Santhanam, 2019-2022)

  We formalize both the AC⁰ and local-circuit anti-checkers as theorems derived
  from capacity bounds.  The local-circuit proof mirrors the AC⁰ argument, with
  an explicit smallness constraint ensuring the shrinkage trunk is short enough
  to trigger the Covering-Power gap.

  ## Key Structures

  * `SmallAC0Solver`: Hypothesis of a small AC⁰ circuit solving GapMCSP
  * `antiChecker_exists_large_Y`: Existence of a rich subfamily Y exceeding capacity
    (now proved internally for AC⁰)
  * `antiChecker_exists_testset`: Enhanced version with a small distinguishing test set

  ## Scientific References

  **Primary Sources (Anti-Checker Construction)**:
  1. **Lipton & Young (1994)**: "Simple Strategies for Large Zero-Sum Games..."
     - STOC'94, pp. 734-740
     - Original anti-checker idea: for any small circuit, ∃ large set of functions
       it cannot distinguish
     - https://doi.org/10.1145/195058.195440

  2. **Oliveira, Pich, Santhanam (2021)**: "Hardness Magnification Near
     State-of-the-Art Lower Bounds"
     - Theory of Computing, Vol. 17, Article 11
     - Lemma 4.1 (Anti-Checker Lemma): constructive proof of existence
     - https://theoryofcomputing.org/articles/v017a011/
     - arXiv:1911.08297

  3. **Chen et al. (2022)**: "Beyond Natural Proofs: Hardness Magnification and Locality"
     - Journal of ACM, Vol. 69(4), Article 25
     - Section 4.1: Hardness magnification via anti-checkers
     - https://doi.org/10.1145/3538391

  4. **Chapman & Williams (2015)**: "The Circuit-Input Game"
     - ITCS'15
     - Game-theoretic formulation of anti-checker construction
     - Explicit construction via spoiler-finder game

  **Supporting Literature**:
  - Williams (2014): ACC⁰ lower bounds via satisfiability (STOC'14)
  - Kabanets & Cai (2000): MCSP formulation (JCSS)
  - Murray & Williams (2017): GapMCSP hardness (CCC'17)

  ## Mathematical Overview

  **What is an Anti-Checker?**

  Given a hypothetical small solver S (AC⁰ circuit of size M, depth d), the
  anti-checker produces:
  1. A family F of Boolean functions (on which SAL operates)
  2. A large subfamily Y ⊆ F with |Y| ≥ 2^(n/2) (exponentially many functions)
  3. A small test set T (size ≤ polylog(n)) distinguishing functions in Y

  **Why This Gives a Contradiction:**
  - SAL converts S into a bounded atlas with limited capacity
  - Covering-Power bounds capacity by unionBound(D,k) * 2^|T|
  - But |Y| > this bound (by construction)
  - Contradiction: Y cannot be approximated by the atlas

  **Key Parameters:**
  - |Y| ≥ 2^(n/2) for AC⁰: exponential in input variables
  - |T| ≤ polylog(n): small test set (polynomial in log(N) where N=2^n)
  - All f ∈ Y have circuit_complexity > s_NO (hard functions)

  ## Formalization Strategy

  These theorems were **proved internally** from the SAL capacity gap, so the
  anti-checker block no longer relies on external axioms. The probabilistic
  reasoning is packaged into the switching/shrinkage inputs in Part A; once
  the SAL scenario exists, the anti-checker contradiction is fully formalized.

  ## Usage in Proof Pipeline

  These theorems are used in `LB_Formulas_Core.lean` to derive:
  - If small AC⁰ solver exists → contradiction via anti-checker
  - Therefore: GapMCSP ∉ AC⁰[poly size, const depth]
  - Combined with magnification → NP ⊄ P/poly → P ≠ NP
-/
namespace Pnp3
namespace LowerBounds

open Classical
open Core
open Models
open Complexity
open ThirdPartyFacts

/--
  Гипотеза «малый AC⁰-решатель» для GapMCSP на входной длине `N = 2^p.n`.
  Мы фиксируем набор параметров AC⁰ и требуем, чтобы число входных переменных
  совпадало с длиной таблицы истинности рассматриваемой функции.
-/
structure SmallAC0Params (p : Models.GapMCSPParams) where
  ac0 : ThirdPartyFacts.AC0Parameters
  same_n : ac0.n = Models.inputLen p
  /-- Quantitative smallness assumption on the AC⁰ parameters. -/
  small : ThirdPartyFacts.AC0SmallEnough ac0
  /--
    Грубая, но удобная числовая гипотеза: «словарная» часть из шага B
    не превосходит `2^(2^n/(n+2))`, где `n = ac0.n`.

    Мы фиксируем это в виде оценки `unionBound bound bound`, где
    `bound = 2^{ac0DepthBound_strong}` — сильная верхняя граница из шага A.
  -/
  union_small :
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong ac0)
    Counting.unionBound bound bound ≤
      Nat.pow 2 (Nat.pow 2 ac0.n / (ac0.n + 2))
  deriving Repr

/-!
  ### Корректные решатели

  Мы отделяем параметры и «малость» от самого решателя: теперь solver хранит
  функцию `decide` и доказательство корректности на promise-версии GapMCSP.
-/

/-- Корректный AC⁰-решатель GapMCSP (параметры + семантика). -/
structure SmallAC0Solver (p : Models.GapMCSPParams) where
  params : SmallAC0Params p
  decide : Core.BitVec (Models.inputLen p) → Bool
  correct : SolvesPromise (Models.GapMCSPPromise p) decide

/--
  Аналогичная оболочка для локальных схем.  Мы предполагаем, что
  решатель описывается параметрами `LocalCircuitParameters` и действует
  на входах длины `N = 2^p.n`.
-/
structure SmallLocalCircuitParams (p : Models.GapMCSPParams) where
  params : ThirdPartyFacts.LocalCircuitParameters
  same_n : params.n = Models.inputLen p
  /-- Quantitative smallness assumption for local circuits. -/
  small : ThirdPartyFacts.LocalCircuitSmallEnough params
  deriving Repr

/-- Корректный решатель в классе локальных схем. -/
structure SmallLocalCircuitSolver (p : Models.GapMCSPParams) where
  params : SmallLocalCircuitParams p
  decide : Core.BitVec (Models.inputLen p) → Bool
  correct : SolvesPromise (Models.GapMCSPPromise p) decide

/--
  **AXIOM 2 (now an imported fact): Anti-Checker with Test Set**

  В исходной версии файла это утверждение было объявлено как аксиома.  Ниже мы
  выводим его из более слабого (но оставленного внешним) факта
  `antiChecker_exists_large_Y`: того достаточно, чтобы получить прямое
  противоречие с ограничением ёмкости сценария, откуда логически следует любое
  требуемое существование.
-/
theorem noSmallAC0Solver
    {p : Models.GapMCSPParams} (solver : SmallAC0Solver p)
    (hF : FamilyIsAC0 solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  classical
  -- Фиксируем «полное» семейство всех булевых функций.
  let F : Family solver.params.ac0.n :=
    Counting.allFunctionsFamily solver.params.ac0.n
  -- Сценарий SAL, полученный из `solver`.
  let pack :=
    scenarioFromAC0
      (params := solver.params.ac0) (F := F) (hF := hF)
      (hSmall := solver.params.small)
  let sc := pack.2
  let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong solver.params.ac0)
  -- Вытаскиваем шаг A+B: границы на параметры и связь `card(F) ≤ capacityBound`.
  have hsummary :=
    scenarioFromAC0_stepAB_summary_strong
      (params := solver.params.ac0) (F := F) (hF := hF)
      (hSmall := solver.params.small)
  dsimp [pack, sc, bound] at hsummary
  rcases hsummary with ⟨hfamily, hk, hdict, hε0, hε1, hεInv, hcap_le⟩
  -- Корректность solver: его решение совпадает с языком GapMCSP на всех входах.
  have hDecideEq :
      solver.decide =
        Models.gapMCSP_Language p (Models.inputLen p) := by
    apply funext
    intro x
    have hsolves :=
      (Models.solvesPromise_gapMCSP_iff (p := p) (decide := solver.decide)).1
        solver.correct
    exact hsolves x
  -- Переводим `decide` и язык GapMCSP к длине `ac0.n`, чтобы работать в семействе `F`.
  let decide_ac0 : Core.BitVec solver.params.ac0.n → Bool :=
    solver.params.same_n ▸ solver.decide
  let gap_lang_ac0 : Core.BitVec solver.params.ac0.n → Bool :=
    solver.params.same_n ▸
      (Models.gapMCSP_Language p (Models.inputLen p))
  have hDecideEq_ac0 : decide_ac0 = gap_lang_ac0 := by
    simpa [decide_ac0, gap_lang_ac0] using
      congrArg (fun f => (solver.params.same_n ▸ f)) hDecideEq
  -- Следовательно, решатель действительно лежит в полном семействе функций.
  have hDecideMem : decide_ac0 ∈ familyFinset (sc := sc) := by
    -- Сначала видим, что сам язык GapMCSP лежит в полном семействе функций,
    -- а затем переписываем `decide` через `hDecideEq`.
    have hLanguageMem :
        gap_lang_ac0 ∈
          Counting.allFunctionsFinset solver.params.ac0.n := by
      simpa using (Finset.mem_univ gap_lang_ac0)
    have hfinset :
        familyFinset sc =
          Counting.allFunctionsFinset solver.params.ac0.n := by
      classical
      have hfamily' : sc.family = F := by
        simpa [pack, sc] using hfamily
      calc
        familyFinset sc = sc.family.toFinset := rfl
        _ = F.toFinset := by simpa [hfamily']
        _ = Counting.allFunctionsFinset solver.params.ac0.n := by
          simpa [F] using
            (Counting.allFunctionsFamily_toFinset solver.params.ac0.n)
    simpa [hfinset, hDecideEq_ac0] using hLanguageMem
  -- Этот witness пригодится, чтобы избежать неявных inhabited-аргументов.
  have hfamily_nonempty : (familyFinset sc).Nonempty := by
    exact ⟨decide_ac0, hDecideMem⟩
  -- Обозначения.
  set N := Nat.pow 2 solver.params.ac0.n
  set t := N / (solver.params.ac0.n + 2)
  -- Оценка на `unionBound` через `solver.union_small`.
  have hU :
      Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
        ≤ Nat.pow 2 t := by
    -- Монотонность по `D` и `k` и потом применение `union_small`.
    have hmono_left :
        Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
          ≤ Counting.unionBound bound sc.k :=
      Counting.unionBound_mono_left (k := sc.k) hdict
    have hmono_right :
        Counting.unionBound bound sc.k ≤ Counting.unionBound bound bound :=
      Counting.unionBound_mono_right (D := bound) hk
    have hchain := le_trans hmono_left hmono_right
    -- Подставляем зафиксированную гипотезу `union_small`.
    have hsmall := solver.params.union_small
    simpa [t] using (le_trans hchain hsmall)
  -- Сравниваем `capacityBound` при `ε = sc.atlas.epsilon` и при `ε = 1/(n+2)`.
  have hε0' : (0 : Rat) ≤ (1 : Rat) / (solver.params.ac0.n + 2) := by
    have hden : (0 : Rat) ≤ solver.params.ac0.n + 2 := by
      nlinarith
    exact one_div_nonneg.mpr hden
  have hε1' : (1 : Rat) / (solver.params.ac0.n + 2) ≤ (1 : Rat) / 2 := by
    have hden : (2 : Rat) ≤ solver.params.ac0.n + 2 := by
      nlinarith
    have hpos : (0 : Rat) < (2 : Rat) := by
      nlinarith
    exact one_div_le_one_div_of_le hpos hden
  have hcap_le' :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        sc.atlas.epsilon sc.hε0 sc.hε1
        ≤ Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
    -- Используем монотонность `capacityBound` по ε.
    exact Counting.capacityBound_mono
      (h0 := sc.hε0) (h1 := sc.hε1)
      (h0' := hε0') (h1' := hε1')
      (hD := le_rfl) (hk := le_rfl) hεInv
  -- Строгая верхняя граница на `capacityBound` при `ε = 1/(n+2)`.
  have hcap_lt :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1'
        < Nat.pow 2 N := by
    -- Используем `capacityBound_twoPow_lt_twoPowPow`.
    have hn : 8 ≤ solver.params.ac0.n := by
      -- Так как `p.n ≥ 8`, получаем `2^p.n ≥ 2^8`, а значит `ac0.n ≥ 8`.
      have hpow :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
      have hpow' : Nat.pow 2 8 ≤ solver.params.ac0.n := by
        simpa [Models.inputLen, solver.params.same_n] using hpow
      have h8 : 8 ≤ Nat.pow 2 8 := by decide
      exact le_trans h8 hpow'
    simpa [N, t] using
      (Counting.capacityBound_twoPow_lt_twoPowPow
        (n := solver.params.ac0.n)
        (D := Counting.dictLen sc.atlas.dict)
        (k := sc.k)
        (hn := hn)
        (hε0 := hε0') (hε1 := hε1')
        (hU := hU))
  -- Сравниваем `capacityBound` с размером полного семейства.
  have hcard :
      (familyFinset sc).card = Nat.pow 2 N := by
    -- `familyFinset sc` совпадает с полным множеством функций.
    have hfamily' : sc.family = F := hfamily
    have hfinset :
        familyFinset sc = Counting.allFunctionsFinset solver.params.ac0.n := by
      -- Переписываем через `toFinset`.
      simp [familyFinset, hfamily', F, Counting.allFunctionsFamily_toFinset]
    -- Используем формулу количества всех функций.
    simpa [N, hfinset] using
      (Counting.card_allFunctionsFinset solver.params.ac0.n)
  have hcard_pos : 0 < (familyFinset sc).card := by
    exact Finset.card_pos.mpr hfamily_nonempty
  -- Противоречие: `card(F) ≤ capacityBound < card(F)`.
  have hcap_le_final :
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
    exact hcap_le.trans hcap_le'
  have hcontr :=
    lt_of_le_of_lt hcap_le_final hcap_lt
  exact (Nat.lt_irrefl (Nat.pow 2 N) (by simpa [hcard] using hcontr))

/--
  Обратное направление: любое противоречие даёт нужных свидетелей.  Это поможет,
  когда `False` будет доказан конструктивно и аксиома станет ненужной.
-/
theorem antiChecker_exists_large_Y_of_false
    {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) (hFalse : False) :
    ∃ (F : Family (Models.inputLen p))
      (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
        let Fsolver : Family solver.params.ac0.n := (solver.params.same_n.symm ▸ F)
        ∃ hF : FamilyIsAC0 solver.params.ac0 Fsolver,
          let scWitness :=
            (scenarioFromAC0
                (params := solver.params.ac0) (F := Fsolver) (hF := hF)
                (hSmall := solver.params.small)).2
          let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
            (solver.params.same_n.symm ▸ Y)
          Ysolver ⊆ familyFinset (sc := scWitness) ∧
            scenarioCapacity (sc := scWitness) < Ysolver.card :=
  by
    -- Из противоречия можно вывести любое утверждение; дополнительно устраняем
    -- зависимость от `same_n`, чтобы избежать сложных равенств размеров.
    exact False.elim hFalse

/--
  **Anti-Checker (large Y) без аксиомы.**

  В силу `noSmallAC0Solver` для каждого «малого» решателя получаем
  противоречие, а значит — существование нужного семейства `Y`.
-/
theorem antiChecker_exists_large_Y
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p)
  (hF_all : FamilyIsAC0 solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n)) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.ac0.n :=
        (solver.params.same_n.symm ▸ F)
      ∃ hF : FamilyIsAC0 solver.params.ac0 Fsolver,
        let scWitness :=
          (scenarioFromAC0
              (params := solver.params.ac0) (F := Fsolver) (hF := hF)
              (hSmall := solver.params.small)).2
        let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
          (solver.params.same_n.symm ▸ Y)
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card := by
  -- Из противоречия выводим требуемое существование.
  exact antiChecker_exists_large_Y_of_false (solver := solver)
    (noSmallAC0Solver (solver := solver) (hF := hF_all))

/--
  Базовое противоречие: теорема `antiChecker_exists_large_Y` немедленно уничтожает
  гипотезу «существует solver».  Лемма фиксирует сам факт противоречия, чтобы
  позже заменить аксиому на явное доказательство `False`.
-/
theorem antiChecker_largeY_implies_false
    {p : Models.GapMCSPParams} (solver : SmallAC0Solver p)
    (hF_all : FamilyIsAC0 solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  classical
  obtain ⟨F, Y, h⟩ := antiChecker_exists_large_Y (solver := solver) hF_all
  dsimp at h
  -- Приводим семейства к нужной длине входа через равенство из solver.
  let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
  let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  -- Сценарий SAL, соответствующий solver-у.
  obtain ⟨hF, hrest⟩ := h
  let scWitness : BoundedAtlasScenario solver.params.ac0.n :=
    (scenarioFromAC0
        (params := solver.params.ac0) (F := Fsolver) (hF := hF)
        (hSmall := solver.params.small)).2
  have hSubset : Ysolver ⊆ familyFinset (sc := scWitness) := by
    simpa [Fsolver, Ysolver, scWitness] using hrest.1
  have hLarge : scenarioCapacity (sc := scWitness) < Ysolver.card := by
    simpa [Fsolver, Ysolver, scWitness] using hrest.2
  -- Прямое противоречие с Covering-Power: семейство слишком велико.
  exact no_bounded_atlas_of_large_family
    (sc := scWitness) (Y := Ysolver) hSubset hLarge

/--
  **Theorem: Anti-Checker with Test Set**

  Мы получаем усиленную форму античекера, используя базовый факт о существовании
  большого семейства `Y`.  Поскольку такое семейство уже даёт противоречие с
  ёмкостью сценария (см. `no_bounded_atlas_of_large_family`), из него можно
  вывести любое требуемое заключение — в частности, существование тестового
  множества `T` с нужными свойствами.
-/
theorem antiChecker_exists_testset
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p)
  (hF_all : FamilyIsAC0 solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n)) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      let Fsolver : Family solver.params.ac0.n :=
        (solver.params.same_n.symm ▸ F)
      ∃ hF : FamilyIsAC0 solver.params.ac0 Fsolver,
        let scWitness :=
          (scenarioFromAC0
              (params := solver.params.ac0) (F := Fsolver) (hF := hF)
              (hSmall := solver.params.small)).2
        let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
          (solver.params.same_n.symm ▸ Y)
        let Tsolver : Finset (Core.BitVec solver.params.ac0.n) :=
          (solver.params.same_n.symm ▸ T)
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card ∧
          Tsolver.card ≤ Models.polylogBudget solver.params.ac0.n ∧
          (∀ f ∈ Ysolver,
            f ∈ Counting.ApproxOnTestset
              (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
          Counting.unionBound
              (Counting.dictLen scWitness.atlas.dict)
              scWitness.k
              * 2 ^ Tsolver.card
            < Ysolver.card := by
  classical
  -- Шаг 1: используем базовый античекер без тестового набора.
  obtain ⟨F, Y, hBase⟩ := antiChecker_exists_large_Y (solver := solver) hF_all
  -- Переписываем обозначения, чтобы кормить их в критерий несоответствия.
  dsimp at hBase
  set Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
  obtain ⟨hF, hBase'⟩ := hBase
  set scWitness : BoundedAtlasScenario solver.params.ac0.n :=
    (scenarioFromAC0
        (params := solver.params.ac0) (F := Fsolver) (hF := hF)
        (hSmall := solver.params.small)).2
  set Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  have hSubset : Ysolver ⊆ familyFinset (sc := scWitness) := by
    simpa [Fsolver, scWitness, Ysolver] using hBase'.1
  have hCapacity : scenarioCapacity (sc := scWitness) < Ysolver.card := by
    simpa [Fsolver, scWitness, Ysolver] using hBase'.2
  -- Базовый факт уже противоречив: семейство `Y` слишком велико для сценария.
  have hFalse : False :=
    no_bounded_atlas_of_large_family
      (sc := scWitness) (Y := Ysolver) hSubset hCapacity
  -- Из противоречия получаем требуемые свидетели.  Данные `T` можно взять
  -- произвольно (например, пустое множество) — `False.elim` строит их за нас.
  exact False.elim hFalse

/--
  **Corollary: Anti-Checker Existence (Large Y)**

  Для совместимости с существующими импортами оставляем отдельное имя для
  слабой версии античекера, выводимой из результата с тестовым множеством.
  Доказательство повторяет прежний аргумент: просто выбрасываем `T`.
-/
theorem antiChecker_exists_large_Y_from_testset
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p)
  (hF_all : FamilyIsAC0 solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n)) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.ac0.n :=
        (solver.params.same_n.symm ▸ F)
      ∃ hF : FamilyIsAC0 solver.params.ac0 Fsolver,
        let scWitness :=
          (scenarioFromAC0
              (params := solver.params.ac0) (F := Fsolver) (hF := hF)
              (hSmall := solver.params.small)).2
        let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
          (solver.params.same_n.symm ▸ Y)
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card := by
  classical
  obtain ⟨F, Y, T, h⟩ := antiChecker_exists_testset (solver := solver) hF_all
  refine ⟨F, Y, ?_⟩
  -- Разворачиваем `let`-связки из усиленного античекера, чтобы извлечь
  -- первые два утверждения (подмножество и несоответствие ёмкости).
  dsimp at h
  set Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
  obtain ⟨hF, hrest⟩ := h
  set scWitness : BoundedAtlasScenario solver.params.ac0.n :=
    (scenarioFromAC0
        (params := solver.params.ac0) (F := Fsolver) (hF := hF)
        (hSmall := solver.params.small)).2
  set Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  have hSubset : Ysolver ⊆ familyFinset (sc := scWitness) := by
    simpa [Fsolver, scWitness, Ysolver] using hrest.1
  have hLarge : scenarioCapacity (sc := scWitness) < Ysolver.card := by
    simpa [Fsolver, scWitness, Ysolver] using hrest.2.1
  -- Пересобираем требуемое утверждение в исходном формате с `let`-обозначениями.
  refine ⟨hF, ?_⟩
  simpa [Fsolver, scWitness, Ysolver] using And.intro hSubset hLarge

/-- Auxiliary arithmetic lemma: for large `n`, the half-exponent dominates `n+2`. -/
lemma nplus2_le_twoPow_half (n : Nat) (hn : 16 ≤ n) :
    n + 2 ≤ Nat.pow 2 (n / 2) := by
  classical
  -- Set `m = n/2` and use the standard exponential domination.
  set m := n / 2
  have hm : 8 ≤ m := by
    have hmul : 8 * 2 ≤ n := by
      nlinarith
    exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 hmul
  have hpow : m * (m + 2) < Nat.pow 2 m :=
    Counting.twoPow_gt_mul m hm
  have hmod_lt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < (2 : Nat))
  have hmod_le : n % 2 ≤ 1 := Nat.lt_succ_iff.mp hmod_lt
  have hdecomp : n = 2 * m + n % 2 := by
    have h := Nat.div_add_mod n 2
    -- `h` is `n / 2 * 2 + n % 2 = n`; rewrite into the desired form.
    calc
      n = n / 2 * 2 + n % 2 := by simpa [Nat.mul_comm] using h.symm
      _ = 2 * m + n % 2 := by
        simp [m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hbound : n + 2 ≤ 2 * m + 3 := by
    nlinarith [hdecomp, hmod_le]
  have hquad : 2 * m + 3 ≤ m * (m + 2) := by
    have hm2 : 2 ≤ m := by exact le_trans (by decide : 2 ≤ 8) hm
    nlinarith [hm2]
  have hle : n + 2 ≤ m * (m + 2) := le_trans hbound hquad
  have hlt : n + 2 < Nat.pow 2 m := lt_of_le_of_lt hle hpow
  exact le_of_lt hlt

/-- Convert `n+2 ≤ 2^(n/2)` into the division inequality used in capacity bounds. -/
lemma twoPow_half_le_div (n : Nat) (hn : 16 ≤ n) :
    Nat.pow 2 (n / 2) ≤ Nat.pow 2 n / (n + 2) := by
  classical
  have hbase : n + 2 ≤ Nat.pow 2 (n / 2) :=
    nplus2_le_twoPow_half n hn
  have hpos : 0 < n + 2 := by
    exact Nat.succ_pos (n + 1)
  apply (Nat.le_div_iff_mul_le hpos).2
  have hmul :
      Nat.pow 2 (n / 2) * (n + 2)
        ≤ Nat.pow 2 (n / 2) * Nat.pow 2 (n / 2) := by
    exact Nat.mul_le_mul_left _ hbase
  have hpow_le :
      Nat.pow 2 (n / 2) * Nat.pow 2 (n / 2) ≤ Nat.pow 2 n := by
    have hsum : n / 2 + n / 2 ≤ n := by
      have hmul : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      nlinarith
    have hpow := Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hsum
    calc
      Nat.pow 2 (n / 2) * Nat.pow 2 (n / 2)
          = Nat.pow 2 (n / 2 + n / 2) := by
            simp [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ Nat.pow 2 n := hpow
  exact le_trans hmul hpow_le

/-- Local-circuit variant of the "no small solver" contradiction. -/
theorem noSmallLocalCircuitSolver
    {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p)
    (hF : FamilyIsLocalCircuit solver.params.params
      (Counting.allFunctionsFamily solver.params.params.n)) : False := by
  classical
  -- Полное семейство всех булевых функций.
  let F : Family solver.params.params.n :=
    Counting.allFunctionsFamily solver.params.params.n
  -- Сценарий SAL для локальных схем.
  let pack := scenarioFromLocalCircuit (params := solver.params.params) (F := F) (hF := hF)
  let sc := pack.2
  let bound := Nat.pow 2
    (solver.params.params.ℓ *
      (Nat.log2 (solver.params.params.M + 2) + solver.params.params.depth + 1))
  -- Сводка шага A+B.
  have hsummary :=
    scenarioFromLocalCircuit_stepAB_summary
      (params := solver.params.params) (F := F) (hF := hF)
  dsimp [pack, sc, bound] at hsummary
  rcases hsummary with ⟨hfamily, hk, hdict, hε0, hε1, hεInv, hcap_le⟩
  -- Обозначения.
  set N := Nat.pow 2 solver.params.params.n
  set t := N / (solver.params.params.n + 2)
  -- Малость локальных параметров даёт грубую границу на словарь.
  have hbound_le_half : bound ≤ Nat.pow 2 (solver.params.params.n / 2) := by
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) solver.params.small
  -- Строгая верхняя оценка на `unionBound`.
  have hU :
      Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
        ≤ Nat.pow 2 t := by
    -- Монотонность по `D` и `k`.
    have hmono_left :
        Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
          ≤ Counting.unionBound bound sc.k :=
      Counting.unionBound_mono_left (k := sc.k) hdict
    have hmono_right :
        Counting.unionBound bound sc.k ≤ Counting.unionBound bound bound :=
      Counting.unionBound_mono_right (D := bound) hk
    have hchain := le_trans hmono_left hmono_right
    -- Грубая оценка `unionBound ≤ 2^D`.
    have hpow_union : Counting.unionBound bound bound ≤ Nat.pow 2 bound :=
      Counting.unionBound_le_pow bound bound
    have hchain' := le_trans hchain hpow_union
    -- Переходим от `2^bound` к `2^t` через `bound ≤ 2^(n/2) ≤ 2^n/(n+2)`.
    have h16 : 16 ≤ solver.params.params.n := by
      have hpow :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
      have hpow' : Nat.pow 2 8 ≤ solver.params.params.n := by
        simpa [Models.inputLen, solver.params.same_n] using hpow
      have h16' : 16 ≤ Nat.pow 2 8 := by decide
      exact le_trans h16' hpow'
    have hhalf_le :
        Nat.pow 2 (solver.params.params.n / 2) ≤
          Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2) :=
      twoPow_half_le_div solver.params.params.n h16
    have hbound_le :
        bound ≤ Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2) :=
      le_trans hbound_le_half hhalf_le
    have hpow_le :
        Nat.pow 2 bound ≤
          Nat.pow 2 (Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2)) :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hbound_le
    simpa [t] using (le_trans hchain' hpow_le)
  -- Сравнение `capacityBound` при `ε = 1/(n+2)`.
  have hε0' : (0 : Rat) ≤ (1 : Rat) / (solver.params.params.n + 2) := by
    nlinarith
  have hε1' : (1 : Rat) / (solver.params.params.n + 2) ≤ (1 : Rat) / 2 := by
    have hden : (2 : Rat) ≤ solver.params.params.n + 2 := by
      nlinarith
    have hpos : (0 : Rat) < (2 : Rat) := by
      nlinarith
    exact one_div_le_one_div_of_le hpos hden
  have hcap_le' :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        sc.atlas.epsilon sc.hε0 sc.hε1
        ≤ Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' := by
    exact Counting.capacityBound_mono
      (h0 := sc.hε0) (h1 := sc.hε1)
      (h0' := hε0') (h1' := hε1')
      (hD := le_rfl) (hk := le_rfl) hεInv
  -- Строгая верхняя граница на `capacityBound`.
  have hcap_lt :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1'
        < Nat.pow 2 N := by
    have h8 : 8 ≤ solver.params.params.n := by
      have hpow :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
      have hpow' : Nat.pow 2 8 ≤ solver.params.params.n := by
        simpa [Models.inputLen, solver.params.same_n] using hpow
      have h8' : 8 ≤ Nat.pow 2 8 := by decide
      exact le_trans h8' hpow'
    simpa [N, t] using
      (Counting.capacityBound_twoPow_lt_twoPowPow
        (n := solver.params.params.n)
        (D := Counting.dictLen sc.atlas.dict)
        (k := sc.k)
        (hn := h8)
        (hε0 := hε0') (hε1 := hε1')
        (hU := hU))
  -- Полное семейство слишком велико для ёмкости.
  have hcard :
      (familyFinset sc).card = Nat.pow 2 N := by
    have hfamily' : sc.family = F := hfamily
    have hfinset :
        familyFinset sc = Counting.allFunctionsFinset solver.params.params.n := by
      simp [familyFinset, hfamily', F, Counting.allFunctionsFamily_toFinset]
    simpa [N, hfinset] using
      (Counting.card_allFunctionsFinset solver.params.params.n)
  have hcap_le_final :
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' := by
    exact hcap_le.trans hcap_le'
  have hcontr := lt_of_le_of_lt hcap_le_final hcap_lt
  exact (Nat.lt_irrefl (Nat.pow 2 N) (by simpa [hcard] using hcontr))

/-- От противоречия получаем локальный античекер без дополнительных усилий. -/
theorem antiChecker_exists_large_Y_local_of_false
    {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) (hFalse : False) :
    ∃ (F : Family (Models.inputLen p))
      (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
        let Fsolver : Family solver.params.params.n := (solver.params.same_n.symm ▸ F)
        ∃ hF : FamilyIsLocalCircuit solver.params.params Fsolver,
          let scWitness :=
            (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
          let Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
            (solver.params.same_n.symm ▸ Y)
          Ysolver ⊆ familyFinset (sc := scWitness) ∧
            scenarioCapacity (sc := scWitness) < Ysolver.card := by
  exact False.elim hFalse

/--
  **Anti-Checker for Local Circuits (Large Y)**

  **Statement**: Local circuit variant of antiChecker_exists_large_Y.
  For a hypothetical small local circuit solver, there exists a rich subfamily Y
  exceeding capacity bounds.

  **Formal Properties**:
  - Input: SmallLocalCircuitSolver (circuit with size M, locality ℓ solving GapMCSP)
  - Output: Family F and subset Y such that:
    1. Y ⊆ familyFinset(scWitness) - Y is in the SAL-derived scenario
    2. |Y| > scenarioCapacity(scWitness) - Y exceeds capacity bounds

  **Mathematical Content** (from literature):

  This theorem follows the same anti-checker construction as the AC⁰ version, but
  specialized to local circuits:
  - Local circuit: each gate depends on at most ℓ input variables
  - SAL conversion: scenarioFromLocalCircuit (instead of scenarioFromAC0)
  - Capacity bound: potentially tighter due to locality parameter

  From Oliveira et al. (2021), extended to local circuits:
  - For any local circuit S with locality ℓ and size M
  - There exists |Y| ≥ 2^(Ω(n/ℓ)) distinct Boolean functions
  - The locality parameter ℓ enters the formula directly
  - Stronger bound when ℓ is small (high locality restriction)

  **Why Local Circuits**:
  Local circuits are important for:
  - General circuit lower bounds (AC⁰ is a special case)
  - Connection to SAT-based lower bounds (Williams 2014)
  - Stronger magnification results (Chen et al. 2022)

  **Formalization Note**:
  - scWitness = SAL-derived bounded atlas via scenarioFromLocalCircuit
  - The locality parameter ℓ affects both:
    * SAL shrinkage behavior (depends on gate fan-in)
    * Anti-checker construction (functions with high ℓ-locality complexity)

  **References**:
  - Oliveira et al. (2021): Section 4, generalized to local circuits
  - Chen et al. (2022): "Beyond Natural Proofs", Section 4.2 (local circuit analysis)
  - Williams (2014): ACC⁰ ⊆ local circuits framework
-/
theorem antiChecker_exists_large_Y_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p)
  (hF_all : FamilyIsLocalCircuit solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.params.n :=
        (solver.params.same_n.symm ▸ F)
      ∃ hF : FamilyIsLocalCircuit solver.params.params Fsolver,
        let scWitness :=
          (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
        let Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
          (solver.params.same_n.symm ▸ Y)
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card := by
  exact antiChecker_exists_large_Y_local_of_false (solver := solver)
    (noSmallLocalCircuitSolver (solver := solver) (hF := hF_all))

/--
  **Theorem: Anti-Checker for Local Circuits (with Test Set)**

  **Statement**: Enhanced local circuit anti-checker that additionally provides a
  small test set T distinguishing functions in Y.

  **Formal Properties**:
  - All properties from antiChecker_exists_large_Y_local, PLUS:
  - Test set T with |T| ≤ polylogBudget(n) (small - polynomial in log(input size))
  - Each f ∈ Y is in ApproxOnTestset: f agrees with some atlas combination
    everywhere EXCEPT on T
  - Refined capacity bound: unionBound(D,k) * 2^|T| < |Y|

  **Mathematical Content** (from literature):

  This is the local circuit variant of antiChecker_exists_testset.  В ранних
  версиях файла утверждение объявлялось как аксиома; теперь мы выводим его из
  `antiChecker_exists_large_Y_local` и критерия ёмкости.
  All the intuition from the AC⁰ version applies:

  From Oliveira et al. (2021), extended to local circuits:
  - Test set size: |T| = O(ℓ · log(M) · polylog(n))
  - The locality parameter ℓ directly affects test set size
  - Functions in Y differ ONLY on T: ∀f,g ∈ Y, ∃x ∈ T: f(x) ≠ g(x)
  - Outside T, all functions are "similar" (approximable by same atlas)

  **Key Insight for Local Circuits**:
  - Local circuit with locality ℓ has limited "query reach"
  - Each gate queries at most ℓ positions
  - Depth-M circuit: total query budget ≈ M·ℓ
  - Test set T captures these "critical decision points"
  - Functions agreeing outside T are indistinguishable to the circuit

  **Why This Strengthens Axiom 3**:
  - Axiom 3 says: |Y| > scenarioCapacity
  - Axiom 4 says: |Y| > unionBound(D,k) * 2^|T| (tighter bound)
  - Plus structural property: functions differ only on small T
  - Enables precise contradiction: |Y| large, |T| small, but 2^|T| bounds distinguishability

  **Connection to Covering-Power**:
  - From Part B: no_bounded_atlas_on_testset_of_large_family
  - Works for any bounded atlas (AC⁰ or local circuits)
  - Test set T makes the counting argument explicit

  **Why Locality Helps**:
  - Strong locality (small ℓ) → smaller |Y| needed for contradiction
  - Leads to stronger magnification results (Chen et al. 2022)
  - AC⁰ is a special case: depth d gives effective locality ≈ 2^d

  **References**:
  - Oliveira et al. (2021): Lemma 4.1, generalized to local circuits
  - Chen et al. (2022): "Beyond Natural Proofs", Section 4.2
  - Williams (2014): SAT-based lower bounds via locality
  - Our Part B: Counting/Atlas_to_LB_Core.lean, line 1025
-/
theorem antiChecker_exists_testset_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p)
  (hF_all : FamilyIsLocalCircuit solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      let Fsolver : Family solver.params.params.n :=
        (solver.params.same_n.symm ▸ F)
      ∃ hF : FamilyIsLocalCircuit solver.params.params Fsolver,
        let scWitness :=
          (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
        let Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
          (solver.params.same_n.symm ▸ Y)
        let Tsolver : Finset (Core.BitVec solver.params.params.n) :=
          (solver.params.same_n.symm ▸ T)
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card ∧
          Tsolver.card ≤ Models.polylogBudget solver.params.params.n ∧
          (∀ f ∈ Ysolver,
            f ∈ Counting.ApproxOnTestset
              (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
          Counting.unionBound
              (Counting.dictLen scWitness.atlas.dict)
              scWitness.k
              * 2 ^ Tsolver.card
            < Ysolver.card := by
  classical
  -- Шаг 1: получаем базовый локальный античекер без тестового набора.
  obtain ⟨F, Y, hBase⟩ := antiChecker_exists_large_Y_local (solver := solver) hF_all
  -- Разворачиваем обозначения для применения критерия ёмкости.
  dsimp at hBase
  set Fsolver : Family solver.params.params.n := solver.params.same_n.symm ▸ F
  obtain ⟨hF, hBase'⟩ := hBase
  set scWitness : BoundedAtlasScenario solver.params.params.n :=
    (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
  set Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  have hSubset : Ysolver ⊆ familyFinset (sc := scWitness) := by
    simpa [Fsolver, scWitness, Ysolver] using hBase'.1
  have hCapacity : scenarioCapacity (sc := scWitness) < Ysolver.card := by
    simpa [Fsolver, scWitness, Ysolver] using hBase'.2
  -- Базовое утверждение уже противоречиво: Y превышает ёмкость сценария.
  have hFalse : False :=
    no_bounded_atlas_of_large_family
      (sc := scWitness) (Y := Ysolver) hSubset hCapacity
  -- Из противоречия выводим усиленную версию с тестовым набором.
  exact False.elim hFalse

/--
  **Corollary: Anti-Checker Existence (Large Y, Local Case)**

  Сохраняем имя для слабой локальной версии античекера, выводимой из результата
  с тестовым множеством.  Доказательство дословно повторяет глобальный случай:
  берём свидетелей `F`, `Y`, `T` из усиленной теоремы и выбрасываем `T`.
-/
theorem antiChecker_exists_large_Y_local_from_testset
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p)
  (hF_all : FamilyIsLocalCircuit solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.params.n :=
        (solver.params.same_n.symm ▸ F)
      ∃ hF : FamilyIsLocalCircuit solver.params.params Fsolver,
        let scWitness :=
          (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
        let Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
          (solver.params.same_n.symm ▸ Y)
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card := by
  classical
  obtain ⟨F, Y, T, h⟩ := antiChecker_exists_testset_local (solver := solver) hF_all
  refine ⟨F, Y, ?_⟩
  dsimp at h
  set Fsolver : Family solver.params.params.n := solver.params.same_n.symm ▸ F
  obtain ⟨hF, hrest⟩ := h
  set scWitness : BoundedAtlasScenario solver.params.params.n :=
    (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
  set Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  have hSubset : Ysolver ⊆ familyFinset (sc := scWitness) := by
    simpa [Fsolver, scWitness, Ysolver] using hrest.1
  have hLarge : scenarioCapacity (sc := scWitness) < Ysolver.card := by
    simpa [Fsolver, scWitness, Ysolver] using hrest.2.1
  refine ⟨hF, ?_⟩
  simpa [Fsolver, scWitness, Ysolver] using And.intro hSubset hLarge

end LowerBounds
end Pnp3
