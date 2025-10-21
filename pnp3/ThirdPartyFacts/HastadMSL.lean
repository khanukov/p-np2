import ThirdPartyFacts.BaseSwitching
import ThirdPartyFacts.AC0Witness
import Core.PDT
import Core.TrunkBuilder
import AC0.Formulas

  /-!
    pnp3/ThirdPartyFacts/HastadMSL.lean

    This module isolates the statement-level interface to the classical switching
    and multi-switching lemmas due to Håstad, Impagliazzo–Matthews–Paturi, and
    Servedio–Tan.  While the genuine proofs are still pending, we now provide
    explicit (albeit very weak) witnesses so that no new axioms are introduced in
    the shrinkage pipeline.  These placeholders keep the downstream structure in
    place and make it straightforward to slot in the real combinatorial bounds
    later on.

    The key outcome is an `AC0PartialWitness` delivering a partial decision tree
    together with quantitative bounds on its depth and approximation error.  The
    intermediate `SwitchingLemmaOutcome` is provided for completeness and to make
    the expected data available to future formalisation work.
  -/

namespace Pnp3
namespace ThirdPartyFacts

open Core

/-- Parameters for the basic switching lemma. -/
structure SwitchingLemmaParameters where
  n : Nat
  k : Nat
  p : Q
  t : Nat
  deriving Repr

/-- A lightweight record for the switching lemma outcome. -/
structure SwitchingLemmaOutcome
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) where
  tree : PDT params.n
  depth_le : PDT.depth tree ≤ params.t
  failure : Q
  failure_bound : failure ≤ 1

/--
  Запись того, что для фиксированного КНФ `φ` уже построено дерево решений,
  удовлетворяющее классической switching-лемме.  Мы оформляем это как
  типкласс, чтобы последующий код мог зависеть от результата леммы без
  непосредственного обращения к глобальной аксиоме.
-/
class HasSwitchingWitness
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) : Type where
  outcome : SwitchingLemmaOutcome params φ

/-- Удобный аксессор: возвращает данные switching-леммы из экземпляра класса. -/
noncomputable def switchingWitness
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k)
    [w : HasSwitchingWitness params φ] :
    SwitchingLemmaOutcome params φ :=
  w.outcome

/--
  The classical switching lemma (statement only).  Until the full proof is
  ported to Lean we expose a tiny placeholder returning the degenerate decision
  tree consisting of a single leaf.  The quantitative failure bound is set to
  `1`, matching the fact that we make no attempt at proving a meaningful
  probability estimate yet.  This keeps the downstream interface axiom-free
  while clearly marking the remaining work.
-/
noncomputable def SwitchingLemma
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) :
    SwitchingLemmaOutcome params φ :=
  { tree := PDT.leaf (fun _ => none)
    depth_le := by simp [PDT.depth]
    failure := 1
    failure_bound := by norm_num }

/--
  Временный (аксиоматический) экземпляр класса `HasSwitchingWitness`: пока
  полноценное доказательство не перенесено в Lean, мы просто упаковываем
  результат аксиомы `SwitchingLemma`.  Это позволит позднее заменить
  определение на настоящее доказательство без изменений в остальном коде.
-/
noncomputable instance instHasSwitchingWitness
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) :
    HasSwitchingWitness params φ :=
  ⟨SwitchingLemma params φ⟩

/--
Parameters for the multi-switching lemma.  The only additional field is the
size of the family; other quantitative data is encoded directly in
`AC0Parameters` when we convert the outcome into a partial witness.
-/
structure MultiSwitchingParameters extends SwitchingLemmaParameters where
  s : Nat
  deriving Repr

/--
Outcome of the multi-switching lemma specialised to AC⁰ families.  The witness
packages the partial decision tree together with the usual depth and error
bounds.
-/
structure MultiSwitchingOutcome
    (params : AC0Parameters) (F : Family params.n) where
  witness : AC0PartialWitness params F

namespace MultiSwitchingOutcome

variable {params : AC0Parameters} {F : Family params.n}

/--
  Accessor exposing the partial certificate carried by a multi-switching outcome.
  Keeping this helper close to the type definition avoids pattern matching on the
  record and makes the eventual constructive proof easier to refactor.
-/
@[simp] def certificate (out : MultiSwitchingOutcome params F) :
    Core.PartialCertificate params.n out.witness.tailDepth F :=
  out.witness.certificate

/-- Depth information inherited from the underlying AC⁰ partial witness. -/
@[simp] lemma depthBound (out : MultiSwitchingOutcome params F) :
    (certificate (params := params) (F := F) out).depthBound =
      out.witness.certificate.depthBound := rfl

/-- Error parameter associated with the partial witness. -/
@[simp] lemma epsilon (out : MultiSwitchingOutcome params F) :
    (certificate (params := params) (F := F) out).epsilon =
      out.witness.certificate.epsilon := rfl

end MultiSwitchingOutcome

/-
  Небольшой служебный раздел: фиксируем удобные обозначения для "канонического"
  ствола, который опрашивает заранее заданный список переменных.  Эти функции
  используются лишь в будущей конструктивной версии multi-switching леммы, но
  уже сейчас полезно собрать их в одном месте, чтобы облегчить дальнейшую
  интеграцию.  Все доказательства опираются на комбинаторные факты из
  `Core.TrunkBuilder`.
-/
section TrunkScaffolding

open Core

variable {params : AC0Parameters}

/-- Канонический ствол, кодирующий последовательность переменных `vars`. -/
@[simp] def canonicalPartialTrunk (vars : List (Fin params.n)) :
    Core.PartialDT params.n 0 :=
  Core.PartialDT.ofPDT (Core.canonicalTrunk (n := params.n) vars)

lemma depth_canonicalPartialTrunk (vars : List (Fin params.n)) :
    Core.PDT.depth (canonicalPartialTrunk (params := params) vars).trunk
      = vars.length := by
  simpa [canonicalPartialTrunk]
    using Core.depth_trunkOfList_base (n := params.n) (vars := vars)

lemma leafDict_canonicalPartialTrunk (vars : List (Fin params.n)) :
    (canonicalPartialTrunk (params := params) vars).leafDict
      = Core.trunkLeaves (n := params.n) (Core.canonicalBase params.n) vars := by
  simpa [canonicalPartialTrunk]
    using Core.leaves_trunkOfList (n := params.n) (vars := vars)
      (β := Core.canonicalBase params.n)

lemma leafDict_length_canonicalPartialTrunk (vars : List (Fin params.n)) :
    (canonicalPartialTrunk (params := params) vars).leafDict.length
      = Nat.pow 2 vars.length := by
  have hpow :=
    Core.length_trunkLeaves (n := params.n) (β := Core.canonicalBase params.n)
      (vars := vars)
  have hdict := congrArg List.length
    (leafDict_canonicalPartialTrunk (params := params) (vars := vars))
  simpa [canonicalPartialTrunk] using hdict.trans hpow

lemma canonicalTrunk_eq_decisionTree_build
    (β : Core.Subcube params.n) (vars : List (Fin params.n)) :
    Core.trunkOfList (n := params.n) β vars
      = AC0.DecisionTree.build (n := params.n) β vars := by
  induction vars generalizing β with
  | nil =>
      simp [Core.trunkOfList, AC0.DecisionTree.build]
  | cons i rest ih =>
      have hfalse := ih (Core.extendSubcube β i false)
      have htrue := ih (Core.extendSubcube β i true)
      have hsetFalse :
          AC0.DecisionTree.setBit β i false =
            Core.extendSubcube β i false := rfl
      have hsetTrue :
          AC0.DecisionTree.setBit β i true =
            Core.extendSubcube β i true := rfl
      simpa [Core.trunkOfList, AC0.DecisionTree.build,
        AC0.DecisionTree.setBit, hsetFalse, hsetTrue, hfalse, htrue]

lemma canonicalTrunk_finRange_eq_full :
    Core.canonicalTrunk (n := params.n) (List.finRange params.n)
      = AC0.DecisionTree.full (n := params.n) := by
  classical
  have := canonicalTrunk_eq_decisionTree_build (params := params)
    (β := Core.canonicalBase params.n) (vars := List.finRange params.n)
  simpa [Core.canonicalTrunk, AC0.DecisionTree.full]
    using this

end TrunkScaffolding

section PerfectWitness

open Core

variable {params : AC0Parameters}

/--
  A deterministic AC⁰ witness extracted from the full decision tree on `n`
  variables.  The construction peels the canonical tree into a trunk consisting
  of the first `ℓ = min (log₂ (M+2)) n` variables and uniform tails handling the
  remaining `n - ℓ` queries.  The resulting certificate achieves zero
  approximation error while already satisfying the logarithmic trunk bound that
  the genuine multi-switching lemma will ultimately provide.
-/
noncomputable def perfectPartialWitness
    (F : Family params.n) :
    AC0PartialWitness params F := by
  classical
  -- Split the full list of variables into a logarithmic trunk and a tail.
  let ℓ := Nat.min (Nat.log2 (params.M + 2)) params.n
  have hℓ_le_log : ℓ ≤ Nat.log2 (params.M + 2) := Nat.min_le_left _ _
  have hℓ_le_n : ℓ ≤ params.n := Nat.min_le_right _ _
  let tailDepth := params.n - ℓ
  have add_trunk_tail : ℓ + tailDepth = params.n := Nat.add_sub_of_le hℓ_le_n
  let vars : List (Fin params.n) := List.finRange params.n
  let front : List (Fin params.n) := vars.take ℓ
  have front_len : front.length = ℓ := by
    simpa [front, vars, hℓ_le_n, Nat.min_eq_left] using List.length_take ℓ vars
  let suffix : List (Fin params.n) := vars.drop ℓ
  have suffix_len : suffix.length = params.n - ℓ := by
    simpa [suffix, vars] using List.length_drop ℓ vars
  -- Build the trunk as the canonical tree querying the front variables.
  let trunk : PDT params.n :=
    Core.trunkOfList (n := params.n) (Core.canonicalBase params.n) front
  have depth_trunk : PDT.depth trunk = ℓ := by
    simpa [trunk, front_len]
      using Core.depth_trunkOfList_base (n := params.n) (vars := front)
  -- Each tail is another canonical trunk over the remaining variables.
  let tails : ∀ β : Core.Subcube params.n, β ∈ PDT.leaves trunk → PDT params.n :=
    fun β _ => Core.trunkOfList (n := params.n) β suffix
  have tails_depth :
      ∀ β hβ, PDT.depth (tails β hβ) ≤ tailDepth := by
    intro β hβ
    have := Core.depth_trunkOfList (n := params.n) (vars := suffix) β
    simpa [tails, suffix, suffix_len] using (le_of_eq this)
  -- Refining the trunk with these tails reconstructs the full decision tree.
  have trunk_refined :
      PDT.refine trunk tails
        = Core.trunkOfList (n := params.n)
            (Core.canonicalBase params.n)
            (front ++ suffix) := by
    simpa [trunk, tails]
      using Core.refine_trunkOfList_append
        (n := params.n)
        (β := Core.canonicalBase params.n)
        (vars₁ := front)
        (vars₂ := suffix)
  have front_suffix : front ++ suffix = vars := by
    simpa [front, suffix, vars] using List.take_append_drop ℓ vars
  -- Package the data into a partial decision tree.
  let partialTree : Core.PartialDT params.n tailDepth :=
    { trunk := trunk
      tails := tails
      tail_depth_le := tails_depth }
  -- The realised tree coincides with the full decision tree on all variables.
  have realize_append :
      partialTree.realize =
        Core.trunkOfList (n := params.n) (Core.canonicalBase params.n)
          (front ++ suffix) := by
    simpa [partialTree, trunk_refined]
  have realize_trunk :
      partialTree.realize =
        Core.trunkOfList (n := params.n) (Core.canonicalBase params.n) vars := by
    simpa [front_suffix] using realize_append
  have hcanon :
      Core.trunkOfList (n := params.n) (Core.canonicalBase params.n) vars
        = AC0.DecisionTree.full (n := params.n) := by
    simpa [vars, Core.canonicalTrunk]
      using canonicalTrunk_finRange_eq_full (params := params)
  have realize_full :
      partialTree.realize = AC0.DecisionTree.full (n := params.n) :=
    realize_trunk.trans hcanon
  let baseCert := AC0.perfectCertificate (n := params.n) F
  have base_realize :
      baseCert.witness.realize = AC0.DecisionTree.full (n := params.n) := by
    simp [baseCert, AC0.perfectCertificate, Core.PartialDT.realize_ofPDT]
  -- Assemble the final AC⁰ witness.
  refine
    { level := ℓ
      tailDepth := tailDepth
      certificate :=
        { witness := partialTree
          depthBound := ℓ
          epsilon := 0
          trunk_depth_le := by
            change PDT.depth trunk ≤ ℓ
            exact (le_of_eq depth_trunk)
          selectors := baseCert.selectors
          selectors_sub := by
            intro f β hf hβ
            have hfull : β ∈ baseCert.witness.realize.leaves :=
              baseCert.selectors_sub hf hβ
            have hfull_full :
                β ∈ (AC0.DecisionTree.full (n := params.n)).leaves := by
              simpa [base_realize] using hfull
            simpa [realize_full] using hfull_full
          err_le := by
            intro f hf
            simpa using baseCert.err_le hf }
      depthBound_le_level := by simp
      level_le_log := hℓ_le_log
      depth_le := by
        have := params.depthBudget_bound
        simpa [tailDepth, add_trunk_tail, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
      epsilon_nonneg := by simp
      epsilon_le_inv := by
        have hden : (0 : Core.Q) < (params.n + 2 : Core.Q) := by
          exact_mod_cast (Nat.succ_pos (params.n + 1))
        have hnum : (0 : Core.Q) ≤ (1 : Core.Q) := by norm_num
        have := div_nonneg hnum (le_of_lt hden)
        simpa using this }

end PerfectWitness

/--
  Типкласс, фиксирующий наличие multi-switching свидетеля для семейства `F`.
  В отличие от прежнего кода, здесь мы явно отделяем интерфейс от источника
  данных: дальнейшие леммы будут зависеть только от существования экземпляра
  `HasMultiSwitchingWitness`, что упростит замену аксиом реальными доказательствами.
-/
class HasMultiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n) : Type where
  outcome : MultiSwitchingOutcome params F

/-- Получаем свидетеля из экземпляра класса `HasMultiSwitchingWitness`. -/
noncomputable def multiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n)
    [w : HasMultiSwitchingWitness params F] :
    MultiSwitchingOutcome params F :=
  w.outcome

  /--
    Statement-level multi-switching lemma (Servedio–Tan / Håstad).  At the
    moment we expose the explicit "perfect" witness built from the full decision
  tree on `n` variables.  This is enough to keep the shrinkage pipeline
  axiom-free; future work will replace this definition by the genuine
  multi-switching construction with quasi-polynomial bounds.
-/
noncomputable def MultiSwitchingLemma
    (params : AC0Parameters) (F : Family params.n) :
    MultiSwitchingOutcome params F :=
  ⟨perfectPartialWitness (params := params) F⟩

/--
  The auxiliary instance exposing the current multi-switching witness.  Once
  the actual lemma is formalised this instance will continue to work unchanged,
  merely picking up the stronger bounds.
-/
noncomputable instance instHasMultiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n) :
    HasMultiSwitchingWitness params F :=
  ⟨MultiSwitchingLemma params F⟩

end ThirdPartyFacts
end Pnp3
