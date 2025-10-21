import Core.BooleanBasics
import Core.SAL_Core
import Core.ShrinkageWitness
import Models.Model_GapMCSP
import ThirdPartyFacts.Facts_Switching
import ThirdPartyFacts.LeafBudget

/-!
  pnp3/Core/ShrinkageAC0.lean

  Усиление shrinkage-интерфейса: мы фиксируем модель, в которой к
  частичному PDT допускаются оракульные листья с ограниченным фанином.
  Такой формат соответствует «локальной» постановке из JACM'22 и позволяет
  явно контролировать параметр локальности при дальнейшем преобразовании
  в SAL-сценарий.
-/

namespace Pnp3
namespace Core

open Models
open ThirdPartyFacts

/--
  Параметры оракульного расширения: единственная величина, которая
  нам нужна, — это максимальный фанин `maxArity` для каждого оракульного
  узла.  В дальнейшем этот параметр будет ограничен полилогарифмом от
  размера входа.
-/
structure OracleParameters where
  maxArity : Nat
  deriving Repr

/--
  Свидетельство shrinkage для AC⁰ с оракульными листьями.  Мы храним
  обычный частичный сертификат (`base`) вместе с доказательством того,
  что глубина хвостов не превышает допустимый фанин `oracle.maxArity`.
  Дополнительно фиксируем верхнюю границу `oracle_le_polylog`, которая
  ограничивает фанин полилогарифмом от длины входа.
-/
structure OraclePartialWitness
    (params : AC0Parameters)
    (oracle : OracleParameters)
    (F : Family params.n) where
  base : AC0PartialWitness params F
  level_le_oracle : base.level ≤ oracle.maxArity
  oracle_le_polylog : oracle.maxArity ≤ polylogBudget (Nat.pow 2 params.n)

/-!
  Конструкция `OraclePartialWitness` больше не опирается на отдельную аксиому:
  мы производим её из внешнего факта `ac0PartialWitness`, а пользователь
  указывает необходимые числовые ограничения явно.  Такой подход подчёркивает,
  какие оценки потребуются на следующих шагах (например, полилогарифмический
  контроль фанина), и исключает зависимость части A от новых предположений.
-/
noncomputable def OraclePartialWitness.ofAC0
    (params : AC0Parameters)
    (oracle : OracleParameters)
    (F : Family params.n)
    (hlevel : (ac0PartialWitness params F).level ≤ oracle.maxArity)
    (horacle : oracle.maxArity ≤ polylogBudget (Nat.pow 2 params.n)) :
    OraclePartialWitness params oracle F :=
  { base := ac0PartialWitness params F
    , level_le_oracle := hlevel
    , oracle_le_polylog := horacle }

namespace OraclePartialWitness

variable {params : AC0Parameters}
variable {oracle : OracleParameters}
variable {F : Family params.n}

open ThirdPartyFacts

/--
  Оракульный свидетель порождает частичное дерево решений — это просто
  сертификат `AC0PartialWitness`.  Явное имя избавляет от постоянного
  обращения к полю `base.certificate` в последующих леммах.
-/
@[simp] noncomputable def certificate
    (W : OraclePartialWitness params oracle F) :
    PartialCertificate params.n W.base.level F :=
  W.base.certificate

/-- Ограничение на глубину хвостов: они не превосходят допустимый фанин. -/
lemma level_le_maxArity
    (W : OraclePartialWitness params oracle F) :
    W.base.level ≤ oracle.maxArity :=
  W.level_le_oracle

/-- Полилогарифмическая граница на фанин оракулов. -/
lemma oracle_le_polylogBudget
    (W : OraclePartialWitness params oracle F) :
    oracle.maxArity ≤ polylogBudget (Nat.pow 2 params.n) :=
  W.oracle_le_polylog

/--
  Любой хвост частичного дерева имеет глубину `≤ oracle.maxArity`.  Это прямое
  следствие ограничения на `base.level` и поля `tail_depth_le` сертификата.
-/
lemma tail_depth_le_maxArity
    (W : OraclePartialWitness params oracle F)
    {β : Subcube params.n}
    (hβ : β ∈ PDT.leaves W.certificate.witness.trunk) :
    PDT.depth (W.certificate.witness.tails β hβ) ≤ oracle.maxArity := by
  have htail := W.certificate.witness.tail_depth_le β hβ
  exact htail.trans W.level_le_oracle

/--
  Основной shrinkage-объект, ассоциированный с оракульным свидетелем.  Он
  заменяет каждую ссылку на частичный сертификат на конкретное PDT и списки
  листьев, пригодные для запуска SAL.
-/
@[simp] noncomputable def shrinkage
    (W : OraclePartialWitness params oracle F) : Shrinkage params.n :=
  Core.PartialCertificate.toShrinkage
    (n := params.n)
    (ℓ := W.base.level)
    (F := F)
    W.certificate

/-- Семейство функций в shrinkage совпадает с исходным списком `F`. -/
@[simp] lemma shrinkage_family
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).F = F := by
  classical
  --  Lean-линтер жаловался на `simpa`, хотя доказательство сводится к прямому
  --  применению вспомогательного факта.  Явное раскрытие `change` подчёркивает,
  --  что используется ровно лемма `toShrinkage_family`, и избавляет от шума.
  change (Core.PartialCertificate.toShrinkage
      (n := params.n) (ℓ := W.base.level) (F := F) W.certificate).F = F
  exact
    (Core.PartialCertificate.toShrinkage_family
      (n := params.n) (ℓ := W.base.level) (F := F) W.certificate)

/-- Формула для глубины построенного PDT: `depthBound + level`. -/
@[simp] lemma shrinkage_depth
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).t = W.certificate.depthBound + W.base.level := by
  classical
  --  Та же идея: линтер предлагал заменить `simpa`.  Явное `change` делает
  --  переписывание очевидным и оставляет доказательство ссылкой на базовую
  --  лемму `toShrinkage_depth`.
  change (Core.PartialCertificate.toShrinkage
      (n := params.n) (ℓ := W.base.level) (F := F) W.certificate).t
      = W.certificate.depthBound + W.base.level
  exact
    (Core.PartialCertificate.toShrinkage_depth
      (n := params.n) (ℓ := W.base.level) (F := F) W.certificate)

/-- Ошибка shrinkage совпадает с ошибкой частичного сертификата. -/
@[simp] lemma shrinkage_epsilon
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).ε = W.certificate.epsilon := by
  classical
  --  Аналогично, избавляемся от `simpa`, чтобы линтер не ругался, и явно
  --  используем подготовленную лемму из `PartialCertificate`.
  change (Core.PartialCertificate.toShrinkage
      (n := params.n) (ℓ := W.base.level) (F := F) W.certificate).ε
      = W.certificate.epsilon
  exact
    (Core.PartialCertificate.toShrinkage_epsilon
      (n := params.n) (ℓ := W.base.level) (F := F) W.certificate)

/--
  Глубина PDT из оракульного свидетеля наследует стандартную оценку
  `Nat.pow (log₂(M+2)) (d+1)`, полученную из факта `partial_shrinkage_for_AC0`.
-/
lemma shrinkage_depth_le
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).t ≤
      Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  classical
  have h := W.base.depth_le
  have heq := W.shrinkage_depth (params := params) (oracle := oracle) (F := F)
  exact heq.symm ▸ h

/--
  Более грубая, но полезная для быстрых оценок граница: глубина не превышает
  `depthBound + oracle.maxArity`.
-/
lemma shrinkage_depth_le_oracle
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).t ≤ W.certificate.depthBound + oracle.maxArity := by
  classical
  have hbound := Nat.add_le_add_left W.level_le_oracle W.certificate.depthBound
  have heq := W.shrinkage_depth (params := params) (oracle := oracle) (F := F)
  exact heq.symm ▸ hbound

/--
  Подставляем полилогарифмическую границу на фанин: глубина PDT, полученная из
  оракульного свидетеля, не превосходит `depthBound + polylogBudget (2^n)`.
  Эта оценка понадобится при переносе данных шага A в ёмкостные леммы шага B.
-/
lemma shrinkage_depth_le_polylog
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).t ≤
      W.certificate.depthBound + polylogBudget (Nat.pow 2 params.n) := by
  classical
  have hbase := shrinkage_depth_le_oracle
    (params := params) (oracle := oracle) (F := F) (W := W)
  have hmono :
      W.certificate.depthBound + oracle.maxArity ≤
        W.certificate.depthBound + polylogBudget (Nat.pow 2 params.n) := by
    exact Nat.add_le_add_left (oracle_le_polylogBudget (W := W)) _
  exact hbase.trans hmono

/-- Ошибка shrinkage неотрицательна, как и у исходного сертификата. -/
lemma shrinkage_error_nonneg
    (W : OraclePartialWitness params oracle F) :
    (0 : Q) ≤ (W.shrinkage).ε := by
  classical
  have h := W.base.epsilon_nonneg
  have heq := W.shrinkage_epsilon (params := params) (oracle := oracle) (F := F)
  exact heq.symm ▸ h

/-- Ошибка shrinkage ограничена `1 / (n + 2)`. -/
lemma shrinkage_error_le_inv
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).ε ≤ (1 : Q) / (params.n + 2) := by
  classical
  have h := W.base.epsilon_le_inv
  have heq := W.shrinkage_epsilon (params := params) (oracle := oracle) (F := F)
  exact heq.symm ▸ h

/--
  Из оценки `ε ≤ 1/(n+2)` немедленно следует привычное условие `ε ≤ 1/2`.
  Факт используется при применении энтропийных ограничений на семейства функций.
-/
lemma shrinkage_error_le_half
    (W : OraclePartialWitness params oracle F) :
    (W.shrinkage).ε ≤ (1 : Q) / 2 := by
  have h := shrinkage_error_le_inv (params := params) (oracle := oracle) (F := F)
    (W := W)
  exact ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
    params.n (ε := (W.shrinkage).ε) h

/-- Атлас, соответствующий оракульному свидетелю. -/
@[simp] noncomputable def atlas
    (W : OraclePartialWitness params oracle F) : Atlas params.n := by
  classical
  exact { dict := PDT.leaves W.shrinkage.tree
          , epsilon := W.shrinkage.ε }

/-- Построенный атлас корректно аппроксимирует семейство `F`. -/
lemma atlas_works
    (W : OraclePartialWitness params oracle F) :
    WorksFor W.atlas F := by
  classical
  letI : DecidableEq (Subcube params.n) := inferInstance
  have h := SAL_from_Shrinkage (n := params.n) (S := W.shrinkage)
  unfold WorksFor at h ⊢
  intro f hfF
  have hf_eq := congrArg (fun l : Family params.n => f ∈ l)
      (shrinkage_family (W := W))
  have hf_shrinkage : f ∈ W.shrinkage.F := by
    exact (Eq.mp hf_eq.symm) hfF
  obtain ⟨Rf, hsubset, herr⟩ := h f hf_shrinkage
  refine ⟨Rf, ?_, ?_⟩
  · change listSubset Rf (PDT.leaves W.shrinkage.tree)
    exact hsubset
  · change errU f Rf ≤ W.shrinkage.ε
    exact herr

/--
  После удаления дубликатов выбранных листьев ошибка аппроксимации не
  ухудшается.  Это непосредственно следует из универсальной леммы о
  `errU` из модуля `LeafBudget`.  Формулируем её здесь для удобного
  обращения к `OraclePartialWitness`.
-/
lemma selectors_dedup_error_le
    (W : OraclePartialWitness params oracle F)
    {f : BitVec params.n → Bool} (hf : f ∈ F) :
    errU f ((W.shrinkage.Rsel f).dedup) ≤ W.shrinkage.ε := by
  classical
  have hf' : f ∈ W.shrinkage.F := by
    simpa [shrinkage_family (W := W)] using hf
  have h :=
    (err_le_of_dedup (S := W.shrinkage) (f := f) hf')
  exact h

/--
  Очищенные списки листьев не превосходят по длине полный словарь PDT.
  Получаем равномерную границу `k`, применимую ко всем функциям семейства.
-/
lemma selectors_dedup_length_bound
    (W : OraclePartialWitness params oracle F) :
    ∃ k : Nat,
      k ≤ (PDT.leaves W.shrinkage.tree).length ∧
      ∀ {f : BitVec params.n → Bool},
        f ∈ F →
          ((W.shrinkage.Rsel f).dedup).length ≤ k := by
  classical
  obtain ⟨k, hk₁, hk₂⟩ :=
    (leaf_budget_from_shrinkage (S := W.shrinkage))
  refine ⟨k, hk₁, ?_⟩
  intro f hf
  have hf' : f ∈ W.shrinkage.F := by
    simpa [shrinkage_family (W := W)] using hf
  exact hk₂ hf'

/--
  Для любой функции семейства достаточно `2^{depthBound + oracle.maxArity}`
  листьев: сначала используем универсальный bound `≤ 2^{depth}` для PDT, а
  затем подставляем оценку глубины `depth ≤ depthBound + oracle.maxArity`.
-/
lemma selectors_dedup_length_le_pow_oracle
    (W : OraclePartialWitness params oracle F)
    {f : BitVec params.n → Bool} (hf : f ∈ F) :
    ((W.shrinkage.Rsel f).dedup).length ≤
      Nat.pow 2 (W.certificate.depthBound + oracle.maxArity) := by
  classical
  have hf' : f ∈ W.shrinkage.F := by
    simpa [shrinkage_family (W := W)] using hf
  have hbase :=
    (leaf_budget_le_pow_depth (S := W.shrinkage) (f := f) hf')
  have hdepth :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2)
      (shrinkage_depth_le_oracle (W := W))
  have hchain := hbase.trans hdepth
  exact hchain

/--
  Размер словаря атласа оценивается той же функцией, что и списки листьев:
  `|dict| ≤ 2^{depthBound + oracle.maxArity}`.
-/
lemma atlas_dict_length_le_pow_oracle
    (W : OraclePartialWitness params oracle F) :
    W.atlas.dict.length ≤
      Nat.pow 2 (W.certificate.depthBound + oracle.maxArity) := by
  classical
  have hleaves :=
    Core.leaves_count_bound (t := W.shrinkage.tree)
  have htree :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2)
      (Shrinkage.depth_le_depthBound (S := W.shrinkage))
  have hdepth :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2)
      (shrinkage_depth_le_oracle (W := W))
  have hchain := hleaves.trans (htree.trans hdepth)
  simpa [atlas]
    using hchain

/--
  Переписываем оценку через полилогарифмический бюджет `polylogBudget`.
  Чисто арифметический шаг: заменяем `oracle.maxArity` на его верхнюю границу.
-/
lemma atlas_dict_length_le_polylog
    (W : OraclePartialWitness params oracle F) :
    W.atlas.dict.length ≤
      Nat.pow 2
        (W.certificate.depthBound
          + polylogBudget (Nat.pow 2 params.n)) := by
  classical
  have hbase := atlas_dict_length_le_pow_oracle
    (params := params) (oracle := oracle) (F := F) (W := W)
  have hmono :
      W.certificate.depthBound + oracle.maxArity ≤
        W.certificate.depthBound
          + polylogBudget (Nat.pow 2 params.n) := by
    exact Nat.add_le_add_left
      (oracle_le_polylogBudget (W := W)) _
  have hpow :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hmono
  exact hbase.trans hpow

/--
  Та же полилогарифмическая оценка распространяется и на очищенные списки
  листьев для каждой функции семейства.
-/
lemma selectors_dedup_length_le_polylog
    (W : OraclePartialWitness params oracle F)
    {f : BitVec params.n → Bool} (hf : f ∈ F) :
    ((W.shrinkage.Rsel f).dedup).length ≤
      Nat.pow 2
        (W.certificate.depthBound
          + polylogBudget (Nat.pow 2 params.n)) := by
  classical
  have hbase := selectors_dedup_length_le_pow_oracle
    (params := params) (oracle := oracle) (F := F) (W := W)
    (f := f) hf
  have hmono :
      W.certificate.depthBound + oracle.maxArity ≤
        W.certificate.depthBound
          + polylogBudget (Nat.pow 2 params.n) := by
    exact Nat.add_le_add_left
      (oracle_le_polylogBudget (W := W)) _
  have hpow :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hmono
  exact hbase.trans hpow

end OraclePartialWitness

end Core
end Pnp3
