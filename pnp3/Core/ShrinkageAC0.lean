import Core.BooleanBasics
import Core.SAL_Core
import Core.ShrinkageWitness
import Models.Model_GapMCSP
import ThirdPartyFacts.Facts_Switching

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

/--
  Внешний факт оформляем в виде тайпкласса: наличие экземпляра
  `HasOraclePartialWitness` гарантирует существование оракульного shrinkage-
  свидетельства с указанными численными границами.  Это устраняет явную
  аксиому и делает зависимости от внешних результатов прозрачными для
  последующих модулей.
-/
class HasOraclePartialWitness
    (params : AC0Parameters)
    (oracle : OracleParameters)
    (F : Family params.n) : Type where
  /-- Оракульное shrinkage-свидетельство для семейства `F`. -/
  witness : OraclePartialWitness params oracle F

/-- Извлекаем оракульное shrinkage-свидетельство из тайпкласса. -/
noncomputable def oraclePartialWitness
    (params : AC0Parameters)
    (oracle : OracleParameters)
    (F : Family params.n)
    [w : HasOraclePartialWitness params oracle F] :
    OraclePartialWitness params oracle F :=
  w.witness

/-- Проекция: получаем обычный частичный сертификат из оракульного свидетеля. -/
noncomputable def oracleWitnessCertificate
    {params : AC0Parameters}
    {oracle : OracleParameters}
    {F : Family params.n}
    (W : OraclePartialWitness params oracle F) :
    PartialCertificate params.n W.base.level F :=
  W.base.certificate

/-- Ограничение на глубину хвостов: они не превосходят допустимый фанин. -/
lemma oracleWitness_level_le_maxArity
    {params : AC0Parameters}
    {oracle : OracleParameters}
    {F : Family params.n}
    (W : OraclePartialWitness params oracle F) :
    W.base.level ≤ oracle.maxArity :=
  W.level_le_oracle

/-- Полилогарифмическая граница на фанин оракулов. -/
lemma oracleWitness_polylog_bound
    {params : AC0Parameters}
    {oracle : OracleParameters}
    {F : Family params.n}
    (W : OraclePartialWitness params oracle F) :
    oracle.maxArity ≤ polylogBudget (Nat.pow 2 params.n) :=
  W.oracle_le_polylog

end Core
end Pnp3
