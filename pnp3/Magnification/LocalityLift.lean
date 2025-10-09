import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Core.BooleanBasics
import LowerBounds.AntiChecker
import Models.Model_GapMCSP
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/Magnification/LocalityLift.lean

  Этот модуль содержит абстрактный интерфейс «Locality-Lift»: из гипотезы о
  существовании небольшого (в общем смысле) решателя GapMCSP и малого
  тест-набора `T` строится решатель в модели локальных схем.  Реализация этой
  леммы будет происходить за пределами Lean; здесь мы фиксируем лишь точную
  сигнатуру, чтобы остальные части цепочки A→B→C могли обращаться к ней как к
  готовому факту.
-/

namespace Pnp3
namespace Magnification

open Models
open LowerBounds

/--
  Параметры общего (неограниченного) решателя: храним число входов `n`,
  размер схемы `size` и глубину `depth`.  Этой информации достаточно, чтобы
  контролировать перенос параметров в локальную модель.
-/
structure GeneralCircuitParameters where
  n     : Nat
  size  : Nat
  depth : Nat
  deriving Repr

/--
  Гипотеза о существовании малого общего решателя для GapMCSP.  Как и в
  остальных оболочках (`SmallAC0Solver`, `SmallLocalCircuitSolver`), мы
  фиксируем только параметры, не вдаваясь в реализацию схемы.
-/
structure SmallGeneralCircuitSolver (p : GapMCSPParams) where
  params : GeneralCircuitParameters
  same_n : params.n = inputLen p
  deriving Repr

/--
  Формализация шага Locality-Lift: из общего решателя и тест-набора `T`
  получаем локальный решатель сопоставимых размеров.  Точные зависимости
  между параметрами вынесены в виде неравенств.  Факт будет обоснован в
  математической части; здесь он оформлен как аксиома для дальнейших модулей.
-/
axiom locality_lift
  {p : GapMCSPParams}
  (general : SmallGeneralCircuitSolver p) :
    ∃ (T : Finset (Core.BitVec (inputLen p)))
      (loc : SmallLocalCircuitSolver p),
        T.card ≤ Models.polylogBudget (inputLen p) ∧
        loc.params.M ≤ general.params.size * (T.card.succ) ∧
        loc.params.ℓ ≤ Models.polylogBudget (inputLen p) ∧
        loc.params.depth ≤ general.params.depth

end Magnification
end Pnp3
