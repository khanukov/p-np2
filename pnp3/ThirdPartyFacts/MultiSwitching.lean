/--
  Главный модуль многоуровневой switching-леммы: подключает базовые определения
  (`Core`) и вспомогательные надстройки (например, работу с глобальными
  селекторами).  Постепенно мы будем выделять дополнительные компоненты
  `MultiSwitching.*`, чтобы упростить навигацию по коду и доказательствам.
-/
import Pnp3.ThirdPartyFacts.MultiSwitching.Core
import Pnp3.ThirdPartyFacts.MultiSwitching.SelectorPool

namespace Pnp3
namespace ThirdPartyFacts
namespace MultiSwitching

-- Этот файл служит точкой входа и сам по себе не содержит новых определений.
-- Все ключевые конструкции живут в подмодулях `Core` и `SelectorPool`.

end MultiSwitching
end ThirdPartyFacts
end Pnp3
