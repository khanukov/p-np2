import ThirdPartyFacts.SwitchingLemma

/-!
  Smoke test for SwitchingLemma module
-/

namespace Pnp3
namespace Tests

open ThirdPartyFacts.SwitchingLemma
open Core

-- Проверяем, что определения доступны
#check canonicalDTDepth
#check Barcode
#check TraceStep
#check encode
#check decode
#check single_switching_bound
#check multi_switching_bound

end Tests
end Pnp3
