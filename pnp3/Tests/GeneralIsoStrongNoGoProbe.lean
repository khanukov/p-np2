import Models.Model_PartialMCSP
import Counting.CircuitCounting
import Tests.CircuitCountTraceBoundProbe

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongNoGoProbe

open Models
open Counting
open CircuitCountTraceBoundProbe

/-- L1 partial bridge: package the strict trace-image slack lemma under the
`GeneralIsoStrongNoGoProbe` namespace for downstream assembly. -/
theorem bounded_trace_card_lt_of_general_slack
    (p : GapPartialMCSPParams)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack :
      circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - D.card)) :
    ((circuitsOfSizeAtMost p.n p.sYES).image
      (traceCircuitOnRows
        ((Finset.univ \ D).attach)
        (fun a => a.1))).card
      < 2 ^ ((Finset.univ \ D).card) := by
  have hSlack' :
      circuitCountBound p.n (p.sNO - 1) < 2 ^ ((Finset.univ \ D).card) := by
    simpa [Finset.card_sdiff (Finset.subset_univ D)] using hSlack
  exact boundedSizeTrace_image_card_lt_of_slack p D hSlack'

end GeneralIsoStrongNoGoProbe
end Tests
end Pnp3
