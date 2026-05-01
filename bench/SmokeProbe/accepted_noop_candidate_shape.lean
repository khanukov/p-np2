/-!
# Smoke probe — accepted_noop_candidate_shape

Research Governance v0.1, PR 5.

This file is a positive control: a benign minimum that all currently-
shipped guards (PR 1, PR 2, PR 3, PR 3b, PR 4a) pass.  It lives
permanently in `bench/SmokeProbe/`; the smoke driver does NOT stage
it elsewhere.  Its expected result is `PASS_SHAPE_ONLY` — never
`accepted`.  Per `RESEARCH_CONSTITUTION.md` Rule 1, an `accepted`
status requires a closed `P_ne_NP_unconditional` term, which this
probe does not provide.

This file is NOT part of `lake build`.
-/

namespace Pnp3
namespace SmokeProbe

example : True := trivial

end SmokeProbe
end Pnp3
