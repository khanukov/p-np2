# Parameter chase for step C

Global checklist for unconditional `P ≠ NP`:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

Working numerical note for step C.  This is not the source of the
global project status: the final status is recorded in `STATUS.md` and
`TODO.md`.

This note collects the numerical ranges used to keep parts A–C
consistent with each other.

- `polylogBudget N = (log₂(N+1)+1)^4` — the base budget bounding the
  anti-checker test sets.  Applied for Partial MCSP (`N = 2^n`) and for
  sparse languages (`N = n`).
- For the SAL scenario with parameters `(dictLen, k)`, the test-set
  capacity is `unionBound dictLen k * 2^{|T|}`.  This is exactly the
  quantity compared with the size of the family `Y` in the lemma
  `no_bounded_atlas_on_testset_of_large_family`.
- The oracle parameters from `Core.OraclePartialWitness` satisfy two
  conditions: the depth of the partial tree tails does not exceed
  `maxArity`, and `maxArity` itself is bounded by
  `polylogBudget (2^n)`.
- The Locality-Lift preserves the same budgets: the anti-checker test
  sets stay bounded by `polylogBudget (2^n)`, and the size of the local
  circuit only grows by a multiplicative factor of `|T|+1`.  Hence a
  prohibition on local circuits immediately transfers to a prohibition
  on general circuits (see `general_statement_from_locality` in the
  partial-track bridges).

Pinning the parameters this way guarantees that all the estimates we
use stay within the `2^{o(N)}` regime and remain compatible with the
hypotheses of CJW'22 and OPS'19.
