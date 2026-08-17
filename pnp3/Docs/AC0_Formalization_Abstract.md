# AC0 Formalization Abstract — Withdrawn Claim

Updated: 2026-08-17

The earlier candidate abstract described the zero-hypothesis endpoint as an
AC0 lower-bound formalization. That description exceeded the proved statement
and is withdrawn.

The machine-checked result is a vacuity audit: `SmallAC0Solver_Partial`
contains a `SmallAC0ParamsPartial` value and an `AC0EasyFamilyDataPartial`
value, and those two projections already imply `False`. The proof does not use
the package’s solver correctness, semantic decider, circuit, or circuit
correctness equation.

Accordingly, this material may be described only as a formal audit of an
inconsistent enriched easy-family package. It must not be presented as a
formalization of `Partial-MCSP ∉ AC0`, as a new restricted-circuit lower
bound, or as progress toward `P != NP`.
