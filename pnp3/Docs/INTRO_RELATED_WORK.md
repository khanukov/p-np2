# AC0 Intro / Related-Work Draft — Audit Status

Updated: 2026-08-17

The former paper-ready AC0 separation language is withdrawn. The repository
does not currently prove a standard AC0 lower bound through the pnp3 endpoint.

What is formalized is the narrower statement that
`SmallAC0ParamsPartial p` and `AC0EasyFamilyDataPartial params.ac0` are
inconsistent. The easy-family package assumes both AC0 realizability and a
cardinality at least `2^(2^n)`, while the parameter package supplies the
capacity upper bound. This contradiction is independent of solver correctness.

Any future literature discussion should distinguish that vacuity certificate
from genuine AC0 and AC0[p] lower bounds for MCSP in the cited literature.
Until a non-vacuous standard circuit-class interface and proof are supplied,
there is no AC0 theorem here to position as a research contribution.
