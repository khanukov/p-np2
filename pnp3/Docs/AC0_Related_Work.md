# AC0 Related Work — Endpoint Audit

Updated: 2026-08-17

The pnp3 zero-hypothesis endpoint is not comparable to published standard-AC0
lower bounds: its quantified `SmallAC0Solver_Partial` type contains an
inconsistent enriched easy-family payload. The contradiction follows from
`params` and `easyData` without using solver correctness.

Relevant genuine lower-bound literature includes:

- Cheraghchi, Kabanets, Lu, and Myrisiotis, “Circuit Lower Bounds for MCSP
  from Local Pseudorandom Generators,” ICALP 2019.
- Golovnev, Ilango, Impagliazzo, Kabanets, Kolokolova, and Tal, “AC0[p]
  Lower Bounds Against MCSP via the Coin Problem,” ICALP 2019.
- Ilango, “Constant Depth Formula and Partial Function Versions of MCSP are
  Hard,” FOCS 2020.

These papers are background only. The repository’s proved enriched-package
inconsistency must not be described as reproducing, strengthening, or newly
formalizing their standard complexity-class lower bounds.
