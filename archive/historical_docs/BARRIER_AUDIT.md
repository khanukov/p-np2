# Barrier Audit (PNP3)

Date: 2026-02-22

This note separates:

1. what is already machine-checked in the current codebase;
2. what is not yet formalized and therefore must not be claimed as proved.

## 1. Locality route: formally explicit in Lean

The active formula-track contradiction is explicitly locality-based:

- `pnp3/Tests/BarrierAudit.lean`:
  - `locality_contradiction_from_provider_witness`
  - `locality_contra_np_to_formula`
- `pnp3/Magnification/Facts_Magnification_Partial.lean`:
  - `OPS_trigger_formulas_partial_of_provider_formula_separation`
- `pnp3/LowerBounds/AntiChecker_Partial.lean`:
  - `noSmallLocalCircuitSolver_partial_v2`
- `pnp3/ThirdPartyFacts/PartialLocalityLift.lean`:
  - `locality_lift_partial`

Interpretation: in the current formal pipeline, any strict formula witness is
pushed through a structured locality provider to a local solver, and then ruled
out by `noSmallLocalCircuitSolver_partial_v2`.

## 2. Classical barriers: current formal status

For the three classical barriers (relativization, natural proofs, algebrization):

- there is currently no dedicated formal interface in `pnp3/` encoding these
  barrier notions;
- therefore there is no theorem in the repository that can be read as a formal,
  machine-checked "bypass certificate" for these three barriers.

So statements like "the project already formally bypasses natural proofs" are
currently too strong.

## 3. About the "naturality via AC0" idea

`AC0`/multi-switching facts in this repository currently play a different role:

- they provide witness/certificate pipelines used to derive formula-track lower
  bounds and locality extraction;
- by themselves they do **not** formalize Razborov-Rudich conditions
  (constructivity + largeness + usefulness against `P/poly`) nor a theorem that
  these conditions are violated.

Hence, at this stage, "naturality is bypassed by AC0" can be used only as an
informal research hypothesis, not as a formalized claim.

## 4. Next formalization target (to remove ambiguity)

To make barrier claims explicit in code, dedicated interface modules are now
present:

1. `pnp3/Barrier/Relativization.lean`
- oracle-parametric notion `Relativizing`;
- witness type `RelativizationBypassWitness`.

2. `pnp3/Barrier/NaturalProofs.lean`
- explicit triad interface (constructive / large / useful);
- witness type `NaturalProofBypassWitness`.

3. `pnp3/Barrier/Algebrization.lean`
- oracle-family invariance notion `Algebrizing`;
- witness type `AlgebrizationBypassWitness`.

4. `pnp3/Barrier/Bypass.lean`
- wrapper theorems that make barrier obligations explicit parameters of final
  statements (`..._with_barriers`).

At the current stage, the safe claim remains:

- locality-based contradiction is formalized;
- classical barrier-bypass claims are not yet formalized.
