# L1 general iso-strong no-go — session 4 (codex53)

## 1. Executive verdict

RED_GENERAL_ISOSTRONG_REFUTED

## 2. What landed

- `Pnp3.Tests.GeneralIsoStrongNoGoProbe.isoStrong_conclusion_negative_general`

## 3. General route-level assembly status

The final general L1 route-level assembly is now landed: for any
`F : GapSliceFamilyEventually` and any per-slice DAG witness family
`hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))`,
we have a formal contradiction with `IsoStrongFamilyEventually F hInDag`.

Concretely, the theorem

- `isoStrong_conclusion_negative_general`

proves

- `¬ IsoStrongFamilyEventually F hInDag`.

So the general iso-strong route pattern is refuted at this probe layer.

## 4. Remaining blockers

None at L1 for this route-level theorem. The requested final assembly theorem
is present and kernel-checked.

## 5. Next action

close_isoStrong_route_pattern_refuted
