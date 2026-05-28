# How to finish the unconditional proof? What is actually missing right now?

Updated: 2026-05-28.

Route policy (canonical lock):
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Short, honest answer

**Fully unconditional — not yet, not everything is in place.**

The important branching is:

1. **Conditionally, `ComplexityInterfaces.NP_not_subset_PpolyDAG` is already
   derivable** (via the existing wrappers), provided you supply the missing
   source payload.
2. **Unconditionally, `ComplexityInterfaces.NP_not_subset_PpolyDAG` is not
   yet derivable**, because the active tree still has no internal,
   theorem-level source for that payload free of external assumptions.

The public surface is now reduced to a single honest frontier object:
`ResearchGapWitness`.  To obtain a truly zero-argument final theorem, this
witness must be proved inside
`pnp3/Magnification/UnconditionalResearchGap.lean`.

---

## What is already in place

### 1) Interface-level definition of the target

`ComplexityInterfaces.NP_not_subset_PpolyDAG` is already defined at the
interface layer as the proposition `∃ L, NP L ∧ ¬ PpolyDAG L`.

### 2) Working endpoint theorems with explicit input hypotheses

The branch carries endpoint theorems under the Research Constitution
Rule 6 audit / quarantine prefixes:

- `RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptotic_blocker`
  (asymptotic route; consumes the refuted `MagnificationAssumptions`);
- `AuditOnly_NP_not_subset_PpolyDAG_final_of_blocker_TM`
  (concrete `_TM` route; compatibility wrapper).

So the wiring from a source hypothesis to the final DAG separation is
present, but it is explicitly marked as not-a-claim at the name level.

### 3) Why the current public final is still not unconditional

`P_ne_NP_final` currently takes a single meaningful argument:

- `gap : ResearchGapWitness`.

This witness contains exactly the remaining mathematical debt:
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

The old multiswitching / asymptotic route is still retained, but now
under the explicit `RefutedRoute_*` audit prefix:

- `RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D`,
- `RefutedRoute_P_ne_NP_final_of_multiswitchingData hMS D`.

`D` already packages both the asymptotic slice source and the
TM-witness for NP-membership, so `hNPbridge : AsymptoticNPPullback ...`
is no longer a public input even on the legacy mainline route.

The historical bundle argument `hMag : MagnificationAssumptions` is
moved into the compatibility wrapper
`RefutedRoute_P_ne_NP_final_of_magnification` (with the explicit
quarantine prefix) and is no longer a blocker on the default route.

Intermediate closure steps still exist, but they no longer masquerade
as the final unconditional API.  If they route through a refuted
support-bounds surface, they remain compatibility / audit plumbing.

---

## What exactly is missing for the unconditional final

For `NP_not_subset_PpolyDAG`, the public route in the active tree is
now closed against a single frontier object:
`NP_not_subset_PpolyDAG_final gap`,
where `gap : ResearchGapWitness`.

Legacy compatibility routes such as
`RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D`
and `RefutedRoute_NP_not_subset_PpolyDAG_final_of_magnification hMag`
are retained for audit and backward compatibility but are not counted
as unconditional progress — the quarantine prefix makes that visible
at the name level.

The old DAG-side audit route closes like this:

1. on the canonical threshold slice, any `PpolyDAG` witness is
   converted into a `PpolyFormula` witness;
2. the support bounds come from `hMS`;
3. the already-closed fixed-slice collapse consumer then fires.

The principal remaining debt before unconditional `P_ne_NP` is now
localised in one field:

```text
ResearchGapWitness.dagSeparation :
  ComplexityInterfaces.NP_not_subset_PpolyDAG
```

At a lower level, this may be proved through a new formula / locality
source theorem, but such a theorem must:

1. not use the refuted
   `FormulaSupportBoundsFromMultiSwitchingContract`;
2. not reinstate the old false
   `FormulaSupportRestrictionBoundsPartial`;
3. avoid truth-table hardwiring and singleton / per-formula AC0
   provenance;
4. yield a genuine `ComplexityInterfaces.NP_not_subset_PpolyDAG`.

Technical progress on this point: `P_ne_NP_final` and
`NP_not_subset_PpolyDAG_final` no longer accept `hMS`, `hAsym`,
`hNPbridge`, or `D` directly.  Those surfaces survive only as
compatibility / audit wrappers.

The final `ResearchGapWitness` port is method-agnostic.  An algebraic,
spectral, finite-field, SOS, or Fourier-analytic proof of
`NP_not_subset_PpolyDAG` plugs in at the same point; it does not have
to produce support sets, AC0 provenance, random restrictions, or
`AcceptedFamilyCertificateAt`.

---

## Can `ComplexityInterfaces.NP_not_subset_PpolyDAG` be proved at least
   conditionally right now?

### Yes — **conditionally on the current set of hypotheses**

That is exactly what the honest frontier endpoint does:

- `NP_not_subset_PpolyDAG_final gap` yields
  `ComplexityInterfaces.NP_not_subset_PpolyDAG`;
- `P_ne_NP_final gap` immediately yields
  `ComplexityInterfaces.P_ne_NP`.

The old audit route is still conditional too (and now under the
`RefutedRoute_` prefix, as befits a quarantined wrapper):

- `RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D`,
- `RefutedRoute_P_ne_NP_final_of_multiswitchingData hMS D`.

### No — **unconditionally, right now**

Because the active tree still has no internal, zero-argument theorem
that itself constructs / eliminates the remaining assumption payload.

---

## Note on the auditor's verdict (current branch posture)

Yes, the general direction of the auditor is correct: the literal
fixed-slice route is not a working path to unconditional closure and
must be treated as a no-go branch.

Important clarification for the active branch: the no-go applies to the
historical fixed-slice support-half / blocker hunt.  The currently
closed DAG route is different: it uses the fixed-slice `DAG → Formula`
bridge on the threshold slice and does not resurrect the old
support-half branch.

---

## Minimal closure plan (in practice)

1. Keep `pnp3/Magnification/UnconditionalResearchGap.lean` as the
   single file in which the breakthrough is expected to appear.
2. Prove `ResearchGapWitness` without using refuted support-bounds
   surfaces.
3. After that, expose the zero-argument theorem:
   `P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP`.

### Practical sequencing (what to do right now)

1. **First prove a non-vacuous source theorem**: it should yield
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`, or a sufficient
   lower-level theorem from which it follows.
2. **Then construct `ResearchGapWitness` inside
   `UnconditionalResearchGap.lean`**.
3. **Only then** enable the commented template
   `P_ne_NP_unconditional`.

---

## Definition of done (to honestly say "unconditional")

All of the following must hold simultaneously:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` is proved inside the
   tree, without an external DAG input.
2. The public final does not require an external class-level
   `NP_not_subset_PpolyDAG`.
3. The public final does not require an external assumption payload.
4. A zero-argument theorem `P_ne_NP_unconditional` is derived in the
   active branch.
5. `./scripts/check.sh` and the audit tests pass without special
   provider stubs.
