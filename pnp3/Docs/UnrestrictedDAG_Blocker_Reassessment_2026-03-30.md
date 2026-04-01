# Unrestricted DAG blocker reassessment (2026-03-30)

Status: **research-roadmap note** (not a proved Lean theorem).

This memo records a re-check of the current last-blocker formulation for
unrestricted DAGs in the `NP ⊄ PpolyDAG` program and explains why the mainline
should shift away from stable-restriction endpoints.

---

## 1) Re-checked literature-level facts we accept as roadmap constraints

We treat the following as the current high-level picture:

1. Hardness magnification for Gap-/approx-MCSP style problems supports
   "slightly-superlinear lower bound ⇒ breakthrough consequence" regimes.
2. A locality/localizability barrier exists for magnification techniques based
   on local/subcube/restriction style arguments; this is a serious design
   constraint for source theorems targeting unrestricted circuits/DAGs.
3. Strong unconditional progress via shrinkage / local-PRG methods is known for
   restricted models (e.g. formulas, branching programs, AC0 variants,
   comparator circuits), but this does **not** automatically transfer to
   unrestricted DAG/circuit lower bounds.
4. For unrestricted DAGs, endpoint theorems that are only
   "accepts a structured image/family" are typically too weak unless they carry
   additional global pseudorandomness / measure-transfer content.

Operational interpretation for this repository:

- locality-style Route-B (`stableRestrictionGoal`) remains mathematically useful
  as a formalized route, but should no longer be treated as the default
  "expected-to-close" final blocker for unrestricted DAGs;
- the expected final blocker should be **distributional/global**, not merely
  locality-preserving.

---

## 2) Why `∀z, D(G(z)) = 1` alone does not close the unrestricted-DAG blocker

If a source theorem yields only

```text
∀ z, D(G(z)) = 1,
```

this proves image acceptance but does not by itself force a contradiction with
small DAG solvers for Gap-MCSP. The missing ingredient is a quantitative bridge
from the image distribution to uniform (or an equivalent global hardness
certificate).

Concretely, one-shot contradiction needs all three parts simultaneously:

1. image supported on "easy" YES-side objects;
2. pseudorandomness / indistinguishability against small DAGs;
3. an independent upper bound on small-DAG acceptance under uniform for the same
   promise/gap regime.

Without (2), the accepted image may be large and entirely YES-consistent while
remaining compatible with small-DAG behavior on uniform inputs.

---

## 3) Candidate final blocker theorem shape (recommended)

A source theorem for unrestricted DAGs should look like an explicit
**easy-image pseudorandom distribution certificate**.

```lean
/-- Sketch only: final names/fields may differ. -/
structure EasyImagePRGAt (N sYes sNo : Nat) where
  μ            : Dist (Core.BitVec N)
  support_easy : ∀ x ∈ μ.support, CircuitSize x ≤ sYes
  fools_small  : ∀ D,
      dagSize D ≤ N^(1+η) →
      |Pr[x ~ μ, eval D x] - Pr[x ~ uniform, eval D x]| ≤ ε
```

Then the intended one-shot contradiction theorem is:

```lean
theorem noSmallDAG_of_EasyImagePRG
  (hμ : EasyImagePRGAt N sYes sNo)
  : ¬ ∃ D, SolvesGapMCSP D sYes sNo ∧ dagSize D ≤ N^(1+η)
```

This is the mathematically precise place where the final unrestricted-DAG gap
should be closed.

---

## 4) Architecture consequence for Lean mainline

### 4.1 What to demote

- Demote `DAGStableRestrictionCertificate` from "mainline final blocker" to
  "legacy/alternative route".
- Keep stable-restriction stack as reusable infrastructure, but stop treating it
  as the canonical last mile for unrestricted DAG separation.

### 4.2 What to promote

Promote one of the following global endpoints as primary:

1. `SmallDAGWitness -> AcceptedDistributionCertificateAt`
   (contains explicit closeness-to-uniform / pseudorandomness against small
   DAGs), or
2. `SmallDAGWitness -> MCLP/non-disjoint-promise certificate`
   followed by extraction of hitting-set / pseudorandom objects.

Both target global objects rather than local restriction invariants.

---

## 5) Practical validation policy (before claiming unrestricted progress)

1. First validate the new consumer on restricted models where PRG/hitting-set
   style methods are already known to succeed.
2. Require endpoint fields that explicitly encode distributional transfer
   (not only image acceptance).
3. Treat "distinguisher breaks PRG" as heuristic unless accompanied by a formal
   global theorem closing the promise/counting gap.
4. Keep variant boundaries explicit: total vs partial, promise shape,
   uniform vs nonuniform, restricted vs unrestricted models.

---

## 6) Current action items

1. Add a dedicated distributional consumer layer in Lean
   (`AcceptedDistributionCertificateAt`-style surface).
2. Refactor PRG-route wrappers so that they cannot terminate at
   image-acceptance-only statements.
3. Keep stable-restriction route buildable, but mark it as secondary fallback.
4. Use restricted-model instantiations as regression tests for the new global
   consumer stack before re-attacking unrestricted DAGs.
