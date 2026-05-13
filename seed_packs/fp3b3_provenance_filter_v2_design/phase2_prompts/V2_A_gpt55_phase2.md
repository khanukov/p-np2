# Phase 2 prompt — fp3b3 V2-`V2_A_gpt55` Lean self-attack

You are formalising the Phase 2 self-attack of one direction of
`ProvenanceFilter_v2`.  Phase 1 (paper sketch) has been
operator-reviewed and approved **with changes** per
`seed_packs/fp3b3_provenance_filter_v2_design/reviews/V2_A_gpt55_review_gpt55.md`.

Your task: produce kernel-checked Lean theorems formalising the
Phase 2 obligations from the seed pack contract, with the reviewer's
required non-vacuity replacement.  Do **not** use parity as the
non-vacuity target unless you first change the filter constants or syntax in a
separately approved design round; for this Phase 2 prompt, the honest family is
`seededPrefixAnd`.

Pick `<YOUR-HANDLE>` (your initials, model name, etc.).

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN.

## 1. Required reading (in order)

1. The Phase 1 sketch:
   `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/Sketch.lean`.
2. The reviewer's report:
   `seed_packs/fp3b3_provenance_filter_v2_design/reviews/V2_A_gpt55_review_gpt55.md`.
   **Read the Risks section carefully** — the reviewer rejected the parity
   non-vacuity target and requires `seededPrefixAnd` instead.
3. `seed_packs/fp3b3_provenance_filter_v2_design/README.md` and
   `WORKER_PROMPT.md` — the contract.
4. The four obstructions:
   * `outputs/nogolog.jsonl::NOGO-000001` and
     `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`, especially
     `HardwiringObstruction`, `HardwiringGuard`, and
     `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance`;
   * `outputs/nogolog.jsonl::NOGO-000004` and
     `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2`;
   * `outputs/nogolog.jsonl::NOGO-000005` (scope correction);
   * `outputs/nogolog.jsonl::NOGO-000006` and
     `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean::adversaryFamily_v_arbpayload`
     plus witness in `Witness.lean`.
5. The fp3b4 meta-barrier (your filter must explicitly dodge it):
   * `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/SupportCardinalityOnly.lean`
     (`IsSupportCardinalityOnly`),
   * `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`
     (`support_cardinality_barrier`).
6. Filter under attack:
   `FP3Attempt.InSupportFunctionalDiversity` in
   `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`.

## 2. Concrete file layout and exact theorem names

Create files under
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`:

| File | Goal | Required names |
| ---- | ---- | -------------- |
| `Filter.lean` | Re-export / Lean-formalise the V2-A filter and helper counters. | `FormulaShape.notGateCount`, `FormulaShape.andGateCount`, `FormulaShape.orGateCount`, `FormulaShape.booleanGateCount`, `ProvenanceFilter_v2_V2_A_gpt55` |
| `NotSupportCardinalityOnly.lean` | Prove the filter dodges fp3b4's barrier. | `ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only` |
| `ExcludesOverbroad.lean` | Prove bounded-support hardwiring shapes are rejected. | `excludes_overbroad_V2_A` |
| `ExcludesPrefixAnd.lean` | Prove the NOGO-000004 prefix-AND witness is rejected. | `excludes_prefixAnd_V2_A` |
| `ExcludesArbitraryPayload.lean` | Prove the NOGO-000006 arbitrary `ttFormula` payload witness is rejected. | `excludes_arbitrary_payload_V2_A` |
| `ExcludesPrefixAnd.lean` or a small local helper file | Optional helper: gate counts of prefix-AND syntax. | e.g. `prefixAnd_orGateCount_eq_zero`, `prefixAnd_notGateCount_eq_zero` |
| `NonVacuity.lean` | Define and admit a specific honest family. | `seededPrefixAnd`, `seededPrefixAnd_language`, `seededPrefixAnd_witness`, `V2_A_admits_seededPrefixAnd` |
| `Survivor.lean` | Compose the obligations. | `ProvenanceFilter_v2_V2_A_gpt55_survives_known_obstructions` |

## 3. Required imports

Use only imports needed for each file, but expect to need these modules across
the Phase-2 set:

```lean
import Complexity.Interfaces
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Sketch
import Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly
import Magnification.AuditRoutes.SupportCardinalityBarrier.Barrier
import Magnification.AuditRoutes.FixedParamsProbe
import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2
import Magnification.AuditRoutes.LogWidthAdversary.Composition
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Family
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Composition
import Magnification.AuditRoutes.LogWidthAdversary.TTFormulaSizeBound
import Tests.FormulaSupportBoundsFalsifiabilityProbe
import Mathlib.Tactic
```

Also inspect and reuse existing lemmas where possible:

* `FP3b1.LogWidthAdversary.prefixAnd_support_card`;
* `FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2_support_card`;
* `ArbitraryLogWidthTT.adversaryFamily_v_arbpayload_support_card`;
* `SupportCardinalityBarrier.IsSupportCardinalityOnly` and
  `support_cardinality_barrier`;
* `FormulaCircuit.rename` and `ttFormula` from
  `Tests.FormulaSupportBoundsFalsifiabilityProbe`.

## 4. Mandatory theorem signatures

The exact signatures below are the required public surface.  You may add helper
lemmas with more convenient statements, but the listed names and theorem types
must compile.

### 4.1 `Filter.lean`

Keep the sketch as historical record; do not edit it.  In `Filter.lean`, either
import and re-export the sketch definition, or duplicate the same definition if
that proves cleaner for downstream imports.  The public names must be:

```lean
namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

namespace FormulaShape

def notGateCount {n : Nat} : FormulaCircuit n → Nat := by
  -- if duplicating rather than importing, provide the recursive definition

def andGateCount {n : Nat} : FormulaCircuit n → Nat := by
  -- recursive definition

def orGateCount {n : Nat} : FormulaCircuit n → Nat := by
  -- recursive definition

def booleanGateCount {n : Nat} (c : FormulaCircuit n) : Nat :=
  notGateCount c + andGateCount c + orGateCount c

end FormulaShape

open Pnp3.ComplexityInterfaces
open FormulaShape

def ProvenanceFilter_v2_V2_A_gpt55
    {L : Language} (w : InPpolyFormula L) : Prop :=
  (∀ B : Nat, ∃ n : Nat, B < (FormulaCircuit.support (w.family n)).card) ∧
  (∀ n : Nat,
    booleanGateCount (w.family n) ≤
      16 * (FormulaCircuit.support (w.family n)).card + 16) ∧
  (∀ n : Nat,
    FormulaCircuit.depth (w.family n) ≤
      8 * (FormulaCircuit.support (w.family n)).card + 8) ∧
  (∀ n : Nat,
    2 ≤ (FormulaCircuit.support (w.family n)).card →
      0 < orGateCount (w.family n) ∧ 0 < notGateCount (w.family n))

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
```

If importing the sketch gives these names directly, `Filter.lean` may simply
import the sketch and add helper lemmas; do not create a second incompatible
copy.

### 4.2 `NotSupportCardinalityOnly.lean`

```lean
theorem ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only :
    ¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
        @ProvenanceFilter_v2_V2_A_gpt55
```

Concrete strategy: exhibit two `InPpolyFormula` witnesses with the same support
cardinality profile and different filter outcomes.  Recommended pair:

* accepting witness: `seededPrefixAnd_witness` from `NonVacuity.lean`;
* rejecting witness: a full-support monotone prefix-AND family, e.g.
  `fullPrefixAnd_witness`, with support card `n` but no OR/NOT gates for
  `n ≥ 2`.

Both witnesses have support-cardinality profile `fun n => n` (up to small
length conventions; make both conventions identical at `n = 0, 1`).  The filter
separates them via OR/NOT presence, which is structural information beyond
support cardinality.

### 4.3 `ExcludesOverbroad.lean`

Use the strongest concrete statement Lean supports for the NOGO-000001 bounded
hardwiring shape.  The required public theorem is the general bounded-support
version:

```lean
theorem excludes_overbroad_V2_A
    {L : Pnp3.ComplexityInterfaces.Language}
    (w : Pnp3.ComplexityInterfaces.InPpolyFormula L)
    (hBounded : ∃ B : Nat,
      ∀ n : Nat,
        (Pnp3.ComplexityInterfaces.FormulaCircuit.support (w.family n)).card ≤ B) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55 w
```

Concrete strategy: unfold `ProvenanceFilter_v2_V2_A_gpt55`; the first conjunct
asserts unbounded support, contradicting `hBounded`.  If the existing
`HardwiringObstruction` witness can be made strict enough, add a corollary
specialized to it, but do not weaken or replace the required theorem above.

### 4.4 `ExcludesPrefixAnd.lean`

```lean
theorem excludes_prefixAnd_V2_A :
    ¬ ProvenanceFilter_v2_V2_A_gpt55
        Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
          .adversaryWitness_v_natlog2
```

Concrete strategy: use the support-cardinality theorem for
`adversaryFamily_v_natlog2` to choose a length with support at least `2`, then
show the concrete `prefixAnd` syntax has zero `orGateCount` and zero
`notGateCount`.  The filter's fourth conjunct then produces
`0 < 0` for OR or NOT.

### 4.5 `ExcludesArbitraryPayload.lean`

```lean
theorem excludes_arbitrary_payload_V2_A
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
    (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55
        (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
          .adversaryWitness_v_arbpayload F hF)
```

Concrete strategy: prove lower bounds on the V2-A syntactic counters for the
recursive `ttFormula` constructor.  Because `ttFormula` recursively builds

```lean
or (and (not input0) c0') (and input0 c1')
```

at every positive width, the OR/AND/NOT counts grow with the full decision-tree
syntax.  Combine that with
`ArbitraryLogWidthTT.adversaryFamily_v_arbpayload_support_card` to contradict
`booleanGateCount ≤ 16 * widthFn n + 16` at a large length.  Do not rely on the
existing upper size bound alone; V2-A needs a lower bound.

### 4.6 `NonVacuity.lean`

The honest family is **not parity**.  Use the review-approved replacement
`seededPrefixAnd`:

```lean
def seededPrefixAnd : (n : Nat) → Pnp3.ComplexityInterfaces.FormulaCircuit n

def seededPrefixAnd_language : Pnp3.ComplexityInterfaces.Language :=
  fun n x => Pnp3.ComplexityInterfaces.FormulaCircuit.eval (seededPrefixAnd n) x

def seededPrefixAnd_witness :
    Pnp3.ComplexityInterfaces.InPpolyFormula seededPrefixAnd_language

theorem V2_A_admits_seededPrefixAnd :
    ProvenanceFilter_v2_V2_A_gpt55 seededPrefixAnd_witness
```

Definition requirement:

```text
seededPrefixAnd(0) = true       -- or any fixed no-support convention
seededPrefixAnd(1) = x₀         -- keep conventions aligned with helper witnesses
seededPrefixAnd(n ≥ 2) = ((x₀ ∧ ¬x₁) ∨ (¬x₀ ∧ x₁)) ∧ x₂ ∧ ... ∧ xₙ₋₁
```

Proof obligations:

* support cardinality is `n` for all `n ≥ 2`, and unbounded overall;
* `booleanGateCount` is linear and below `16 * support + 16`;
* `FormulaCircuit.depth` is linear and below `8 * support + 8`;
* OR and NOT counts are positive whenever support card is at least two.

### 4.7 `Survivor.lean`

```lean
theorem ProvenanceFilter_v2_V2_A_gpt55_survives_known_obstructions :
    (¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
        @ProvenanceFilter_v2_V2_A_gpt55) ∧
    (∀ {L : Pnp3.ComplexityInterfaces.Language}
      (w : Pnp3.ComplexityInterfaces.InPpolyFormula L),
      (∃ B : Nat,
        ∀ n : Nat,
          (Pnp3.ComplexityInterfaces.FormulaCircuit.support (w.family n)).card ≤ B) →
        ¬ ProvenanceFilter_v2_V2_A_gpt55 w) ∧
    (¬ ProvenanceFilter_v2_V2_A_gpt55
        Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
          .adversaryWitness_v_natlog2) ∧
    (∀ (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
       (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F),
      ¬ ProvenanceFilter_v2_V2_A_gpt55
        (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
          .adversaryWitness_v_arbpayload F hF)) ∧
    ProvenanceFilter_v2_V2_A_gpt55 seededPrefixAnd_witness
```

Concrete strategy: assemble the previous public theorems.

## 5. Allowed scope

* New files under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`
  per §2 layout.
* `lakefile.lean` — append new modules.
* `pnp3/Tests/AuditRoutes_ProvenanceFilterV2_V2_A_gpt55_<YOUR-HANDLE>_Smoke.lean`
  (optional regression smoke).
* `outputs/attempts.jsonl` — append ONE entry on Phase 2 completion.
* `seed_packs/fp3b3_provenance_filter_v2_design/critic_reports/V2_A_gpt55_<YOUR-HANDLE>.md`
  — six-attack Critic report per `spec/critic_protocol.md`.

## 6. Forbidden

* Editing the Phase 1 sketch (it stays as historical record).
* Editing the reviewer's review document.
* Editing other directions' files.
* Editing existing JSONL ledger entries (Rule 9).
* Editing trust root, FP3b1/fp3b2/fp3b4 theorem bodies, the FP-3
  candidate filter, CL-0 predicates.
* `axiom`, `opaque`, `Fact`, typeclass-payload (Rule 16).
* `sorry`/`admit` (Rule 1).
* `pnp3/Candidates/`, `gap_from_*`, `SourceTheorem_*`, final endpoint,
  `ProvenanceFilter_v1` promotion.
* Promoting your v2 to "accepted" — survivor candidates ship here as audit
  artifacts; promotion is a separate post-Phase-2 PR.
* Wave 1 activation by force.

## 7. Direction-specific traps from review

* **Parity non-vacuity failure:** the original parity family likely violates the
  linear gate-count cap in tree syntax.  Use `seededPrefixAnd` instead.
* **Lower-bound burden for `ttFormula`:** existing artifacts emphasize support
  cardinality and upper size bounds.  V2-A needs lower bounds on its own gate
  counters for the concrete recursive `ttFormula` syntax.
* **Overbroad theorem ambiguity:** NOGO-000001 is about an overbroad provenance
  route and hardwiring witness shape, not necessarily a conveniently named
  strict `InPpolyFormula` witness with all needed support lemmas.  State the
  theorem at the strongest concrete level Lean supports without overclaiming;
  the required bounded-support theorem is mandatory.
* **Syntax sensitivity:** the filter does not semantically exclude concise
  adversarial payloads.  The formal statements must target the packaged
  `ttFormula`/`rename` witness from NOGO-000006.
* **Padding attacks:** a satisfying family can be made failing by adding
  redundant gates; conversely, a hardwiring family might be rewritten into a
  smaller mixed-gate syntax.  This does not refute the concrete exclusions but
  limits interpretation.
* **Kernel engineering:** proving same-support-cardinality witnesses for
  `¬ IsSupportCardinalityOnly` may require boilerplate `InPpolyFormula`
  packaging and polynomial bounds; keep witness families simple.

## 8. Output (exactly ONE of two)

### Outcome A — survivor candidate landed

Submit a unified diff or branch named
`worker/fp3b3/V2_A_gpt55_phase2_<YOUR-HANDLE>` with all §2 files plus lakefile
wiring, optional smoke, ledger append, and Critic report.

**Acceptance checklist:**

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` 17/17 + 12.b/c/d/e/f/g/h/j/k green.
- [ ] `rg "\bsorry\b|\badmit\b" -g"*.lean"
       pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`
      returns nothing.
- [ ] All seven theorem surfaces from §4 compile.
- [ ] `validate_jsonl.py` OK on both ledgers.
- [ ] Critic report classified `pass` per
      `spec/critic_protocol.md` §1–3.

### Outcome B — structured failure report

If Phase 2 reveals the candidate is structurally hopeless, ship a markdown
failure report at:

```text
seed_packs/fp3b3_provenance_filter_v2_design/failures/V2_A_gpt55_phase2_<YOUR-HANDLE>.md
```

Sections: what was attempted, where it broke (Lean errors verbatim), local vs
global obstruction, what the integrator must know.  A `global` obstruction
informs the operator that `V2_A_gpt55` is dead and saturates one of four
directions.

## 9. Begin

1. Pick `<YOUR-HANDLE>`.
2. Verify baseline.
3. Read §1 materials, especially the reviewer's Risks.
4. Start with `ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only` —
   it is the gating result.
5. Iterate through the remaining theorems in §4.
6. Compose `Survivor.lean`.
7. Write Critic report + ledger append.
8. Submit.

End of prompt.
