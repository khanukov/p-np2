# Phase 2 prompt — fp3b3 V2-C GPT55 Lean self-attack

You are formalising the Phase 2 self-attack of one direction of
`ProvenanceFilter_v2`.  Phase 1 (paper sketch) has been operator-reviewed and
approved-with-changes per:

```text
seed_packs/fp3b3_provenance_filter_v2_design/reviews/V2_C_GPT55_review_codex55c.md
```

Your task: produce kernel-checked Lean theorems formalising the Phase 2
obligations from the seed pack contract.  This is still an audit side track, not
mainline progress toward `P != NP`.

Preserve `<HANDLE>` as a placeholder where the actual Phase 2 engineer must pick
their own handle.

---

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN before making Phase 2 changes.

## 1. Required reading, in order

1. Phase 1 sketch:
   `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/Sketch.lean`.
2. Review report:
   `seed_packs/fp3b3_provenance_filter_v2_design/reviews/V2_C_GPT55_review_codex55c.md`.
   Read §6 risks carefully; they are mandatory traps to address.
3. Seed-pack contract:
   `seed_packs/fp3b3_provenance_filter_v2_design/README.md` and
   `seed_packs/fp3b3_provenance_filter_v2_design/WORKER_PROMPT.md`.
4. NOGO entries:
   * `outputs/nogolog.jsonl::NOGO-000001`;
   * `outputs/nogolog.jsonl::NOGO-000004`;
   * `outputs/nogolog.jsonl::NOGO-000005`;
   * `outputs/nogolog.jsonl::NOGO-000006`;
   * `outputs/nogolog.jsonl::NOGO-000007`.
5. fp3b4 support-cardinality barrier:
   * `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/SupportCardinalityOnly.lean`, especially
     `IsSupportCardinalityOnly`;
   * `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`, especially
     `support_cardinality_barrier`.
6. Existing adversary modules to reuse:
   * `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`, especially
     `FP3Attempt.InSupportFunctionalDiversity` and the NOGO-000001 fixed-slice probe material;
   * `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Family_NatLog2.lean`, especially
     `prefixAnd_size`, `logWidthNat`, and
     `Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2`;
   * `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean`, especially
     `adversaryFamily_v_arbpayload_support_card`;
   * `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Witness.lean`, especially
     `adversaryWitness_v_arbpayload`.

## 2. Concrete file layout

Create Phase 2 files under:

```text
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/
```

| File | Goal | Required theorem / definition surface |
| ---- | ---- | ---- |
| `Filter.lean` | Re-export or restate the Phase 1 filter | `ProvenanceFilter_v2_V2_C_GPT55` |
| `NotSupportCardinalityOnly.lean` | Prove the filter dodges fp3b4's barrier | `ProvenanceFilter_v2_V2_C_GPT55_not_support_cardinality_only` |
| `ExcludesOverbroad.lean` | Prove the filter rejects the NOGO-000001 fixed-slice hardwiring shape | `excludes_overbroad_V2_C_GPT55` |
| `ExcludesPrefixAnd.lean` | Prove the filter rejects the NOGO-000004/000005 prefix-AND family | `excludes_prefixAnd_V2_C_GPT55` |
| `ExcludesArbitraryPayload.lean` | Prove the filter rejects the NOGO-000006 all-essential arbitrary payload witness | `excludes_arbitrary_payload_V2_C_GPT55` |
| `NonVacuity.lean` | Prove the filter admits a specific honest family | `V2_C_GPT55_admits_orAll` |
| `Survivor.lean` | Compose the exclusions + non-vacuity for human Critic review | `ProvenanceFilter_v2_V2_C_GPT55_survives_known_obstructions` |

Also update `lakefile.lean` to include these modules.

## 3. Mandatory theorem signatures

Use these names exactly unless Lean namespace conflicts force a minimal fully
qualified adjustment.  Do not add `axiom`, `opaque`, `Fact`, `sorry`, `admit`,
or `native_decide`.

### 3.1 `Filter.lean`

Required imports should include the sketch or the dependencies needed to restate
it:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Sketch
```

Required surface:

```lean
namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_C_GPT55

open Pnp3.ComplexityInterfaces

-- Either re-use the sketch definition directly, or restate an identical
-- definition here if the build architecture requires it.
#check ProvenanceFilter_v2_V2_C_GPT55

end V2_C_GPT55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
```

### 3.2 `NotSupportCardinalityOnly.lean`

Required imports:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Filter
import Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly
```

Exact theorem signature:

```lean
theorem ProvenanceFilter_v2_V2_C_GPT55_not_support_cardinality_only :
    ¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
        @ProvenanceFilter_v2_V2_C_GPT55
```

Concrete strategy: exhibit two `InPpolyFormula` witnesses, possibly over simple
languages such as constant-false languages, with identical support-cardinality
profiles but different filter membership.  Good witness ideas:

* accepted side: a constant or OR-style family with bounded size increments and
  valid zero-extension;
* rejected side: same support cardinalities but formulas whose false-extension
  semantics intentionally disagree at one successor length, or formulas with
  unbounded duplicate-gate size jumps.

The proof must demonstrate that V2-C uses syntactic size and cross-length
semantics, not only support cardinality.

### 3.3 `ExcludesOverbroad.lean`

Required imports:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Filter
import Magnification.AuditRoutes.FixedParamsProbe
import Models.Model_PartialMCSP
import Tests.FormulaSupportBoundsFalsifiabilityProbe
```

Exact theorem signature to implement:

```lean
theorem excludes_overbroad_V2_C_GPT55
    (p : Pnp3.Models.GapPartialMCSPParams)
    (w : Pnp3.ComplexityInterfaces.InPpolyFormula
        (Pnp3.Models.gapPartialMCSP_Language p))
    (hFamily :
      w.family =
        (fun m =>
          if hm : m = Pnp3.Models.partialInputLen p then
            (hm ▸
              (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula
                (Pnp3.Models.gapPartialMCSP_Language p
                  (Pnp3.Models.partialInputLen p))) :
              Pnp3.ComplexityInterfaces.FormulaCircuit m)
          else
            Pnp3.ComplexityInterfaces.FormulaCircuit.const false)) :
    ¬ ProvenanceFilter_v2_V2_C_GPT55 w
```

This theorem targets the concrete fixed-slice hardwiring family described in
NOGO-000001: a truth-table formula at `partialInputLen p` and `const false` at
every other length.  If the exact `ttFormula` namespace differs after imports,
adjust only the qualification, not the theorem name or mathematical content.
Do not claim that every possible `OverbroadUniformProvenance` object is rejected;
that assumption is too broad to determine a unique witness.

### 3.4 `ExcludesPrefixAnd.lean`

Required imports:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Filter
import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2
```

Exact theorem signature:

```lean
theorem excludes_prefixAnd_V2_C_GPT55 :
    ¬ ProvenanceFilter_v2_V2_C_GPT55
        Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1
          .LogWidthAdversary.adversaryWitness_v_natlog2
```

Concrete strategy: use a width-increase length for `logWidthNat`.  At such a
length, `prefixAnd` at `n+1` reads one more prefix coordinate than `prefixAnd` at
`n`.  Choose an old input whose old prefix window is all true but whose newly
included prefix coordinate is false.  This contradicts V2-C's zero-extension
identity.  Do not rely only on size increments for this exclusion.

### 3.5 `ExcludesArbitraryPayload.lean`

Required imports:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Filter
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Family
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness
```

Exact theorem signature:

```lean
theorem excludes_arbitrary_payload_V2_C_GPT55
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
    (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F) :
    ¬ ProvenanceFilter_v2_V2_C_GPT55
        (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
          .adversaryWitness_v_arbpayload F hF)
```

Concrete strategy: make the all-essential / width-increase argument primary.
When `widthFn` increases from `k` to `k+1`, the length-`n+1` truth-table formula
depends essentially on a fresh prefix coordinate that the length-`n` formula did
not read.  The V2-C zero-extension map sets only the final ambient coordinate to
`false`; it does not erase that fresh prefix coordinate.  Use all-essentiality to
construct two old inputs that should be indistinguishable to the old formula but
distinguished by the new formula, contradicting the zero-extension law.

Do not claim that bounded size increment is an edit-distance theorem.  It is
only a size recurrence.

### 3.6 `NonVacuity.lean`

Required imports:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Filter
```

Define a concrete OR-of-all-inputs family.  Exact required public surfaces:

```lean
def orAllFormula (n : Nat) : Pnp3.ComplexityInterfaces.FormulaCircuit n

def orAllLanguage : Pnp3.ComplexityInterfaces.Language :=
  fun n x => Pnp3.ComplexityInterfaces.FormulaCircuit.eval (orAllFormula n) x

def orAll_witness : Pnp3.ComplexityInterfaces.InPpolyFormula orAllLanguage

theorem V2_C_GPT55_admits_orAll :
    ProvenanceFilter_v2_V2_C_GPT55 orAll_witness
```

The final Lean file must contain real definitions/proofs, not the placeholders
above.  Prove:

* `orAllFormula (n+1)` at `(x,false)` evaluates to `orAllFormula n` at `x`;
* `FormulaCircuit.size (orAllFormula (n+1)) ≤ FormulaCircuit.size (orAllFormula n) + δ`
  for a fixed small `δ`;
* `orAll_witness` has a polynomial size bound.

### 3.7 `Survivor.lean`

Required imports:

```lean
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.NotSupportCardinalityOnly
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.ExcludesOverbroad
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.ExcludesPrefixAnd
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.ExcludesArbitraryPayload
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.NonVacuity
```

Required theorem name:

```lean
theorem ProvenanceFilter_v2_V2_C_GPT55_survives_known_obstructions :
    True
```

A stronger structured conjunction is welcome if it remains clean and does not
introduce any axioms or opaque packaging.  At minimum, this file must import and
`#check` all required theorem surfaces so build drift is caught.

## 4. Allowed scope

* New files under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/` listed above.
* `lakefile.lean` — append the new modules.
* Optional smoke test under `pnp3/Tests/`.
* On Phase 2 completion only, append one `outputs/attempts.jsonl` entry if the
  worker contract requires it.
* Critic report at
  `seed_packs/fp3b3_provenance_filter_v2_design/critic_reports/V2_C_GPT55_<HANDLE>.md`.

## 5. Forbidden

* Editing the Phase 1 sketch.
* Editing this review prompt or the review document.
* Editing other V2 directions.
* Editing existing JSONL ledger entries.
* Touching trust root.
* Editing fp3b1/fp3b2/fp3b4 theorem bodies, the FP-3 candidate filter, or CL-0 predicates.
* Adding `axiom`, `opaque`, `Fact`, typeclass-payload shortcuts, `sorry`, `admit`, or `native_decide`.
* Creating `pnp3/Candidates/` artifacts.
* Adding `gap_from_*`, `SourceTheorem_*`, final endpoint, or accepted-filter promotion.
* Activating Wave 1 by force.

## 6. Direction-specific traps from review

* **True-slice payload risk:** zero-extension only controls `(x, false)`.  Payload on `(x, true)` may accumulate over lengths; Phase 2 must either exclude it or report a structured failure.
* **Size recurrence is not edit distance:** `size (n+1) ≤ size n + δ` does not mean `family (n+1)` was obtained from `family n` by a bounded local edit.
* **NOGO-000001 theorem-shape risk:** an overbroad provenance assumption may not determine a unique witness.  Target the concrete fixed-slice witness or state a precise local lemma.
* **All-essential proof burden:** excluding arbitrary payload should rely on all-essentiality at width-increase lengths and must handle the fact that the fresh log-width coordinate is not the final ambient coordinate.
* **Kernel plumbing risk:** OR non-vacuity is simple mathematically but still needs careful `Fin` casts for the zero-extension identity.
* **Vacuity/circularity risk:** do not strengthen the filter in Phase 2 to exclude everything, and do not add opaque provenance/certification fields.

## 7. Output: exactly one of two outcomes

### Outcome A — survivor candidate landed

Submit a branch/diff named:

```text
worker/fp3b3/V2_C_GPT55_phase2_<HANDLE>
```

It must contain all seven files, lakefile wiring, optional smoke test, Phase 2
Critic report, and any append-only ledger entry required by the worker contract.

Acceptance checklist:

* `lake build PnP3 Pnp4` green.
* `./scripts/check.sh` green.
* `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/` returns nothing.
* All seven theorem surfaces above compile.
* JSONL validation is green if a ledger append is made.
* Critic report is classified `pass` under `spec/critic_protocol.md`.

### Outcome B — structured failure report

If Phase 2 reveals the candidate is structurally hopeless, ship:

```text
seed_packs/fp3b3_provenance_filter_v2_design/failures/V2_C_GPT55_phase2_<HANDLE>.md
```

Sections: what was attempted, where it broke (Lean errors verbatim), local vs
global obstruction, and what the integrator must know.

## 8. Begin

1. Pick `<HANDLE>`.
2. Verify baseline.
3. Start with `ProvenanceFilter_v2_V2_C_GPT55_not_support_cardinality_only`.
4. Then prove the three exclusions.
5. Prove OR non-vacuity.
6. Compose `Survivor.lean`.
7. Write Critic report and any permitted append-only ledger entry.
8. Submit.

End of prompt.
