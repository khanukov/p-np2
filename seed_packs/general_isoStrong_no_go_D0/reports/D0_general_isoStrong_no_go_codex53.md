Task: general iso-strong no-go D0
Handle: codex53
Branch: main
Commit before: UNCOMMITTED
Commit after: UNCOMMITTED
Changed files:
- seed_packs/general_isoStrong_no_go_D0/README.md
- seed_packs/general_isoStrong_no_go_D0/WORKER_PROMPT_D0.md
- seed_packs/general_isoStrong_no_go_D0/reports/.gitkeep
- seed_packs/general_isoStrong_no_go_D0/failures/.gitkeep
- seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md

Outcome:
  REPORT_LANDED

Executive verdict:
  NEEDS_LEAN_PROBE

General theorem plausible:
  unclear

Key blocker:
  No existing general theorem that turns the broad YES-side (circuits of size ≤ sYES)
  into a finite trace family cardinality bound matching `F.Mof n (F.Tof n β)`.

Recommended next action:
  open_circuit_count_trace_bound_L0

Commands run:
  - ./scripts/check.sh → status: PASS

Scope violations:
  none

---

## 1. Executive verdict

**NEEDS_LEAN_PROBE**.

Reason: the canonical contradiction is fully formalized for `sYES = 1` using a
special finite candidate type (`Size1Candidate`) and exact cardinality `n+2`.
For general `IsoStrongFamilyEventually`, the same diagonal template looks
conceptually reusable, but the current repository does not visibly contain the
needed general enumeration/cardinality bridge for circuits of size `≤ sYES` tied
to the existing `Mof/Tof` interface obligations.

## 2. Candidate general theorem shape

Strongest plausible target shape (as a test theorem, not a route claim):

```lean
theorem isoStrong_conclusion_negative_general
  (F : GapSliceFamilyEventually)
  (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
  (hEnum : -- finite enumeration/cardinality for YES-side candidate traces)
  (hTraceBound : -- trace count ≤ F.Mof n (F.Tof n β) eventually)
  : ¬ IsoStrongFamilyEventually F hInDag
```

Current evidence suggests a weaker theorem with explicit side hypotheses
(`hEnum`, `hTraceBound`, maybe additional semantic constraints on YES) is more
plausible than a clean theorem with only `F` and `hInDag`.

## 3. Canonical proof dependency audit

- `F.Mof n (F.Tof n β) = n + 2`:
  - **Does not directly generalize** as an equality form.
  - In general, interface field `hM` gives `Mof = circuitCountBound n T`, and
    `hT` ties `T = sNO - 1` only eventually.

- `sYES = 1`:
  - **Canonical-specific and critical** for size-1 candidate compression.
  - Generalization requires replacing size-1 traces by traces induced by all
    circuits of size `≤ sYES`.

- `Size1Candidate` trace count:
  - **Canonical-specific implementation artifact** with exact finite type and
    exact card formula `n+2`.
  - Must be replaced by finite family indexed by bounded-size circuits.

- trace-diagonalisation lemma:
  - **Conceptually generalizes** (finite image not surjective if strict card
    gap), but requires concrete finite index type with proven card bound.

- `exists_valid_agreeing_not_yes_under_slack`:
  - **Partially generalizable in idea**, but currently built around size-1
    trace machinery in the canonical probe.

- `slack_for_D_of_isoStrong_slack`:
  - **Likely generalizable structurally** because it converts iso-strong slack
    form to a set-cardinality form; arithmetic side conditions may differ.

- `CorrectOnPromiseSlice` extraction:
  - **Generalizes**; this is interface-level plumbing from `InPpolyDAG` witness
    families to promise-slice correctness.

## 4. Replace size-1 traces with size-≤sYES traces

- Is there a finite enumerable type/list of circuits of size ≤ s?
  - **Likely yes in principle** (syntax trees are finite at bounded size), but
    no audited general-purpose finite type appears in the required-reading
    modules.

- Does `circuitCountBound n s` upper-bound traces of such circuits?
  - `circuitCountBound` is defined as an over-approx recurrence intended as an
    upper bound on count of circuits of size ≤ s.
  - What is missing is a ready-to-use Lean theorem in the inspected boundary
    linking this recurrence to **cardinality of a concrete enumerable family**
    and then to **trace family cardinality**.

- Is that enough for the same diagonalisation?
  - **Probably enough mathematically**: if `#traces ≤ #circuits ≤ Mof < 2^(free)`
    then finite non-surjectivity diagonalization repeats.
  - **Formally not yet enough** without the missing cardinality lemmas.

- Does repo already contain needed enumeration/cardinality lemmas?
  - Not evident in the required-reading set; canonical proof side uses an
    ad-hoc `Size1Candidate` finite type instead.

## 5. Mof relationship

From interfaces:

- Eventual `hM`: `F.Mof n T = circuitCountBound n T` (for `n ≥ F.N0`).
- Eventual `hT`: `F.Tof n β = (F.paramsOf n β).sNO - 1` (for `n ≥ F.N0`).

So eventually:

`F.Mof n (F.Tof n β) = circuitCountBound n ((F.paramsOf n β).sNO - 1)`.

Given `p.gap_ok : p.sYES + 1 ≤ p.sNO`, we get `p.sYES ≤ p.sNO - 1`, and by
monotonicity one would expect:

`circuitCountBound p.n p.sYES ≤ circuitCountBound p.n (p.sNO - 1)`.

But the monotonicity theorem for `circuitCountBound` is not identified in this
D0 markdown pass as an already-exported lemma in required modules.

## 6. General diagonalisation sketch

Plausible template:

1. From iso-strong, obtain eventual slack:
   `Mof < 2^(tableLen - κ)` (or equivalent D-card form).
2. Let `D` be fixed coordinates; free rows count is `tableLen - |D|`.
3. Define candidate family = traces on free rows induced by all YES-eligible
   circuits (size ≤ sYES, and consistency constraints as needed).
4. Prove `#candidate_traces ≤ Mof`.
5. Since `Mof < 2^(#free_rows)`, choose label not equal to any candidate trace.
6. Build diagonal `z` agreeing on `D` and following `label` on free rows.
7. Show `z` valid, agrees on `D`, and cannot be YES by trace contradiction.
8. Contradict forcing clause requiring YES on all valid/agreeing completions.

This is the same architecture as canonical L1, but Step 4 is the active formal
blocker in general form.

## 7. Blockers

- no audited reusable circuit enumeration object for `size ≤ sYES` in the
  required-reading boundary;
- `circuitCountBound` is a recurrence definition, but D0 did not locate a
  theorem package connecting it to concrete finite cardinalities/traces;
- missing trace-count transfer lemma (circuits -> traces over chosen row set);
- YES-side in general families may require additional semantics to tie
  `PartialMCSP_YES` to bounded circuit-induced traces exactly as needed;
- `F.hM`/`F.hT` are eventual, so bookkeeping around `n ≥ N0` must be threaded
  through the contradiction theorem statement.

## 8. Recommended next action

**open_circuit_count_trace_bound_L0**.

Rationale: the highest-leverage next Lean probe is to formalize (or locate and
expose) the bounded-size circuit enumeration + cardinality + trace-image bound
pipeline. Once this exists, the general no-go theorem can be attempted with
minimal changes to the canonical diagonal core.
