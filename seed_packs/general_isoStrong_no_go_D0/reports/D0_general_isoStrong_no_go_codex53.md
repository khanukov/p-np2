Task: general iso-strong no-go D0
Handle: codex53
Branch: work (task requested: main)
Commit before: a043c690bfec5566be157365963bceda1d375390
Commit after: PENDING
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
  The canonical contradiction critically uses a size-1-candidate finite type with exact cardinality `n+2`; the current general interfaces do not provide a corresponding finite type/cardinality bridge for circuits of size `≤ sYES`, nor a theorem linking `circuitCountBound` to trace counts for those circuits.

Recommended next action:
  open_circuit_count_trace_bound_L0

Commands run:
  - ./scripts/check.sh → PENDING

Scope violations:
  none

---

## 1. Executive verdict

**NEEDS_LEAN_PROBE**.

Reasoning (D0-level):
- The canonical theorem `isoStrong_conclusion_negative_for_canonical` is established for the specific family induced by `canonicalAsymptoticHAsym`, with fixed `sYES = 1`, `sNO = 2`, and canonical arithmetic identity `F.Mof n (F.Tof n β) = n + 2`.
- The high-level diagonalisation pattern *looks* extensible, but the concrete refutation depends on exact finitary counting artifacts (not merely asymptotic inequalities), and those artifacts are not currently exposed in the general `GapSliceFamilyEventually` interfaces.
- Therefore a markdown-only argument is insufficient to settle a general no-go theorem; an L0 Lean probe is required.

## 2. Candidate general theorem shape

Strongest plausible shape (subject to additional counting hypotheses):

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (hEnum : ∀ n β, FiniteCandidateFamily F n β)
    (hTraceBound : ∀ n β, candidateTraceCount F n β ≤ F.Mof n (F.Tof n β))
    (hSlackBridge : ∀ n β, F.Mof n (F.Tof n β) < 2 ^ (tableLen n - κ n β)) :
    ¬ IsoStrongFamilyEventually F hInDag
```

Weaker but more immediately realistic shape:

```lean
theorem isoStrong_conclusion_negative_general_if_trace_counted
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (hCountableDiagonalPackage : IsoStrongDiagonalPackage F) :
    ¬ IsoStrongFamilyEventually F hInDag
```

where `IsoStrongDiagonalPackage` explicitly bundles:
1. finite candidate enumeration,
2. candidate-to-trace map,
3. candidate-trace cardinality upper bound,
4. diagonal z construction + validity/agreement/not-YES lemmas.

## 3. Canonical proof dependency audit

- `F.Mof n (F.Tof n β) = n + 2`  
  **Status:** canonical-specific (does not generalize from interfaces alone).  
  In canonical data, this comes from `sNO = 2`, so `Tof = 1` and recurrence collapses to `n+2` at size-1.

- `sYES = 1`  
  **Status:** canonical-specific.  
  This is the critical simplifier enabling a tractable `Size1Candidate` universe.

- `Size1Candidate` trace count  
  **Status:** canonical-specific artifact.  
  General route would need `Size≤sYESCandidate` analog and cardinality machinery.

- trace-diagonalisation lemma  
  **Status:** conceptually generalizable, formally missing general infrastructure.  
  The pigeonhole structure is abstractly generic once candidate traces are finitely bounded.

- `exists_valid_agreeing_not_yes_under_slack`  
  **Status:** partially generalizable schema; current implementation canonicalized through size-1 machinery.

- `slack_for_D_of_isoStrong_slack`  
  **Status:** likely generalizable at arithmetic layer if `Mof`/`Tof` interfaces give enough monotonic and substitution facts.

- `CorrectOnPromiseSlice` extraction  
  **Status:** already generalizable/portable; this is an interface-level bridge from `InPpolyDAG` family hypothesis.

## 4. Replace size-1 traces with size-≤sYES traces

- Is there a finite enumerable type/list of circuits of size ≤ s?  
  **At model level:** very likely yes mathematically.  
  **In current repo interfaces used by canonical proof:** not obviously packaged as a reusable finite type with cardinality theorem.

- Does `circuitCountBound n s` upper-bound traces of such circuits?  
  **Intended interpretation:** yes (recurrence is a counting overapproximation).  
  **Formal status in this path:** not yet a proven bridge from syntax-enumeration cardinality to trace-count bound for the diagonal layer.

- Is that enough for the same diagonalisation?  
  **Almost:** enough for pigeonhole if combined with (a) trace-map finite image and (b) z-construction linking trace disagreement to not-YES.

- Does repo already contain needed enumeration/cardinality lemmas?  
  **D0 finding:** not in a directly reusable general package in the required interface files; canonical proof appears to rely on a bespoke size-1 finite type route.

## 5. Mof relationship

D0 readout of expected equalities/inequalities:

- `F.Mof n (F.Tof n β) = circuitCountBound n (F.Tof n β)`  
  **Likely true by definitional unfolding** for families constructed from asymptotic track data; must be checked per constructor in Lean.

- `F.Tof n β = (F.paramsOf n β).sNO - 1`  
  **Likely definitional** in eventual gap-slice family construction; again, requires Lean-level rewrite confirmation.

- `circuitCountBound p.n p.sYES ≤ F.Mof n (F.Tof n β)` from `p.gap_ok : p.sYES + 1 ≤ p.sNO`  
  **Requires monotonicity** of `circuitCountBound` in second argument and parameter alignment (`p = F.paramsOf n β`).  
  D0 did not find a completed reusable monotonic lemma chain sufficient to claim this automatically.

## 6. General diagonalisation sketch

Plausible general schema if missing counting lemmas are supplied:

1. From iso-strong slack, derive strict inequality of form `Mof < 2^(tableLen - κ)` on large slices.
2. Enumerate all candidate traces induced by circuits of size `≤ sYES`; prove count `≤ Mof`.
3. By pigeonhole over Boolean labelings of the projection set `D`, choose label not equal to any candidate trace.
4. Construct diagonal partial assignment/table `z` consistent with promise encoding.
5. Prove: `z` valid, `z` agrees on `D`, and `z ∉ YES` (via “if YES then some candidate trace matches label” contradiction).
6. Contradict iso-strong forcing conclusion (`hForce`) on the same slice.

This is structurally identical to canonical L1, but the canonical size-1 finite combinatorics must be replaced by general size-≤sYES combinatorics.

## 7. Blockers

Exact blockers (D0):

- no ready-made general circuit enumeration package at `size ≤ sYES` wired to this route;
- `circuitCountBound` is available as recurrence/overapproximation, but a direct theorem “it upper-bounds candidate trace cardinality used by iso-strong diagonalisation” is missing here;
- trace-count bridge over circuits to row-traces is missing in generalized form;
- canonical not-YES bridge currently specialized through size-1 consistency lemmas;
- interface-level assumptions `F.hM`/`Mof` arithmetic appear insufficient alone without extra counting package;
- potential arithmetic/monotonicity gap for promoting `sYES` bound to `Tof = sNO-1` bound.

## 8. Recommended next action

**open_circuit_count_trace_bound_L0**.

Rationale:
- This is the narrowest missing formal brick that decides whether canonical refutation scales generally.
- It avoids premature “canonical-only” or “general-no-go” claims.
- It directly targets the required reusable combinatorial infrastructure.
