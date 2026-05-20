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
  The canonical contradiction critically uses a size-1-candidate finite type with exact cardinality `n+2`; the current general interfaces do not provide a corresponding finite type/cardinality bridge for circuits of size `≤ sYES`, nor a theorem linking `circuitCountBound` to trace counts for those circuits.  Monotonicity of `circuitCountBound` in the size argument is also not packaged in the inspected interface boundary.

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
- The canonical theorem `isoStrong_conclusion_negative_for_canonical`
  (`pnp3/Tests/IsoStrongConclusionProbe.lean:368`) is established for the
  specific family induced by `canonicalAsymptoticHAsym`, with fixed
  `sYES = 1`, `sNO = 2`, and canonical arithmetic identity
  `F.Mof n (F.Tof n β) = n + 2`.
- The high-level diagonalisation pattern *looks* extensible, but the
  concrete refutation depends on exact finitary counting artifacts (not
  merely asymptotic inequalities), and those artifacts are not currently
  exposed in the general `GapSliceFamilyEventually` interfaces.
- Therefore a markdown-only argument is insufficient to settle a general
  no-go theorem; an L0 Lean probe is required.

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

Granular shape (matches what an L0 task would need to discharge piece by
piece, mirroring `F.hM`/`F.hT` structure of `GapSliceFamilyEventually`):

```lean
theorem isoStrong_conclusion_negative_general_granular
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (hTof   : ∀ n β, F.Tof n β = (F.paramsOf n β).sNO - 1)
    (hMof   : ∀ n β, F.Mof n (F.Tof n β) = circuitCountBound n (F.Tof n β))
    (hCount : ∀ n β,
        candidateTraceCount F n β ≤ circuitCountBound n ((F.paramsOf n β).sYES))
    (hMono  : ∀ n β,
        circuitCountBound n ((F.paramsOf n β).sYES)
          ≤ circuitCountBound n ((F.paramsOf n β).sNO - 1)) :
    ¬ IsoStrongFamilyEventually F hInDag
```

Wrapper shape (single packed-input variant — useful as the final L1
endpoint once granular bricks are landed):

```lean
theorem isoStrong_conclusion_negative_general_if_trace_counted
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (hCountableDiagonalPackage : IsoStrongDiagonalPackage F) :
    ¬ IsoStrongFamilyEventually F hInDag
```

where `IsoStrongDiagonalPackage` explicitly bundles:
1. finite candidate enumeration (`Cand F n β : Type`, `Fintype (Cand F n β)`);
2. candidate-to-trace map (`traceOf : Cand F n β → (FreeRows F n β → Bool)`);
3. candidate-trace cardinality upper bound
   (`Fintype.card (Cand F n β) ≤ F.Mof n (F.Tof n β)`);
4. diagonal `z` construction + validity/agreement/not-YES lemmas.

The granular shape and the wrapper shape are equivalent up to packaging:
the wrapper bundles fields 1–4 above, the granular form exposes them as
top-level hypotheses.  An L0 task should target the granular bricks;
the wrapper is the L1 closure shape.

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

- trace-diagonalisation lemma (`exists_trace_not_size1_of_card_lt`)  
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
  **Not derivable from `gap_ok` alone.**  `gap_ok` is a threshold
  relation; it does **not** by itself imply
  `circuitCountBound n sYES ≤ circuitCountBound n (sNO - 1)`.
  Closing this step requires a separately-proved monotonicity lemma
  for `circuitCountBound` in its size argument, plus parameter
  alignment (`p = F.paramsOf n β`).  D0 did not find a completed
  reusable monotonic lemma chain in `pnp3/Models/Model_PartialMCSP.lean`
  or in the required-reading boundary.  This is one of the named
  bricks for the proposed L0 task.

## 6. General diagonalisation sketch

Plausible general schema if missing counting lemmas are supplied:

1. From iso-strong slack (eventual form), derive strict inequality
   `Mof < 2^(tableLen - κ)` on large slices.
2. Pick fixed coordinate set `D` with `|D| = tableLen - κ`; let
   `FreeRows := tableLen \ D`, so `|FreeRows| = tableLen - |D| = κ`.
   (Roles of `D` and `FreeRows` follow the canonical L1 convention;
   the actual diagonalisation acts on the FreeRows side.)
3. Define candidate family `Cand F n β = { c : circuit | size c ≤ sYES }`
   with a finite enumeration (this is the L0 brick).  Define the
   trace map `traceOn_FreeRows : Cand F n β → (FreeRows → Bool)` by
   restriction of the row-evaluation of each candidate.
4. **Counting step (the L0 bottleneck).**  Show
   `Fintype.card (image traceOn_FreeRows) ≤ Fintype.card (Cand F n β)
       ≤ circuitCountBound n ((F.paramsOf n β).sYES)
       ≤ circuitCountBound n ((F.paramsOf n β).sNO - 1)
       = F.Mof n (F.Tof n β)
       < 2 ^ |FreeRows|`
   where the second inequality uses the L0 enumeration cardinality
   lemma, the third uses `circuitCountBound` monotonicity at
   `sYES ≤ sNO - 1` from `gap_ok`, the equality uses `F.hM`/`F.hT`,
   and the strict inequality is the iso-strong slack from step 1.
5. By pigeonhole over Boolean labelings of `FreeRows`, choose
   `label : FreeRows → Bool` outside `image traceOn_FreeRows`.
6. Build diagonal `z` that agrees with the promise data on `D` and
   encodes `label` on `FreeRows`.
7. Prove `z` valid, `z` agrees on `D`, and `z ∉ YES`:  if `z ∈ YES`,
   some candidate `c ∈ Cand` realises a row trace matching `label` on
   `FreeRows`, contradicting the pigeonhole choice.
8. Contradict iso-strong forcing conclusion (`hForce`) on the same
   slice.

This is structurally identical to canonical L1, but the canonical
size-1 finite combinatorics in step 3–4 must be replaced by general
size-≤sYES combinatorics.  Steps 1, 2, 5, 6, 7, 8 are essentially
parameter-agnostic; the canonical proof's step-3/4 specialisation
to `Size1Candidate` + `n + 2` is what the L0 task generalises.

## 7. Blockers

Exact blockers (D0):

- no ready-made general circuit enumeration package at `size ≤ sYES`
  wired to this route;
- `circuitCountBound` is available as recurrence/overapproximation
  (`pnp3/Models/Model_PartialMCSP.lean`), but a direct theorem
  "it upper-bounds candidate trace cardinality used by iso-strong
  diagonalisation" is missing here;
- trace-count bridge over circuits to row-traces is missing in
  generalized form;
- canonical not-YES bridge currently specialized through size-1
  consistency lemmas (`is_consistent_diagonal_table_implies_label_trace`);
- interface-level assumptions `F.hM`/`Mof` arithmetic appear
  insufficient alone without extra counting package;
- monotonicity of `circuitCountBound` in the size argument is not
  packaged in the inspected interface boundary; `gap_ok` alone does
  not yield the required `sYES → (sNO - 1)` lifting.

## 8. Recommended next action

**open_circuit_count_trace_bound_L0**.

Rationale:
- This is the narrowest missing formal brick that decides whether
  canonical refutation scales generally.
- It avoids premature "canonical-only" or "general-no-go" claims.
- It directly targets the required reusable combinatorial
  infrastructure: bounded-size circuit enumeration, cardinality
  bound, monotonicity of `circuitCountBound`, and a trace-image
  cardinality lemma.

Suggested L0 deliverables (one Lean file under `pnp3/Tests/` or
`pnp3/Combinatorics/`):

1. `boundedSizeCircuitEnum : (n s : Nat) → Fintype { c : Circuit n | size c ≤ s }`.
2. `boundedSizeCircuitEnum_card_le : Fintype.card (boundedSizeCircuitEnum n s) ≤ circuitCountBound n s`.
3. `circuitCountBound_mono : ∀ n, Monotone (circuitCountBound n ·)`.
4. `boundedSizeTrace_image_card_le : ∀ (R : Finset rows) (n s),
     Fintype.card (image (traceOn R) (boundedSizeCircuitEnum n s))
       ≤ circuitCountBound n s`.

Bricks 1–4 unlock the granular shape in section 2 and the wrapper
shape via direct packaging.
