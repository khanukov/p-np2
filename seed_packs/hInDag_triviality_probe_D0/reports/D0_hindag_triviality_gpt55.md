# hInDag triviality probe D0 report

## 1. Executive verdict

`YELLOW_INCONCLUSIVE`

Short version: the probe found no in-repo theorem that already proves the canonical `hInDag` family, and no route closes using only the existing compiler surfaces.  The canonical Boolean decider is visibly polynomial-time at the algorithm-design level for the intended `sYES = 1, sNO = 2` path, but the repo does **not** currently expose the intermediate theorem needed to feed that decider into `proved_P_subset_PpolyDAG_internal`.  Closing that gap requires either a TM/`P` witness for the canonical asymptotic language or a direct non-uniform DAG construction for the fixed-slice languages; both are real formal-construction work, not a D0 markdown-only consequence.

This is **Infrastructure / audit** work under the repository classification rules: it audits whether a proposed DAG-side consumer hypothesis is vacuous/trivial.  It does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, and it should not be reported as P-vs-NP mainline progress.

## 2. Required-reading inventory

Read and used:

- `RESEARCH_CONSTITUTION.md`.  Relevant constraints: the frozen target requires an honest `ResearchGapWitness.dagSeparation`, and trust-root identifiers including `ComplexityInterfaces.P`, `NP`, `PpolyDAG`, `NP_not_subset_PpolyDAG`, `P_ne_NP`, `ResearchGapWitness`, and `ResearchGapWitness.dagSeparation` are frozen.  The constitution also forbids advertising the final separation claim without a closed no-argument theorem meeting the listed dependency conditions.
- `STATUS.md`.
- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`.
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md`.
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`.
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`.
- `pnp3/Complexity/Interfaces.lean`.
- `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`.
- `pnp3/Complexity/Simulation/Circuit_Compiler.lean`.
- `pnp3/Models/Model_PartialMCSP.lean`.
- `pnp3/Magnification/FinalResultMainline.lean`.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- `pnp3/RefutedPredicates/Registry.lean`.
- `outputs/nogolog.jsonl`, specifically `NOGO-000004`, `NOGO-000006`, `NOGO-000008`, and `NOGO-000009`.

Missing required-reading paths: none observed.

## 3. Statement under test

The canonical downstream `hInDag` family appears in the route definitions as the hypothesis argument to `AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`, and `AsymptoticPromiseYesWeakRouteEventually`: each quantifies over a family assigning `ComplexityInterfaces.InPpolyDAG` to every `(n, β)` slice of `eventualGapSliceFamily_of_asymptotic hAsym`.

At the canonical instantiation, the exact Lean family under test is:

```lean
∀ n : Nat, ∀ β : Rat,
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language
      ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
          Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

Unfolding the adapter shows why `β` is irrelevant for this probe: `eventualGapSliceFamily_of_asymptotic hAsym` sets `paramsOf n _β := hAsym.pAt (max n hAsym.N0) ...`; for the canonical `hAsym`, `N0 = 8` and `pAt` is `canonicalAsymptoticParams`.  Thus the target is a family of fixed-slice `gapPartialMCSP_Language` DAG witnesses for canonical parameters indexed by `max n 8`.

The relevant public route binders are:

```lean
def AsymptoticIsoStrongRoute
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ hInDag :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)),
    IsoStrongFamilyEventually ...
```

and analogously for `AsymptoticPromiseYesCertificateRoute` and `AsymptoticPromiseYesWeakRouteEventually`.

## 4. Route 1 audit — P-membership + compiler bridge

### Search result

I searched for in-repo theorems of the form

- `ComplexityInterfaces.P (gapPartialMCSP_Language _)`,
- `ComplexityInterfaces.P (Models.gapPartialMCSP_Language _)`,
- `ComplexityInterfaces.P (gapPartialMCSP_AsymptoticLanguage _)`, and
- `InPpolyDAG (gapPartialMCSP_Language _)`.

No existing theorem was found that proves `P` membership for either a fixed-slice `gapPartialMCSP_Language p` or the asymptotic `gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec`.  The search did find only downstream consumers of hypothetical `InPpolyDAG` witnesses, the compiler endpoint, NP-membership wrappers from TM witnesses, and the refutation-test truth-table formula witness.  In particular, `Model_PartialMCSP.lean` exposes NP-membership only from explicit TM witnesses, not P-membership.

### Exact compiler bridge

The bridge is real and closed, but it starts from `ComplexityInterfaces.P L`, not from a raw Boolean function or a Lean decider:

```lean
def P_subset_PpolyDAG : Prop :=
  ∀ L : Language, P L → PpolyDAG L
```

The internal route factors through straight-line circuits:

```lean
def P_subset_PpolyStraightLine : Prop :=
  ∀ L : Language, P L → PpolyStraightLine L

theorem P_subset_PpolyDAG_of_P_subset_PpolyStraightLine :
    P_subset_PpolyStraightLine → P_subset_PpolyDAG
```

The no-argument compiler endpoint is:

```lean
theorem proved_P_subset_PpolyDAG_internal :
    P_subset_PpolyDAG
```

Its proof obtains a polynomial-time TM for `L` by destructing `exists_poly_tm_for_P (L := L) hPL`; therefore the missing input for this route is a theorem of type `ComplexityInterfaces.P <target-language>`, not merely a computable Lean function.

### Route 1 gap estimate

For the asymptotic language route, a suitable missing theorem would be:

```lean
theorem canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

Together with an existing slice-transport theorem from the asymptotic language to each fixed `paramsOf n β` slice, this could feed `proved_P_subset_PpolyDAG_internal` and then produce the requested `InPpolyDAG` witnesses.  However, the current repo does not expose that slice-level `P` theorem or the transport theorem.  More importantly, `P` is the internal TM-based polynomial-time class, so the proof would need a concrete TM and a runtime proof, not merely `decideAsymptotic_iff`.

Line-count estimate: a complete TM proof for `decideAsymptotic` is not a ≤200 LOC D0 addition.  The canonical decider file itself states that the verifier-components/TM closure is planned as about 2500 LOC of TM engineering.  A direct non-uniform fixed-slice DAG construction might avoid TM work, but that is a different theorem and still requires a formal truth-table-to-`DagCircuit` or specialized size-1-candidate DAG construction that is not currently present.

## 5. Route 2 audit — canonical decider + compiler

### Compiler input shape

`decideAsymptotic` is a Lean Boolean function:

```lean
def decideAsymptotic (N : Nat) (x : Bitstring N) : Bool := ...
```

and `decideAsymptotic_iff` proves correctness against `gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec`:

```lean
theorem decideAsymptotic_iff (N : Nat) (x : Bitstring N) :
    decideAsymptotic N x = true ↔
      gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec N x = true
```

But the compiler endpoint does not accept a Lean `Bool` decider, a `Decidable` instance, or a semantic `Bitstring n → Bool` family.  It accepts `P L`, and internally extracts a polynomial-time TM using `exists_poly_tm_for_P`.  Therefore `decideAsymptotic` does not already satisfy the compiler input shape.

### Polynomial-time status of `decideAsymptotic`

The implementation is algorithmically polynomial in the input length under the intended cost model, but this is not represented by an in-repo `P` theorem.

Facts established in Lean:

- `size1Candidates m` is exactly the size-1 candidate list: `Circuit.const false`, `Circuit.const true`, and all `Circuit.input i` for `i : Fin m`.
- `decideYesAt1 m T` is `List.any` over `size1Candidates m`, checking `is_consistent_bool C T`.
- `findCanonicalSlice N` searches `List.range (N + 1)` for `Partial.inputLen m = N`, and the `_iff` lemmas characterize `some`/`none` results.
- `decideAsymptotic` returns `false` when `findCanonicalSlice N = none` and otherwise runs `decideYesAt1` at the found canonical slice.
- `decideAsymptotic_of_not_canonical` formally proves off-canonical rejection.

What is absent:

- no theorem bounding the runtime of `findCanonicalSlice`, `decodePartial`, `is_consistent_bool`, `decideYesAt1`, or `decideAsymptotic`;
- no theorem translating `decideAsymptotic_iff` plus a runtime bound into `ComplexityInterfaces.P`;
- no theorem translating a Lean function-level decider directly into `InPpolyDAG`.

Thus Route 2 does not close on current `main`.

## 6. Route 3 audit — direct algorithmic argument from `sYES=1, sNO=2`

### Validation of the heuristic

The heuristic is correct at the implementation/algorithm level:

1. `canonicalAsymptoticSpec` sets `sYES := fun _ => 1` and `sNO := fun _ => 2`.
2. `canonicalAsymptoticParams` uses the same thresholds for each large enough slice, and the `[simp]` lemmas expose `sYES = 1`, `sNO = 2`, and `partialInputLen = Partial.inputLen n`.
3. `decideYesAt1` enumerates the `m + 2` size-1 candidates via `size1Candidates m` and checks consistency using `is_consistent_bool`.
4. `Partial.inputLen m` is `2 * Partial.tableLen m`; `Partial.tableLen m` is `2^m`, so the encoded table length is `N = 2 · 2^m`.
5. At canonical length, `decideAsymptotic_at_inputLen` reduces the asymptotic decider to `decideYesAt1 m (decodePartial x)`.
6. At non-canonical length, `decideAsymptotic_of_not_canonical` returns `false`.

So the informal cost argument is sound in outline: there are `m + 2` candidate circuits; each consistency check scans a table of `2^m` rows; the work is `O((m+2)2^m) = O(N log N)` at canonical lengths, plus the bounded canonical-slice search off canonical lengths.

### Why it still does not close

The direct argument does not currently produce a `DagCircuit` family.  To close the exact target without the `P` compiler, the repo would need a theorem such as one of the following:

```lean
theorem fixedSlice_gapPartialMCSP_sYES_one_in_PpolyDAG
    (p : Pnp3.Models.GapPartialMCSPParams) (hp : p.sYES = 1) :
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language p)
```

or the canonical family-specialized theorem:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
  ∀ n : Nat, ∀ β : Rat,
    Pnp3.ComplexityInterfaces.InPpolyDAG
      (Pnp3.Models.gapPartialMCSP_Language
        ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
            Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

The repo does contain a truth-table hardwiring theorem for `PpolyFormula (gapPartialMCSP_Language p)`, but it lives in a falsifiability test file that imports refuted-predicate infrastructure and proves formula, not DAG, membership.  It is therefore not an admissible import for this probe and is not the requested `InPpolyDAG` theorem.

## 7. Cross-route synthesis

- **Route 1 does not close.**  `proved_P_subset_PpolyDAG_internal` exists and is closed, but it requires `P L`.  No in-repo theorem proves `P (gapPartialMCSP_Language p)` or `P (gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec)`.
- **Route 2 does not close.**  `decideAsymptotic` and `decideAsymptotic_iff` exist, but the compiler consumes a TM-based `P` witness, not a Lean Boolean decider.  The missing intermediate theorem is:

  ```lean
  theorem canonicalAsymptoticLanguage_in_P :
    Pnp3.ComplexityInterfaces.P
      (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
        Pnp3.Magnification.canonicalAsymptoticSpec)
  ```

  plus slice transport from the asymptotic language to the fixed-slice `paramsOf n β` languages if one wants exactly the downstream `hInDag` family.

- **Route 3 does not close, but remains the most plausible direct attack.**  The algorithmic `sYES=1` enumeration is polynomial and very small conceptually.  The missing theorem is the direct DAG-family witness:

  ```lean
  theorem hInDag_for_canonicalAsymptoticHAsym :
    ∀ n : Nat, ∀ β : Rat,
      Pnp3.ComplexityInterfaces.InPpolyDAG
        (Pnp3.Models.gapPartialMCSP_Language
          ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
              Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
  ```

  A more reusable variant would be a fixed-slice theorem for all `p` with `p.sYES = 1`.  This theorem is not present on `main`.

Because none of these theorems exists and constructing either a TM `P` witness or a direct `DagCircuit` family is beyond a markdown-only D0 patch, the probe remains YELLOW rather than RED or GREEN.

## 8. NoGo cross-check

The existing refutations do **not** block the three attack routes above, but they constrain how any result may be interpreted.

- PR 13 / `FormulaSupportBoundsFalsifiabilityProbe.lean`: the falsifiability test proves that `FormulaSupportRestrictionBoundsPartial` and related formula-support assumptions are inconsistent via truth-table hardwiring.  It does not refute the DAG-side fixed-slice membership statement under test.  It does, however, warns that formula-side hardwiring is dangerous and must not be repackaged as lower-bound progress.
- `NOGO-000004`: a hardwiring attack against support-cardinality provenance filters.  This is local to AC0/locality-support filters; it does not rule out a benign upper-bound theorem `InPpolyDAG (gapPartialMCSP_Language p)`.
- `NOGO-000006`: an arbitrary all-essential log-width truth-table payload hardwiring attack against support-cardinality filters.  Again, this restricts provenance-filter claims, not P/DAG upper-bound constructions.
- `NOGO-000008`: tautological-seed syntactic rewriting defeats syntactic-only V2 filters.  It is irrelevant to the compiler/P-membership route except as a warning not to cite syntactic filters as lower-bound progress.
- `NOGO-000009`: structural-normalisation patches for V2-style filters are self-defeating.  It is likewise local to V2 support-filter design.

Conclusion: none of PR 13 or `NOGO-000004/6/8/9` prevents proving the `hInDag` family as an upper-bound/triviality theorem.  They only prevent overclaiming restricted formula/locality/filter routes as mainline P-vs-NP progress.

## 9. Verdict-specific consequence

For `YELLOW_INCONCLUSIVE`:

The specific Lean construction that would settle the probe is one of the following.

Preferred direct settlement:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
  ∀ n : Nat, ∀ β : Rat,
    Pnp3.ComplexityInterfaces.InPpolyDAG
      (Pnp3.Models.gapPartialMCSP_Language
        ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
            Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

Reusable direct settlement:

```lean
theorem fixedSlice_gapPartialMCSP_sYES_one_in_PpolyDAG
    (p : Pnp3.Models.GapPartialMCSPParams) (hp : p.sYES = 1) :
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language p)
```

Compiler-route settlement:

```lean
theorem canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

plus a transport theorem from asymptotic-language `PpolyDAG`/`InPpolyDAG` to each canonical fixed slice, or a separate fixed-slice `P` theorem for every canonical parameter.

Why this is out of D0 scope: the compiler route requires the TM-verifier/polytime construction that the repo explicitly documents as a multi-session TM-engineering obligation.  The direct DAG route requires a formal circuit-family construction over the dependent `DagCircuit` syntax and size accounting.  Neither theorem already exists, and neither is safely derivable in markdown from existing surfaces.

Downstream status implication: the post-PR13 retarget and iso-strong audit should **not** be updated to RED yet.  They should record that `open_hInDag_triviality_probe_L0` remains the next decisive work item, with the direct DAG construction as the preferred target.  The promise-YES L0 probe should not be promoted ahead of this until the `hInDag` triviality question is kernel-settled.

## 10. Scope statement

No mainline Lean source was introduced or edited.  No spec, JSONL, `NoGoLog`, `known_guards`, trust-root surface, `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or `P ≠ NP` claim was introduced.  No refuted predicate was promoted.  No `VerifiedNPDAGLowerBoundSource` construction was introduced.  No TM-verifier session work was performed.

Only this markdown report was added under the allowed report directory.

## 11. Commands run

```sh
pwd && find .. -name AGENTS.md -print
cat AGENTS.md && printf '\n--- prompt ---\n' && cat seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
sed -n '1,260p' seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
sed -n '260,520p' seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
git status --short --branch && git rev-parse HEAD && git branch --show-current
for f in RESEARCH_CONSTITUTION.md STATUS.md seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl; do echo "=== $f ==="; test -f "$f" && sed -n '1,220p' "$f" || echo MISSING; done
rg -n "def P |abbrev P |class P |PpolyDAG|InPpolyDAG|P_subset|proved_P_subset|decideAsymptotic|decideYesAt1|findCanonicalSlice|gapPartialMCSP_Language|eventualGapSliceFamily_of_asymptotic|AsymptoticIsoStrongRoute|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually|FormulaCertificateProviderPartial|Probe 13|NOGO-00000[4689]" pnp3 seed_packs outputs/nogolog.jsonl STATUS.md RESEARCH_CONSTITUTION.md
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '1,170p'
nl -ba pnp3/Complexity/PsubsetPpolyDAG_Internal.lean | sed -n '1,220p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '1,220p'
nl -ba pnp3/Complexity/PsubsetPpolyDAG_Internal.lean | sed -n '1,180p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '250,360p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '1,120p'; nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '380,460p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '460,560p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '553,640p'
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '1,220p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,260p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,130p'; nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '260,310p'
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '126,260p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '1,220p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '520,690p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '690,840p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '840,960p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '960,1080p'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '200,300p'
rg -n "P \\(gapPartialMCSP|P \\(Models\\.gapPartialMCSP|P \\(.*Asymptotic|gapPartialMCSP.*PpolyDAG|InPpolyDAG \\(gapPartialMCSP|gapPartialMCSP_AsymptoticLanguage.*P|decideAsymptotic.*P|P_subset_PpolyDAG" pnp3
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '1440,1555p'
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '600,725p'
rg -n "structure InPpolyDAG|def PpolyDAG|abbrev PpolyDAG|structure InPpolyFormula|def PpolyFormula" pnp3/Complexity/Interfaces.lean && nl -ba pnp3/Complexity/Interfaces.lean | sed -n '250,390p'
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '400,455p'
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '1,180p'
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '180,330p'
rg -n "ppolyDAG.*ppolyFormula|ppolyFormula.*ppolyDAG|Formula.*DAG|of_PpolyFormula|PpolyDAG.*Formula" pnp3/Complexity pnp3/Tests pnp3/Magnification/FinalResultMainline.lean
rg -n "toDag|FormulaCircuit.*Dag|DagCircuit\\.const|DagCircuit.*input|inductive DagCircuit|structure DagCircuit|def eval \\{n : Nat\\} : DagCircuit|namespace DagCircuit" pnp3/Complexity/Interfaces.lean pnp3/Complexity
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '170,220p'; nl -ba pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean | sed -n '1,110p'
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '220,248p'; nl -ba pnp3/Complexity/Interfaces.lean | sed -n '468,505p'; nl -ba pnp3/Complexity/Interfaces.lean | sed -n '505,535p'
rg -n "def eventualGapSliceFamily_of_asymptotic|structure GapSliceFamilyEventually|paramsOf" pnp3/Magnification pnp3/Models/Model_PartialMCSP.lean
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '150,185p'
find seed_packs/hInDag_triviality_probe_D0 -maxdepth 2 -type d -print && find seed_packs/hInDag_triviality_probe_D0 -maxdepth 2 -type f -print
rg -n "canonicalAsymptoticVerifierComponents|witnessOfComponents|Components" pnp3/Magnification/CanonicalAsymptoticDecider.lean
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '680,775p'
python3 - <<'PY'
import json
ids={'NOGO-000004','NOGO-000006','NOGO-000008','NOGO-000009'}
with open('outputs/nogolog.jsonl') as f:
 for i,l in enumerate(f,1):
  o=json.loads(l)
  if o.get('id') in ids:
   print(i,o['id'],o.get('failure_class'),o.get('method_family'),o.get('structural_pattern')[:180].replace('\n',' '))
PY
python3 - <<'PY'
# Edited the report wording to satisfy the doc-honesty linter, then reran the check.
PY
./scripts/check.sh
```
