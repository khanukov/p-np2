# hInDag triviality probe D0 — report

## 1. Executive verdict

YELLOW_INCONCLUSIVE

Short form: the target `hInDag` family is not closed RED on the current repo surface, because no existing theorem gives either

```lean
ComplexityInterfaces.P
  (Models.gapPartialMCSP_AsymptoticLanguage
    Magnification.canonicalAsymptoticSpec)
```

or

```lean
ComplexityInterfaces.PpolyDAG
  (Models.gapPartialMCSP_AsymptoticLanguage
    Magnification.canonicalAsymptoticSpec)
```

without an additional concrete TM/circuit construction.  The mathematical algorithm is very likely polynomial-time: at canonical length `N = 2 * 2^m`, `decideAsymptotic` enumerates the `m + 2` size-1 candidates and checks them against the decoded partial truth table, and off canonical lengths it returns `false`.  However, the repo's `P` and `P ⊆ PpolyDAG` bridge are TM-shaped, not mere Lean-function-shaped; the missing construction is the concrete polynomial-time TM / component package already identified by the repo as an ~800--1500 LOC obligation, not a ≤200 LOC D0 patch.

This is **Infrastructure** under the repository progress classification: it audits an API/route vulnerability and does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.

## 2. Required-reading inventory

Read and used:

- `RESEARCH_CONSTITUTION.md`.
- `STATUS.md`.
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md`.
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`.
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`.
- `pnp3/Complexity/Interfaces.lean`.
- `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`.
- `pnp3/Complexity/Simulation/Circuit_Compiler.lean`.
- `pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean` and `TuringEncoding.lean` as supporting files to identify the exact shape of `P`.
- `pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean` as supporting file because it directly names the remaining verifier-components obligation.
- `pnp3/Models/PartialTruthTable.lean` and `pnp3/Models/Model_PartialMCSP.lean`.
- `pnp3/Magnification/FinalResultMainline.lean`.
- `pnp3/Magnification/AsymptoticDAGCollapse.lean` and `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean` as supporting files for the global-to-slice `PpolyDAG` bridge.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- `pnp3/RefutedPredicates/Registry.lean`.
- `outputs/nogolog.jsonl`, especially NOGO-000004, NOGO-000006, NOGO-000008, and NOGO-000009.

Missing required reading:

- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md` is absent in this checkout.  `find seed_packs/post_pr13_provider_retarget_D0 -maxdepth 3 -type f -print` and `find seed_packs -path '*provider_retarget*' -type f -print` found no provider-retarget report path.

## 3. Statement under test

The exact family asked of the asymptotic iso-strong / promise-YES consumers is the `hInDag` argument in `AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`, and `AsymptoticPromiseYesWeakRouteEventually`:

```lean
∀ n : Nat, ∀ β : Rat,
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language
      ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
          Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

The relevant definitions quantify exactly this shape for `hInDag`: `AsymptoticIsoStrongRoute` takes `∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))`; the promise-YES certificate and weak routes repeat the same family argument.

The canonical adapter is total below threshold by using `hAsym.pAt (max n hAsym.N0)`, so at the canonical instantiation the slice parameters are always canonical asymptotic parameters at `max n 8`; the `β` argument is ignored by the adapter.

## 4. Route 1 audit — P-membership + compiler bridge

### Search for existing P-membership

Search command:

```sh
rg -n "P \\(.*gapPartialMCSP|gapPartialMCSP.* P|gapPartialMCSP_Asymptotic.*P|InPpolyDAG \\(gapPartialMCSP|PpolyDAG \\(gapPartialMCSP|decideAsymptotic.*poly|poly.*decideAsymptotic|CanonicalAsymptoticVerifierComponents|GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec" pnp3 -g'*.lean'
```

Result: no theorem of the shape

```lean
Pnp3.ComplexityInterfaces.P
  (Pnp3.Models.gapPartialMCSP_Language _)
```

or

```lean
Pnp3.ComplexityInterfaces.P
  (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage _)
```

was found.  The matches were consumers/scaffolds: fixed-slice `PpolyDAG` assumptions, asymptotic-to-fixed-slice `PpolyDAG` transport, and the canonical verifier scaffold.

### Exact compiler bridge

`P` in the public interface is an abbreviation for the internal TM-based class:

```lean
abbrev P : Language → Prop := Internal.PsubsetPpoly.Complexity.P.{0}
```

Internally, `P` is `polyTimeDecider`, i.e. an existential over a concrete `TM`, exponent `c`, runtime bound, and language-correctness proof:

```lean
def polyTimeDecider (L : Language) : Prop :=
  ∃ (M : TM.{u}) (c : ℕ),
    (∀ n, M.runTime n ≤ n ^ c + c) ∧
    (∀ n (x : Bitstring n), TM.accepts (M := M) (n := n) x = L n x)
```

The compiler's no-argument endpoint is:

```lean
theorem proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG
```

and `P_subset_PpolyDAG` means `∀ L, P L → PpolyDAG L`.  The proof route factors through straight-line circuits: `P_subset_PpolyStraightLine := ∀ L, P L → PpolyStraightLine L`, and `P_subset_PpolyDAG_of_P_subset_PpolyStraightLine` repackages straight-line witnesses as DAG witnesses.

The compiled-runtime proof shape confirms that the compiler consumes a `P` proof by extracting a concrete polynomial-time TM via `exists_poly_tm_for_P`; it does **not** consume an arbitrary Lean Boolean function with an informal runtime argument.

### Gap estimate

If one had

```lean
theorem canonicalAsymptotic_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

then the remaining Lean chain to `PpolyDAG` would be short:

1. Apply `Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal` to get
   `PpolyDAG (gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec)`.
2. Use the canonical-length bridge `eventualCanonicalBridge_of_asymptotic` and `ppolyDAGOnSlicesEventually_of_globalWitness_atCanonicalLengths` to get per-slice `PpolyDAG`.
3. Use classical choice on `PpolyDAG := ∃ _ : InPpolyDAG L, True` to extract the `InPpolyDAG` witness demanded by `hInDag`.

That final chain is plausibly small.  The non-small part is constructing `canonicalAsymptotic_in_P`, because it requires a concrete `TM` whose `accepts` semantics matches `decideAsymptotic` with a polynomial runtime proof.

Route 1 therefore does **not** close RED.

## 5. Route 2 audit — canonical decider + compiler

### Compiler input shape

The compiler input shape is a concrete TM package, not a Lean decider function.  Public `P` unfolds to `polyTimeDecider`, which requires `∃ M : TM, ∃ c`, a runtime bound, and an equality `TM.accepts M n x = L n x`.  The `TM` structure has a finite state type, start/accept states, a transition function, and `runTime`.

`decideAsymptotic` is a Lean-level Boolean function:

```lean
def decideAsymptotic (N : Nat) (x : Bitstring N) : Bool := ...
```

The repository proves correctness of that function against the canonical asymptotic language:

```lean
theorem decideAsymptotic_iff (N : Nat) (x : Bitstring N) :
  decideAsymptotic N x = true ↔
    gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec N x = true
```

But this theorem is not itself a `P` proof.  The file introduces `CanonicalAsymptoticVerifierComponents`, whose fields are exactly the missing TM, polynomial runtime, and `accepts_eq` bridge to `decideAsymptotic`.  Its `witness` construction then turns such components into `GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

### Polynomial-time implementation trace

The implementation has the expected algorithmic shape:

- `canonicalAsymptoticSpec` sets `sYES n = 1` and `sNO n = 2`.
- `Partial.tableLen n = 2^n` and `Partial.inputLen n = 2 * tableLen n`.
- `size1Candidates m` is `[Circuit.const false, Circuit.const true] ++ List.finRange m |>.map Circuit.input`, i.e. exactly `m + 2` candidates.
- `decideYesAt1 m T` is `(size1Candidates m).any (fun C => is_consistent_bool C T)`.
- `findCanonicalSlice N` scans `List.range (N + 1)` looking for `Partial.inputLen m = N`.
- `decideAsymptotic N x` returns `false` if `findCanonicalSlice N = none`; if it finds `m`, it casts `x` to length `Partial.inputLen m`, decodes it, and calls `decideYesAt1 m`.
- `decideAsymptotic_of_not_canonical` proves the off-canonical false branch.
- `decideAsymptotic_iff` combines the canonical and off-canonical cases and proves semantic correctness.

The heuristic runtime argument is valid at the mathematical level: on canonical length `N = 2 * 2^m`, checking `m + 2` candidates over a `2^m`-row partial truth table is `O(m * 2^m) = O(N log N)`, and the off-canonical scan is at most polynomial in `N`.  The repo even records the same runtime sketch in the GapMCSP verifier scaffold: phases over table positions cost `2^n` iterations with `O(n + 1)` navigation, totaling `O(n · 2^n) = O(N · log N)`.

What is absent is a theorem converting that trace into the `P`/compiler input shape.  The scaffold states that the remaining open obligation is:

```lean
buildCanonicalVerifierComponents :
  CanonicalAsymptoticVerifierComponents
```

and describes it as a concrete TM realizing `decideAsymptotic` in polynomial time.

Route 2 therefore does **not** close RED.

## 6. Route 3 audit — direct algorithmic argument from `sYES=1, sNO=2`

The direct algorithmic record is confirmed as an informal/mathematical algorithm:

- `canonicalAsymptoticSpec.sYES n = 1`; `canonicalAsymptoticSpec.sNO n = 2`.
- Size-1 circuits are proved to be exactly constants and projections for the purpose of `≤ 1` enumeration: every candidate in `size1Candidates` has size one, and every circuit of size at most one is in `size1Candidates`.
- `decideYesAt1_iff` proves that `decideYesAt1 m T` decides `PartialMCSP_YES_at m 1 T`.
- `decideYesAt1_iff_const_or_input` gives the closed-form predicate: either a constant is consistent with all constrained cells, or some projection coordinate is consistent with all constrained cells.
- `decideAsymptotic_at_inputLen_iff_size1` exposes the row-wise characterization at canonical length.

Thus the polynomial-time argument in the prompt is mathematically sound.  However, a direct RED conclusion would need one of the following formal bridges:

```lean
Pnp3.ComplexityInterfaces.P
  (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
    Pnp3.Magnification.canonicalAsymptoticSpec)
```

or, bypassing `P`,

```lean
Pnp3.ComplexityInterfaces.PpolyDAG
  (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
    Pnp3.Magnification.canonicalAsymptoticSpec)
```

or an even more direct per-slice theorem:

```lean
∀ n : Nat, ∀ β : Rat,
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language
      ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
          Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

No such theorem exists on the current non-refuted surface.

A tempting fixed-slice hardwiring observation exists: `gapPartialMCSP_Language p` is false off one length, and any Boolean function at one finite length can be hardwired by a truth-table formula.  That idea is already present in Probe 2 of the falsifiability audit, where a fixed-slice `PpolyFormula (gapPartialMCSP_Language p)` is built using a recursive `ttFormula`.  But the existing theorem lives in a test file importing `Magnification.LocalityProvider_Partial`, which is explicitly forbidden for this probe because it transitively imports refuted predicates.  It also targets `PpolyFormula`, not `InPpolyDAG`; there is no public formula-to-DAG or generic fixed-slice `InPpolyDAG` theorem found in the allowed surface.  Rebuilding a DAG hardwiring theorem may be possible, but it is not already present and would be new Lean construction, not a markdown D0 closure.

Route 3 therefore does **not** close RED.

## 7. Cross-route synthesis

- Route 1 closes after `canonicalAsymptotic_in_P`, but that theorem is absent.
- Route 2 closes after `buildCanonicalVerifierComponents : CanonicalAsymptoticVerifierComponents`, or an equivalent `P` theorem for the canonical asymptotic language, but that construction is absent and explicitly scaffolded as substantial engineering.
- Route 3 confirms polynomial-time decidability at the algorithmic level, but the exact missing intermediate theorem remains a concrete formal bridge from the Lean decider to either `P` or directly to `PpolyDAG`/`InPpolyDAG`.

Most precise blocking theorem:

```lean
def buildCanonicalVerifierComponents :
  Pnp3.Magnification.CanonicalAsymptoticVerifierComponents
```

Equivalent downstream theorem sufficient for this probe:

```lean
theorem canonicalAsymptotic_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

Equivalent final theorem sufficient for the consumers:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
  ∀ n : Nat, ∀ β : Rat,
    Pnp3.ComplexityInterfaces.InPpolyDAG
      (Pnp3.Models.gapPartialMCSP_Language
        ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
            Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

Why YELLOW rather than `INCONCLUSIVE_NEEDS_LEAN`: the missing construction is not a ≤200 LOC staging theorem.  The repo's own verifier scaffold estimates the concrete TM/verifier implementation at ~800--1500 LOC, and the direct DAG route would need comparable new syntax/semantics plumbing for a uniform polynomial-size DAG family over all canonical lengths.  A ≤200 LOC file could at most restate the target or use forbidden/refuted imports; it would not kernel-check the missing TM/circuit construction.

## 8. NoGo cross-check

PR 13 and NOGO-000004/000006/000008/000009 do not forbid the three attack routes above, but they constrain how the result must be interpreted.

- PR 13 refutes `FormulaCertificateProviderPartial`; the registry explains that its universal quantification over arbitrary `PpolyFormula (gapPartialMCSP_Language p)` is satisfied by Probe-2 truth-table hardwiring and then contradicts locality.  This forbids importing or promoting the refuted provider route, but it does not refute a DAG-side `hInDag` witness.
- NOGO-000004 and NOGO-000006 are hardwiring failures for support-cardinality filters on formula-side/log-width truth-table payloads.  They warn that syntactic/support filters cannot distinguish arbitrary hardwiring from intended structure.  They do not invalidate a legitimate `P`-to-`PpolyDAG` compiler construction.
- NOGO-000008 and NOGO-000009 rule out syntactic-only provenance-filter designs and a natural normalization patch.  Again, they apply to AC0/locality support-filter side tracks, not to the TM-shaped `P` proof or the canonical DAG compiler.

The key restriction from the NoGo material is methodological: if a future RED proof uses truth-table hardwiring, it must not be advertised as mainline `P != NP` progress and must not re-enable any refuted formula/locality predicates.

## 9. Verdict-specific consequence

Because the verdict is `YELLOW_INCONCLUSIVE`, the construction that would settle the probe is:

```lean
def buildCanonicalVerifierComponents :
  Pnp3.Magnification.CanonicalAsymptoticVerifierComponents
```

or equivalently:

```lean
theorem canonicalAsymptotic_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

or directly:

```lean
theorem canonicalAsymptotic_in_PpolyDAG :
  Pnp3.ComplexityInterfaces.PpolyDAG
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

Once any one of these exists on the non-refuted surface, the downstream slice family can be obtained by the existing canonical-length bridge and global-to-slice `PpolyDAG` transport, followed by extracting the `InPpolyDAG` witness from the existential definition of `PpolyDAG`.

This is out of D0 scope because the needed proof is a concrete TM/circuit-construction project, not merely a route audit.  The next action is `open_hInDag_triviality_probe_L0`, focused specifically on either the `CanonicalAsymptoticVerifierComponents` implementation or a direct polynomial-size `DagCircuit` family for `decideAsymptotic`.

## 10. Scope statement

No mainline Lean source was introduced or edited.  No staging Lean file was introduced because the verdict is not `INCONCLUSIVE_NEEDS_LEAN`.  No spec, JSONL, NoGoLog, `known_guards`, trust-root surface, `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or `P ≠ NP` claim was introduced.  No refuted predicate was imported or promoted.  The only repository change for this task is this markdown report under `seed_packs/hInDag_triviality_probe_D0/reports/`.

## 11. Commands run

```sh
pwd && find .. -name AGENTS.md -print
```

```sh
cat AGENTS.md && printf '\n--- prompt ---\n' && cat seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
```

```sh
sed -n '1,260p' seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
```

```sh
sed -n '260,520p' seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
```

```sh
git status --short --branch && git rev-parse HEAD && git checkout -b hindag-triviality-probe-d0
```

```sh
for f in RESEARCH_CONSTITUTION.md STATUS.md seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl; do echo '---' $f; test -e $f && wc -l $f || echo MISSING; done
```

```sh
find seed_packs/post_pr13_provider_retarget_D0 -maxdepth 3 -type f -print 2>/dev/null || true; find seed_packs -path '*provider_retarget*' -type f -print
```

```sh
rg -n "canonicalAsymptoticSpec|canonicalAsymptoticParams|canonicalAsymptoticHAsym|sYES|sNO|eventualGapSliceFamily_of_asymptotic|def decideAsymptotic|theorem decideAsymptotic_iff|def decideYesAt1|theorem decideYesAt1|def findCanonicalSlice|findCanonicalSlice_iff|decideAsymptotic_of_not_canonical|gapPartialMCSP_Language|gapPartialMCSP_AsymptoticLanguage|Partial.inputLen|def InPpolyDAG|abbrev InPpolyDAG|def P |def PpolyDAG|P_subset_PpolyDAG|PpolyStraightLine|proved_P_subset_PpolyDAG_internal|AsymptoticIsoStrongRoute|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually|FormulaCertificateProviderPartial|NOGO-00000[4689]" RESEARCH_CONSTITUTION.md STATUS.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl
```

```sh
sed -n '220,285p' pnp3/Magnification/CanonicalAsymptoticTrackData.lean; sed -n '1,260p' pnp3/Magnification/CanonicalAsymptoticDecider.lean; sed -n '720,770p' pnp3/Magnification/CanonicalAsymptoticDecider.lean; sed -n '430,485p' pnp3/Magnification/CanonicalAsymptoticDecider.lean
```

```sh
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '85,260p'; nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '150,225p'; nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '700,760p'
```

```sh
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '1,225p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '1,120p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '650,760p'
```

```sh
rg -n "def inputLen|abbrev inputLen|def tableLen|abbrev tableLen|def gapPartialMCSP_Language|def gapPartialMCSP_AsymptoticLanguage|structure GapPartialMCSPParams|GapPartialMCSP_Asymptotic_TMWitness" pnp3/Models/Model_PartialMCSP.lean; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '20,90p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '560,630p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '830,890p'
```

```sh
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '90,125p'; nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '630,650p'; rg -n "namespace Partial|tableLen|inputLen" pnp3 -g'*.lean' | head -30
```

```sh
rg -n "namespace Partial|def tableLen|def inputLen" pnp3/Models/Model_PartialMCSP.lean pnp3 -g'*.lean'
```

```sh
nl -ba pnp3/Models/PartialTruthTable.lean | sed -n '30,45p'; nl -ba pnp3/Complexity/Interfaces.lean | sed -n '240,360p'; nl -ba pnp3/Complexity/Interfaces.lean | sed -n '700,770p'; nl -ba pnp3/Complexity/PsubsetPpolyDAG_Internal.lean | sed -n '1,70p'; nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '560,625p'
```

```sh
rg -n "def P |abbrev P |def NP |def PpolyDAG|def InPpolyDAG|structure InPpolyDAG|def P_subset_PpolyDAG" pnp3/Complexity/Interfaces.lean
```

```sh
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '45,65p'; nl -ba pnp3/Complexity/Interfaces.lean | sed -n '430,455p'; nl -ba pnp3/Complexity/Interfaces.lean | sed -n '645,655p'
```

```sh
rg -n "namespace Complexity|abbrev P|def P |structure TM|exists_poly_tm_for_P" pnp3/Complexity/PsubsetPpolyInternal -g'*.lean' pnp3/Complexity/Simulation/Circuit_Compiler.lean
```

```sh
nl -ba pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean | sed -n '31,72p'; nl -ba pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean | sed -n '40,70p'
```

```sh
rg -n "P \\(.*gapPartialMCSP|gapPartialMCSP.* P|gapPartialMCSP_Asymptotic.*P|InPpolyDAG \\(gapPartialMCSP|PpolyDAG \\(gapPartialMCSP|decideAsymptotic.*poly|poly.*decideAsymptotic|CanonicalAsymptoticVerifierComponents|GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec" pnp3 -g'*.lean'
```

```sh
nl -ba pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean | sed -n '1,120p'; nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '218,282p'; nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '900,915p'
```

```sh
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '902,980p'; rg -n "eventualGapSliceFamily_of_asymptotic|ppolyDAG_fixed_of_asymptotic|InPpolyDAG.*Asymptotic|PpolyDAG.*AsymptoticLanguage.*canonical" pnp3/Magnification/FinalResultMainline.lean pnp3 -g'*.lean'
```

```sh
nl -ba pnp3/Magnification/AsymptoticDAGCollapse.lean | sed -n '60,95p'; nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '160,200p'
```

```sh
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '1,130p'; nl -ba pnp3/RefutedPredicates/Registry.lean | sed -n '100,130p'
```

```sh
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '128,235p'
```

```sh
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '235,315p'
```

```sh
rg -n "ppolyDAG.*ppolyFormula|ppolyFormula.*ppolyDAG|PpolyFormula.*PpolyDAG|PpolyDAG.*PpolyFormula|Formula.*DAG|DAG.*Formula" pnp3/Complexity pnp3 -g'*.lean'
```

```sh
rg -n "constFalseDag|truth-table|truth table|ttDag|DagCircuit.*rename|fixedSlice.*PpolyDAG|gapPartialMCSP.*in_PpolyDAG|InPpolyDAG.*fixed|fixed.*InPpolyDAG" pnp3 -g'*.lean'
```

```sh
nl -ba pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean | sed -n '1390,1495p'
```

```sh
nl -ba pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean | sed -n '1490,1510p'
```

```sh
python3 - <<'PY'
import json
for line in open('outputs/nogolog.jsonl'):
    o=json.loads(line)
    if o['id'] in {'NOGO-000004','NOGO-000006','NOGO-000008','NOGO-000009'}:
        print(o['id'], o['failure_class'], o['method_family'])
        print(o.get('structural_pattern','')[:500])
        print(o.get('why_generalizes','')[:500])
        print()
PY
```

```sh
./scripts/check.sh
```
