# hInDag triviality probe D0 — gpt55

## 1. Executive verdict

`YELLOW_INCONCLUSIVE`

The canonical `hInDag` family is **not already trivially provable from the searched mainline surfaces** by Route 1, Route 2, or Route 3.  The direct polynomial-time story for `sYES = 1, sNO = 2` is mathematically compelling, but the repository's usable `P ⊆ PpolyDAG` compiler consumes a concrete `ComplexityInterfaces.P` witness, i.e. a polynomial-time TM package.  The current code has the Boolean decider and correctness theorem, but not a `P` witness / concrete TM for that decider.

The blocking construction is therefore:

```lean
theorem canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

or equivalently a concrete no-certificate TM package computing
`Pnp3.Magnification.decideAsymptotic` in polynomial time, from which the theorem above follows.  This is not present in the repo and is not a ≤200 LOC D0 staging theorem: the project itself documents the matching TM engineering as a multi-session construction.

## 2. Required-reading inventory

Read / inspected:

- `RESEARCH_CONSTITUTION.md`.
- `STATUS.md`.
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md`.
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`.
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`.
- `pnp3/Complexity/Interfaces.lean`.
- `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`.
- `pnp3/Complexity/Simulation/Circuit_Compiler.lean`.
- `pnp3/Models/Model_PartialMCSP.lean`.
- `pnp3/Magnification/FinalResultMainline.lean`, especially the route definitions at lines 218--282.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- `pnp3/RefutedPredicates/Registry.lean`.
- `outputs/nogolog.jsonl`, especially NOGO-000004, NOGO-000006, NOGO-000008, and NOGO-000009.
- Additional relevant files discovered while auditing:
  - `pnp3/Magnification/AsymptoticDAGCollapse.lean`.
  - `pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean`.

Missing required reading:

- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md` is absent in this checkout.  `find seed_packs/post_pr13_provider_retarget_D0 -maxdepth 3 -type f -print` returned no files because the directory/report is not present.

## 3. Statement under test

The exact family under test at the canonical instantiation is:

```lean
∀ n β,
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language
      ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
          Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

This is the `hInDag` argument shape consumed by the asymptotic route definitions.  `AsymptoticIsoStrongRoute` quantifies over exactly this `InPpolyDAG` family at `FinalResultMainline.lean:220--224`; the promise-YES certificate route uses the same family at lines 240--244; and the weak eventual route uses it at lines 267--271.

Because `eventualGapSliceFamily_of_asymptotic` defines `paramsOf n β := hAsym.pAt (max n hAsym.N0) ...`, the canonical instantiation always points to a legal canonical slice at `max n 8`, independent of `β`.

## 4. Route 1 audit — P-membership + compiler bridge

### 4.1 Search for existing `P` membership

I searched `pnp3/` for in-repo theorem surfaces of the shape:

- `ComplexityInterfaces.P (gapPartialMCSP_Language _)`;
- `ComplexityInterfaces.P (gapPartialMCSP_AsymptoticLanguage _)`;
- nearby `gapPartialMCSP_*_in_P` names.

No theorem of either exact shape was found.

Relevant positive findings were NP/TM-witness surfaces, not P surfaces:

```lean
theorem gapPartialMCSP_in_NP_of_TM
    (p : GapPartialMCSPParams) :
    gapPartialMCSP_in_NP_TM p → NP (gapPartialMCSP_Language p)
```

and

```lean
theorem gapPartialMCSP_Asymptotic_in_NP_of_TM
    (spec : GapPartialMCSPAsymptoticSpec) :
    gapPartialMCSP_Asymptotic_in_NP_TM spec →
      NP (gapPartialMCSP_AsymptoticLanguage spec)
```

These are not enough for `proved_P_subset_PpolyDAG_internal`, whose input is `P`, not `NP`.

### 4.2 Exact compiler bridge and intermediate predicate

The active bridge is:

```lean
theorem proved_P_subset_PpolyDAG_internal :
    P_subset_PpolyDAG
```

in `pnp3/Complexity/Simulation/Circuit_Compiler.lean:602--608`.

Its proof shape goes through the straight-line intermediate:

```lean
theorem P_subset_PpolyDAG_of_P_subset_PpolyStraightLine :
    P_subset_PpolyStraightLine → P_subset_PpolyDAG
```

where

```lean
def P_subset_PpolyStraightLine : Prop :=
  ∀ L : Language, P L → PpolyStraightLine L
```

in `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean:43--54`.

Inside the compiler proof, a `P L` witness is unpacked via:

```lean
theorem exists_poly_tm_for_P {L : Language} :
    P L →
      ∃ (M : TM) (c : Nat),
        (∀ n, M.runTime n ≤ n ^ c + c) ∧
        (∀ n (x : Bitstring n), TM.accepts M n x = L n x)
```

at `pnp3/Complexity/Simulation/TM_Encoding.lean:35--43`.  Thus the compiler's exact input is not a Lean function, a `Decidable` instance, or a semantic decider theorem alone; it is a concrete polynomial-time TM packaged as `ComplexityInterfaces.P`.

### 4.3 Gap estimate

If the missing theorem

```lean
canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

already existed, the rest of Route 1 would be small:

1. Apply `Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal` to get
   `PpolyDAG (gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec)`.
2. Use the public fixed-slice bridge
   `Pnp3.Magnification.ppolyDAG_fixed_of_asymptotic_slice` from
   `pnp3/Magnification/AsymptoticDAGCollapse.lean:66--74`, instantiated with the canonical slice equality supplied by `canonicalAsymptoticHAsym.sliceEq`.
3. Destructure the resulting `PpolyDAG` existential to obtain the required
   `InPpolyDAG` witness for each `n β`.

That packaging is plausibly tens of Lean lines.  The non-small part is proving the `P` theorem itself.

## 5. Route 2 audit — canonical decider + compiler

### 5.1 Compiler input shape

`decideAsymptotic` has type:

```lean
def decideAsymptotic (N : Nat) (x : Bitstring N) : Bool
```

and the correctness theorem is:

```lean
theorem decideAsymptotic_iff (N : Nat) (x : Bitstring N) :
    decideAsymptotic N x = true ↔
      gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec N x = true
```

in `pnp3/Magnification/CanonicalAsymptoticDecider.lean:197--203` and `243--261`.

This does **not** already satisfy the compiler input shape.  The compiler requires `P L`, which unfolds to a polynomial-time TM witness.  The repo has a TM-oriented component structure:

```lean
structure CanonicalAsymptoticVerifierComponents where
  M : Internal.PsubsetPpoly.TM.{0}
  c : Nat
  k : Nat
  runTime_poly : ∀ n,
    M.runTime (n + certificateLength n k) ≤
      (n + certificateLength n k) ^ c + c
  accepts_eq : ∀ n (x : Bitstring n) (w : Bitstring (certificateLength n k)),
    Internal.PsubsetPpoly.TM.accepts
      (M := M)
      (n := n + certificateLength n k)
      (concatBitstring x w) = decideAsymptotic n x
```

at `pnp3/Magnification/CanonicalAsymptoticDecider.lean:702--720`.  But this is a structure definition, not an inhabitant, and it targets the NP-style verifier architecture with certificates.  It yields `GapPartialMCSP_Asymptotic_TMWitness` if a component package is supplied, as shown at lines 727--745; it does not itself produce `P` membership.

### 5.2 Polynomial-time implementation evidence

The implementation is small and visibly polynomial as a mathematical algorithm:

- `findCanonicalSlice N` scans `List.range (N + 1)` and tests `Partial.inputLen m = N` (`CanonicalAsymptoticDecider.lean:132--134`).
- At canonical length it calls `decideYesAt1 m (decodePartial x)` (`CanonicalAsymptoticDecider.lean:197--203`).
- `decideYesAt1` enumerates `size1Candidates m`, and `size1Candidates m` is exactly `const false`, `const true`, and the `m` projections (`CanonicalAsymptoticDecider.lean:43--47`, `106--108`).
- The theorem `decideYesAt1_iff` proves this enumeration exactly characterizes `PartialMCSP_YES_at m 1` (`CanonicalAsymptoticDecider.lean:110--123`).
- The theorem `decideAsymptotic_at_inputLen_iff_size1` gives the closed row-wise condition: either a constant candidate is consistent or some projection candidate is consistent (`CanonicalAsymptoticDecider.lean:461--474`).

However, I found no Lean theorem bounding the runtime of `decideAsymptotic` as a TM, no `ComplexityInterfaces.P` theorem for the canonical asymptotic language, and no theorem directly producing `PpolyDAG` from this decider.

### 5.3 Off-canonical lengths

The off-canonical semantic behavior is already closed:

```lean
theorem decideAsymptotic_of_not_canonical (N : Nat) (x : Bitstring N)
    (h : ¬ ∃ m, N = Partial.inputLen m) :
    decideAsymptotic N x = false
```

at `pnp3/Magnification/CanonicalAsymptoticDecider.lean:222--233`, with the matching language theorem at lines 235--241.  A future compiler/TM proof can use the same constant-false behavior off canonical lengths, but that proof is still not present.

## 6. Route 3 audit — direct algorithmic argument from `sYES=1, sNO=2`

The heuristic polynomial-time argument is confirmed at the level of the Lean implementation's algorithmic structure.

- `canonicalAsymptoticSpec` sets `sYES := fun _ => 1` and `sNO := fun _ => 2` (`CanonicalAsymptoticTrackData.lean:46--57`).
- `canonicalAsymptoticParams` likewise sets fixed-slice `sYES := 1` and `sNO := 2` (`CanonicalAsymptoticTrackData.lean:113--124`), with simp lemmas for both fields at lines 129--133.
- `decideYesAt1 m T` runs `.any` over `size1Candidates m` (`CanonicalAsymptoticDecider.lean:106--108`).
- `size1Candidates m` is a list of length `m + 2` in content: two constants plus `List.finRange m` mapped to input projections (`CanonicalAsymptoticDecider.lean:43--47`).
- The canonical input length is `Partial.inputLen n`, and `partialInputLen p := Partial.inputLen p.n`; the model comment states this is `2 * 2^n` (`Model_PartialMCSP.lean:111--112`).
- The asymptotic language at canonical length decodes the partial table and checks `PartialMCSP_YES_at n (spec.sYES n)` (`Model_PartialMCSP.lean:620--635`, with the canonical-length theorem at lines 701--705).

Therefore, on canonical input length `N = Partial.inputLen m = 2 · 2^m`, the direct evaluator checks `m + 2` size-1 candidates, each against a table of `2^m` rows.  Measured in `N`, this is `O(N log N)` at the mathematical pseudocode level.  Off canonical lengths, `findCanonicalSlice` scans at most `N + 1` candidates, so that side is also polynomial in `N` at the same informal level.

But the exact missing intermediate theorem remains:

```lean
theorem canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

or a stronger theorem directly producing:

```lean
theorem canonicalAsymptoticLanguage_in_PpolyDAG :
  Pnp3.ComplexityInterfaces.PpolyDAG
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

with the first theorem followed by `proved_P_subset_PpolyDAG_internal` being the intended compiler route.

The repository explicitly records that the remaining obligation is a concrete TM matching `decideAsymptotic` with polynomial runtime.  `STATUS.md:191--223` lists the decomposition and describes the current open target as building a TM that ignores `w` and computes the known Bool function on `x`.  `GapMCSPVerifier.lean:97--105` similarly states the reduction target is `buildCanonicalVerifierComponents : CanonicalAsymptoticVerifierComponents` and describes it as a concrete TM realizing `decideAsymptotic` in polynomial time.

## 7. Cross-route synthesis

- **Route 1 does not close.**  The compiler bridge exists and is strong enough once `P` membership is available, but no canonical `P` theorem for `gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec` or fixed-slice `gapPartialMCSP_Language p` was found.
- **Route 2 does not close.**  `decideAsymptotic` is present and correct, but the compiler consumes a polynomial-time TM packaged as `P`, not a raw Lean Bool decider.
- **Route 3 does not close at D0.**  The direct runtime argument is confirmed informally from the implementation, but it still needs a concrete TM/runtime theorem to enter the repo's `P ⊆ PpolyDAG` pipeline.

The precise missing theorem that would settle all three compiler-based routes is:

```lean
theorem canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

A slightly more operational staging theorem would be:

```lean
def canonicalAsymptoticPDeciderComponents :
  -- a concrete TM M and exponent c such that
  --   ∀ N, M.runTime N ≤ N ^ c + c
  --   ∀ N x, TM.accepts M N x =
  --     Pnp3.Magnification.decideAsymptotic N x
```

followed by `decideAsymptotic_iff` to package `ComplexityInterfaces.P`.

For the final `hInDag` family, the downstream packaging theorem after `canonicalAsymptoticLanguage_in_P` would be:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
  ∀ n β,
    Pnp3.ComplexityInterfaces.InPpolyDAG
      (Pnp3.Models.gapPartialMCSP_Language
        ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
            Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

This wrapper is likely small **after** the `P` theorem exists.  It is not currently derivable from the searched surfaces alone.

## 8. NoGo cross-check

The existing refutations do not restrict the three attack routes directly:

- PR 13 refutes `FormulaCertificateProviderPartial`, and the registry lists it as a refuted predicate (`RefutedPredicates/Registry.lean:111--124`).  Routes 1--3 do not import or assume that provider.
- Probe 2 truth-table hardwiring shows that fixed-slice `gapPartialMCSP_Language p` is in `PpolyFormula` by nonuniform hardwiring (`FormulaSupportBoundsFalsifiabilityProbe.lean:30--44`, theorem at lines 218--220).  This explains why formula-support/provider routes are vacuous, but it is not the same as a uniform `P` witness nor an existing DAG witness for the canonical asymptotic language.
- NOGO-000004 and NOGO-000006 are hardwiring attacks against support-cardinality/provenance filters in the AC0/locality-support side track.
- NOGO-000008 and NOGO-000009 rule out syntactic-only ProvenanceFilter-v2 style patches and normalizer patches.

These NoGo entries warn against formula/provenance side routes and hardwiring overclaims.  They do not forbid proving a genuine TM-based `P` theorem for the canonical `sYES = 1` asymptotic language, nor do they provide such a theorem.

## 9. Verdict-specific consequence

For `YELLOW_INCONCLUSIVE`, the Lean construction that would settle the probe is:

```lean
theorem canonicalAsymptoticLanguage_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

plus the small wrapper:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
  ∀ n β,
    Pnp3.ComplexityInterfaces.InPpolyDAG
      (Pnp3.Models.gapPartialMCSP_Language
        ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
            Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

Why this is out of D0 scope:

- The report confirms the polynomial algorithm, but the in-repo `P` interface is TM-based.
- The repo's own documentation decomposes the concrete TM construction into a multi-session verifier plan (`STATUS.md:214--223`).
- `CanonicalAsymptoticVerifierComponents` is only a structure; no inhabitant exists in the searched tree.
- The conditional L0 Lean allowance is limited to ≤200 lines and exactly one probe theorem or negative companion.  A kernel-checked `P` theorem would require a concrete TM and runtime proof, not merely a semantic proof about a Lean function.

Next action under this verdict: `open_hInDag_triviality_probe_L0` focused specifically on constructing or ruling out the concrete `canonicalAsymptoticLanguage_in_P` theorem / TM package.

## 10. Scope statement

Confirmed scope:

- No mainline Lean source file was introduced or edited.
- No spec file was edited.
- No JSONL / NoGoLog file was edited.
- No `known_guards` file was edited.
- No trust-root surface was edited.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or `P ≠ NP` claim was introduced.
- No refuted predicate was imported, promoted, or used in a new theorem.
- No L0 Lean staging file was landed because the verdict is `YELLOW_INCONCLUSIVE`, not `INCONCLUSIVE_NEEDS_LEAN`.

This report is infrastructure/audit work, not mainline lower-bound progress.  It does not reduce `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.

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
git status --short && git rev-parse --abbrev-ref HEAD && git rev-parse HEAD
```

```sh
for f in RESEARCH_CONSTITUTION.md STATUS.md seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl; do echo "=== $f ==="; if [ -f "$f" ]; then wc -l "$f"; else echo MISSING; fi; done
```

```sh
find seed_packs/post_pr13_provider_retarget_D0 -maxdepth 3 -type f -print 2>/dev/null || true
find seed_packs/asymptotic_isostrong_route_audit_D0/reports -maxdepth 1 -type f -print
```

```sh
rg -n "canonicalAsymptotic|decideAsymptotic|decideYesAt1|findCanonicalSlice|gapPartialMCSP_Language|eventualGapSliceFamily|InPpolyDAG|PpolyStraightLine|proved_P_subset_PpolyDAG_internal|AsymptoticIsoStrongRoute|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually|FormulaCertificateProviderPartial|NOGO-000004|NOGO-000006|NOGO-000008|NOGO-000009" RESEARCH_CONSTITUTION.md STATUS.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl
```

```sh
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '360,465p'
nl -ba pnp3/Complexity/PsubsetPpolyDAG_Internal.lean | sed -n '1,80p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '540,625p'
```

```sh
rg -n "def P |structure P|def NP |def P_subset_PpolyDAG|exists_poly_tm_for_P|PolyTimeTM" pnp3/Complexity/Interfaces.lean pnp3/Complexity -g'*.lean'
```

```sh
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '600,665p'
nl -ba pnp3/Complexity/Simulation/TM_Encoding.lean | sed -n '1,70p'
nl -ba pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean | sed -n '1,70p'
```

```sh
rg -n "def gapPartialMCSP_Language|def gapPartialMCSP_AsymptoticLanguage|structure GapPartialMCSPParams|partialInputLen|inputLen|eventualGapSliceFamily_of_asymptotic|paramsOf" pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Magnification/CanonicalAsymptoticTrackData.lean
```

```sh
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '90,122p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '330,365p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '616,655p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '682,712p'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '218,286p'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '890,970p'
```

```sh
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '218,282p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '692,735p'
```

```sh
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '1,230p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,220p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '220,380p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '380,520p'
```

```sh
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '126,220p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,160p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '160,320p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '320,475p'
```

```sh
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,180p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '180,280p'
```

```sh
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '132,188p'
```

```sh
rg -n "ComplexityInterfaces\.P \(gapPartialMCSP|P \(gapPartialMCSP|gapPartialMCSP_.*_in_P|InPpolyDAG \(gapPartialMCSP_AsymptoticLanguage|PpolyDAG \(gapPartialMCSP_AsymptoticLanguage|GapPartialMCSP_Asymptotic_TMWitness|CanonicalAsymptoticVerifierComponents|witnessOfComponents|canonicalAsymptotic.*Ppoly|decideAsymptotic.*poly|poly.*decideAsymptotic|runTime.*decideAsymptotic|PartialMCSP.*PpolyDAG|gapPartialMCSP_Language.*InPpolyDAG" pnp3 -g'*.lean'
```

```sh
nl -ba pnp3/Magnification/AsymptoticDAGCollapse.lean | sed -n '1,160p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '690,772p'
nl -ba pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean | sed -n '80,110p'
nl -ba pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean | sed -n '220,235p'
```

```sh
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '1,90p'
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '600,648p'
nl -ba pnp3/RefutedPredicates/Registry.lean | sed -n '1,150p'
cat outputs/nogolog.jsonl | python3 - <<'PY'
import sys,json
for line in sys.stdin:
 d=json.loads(line)
 if d.get('id') in {'NOGO-000004','NOGO-000006','NOGO-000008','NOGO-000009'}:
  print(d['id'], d.get('failure_class'), d.get('method_family'), d.get('structural_pattern')[:300])
PY
```

```sh
python3 - <<'PY'
import json
for line in open('outputs/nogolog.jsonl'):
 d=json.loads(line)
 if d.get('id') in {'NOGO-000004','NOGO-000006','NOGO-000008','NOGO-000009'}:
  print('---',d['id'])
  for k in ['failure_class','method_family','status','structural_pattern','why_generalizes']:
   print(k+':', d.get(k,'')[:600])
PY
```

```sh
nl -ba STATUS.md | sed -n '1,90p'
nl -ba STATUS.md | sed -n '115,155p'
nl -ba STATUS.md | sed -n '183,224p'
nl -ba seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md | sed -n '1,80p'
nl -ba seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md | sed -n '330,390p'
```

```sh
nl -ba STATUS.md | sed -n '183,224p'
```

```sh
rg -n "fixedSlice_gapPartialMCSP_in_PpolyFormula|ppolyDAG_of|Formula.*DAG|toDag|FormulaCircuit.*DagCircuit|gapPartialMCSP.*PpolyFormula|PpolyFormula.*gapPartialMCSP" pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/Complexity -g'*.lean'
```

```sh
rg -n "PpolyDAG.*PpolyFormula|PpolyFormula.*PpolyDAG|Dag.*Formula|Formula.*Dag|toDag.*Formula|formula.*dag|FormulaCircuit.*Dag" pnp3/Complexity pnp3 -g'*.lean'
```

```sh
rg -n "structure GapSliceFamilyEventually|def eventualGapSliceFamily_of_asymptotic|paramsOf|AsymptoticFormulaTrackHypothesis" pnp3/Magnification/FinalResultMainline.lean pnp3/Models/Model_PartialMCSP.lean
```

```sh
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '36,62p'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '164,184p'
```

```sh
./scripts/check.sh
```
