# hInDag triviality probe D0 — gpt55

## 1. Executive verdict

`YELLOW_INCONCLUSIVE`

Short version: the canonical decider is mathematically polynomial-time by direct source inspection, and the repository already has a coarse `P_subset_PpolyDAG` compiler endpoint.  However, the in-repo compiler consumes the formal `ComplexityInterfaces.P` predicate, which is a TM witness with a polynomial runtime bound, not a bare Lean Boolean function or a metatheoretic runtime argument.  I found no existing theorem proving `ComplexityInterfaces.P (Models.gapPartialMCSP_AsymptoticLanguage Magnification.canonicalAsymptoticSpec)` or per-slice `ComplexityInterfaces.P (Models.gapPartialMCSP_Language p)`.  The exact missing construction is a concrete TM/polytime witness for `decideAsymptotic`; the repo itself documents this as a multi-session TM-engineering target, not a ≤200 LOC L0 addition.

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
- `pnp3/Magnification/FinalResultMainline.lean`.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- `pnp3/RefutedPredicates/Registry.lean`.
- `outputs/nogolog.jsonl`, especially `NOGO-000004`, `NOGO-000006`, `NOGO-000008`, `NOGO-000009`.

Missing / moved:

- Required reading path `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md` is absent on this checkout.  `rg --files seed_packs | rg 'provider_retarget|post_pr13'` returned no matching path.

## 3. Statement under test

At the canonical instantiation, the `hInDag` family consumed by the asymptotic routes is:

```lean
∀ n : Nat, ∀ β : Rat,
  Pnp3.ComplexityInterfaces.InPpolyDAG
    (Pnp3.Models.gapPartialMCSP_Language
      ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
          Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

This is the witness-level version of the family quantified in `AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`, and `AsymptoticPromiseYesWeakRouteEventually`.  Those route definitions quantify `hInDag` as a function returning `ComplexityInterfaces.InPpolyDAG` for every `(n, β)` slice, not merely `PpolyDAG` propositions.

Unfolding the adapter, `eventualGapSliceFamily_of_asymptotic hAsym` sets:

```lean
paramsOf n _β := hAsym.pAt (max n hAsym.N0) (Nat.le_max_right _ _)
```

For `canonicalAsymptoticHAsym`, this means the actual per-slice parameter is `canonicalAsymptoticParams (max n 8) _`, independent of `β`.

## 4. Route 1 audit — P-membership + compiler bridge

### Search result for P-membership theorems

I searched `pnp3/` for theorem surfaces of the requested shape:

```sh
rg -n "ComplexityInterfaces\.P\s*\(|\bP\s*\(gapPartialMCSP|gapPartialMCSP_.*in_P|InPpolyDAG.*gapPartialMCSP|gapPartialMCSP.*InPpolyDAG|PpolyDAG.*gapPartialMCSP|gapPartialMCSP.*PpolyDAG" pnp3 -g '*.lean'
```

Findings:

- No theorem of shape
  ```lean
  Pnp3.ComplexityInterfaces.P (Pnp3.Models.gapPartialMCSP_Language _)
  ```
  was found.
- No theorem of shape
  ```lean
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage _)
  ```
  was found.
- Many hits are consumers or negative/refuted routes taking `PpolyDAG`/`InPpolyDAG` as an assumption.
- The relevant unconditional positive fixed-slice hardwiring theorem found is only formula-side:
  ```lean
  theorem fixedSlice_gapPartialMCSP_in_PpolyFormula
      (p : GapPartialMCSPParams) :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)
  ```
  It appears in `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` and uses truth-table hardwiring at the single active input length.  This does not directly supply `ComplexityInterfaces.P`, `ComplexityInterfaces.PpolyDAG`, or `ComplexityInterfaces.InPpolyDAG`.

### Exact compiler bridge

The public strict `P` abbreviation is TM-based:

```lean
abbrev P : Language → Prop := Internal.PsubsetPpoly.Complexity.P.{0}
```

The underlying internal definition is:

```lean
def polyTimeDecider (L : Language) : Prop :=
  ∃ (M : TM.{u}) (c : ℕ),
    (∀ n, M.runTime n ≤ n ^ c + c) ∧
    (∀ n (x : Bitstring n), TM.accepts (M := M) (n := n) x = L n x)

def P (L : Language) : Prop := polyTimeDecider.{u} L
```

The intermediate predicate inside the compiler route is `P_subset_PpolyStraightLine`:

```lean
structure InPpolyStraightLine (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, StraightLineCircuit n
  family_size_le : ∀ n, (toDag (family n)).size ≤ polyBound n
  correct : ∀ n (x : Bitstring n), eval (family n) x = L n x

def PpolyStraightLine (L : Language) : Prop :=
  ∃ _ : InPpolyStraightLine L, True

def P_subset_PpolyStraightLine : Prop :=
  ∀ L : Language, P L → PpolyStraightLine L

theorem P_subset_PpolyDAG_of_P_subset_PpolyStraightLine :
    P_subset_PpolyStraightLine → P_subset_PpolyDAG
```

The no-arg internal endpoint already provides the coarse compiler:

```lean
theorem proved_P_subset_PpolyDAG_internal :
    P_subset_PpolyDAG
```

Therefore Route 1 closes only after a `P` witness is available.  It does **not** close from the existing canonical decider alone.

### Gap estimate

If a theorem existed:

```lean
theorem canonicalAsymptotic_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

then the global proposition-level DAG conclusion would be a tiny composition with `proved_P_subset_PpolyDAG_internal`.  A separate witness-extraction theorem would still be needed to turn the proposition

```lean
Pnp3.ComplexityInterfaces.PpolyDAG L
```

into a chosen `Pnp3.ComplexityInterfaces.InPpolyDAG L` if the target demands the witness-level family directly.  That extraction is logically small and classical:

```lean
noncomputable def inPpolyDAG_of_PpolyDAG
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.PpolyDAG L) :
    Pnp3.ComplexityInterfaces.InPpolyDAG L := Classical.choose h
```

But the hard part is not this extraction; it is the missing formal `P` theorem, i.e. a concrete TM for the decider with a polynomial runtime proof.

## 5. Route 2 audit — canonical decider + compiler

### Compiler input shape

The compiler does not consume a Lean function, a `Decidable` instance, or an informal algorithm.  It consumes `ComplexityInterfaces.P L`, which expands to an internal TM witness:

```lean
∃ (M : Internal.PsubsetPpoly.TM) (c : ℕ),
  (∀ n, M.runTime n ≤ n ^ c + c) ∧
  (∀ n (x : Bitstring n),
    Internal.PsubsetPpoly.TM.accepts (M := M) (n := n) x = L n x)
```

The canonical decider has type:

```lean
def decideAsymptotic (N : Nat) (x : Bitstring N) : Bool
```

and correctness theorem:

```lean
theorem decideAsymptotic_iff (N : Nat) (x : Bitstring N) :
  decideAsymptotic N x = true ↔
    gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec N x = true
```

This is pointwise Boolean correctness, not a TM acceptance theorem.  It therefore does not already satisfy the compiler input shape.

### Polynomial-time status of `decideAsymptotic`

By tracing the implementation, the intended runtime argument is confirmed at the mathematical/algorithmic level:

- `size1Candidates m` is exactly the list:
  ```lean
  Circuit.const false :: Circuit.const true ::
    (List.finRange m).map Circuit.input
  ```
  so it has `m + 2` candidates.
- `decideYesAt1 m T` computes:
  ```lean
  (size1Candidates m).any (fun C => is_consistent_bool C T)
  ```
- `findCanonicalSlice N` searches `List.range (N + 1)` for an `m` with `Partial.inputLen m = N`.
- `decideAsymptotic N x` returns `false` if `findCanonicalSlice N = none`; otherwise it casts `x` to the canonical length and calls `decideYesAt1 m (decodePartial x)`.
- `decideAsymptotic_of_not_canonical` proves the off-canonical semantic case returns `false`.

The source therefore supports the heuristic runtime:

- At canonical length `N = Partial.inputLen m = 2 * 2^m`, `decideYesAt1` checks `m + 2` candidates.
- Each `is_consistent_bool` pass ranges over the partial truth-table rows, i.e. `2^m` table positions in the intended model.
- Total candidate-consistency work is `(m + 2) * 2^m`, which is `O(N log N)` because `N = 2 * 2^m`.
- Off canonical lengths are rejected after the `findCanonicalSlice` search over at most `N + 1` candidate slice indices.  Even allowing arithmetic costs, the intended formal route is polynomial in `N`.

However, I found no in-repo runtime lemma such as:

```lean
theorem decideAsymptotic_polytime :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

nor a lower-level `Internal.PsubsetPpoly.TM` package implementing `decideAsymptotic`.

### Off-canonical case

The off-canonical behavior is explicitly handled by:

```lean
theorem decideAsymptotic_of_not_canonical (N : Nat) (x : Bitstring N)
    (h : ¬ ∃ m, N = Partial.inputLen m) :
    decideAsymptotic N x = false
```

So a future compiler/TM construction can use the same constant-false behavior off canonical lengths.  But that theorem is still just a semantic equation for the Lean function.

## 6. Route 3 audit — direct algorithmic argument from `sYES=1, sNO=2`

Confirmed source facts:

- `canonicalAsymptoticParams` sets `sYES := 1` and `sNO := 2`.
- `canonicalAsymptoticHAsym` is an unconditional `AsymptoticFormulaTrackHypothesis` with `N0 := 8` and `pAt := canonicalAsymptoticParams`.
- `Partial.inputLen` is documented/formalized as `2 * 2^n` via `partialInputLen`; `gapPartialMCSP_Language p` is false off its one active length and decodes only at `partialInputLen p`.
- `gapPartialMCSP_AsymptoticLanguage spec` is false off canonical lengths and checks `PartialMCSP_YES_at n (spec.sYES n)` at canonical length.
- `decideAsymptotic_iff` proves the computable decider matches the canonical asymptotic language pointwise.

The heuristic polynomial-time argument is therefore correct as a mathematical algorithmic argument.  It is not currently a formal `ComplexityInterfaces.P` theorem because the repository's `P` class is deliberately TM-faithful.

The exact missing intermediate theorem between “`decideAsymptotic` is polynomial-time” and a DAG conclusion for the asymptotic language is:

```lean
theorem canonicalAsymptotic_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
```

Equivalently, at the lower engineering boundary:

```lean
structure CanonicalAsymptoticVerifierComponents where
  M : Pnp3.Internal.PsubsetPpoly.TM.{0}
  c : Nat
  k : Nat
  runTime_poly : ∀ n,
    M.runTime (n + certificateLength n k) ≤
      (n + certificateLength n k) ^ c + c
  accepts_eq : ∀ n (x : Bitstring n) (w : Bitstring (certificateLength n k)),
    Pnp3.Internal.PsubsetPpoly.TM.accepts
      (M := M)
      (n := n + certificateLength n k)
      (concatBitstring x w) = decideAsymptotic n x
```

The repo already provides the bridge from these components to the canonical TM witness and then to the canonical asymptotic data, but it does not provide the concrete components.

## 7. Cross-route synthesis

- **Route 1 does not close.**  The compiler endpoint exists, but the antecedent `ComplexityInterfaces.P` for either the per-slice or canonical asymptotic language is absent.
- **Route 2 does not close.**  `decideAsymptotic` has pointwise correctness, but the compiler input is a concrete TM/polytime witness, not a Lean function.
- **Route 3 confirms the algorithmic polynomial-time story but does not close in Lean.**  The implementation is consistent with `O(N log N)` at canonical lengths and polynomial off canonical lengths.  The missing formal object is still the TM/polytime implementation of that decider.

Precise missing intermediate theorems / constructions:

1. Global P theorem:
   ```lean
   theorem canonicalAsymptotic_in_P :
     Pnp3.ComplexityInterfaces.P
       (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
         Pnp3.Magnification.canonicalAsymptoticSpec)
   ```
2. Optional proposition-to-witness extraction after applying the compiler:
   ```lean
   noncomputable def inPpolyDAG_of_PpolyDAG
       {L : Pnp3.ComplexityInterfaces.Language}
       (h : Pnp3.ComplexityInterfaces.PpolyDAG L) :
       Pnp3.ComplexityInterfaces.InPpolyDAG L := Classical.choose h
   ```
3. Per-slice transfer, if the final target remains exactly the route-family `hInDag` rather than a global asymptotic language statement:
   ```lean
   theorem canonical_eventual_slice_inPpolyDAG
       (n : Nat) (β : Rat) :
     Pnp3.ComplexityInterfaces.InPpolyDAG
       (Pnp3.Models.gapPartialMCSP_Language
         ((Pnp3.Magnification.eventualGapSliceFamily_of_asymptotic
             Pnp3.Magnification.canonicalAsymptoticHAsym).paramsOf n β))
   ```

The blocking theorem is not theorem (2); theorem (2) is small.  The blocking theorem is theorem (1), or equivalently the concrete `CanonicalAsymptoticVerifierComponents` implementation.  `STATUS.md` describes the concrete TM construction as the remaining open TM-verifier obligation and decomposes it as a multi-session construction, so D0 should not land a ≤200 LOC Lean file pretending to close it.

## 8. NoGo cross-check

The existing refutations do not directly forbid the three attack routes, but they constrain how conclusions may be reported.

- PR 13 refutes `FormulaCertificateProviderPartial`.  It depends on Probe 2 fixed-slice truth-table hardwiring and shows the formula-certificate route is inconsistent.  Therefore this hInDag probe must not import or promote the refuted certificate/provider surfaces.
- `NOGO-000004` and `NOGO-000006` are hardwiring attacks against support-cardinality/provenance filters.  They warn that truth-table-like nonuniform witnesses can satisfy apparently nontrivial support-diversity filters.  They do not refute a genuine TM-based proof that the canonical asymptotic language is in `P`, but they make formula/support provenance routes unsafe as mainline progress.
- `NOGO-000008` and `NOGO-000009` rule out syntactic-only provenance filter designs and natural normalization patches.  They again do not restrict a TM/polytime decider route, but they prevent reporting syntactic provenance fixes as progress.

Thus, none of `NOGO-000004/6/8/9` blocks constructing a `ComplexityInterfaces.P` witness for `decideAsymptotic`; they mainly block side attempts to rescue the old formula/provenance filters.

## 9. Verdict-specific consequence

For `YELLOW_INCONCLUSIVE`:

The specific Lean construction that would settle the probe is a concrete polynomial-time TM implementation of `decideAsymptotic`, packaged either as:

```lean
theorem canonicalAsymptotic_in_P :
  Pnp3.ComplexityInterfaces.P
    (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
      Pnp3.Magnification.canonicalAsymptoticSpec)
mkdir -p seed_packs/hInDag_triviality_probe_D0/reports
cat > seed_packs/hInDag_triviality_probe_D0/reports/D0_hindag_triviality_gpt55.md <<'EOF_REPORT'
# hInDag triviality probe D0 — gpt55
...
EOF_REPORT
./scripts/check.sh
```

or as an inhabitant of `Pnp3.Magnification.CanonicalAsymptoticVerifierComponents`, from which existing bridges can recover the canonical TM witness.  This is out of D0 scope because the repository documents it as the remaining TM-verifier construction, with `CanonicalAsymptoticDecider.lean` only reducing the obligation to that typed engineering target.  The expected construction is not a small wrapper around an existing theorem; it requires building and proving a TM that computes the slice detector, decoder, candidate enumeration, consistency checks, and Boolean output with a polynomial runtime bound.

No L0 Lean file was landed because the verdict is `YELLOW_INCONCLUSIVE`, not `INCONCLUSIVE_NEEDS_LEAN`.

Next action: `open_hInDag_triviality_probe_L0`, focused specifically on either (a) constructing `CanonicalAsymptoticVerifierComponents`, or (b) proving an explicit obstruction that the current TM interface lacks enough executable primitives to implement it without extending the internal TM library.

## 10. Scope statement

Confirmed scope:

- No mainline Lean source file was introduced or edited.
- No staging Lean file was introduced because the verdict is not `INCONCLUSIVE_NEEDS_LEAN`.
- No spec, JSONL, NoGoLog, `known_guards`, trust-root, `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or `P ≠ NP` claim was introduced.
- No refuted predicate was imported or promoted.
- No TM-verifier session work was performed.
- This report classifies the task as **Infrastructure / audit**, not P-vs-NP mainline progress.

## 11. Commands run

```sh
pwd && rg --files -g 'AGENTS.md' -g 'WORKER_PROMPT_D0.md' -g '!/.git'
cat AGENTS.md && printf '\n---PROMPT---\n' && cat seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
sed -n '1,260p' seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
sed -n '261,520p' seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md
git status --short && git rev-parse --abbrev-ref HEAD && git rev-parse HEAD
git switch -c worker/hindag-triviality-d0 || git switch worker/hindag-triviality-d0
for f in RESEARCH_CONSTITUTION.md STATUS.md seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl; do echo '###' $f; test -f "$f" && wc -l "$f" || echo MISSING; done
rg --files seed_packs | rg 'provider_retarget|post_pr13'
rg -n "canonicalAsymptoticSpec|canonicalAsymptoticParams|canonicalAsymptoticHAsym|decideAsymptotic|decideAsymptotic_iff|decideYesAt1|findCanonicalSlice|_iff|def P |def NP |def PpolyDAG|def PpolyFormula|def InPpolyDAG|PpolyStraightLine|P_subset_PpolyDAG|proved_P_subset_PpolyDAG_internal|gapPartialMCSP_Language|inputLen|eventualGapSliceFamily_of_asymptotic|AsymptoticIsoStrongRoute|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually|Probe 2|Probe 13|NOGO-000004|NOGO-000006|NOGO-000008|NOGO-000009" RESEARCH_CONSTITUTION.md STATUS.md seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyDAG_Internal.lean pnp3/Complexity/Simulation/Circuit_Compiler.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification/FinalResultMainline.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean outputs/nogolog.jsonl
sed -n '110,230p' pnp3/Magnification/CanonicalAsymptoticTrackData.lean
sed -n '90,190p' pnp3/Magnification/CanonicalAsymptoticDecider.lean
sed -n '340,470p' pnp3/Complexity/Interfaces.lean
sed -n '640,655p' pnp3/Complexity/Interfaces.lean
sed -n '1,80p' pnp3/Complexity/PsubsetPpolyDAG_Internal.lean
sed -n '570,625p' pnp3/Complexity/Simulation/Circuit_Compiler.lean
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '250,465p'
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '640,652p'
nl -ba pnp3/Complexity/PsubsetPpolyDAG_Internal.lean | sed -n '1,57p'
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '600,625p'
rg -n "^def P |^def NP |structure TM" pnp3/Complexity/Interfaces.lean
rg -n "\bP \(L|def P\b|def NP\b|structure.*P" pnp3/Complexity/Interfaces.lean | head -50
sed -n '1,80p' pnp3/Complexity/Interfaces.lean && rg -n "abbrev P|class P|P :" pnp3 -g '*.lean' | head -50
rg -n "abbrev NP|NP_TM" pnp3/Complexity/Interfaces.lean pnp3/Complexity/PsubsetPpolyInternal -g '*.lean' | head -80
nl -ba pnp3/Complexity/Interfaces.lean | sed -n '500,585p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,180p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '200,360p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '620,735p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '132,260p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '260,340p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '735,775p'
rg -n "def gapPartialMCSP_Language|def gapPartialMCSP_AsymptoticLanguage|def eventualGapSliceFamily_of_asymptotic|inputLen|partialInputLen|structure GapSliceFamily|paramsOf" pnp3/Models/Model_PartialMCSP.lean
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '70,125p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '600,655p'
nl -ba pnp3/Models/Model_PartialMCSP.lean | sed -n '690,710p'
rg -n "eventualGapSliceFamily_of_asymptotic|structure EventualGapSliceFamily|paramsOf|AsymptoticIsoStrongRoute|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually" pnp3/Magnification/FinalResultMainline.lean pnp3/Models/Model_PartialMCSP.lean pnp3/Magnification -g '*.lean'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '160,285p'
rg -n "ComplexityInterfaces\.P\s*\(|\bP\s*\(gapPartialMCSP|gapPartialMCSP_.*in_P|InPpolyDAG.*gapPartialMCSP|gapPartialMCSP.*InPpolyDAG|PpolyDAG.*gapPartialMCSP|gapPartialMCSP.*PpolyDAG" pnp3 -g '*.lean'
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '200,235p'
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '590,620p'
nl -ba pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean | sed -n '120,155p'
rg -n "toDag|Dag.*Formula|Formula.*Dag|PpolyDAG_of_PpolyFormula|ppolyDAG.*Formula|PpolyFormula.*PpolyDAG|InPpolyDAG.*PpolyFormula|PpolyDAG_of" pnp3/Complexity pnp3 -g '*.lean' | head -100
head -40 pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean && head -50 pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean && sed -n '380,425p' pnp3/Complexity/Interfaces.lean
rg -n "def P \(|abbrev P|structure TM|def accepts|def runTime" pnp3/Complexity/PsubsetPpolyInternal -g '*.lean' | head -80
nl -ba pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean | sed -n '1,65p'
nl -ba pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean | sed -n '45,62p'
nl -ba pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean | sed -n '175,190p'
python3 - <<'PY'
import json
for line in open('outputs/nogolog.jsonl'):
    o=json.loads(line)
    if o['id'] in ['NOGO-000004','NOGO-000006','NOGO-000008','NOGO-000009']:
        print(o['id'], o.get('candidate_id'), o.get('failure_class'), o.get('method_family'))
        print(o.get('structural_pattern','')[:700])
        print(o.get('why_generalizes','')[:700])
        print('---')
PY
nl -ba STATUS.md | sed -n '15,80p'
nl -ba STATUS.md | sed -n '115,155p'
nl -ba STATUS.md | sed -n '183,212p'
./scripts/check.sh
git status --short
./scripts/check.sh
rm -rf /tmp/p-np2-base-check && git worktree add --detach /tmp/p-np2-base-check ac96653ef5115bb407b3c1ca3137000c0758dabf && cd /tmp/p-np2-base-check && ./scripts/check.sh
pkill -TERM -f '/tmp/p-np2-base-check|lake|lean' || true
mkdir -p seed_packs/hInDag_triviality_probe_D0/failures
cat > seed_packs/hInDag_triviality_probe_D0/failures/check_flake_gpt55.md <<'EOF_FAILURE'
# check.sh coordinator flake note — hInDag triviality probe D0
...
EOF_FAILURE
```
