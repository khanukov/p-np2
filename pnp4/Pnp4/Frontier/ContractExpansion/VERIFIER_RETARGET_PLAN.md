# VERIFIER_RETARGET_PLAN — the frozen NP-verifier target and its first slices

**Status:** versioned decision record; FEAS-0 outcome (a) discharged on
`work/feas0-target-bound` from `main = 7d65c77d`. **Original base of record:** `main = 98250643`
(`Merge pull request #1626 from khanukov/work/runtime-advice`).
**Authored on branch:** `work/verifier-retarget-plan`.

**Progress classification (AGENTS.md): Infrastructure.** This document freezes a target and
schedules specification/machine-interface work. The FEAS-0 implementation reduces neither
`VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound`, constructs no verifier TM, and
carries **no `P ≠ NP` claim**.

It supersedes, for everything on the current-`main` critical path, the earlier read-only planning
manifest `verifier-next-slices.md` (branch `work/verifier-planning`, base of record
`main = 5d8ee5f8`). §2 lists exactly which of that manifest's assumptions are now stale and which
survive. No implementation code is introduced here.

> **Revision note (revision 2).** The first revision of this file froze the target
> *unconditionally* and retired the length-gated target immediately. Review found a feasibility
> hole that makes both moves premature (§1.0), a **false** generic injectivity goal (§4.3), a
> gamma-canonicity hypothesis that is actually a **theorem** (§4.3), incorrect axiom expectations
> for P0 (§4.2), an unenforceable runtime-advice gate (§1.3 caveat 6), and several inventory /
> unit / range errors. All were resolved in revision 2.
>
> **Revision note (this revision, 3).** Two independent audits of revision 2 found that the new
> §1.0 reintroduced the very defect it had just fixed elsewhere: FEAS-0's outcomes (a) and (b) were
> stated over a **generic** codec, where both are false, while the frozen target is the concrete
> `treeCircuitWitnessCodec (thresholdPoly k)`; and (b) was presented as an alternative to (a) when
> in fact **(b) implies (a)**, so a failed (a) silently killed (b) too and would have forced the
> void outcome. Resolved: every FEAS statement is specialized to the concrete codec, the implication
> is stated, and a genuinely distinct fourth outcome — a polynomial-time *decision procedure* for
> the wide-target regime — is added (§1.0). The decisive decode is no longer left "open": at the
> concrete codec the all-blank witness decodes to `Circuit.input ⟨0, _⟩`, so the flagship oversized
> word is *rejected*, and the projection-table argument gives a full route to outcome (a). Also
> corrected: D1a's bridge structure is now `acc`-parameterized so its "no P0 dependency" claim holds
> at declaration level (§4.4/§4.5), the donor stack is "not a prerequisite" rather than
> "off the critical path" (§3.4), `RuntimeAdviceBarrier.lean`'s provenance (it landed with `#1626`,
> §3.1), the `TreeMCSP*` overlap count (§3.2), and the `readNatBE` citation (§4.3.2).
>
> **Revision note (this revision, 4).** Two independent audits of revision 3 agreed the route is
> sound and executable but found the FEAS-0 write-up not yet actionable, plus residual
> inconsistencies. Resolved here:
>
> * **The FEAS-0 proof conflated two different targets.** `ContentAccepts` reads its witness window,
>   its truth table and its relation conjunct at `pr.2.n` — the target the *narrow* parser returns —
>   not at the header value `n'`. Revision 3 wrote the whole route in terms of `n'`. The route is
>   rewritten around `r := pr.2.n`, with `parseTreeMCSPPrefixInput_length_convention`
>   (`PrefixParserConvention.lean:1231`) supplying `M n' = M r` (§1.0). This makes the route
>   *independent of I1*: it needs neither injectivity of `treeMCSPPrefixM codec` nor
>   `consumed = gammaLen r`.
> * **The truth-table slice was assumed to be available; it is not.**
>   `parseTreeMCSPPrefixInput_inversion` (`ContentPrefixExtensionCoincidence.lean:140`) exposes only
>   the length gate and the gamma decode — it says nothing about `input.x`. FEAS-0 now carries an
>   explicit scheduled lemma recovering that slice (§1.0), and its budget rises accordingly.
> * **FEAS-0 exit discipline was inconsistent**: (a) alone was declared green while the prose said a
>   verifier needs (b)'s computable rejection rule. The bounded-timeout construction that makes (a)
>   sufficient is now stated explicitly, together with the honest note that it is a
>   machine-construction argument, not a formalized theorem (§1.0).
> * **A failure of (a) is a family, not a word**: `¬(a)` is `∀ c, ∃ (N, z, n')`, not "a single
>   accepted word with super-polynomial decoded target" (§1.0).
> * **D1b's dependency on D1a was recorded in the graph but nowhere else** — the slice log, the
>   branch strategy and §4.5's own heading all named P0 only (§4.5, §5, §7.1).
> * **The `ContractExpansion/` divergence inventory was wrong in both directions**: nine paths
>   differ at the two tips, of which six are `.lean` modules added *independently on both sides* and
>   three (`ConsolidatedTreeSeparation.lean`, `PrefixExtensionNPWitness.lean`, the directory
>   `README.md`) differ only because `main` moved. Repo-wide the figure is 40 (§3.2).
> * Also corrected: P0's axiom rule now reads "standard triple **or lighter**", consistent with G9,
>   and §6.2's purity command no longer demands empty output it cannot get (§4.2, §6.2, §8); the
>   residual "off the critical path" donor wording in §4.7 (§3.4 had already withdrawn it); the
>   `readNatBE` recursion citation (§4.3.2); and outcome **(c)** was added to the unlock statements
>   (though §9's last bullet was missed — see revision 5).
>
> **Revision note (this revision, 5).** Two independent audits of revision 4 agreed the route is
> actionable and found no critical blocker, but flagged five residual defects plus two stale figures
> in the bottom line. All are fixed here, and none changes the route:
>
> * **The bounded-timeout argument made an invalid same-polynomial inference.** From
>   `2 ^ n' ≤ N ^ c + c` it does **not** follow that `M n' ≤ N ^ c + c`: `M` also carries
>   `gammaLen n'`, `idxWidth codec.witnessBits n'` and `codec.witnessBits n'`. The timeout is now
>   derived through the growth chain on `main` —
>   `polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly` (`WitnessGrowthReduction.lean:94`) plus
>   `PolyBoundedInTable.powAdd` (`ExtractedScheduleGrowth.lean:114`) — giving exponent `c · d`, not
>   `c`, and the certificate and witness windows are now counted explicitly (§1.0, §8 F0, §9).
>   Outcome (a) remains sufficient; what is withdrawn is "(a)'s exponent *is* the timeout".
> * **The opening "hole" paragraph still read `codec.verifies n' x w`.** The relation conjunct is at
>   `r := pr.2.n`; revision 4 fixed the route but not its own motivating paragraph (§1.0).
> * **§4's sequencing sentence still said "D1b follows P0"** although D1b needs P0 *and* D1a — the
>   one place revision 4 missed after correcting the heading, graph, branch strategy, gate table and
>   slice log (§4).
> * **The repo-wide divergence count is 40, not 41** (`git diff --name-status --diff-filter=M main
>   pr1618 | wc -l` = 40). The scoped `ContractExpansion/` inventory (nine shared differing paths,
>   six added on both sides, three `main`-only-changed) is unchanged and correct (§3.2).
> * **§9's last bullet carried the stale FEAS-0 budget and unlock condition** — `250–450 LOC · 1–2
>   modules` and "(a) or (b)" — contradicting §1.0's `350–600 LOC · 2 modules` and the
>   (a)/(b)/(c) policy stated everywhere else (§9).
>
> * Also corrected in revision 4: P0's axiom rule now reads "standard triple **or lighter**", consistent with G9,
>   and §6.2's purity command no longer demands empty output it cannot get (§4.2, §6.2, §8); the
>   residual "off the critical path" donor wording in §4.7 (§3.4 had already withdrawn it); the
>   `readNatBE` recursion citation (§4.3.2); and outcome **(c)** now appears in every unlock
>   statement, including §9.
>
> **Revision note (this revision, 6).** One blocker survived revision 5's audits: the bounded-timeout
> argument was fixed at the level of *which polynomial*, but not at the level of *which target*. Its
> steps still accounted the verifier's work at the header value `n'` — `codec.witnessBits n'`,
> `2 ^ n'` assignments, `thresholdPoly k n'` — while `ContentAccepts` reads its witness window and
> states its relation conjunct at `r := pr.2.n` (`ContentPrefixExtension.lean:152`). `M n' = M r`
> gives neither `n' = r` nor `codec.witnessBits n' = codec.witnessBits r` nor
> `thresholdPoly k n' = thresholdPoly k r`, so the `n'`-side growth chain transferred to none of the
> quantities that matter. Resolved: the work is now accounted at `r` throughout, with each component
> bounded **directly** by `M r = M n'` — `tableLen r ≤ M r` (`PrefixParserConvention.lean:48`),
> `codec.witnessBits r ≤ M r` (`TreeMCSPPrefixSemanticVerifier.lean:78`), hence
> `r ≤ bitLength (M n')` and `thresholdPoly k r = polylog N` — and never by transfer from `n'`
> (§1.0 step 5, §8 F0/F0b, §9). The growth chain is retained for what it does bound, `M n'` itself,
> so the larger timeout polynomial and its exponent `c · d` stand; revision 5's *second* exponent
> `c · e` is withdrawn, because it bounded `codec.witnessBits n'`, a quantity the verifier never
> reads. Outcome (a) remains sufficient, and no slice, budget or dependency changes.

> **Implementation note (revision 7).** FEAS-0 outcome (a) is now proved by
> `ContentTargetSizeBound.lean`, building on the merged `ContentParseFieldRecovery.lean`.
> The proof computes the all-blank decode at `r := pr.2.n`, forces `tableLen r ≤ N`, and closes
> `contentAccepts_target_poly_treePoly` through `PolyBoundedInTable.powAdd`.  Its sole
> header/parsed-target reconciliation is `M n_header = M r`; it uses no I1 result and never infers
> `n_header = r`.  Section 1.1 is therefore frozen.  This closes only target-size feasibility.
> GATE-0 now separately proves concrete non-vacuity; a concrete verifier TM, runtime proof and the
> `TM.accepts` bridge remain open.

---

## 1. The target

### 1.0 FEAS-0 — feasibility gate · **discharged by outcome (a)**

**The hole.** `ContentAccepts` reads its query window at the *content-computed* length
`treeMCSPPrefixM codec n'`, where `n'` is decoded from the word's own Elias-gamma header. Nothing
bounds `n'` polynomially in the physical length `N`. Concretely, on `main`:

* `contentHeader? z = decodeGamma? (padWord z (2 * N + 1)) tagLen`
  (`ContentPrefixExtension.lean:111`). `decodeGammaAux?` (`PrefixParserConvention.lean:87`) scans
  for the unary terminator, i.e. the first `true` bit at `tagLen + zeros`. Every cell at index
  `≥ N` reads blank (`padRead_ge`, `ContentPrefixExtension.lean:88`), so a successful decode forces
  the terminator *inside the support*: `tagLen + zeros < N`.
* The decoded value is `n' + 1 = 2 ^ zeros + payload` with `payload < 2 ^ zeros`. Hence `n'` may be
  as large as `2 ^ (N - tagLen - 1) - 1` — **exponential in `N`** (`tagLen = 8`,
  `PrefixParserConvention.lean:13`).
* `contentInput?` then runs the strict parser on `padWord z (treeMCSPPrefixM codec n')`, and
  `treeMCSPPrefixM codec n' ≥ tableLen n' = 2 ^ n'` (`tableLen_le_treeMCSPPrefixM`,
  `PrefixParserConvention.lean:48`) — **doubly exponential in `N`**. The relation conjunct of
  `ContentAccepts` is `codec.verifies r x w` at **`r := pr.2.n`**, the target the *narrow* parser
  returns — **not** at the header value `n'`. (Corrected in revision 5: revision 4 fixed this in the
  route below but left `codec.verifies n' x w` here. The two targets are reconciled by
  `M n' = M r`, Step 0, never by injectivity.) Its `ComputesTruthTable` component
  (`TruthTableMCSP.lean:35`) quantifies over all `2 ^ r` inputs, and the parse itself runs on a
  window of physical width `M n' = M r`.

Such words are not hypothetical, and they *parse*. Take `zeros := N - tagLen - 1`, a single `1` at
index `N - 1`, the tag field set to `treePrefixTag` (`PrefixParserConvention.lean:10`), everything
else `false`. Then `payload = 0` (blank), so `n' + 1 = 2 ^ zeros` and `consumed = 2 * zeros + 1`,
which is *exactly* `gammaLen n'` (§4.3). The strict parser's length gate compares
`treeMCSPPrefixM codec n'` with itself and passes; every field slice fits by the Layout offset
lemmas (§4.3); `x` is the all-false table, `i = 0`, `p` empty, `pad` all-zero, so `prefixAgrees` is
vacuous and `padZero = true`. For *this* word the narrow re-decode returns the same header value, so
`r = n'`, and acceptance reduces to the single question
`codec.verifies r (all-false table) (all-zero witness block)` — and *whatever the answer*, a
polynomial-time verifier must decide it in `poly(N)` steps without reading a `2 ^ r`-cell window.

**Why this blocked the freeze, not just the D-track.** The length gate that the CT route removed was
doing feasibility work: on the length-gated target, `N = treeMCSPPrefixM codec n` pins
`n = O(log N)` by construction, so the verifier's work is polynomial in its input. `ContentAccepts`
drops that gate and replaces it with nothing. While FEAS-0 was unsettled it was not known whether
`L' ∈ NP` was achievable at all by this route, so the target stayed provisional. It stayed
provisional until `contentAccepts_target_poly_treePoly` discharged outcome (a); §1.1 now records the
frozen target.

**What the concrete codec actually does with that word — computed, not left open.** The previous
revision left the decisive decode "open"; it is not. Chase the concrete decoder on the all-blank
witness block `w = fun _ => false`:

* `(treeCircuitWitnessCodec threshold).decode n' w
   = ((treeSelfDelimitingCode threshold).dec n' (List.ofFn w)).map Prod.fst`
  (`SelfDelimitingCircuitCode.toCodec`, `ConcreteCodecGap.lean:125`, `decode` field at `:130`), and
  `.dec n' = decodeCircuitFull n' (bitLength n')` (`ConcreteTreeCodec.lean:56`) `= decodeCircuit n'
  (bitLength n') bits.length bits` (`CircuitDecodeDepthFree.lean:62`), i.e.
  `decodeCircuitTreeAtDepth` through `fromTree` (`CircuitTreeBridge.lean:96`).
* On an all-`false` list, `decodeCircuitTreeAtDepth` (`Encoding.lean:182`) takes the
  **input-gate** branch `false :: false :: false :: rest` (`:188`); `Circuit.const` requires the
  prefix `001b` (`:199`, encoder at `:125`), so `const` is *not* reachable from blanks.
* The branch's guard `rest.length < width` does not fire: `width = bitLength n'` and
  `codec.witnessBits n' = (bitLength n' + 4) * thresholdPoly k n' ≥ bitLength n' + 4`
  (`ConcreteTreeCodec.lean:54`, `thresholdPoly k n' ≥ 1`). `decodeFin (bitLength n')` on the blank
  payload returns `some ⟨0⟩` (`Encoding.lean:33`), and the index test `i_fin.val < n'` (`:196`)
  then splits:
  * `n' = 0` → `none`, so `codec.verifies 0 x w` is **false** (it needs a decoded `c`);
  * `n' ≥ 1` → `some (Circuit.input ⟨0, _⟩)`, of size `1` (`Model_PartialMCSP.lean:51`) — **not**
    `Circuit.const false`.

So the flagship word above **is rejected** at the concrete codec: `ComputesTruthTable
treeCircuitClass (Circuit.input ⟨0, _⟩) x` demands that `x` be the truth table of the projection
`x ↦ x 0`, and that word's `x` is all-false. The generic worry does not instantiate here, and (a) is
therefore *expected to hold* at the concrete codec.

**The route to (a), in full — and note the target it runs on is `pr.2.n`, not `n'`.** This is the
correction that makes the route actionable. `ContentAccepts` (`ContentPrefixExtension.lean:152`)
reads its witness window, its truth table and its relation conjunct at **`pr.2.n`** — the `n` field
of the `PrefixInput` the *narrow* parser returned — and only the header decode mentions `n'`
(`= pr.1`). Revision 3 wrote the entire route in terms of `n'`; every step below that touches the
tape is therefore at `r := pr.2.n`, and the two are reconciled by the length gate, not by
injectivity.

Fix notation: `codec := treeCircuitWitnessCodec (thresholdPoly k)`,
`M := treeMCSPPrefixM codec`, let `z : PrefixBitVec N` be accepted with
`contentHeader? z = some (n', consumed)` and `contentInput? codec z = some pr`, and set
`r := pr.2.n`.

*Step 0 — `M n' = M r`, with no injectivity.* `contentInput?` (`:123`) runs
`parseTreeMCSPPrefixInput` on `padWord z (M n')`, a vector of physical length `M n'`, so
`parseTreeMCSPPrefixInput_length_convention` (`PrefixParserConvention.lean:1231`) gives

```text
M n' = M r .
```

This is the whole reconciliation, and it is already on `main`. **Do not** reach for
`treeMCSPPrefixM_injective_treePoly` to get `n' = r`: that is an I1 output (§4.3.1) and using it
here would invert §4.6's ordering. FEAS-0 never needs `n' = r`, because (a)'s conclusion bounds
`M n'`, and `M n' = M r` converts any bound on `M r` into one on `M n'`.

*Step 1 — case split.* Either `M n' ≤ N`, and (a)'s bound is immediate with `c = 1`; or `M n' > N`.

*Step 2 — the wide case has a blank witness window.* By Step 0, `contentWitness codec z r` reads at
`M r + j = M n' + j > N` (`ContentPrefixExtension.lean:135`), so every cell is blank
(`padRead_ge`, `:88`) and the witness block is `fun _ => false`.

*Step 3 — the decode, at `r`.* The relation conjunct is `codec.verifies r pr.2.x (blank)`
(`treeMCSPSearchProblem.relation = encoding.verifies`, `SearchMCSPConcreteTargets.lean:121`), and
`codec.verifies` (`:61`) demands `codec.decode r (blank) = some c` with `Circuit.size c ≤
thresholdPoly k r` and `ComputesTruthTable treeCircuitClass c pr.2.x`. By the computation above,
applied **at `r`**: `r = 0` gives `none` and kills acceptance, so `r ≥ 1`, and then
`c = Circuit.input ⟨0, _⟩`.

*Step 4 — recover the truth-table slice (new lemma, see below).* `ComputesTruthTable` at the
all-true assignment forces one cell of `pr.2.x` to be `true`: `bitVecToNat (fun _ => true) = 2 ^ r - 1`
(`Model_PartialMCSP.lean:74`) and `truthTableFunction` indexes the table at that value (`:303`), so
`pr.2.x ⟨2 ^ r - 1, _⟩ = true`. To turn that into a statement about `z` we need the parser's
`x`-slice, which **is not available on `main`** — see the scheduled lemma below. With it,
`pr.2.x j = padRead z (tagLen + cg + j)` for the narrow-window gamma width `cg`, so
`padRead z (tagLen + cg + 2 ^ r - 1) = true`, and `lt_of_padRead_eq_true`
(`ContentPrefixExtensionPadding.lean:127`) gives

```text
tagLen + cg + 2 ^ r - 1 < N ,   hence   tableLen r = 2 ^ r ≤ N   and   r ≤ bitLength N .
```

Note the bound is on `r`. Nothing here bounds `n'` — and nothing needs to: `n'` may be astronomical
as a *value* while `M n'` is small, because `M` is not injective.

*Step 5 — arithmetic.* `M n' = M r = tagLen + gammaLen r + tableLen r + idxWidth codec.witnessBits r
+ codec.witnessBits r`. Under `2 ^ r ≤ N`, i.e. `r ≤ bitLength N`: `tagLen = 8`,
`tableLen r ≤ N`, `gammaLen r = 2 · bitLength (r+1) − 1 = O(log log N)`,
`codec.witnessBits r = (bitLength r + 4) · (r ^ k + k) = O(log log N · (log N) ^ k)`, and
`idxWidth codec.witnessBits r = bitLength (codec.witnessBits r)` is smaller still. So

```text
M n' ≤ N + polylog N ≤ N ^ c + c   for a small c depending only on k.
```

**The scheduled sublemmas.** Two are arithmetic — `bitVecToNat (fun _ => true) = 2 ^ n - 1` and the
polylog bound on `(bitLength r + 4) * (r ^ k + k)` under `2 ^ r ≤ N`. The third is the slice
recovery, and it is the one revision 3 silently assumed. `parseTreeMCSPPrefixInput_inversion`
(`ContentPrefixExtensionCoincidence.lean:140`) returns **exactly** `m = treeMCSPPrefixM codec
input.n` and `∃ consumed, decodeGamma? y tagLen = some (input.n, consumed)` — it does **not** expose
`input.x`. FEAS-0 must therefore prove:

```lean
/-- **Truth-table slice recovery.**  The parser's success cascade pins `input.x` to the canonical
`x`-slice of the ambient word.  `consumed` is the *narrow-window* gamma width, carried
**symbolically**: FEAS-0 never needs `consumed = gammaLen input.n`, so this does not depend on
I1's §4.3.2, and no range side condition is needed because a successful parse already produced the
slice. -/
theorem parseTreeMCSPPrefixInput_x_slice
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (h : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ∃ consumed : Nat,
      decodeGamma? y tagLen = some (input.n, consumed)
        ∧ sliceBits? y (tagLen + consumed)
            (Pnp3.Models.Partial.tableLen input.n) = some input.x

/-- Content-side pointwise form: the parsed truth table is a blank-padded read of `z` itself. -/
theorem contentInput?_x_apply
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {N : Nat}
    (z : PrefixBitVec N)
    {pr : Σ r : Nat, PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec z = some pr) :
    ∃ cg : Nat, ∀ j : Fin (Pnp3.Models.Partial.tableLen pr.2.n),
      pr.2.x j = padRead z (tagLen + cg + j.1)
```

The types line up without `HEq`: `instanceBits := fun n => tableLen n`
(`SearchMCSPConcreteTargets.lean:118`) and `TruthTable n = Core.BitVec (tableLen n)`
(`TruthTableMCSP.lean:11`), so `input.x : PrefixBitVec (tableLen input.n)` is already a
`TruthTable input.n`. The proof of the first is the same eleven-way cascade
`parseTreeMCSPPrefixInput_inversion` already walks (`Coincidence.lean:140`–), reading off the `x`
branch instead of discarding it; the second composes it with `padWord_apply`
(`ContentPrefixExtension.lean:92`).

**Every FEAS-0 statement is at the concrete codec.** For an arbitrary
`codec : TreeCircuitWitnessCodec threshold` outcome (a) — and hence (b) — is **false**, so a
generic signature would schedule an unprovable theorem, exactly the defect §4.3.1 rejects for
injectivity. Witness: shift the concrete codec by one marker bit — `witnessBits' n := witnessBits n
+ 1`, `encode'` writes `true` at cell `0` followed by `encode n c`, and `decode'` runs
`codec.decode` on cells `1 …` when cell `0` is `true` but returns `some (Circuit.const false)` when
it is `false`. `decode_encode` still holds (every encoding sets the marker, and it is the only
field constraining `decode`), the all-blank witness now decodes to `Circuit.const false` of size
`1 ≤ thresholdPoly k n'` (`Model_PartialMCSP.lean:53`), `ComputesTruthTable` against the all-false
table holds, and the word above is accepted with `treeMCSPPrefixM codec' n'` doubly exponential in
`N`. So: **no codec-generic FEAS statement.** A later slice wanting one must carry an explicit
premise about `decode` of the all-blank witness.

**FEAS-0 must produce one of four outcomes, all stated at
`treeCircuitWitnessCodec (thresholdPoly k)`.**

*(a) Polynomial size bound — the expected route (see above).* An unconditional bound from accepted
complete words to the decoded convention length:

```lean
theorem contentAccepts_target_poly_treePoly (k : Nat) :
    ∃ c : Nat, ∀ (N : Nat) (z : PrefixBitVec N) (n' consumed : Nat),
      contentHeader? z = some (n', consumed) →
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z →
      treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n' ≤ N ^ c + c
```

*(b) Polynomial fast-rejection equivalent — (a) plus the check that computes it.* A `Bool`
predicate `contentBudgetOK` on the word, computable in `poly(N)` *without materialising the wide
window*, such that

```lean
theorem contentBudgetOK_eq_false_rejects (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    contentBudgetOK k z = false →
      ¬ ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z

theorem contentBudgetOK_bounds_target (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat} (hheader : contentHeader? z = some (n', consumed))
    (hok : contentBudgetOK k z = true) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n'
      ≤ <an explicit polynomial in N>
```

i.e. every word whose decoded target is super-polynomial is rejected by a check that never reads the
big window. `contentBudgetOK` may inspect the header (`O(N)` cells) and the *support* of `z`, but
must not slice at offsets beyond `poly(N)`.

**(b) implies (a) — they are not alternatives, and (b) is not a fallback.** Contraposing the first
theorem, an accepted word has `contentBudgetOK … = true`; the second then bounds its decoded target.
So a proof of (b) *is* a proof of (a) with a different exponent, and a refutation of (a) refutes (b)
as well. Read the pair as "the bound, plus the check that computes it". Do **not** schedule (b) as
the escape hatch for a failed (a); the escape hatch is (c).

**What refuting (a) actually requires — a family, not a word.** Corrected in this revision.
Revision 3 said a refutation of (a) is "a single accepted word with super-polynomial decoded
target". That is not the negation. (a) is `∃ c, ∀ N z n' …`, so

```text
¬(a)  =  ∀ c : Nat, ∃ (N : Nat) (z : PrefixBitVec N) (n' consumed : Nat),
           contentHeader? z = some (n', consumed) ∧ ContentAccepts codec z
             ∧ treeMCSPPrefixM codec n' > N ^ c + c .
```

One accepted word with a wide decoded target refutes (a) *at a particular `c`* only, and there is
always a larger `c` that absorbs any finite set of words. Routing to (c) therefore requires
exhibiting an accepted family whose decoded target outruns **every** polynomial — which, by Steps
2–5 above, would mean exhibiting accepted words with an all-blank witness window whose decoded
circuit is not `Circuit.input ⟨0, _⟩`. At this codec that is what the decode computation rules out.

**Is (a) alone enough for a verifier? Yes — via a bounded timeout.** Revision 3 declared (a) green
while simultaneously saying "a verifier needs a computable rejection rule, not merely the existence
of a bound", which left the reader unable to tell whether (b) was mandatory. It is not. Given (a)
with exponent `c`, a verifier machine can:

1. decode the header from at most `N` cells — `contentHeader?` terminates inside the support, so this
   is `O(N)` work and yields `n'` as a binary numeral of at most `N` bits;
2. test `2 ^ n' ≤ N ^ c + c` **without materialising `2 ^ n'`**, by comparing `n'` against
   `bitLength (N ^ c + c) = O(log N)`. The numeral `n'` has `O(N)` bits, so this comparison is
   `poly(N)`;
3. if the test fails, `M n' ≥ tableLen n' = 2 ^ n' > N ^ c + c`, so by (a)'s contrapositive the word
   is **not** accepted — reject, having read only `poly(N)` cells;
4. otherwise `2 ^ n' ≤ N ^ c + c` — and *that*, not `M n' ≤ N ^ c + c`, is what the machine has in
   hand. **Corrected in revision 5:** revision 4 inferred the second from the first, which does not
   follow. (a) bounds `M n'`, but the only test the machine can run cheaply is on
   `tableLen n' = 2 ^ n'`, and `M n'` additionally carries `gammaLen n'`,
   `idxWidth codec.witnessBits n'` and `codec.witnessBits n'`
   (`treeMCSPPrefixM`, `PrefixParserConvention.lean:40`), so the same exponent cannot be reused.
   Derive the larger timeout polynomial from the growth chain already on `main`:
   `polyBoundedInTable_thresholdPoly k` (`ThresholdGrowth.lean:53`) →
   `polyBoundedInTable_treeWitnessBits_of_thresholdPoly` (`ConcreteTreeCodec.lean:78`) →
   `polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly` (`WitnessGrowthReduction.lean:94`) →
   `PolyBoundedInTable.powAdd` (`ExtractedScheduleGrowth.lean:114`, which converts a
   `(tableLen n + 1) ^ k` bound to the `tableLen n ^ d + d` shape). That yields an exponent `d`
   with, for every `n'`,

   ```text
   M n' ≤ (2 ^ n') ^ d + d ,
   ```

   so under the test `2 ^ n' ≤ N ^ c + c` the parse window collapses to a polynomial in `N`:

   ```text
   M n' ≤ (N ^ c + c) ^ d + d  =:  P N .
   ```

   This is a bound on the **header** target `M n'` and on nothing else at `n'`; step 5 says why that
   is enough, and why the quantities at `n'` other than `M n'` are irrelevant;
5. **the work is at `r := pr.2.n`, and every component of it is bounded *directly* by `M n'`.**
   Corrected in revision 6: revisions 4 and 5 accounted the verifier's work at `n'` —
   `codec.witnessBits n'`, `2 ^ n'` assignments, `thresholdPoly k n'` — but `ContentAccepts`
   (`ContentPrefixExtension.lean:152`) reads `contentWitness codec z pr.2.n` and states its relation
   conjunct at `pr.2.n`, so the working quantities are `tableLen r`, `codec.witnessBits r` and
   `thresholdPoly k r`. `M n' = M r` (Step 0) does **not** give `n' = r`, and therefore gives
   neither `codec.witnessBits n' = codec.witnessBits r` nor
   `thresholdPoly k n' = thresholdPoly k r`; the `n'`-side chain of step 4 transfers to none of them.
   Do not attempt the transfer — bound each component at `r` outright, using `M n' = M r` only to
   land the bound back on `P N`:

   ```text
   tableLen r = 2 ^ r    ≤ M r = M n' ≤ P N      (tableLen_le_treeMCSPPrefixM, `PrefixParserConvention.lean:48`)
   codec.witnessBits r   ≤ M r = M n' ≤ P N      (witnessBits_le_treeMCSPPrefixM, `TreeMCSPPrefixSemanticVerifier.lean:78`)
   r ≤ bitLength (M n')  = O(log (P N)) = O(log N)                     (from 2 ^ r ≤ M n')
   thresholdPoly k r = r ^ k + k ≤ (bitLength (M n')) ^ k + k = polylog N
   ```

   Both component lemmas are already on `main`, both are stated at *every* argument (so applying them
   at `r` needs nothing about `n'`), and each is a summand-of-`treeMCSPPrefixM` fact
   (`treeMCSPPrefixM`, `PrefixParserConvention.lean:40`), which is exactly why no growth chain and no
   second exponent is needed for them;
6. every cell the verifier touches is then `poly(N)`, **including the certificate and witness
   windows** that revision 4's step 4 omitted: the strict parse spans `M n' ≤ P N` cells,
   `contentWitness` spans `[M r, M r + codec.witnessBits r) = [M n', M n' + codec.witnessBits r)`
   (`ContentPrefixExtension.lean:135`), which by step 5 lies inside the first `2 · M n' ≤ 2 · P N`
   cells, and the certificate block of the complete word occupies `certificateLength · 1` cells
   (`= · + 1`, `pnp3/Complexity/Interfaces.lean:521`) — at most

   ```text
   2 · ((N ^ c + c) ^ d + d) + N + 1
   ```

   cells in total. The `ComputesTruthTable` check then runs over `2 ^ r ≤ M n' ≤ P N` assignments —
   *not* `2 ^ n'` — of a circuit of size `≤ thresholdPoly k r = polylog N`, also `poly(N)`.

So (a)'s exponent **yields** a timeout but **is not** the timeout: the timeout polynomial has
exponent `c · d`, with `d` from `powAdd` above, and that single polynomial `P N` covers the parse
window, the witness window and the truth-table work, because step 5 bounds each `r`-side component by
`M n'` directly. Revision 4's "(a)'s exponent *is* the timeout" was the invalid same-polynomial
inference; revision 5's *second* exponent `c · e` is withdrawn in revision 6 — it bounded
`codec.witnessBits n'`, which the verifier never uses, and the quantity it does use,
`codec.witnessBits r`, is bounded by `M r = M n'` outright. Outcome (a) remains sufficient after both
corrections. (b) is that (larger) timeout packaged
as a `Bool` predicate with its own correctness lemma. **Honest caveat:** steps 1–6 are a
machine-construction argument, not
a formalized theorem — they are discharged in the deferred machine slices (§4.7), not in FEAS-0.
FEAS-0 green at (a) therefore means "the route is not blocked and the timeout exists in principle",
not "a poly-time verifier has been built". Prefer (b) when it is no harder, because the D-track needs
the `Bool` rule anyway and (b) hands it over already proved.

*(c) Polynomial-time wide-target decision procedure.* If (a) is refuted — i.e. the family displayed
below exists, so that accepted words outrun *every* polynomial bound — the route is still not dead,
and this is the outcome (b) cannot express. A word with `treeMCSPPrefixM codec n' > N` has an all-blank witness window and
an all-blank tail of its truth-table field, so its acceptance depends only on the header, the
support of `z`, and a *fixed* decode fact — potentially a closed-form rule decidable in `poly(N)`
even though the nominal window is astronomically wide. What must be produced is then a decision
procedure rather than a bound:

```lean
def contentDecide (k : Nat) {N : Nat} (z : PrefixBitVec N) : Bool

theorem contentDecide_eq_true_iff (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    contentDecide k z = true ↔ ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z
```

with `contentDecide` reading only `poly(N)` cells — never slicing at an offset beyond `poly(N)` —
plus the runtime accounting that names the polynomial. Note (c) subsumes both (a) and (b) as a
verifier prerequisite but is strictly weaker as a *statement about targets*: it permits accepted
words with super-polynomial `treeMCSPPrefixM codec n'`.

*(d) Target repair.* If none of (a), (b), (c) goes through, `ContentAccepts` is the wrong predicate
and the freeze is void. The repair direction is a **budgeted** content predicate — a content-side
gate that is polynomial rather than absent, e.g. requiring
`tagLen + gammaLen n' + tableLen n' ≤ N` (which recovers `n' = O(log N)` without re-introducing the
exact equality `N = treeMCSPPrefixM codec n`). That is a new §1.1 and a new plan revision, not a
slice.

**Budget — raised in this revision:** 350–600 LOC · 2 modules. Revision 3 budgeted 250–450 LOC · 1–2
modules for "the case split on `M n' ≤ N`, the blank-witness decode, the all-true assignment, and the
arithmetic", which omitted the slice-recovery lemma it assumed was available. Split:

* `ContentParseFieldRecovery.lean` — `parseTreeMCSPPrefixInput_x_slice` and
  `contentInput?_x_apply` (100–200 LOC; the eleven-way cascade of `Coincidence.lean:140` re-walked
  to keep the `x` branch);
* `ContentTargetSizeBound.lean` — Steps 0–5 and the two arithmetic sublemmas (250–400 LOC).

**Exit (FEAS-0 green):** (a), (b) or (c) proved at the concrete codec, `#check`/`#print axioms`
lines added, and this file's §1.1/§1.2 promoted from *provisional* to *frozen* in the same PR.
**Stop/go (F0):** only outcome (d) is red. If the outcome is (d), **halt GATE-0, P0, I1, D1a and
D1b**, revise §1.1, and do not open any slice against `ContentAccepts` until the repaired predicate
is frozen. A failure of (a) alone is *not* outcome (d) — it routes to (c), and it also kills (b), so
do not re-open (b) after (a) falls; and remember that "failure of (a)" means the `∀ c, ∃ …` family
above, not one wide word. FEAS-0 was the only item in §4 permitted to start during the now-closed
provisional phase.
**Stop/go (F0b) — no I1 dependency.** No FEAS-0 declaration may cite
`treeMCSPPrefixM_injective_treePoly`, `treeMCSPPrefixM_injective_of_monotone` or
`decodeGamma?_consumed_eq_gammaLen` (all §4.3, all I1 outputs). Step 0 uses
`parseTreeMCSPPrefixInput_length_convention` (`PrefixParserConvention.lean:1231`) and the slice
lemma carries `consumed` symbolically, so the route is I1-free by construction. A slice that needs
`n' = pr.2.n` or `consumed = gammaLen pr.2.n` has inverted §4.6's ordering — reject it and re-derive
via Step 0.

### 1.1 The frozen target

Input (2) of the conditional chain — the NP-membership obligation — is **frozen** at the
content-truthful route. FEAS-0 outcome (a) removes the target-size blocker; the interface remains
an explicit, unproved machine obligation:

```text
target interface : ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))
target predicate : ContentAccepts    codec (z : PrefixBitVec N)
target language  : ContentPrefixExtensionLanguage codec                                  (`L'`)
```

Exact declarations, all in `pnp4/Pnp4/Frontier/ContractExpansion/ContentPrefixExtension.lean`:

| Declaration | Line | Shape |
|---|---|---|
| `padRead` / `padWord` | `:77` / `:81` | blank-padded read of a finite bitstring |
| `padRead_lt` / `padRead_ge` | `:84` / `:88` | in-support read / blank tail |
| `contentHeader?` | `:111` | `decodeGamma? (padWord z (2 * N + 1)) tagLen` |
| `contentInput?` | `:123` | strict parser re-run on `padWord z (treeMCSPPrefixM codec n')` |
| `contentWitness` | `:135` | `codec.witnessBits n` cells at `treeMCSPPrefixM codec n` |
| **`ContentAccepts`** | **`:152`** | `∃ pr, contentInput? codec z = some pr ∧ pr.2.prefixAgrees … ∧ relation …` |
| `ContentPrefixExtendable` | `:165` | `∃ w, ContentAccepts codec (concatBitstring y w)` |
| `ContentPrefixExtensionLanguage` | `:172` | classical `Bool` wrapper of the above |
| `ContentPrefixExtensionLanguage_accepts_iff` | `:178` | wrapper unwrapping |
| **`ContentPrefixExtensionNPWitness`** | **`:211`** | `M`, `c`, `runTime_poly`, `correct` |
| `contentPrefixExtensionLanguage_in_NP_of_witness` | `:231` | witness ⇒ `NP L'` |

Downstream consumers already exist and are unconditional given the interface:
`ContentConsolidatedSource.lean:57` `verifiedSourceCT_of_noPolynomialBoundedSearchSolver`,
`:73` `verifiedSourceCT_treePoly`, `:86` `NP_not_subset_PpolyDAG_treePolyCT`. At the concrete
threshold those take exactly two explicit hypotheses: `NoPolynomialBoundedSearchSolver`
(input (1), untouched by this plan) and `ContentPrefixExtensionNPWitness` (input (2), the target).

Note the certificate exponent is **fixed to `k = 1`** by the interface: `ContentPrefixExtensionNPWitness`
has no `k` field (`contentPrefixExtensionLanguage_in_NP_of_witness` supplies the literal `1`), and
`certificateLength n 1 = n + 1` (`pnp3/Complexity/Interfaces.lean:521`). The length-gated
`PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean:75`) does carry a `k`. Any slice that
needs a different certificate exponent is out of scope by construction.

### 1.2 Status of the length-gated target: retained for audit compatibility, not preferred for new slices

`PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean:75`) and its chain
(`ExplicitConditionalSource.lean`, `ConcreteTreeCodecSource.lean`,
`ConsolidatedTreeSeparation.lean`) are **retained as compiled and audited compatibility
surfaces**, and are **not retired**. FEAS-0 outcome (a) removed a *blocker* on the content route; it
did not establish that the content route is superior, so the length-gated target is **not preferred**
for new slices rather than rejected. Concretely:

* **New slices should state their headline against `ContentAccepts` / `L'`** and are scheduled in §4.
  A new slice whose only target is `PrefixExtensionLanguage` / `PrefixExtensionNPWitness` is **not**
  rejected on target grounds alone: it is dispreferred, and is admissible once it records an explicit
  rationale for choosing the length-gated route (compatibility or audit maintenance always qualifies,
  as does a stated technical obstruction on the `L'` side). Reject only a slice that offers no such
  rationale.
* **Audit compatibility is preserved regardless.** The length-gated modules keep compiling, keep
  their `#check` lines in `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` and their
  `#print axioms` lines in `pnp4/Pnp4/Tests/AxiomsAudit.lean`, and keep being cited by
  `AGENTS.md`'s "most concrete live form" paragraph. Removing or weakening them is **not** part of
  this plan under any FEAS-0 outcome.
* **Bridging lemmas are admissible in both directions** when they serve either route, e.g. the
  coincidence family `ContentPrefixExtensionCoincidence.lean:276`
  `ContentPrefixExtendable_iff_of_parse` / `:324` `ContentPrefixExtensionLanguage_eq_of_parse`.
  Under FEAS-0 outcome (d) the old → new direction is the one that survives.
* One CT-A artifact is **mis-targeted relative to the CT route** (slice P0): the semantic core
  `TreeMCSPPrefixSemanticVerifier.lean:252` `treePrefixSemanticAccepts_correct` is stated for
  `PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)`, not for `L'`. P0 adds
  an `L'`-side counterpart; it does not remove or re-point the existing theorem.

### 1.3 What the freeze does **not** buy — target-validity caveats

These must be restated in every slice's module docstring as applicable; they are the honest
boundary of the frozen target.

1. **The `(★′)` bridge is the whole remaining machine obligation.** No verifier TM, no runtime
   bound, and no `TM.accepts … = ContentAccepts …` statement exists for `L'` anywhere in the
   repository.
2. **Padding invariance is proved for the predicate, not the language.**
   `ContentPrefixExtensionPadding.lean:314` `ContentAccepts_padWord_of_le` and `:333`
   `ContentAccepts_iff_of_padRead_eq` are about *complete* words. Membership in `L'` at physical
   length `m` quantifies over `Bitstring (certificateLength m 1)` concatenated at offset `m`, both
   of which move with `m`; wrapper-level invariance is unproved.
3. **The re-decode gate's vacuity is open only in its *value* tests, not its gamma decode.**
   Corrected in this revision: `consumed = gammaLen n'` is a **theorem**, not a hypothesis — a
   successful `decodeGammaAux?` returns `consumed = 2 * zeros + 1` with
   `n' + 1 = 2 ^ zeros + payload` and `payload < 2 ^ zeros`, so `bitLength (n' + 1) = zeros + 1`
   and `gammaLen n' = 2 * zeros + 1` (§4.3). Consequently the strict parser's
   `m = treeMCSPPrefixM codec n_dec` gate *is* unconditionally vacuous given a successful header
   decode, and every range/fit premise of the narrow-window parse discharges from the Layout offset
   lemmas. What remains open is exactly three **value** tests inside
   `parseTreeMCSPPrefixInput` (`PrefixParserConvention.lean:1130`): `tag = treePrefixTag`,
   `i ≤ codec.witnessBits n'`, and `padZero = true`. Those are sound rejections, not defects.
   (The previous revision asserted the opposite — that unconditional gate vacuity is false and
   canonicity must be assumed. Both statements were wrong.)
4. **Non-vacuity is proved at the concrete codec.** `ContentPrefixExtensionNonVacuity.lean`
   constructs accepted zero-prefix words generically from a satisfied predicate and discharges the
   concrete case with the all-false table and `Circuit.const false`; in particular
   `contentAccepts_nonvacuous_treePoly` gives an accepted complete word for every `k, n`.  This is
   GATE-0's specification-side result, not a verifier TM or NP-witness construction.
5. **The obligation lives in this repository's machine model only.** `NP` is `NP_TM`
   (`pnp3/Complexity/Interfaces.lean:560`) over `Pnp3.Internal.PsubsetPpoly.TM`: deterministic
   single-tape, binary alphabet, no read-only input tape, tape length `n + runTime n + 1`
   (`TuringEncoding.lean:73`), `runTime : ℕ → ℕ` an unrestricted **structure field** (`:60`), and
   `TM.accepts` evaluated **at exactly step `runTime n`** (`:178`, `:183`) with no halting
   predicate. No cross-model runtime-robustness theorem is formalized.
6. **The unrestricted `runTime` field is a live model audit finding, and avoiding it is
   *unenforced*.** `pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean:77`
   `lengthAdviceLanguage_in_repo_P` proves that *every* `A : Nat → Bool`, with no computability
   hypothesis, yields a length-only language in this repository's `P`, via `lengthAdviceTM` (`:44`)
   whose zero-or-one-step runtime stores `A n`. Consequence for this plan: discharging
   `ContentPrefixExtensionNPWitness` establishes NP-membership *in a model whose `P` admits
   arbitrary length advice*. Corrected in this revision: **nothing in `ContentVerifierBridge`
   (§4.5) prevents a bridge instance from exploiting that channel.** `runTime_poly` bounds the
   clock's *magnitude*; it says nothing about how the clock is computed, so a machine whose
   `runTime` encodes advice can satisfy `accepts_eq` legitimately. G6 is therefore a **review
   convention, not a machine-checked gate**. Making it enforceable requires a formal clock
   premise — an added field constraining `M.runTime` to a named explicit arithmetic expression, or
   a repo-level amendment to `TM` making `runTime` uniform. Until such a premise is written down
   and cited here, do **not** describe the CT route as advice-free.
7. **Target-size feasibility is closed; machine feasibility is not (§1.0).**
   `contentAccepts_target_poly_treePoly` now bounds the header convention length of every accepted
   complete word by `N ^ c + c`. Its wide-case forcing is at **`r := pr.2.n`**, transported by
   `M n_header = M r`, never by injectivity. This supplies the bounded-timeout argument in
   principle, but no verifier TM, runtime accounting theorem, or `TM.accepts` bridge has been built.
   Therefore `L'` still may not be described as *proved* polynomial-time verifiable or in NP.

---

## 2. Re-audit of `verifier-next-slices.md` against current `main`

The donor manifest was written at `main = 5d8ee5f8`. At this slice-log revision `main` is
`014a7768`, **57 commits ahead** (`git rev-list --count 5d8ee5f8..014a7768 = 57`), and those commits
are precisely the work that changed
the retarget picture: `#1621` (AC0 audit), `#1622` (documentation-state audit), **`#1623` (CT-A)**,
**`#1624` (CT-B)**, **`#1625` (CT-C)**, **`#1626` (runtime advice)**, **`#1627` (retarget
plan)**, **`#1628` (field recovery)**, **`#1629` (FEAS target bound)** and **`#1630`
(concrete non-vacuity)**.

### 2.1 Stale assumptions — corrected

| Donor claim | Verdict | Correction |
|---|---|---|
| §0 "`main` = `5d8ee5f8`" | **stale** | `main = 014a7768`; `git rev-list --count pr1618..main = 57` (the merge base is still `5d8ee5f8`, so this equals `5d8ee5f8..main`). |
| §0 "`ContractExpansion/` has 39 files on main" | **stale** | 39 files on `5d8ee5f8`, **51** on `014a7768` (`git ls-tree -r --name-only`). |
| §0 / §9 "Nothing on `main` is reusable"; "every module named below as a donor exists **only** in the PR stack" | **false** | Twelve modules directly on the retarget path landed on `main` after the donor snapshot (§3.1) — eleven in `ContractExpansion/` plus `ModelAudit/RuntimeAdviceBarrier.lean`. Six of the eleven also exist, **divergently**, on `pr1618` (§3.2), so the PR stack is not a superset of `main`. |
| §0 "BASE for every slice: `4a8ee0c9`; do not branch from `main`" | **false for this plan** | Every slice in §4 is dependency-closed on `main = 014a7768` at this revision and branches from it (§5). Branching from `4a8ee0c9` would *lose* the CT, FEAS and GATE-0 prerequisites. |
| §0 "`git diff --stat main...pr1618` = 184 files / +56544 / −2420 — the whole stack" | **arithmetically unchanged, semantically misleading** | The number is identical today only because `...` resolves to the merge base, which is still `5d8ee5f8`. It therefore describes the stack against a 57-commit-old `main`, and hides the rebase surface in §3.2. |
| §4 GATE-0 = "embedding-route spike (A′ vs B) on `clearIterProgram`" | **not this plan's GATE-0** | It gates donor slices P1…P4 / D3 inside `pr1618`. It has no bearing on any slice targeting `ContentAccepts`. Superseded by FEAS-0 (§1.0) and GATE-0 (§4.1). |
| §4 track letters P / I / D = pop arm / input arm / driver | **repurposed** | Retargeted in §4 to P = predicate-side semantic core, I = invariance and gate closure, D = machine/clock interface. The donor tracks stay valid *inside* `pr1618` and are parked (§3.3). |
| §9 "The pop arm's machine is finished; only the run remains" | **true of `pr1618`, irrelevant to input (2)** | See §3.4: the donor machine is a transcoder, not a verifier. |

### 2.2 Donor findings re-verified as still accurate (on `pr1618`, not on `main`)

* `LoopLayout` (`TreeMCSPBinToUnaryLoopFullScanReachesSink.lean`) still carries the **global** blank
  clause `∀ q, (q : Nat) < (c.head : Nat) - u → c.tape q = false`. The donor's §3.2 blocker stands.
* `TreeMCSPDriverStepTape.lean` still has the degenerate `| _, _ => True` arm of `DriverStepFits`
  (line 139) alongside `| _, _ => tape` (line 89). The donor's §3.3 operand-underflow gap stands.
* `TreeMCSPPopIterRun.lean`, any `inputIter*`, `TreeMCSPDriverProgram.lean` and
  `TreeMCSPDriverRealizationInstance.lean` are all **absent** from `pr1618`, as the donor stated.
* Branch tips are unchanged: `pr1526 = b1f4f31d` (289 commits ahead of the common merge base
  `5d8ee5f8`), `pr1616 = 57ee057a` (335), `pr1618 = 4a8ee0c9` (364).

---

## 3. Module boundary: current `main` vs donor-only

### 3.1 On current `main` — the retarget's actual foundation (12 modules, all reusable)

Landed by `#1623` through `#1626` and `#1628` through `#1630`, all absent from the donor's base of record
(`git ls-tree -r --name-only 5d8ee5f8` lists none of them):

| Module | LOC | Key declarations for this plan |
|---|---|---|
| `ContentPrefixExtension.lean` | 239 | the frozen target, §1.1 |
| `ContentPrefixExtensionCoincidence.lean` | 341 | `readBit?_mono` `:47`, `readNatBE_mono` `:59`, `decodeGammaAux?_mono` `:82`, `decodeGamma?_concat_pad` `:115`, `parseTreeMCSPPrefixInput_inversion` `:140`, `padWord_concat_left` `:207`, `contentWitness_concat` `:218`, `contentInput?_concat_of_parse` `:244`, `ContentPrefixExtendable_iff_of_parse` `:276`, `ContentPrefixExtensionLanguage_eq_of_parse` `:324` |
| `ContentPrefixExtensionPadding.lean` | 358 | `padRead_padWord_of_le` `:103`, `padWord_padWord_of_le` `:111`, `eq_padWord_of_padRead_eq` `:120`, `lt_of_padRead_eq_true` `:127`, `readBit?_padWord_of_lt/_of_ge` `:136`/`:143`, `readNatBE_padWord_transfer` `:151`, `decodeGammaAux?_padWord_support` `:186`, `decodeGammaAux?_padWord_canonical` `:223`, `contentHeader?_padWord_of_le` `:278`, `contentInput?_padWord_of_le` `:293`, `contentWitness_padWord_of_le` `:300`, `ContentAccepts_padWord_of_le` `:314`, `ContentAccepts_iff_of_padRead_eq` `:333`, `contentHeader?_of_decodeGamma` `:349` |
| `ContentPrefixExtensionPaddingTransport.lean` | 63 | `ContentAccepts_padWord_of_prefixExtendable` `:39` (the classical conditional existential) |
| `ContentPrefixExtensionTransfer.lean` | 155 | `DecidesContentPrefixExtensionLanguage` `:51`, `correctNextBitDecider_of_decidesContentLanguage` `:62`, `boundedSearchSolver_of_deciderFamilyCT` `:92`, `boundedSearchSolver_of_PpolyDAG_contentPrefixExtension` `:111`, `not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver` `:132`, `_of_noPolynomialBoundedSearchSolver` `:145` |
| `ContentConsolidatedSource.lean` | 96 | the three consolidated CT sources, §1.1 |
| `TreeMCSPPrefixSemanticVerifier.lean` | 304 | `witnessBits_le_treeMCSPPrefixM` `:78`, `prefixAgreesBool` `:99` + `_eq_true_iff` `:105`, `instDecidableCodecVerifies` `:114` (local), `verifiesBool` `:121` + `_eq_true_iff` `:128`, `sliceBits?_zero` `:137`, `witnessBits_le_certificateLength` `:148`, `extractWitness?` `:160` + `extractWitness_eq` `:172`, `treePrefixSemanticAccepts` `:192`, `treePrefixSemanticAccepts_correct` `:252` (**mis-targeted, see §1.2**) |
| `ModelAudit/RuntimeAdviceBarrier.lean` | 88 | `lengthAdviceLanguage` `:37`, `lengthAdviceTM` `:44` (`runTime := if A n then 1 else 0`), `lengthAdviceTM_runTime_le_one` `:54`, `lengthAdviceTM_accepts` `:60`, `lengthAdviceLanguage_in_repo_P` `:77` — the caveat-6 source. **Provenance corrected in this revision:** this module landed with `#1626` (commit `f7244834`, "audit(pnp4): expose runtime advice barrier"); it is *not* part of the pre-existing foundation, and the previous revision listed it there. |
| `TreeMCSPPrefixVerifierLayout.lean` | 274 | `prefixVerifierInputLen` `:33`, `prefixVerifierCertStart` `:44`, `concatBitstring_left/_right` `:72`/`:80`, `verifierTape_left/_right` `:103`/`:114`, `queryXOffset` `:136`, `queryIdxOffset` `:139`, `queryPrefixOffset` `:143`, `queryPrefixOffset_add_witnessBits` `:148`, `queryPrefixOffset_le` `:157`, `queryXOffset_le_treeMCSPPrefixM` `:166`, `queryIdxOffset_le_treeMCSPPrefixM` `:174`, `gammaLen_le_treeMCSPPrefixM` `:183`, `instanceSize_lt_treeMCSPPrefixM` `:194`, `gammaZeros` `:219`, `gammaTermOffset` `:223`, `gammaLen_eq_two_mul_gammaZeros_add_one` `:226`, `gammaTermOffset_lt_queryXOffset` `:239`, `gammaTermOffset_le_treeMCSPPrefixM` `:246`, `gammaMirror_mem` `:258` |
| `ContentParseFieldRecovery.lean` | 156 | `parseTreeMCSPPrefixInput_x_slice` `:57`, `contentInput?_x_apply` `:124` — FEAS parser-field recovery from `#1628` |
| `ContentTargetSizeBound.lean` | 295 | concrete blank decode and support forcing, culminating in `contentAccepts_target_poly_treePoly` `:259` — FEAS outcome (a) from `#1629` |
| `ContentPrefixExtensionNonVacuity.lean` | 190 | `contentAccepts_zeroPrefixQuery_of_predicate` `:101`, `contentPrefixExtensionLanguage_zeroPrefixQuery` `:131`, `contentAccepts_nonvacuous_treePoly` `:177` — GATE-0 from `#1630` |

Plus the pre-existing foundation, unchanged since the donor snapshot and equally reusable:

* `PrefixParserConvention.lean` (1337 LOC) — `treePrefixTag` `:10`, `tagLen` `:13`, `bitLength`
  `:22`, `gammaLen` `:26`, `idxWidth` `:30`, `treeMCSPPrefixM` `:40`,
  `tableLen_le_treeMCSPPrefixM` `:48`, `readBit?` `:57`, `readNatBE` `:61`, `sliceBits?` `:70`,
  `allZeroSlice?` `:78`, `decodeGammaAux?` `:87`, `decodeGamma?` `:101`,
  `prefixLength_lt_two_pow_idxWidth` `:329`, `gammaLen_eq_zeros_add_bitLength` `:364`,
  `gammaLen_eq_two_mul_zeros_add_one` `:371`, `encodeTreeMCSPPrefixFields` `:631`,
  `encodeTreeMCSPPrefixFields_length_convention` `:659`,
  `CanonicalRawTreeMCSPPrefixFields.toPrefixInput` `:675`, `parseTreeMCSPPrefixInput` `:1130`,
  `parse_encodeTreeMCSPPrefixFields` `:1184`, `treeMCSPConcretePrefixParser` `:1203`,
  `parseTreeMCSPPrefixInput_length_convention` `:1231`.
* `PrefixExtensionLanguage.lean` — `PrefixBitVec` `:10`, `PrefixInput` `:31`,
  `PrefixInput.prefixAgrees` `:52`, `PrefixExtendableInput` `:100`, `PrefixExtendable` `:108`,
  `PrefixExtensionLanguage` `:124`, `PrefixExtensionLanguage_accepts_iff` `:131`.
* `PrefixExtensionLanguageNP.lean` — `TreeCircuitWitnessCodec.verifiesDecidable` `:92`. **P0 depends
  on this module** (via `verifiesBool`); it was missing from the previous revision's inventory, and
  its axiom footprint is what makes §4.2's G2 expectation nontrivial.
* `TreeMCSPPrefixSerializer.lean` — `zeroPrefixFields` `:42` (sets `i := 0` at `:49`),
  `zeroPrefixQueryValue` `:57`, `parse_zeroPrefixQueryValue` `:68`, `zeroPrefixQueryValue_parses`
  `:84`.
* `ConcreteTreeCodec.lean` — `treeSelfDelimitingCode` `:53` (`witnessBits n = (bitLength n + 4) * threshold n`,
  `:54`), `treeCircuitWitnessCodec` `:67`,
  `polyBoundedInTable_treeWitnessBits_of_thresholdPoly` `:78`.
* `ThresholdGrowth.lean` — `thresholdPoly` `:36` (`= n ^ k + k`).
* `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` — `TreeCircuitWitnessCodec` `:44`
  (`witnessBits : Nat → Nat` at `:46`, **unconstrained** — see §4.3), `.verifies` `:61`, `.sound`
  `:73`, `.complete` `:85`, `TreeMCSPSearchWitnessEncoding.ofCodec` `:98`, `treeMCSPSearchProblem`
  `:114`.
* `pnp4/Pnp4/AlgorithmsToLowerBounds/TruthTableMCSP.lean` — `TruthTable` `:11`, `treeCircuitClass`
  `:22`, `truthTableFunction` `:28`, `ComputesTruthTable` `:35`, `circuitComplexityLE` `:50`,
  `treeMCSPPredicate` `:87`.
* `pnp3/Models/Model_PartialMCSP.lean` — `Circuit` `:42`, `Circuit.size` `:51`
  (`Circuit.const _ => 1` at `:53`), `Circuit.eval` `:59`.
* `pnp3/Complexity/Interfaces.lean` — `certificateLength` `:521`, `concatBitstring` `:528`,
  `NP_TM` `:560`, `NP` `:580`.
* `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` — `TM` `:45`, `runTime` `:60`,
  `tapeLength` `:73`, `initialConfig` `:133`, `initial_tape_input` `:140`,
  `initial_tape_blank` `:146`, `run` `:178`, `accepts` `:183`.
(`RuntimeAdviceBarrier.lean` is **not** in this second list: it is `#1626` work and is now a row of
the table above.)

### 3.2 Donor-only (`pr1618 = 4a8ee0c9`) — and the overlap that is *not* clean

`ContractExpansion/` has **216** files on `pr1618` versus 51 on `main`; **183** of them are
`TreeMCSP*` modules (region-embedding toolkit, arm programs, arm runs, corridor invariants, driver
interface, transcoder capstone). **Inventory corrected in this revision:** the previous revision said
"none of these exist on `main`", which is false. `main` has **15** `TreeMCSP*` modules in this
directory, all 15 of them also on `pr1618`, so **168** of the 183 are donor-only. Of the 15 shared
ones, 13 are byte-identical on both branches and exactly **2** diverge —
`TreeMCSPPrefixSemanticVerifier.lean` and `TreeMCSPPrefixVerifierLayout.lean`, both rows of the table
below.

**Divergence inventory — corrected in this revision.** Revision 3 said "six modules in all exist on
both with different contents", which was wrong in both directions. The exact figures, all by blob
comparison at the two tips against the merge base `5d8ee5f8`:

* **Nine paths** in `ContractExpansion/` exist at *both* tips with **different contents** — eight
  `.lean` modules plus the directory `README.md`.
* Of those nine, **six `.lean` modules were added independently on both sides** (absent at the merge
  base, so there is *no common ancestor blob*): the four `Content*` modules below plus
  `TreeMCSPPrefixSemanticVerifier.lean` and `TreeMCSPPrefixVerifierLayout.lean`. These are the
  genuine conflict set — a rebase must merge two independent implementations, not replay a diff.
* The remaining three — **`ConsolidatedTreeSeparation.lean`**, **`PrefixExtensionNPWitness.lean`**
  and **`README.md`** — differ only because `main` moved; `pr1618` still carries the merge-base
  blob, so a rebase takes `main`'s version cleanly. Revision 3 omitted all three. Note the first two
  are exactly the length-gated chain modules §1.2 retains and `AGENTS.md:31–36` cites.
* Five more (`ContentPrefixExtensionPadding.lean`, `ContentPrefixExtensionPaddingTransport.lean`,
  `ContentParseFieldRecovery.lean`, `ContentTargetSizeBound.lean`,
  `ContentPrefixExtensionNonVacuity.lean`) exist only on `main`.
* **Repo-wide the divergent-path count is 40**, not nine
  (`git diff --name-status --diff-filter=M main pr1618 | wc -l` = 40; revision 4 said 41): the CI workflows, `AGENTS.md`,
  `lakefile.lean`, `STATUS.md`, both `AxiomsAudit.lean` files, `AlgorithmsToLowerBoundsSurfaceTests.lean`,
  five `pnp3/LowerBounds` and `pnp3/Magnification` modules, two `TuringToolkit` modules and a dozen
  Markdown documents all differ at the tips.

So `pr1618` is not a superset and a rebase is not a fast-forward. **Sizes in bytes throughout**
(`git cat-file -s`):

| Module | `pr1618` (bytes) | `main` (bytes) |
|---|---|---|
| `ContentPrefixExtension.lean` | 9 513 | **15 048** |
| `ContentPrefixExtensionCoincidence.lean` | 14 991 | **16 531** |
| `ContentPrefixExtensionTransfer.lean` | 7 387 | **8 761** |
| `ContentConsolidatedSource.lean` | 3 856 | **5 580** |
| `TreeMCSPPrefixSemanticVerifier.lean` | **15 858** | 14 166 |
| `TreeMCSPPrefixVerifierLayout.lean` | 12 967 | **14 231** |
| `ContentPrefixExtensionPadding.lean` | *absent* | **20 417** |
| `ContentPrefixExtensionPaddingTransport.lean` | *absent* | **2 960** |
| `ContentParseFieldRecovery.lean` | *absent* | **8 303** |
| `ContentTargetSizeBound.lean` | *absent* | **13 767** |
| `ContentPrefixExtensionNonVacuity.lean` | *absent* | **10 984** |
| `ConsolidatedTreeSeparation.lean` | *merge-base blob* | **changed on `main`** |
| `PrefixExtensionNPWitness.lean` | *merge-base blob* | **changed on `main`** |
| `README.md` | *merge-base blob* | **changed on `main`** |

`main` is ahead on the CT chain (CT-C, FEAS recovery/bound and GATE-0 non-vacuity exist only on `main`); `pr1618` is ahead only on
`TreeMCSPPrefixSemanticVerifier.lean`. Any future rebase of the stack must reconcile the six
added-on-both-sides modules by hand, take `main`'s version of the three `main`-only-changed paths,
and additionally settle `lakefile.lean`, `AlgorithmsToLowerBoundsSurfaceTests.lean` and
`AxiomsAudit.lean` — 40 divergent paths repo-wide.

### 3.3 Disposition of the donor stack: parked, not cancelled

`pr1526` / `pr1616` / `pr1618` are **parked**. No slice in this plan branches from them, imports
from them, or is blocked by them. They are not reviewed, rebased, or merged as part of the retarget.
Reactivation is a separate decision, and its first step is the six-file reconciliation of §3.2 —
not the donor's GATE-0.

### 3.4 Why the donor machine stack does not discharge input (2) — insufficient, but reusable

The donor's headline machine results are **transcoder** results, not verifier results.
`TreeMCSPTranscoderCapstone.lean` on `pr1618` proves `DriverRealization.transcodes` (`:40`) and
`DriverRealization.transcodes_faithful` (`:59`–`:78`): for a certificate
`encodeCircuit width h_width c ++ tail`, the machine's output window spells the `transcodeWitness`
gate stream, and that stream decodes to a straight-line program computing `Circuit.eval c` on every
input — conditional on a `DriverRealization` instance (`TreeMCSPDriverRealization.lean:45`, whose
`step_run` field `:54` is the missing per-iteration run obligation) that does not exist. That is
substantial machinery, and this section is about *scope*, not quality.

Against the frozen target that is **one component of one conjunct**. It never:

* reads the tag or decodes the Elias-gamma header (`contentHeader?`);
* reads the truth-table field `x` or the prefix-length field `i`;
* checks `prefixAgrees`, i.e. that the certificate extends the query's active prefix;
* checks `Circuit.size c ≤ threshold n`, or compares `Circuit.eval c` against
  `truthTableFunction x` on all `tableLen n = 2 ^ n` points;
* says anything about `TM.accepts`, `runTime`, or the exact-step evaluation point.

So even a completed donor driver instance would leave the `(★′)` bridge open.

**But it is not dead weight.** Witness-decoding — turning a certificate block into an object whose
`Circuit.eval` can be checked — is a genuine sub-obligation of *any* verifier for `L'`, and
`transcodeWitness` plus the region-embedding toolkit is the only machinery in the repository that
attacks it. The accurate statement is **insufficient but potentially reusable**: the donor stack
supplies at most the witness-decoding component, and the five bullets above must be scheduled
separately.

**Corollary for sequencing — narrowed in this revision.** The claim is now the weaker and defensible
one: **donor completion is not a prerequisite for FEAS-0, P0 or D1a**, none of which imports or cites
anything on `pr1618`, so nothing in §4 waits on it. It is **not** claimed that the donor arms are
categorically off the critical path to input (2): whether the eventual verifier machine reuses the
transcoder's witness-decoding machinery is a *machine-architecture* question, and that architecture
is not fixed in this plan (§4.7 defers the machine-construction slices). **Now that FEAS-0 has
landed, reassess the donor stack only when the machine architecture is chosen** — and until then,
do not book the donor manifest's "5 slices / ~3100–4400 LOC to the pop arm" as progress
on the `(★′)` bridge, because by itself it discharges none of the five bullets above.

---

## 4. FEAS-0, GATE-0 and the first slices

All items below are **dependency-closed on `main = 014a7768`** at this slice-log revision: every donor lemma they cite is in
§3.1, none is on `pr1618`.

**Sequencing.** FEAS-0 (§1.0) has landed as outcome (a). GATE-0, P0, I1 and D1a are now mutually
independent and may run in parallel, and D1b follows **both P0 and D1a** (D1b specializes D1a's
`acc`-parameterized bridge structure to `contentSemanticAccepts`, §4.4/§4.5).

Every slice obeys: **≤ 1500 changed `.lean` LOC (added + deleted) and ≤ 10 changed `.lean` modules**
(§6). Every new module carries the Infrastructure classification line and the
"**No `P ≠ NP` claim**" sentence, plus caveats 1–7 of §1.3 as applicable.

### 4.1 GATE-0 — non-vacuity of `ContentAccepts` at the concrete codec · **blocking for D-track, not for P0/I1**

**Why this was a gate.** Before this slice, nothing proved that any word was
`ContentAccepts`-accepted (§1.3, caveat 4).
If `ContentAccepts` were unsatisfiable at the concrete codec, `L'` would be the empty language;
`ContentPrefixExtensionNPWitness` would then be discharged by a trivial machine, and the
consolidated CT source `NP_not_subset_PpolyDAG_treePolyCT` would be worthless — its other
hypothesis, `NoPolynomialBoundedSearchSolver`, would be refuted rather than merely open, since
`ContentPrefixExtensionTransfer.lean:145` pins the *empty* `L'` outside `PpolyDAG`. Building a
verifier machine before settling this risks discharging a vacuous obligation. This replaces, and is
unrelated to, the donor's arm-embedding GATE-0.

**Status: PASS.** The three outputs below now settle the gate, culminating in
`contentAccepts_nonvacuous_treePoly` at the concrete codec.

**New module:** `ContentPrefixExtensionNonVacuity.lean`.

**Exact outputs.**

```lean
/-- Generic: a satisfied promise at `n` makes the zero-prefix query content-extendable. -/
theorem contentAccepts_zeroPrefixQuery_of_predicate
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpred : treeMCSPPredicate n (threshold n) x) :
    ∃ w : Pnp3.ComplexityInterfaces.Bitstring
            (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1),
      ContentAccepts codec
        (Pnp3.ComplexityInterfaces.concatBitstring (zeroPrefixQueryValue codec n x) w)

/-- Hence the zero-prefix query is in `L'`. -/
theorem contentPrefixExtensionLanguage_zeroPrefixQuery
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpred : treeMCSPPredicate n (threshold n) x) :
    ContentPrefixExtensionLanguage codec (treeMCSPPrefixM codec n)
      (zeroPrefixQueryValue codec n x) = true

/-- Concrete discharge: the all-false table on `n` variables is computed by `Circuit.const false`,
of size `1`.  (The binder `n` is used: it fixes the instance the witness is built at.) -/
theorem contentAccepts_nonvacuous_treePoly (k n : Nat) :
    ∃ z : PrefixBitVec
            (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n
              + Pnp3.ComplexityInterfaces.certificateLength
                  (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n) 1),
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z
```

The third signature is corrected in this revision: the previous form
`∃ (N : Nat) (z : PrefixBitVec N), …` left `n` an unused binder, so the statement was weaker than
its docstring and would draw an unused-variable lint. Pinning `z`'s length to the concatenated
zero-prefix shape makes `n` load-bearing.

**Proof route, fully on `main`.**
`zeroPrefixQueryValue_parses` (`TreeMCSPPrefixSerializer.lean:84`) supplies *both* hypotheses that
`contentInput?_concat_of_parse` (`Coincidence.lean:244`) needs — `hparse` **and**
`hn : input.n = n`. `prefixAgrees` is vacuous because `zeroPrefixFields` sets `i := 0`
(`TreeMCSPPrefixSerializer.lean:49`), `toPrefixInput` copies it verbatim
(`PrefixParserConvention.lean:675`), and `PrefixInput.prefixAgrees` is a `∀ k : Fin input.i`
(`PrefixExtensionLanguage.lean:52`). The relation conjunct comes from
`TreeCircuitWitnessCodec.complete` (`SearchMCSPConcreteTargets.lean:85`), with the witness
transported into the certificate's leading `witnessBits` block by
`contentWitness_concat` (`Coincidence.lean:218`). The concrete discharge takes
`c := Pnp3.Models.Circuit.const false` (size `1`, `pnp3/Models/Model_PartialMCSP.lean:53`) against
`x := fun _ => false`, and `1 ≤ thresholdPoly k n = n ^ k + k` for every `k, n` (at `k = 0` the
first summand is `n ^ 0 = 1`; at `k ≥ 1` the second summand suffices).

**Budget:** 200–350 LOC · 1 module. **Exit:** all three theorems green with the standard axiom
triple, `#check`/`#print axioms` lines added.
**Stop/go (G0):** if the third theorem cannot be discharged — i.e. if satisfiability of
`ContentAccepts` at `treeCircuitWitnessCodec (thresholdPoly k)` resists a *concrete* witness —
**halt the D-track and escalate.** Do not begin machine work against a predicate not known to be
satisfiable. P0 and I1 remain admissible either way, since both are statements *about* the predicate
rather than claims that it holds.

### 4.2 P0 — content-side semantic verifier and its correctness · *parallel-safe once FEAS-0 is green*

**Why.** CT-A's semantic core is stated against the length-gated language (§1.2), and its signature
splits query and certificate (`treePrefixSemanticAccepts codec N query cert`,
`TreeMCSPPrefixSemanticVerifier.lean:192`), whereas `ContentAccepts` consumes a **single complete
word** read through `padRead`. The frozen target therefore has no `Bool`-valued computable
counterpart, which is the object every `TM.accepts` bridge must be compared against.

**New module:** `ContentSemanticVerifier.lean`.

**Exact outputs.**

```lean
/-- The content-computed `Bool` verifier on a complete word: content-parse, read the content
witness window, check prefix agreement and codec verification. -/
def contentSemanticAccepts {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) : Bool

/-- **Headline: the Bool verifier decides the frozen predicate.** -/
theorem contentSemanticAccepts_eq_true_iff {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) :
    contentSemanticAccepts codec z = true ↔ ContentAccepts codec z

/-- Rejection when the content parse fails. -/
theorem contentSemanticAccepts_eq_false_of_contentInput_none {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    (h : contentInput? codec z = none) :
    contentSemanticAccepts codec z = false

/-- Padding stability, inherited: the Bool verifier is a function of the padded tape. -/
theorem contentSemanticAccepts_padWord_of_le {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) :
    contentSemanticAccepts codec (padWord z T) = contentSemanticAccepts codec z

/-- **The `L'`-side counterpart of `treePrefixSemanticAccepts_correct`.** -/
theorem contentSemanticAccepts_correct {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {m : Nat} (y : PrefixBitVec m) :
    ContentPrefixExtensionLanguage codec m y = true
      ↔ ∃ w : Pnp3.ComplexityInterfaces.Bitstring
                (Pnp3.ComplexityInterfaces.certificateLength m 1),
          contentSemanticAccepts codec (Pnp3.ComplexityInterfaces.concatBitstring y w) = true
```

**Proof route, fully on `main`.** `contentInput?` is a plain `def` over the computable strict parser
(`PrefixParserConvention.lean:1130`); the two checks reuse `prefixAgreesBool` /
`prefixAgreesBool_eq_true_iff` (`TreeMCSPPrefixSemanticVerifier.lean:99`, `:105`) and `verifiesBool`
/ `verifiesBool_eq_true_iff` (`:121`, `:128`). The existential in `ContentAccepts` is pinned by
`contentInput? codec z = some pr`, so the `↔` is a `match` analysis, not a choice. Padding
stability is `contentInput?_padWord_of_le` (`Padding.lean:293`) and `contentWitness_padWord_of_le`
(`:300`). The last theorem is `ContentPrefixExtensionLanguage_accepts_iff`
(`ContentPrefixExtension.lean:178`) composed with the headline.

Note `contentSemanticAccepts` does **not** need `extractWitness?` (`:160`): the content witness
window is already total via `padRead`, so CT-A's dependent-slice machinery is bypassed. Do not port
it.

**Budget:** 350–550 LOC · 1–2 modules.
**Stop/go (G1):** the headline must be an unconditional `↔`, with **no** `hparse`/`hn` hypothesis. If
a hypothesis is needed, the `Bool` definition is wrong (it is failing to mirror `contentInput?`'s
own failure branches) — fix the definition, not the statement.
**Stop/go (G2) — corrected in this revision.** The previous revision demanded that "the four
non-wrapper theorems avoid `Classical.choice` in `#print axioms`". That is **false and
unachievable**: `verifiesBool` resolves `Decidable (codec.verifies …)` through the local instance
`instDecidableCodecVerifies` (`TreeMCSPPrefixSemanticVerifier.lean:114`) to
`TreeCircuitWitnessCodec.verifiesDecidable` (`PrefixExtensionLanguageNP.lean:92`), which carries
`Classical.choice` — as `pnp4/Pnp4/Tests/AxiomsAudit.lean:479–483` already records for CT-A's own
`verifiesBool_eq_true_iff`. Correct expectations:

* `contentSemanticAccepts_padWord_of_le` — arithmetic/padding only; **may** be
  `[propext, Quot.sound]`, matching `ContentPrefixExtensionPadding.lean`'s Classical-free family.
  Do not force this if the definition routes through `verifiesBool`.
* `contentSemanticAccepts_eq_true_iff`, `contentSemanticAccepts_eq_false_of_contentInput_none`,
  `contentSemanticAccepts_correct` — expect the standard triple
  `[propext, Classical.choice, Quot.sound]` **or lighter**, inherited from `verifiesDecidable` and
  (for the last) the classical language wrapper and noncomputable `concatBitstring`.
* **"Or lighter" is deliberate, and corrected in this revision.** Revision 3 demanded *exactly* the
  triple for these three. That is too strict: `contentSemanticAccepts_eq_false_of_contentInput_none`
  is a pure failure-branch rewrite that can discharge by `simp` on `contentInput? … = none` without
  ever unfolding `verifiesBool`, in which case it legitimately prints a shorter list. Demanding the
  full triple would push an author to *add* a classical detour to satisfy a checklist. The rule is
  therefore the same as G9: **the standard triple or any subset of it.**
* A fourth axiom — anything outside `{propext, Classical.choice, Quot.sound}` — is still a blocker
  (G9).

Computability is a **separate** property from the axiom footprint and must be checked separately:
`contentSemanticAccepts` must be a plain `def` with no `noncomputable` marker, its `Decidable`
instances must resolve to `Fintype.decidableForallFintype` and
`TreeCircuitWitnessCodec.verifiesDecidable` rather than `Classical.propDecidable`, and the slice
must exhibit one `#eval` (or `decide`) on a small concrete word in the surface-test file. `#print
axioms` cannot detect a `Classical.propDecidable` substitution here, because the honest route
already carries `Classical.choice`.

### 4.3 I1 — close the residual gate premises · *parallel-safe once FEAS-0 is green*

**Why.** Two families of side conditions currently infect every coincidence statement and would
infect the machine's correctness proof:

* `hn : input.n = n` in `ContentPrefixExtendable_iff_of_parse` (`Coincidence.lean:276`) and
  `ContentPrefixExtensionLanguage_eq_of_parse` (`:324`). Inversion
  (`parseTreeMCSPPrefixInput_inversion`, `:140`) yields only
  `treeMCSPPrefixM codec input.n = treeMCSPPrefixM codec n`; injectivity of `treeMCSPPrefixM codec`
  is not proved (docstring at `:319–:323`).
* The narrowing direction of the gamma decode, and the enumeration of what actually remains after
  it (§1.3, caveat 3).

**Edited/new modules:** new `ContentPrefixExtensionGateClosure.lean`; no edit to
`Coincidence.lean` in this slice (the `hn`-free corollaries are stated in the new module, so the
existing surface and its audit lines stay untouched).

#### 4.3.1 Injectivity: the generic goal is **false** — specialize it

The previous revision proposed
`treeMCSPPrefixM_injective (codec : TreeCircuitWitnessCodec threshold) : Function.Injective (treeMCSPPrefixM codec)`
and justified it by "`tableLen_le_treeMCSPPrefixM` plus `Nat.lt_two_pow_self` give strict
monotonicity". **Both the goal and the route are wrong.**

* `treeMCSPPrefixM codec n = tagLen + gammaLen n + tableLen n + idxWidth codec.witnessBits n + codec.witnessBits n`
  (`PrefixParserConvention.lean:40`), and `TreeCircuitWitnessCodec.witnessBits : Nat → Nat`
  (`SearchMCSPConcreteTargets.lean:46`) is **unconstrained**: only `decode_encode` touches it, and
  it bounds `witnessBits` from *below*. A codec may pad `witnessBits` upward by any amount at any
  single `n` (the extra bits are simply ignored by `decode`). Since
  `k ↦ k + bitLength k` advances by 1 or 2 per step, `witnessBits` can be inflated at `0` and at `1`
  until `treeMCSPPrefixM codec 0 = treeMCSPPrefixM codec 1`. So injectivity **fails for some legal
  codec**, and no proof can exist.
* `tableLen_le_treeMCSPPrefixM` (`:48`) gives `2 ^ n ≤ treeMCSPPrefixM codec n` — a *lower* bound.
  Strict monotonicity needs an *upper* bound on `treeMCSPPrefixM codec n`, which does not exist
  without constraining `witnessBits`. `instanceSize_lt_treeMCSPPrefixM`
  (`TreeMCSPPrefixVerifierLayout.lean:194`) proves `n < treeMCSPPrefixM codec n`, not monotonicity,
  so it is not a model for this argument.

Replace with the specialized forms, both true:

```lean
/-- Under monotone witness width, `treeMCSPPrefixM codec` is strictly monotone: `tagLen` is
constant, `gammaLen`, `idxWidth codec.witnessBits` and `codec.witnessBits` are monotone, and
`tableLen n = 2 ^ n` is strictly monotone. -/
theorem treeMCSPPrefixM_strictMono {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits) :
    StrictMono (treeMCSPPrefixM codec)

theorem treeMCSPPrefixM_injective_of_monotone {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits) :
    Function.Injective (treeMCSPPrefixM codec)

/-- The concrete codec qualifies: `witnessBits n = (bitLength n + 4) * thresholdPoly k n`. -/
theorem witnessBits_monotone_treePoly (k : Nat) :
    Monotone (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits

theorem treeMCSPPrefixM_injective_treePoly (k : Nat) :
    Function.Injective (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)))

/-- **`hn` eliminated, under the monotonicity premise.** -/
theorem ContentPrefixExtendable_iff_of_parse' {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ContentPrefixExtendable codec y
      ↔ PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y
```

`hmono` replaces `hn`, and every downstream consumer at the concrete threshold discharges it once
via `witnessBits_monotone_treePoly`. Monotonicity of `bitLength` (`PrefixParserConvention.lean:22`,
`if n = 0 then 0 else Nat.log2 n + 1`) and of `n ^ k + k` are the two arithmetic sublemmas.

#### 4.3.2 Gamma canonicity is a **theorem**, and the length gate is unconditionally vacuous

The previous revision carried `hcanon : consumed = gammaLen n'` as a hypothesis and declared
unconditional gate vacuity "false as stated". Corrected: canonicity is forced by a successful
decode.

```lean
/-- A field read of `width` bits is bounded by `2 ^ width`.  (No general bound exists on `main`;
`prefixLength_lt_two_pow_idxWidth` (`PrefixParserConvention.lean:329`) is a different statement.) -/
theorem readNatBE_lt_two_pow {m : Nat} (y : PrefixBitVec m) (offset width : Nat)
    {v : Nat} (h : readNatBE y offset width = some v) :
    v < 2 ^ width

/-- **Canonicity from a successful decode.**  `decodeGammaAux?` terminates at the first `true` bit,
returning `consumed = 2 * zeros + 1` and `n' + 1 = 2 ^ zeros + payload` with `payload < 2 ^ zeros`;
hence `bitLength (n' + 1) = zeros + 1` and `consumed = gammaLen n'`. -/
theorem decodeGamma?_consumed_eq_gammaLen {m : Nat} (y : PrefixBitVec m)
    {offset n' consumed : Nat}
    (h : decodeGamma? y offset = some (n', consumed)) :
    consumed = gammaLen n'

theorem contentHeader?_consumed_eq_gammaLen {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat} (hheader : contentHeader? z = some (n', consumed)) :
    consumed = gammaLen n'

/-- **Narrowing, unconditional.**  A successful content-header decode re-succeeds, with the same
target, on the narrow window `padWord z (treeMCSPPrefixM codec n')`. -/
theorem decodeGamma?_padWord_narrow {N : Nat} (z : PrefixBitVec N)
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed)) :
    decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen = some (n', consumed)

/-- **The length gate never fires.**  The strict parser's re-decode on the narrow window returns
`n'` itself, so its `m = treeMCSPPrefixM codec n_dec` test compares `treeMCSPPrefixM codec n'`
with itself and the `_hlen` branch is always taken. -/
theorem contentInput?_lengthGate_vacuous {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed n_dec consumed_dec : Nat}
    (hheader : contentHeader? z = some (n', consumed))
    (hnarrow : decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen
                 = some (n_dec, consumed_dec)) :
    n_dec = n' ∧ treeMCSPPrefixM codec n' = treeMCSPPrefixM codec n_dec
```

**Proof route, fully on `main`.** Canonicity: `readNatBE_lt_two_pow` (new) by induction on `width`
over the `readNatBE` recursion — declared at `PrefixParserConvention.lean:61`, with the two match
arms this induction mirrors at **`:62`–`:67`** (`| 0 => some 0` and
`| k + 1 => … some ((if b then 2 ^ k else 0) + rest)`, whence `rest < 2 ^ k` gives
`v < 2 ^ k + 2 ^ k = 2 ^ (k+1)`). Citation corrected in this revision: revision 3 pointed at the
whole span `:61`–`:67`, conflating the declaration header with the recursion, and revision 2 pointed
at `:89`, which is the `match fuel with` line *inside* `decodeGammaAux?`. Note the only existing
`readNatBE` structural lemma on `main` is `readNatBE_eq_of_readBit_eq` (`:155`, pointwise
determinacy) — there is **no** width bound anywhere in the repository, which is why
`readNatBE_lt_two_pow` is new. Then `gammaLen_eq_two_mul_zeros_add_one` (`:371`) and `bitLength`
(`:22`) finish.
Narrowing: a successful header decode puts the terminator strictly inside the support
(`padRead_ge`, `ContentPrefixExtension.lean:88`, so `tagLen + zeros < N`), and
`decodeGammaAux?_padWord_support` (`Padding.lean:186`) plus `readNatBE_padWord_transfer` (`:151`)
move both the terminator search and the payload read to the narrow window. The width side condition
is `queryXOffset_le_treeMCSPPrefixM` (`TreeMCSPPrefixVerifierLayout.lean:166`) combined with
`gammaLen_eq_two_mul_gammaZeros_add_one` (`:226`), i.e.
`tagLen + 2 · gammaZeros n' + 1 ≤ treeMCSPPrefixM codec n'`, which is now available *because*
`consumed = gammaLen n'` is a theorem rather than an assumption. Both windows agree on every read
cell: all read positions are `< tagLen + gammaLen n' ≤ 2 * N + 1`, and cells in `[N, ·)` are blank
in both. The existing `decodeGammaAux?_padWord_canonical` (`Padding.lean:223`) cannot be reused: it
requires `2 * N + 1 ≤ T'`, i.e. widening, and here `T' = treeMCSPPrefixM codec n'` may be smaller.

#### 4.3.3 Every remaining parser premise, enumerated

`parseTreeMCSPPrefixInput` (`PrefixParserConvention.lean:1130`) has **eleven** exit points, not
"four field reads". On the narrow window `padWord z (treeMCSPPrefixM codec n')`, given
`contentHeader? z = some (n', consumed)`, they split cleanly:

**Automatic (discharged by §3.1 lemmas — a slice must prove these, not assume them):**

| # | Premise | Discharged by |
|---|---|---|
| 1 | `readNatBE y 0 tagLen` succeeds | `TreeMCSPPrefixVerifierLayout.lean:183` `gammaLen_le_treeMCSPPrefixM` (`tagLen ≤ M n'`) |
| 2 | `decodeGamma? y tagLen` succeeds, returns `(n', consumed)` | `decodeGamma?_padWord_narrow` (§4.3.2) |
| 3 | length gate `m = treeMCSPPrefixM codec n_dec` | `contentInput?_lengthGate_vacuous` (§4.3.2) |
| 4 | `sliceBits? y xOffset (tableLen n')` succeeds | `TreeMCSPPrefixVerifierLayout.lean:174` `queryIdxOffset_le_treeMCSPPrefixM` |
| 5 | `readNatBE y iOffset (idxWidth codec.witnessBits n')` succeeds | `TreeMCSPPrefixVerifierLayout.lean:157` `queryPrefixOffset_le` |
| 6 | `sliceBits? y pOffset i` succeeds | `TreeMCSPPrefixVerifierLayout.lean:148` `queryPrefixOffset_add_witnessBits`, given #10 |
| 7 | `sliceBits? y padOffset (codec.witnessBits n' - i)` succeeds | `TreeMCSPPrefixVerifierLayout.lean:148` `queryPrefixOffset_add_witnessBits`, given #10 |
| 8 | `allZeroSlice? y padOffset (…)` succeeds | same range argument as #7 |

**Not automatic — three genuine *value* tests, and the honest residue:**

| # | Premise | Status |
|---|---|---|
| 9 | `tag = treePrefixTag` | open; `contentHeader?` never reads the tag, so a word with a valid gamma and a wrong tag is legitimately rejected |
| 10 | `i ≤ codec.witnessBits n'` | open; `i` is read off the tape and may exceed the witness width |
| 11 | `padZero = true` | open; the inactive suffix must be all-zero |

So the honest closure statement is a characterisation, not a vacuity claim:

```lean
/-- Given a successful content-header decode, `contentInput?` succeeds **iff** the three value tests
pass; every range/fit premise and the length gate discharge unconditionally. -/
theorem contentInput?_isSome_iff_of_header {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed)) :
    (contentInput? codec z).isSome
      ↔ (<#9 tag test> ∧ <#10 index bound> ∧ <#11 pad-zero test>
           at the canonical offsets of `padWord z (treeMCSPPrefixM codec n')`)
```

**The three value tests are load-bearing and must not be dropped.** A slice claiming that
`contentInput?` *never* returns `none` is wrong and must be rejected: words failing #9/#10/#11 are
simply not in `L'`, which is sound behaviour.

**Budget:** 500–800 LOC · 2–3 modules (split at §4.3.1 / §4.3.2+§4.3.3 if the size gate binds).
**Stop/go (G3):** state injectivity **only** in the two specialized forms of §4.3.1. A slice that
re-proposes the generic `Function.Injective (treeMCSPPrefixM codec)` must be rejected as false, not
merely unproved. Do **not** work around it by strengthening `PrefixInput`.
**Stop/go (G4):** `decodeGamma?_consumed_eq_gammaLen` must be **hypothesis-free** beyond the
successful decode. If canonicity needs an extra premise, the `readNatBE` payload bound is wrong —
fix `readNatBE_lt_two_pow`, not the statement.
**Stop/go (G4b):** `contentInput?_isSome_iff_of_header` must enumerate exactly premises #9–#11 on
its open side. Adding a fourth open premise means a range lemma was missed; folding one away means
the parser was mis-read.

### 4.4 D1a — the machine-facing tape lemmas and the bridge structure · *independent, parallel-safe once FEAS-0 is green*

**Why.** The `(★′)` bridge `TM.accepts (M := M) (concatBitstring x w) = contentSemanticAccepts …`
compares two objects that are currently stated over different data: `TM.accepts` reads a
`Configuration` tape of length `TM.tapeLength n = n + runTime n + 1`
(`TuringEncoding.lean:73`), while `ContentAccepts` reads `padRead` of a finite word. Identifying the
two is a theorem, not a definition, and it is the exact point where caveat 6 becomes visible.

CT-A's layout module is the donor but is **not sufficient on its own**: `verifierTape_left` (`:103`)
and `verifierTape_right` (`:114`) read the start tape in the two `concatBitstring` ranges, and every
offset lemma (`:136`–`:258`, ending at `gammaMirror_mem`) is stated against the *length-gated* query
block `treeMCSPPrefixM codec n`, not against the content-computed window.

**New module:** `ContentVerifierTapeInterface.lean`.

**Exact outputs — none of these depend on P0.**

```lean
/-- **The start tape is the blank-padded complete word.**  For every in-range cell, the
`initialConfig` tape of the concatenated input equals `padRead` of that word — including past the
support, where both are the blank `false`. -/
theorem initialConfig_tape_eq_padRead
    (M : Pnp3.Internal.PsubsetPpoly.TM.{0}) {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n)
    (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = padRead (Pnp3.ComplexityInterfaces.concatBitstring x w) (j : Nat)

/-- **Tape-determined acceptance.**  Any two complete words with the same blank-padded tape are
`ContentAccepts`-equivalent — the machine-facing form of `ContentAccepts_iff_of_padRead_eq`. -/
theorem contentAccepts_of_initialConfig_tape_eq {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N N' : Nat}
    (z : PrefixBitVec N) (z' : PrefixBitVec N')
    (h : ∀ j, padRead z j = padRead z' j) :
    ContentAccepts codec z ↔ ContentAccepts codec z'

/-- **The exact-step obligation, named.**  The bridge a verifier machine must discharge, with the
evaluation point spelled out as `runTime` rather than left implicit.  The acceptance predicate is an
**explicit parameter** `acc`, so this declaration does not mention — and does not depend on — P0's
`contentSemanticAccepts`; D1b instantiates it (§4.5).  See §1.3 caveat 6: this structure does
**not** exclude a machine whose `runTime` carries length advice. -/
structure ContentVerifierBridgeFor
    (acc : ∀ {N : Nat}, PrefixBitVec N → Bool) where
  M : Pnp3.Internal.PsubsetPpoly.TM.{0}
  c : Nat
  runTime_poly : ∀ n,
    M.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n 1)
      ≤ (n + Pnp3.ComplexityInterfaces.certificateLength n 1) ^ c + c
  accepts_eq : ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n)
      (w : Pnp3.ComplexityInterfaces.Bitstring
             (Pnp3.ComplexityInterfaces.certificateLength n 1)),
    Pnp3.Internal.PsubsetPpoly.TM.accepts
        (M := M) (n := n + Pnp3.ComplexityInterfaces.certificateLength n 1)
        (Pnp3.ComplexityInterfaces.concatBitstring x w)
      = acc (Pnp3.ComplexityInterfaces.concatBitstring x w)
```

**Declaration-level dependency, fixed in this revision.** The previous revision displayed this
structure with `accepts_eq` mentioning `contentSemanticAccepts` *and* claimed D1a was independent of
P0, then relegated the repair to a prose note. Both cannot hold: a field mentioning a P0 definition
is a P0 dependency at declaration level. The displayed signature above is therefore the *exact* D1a
output — parameterized by `acc`, mentioning nothing from P0 — and the `codec`-specific alias

```lean
abbrev ContentVerifierBridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :=
  ContentVerifierBridgeFor (fun {_} z => contentSemanticAccepts codec z)
```

is an output of **D1b**, not of D1a. With that split, all three D1a outputs are genuinely
P0-free — in dependency *and* in signature.

**Proof route.** The first theorem is read off `initialConfig`
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean:133`, with `initial_tape_input` `:140`
and `initial_tape_blank` `:146`) — modelled line-for-line on `verifierTape_left` /
`verifierTape_right` (`TreeMCSPPrefixVerifierLayout.lean:103`, `:114`), with `padRead_ge`
(`ContentPrefixExtension.lean:88`) covering the blank tail. The second is
`ContentAccepts_iff_of_padRead_eq` (`Padding.lean:333`) restated for machine consumers.

**Budget:** 250–400 LOC · 1–2 modules.
**Stop/go (G5):** `ContentVerifierBridgeFor.accepts_eq` must be stated with the concatenated length
`n + certificateLength n 1` and no "within `t` steps" quantifier. If a slice introduces a
step-bounded or halting-based variant it has silently changed the machine model — reject it.
**Stop/go (G5b):** no D1a declaration may mention `contentSemanticAccepts`. If one does, the slice
is not P0-independent and must either take the `acc` parameter or move to D1b.

### 4.5 D1b — the bridge specialization and the witness repackaging · **depends on P0 *and* D1a**

Split out from D1a in revision 2, and made exact in revision 3: the P0-dependent part is
*both* declarations below — the `codec`-specific bridge alias (whose statement mentions
`contentSemanticAccepts`) and the repackaging that consumes it. Revision 2 displayed the alias among
D1a's "exact outputs" while calling D1a independent, which was false at declaration level.

**Both dependencies are hard, and this revision records the D1a one everywhere.** D1b's alias
*is* `ContentVerifierBridgeFor` — D1a's structure — instantiated, and `contentPrefixExtensionNPWitness_of_bridge`
projects `B.M`, `B.c`, `B.runTime_poly` and `B.accepts_eq` out of it. So D1b cannot compile without
D1a, and cannot be stated without P0. Revision 3's dependency graph (§4.6) had this right, but the
heading above, the branch strategy (§5) and the slice log (§7.1) all named P0 only; all three are
corrected.

**Module:** appended to `ContentVerifierTapeInterface.lean`, or `ContentVerifierBridgeWitness.lean`
if the size gate binds.

```lean
/-- The frozen target's bridge: D1a's structure at `acc := contentSemanticAccepts codec`. -/
abbrev ContentVerifierBridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :=
  ContentVerifierBridgeFor (fun {_} z => contentSemanticAccepts codec z)

/-- **The bridge discharges the frozen target.**  `(★′)` plus P0's correctness theorem *is* the
NP-witness — the only remaining input is a machine satisfying `ContentVerifierBridge`. -/
def contentPrefixExtensionNPWitness_of_bridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (B : ContentVerifierBridge codec) :
    ContentPrefixExtensionNPWitness codec
```

**Proof route.** A one-line repackaging: `M := B.M`, `c := B.c`, `runTime_poly := B.runTime_poly`
verbatim, and `correct` obtained by rewriting `TM.accepts` to `contentSemanticAccepts` via
`B.accepts_eq` and then applying P0's `contentSemanticAccepts_correct` (§4.2), whose shape matches
the `correct` field of `ContentPrefixExtensionNPWitness` (`ContentPrefixExtension.lean:211`)
exactly at `k = 1`.

**Budget:** 60–120 LOC · 1 module.
**Stop/go (G6) — a review convention, not a machine-checked gate (§1.3 caveat 6).**
`contentPrefixExtensionNPWitness_of_bridge` must consume `runTime_poly` verbatim; if it needs to
*construct* a runtime bound, the bridge structure is under-specified. Reviewers should also refuse a
bridge instance that makes `accepts_eq` easy by hiding work in the clock — that is the advice
channel `lengthAdviceLanguage_in_repo_P` (`RuntimeAdviceBarrier.lean:77`) exhibits. **But note this
is unenforceable as written:** `runTime_poly` constrains the clock's magnitude only, so no theorem
in this slice rules such an instance out. Treat G6 as unenforced until a formal clock premise is
added to `ContentVerifierBridge` and cited in §1.3 caveat 6.

### 4.6 Dependency graph and parallelism

```text
FEAS-0  ──────────────────────────────── DONE: outcome (a), freeze promoted
   ▼
GATE-0  ─┐
P0      ─┼─ mutually independent; all four are now unlocked
I1      ─┤
D1a     ─┘   (bridge structure parameterized by `acc`; no P0 dependency)

P0 + D1a  → D1b = ContentVerifierBridge (the acc := contentSemanticAccepts specialization)
                  + contentPrefixExtensionNPWitness_of_bridge
GATE-0    → any D-track slice past D1a  (do not build a machine for a possibly-vacuous predicate)
I1        → hn-free coincidence consumers  (quality-of-life, blocks nothing in this batch)
{P0, D1a} → the machine construction slices (out of scope here; a separate plan revision)
```

**Shared-file conflict surface — serialize the append or reserve a per-slice block:**

* `lakefile.lean` — the `lean_lib Pnp4` `Glob.one` list. Every slice touches it (AGENTS.md).
* `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` — add to the
  `ContentPrefixExtensionSurface` section; FEAS-0, GATE-0 and P0 all append there.
* `pnp4/Pnp4/Tests/AxiomsAudit.lean` — one `#print axioms` line per new public theorem.
* `pnp4/Pnp4/Frontier/ContractExpansion/README.md` — the CT module list, and the "Plan of record
  for input (2)" paragraph, which must track §1.2's frozen status.
* This file — §1.2, §7 log.

Assign each slice a contiguous reserved block in the three shared files at kickoff; conflicts then
resolve as adjacent-line merges.

### 4.7 Rejected slice proposals

* **"Rebase `pr1618` onto `main`"** as a retarget slice — §3.2/§3.4: it is a 184-file, six-way
  reconciliation that does not advance the frozen target.
* **"Finish `popIter_run_*` / `inputIter_run_full` / the driver instance"** — donor-only and
  transcoder-side, so **not a prerequisite for any slice in §4** and rejected *as a retarget slice
  now*. Wording corrected in this revision: it is **not** claimed to be off the critical path to
  input (2) — §3.4 withdrew that claim, because whether the eventual verifier machine reuses the
  transcoder's witness-decoding machinery is an open machine-architecture question. Reassess after
  the architecture is chosen; admissible then as scoped witness-decoding reuse,
  never as `(★′)` bridge progress on its own.
* **"Port `extractWitness?` to the content side"** — dead weight: `contentWitness` is total
  (§4.2).
* **"Retarget the layout offsets to the content window"** as a standalone slice — pure layout,
  rejected by the no-layout-only rule. Folded into D1a, which carries
  `initialConfig_tape_eq_padRead`.
* **"Prove wrapper-level padding invariance of `L'`"** — not obviously true (the certificate length
  and concatenation offset both move with `m`, §1.3 caveat 2) and not needed by any slice here.
  Out of scope until a slice demonstrably needs it.
* **"Delete or deprecate the length-gated chain"** — forbidden by §1.2 under every FEAS-0 outcome.
* **"Prove `Function.Injective (treeMCSPPrefixM codec)` for a generic codec"** — **false**
  (§4.3.1).
* **"Assume `consumed = gammaLen n'` as a hypothesis"** — unnecessary: it is a theorem (§4.3.2).
* **"Prove `contentInput?` never returns `none`"** — false: premises #9–#11 of §4.3.3 are genuine
  rejections.
* **"Treat the target-size bound as a verifier or NP-membership proof"** — false: FEAS-0 closes
  only the size obstruction; the machine, runtime and `TM.accepts` bridge remain open (§1.3).

---

## 5. Branch and base strategy

```bash
# Base every slice on main, NOT on 4a8ee0c9.
git fetch origin
git checkout -b work/<slice-name> 014a7768      # or the then-current main
```

* **Base:** `main` (`014a7768` at this slice-log revision). One branch per slice, one PR per branch,
  PR base `main`. No stacking: the slices after FEAS-0 are independent, so stacking would only
  serialize review. **D1b is the one exception, and it stacks on *both* P0 and D1a** — it needs P0's
  `contentSemanticAccepts` for its statement and D1a's `ContentVerifierBridgeFor` for its structure
  (§4.5). Branch it from whichever of the two merges last, and rebase onto the other; do not open it
  against bare `main`.
* **Naming:** the active short slice names are `work/feas0-target-bound`,
  `work/gate0-nonvacuity`, `work/p0-content-semantic`, `work/i1-gate-closure`,
  `work/d1a-tape-interface`, and `work/d1b-bridge-witness`.  They retain the same one-slice/one-PR
  discipline as the earlier `work/ct-a-*`, `work/ct-b-*`, and `work/ct-c-*` branches.
* **Never branch from `pr1526` / `pr1616` / `pr1618`** (§3.3). Never merge them into a slice branch.
* **No push without an explicit request** (AGENTS.md line 83). Local commits only by default.
* **Rebase, don't merge**, when `main` moves under an open slice; re-run §6 after every rebase,
  because the LOC/module gate is measured against the *current* merge base.

---

## 6. Size and acceptance gates

### 6.1 Size gate — must pass before opening a PR, and again after every rebase

```bash
# ≤ 1500 changed .lean LOC (added + deleted)
git diff --stat "$(git merge-base main HEAD)"...HEAD -- '*.lean' | tail -1
# ≤ 10 changed .lean modules
git diff --name-only "$(git merge-base main HEAD)"...HEAD -- '*.lean' | wc -l
```

Never waived. If a slice breaches either bound, split it before review — the split points are named
in each slice's "modules" range in §4.

### 6.2 Acceptance commands, in order

```bash
# 1. per-module compile — fastest failure signal
lake build Pnp4.Frontier.ContractExpansion.<NewModule>

# 2. both libraries (check.sh step 1 needs Pnp4's axiom dump)
lake build PnP3 Pnp4

# 3. smoke + tests
lake env lean --run scripts/smoke.lean
lake test

# 4. repository gate (17 steps: build, hygiene, axiom inventory, doc route policy, surface audit)
./scripts/check.sh

# 5. documentation honesty linter (Tier 2, repo-wide)
./scripts/check_doc_honesty.sh

# 6. purity gate — every axiom named anywhere in the audit block must be one of the standard three.
#    Collect the union of all printed axioms and eyeball it; the output is NOT expected to be empty.
lake build Pnp4 2>&1 | grep -A1 "depends on axioms" \
  | grep -oE "\[[^]]*\]" | tr -d '[]' | tr ',' '\n' | tr -d ' ' | sort -u
# Every line of that output must be exactly one of: propext / Classical.choice / Quot.sound.
# Any fourth name is the blocker (G9).

# 7. hygiene (also inside check.sh; standalone for speed)
rg -n "\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom " -g'*.lean' pnp4   # must be empty
```

**Note on step 6 — command corrected in this revision.** Revision 3's filter was
`grep -v "propext, Classical.choice, Quot.sound"` with the comment "must produce no output", while
the very next paragraph said a Classical-free theorem prints a *shorter* list that "this filter also
surfaces". Both cannot hold: any lighter footprint makes the command non-empty, so the gate was
self-contradictory and would fail on the arithmetic/padding families it explicitly blesses. The
replacement above tests the right property — the *set* of axioms used, not the exact string of each
line — so a shorter list passes silently and only a genuinely foreign axiom fails. Lighter footprints
are expected (§4.2, G2, G9): inspect, do not "fix".

### 6.3 Mandatory per AGENTS.md, every slice

* new module registered in `lakefile.lean`;
* every new public theorem `#check`ed in
  `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` (`ContentPrefixExtensionSurface`);
* every new audited surface `#print axioms`-ed in `pnp4/Pnp4/Tests/AxiomsAudit.lean`;
* no `axiom` / `sorry` / `admit` / `native_decide`;
* module docstring states **Infrastructure** and "**No `P ≠ NP` claim**", and reproduces the
  applicable caveats from §1.3 — including caveat 7's distinction between the proved target-size
  bound and the still-unbuilt verifier machine.

---

## 7. Review workflow

The CT-A/B/C commit history is the template; each slice follows the same five stages, and the
per-stage fix commits are expected to be visible in the branch log (as in
`20be8cbf` "address CT-A review", `9ba903d4` "doc-audit fixes", `545fc200` "count split padding
modules accurately").

1. **Implement.** One slice, one branch. Author the Lean, register it, add the surface and axiom
   lines, run §6.2 end to end locally.
2. **Qodo review** on the PR. Treat every finding as blocking until answered in writing. Qodo
   catches statement/docstring mismatches, which are the dominant defect class in this directory —
   the CT-C history is mostly prose-scope corrections, not proof fixes.
3. **Claude review** (`/code-review`, effort `high`, plus `/security-review` when a slice touches
   the machine model). Focus: does the headline actually say what the docstring claims, and is any
   hypothesis silently doing the work?
4. **Codex cross-check.** Independent re-derivation of the slice's headline from its cited donors,
   without reading the proof. Its job is to catch a *true theorem that does not mean what the plan
   said it would* — the failure mode §3.4 found in the donor stack.
5. **Documentation audit.** Re-read the slice's docstrings and this file's §1.3 against the merged
   statements. Update `ContractExpansion/README.md`, and §7's log below, in the same PR. Then
   re-run `./scripts/check.sh` and `./scripts/check_doc_honesty.sh`, because the doc guards read
   Markdown that step 5 has just changed.

**Scope discipline for reviewers.** Reject a slice that (i) deletes or weakens the retained
length-gated compatibility chain (§1.2); (ii) claims any machine-side consequence from a
specification-side lemma; (iii) describes the CT
route as removing length-dependence from the machine (`runTime_poly` is still taken at
`n + certificateLength n 1`) or as advice-free (§1.3 caveat 6); (iv) describes the decision→search
extraction as an equivalence (AGENTS.md line 36); (v) proposes the generic injectivity goal or
unconditional `contentInput?` success (§4.7); or (vi) reports green CI as mathematical progress.

### 7.1 Slice log

| Slice | Branch | Status | Merged as |
|---|---|---|---|
| FEAS-0 target size bound | `work/feas0-target-bound` | merged; outcome (a) green | PR #1629 (`af2365a2`) |
| GATE-0 non-vacuity | `work/gate0-nonvacuity` | merged; G0 green | PR #1630 (`014a7768`) |
| P0 content semantic verifier | `work/p0-content-semantic` | implemented; rebased review/checks in progress | pending PR |
| I1 gate closure | `work/i1-gate-closure` | implemented; documentation review fixes complete | — |
| D1a tape lemmas + bridge structure | `work/d1a-tape-interface` | implemented; all local checks and reviews green | pending PR |
| D1b bridge ⇒ NP-witness | `work/d1b-bridge-witness` | blocked on P0 and **D1a** | — |

---

## 8. Stop/go summary

| Gate | Slice | Condition | Action if red |
|---|---|---|---|
| **F0** | FEAS-0 | **PASS (a):** at `treeCircuitWitnessCodec (thresholdPoly k)`, `contentAccepts_target_poly_treePoly` proves the polynomial bound from accepted complete words to `treeMCSPPrefixM codec n'`. It *yields* a bounded timeout in principle, of exponent `c · d` rather than `c`, via `PolyBoundedInTable.powAdd` (`ExtractedScheduleGrowth.lean:114`), whose polynomial `P N = (N ^ c + c) ^ d + d` bounds `M n' = M r` and — through `tableLen_le_treeMCSPPrefixM` (`PrefixParserConvention.lean:48`) and `witnessBits_le_treeMCSPPrefixM` (`TreeMCSPPrefixSemanticVerifier.lean:78`) applied **at `r := pr.2.n`** — also `tableLen r`, `codec.witnessBits r` and (via `r ≤ bitLength (M n')`) `thresholdPoly k r`, the quantities `ContentAccepts` actually uses. These component bounds come **directly** from `M r = M n'`, never by transferring an `n'`-side bound. Never stated codec-generically — generic (a)/(b) are false. It is **not** a verifier implementation (§1.0) | only outcome (d) was red; it did not occur |
| **F0b** | FEAS-0 | **PASS:** the proof runs on `r := pr.2.n`, uses only `M n_header = M r`, recovers the truth-table slice through `contentInput?_x_apply`, and cites no I1 output | a future consumer needing target equality or gamma canonicity must be re-derived via the convention-length equality |
| **G0** | GATE-0 | **PASS:** `contentAccepts_nonvacuous_treePoly` constructs a concrete `ContentAccepts`-accepted word at `treeCircuitWitnessCodec (thresholdPoly k)` for every `k, n` | the red action is no longer applicable; this pass establishes only non-vacuity, not a verifier or NP witness |
| **G1** | P0 | the `Bool`↔`Prop` headline is hypothesis-free | fix the `Bool` definition's failure branches, not the statement |
| **G2** | P0 | the three codec-path theorems carry the standard triple **or lighter** (same rule as G9 — a shorter list is not a defect); computability checked by instance provenance + one `#eval`, **not** by an axiom check | a fourth axiom, a `noncomputable` marker, or a `Classical.propDecidable` instance is a blocker; a *lighter* footprint is not |
| **G3** | I1 | injectivity stated only as `treeMCSPPrefixM_injective_of_monotone` / `_treePoly` | reject any generic-codec injectivity claim as **false**; do not strengthen `PrefixInput` to dodge it |
| **G4** | I1 | `decodeGamma?_consumed_eq_gammaLen` needs no premise beyond a successful decode | fix `readNatBE_lt_two_pow`, not the statement |
| **G4b** | I1 | `contentInput?_isSome_iff_of_header` leaves exactly premises #9–#11 open | a fourth open premise means a range lemma was missed; folding one away means the parser was mis-read |
| **G5** | D1a | `accepts_eq` uses the exact-step model, no halting/`∃ t ≤` variant | reject: the slice has changed the machine model |
| **G5b** | D1a | no D1a declaration mentions `contentSemanticAccepts` | not P0-independent: take the `acc` parameter or move the declaration to D1b |
| **G6** | D1b | the witness repackaging consumes `runTime_poly` verbatim, and the slice is opened on top of **both** P0 and D1a (§4.5, §5) — **and note advice-avoidance is unenforced** (§1.3 caveat 6) | under-specified bridge, or a D1b branched off bare `main`; do not claim advice-freedom without a formal clock premise |
| **G7** | all | ≤ 1500 LOC and ≤ 10 modules at PR time (§6.1) | split before review; never waived |
| **G8** | all | `./scripts/check.sh` and `./scripts/check_doc_honesty.sh` green | fix before review; a red doc guard is a blocking defect, not a formality |
| **G9** | all | axiom footprint is the standard triple or lighter | investigate any fourth axiom before merge |

---

## 9. Bottom line

* Input (2) is **frozen** at `ContentPrefixExtensionNPWitness` / `ContentAccepts`
  (`ContentPrefixExtension.lean:211`, `:152`). FEAS-0 outcome (a) is proved by
  `contentAccepts_target_poly_treePoly`: accepted complete words have polynomially bounded header
  convention length. This does not build the verifier TM or prove `L' ∈ NP` (§1.0).
* The length-gated `PrefixExtensionNPWitness` is retained as a compiled and audited compatibility
  surface and is dispreferred, rather than retired, for new verifier work; a new slice may target it
  only with the explicit technical or compatibility rationale required by §1.2.
* The donor manifest's central premise — "nothing on `main` is reusable, branch from `4a8ee0c9`" —
  is false. Twelve modules on `main` (CT-A/B/C, FEAS recovery/bound, GATE-0, plus the `#1626` model audit) and the pre-existing
  parser/codec foundation are
  the actual base, and every slice in §4 is dependency-closed on `main = 014a7768` at this
  slice-log revision.
* The donor TM stack is a **transcoder**, not a verifier: it never touches the header, the truth
  table, the size check, or `TM.accepts`, so completing it would not discharge `(★′)`. It is parked
  — but its witness-decoding machinery is a plausible component for a future verifier, so it is
  insufficient rather than useless (§3.4).
* Two claims from revision 2 are **corrected**: generic injectivity of
  `treeMCSPPrefixM codec` is **false** (specialize to monotone `witnessBits`, §4.3.1), and gamma
  canonicity is a **theorem** rather than a hypothesis, which makes the strict parser's length gate
  unconditionally vacuous and reduces the open residue to three explicit value tests (§4.3.2–4.3.3).
* The FEAS-0 route runs on **`r := pr.2.n`**, the target the narrow parser returns — not on the
  header value `n'`, which is what `ContentAccepts` never uses for its witness window, truth table or
  relation. `M n' = M r` comes from `parseTreeMCSPPrefixInput_length_convention`
  (`PrefixParserConvention.lean:1231`), so the route needs **no injectivity and no gamma
  canonicity** and is independent of I1 (§1.0, F0b). The merged
  `ContentParseFieldRecovery.lean` supplies the truth-table slice that
  `parseTreeMCSPPrefixInput_inversion` does not expose, and `ContentTargetSizeBound.lean` consumes
  it to prove the headline.
* **Outcome (a) alone is sufficient**, but its exponent is **not** the timeout: decode the header,
  compare `n'` against `bitLength (N ^ c + c)` without materialising `2 ^ n'`, reject on overflow,
  and on the surviving branch bound the parse window by `P N = (N ^ c + c) ^ d + d` — exponent `d`
  obtained from `polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly` (`WitnessGrowthReduction.lean:94`)
  plus `PolyBoundedInTable.powAdd` (`ExtractedScheduleGrowth.lean:114`), because `M n'` also carries
  the gamma, index and witness widths (§1.0). **The work itself is at `r := pr.2.n`, and is bounded
  directly, not by transfer from `n'`:** `ContentAccepts` reads its witness window and states its
  relation at `pr.2.n`, and `M n' = M r` yields neither `n' = r` nor
  `codec.witnessBits n' = codec.witnessBits r`, so use `tableLen r ≤ M r = M n'`
  (`tableLen_le_treeMCSPPrefixM`, `PrefixParserConvention.lean:48`) and
  `codec.witnessBits r ≤ M r = M n'` (`witnessBits_le_treeMCSPPrefixM`,
  `TreeMCSPPrefixSemanticVerifier.lean:78`), whence `r ≤ bitLength (M n') = O(log N)` and
  `thresholdPoly k r = polylog N`. Parse window, witness window, truth-table enumeration and
  certificate block then all fit in `2 · P N + N + 1` cells, so the single exponent `c · d` suffices;
  revision 5's second exponent `c · e` is withdrawn, having bounded `codec.witnessBits n'`, a
  quantity the verifier never reads. That is a machine-construction argument, not a theorem;
  the machine slices still have to build it. (b) is that timeout packaged as a proved `Bool` rule and
  is preferred when no harder. Refuting (a) needs a **family** `∀ c, ∃ (N, z, n')`, not one wide word.
* The machine model's `runTime` field is unrestricted
  (`RuntimeAdviceBarrier.lean:77` `lengthAdviceLanguage_in_repo_P`), and `ContentVerifierBridge`
  does **not** exclude a bridge that exploits it. Advice-avoidance is an unenforced review
  convention until a formal clock premise is added (§1.3 caveat 6, G6).
* FEAS-0 is implemented in one new 295-line module on top of the already merged field-recovery
  slice. GATE-0, P0, I1 and D1a are now unlocked; D1b still waits for P0 and D1a. Their projected
  budgets remain planning estimates, not completed work.
