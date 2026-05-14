# D6 budget reconciliation — gpt55

Slot: D6 budget reconciliation  
Handle: gpt55  
Branch: main  
Progress classification: Infrastructure / markdown-only route audit.  This report does not implement Lean, promote any provenance filter, edit guardrails, add trust roots, or claim a lower-bound endpoint.

## 1. Executive verdict

**local_only_not_magnification_ready.**

D3′-A should be retained as a correct local anti-collapse theorem for a deliberately tiny log-window fingerprint budget, but fp3b6 should **not** treat that budget as Atserias–Müller magnification-ready.  D5-tight changes the status of the route from "plausible Family A bridge candidate" to "local obstruction unless a substantially different budget is specified."  The mismatch is not a cosmetic constant-factor issue: the quantities visible in the Atserias–Müller theorem surfaces are polynomial, subpolynomial, or at least `r`-multiplied logarithmic footprints, while D3′-A is a hard logarithmic-window cliff.

The most defensible near-term interpretation is therefore:

```text
D3′-A = valid NOGO-000006-facing local anti-collapse witness
D3′-B now = no-go until a repaired budget target is written down
fp3b6 as AM route = not ready without reparameterisation
```

I am not selecting **route_probably_dead_for_AM** because a future seed pack could still define a different filter that charges sampled-oracle cost, matrix-description cost, or payload-independent witness structure.  But the current D3′-A budget itself should not be presented as a theorem-level Atserias–Müller budget.

## 2. What D5-tight changed

D3′-A proves non-separation under the budget

```text
m * k + ρ ≤ widthFn n
```

where `widthFn n = Nat.log2 (n + 1)`.  The proof idea is simple and sound for that local regime: if all rows together can query at most `m*k` payload-window coordinates and the payload window has at least `ρ` unqueried coordinates left, choose a far-NO point by flipping `ρ` unqueried payload bits.  Then the fingerprint sees exactly the same queried bits on the YES anchor and the far-NO point, so radius-1 separation fails.

D5-tight changed the interpretation by extracting the visible Atserias–Müller theorem-level parameters and showing that they do not naturally fit this inequality:

* If `m` is the full distinguisher output length `m_AM`, then `m_AM` is polynomial or linear in the relevant theorem statements, not logarithmic.
* If `k` is the output-bit fan-in / matrix weight `w_AM`, then `w_AM` is generally `n^ε`-scale, inverse-distance-scale, or logarithmically multiplied, not a harmless constant that can disappear inside `Nat.log2 (n+1)`.
* If `m` is reinterpreted as sampled coordinates `r`, the theorem-level formula construction still pays roughly `r*w_AM`, and the oracle/kernel input has length on the order of `10 r log m_AM`.
* D3′-A's `ρ` is a payload-window farness parameter, while AM farness is global Hamming distance from a sparse language and the sampled construction also has separate probability/slack constraints.

Thus D5-tight turns the D3′-A budget into a **local anti-collapse hypothesis** rather than a literature-verified magnification budget.  The hard question is not whether the D3′-A Lean theorem is useful; it is whether the exact `m*k + ρ ≤ log n` window can still exclude the NOGO-000006 hardwiring payload once the fingerprint is permitted to spend the larger footprint used by AM-style magnification.

## 3. Three possible parameter interpretations

### A. Full distinguisher footprint

Interpretation:

```text
m = m_AM
k = w_AM
budget ≈ m_AM * w_AM
```

**Does it fit `widthFn n`?**  No.  Under the natural full-distinguisher reading, `m_AM` is already at least linear or polynomial in the extracted theorem surfaces, and multiplying by `w_AM` only moves farther away from `O(log n)`.  This is the cleanest mismatch: a full AM distinguisher footprint cannot be compressed into the D3′-A log-window cliff.

**Can `widthFn` be changed without leaving the `InPpolyFormula` hardwiring regime?**  Not in the straightforward arbitrary-truth-table way.  The NOGO-000006 payload is placed in a window of width `q(n)` and represented by a truth-table formula of size about `2^{q(n)}`.  With `q(n)=O(log n)`, this stays polynomial.  If `q(n)` is increased to match `m_AM*w_AM`, then `2^{q(n)}` becomes superpolynomial for the AM-scale footprints unless the footprint itself is still `O(log n)`.  That would no longer be the same `InPpolyFormula` hardwiring witness.

**Does it still address NOGO-000006?**  Only in the weak sense that it says a log-window payload can defeat fingerprints that inspect no more than the log window minus `ρ`.  It does **not** address the stronger challenge posed by AM-style full distinguishers: if the fingerprint footprint is much larger than the payload width, it can simply query the entire log-width payload window.  Then the row-union hiding argument collapses.

### B. Sampled fingerprint footprint

Interpretation:

```text
m = r
k = w_AM
budget ≈ r * w_AM
```

**Does it fit `widthFn n`?**  Not in the visible theorem-level regimes reported by D5-tight.  Sampling reduces `m_AM` to `r`, but the construction still samples enough coordinates to make the collision/separation argument work, and each sampled output coordinate depends on up to `w_AM` input bits.  The product `r*w_AM` remains polynomial or subpolynomial above `O(log n)` in the main regimes.

**Can `widthFn` be changed without leaving the `InPpolyFormula` hardwiring regime?**  Only if the sampled footprint can itself be bounded by `O(log n)` or if the payload is no longer represented by an arbitrary truth-table formula.  A payload width `q(n)≈r*w_AM` makes the hardwired truth table size `2^{r*w_AM}`, which is not polynomial in the theorem-level regimes D5-tight extracted.  Conversely, keeping `q(n)=O(log n)` means the sampled fingerprint likely has enough budget to inspect all payload bits, so the D3′-A anti-collapse mechanism no longer fires.

**Does it still address NOGO-000006?**  Partially and only locally.  It addresses the specific failure mode "support-cardinality alone does not imply a sparse fingerprint witness" when the sampled fingerprint is forced to live inside the log-width window.  It does not yet address the AM-like sampled setting, because an `r*w_AM` footprint larger than `q(n)=O(log n)` can defeat the hiding proof by reading the complete payload window.

### C. Oracle/kernel input footprint

Interpretation:

```text
budget ≈ 10 r log m_AM
```

**Does it fit `widthFn n`?**  No for fixed positive sampling growth.  Even though `log m_AM=O(log n)` when `m_AM` is polynomial, the factor `r` remains.  The visible AM construction pays for `r` sampled coordinates, so `10 r log m_AM` is a repeated-coordinate oracle/kernel footprint, not a single log-width payload.

**Can `widthFn` be changed without leaving the `InPpolyFormula` hardwiring regime?**  Not by simply setting `widthFn n := 10 r log m_AM`.  The truth-table formula for an arbitrary payload over that many bits would have size `2^{10 r log m_AM}=m_AM^{10r}`.  This is polynomial only if `r=O(1)` under polynomial `m_AM`, or more generally only under a much tighter regime than the AM theorem-level uses identified by D5-tight.

**Does it still address NOGO-000006?**  It addresses a different object.  NOGO-000006 is about arbitrary all-essential log-width truth-table hardwiring that remains polynomial because the window is logarithmic.  The oracle/kernel interpretation suggests a route that charges the construction's actual input description length.  That may be the right cost model for a future provenance filter, but it does not preserve the D3′-A proof unless the filter still cannot inspect all payload bits.  If the kernel input footprint exceeds the log-width payload, the current anti-collapse proof has no untouched payload coordinates to flip.

## 4. Hardwiring-window constraint

NOGO-000006 is load-bearing precisely because the hardwired payload has **logarithmic width**.  An arbitrary Boolean function on `q` payload bits can be represented by a truth-table formula with exponential dependence on `q`.  When `q=widthFn n=Nat.log2(n+1)`, this exponential is polynomial in `n`, so the arbitrary all-essential payload remains inside the polynomial-size formula-hardwiring regime.

This creates the central budget window:

```text
payload width q(n) = O(log n)
truth-table formula size ≈ 2^{q(n)} = poly(n)
```

If a proposed fingerprint budget exceeds this log-width payload, then yes, in principle a fingerprint can simply inspect all payload bits unless another restriction forbids it.  D3′-A's no-separation proof depends on the opposite condition: the row-support union must leave at least `ρ` payload coordinates unqueried.  Once the budget is large enough to cover every payload coordinate, the proof cannot manufacture a far-NO point that agrees with the YES anchor on all queried coordinates.

This is the key reconciliation point.  The same logarithmic window that keeps arbitrary truth-table hardwiring polynomial also makes the payload small enough for larger AM-style fingerprints to read entirely.  Enlarging the payload to keep hidden coordinates available breaks polynomial truth-table hardwiring; keeping the payload logarithmic makes the current hiding argument too weak for AM-scale budgets.

## 5. Salvage options

### A. Keep D3′-A as local anti-collapse only

This is the safest interpretation.  D3′-A remains valuable because it cleanly refutes the naive implication

```text
all-essential log-width payload + small support cardinality
  ⇒ sparse fingerprint separation witness
```

under a tight log-window budget.  It is relevant to NOGO-000006 because it shows that arbitrary log-width hardwiring does not automatically satisfy a semantic fingerprint-separation predicate.  But it should be reported as **local-only**, not as AM magnification progress.

### B. Change payload width from `log n` to `q(n)`

This is tempting because the D3′-A proof would work again if `q(n)` were made larger than the fingerprint footprint plus `ρ`:

```text
m*k + ρ ≤ q(n)
```

The obstruction is formula size.  For arbitrary truth-table payloads, the hardwired formula has size exponential in `q(n)`.  If `q(n)` tracks `m_AM*w_AM`, `r*w_AM`, or `10r log m_AM` in the visible AM regimes, then `2^{q(n)}` is generally not polynomial.  The resulting witness would no longer be the same polynomial-size hardwiring obstruction formalized by NOGO-000006.

A larger `q(n)` might be usable for restricted payload classes with succinct formulas, but then the argument would stop being an arbitrary all-essential truth-table hardwiring attack.  That would require a new seed pack and a new obstruction statement.

### C. Change matrix filter to charge matrix description/cost, not just sparsity

This is a plausible repair direction.  Instead of forcing `m*k` to fit inside the payload window, a future filter could charge:

* matrix construction cost;
* bit-complexity of the matrix description;
* sampled-coordinate description length;
* fingerprint formula cost;
* dependence on the payload-specific hardwiring map.

This would move the route away from the simple row-union hiding lemma and toward a provenance predicate that asks whether the matrix witness is itself cheaply and honestly obtained.  It may also be better aligned with AM's explicitness and local-oracle accounting.  However, it is not a D3′-B Lean task yet; the budget and theorem statement would need to be redesigned first.

### D. Require matrix witness to be independent of payload-specific hardwiring

This is another plausible repair.  NOGO-000006 hardwiring can choose arbitrary all-essential payloads.  A filter might require that the distinguisher matrix be obtained independently of the payload's truth table or uniformly from the ambient sparse-language structure, rather than tailored to the payload bits.  If the matrix cannot adapt to the hardwired payload, then even a larger budget might fail to certify all arbitrary payloads.

The challenge is formalizing "independent of payload-specific hardwiring" without falling back into syntactic-only or support-cardinality-only traps.  NOGO-000007 warns that support profiles alone are insufficient, and NOGO-000008/NOGO-000009 warn that displayed-syntax exclusions and simple normalisation patches are fragile.  This option therefore needs a semantic/provenance definition, not a quick local Lean extension.

### E. Move to a different route, e.g. almost-natural / Family B

If the goal is a promotable provenance filter rather than preserving Family A, the almost-natural / Family B route may now be higher value.  D5-tight reveals that the clean row-union anti-collapse argument is too small for AM-scale magnification.  A route that explicitly studies representation sensitivity, largeness/constructivity tension, and semantic dependence may better address the NOGO-000006 through NOGO-000009 chain.

This is not a proof that Family A is impossible.  It is a sequencing recommendation: do not spend D3′-B Lean effort before the budget has been repaired, and consider opening the next seed pack on a route whose central predicate is designed around the hardwiring-window constraint from the start.

## 6. Recommended next seed pack

**fp3b7_almost_natural_provenance.**

Rationale:

1. D3′-A can be archived as local-only without being discarded.
2. D5-tight makes a direct D3′-B continuation premature.
3. A pure `fp3b6_budget_repair` pack is possible, but the available repair options are not merely parameter substitutions; they require a different semantic account of matrix provenance, payload independence, or description cost.
4. The NOGO-000008 and NOGO-000009 context already points away from syntactic filters and toward predicates that must be semantic enough to survive rewrite/normalisation attacks but not so natural that they trigger the familiar barrier concerns.

If the operator wants to preserve Family A specifically, the fallback next pack should be **fp3b6_budget_repair**, with an explicit deliverable: choose one target budget among `r*w_AM`, `10r log m_AM`, matrix-description cost, or payload-independent witness cost, and prove on paper that it still blocks NOGO-000006 before any Lean work.

## 7. Explicit go/no-go for D3′-B

**NO — D3′-B Lean dispatch should not proceed now.**

D3′-B was supposed to strengthen the anti-collapse story beyond D3′-A, but D5-tight exposed that the current load-bearing budget is not compatible with the visible AM theorem-level parameters.  Dispatching D3′-B now would risk formalizing a stronger theorem inside the wrong regime: technically correct, but still local-only and not magnification-ready.

D3′-B should wait until a repaired budget statement specifies at least:

* what `m` denotes: full output length, sampled length, oracle/kernel input count, or something else;
* what `k` denotes: row fan-in only, column support too, formula cost, or description cost;
* how `ρ` relates to AM farness or to payload-window farness;
* whether the payload remains arbitrary truth-table hardwiring of logarithmic width;
* why a fingerprint with the repaired budget cannot simply inspect all payload bits;
* how the candidate avoids NOGO-000007 support-cardinality collapse and the NOGO-000008/NOGO-000009 syntactic-rewrite/normalisation traps.

Until those points are fixed in markdown, D3′-B Lean work is premature.

## 8. Scope and checks

Scope discipline for this D6 report:

* Markdown-only report added under the seed pack `reports/` directory.
* No Lean code written.
* No JSONL edits.
* No spec, known-guards, trust-root, registry, or promotion edits.
* No lower-bound endpoint claim.

Command required by the slot:

```text
./scripts/check.sh
```

The command was run after writing this report; see the final worker summary for the exact result.
