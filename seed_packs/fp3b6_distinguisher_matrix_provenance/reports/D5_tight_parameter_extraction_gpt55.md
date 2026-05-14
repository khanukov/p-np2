# D5-tight — theorem-level parameter extraction for D3′-A budget regime

Slot: D5-tight  
Handle: gpt55  
Branch: main  
Progress classification: Infrastructure / parameter-audit report only. This is not a lower-bound theorem, not a `ProvenanceFilter_v1` promotion, and not P-vs-NP mainline progress.

## 1. Executive verdict

**D3prime_budget_regime_too_weak.**

Atserias–Müller-style distinguisher magnification does **not** appear to operate in the D3′-A budget regime

```text
m * k + ρ ≤ widthFn n
```

when the D3′-A symbols are read in the natural fp3b6 way: `m` is the fingerprint output length / number of fingerprint rows, `k` bounds both row and column sparsity, `ρ` is the payload-window farness parameter, and `widthFn n = Nat.log2 (n + 1)`.

The paper's theorem-level parameters instead have:

* full distinguisher output length `m_AM` polynomial in `n` (`m_AM ≤ n^7` in Theorem 1 / Theorem `dist`, and `m_AM ≤ n^11` in the strongly explicit theorem), not logarithmic;
* output-bit fan-in / matrix column weight `w_AM` of order `n^ε` (or `8 log(2n) n^ε` in the strongly explicit application to `n^{-ε}` approximation), not generally constant or logarithmic;
* a **sampled fingerprint length** `r` tied to the log-sparsity exponent `q(n)` (`r = 17⌈n^γ⌉` in the main proof; `r = 5q(n)+10` in the local corollary; `r = ⌈16q(n)+32⌉` in the uniform MCSP proof), but the local formulas use `r` sampled coordinates, each of fan-in `w_AM`, plus an oracle input of length `10r log m_AM`.

Thus the theorem-level products visible in the paper are closer to `m_AM*w_AM`, `r*w_AM`, or `10r log(m_AM)` depending on which fp3b6 parameter one intends to model. None is verified to be `≤ O(log n)`, and the main magnification regimes explicitly permit polynomial or subpolynomial quantities much larger than `Nat.log2 (n+1)`.

## 2. D3′-A budget restatement

D3′-A uses the exact budget condition:

```text
m * k + ρ ≤ widthFn n
```

where, for the fp3b6 audit skeleton:

* `m` = fingerprint rows / output length;
* `k` = row/column sparsity bound;
* `ρ` = payload-window farness;
* `widthFn n = Nat.log2 (n + 1)`.

This condition is a **log-window cliff**: the total fingerprint incidence budget `m*k`, plus the payload-window farness parameter `ρ`, must fit inside the same logarithmic variable window used by the arbitrary all-essential truth-table payload obstruction.

For D3′-A itself this is a coherent local anti-collapse hypothesis: if the sparse fingerprint relation can inspect only a total budget no larger than the log-width payload window, then it cannot automatically certify radius-1 separation for the constructed payload geometry. The question in this D5-tight report is narrower: whether the Atserias–Müller magnification route has theorem-level constants that naturally fall into that same budget.

## 3. Atserias–Müller parameter extraction

Source inspected: Albert Atserias and Moritz Müller, *Simple general magnification of circuit lower bounds*, arXiv:2503.24061v1, TeX source fetched from arXiv on 2026-05-14.

### 3.1 Distinguisher definition and matrix orientation — [verified]

Section 1 / Definition immediately before Theorem 1 defines an `(n,m,ε,δ)`-distinguisher as a binary `n × m` matrix `D` such that, for all `x,y ∈ {0,1}^n`, if `d_H(x,y) ≥ ε n`, then `d_H(xD,yD) ≥ δ m`. The same definition says the **weight** of `D` is the maximum Hamming weight of a **column** of `D`.

Parameter consequence:

* AM input length: `n`.
* AM output length: `m` columns of the `n × m` matrix, i.e. length of `xD`.
* AM sparsity theorem controls output-coordinate fan-in: each output bit `(xD)_j` depends on at most `weight(D)` input bits.
* This is directly analogous to fp3b6 row support if fp3b6 stores the matrix transposed as `m` fingerprint rows by `n` input columns.
* It is **not** a theorem-level two-sided row-and-column sparsity bound in the fp3b6 `SparseDistinguisherMatrix` sense. The AM definition controls maximum column weight of the `n × m` matrix only.

### 3.2 Basic non-strongly-explicit distinguisher theorem — [verified]

Theorem 1 in the introduction, repeated as Theorem `dist` in Section 2, states that for `0 < ε ≤ 1` there is a polynomial-time algorithm which, given `n`, computes an `(n,m,n^{-ε},1/8)`-distinguisher with `m ≤ n^7` and weight at most `⌈2n^ε⌉`.

Parameter consequence:

* Distance/farness radius in the AM approximate problem is `n^{-ε} * n = n^{1-ε}` Hamming distance from `Q`, not radius `1`.
* Output length is polynomial: `m_AM ≤ n^7`.
* Output-bit fan-in is polynomially growing for fixed `ε > 0`: `w_AM ≤ ⌈2n^ε⌉`.
* The full-product analogue `m_AM * w_AM` is at most `O(n^{7+ε})`, not `O(log n)`.
* If fp3b6 `m*k` is intended to model the full distinguisher footprint, the D3′-A budget is far below this theorem-level regime.

### 3.3 Proposition with linear output length and inverse-distance weight — [verified]

Proposition `dist` in Section 2 says there are constants `c,d` such that, for sufficiently large `n` and every real `ε ≤ 1/(c log n)`, there exists an `(n,dn,1/5,ε)`-distinguisher of weight at most `1/ε`.

Parameter consequence:

* This is the most output-length-efficient theorem-level statement found: `m_AM = d n`, not `O(log n)`.
* The weight is `≤ 1/ε`; for `ε = n^{-α}` this becomes `n^α`.
* Even in the tiny-distance case `ε ≤ 1/(c log n)`, output length is linear in `n`, so full `m_AM * w_AM` is at least linear-scale unless `ε` is constant and even then `m_AM*w_AM = Θ(n)`.
* This does not support `m*k ≤ Nat.log2(n+1)`.

### 3.4 Strongly explicit distinguisher theorem — [verified]

Theorem `strdist` in Section 2.3 states that for every large enough `n` and rational `0 < ε < 1`, there exists `m ≤ n^11` and an `(n,m,1/16,ε)`-distinguisher of weight `≤ 8 log(2n)/ε`, and the entries are computable strongly explicitly in polynomial time from `n, ε, i, j`.

Parameter consequence:

* In the uniform MCSP application, the theorem is invoked with `ε` replaced by `n^{-ε}`. The resulting weight is `≤ 8 log(2n) n^ε` and `m(n) ≤ n^11`.
* This strengthens explicitness but worsens the visible polynomial output-length bound relative to Theorem 1.
* Again, neither `m_AM` nor `m_AM*w_AM` is logarithmic.

### 3.5 Kernel / sampled-fingerprint construction — [verified]

Definition `K(Q,D,r)` in Section 3 defines, for `u = (u_1,…,u_r) ∈ [m(n)]^r`, a string containing `n`, the sampled coordinates `u`, and bits `b_j = (xD)_{u_j}`. The paper notes that this encoded kernel string has length at most `10 r(n) log m(n)`.

Lemma `kernel` states that if `x ∈ Q`, the sampled kernel is always in `K`; if `x` is a NO instance of `ε-Q`, then the collision probability is at most `2^q(1-δ)^r`, where `Q` is `2^{q(n)}`-sparse.

Lemma `localform` then gives formulas of shape

```text
AND_b ∘ K_{10r log m} ∘ XOR_w
```

or probabilistic formulas of shape

```text
K_{10r log m} ∘ XOR_w
```

under the conditions `b r δ - b q ≥ n` and `r δ - q ≥ 2`, respectively. Its proof explicitly uses that each sampled bit `(xD)_{u_j}` is an XOR of at most `w` input bits.

Parameter consequence:

* The **sampled** fingerprint length is `r`, not the full `m_AM`.
* The oracle fan-in / kernel encoding length is `10 r log m_AM`.
* The total number of input-wire incidences feeding the sampled XOR layer is morally `r*w_AM`, not `m_AM*w_AM`.
* The success condition requires `r` proportional to the log-sparsity parameter `q(n)` divided by constant distance `δ`; in the paper's main settings `q(n)` is `n^γ` or `n^{o(1)}`, not necessarily `O(log n)`.

### 3.6 Main magnification theorem parameter choices — [verified]

The main theorem (`thm:main`) states: for every `c`, positive reals `δ, ε`, `γ < δ/c`, and every `2^{n^γ}`-sparse `Q ∈ NP`, lower bounds against `n^{-ε}-Q` at thresholds `FML[n^{1+2ε+δ}]` or `PFML[n^{2ε+δ}]` imply `NP ⊄ FML[n^c]`.

In the proof it sets:

```text
q(n) := n^γ
δ(n) := 1/8
w(n) := ceil(2n^ε)
r(n) := 17 ceil(n^γ)
```

and uses the distinguisher with `m ≤ n^7`. The deterministic case yields formulas of form

```text
AND_{ceil(n^{1-γ})} ∘ K_{170 ceil(n^γ) log m} ∘ XOR_{ceil(2n^ε)}
```

and the probabilistic case uses

```text
K_{c n^γ log n} ∘ XOR_{ceil(2n^ε)}
```

for some constant `c`.

Parameter consequence:

* The sampled coordinate count is `r = Θ(n^γ)`.
* The sampled XOR fan-in is `w = Θ(n^ε)`.
* The sampled incidence product is `r*w = Θ(n^{γ+ε})`.
* The oracle input length is `Θ(n^γ log n)` because `m ≤ n^7`.
* These are much larger than `Nat.log2(n+1)` for fixed positive `γ` or `ε`.

### 3.7 Uniform MCSP / strongly explicit application — [verified]

In Section 4.1, Theorem `parityP` invokes a strongly explicit `(n,m(n),1/16,n^{-ε})`-distinguisher with weight `≤ 8 log(2n)n^ε` and `m(n) ≤ n^11`. It sets `q(n) := n^{2γ}` and `r̃(n) := ⌈16q(n)+32⌉`, producing probabilistic formulas of form

```text
K_{O(n^{2γ} log n)} ∘ XOR_{O(n^ε log n)}
```

on input length `n = 2^ℓ`.

Parameter consequence:

* Strong explicitness again uses `r = Θ(n^{2γ})` sampled coordinates and XOR fan-in `Θ(n^ε log n)`.
* The sampled incidence product is `Θ(n^{2γ+ε} log n)`.
* This is not compatible with a log-window budget unless the exponents are collapsed to nonstandard `o(1)`/zero regimes not stated by the theorem.

### 3.8 Sufficiently sparse NP problem parameters — [verified]

The introductory main theorem (`intromain`) works for `2^{n^{o(1)}}`-sparse `Q ∈ NP`. The theorem-level finite-exponent version (`main`) works for `2^{n^γ}`-sparse `Q ∈ NP` with `γ < δ/c`. The local corollary sets `r(n) := 5q(n)+10` for `Q` that is `2^{q(n)}`-sparse and gives oracle fan-in `10r(n) log m`.

Parameter consequence:

* `r` is controlled by the logarithm of the sparse set size, not by `log n` unless the sparse set has only polynomially many strings per length (`q(n)=O(log n)`).
* The main magnification theorem intentionally allows `q(n)=n^γ` and `q(n)=n^{o(1)}`.
* Therefore the paper's sparse-NP parameters do not verify `r`, `r*w`, `10r log m`, or `m*w` as `O(log n)`.

### 3.9 Row support / column support in fp3b6 sense — [verified for one side, unverified for the other]

AM controls the maximum Hamming weight of each column of its `n × m` matrix. Under the transposed fp3b6 convention, that gives a bound on each fingerprint row's input support. I found no theorem-level AM statement bounding, for every original input coordinate, how many output coordinates depend on it. Such a bound might hold for special constructions or be derivable from total weight, but it is not part of the extracted theorem surfaces above.

Parameter consequence:

* fp3b6 row support analogue: **verified** as AM weight `w` after transposition.
* fp3b6 column support analogue: **unverified** at theorem level.
* fp3b6's symmetric `k` row/column sparsity is therefore stronger/different than what AM's definition explicitly advertises.

## 4. Compatibility table

| D3′-A parameter | Atserias–Müller analogue | Match? | Confidence | Notes |
| --- | --- | --- | --- | --- |
| `n` | AM input length `n` for strings in `{0,1}^n` | Partial | High | Same ambient input length, but AM also has encoded kernel strings of length `≤ 10r log m` and MCSP uses `n=2^ℓ` in one application. |
| `widthFn n` | No direct AM theorem parameter; closest candidates are `log m`, `10r log m`, or log-sparsity `q(n)` | No | High | D3′-A fixes `Nat.log2(n+1)`. AM's `log m` is `O(log n)` only because `m` is polynomial, but the kernel fan-in is multiplied by `r`. |
| `m` | Full output length `m_AM` of `xD`, or possibly sampled length `r` if D3′-A is reinterpreted | Mismatched | High | Full `m_AM ≤ n^7`/`n^11`; sampled `r=Θ(q)`. Neither is generally `≤ O(log n)`. |
| `k` | AM weight `w_AM`, after transposing matrix orientation | Partial | High | AM weight bounds output-bit fan-in. Symmetric row/column support `≤ k` is not verified. |
| `m*k` | Full footprint `m_AM*w_AM`, or sampled footprint `r*w_AM` | No | High | Full footprint is polynomial. Sampled footprint in main theorem is `Θ(n^{γ+ε})`; uniform MCSP gives `Θ(n^{2γ+ε} log n)`. |
| `ρ` | AM farness/distance parameter `ε(n)n`, or possibly log-sparsity/sample slack in `rδ-q≥2` | Mismatched | Medium | D3′-A `ρ` is payload-window farness. AM uses relative Hamming distance from `Q` plus sampling repetitions `r`; no direct payload-window parameter was verified. |
| separation radius `1` | AM output separation `δ m` for full fingerprints; sampled collision probability after `r` random coordinates | Partial / No | High | AM does not rely on radius-1 separation in full fingerprint space. It gets constant relative output distance, then samples enough coordinates. |
| row/column sparsity | AM column weight of `n × m` matrix; no extracted bound on all row weights | Partial | High | One-sided sparsity is verified; symmetric `k` is unverified. |
| YES/far-NO relation | AM promise `ε-Q`: YES is `x∈Q`; NO is distance at least `ε(n)n` from every `y∈Q` | Partial | High | Same broad YES/far-NO shape, but AM farness is global Hamming distance from a sparse language, not a log-window payload shell. |

## 5. Critical question

**Does an Atserias–Müller-style distinguisher matrix route plausibly operate in a regime where**

```text
m * k + ρ ≤ widthFn n
```

**or does it require larger `m*k`?**

It appears to require larger `m*k`, unless the fp3b6 symbols are substantially reinterpreted.

There are three possible readings:

1. **Full-distinguisher reading:** `m` is AM's full output length and `k` is AM's output-bit fan-in/weight. Then Theorem 1 gives `m ≤ n^7` and `k ≤ 2n^ε`; strongly explicit use gives `m ≤ n^11` and `k ≤ 8 log(2n)n^ε`. This is plainly not `≤ Nat.log2(n+1)`.
2. **Sampled-fingerprint reading:** `m` is AM's sampled coordinate count `r` rather than full output length. Then the main proof uses `r=17⌈n^γ⌉` and `k=⌈2n^ε⌉`, so `r*k=Θ(n^{γ+ε})`; the uniform MCSP proof uses `r=Θ(n^{2γ})` and `k=Θ(n^ε log n)`. This is also not `≤ O(log n)` in the theorem-level regimes.
3. **Oracle-input reading:** `m*k` is not the right AM quantity; perhaps the relevant local-oracle fan-in is `10r log m_AM`. This is `Θ(n^γ log n)` in the main proof and `Θ(n^{2γ} log n)` in the uniform MCSP proof. Again, this is not `≤ O(log n)` for fixed positive `γ`.

Therefore D3′-A remains useful as a **local anti-collapse theorem**: it honestly shows that a very tight log-window sparse-fingerprint budget does not automatically follow from an all-essential log-width payload. But it is **not magnification-ready as stated** for the Atserias–Müller theorem surfaces checked here. The budget cliff is too stringent relative to the paper's actual sampled-distinguisher and formula-construction parameters.

## 6. Consequence for fp3b6

**revise_D3prime_budget.**

Recommended next step: do not treat D3′-A's current budget as literature-verified. Before D3′-B Lean work, add a markdown design-tightening pass that decides which AM quantity fp3b6 wants to model:

* full output length `m_AM` and weight `w_AM`;
* sampled fingerprint length `r` and weight `w_AM`;
* local-oracle fan-in `10r log m_AM`;
* or a deliberately separate log-window anti-collapse theorem with no claim of AM magnification readiness.

If the aim is AM compatibility, D3′-B should probably use a budget shaped like `r*w + ρ`, `10r log m + ρ`, or a multi-parameter condition involving `q(n), r(n), w(n), δ(n)`, not `m*k + ρ ≤ Nat.log2(n+1)`.

## 7. What remains deliberately unverified

* I did not verify the full AM proofs line-by-line; this report extracts theorem-level and section-level parameter statements only.
* I did not verify whether the concrete AM constructions imply any additional per-input-coordinate output sparsity bound after transposition. The report marks fp3b6 column support as unverified.
* I did not verify whether a special ultra-sparse subcase `q(n)=O(log n)` plus a nonstandard approximation radius could force `r*w=O(log n)`. This is not the main theorem-level regime used for magnification.
* I did not verify version drift beyond the arXiv source fetched as arXiv:2503.24061v1 on 2026-05-14.
* I did not inspect all constants in Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam ITCS 2020, Oliveira–Pich–Santhanam ToC 2021, Chen–Jin–Williams FOCS 2019, or Cheraghchi–Hirahara–Myrisiotis–Yoshida STACS 2021, because the required D5-tight question is specifically the AM theorem-level budget caveat.
* I did not promote `ProvenanceFilter_v1`, add any `SourceTheorem`, add any `gap_from`, edit JSONL/spec/trust roots, or make any endpoint/P≠NP claim.

## 8. References

* Albert Atserias and Moritz Müller, *Simple general magnification of circuit lower bounds*, arXiv:2503.24061v1, 2025. Verified from arXiv TeX source fetched on 2026-05-14.
