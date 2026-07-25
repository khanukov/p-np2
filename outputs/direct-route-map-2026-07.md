# The direct route: what a non-workaround attack on `P ≠ NP` has to look like

Author: automated research session, 2026-07-25.
Companion module: `pnp4/Pnp4/Frontier/DirectRoute/SimulationCalculus.lean`.

**Bottom line up front.** No new separation is proved here, and no path to
`P ≠ NP` is claimed to work. What is established is a kernel-checked structural
theorem about the *entire family* of direct attacks: with the published toolkit,
the assumption `P = NP` enters every argument **multiplicatively**, and no fixed
gain — however large — can ever beat an unbounded multiplier. That single fact
explains every stall in the direct literature, and it names precisely the
property a genuinely new tool must have.

---

## 1. What "direct" forces on us

A direct attack means: assume `P = NP`, compose theorems, contradict a hierarchy
theorem. This is *indirect diagonalization*, and it is not a fringe technique —
it is the only method that has ever unconditionally separated determinism from
nondeterminism: Paul–Pippenger–Szemerédi–Trotter (1983) proved
`NTIME[n] ≠ TIME[n]` for multitape Turing machines.

Any such attack must be non-relativizing, because hierarchy theorems and plain
diagonalization relativize. There are exactly **two** non-relativizing resources
in the literature:

**R1 — local checkability.** A time-`t` computation is a locally constrained
tableau (Cook–Levin). This is what makes `SAT` complete, and it is exactly what
oracle access destroys, since a query is a non-local operation.

**R2 — space-efficient simulation of time.**
- Hopcroft–Paul–Valiant 1975: `TIME[t] ⊆ SPACE[t / log t]`.
- Dymond–Tompa 1985: `TIME[t] ⊆ ATIME[t / log t]`.
- PPST 1983 / Tretkoff: `TIME[t] ⊆ Σ₂TIME[o(t)]`.
- **R. Williams, STOC 2025 (best paper): `TIME[t] ⊆ SPACE[√(t log t)]`.**

Arithmetization is the third candidate non-relativizing tool, but it algebrizes
(Aaronson–Wigderson), so it is excluded by construction.

Note what is new in the list: every pre-2025 gain is a **logarithmic** factor.
Williams' is the first **polynomial** gain — and it lands in `SPACE`.

---

## 2. The calculus, and the three theorems

`SimulationCalculus.lean` makes the family a formal object. Resources are
`(class, exponent)` pairs; arrows are the published simulations plus the
consequences of `SAT ∈ DTIME[n^c]`:

```text
dtime α  → ntime α                      trivial
ntime α  → sigma 1 α                    trivial
sigma j α → dtime (c^j · α)             P = NP collapses PH; each level costs c
dtime α  → dspace (α/2)                 Williams 2025
dtime α  → dspace α                     Hopcroft–Paul–Valiant
ntime α  → dspace α                     trivial
dtime α  → sigma k ((1-δ)·α)            the speedup arrow (δ = 0 published)
padding, inside each class
```

A refutation means deriving `dtime α → dtime β` with `β < α`.

### Theorem 1 — space is a sink (`dspace_sink`)

Once a derivation reaches `dspace`, every later resource is `dspace`.

This is the formal reason the *only polynomial gain in the toolkit cannot be
used*. Williams halves the exponent, but into a class from which no arrow
returns. A contradiction has to be with a time hierarchy, and space never gets
back to time — Savitch, alternation-trading, and `SPACE[s] ⊆ DTIME[2^{O(s)}]`
all either stay in space or cost an exponential.

Williams himself flags the neighbouring question at the end of his paper: his
simulation *relativizes with respect to length-restricted oracles*, and he asks
whether that is a barrier to pushing it to `P ≠ PSPACE`.

### Theorem 2 — the exact threshold (`exponent_monotone`, `contradiction_of_below_threshold`)

Assign potential `α` to `dtime α` and `ntime α`, and `c^j · α` to
`Σ_j TIME[n^α]` — the cost of collapsing `j` alternations under the assumption.
Then:

* if `1 ≤ (1-δ)·c^k`, **every** derivation between time classes is
  non-decreasing in the exponent, so no contradiction exists;
* if `(1-δ)·c^k < 1`, the contradiction is derivable in two steps (speed up,
  then collapse).

So `(1-δ)·c^k` is not an artefact of the potential function; it is the exact
dividing line.

### Theorem 3 — a fixed gain is never enough (`fixed_gain_insufficient`)

> For every alternation depth `k ≥ 1` and every fixed gain `δ < 1` there is an
> assumption exponent `c ≥ 1` at which the threshold holds — and therefore at
> which the calculus derives nothing at all.

`P = NP` supplies only *some* polynomial `c`; a proof must refute the assumption
for **all** `c`. So no speedup arrow with a fixed gain can close the loop, no
matter how large the gain. Even a hypothetical
`DTIME[t] ⊆ Σ₂TIME[t^{0.01}]` would fail.

---

## 3. What this explains

The calculus reproduces the literature exactly.

* **Why PPST works and stops.** PPST assumes `NTIME[n] = TIME[n]`, i.e. `c = 1`.
  At `c = 1` even a logarithmic gain closes the loop, because there is no
  polynomial slowdown to overcome. At `c > 1` the log gain is swamped
  immediately. This is precisely why `NTIME[n] ≠ TIME[n]` has been known since
  1983 while `NTIME[n^2] ≠ TIME[n^2]` is open.
* **Why time-space tradeoffs cap out around `n^{1.8}`.** They assume the
  algorithm is *simultaneously* space-bounded. That extra assumption bounds `c`,
  which puts the argument in the narrow window where the threshold is violated.
  Take the space assumption away and `c` is unbounded again.
* **Why Williams 2025 did not immediately yield new separations against `NP`.**
  Its gain is polynomial — the first ever — but it lands in the sink.

---

## 4. So what would a genuinely new path be?

Theorem 3 contrapositively: **the new tool must have a gain that grows with
`c`, or must use the assumption additively rather than multiplicatively.**

Indirect diagonalization is multiplicative *by construction*: the assumed
algorithm is applied to the whole computation, so its exponent multiplies once
per cycle. That is not a fixable detail; it is what the technique is.

There is exactly one known additive-cost template:

> **The algorithmic method.** The assumed/constructed algorithm is invoked
> **once**, inside a single nondeterministic guess-and-check, rather than as a
> per-step simulation. Its cost then enters the exponent additively.

That is the structure of Williams' `NEXP ⊄ ACC⁰`, and it is the only technique
that has broken through where indirect diagonalization stalled. The formal no-go
in `SimulationCalculus.lean` does **not** cover it, because the algorithmic
method is not a composition of simulation arrows.

So the honest answer to "what is the new direct path" is a precise research
directive rather than a construction:

> Build an **additive-cost** direct argument: a device that consumes the
> hypothetical polynomial-time `SAT` algorithm exactly once, inside a single
> guess, and derives a contradiction with a hierarchy theorem — rather than a
> chain of simulations each of which pays the unknown exponent `c` again.

Two concrete sub-questions that follow, both open and both checkable:

1. **Can Williams' polynomial gain be redirected out of the sink?** Not
   `SPACE`, but a bounded-alternation class: is there
   `TIME[t] ⊆ Σ_k TIME[t^{1-δ}]` for constants `k, δ > 0`? By Theorem 3 this
   alone would still not suffice, but it is the missing polynomial-gain arrow
   and everything else in the area is built from such arrows.
2. **Is there an additive-cost analogue of the Cook–Mertz machinery?** Catalytic
   computation is precisely about *reusing* a resource rather than paying for it
   repeatedly. That is an additive-flavoured idea in a field where every other
   tool is multiplicative, and it is one year old.

---

## 5. Honest limitations

1. **This is a no-go for a named toolkit, not for all proofs.** The calculus
   contains the arrows listed in §2. A technique outside it — the algorithmic
   method, or something not yet invented — is untouched.
2. **Exponent-level abstraction.** The calculus works with polynomial exponents,
   so logarithmic gains appear as `δ = 0`. That is the right granularity for the
   `P` vs `NP` question and the wrong one for fine-grained results; the
   `n^{1.801}` tradeoffs live below its resolution, and the module says so.
3. **`c^j` as the collapse cost is an upper-bound model.** A sharper collapse
   accounting would only lower the threshold, i.e. strengthen Theorem 3's
   conclusion that fixed gains fail.
4. **No new mathematics is claimed.** The theorems are about the shape of proof
   strategies. They are useful because they convert "these approaches seem to
   stall" into "these approaches provably cannot work, and here is the property
   that is missing".

## References

- W. J. Paul, N. Pippenger, E. Szemerédi, W. T. Trotter. *On determinism versus
  non-determinism and related problems.* FOCS 1983.
- J. Hopcroft, W. Paul, L. Valiant. *On time versus space.* JACM 1977.
- P. Dymond, M. Tompa. *Speedups of deterministic machines by synchronous
  parallel machines.* JCSS 1985.
- R. R. Williams. *Simulating Time With Square-Root Space.* STOC 2025 (best
  paper); ECCC TR25-017. <https://eccc.weizmann.ac.il/report/2025/017/>
- J. Cook, I. Mertz. *Tree Evaluation is in space `O(log n · log log n)`.*
  STOC 2024.
- L. Fortnow, D. van Melkebeek. *Time-space tradeoffs for satisfiability.*
  JCSS 2000.
- S. Aaronson, A. Wigderson. *Algebrization: a new barrier in complexity
  theory.* ACM TOCT 2009.
