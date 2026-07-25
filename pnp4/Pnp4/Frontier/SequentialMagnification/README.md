# `Frontier/SequentialMagnification/` — the uniform (streaming) closure port

Added: 2026-07-25.

## One-paragraph summary

Every closure route in this repository so far ends in the **non-uniform**
statement `NP ⊄ PpolyDAG`.  That is strictly stronger than `P ≠ NP`, and every
internal refutation on record (`FormulaSupportRestrictionBoundsPartial → False`,
`FormulaCertificateProviderPartial → False`, `hInDag_triviality`, the iso-strong
closures) is an artefact of non-uniformity: a truth table can be hardwired into
a circuit family for free.  The magnification theorem that `pnp4/README.md`
already names as the mainline reference — McKay–Murray–Williams, STOC 2019 —
does **not** have that shape.  Its conclusion is `P ≠ NP` directly, and its
hypothesis is a *uniform, sequential, memory-bounded* lower bound for MCSP.
This directory supplies the missing port, together with kernel-checked evidence
that the new source predicate is not vacuous.

## The published chain

Cheraghchi–Hirahara–Myrisiotis–Yoshida, *One-Tape Turing Machine and Branching
Program Lower Bounds for MCSP*, STACS 2021 / ECCC TR20-103, restate MMW as:

> **Theorem 47 (a corollary of MMW19).**  There exists a constant `μ > 0` such
> that, if `MCSP[2^{μn}] ∉ DTIME₁[N^{1.01}]`, then `P ≠ NP`.

Their proof of it is two lines: MMW19 Theorem 1.3 says that `P = NP` gives a
one-pass streaming algorithm for `MCSP[s(n)]` with space and update time
`p(s(n))`; a streaming algorithm with update time `u` runs on a one-tape machine
in time `N · u`.

And they prove, unconditionally:

> **Theorem 2.**  There is a constant `μ₂` (close to `1`) with
> `MCSP[2^{μ₂ n}] ∉ BPTIME₁[N^{1.99}]`.

## Why this is worth formalising

The *time* side of the frontier is already won: `1.99 > 1.01`, and the proved
bound is even randomised where the hypothesis only needs deterministic.  The
entire remaining distance to `P ≠ NP` on this route is the gap between the two
constants `μ₁ < μ₂` in the MCSP **size parameter**.  In the authors' own words:

> *"what is missing for proving P ≠ NP is to decrease the size parameter from
> `2^{(1-o(1))n}` to `2^{o(n)}` in Theorem 2, or to increase the size parameter
> from `2^{o(n)}` to `2^{(1-o(1))n}` in Theorem 1."*

That is a far more concrete target than "prove a non-uniform lower bound", and
it is not touched by the barriers that close the other routes here — see
"Barrier status" below.

## Module map

| Module | Content | Status |
|---|---|---|
| `StreamingModel.lean` | One-pass streaming algorithms with an explicit state type; `SpaceBoundedStreaming space` bounds the memory by `2 ^ space` states. | definitions, all proved |
| `StreamingLowerBounds.lean` | `equality_forces_memory`: deciding two-block equality at block length `m` needs `2 ^ m` states. `parity_solvable`: one bit of memory decides a nontrivial function. | **unconditional theorems** |
| `MCSPStreamingTarget.lean` | MCSP read as a bit stream, reusing `circuitComplexityLE treeCircuitClass`; `MCSPStreamingHard`; `fixed_slice_hardwiring_costs_memory`. | definitions + proved |
| `MMWMagnificationPort.lean` | The published MMW contract, the machine-checked contrapositive `P_ne_NP_of_mcsp_streaming_hardness`, `SequentialResearchGapWitness`, and the widened endpoint `PvsNPClosureRoute`. | contract (external) + proved bridge |
| `SizeParameterPadding.lean` | Exact padding lemma: dummy variables change neither circuit complexity nor witnessing size. | **unconditional theorem** |
| `MuGapNoGo.lean` | The two published constants, and the kernel-checked proof that padding cannot bridge them. | **no-go module** |
| `FoolingSet.lean` | The fooling-set / one-way communication method as a reusable tool. | **unconditional theorems** |
| `LocalHSG.lean` | Local hitting-set generators: `local HSG ⟹ MCSPStreamingHard`, plus the counting bound `2 ^ seedLen ≤ circuitCountBound n s` that pins the size parameter. | **unconditional theorems** |
| `SequentialCapstone.lean` | Composition: `P_ne_NP_of_localHSG`, `LocalHSGWitness`. | proved bridge |
| `HSGWindowNoGo.lean` | The window test: `HitsStreamingTests G space` is false once `space ≥ seedLen + 1`; hence `2 ^ space ≤ circuitCountBound n s`. | **no-go module** |
| `../../Tests/SequentialMagnificationAudit.lean` | Probes A–E, the falsifiability audit. | proved |

## Proved vs. open

**Proved outright, no assumptions:**

* `equality_forces_memory` — the fooling-set memory lower bound;
* `no_small_streaming_solver_for_equality`,
  `exists_streaming_hard_function_at_fixed_length`;
* `parity_solvable` — the model is not trivially powerless;
* `fixed_slice_hardwiring_costs_memory` — hardwiring a fixed input length costs
  `≥ N/2` bits of memory here, unlike in `PpolyDAG`;
* `padding_preserves_circuit_size`, `circuitComplexityLE_padding` — exact
  padding;
* `padding_cannot_close_size_parameter_gap` — the padding no-go;
* `probeD_mcsp_streaming_hard_concrete` — `MCSPStreamingHard 0 1 1`, a closed
  satisfiability certificate for the exact predicate the port consumes.

**External published contract, not proved here:**

* `MMWStreamingMagnification` — MMW19 Theorem 1.3, recorded in the same style as
  `AC0pCoinLowerBoundContract` and `CKLMFormulaCircuitLocalPRGSourceContract`.

**Open, research-level:**

* An inhabitant of `MCSPStreamingHard (C.spaceBudget (s n)) n (s n)`.  This is
  the port's actual obligation and it remains untouched.

**Retracted (2026-07-25, same session): the local-HSG shortcut.**

`LocalHSG.MCSPStreamingHard_of_localHSG` is a correct theorem, but
`HSGWindowNoGo.lean` shows its hypothesis is unreachable at the port's
parameters *in this test class*.  A generator with `2 ^ seedLen` seeds is
defeated by a `(seedLen + 1)`-bit shift register that rejects every one of its
outputs and still accepts half of all truth tables.  Hence

```text
2 ^ space ≤ circuitCountBound n s        (localHSG_budget_bound)
```

i.e. the memory budget a local HSG can defeat is at most `Õ(s)`, while the
contract supplies `space = p(s)`.  The route is open only while `p` stays within
`Õ(s)`.

The escape hatch is the test class, not the idea: the window test hardwires its
target set and is therefore **non-uniform**, whereas McKay–Murray–Williams
produce a *uniform* streaming algorithm with bounded update time.  Restricting
`SpaceBoundedStreaming` to bounded-update-time devices is the repair, and it is
also the more faithful model.  That repair is the next work item.

**Therefore this directory does not prove `P ≠ NP` and does not claim to.**

## Barrier status

| Barrier | Applies here? |
|---|---|
| Relativization (B1) | Applies to any route, as always. The MMW magnification step is itself non-relativizing. |
| Natural proofs (B2) | Not directly: the target is a *uniform* space lower bound, not a property of Boolean functions useful against `P/poly`. |
| Algebrization (B3) | Same status as B1. |
| **Locality barrier (B4)** | The CHOPRS JACM 2022 paper states the barrier for `AC⁰-XOR`, `Formula-XOR`, almost-formulas, `GapAND-Formula` and `AC⁰` (their HM frontiers A–E). Streaming and one-tape models are **not** in its stated scope. **This is not a claim that the barrier fails here** — CHMY Theorem 3 proves the analogous short-query-oracle obstruction for their own technique at `μ > 1/2`, which is the same phenomenon. It is a claim that the published barrier does not, as stated, cover this port. |
| Magnification threshold gap (B5) | This is exactly the `μ₁ < μ₂` gap, now recorded quantitatively in `MuGapNoGo.lean` instead of informally. |
| Internal `hInDag`/hardwiring refutations | **Provably do not apply**: `fixed_slice_hardwiring_costs_memory`. |

## The reduced chain

```text
   local HSG (seed λ, local at s, secure vs space-B one-pass streaming)   [BLOCKED here]
 + Shannon-counting slack at s                                            [standard]
 + MMW19 Theorem 1.3                                                      [published contract]
 ─────────────────────────────────────────────────────────────────────────────────────
   P ≠ NP                                                (`P_ne_NP_of_localHSG`)
```

subject to two kernel-checked constraints, the second of which closes it in the
current test class:

```text
2 ^ λ     ≤ circuitCountBound n s   (`seedLength_bound_of_injective_localGenerator`)
2 ^ space ≤ circuitCountBound n s   (`localHSG_budget_bound`, via the window test)
```

## What would actually close the gap

1. **Lower `μ₂`** — a one-tape/streaming lower bound for `MCSP[2^{μn}]` at small
   `μ`.  The published proof routes through a *local* hitting-set generator of
   seed length `Õ(√N)` (Forbes–Kelley), which is what pins `μ ≥ 1/2`.  Lowering
   `μ` means a local HSG with seed length `N^{o(1)}` against read-once oblivious
   branching programs.
2. **Raise `μ₁`** — CHMY Theorem 3 rules this out for `μ > 1/2` *by the existing
   technique* (near-linear-time oracle algorithms with `N^{o(1)}`-length
   queries), so it needs a new magnification mechanism.
3. **Not padding** — closed here, see `MuGapNoGo.lean`.

Both live moves meet at `μ = 1/2`, which is the seed-length exponent of the best
known PRGs for read-once oblivious branching programs.  In that precise sense
the remaining obstruction is a *pseudorandomness* question, not a
circuit-complexity question.

## Governance note

`spec/target.toml` freezes `ResearchGapWitness.dagSeparation :
ComplexityInterfaces.NP_not_subset_PpolyDAG` as *the* target, and `AGENTS.md`
requires pnp4 mainline packages to end in `VerifiedNPDAGLowerBoundSource`.  The
port in this directory deliberately does **not** modify either: the frozen
target is untouched and `UnconditionalResearchGap.lean` is unchanged.
`PvsNPClosureRoute` records the widened endpoint as a *proposal*, so that the
decision to recognise a second mainline stays with the maintainer.

## References

* D. M. McKay, C. D. Murray, R. R. Williams. *Weak lower bounds on
  resource-bounded compression imply strong separations of complexity classes.*
  STOC 2019. <https://dl.acm.org/doi/10.1145/3313276.3316396>
* M. Cheraghchi, S. Hirahara, D. Myrisiotis, Y. Yoshida. *One-Tape Turing
  Machine and Branching Program Lower Bounds for MCSP.* STACS 2021;
  ECCC TR20-103. <https://eccc.weizmann.ac.il/report/2020/103/>
* L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam.
  *Beyond Natural Proofs: Hardness Magnification and Locality.* JACM 69(4):25,
  2022. <https://arxiv.org/abs/1911.08297>
* M. Forbes, Z. Kelley. *Pseudorandom generators for read-once branching
  programs, in any order.* FOCS 2018.
