# A second closure port: uniform sequential magnification

Author: automated research session, 2026-07-25.
Scope: `pnp4/Pnp4/Frontier/SequentialMagnification/` and
`pnp4/Pnp4/Tests/SequentialMagnificationAudit.lean`.

**Bottom line up front.** This report does not solve P vs NP and the code it
describes does not prove `P ≠ NP`. What it does is identify a structural
commitment in this repository that is strictly stronger than the stated goal,
show that the commitment is the direct cause of every refutation on record, and
supply a machine-checked alternative port that survives those refutations —
together with the exact, quantitative statement of what is still missing.

---

## 1. The diagnosis

### 1.1 The repository targets a strictly stronger statement than P ≠ NP

Every route here ends at the same place:

```text
ResearchGapWitness.dagSeparation : ComplexityInterfaces.NP_not_subset_PpolyDAG
VerifiedNPDAGLowerBoundSource
SearchMCSPWeakLowerBound.magnifiesToVerifiedDAGSource
      : weakLowerBound → VerifiedNPDAGLowerBoundSource
```

`spec/target.toml` freezes this as *the* target and `AGENTS.md` makes it the
admissibility criterion for pnp4 mainline work:

> The endpoint must have the strength of an `NP` language lower bound against
> `PpolyDAG`.

`NP ⊄ P/poly` implies `P ≠ NP`; the converse is not known. So the repository has
committed, at the level of enforced policy, to proving something strictly
stronger than what it is trying to prove.

### 1.2 That commitment is the direct cause of every refutation on record

Look at what actually killed each route:

| Refuted | Killing mechanism |
|---|---|
| `FormulaSupportRestrictionBoundsPartial → False` | fixed-slice truth-table hardwiring |
| `FormulaSupportBoundsFromMultiSwitchingContract → False` | same |
| `FormulaSupportBoundsPartial_fromPipeline → False` | singleton per-formula provenance |
| `FormulaCertificateProviderPartial → False` (Probe 13) | universal quantification over `PpolyFormula` witnesses |
| `hInDag_triviality_probe` (`RED_HINDAG_TRIVIAL`) | per-slice truth-table DAG hardwiring |
| iso-strong conclusion closures | promise-YES forcing at a fixed slice |

Each one is a *non-uniformity* artefact. A non-uniform circuit family may
contain, at each input length, a circuit that has the answer table baked in.
No predicate that quantifies over arbitrary members of such a class can be both
non-vacuous and hardwiring-proof. The repository has been re-discovering this
fact, correctly and expensively, for many iterations.

The natural conclusion is not "find a cleverer non-uniform predicate". It is
"stop requiring the non-uniform strengthening".

### 1.3 The repository's own mainline citation does not have the DAG shape

`pnp4/README.md` names McKay–Murray–Williams, *Weak lower bounds on
resource-bounded compression imply strong separations of complexity classes*
(STOC 2019), as the mainline reference for the compression-magnification
frontier. But MMW's Theorem 1.3, as restated and used by Cheraghchi, Hirahara,
Myrisiotis and Yoshida (STACS 2021 / ECCC TR20-103, Theorem 47), reads:

> **Theorem 47 (corollary of MMW19).** There exists a constant `μ > 0` such
> that, if `MCSP[2^{μn}] ∉ DTIME₁[N^{1.01}]`, then `P ≠ NP`.

Their proof: MMW19 Theorem 1.3 states that if `P = NP` then there is a
polynomial `p` such that for every time-constructible `s`, `MCSP[s(n)]` has a
one-pass streaming algorithm with space and update time `p(s(n))`; a streaming
algorithm with update time `u` gives a one-tape machine running in time `N · u`.

The conclusion is `P ≠ NP` **directly**. No `P/poly` lower bound is produced
anywhere in the argument. So the repository's own mainline interface —
`SearchMCSPWeakLowerBound`, whose signature demands
`weakLowerBound → VerifiedNPDAGLowerBoundSource` — is literally unable to
express the theorem it cites as its mainline reference.

That is the gap this work fills.

---

## 2. Why the uniform port is a materially better target

### 2.1 The killing attack provably does not apply

In `PpolyDAG`, a language supported on a single input length is in the class for
free (`fixedSlice_gapPartialMCSP_in_PpolyDAG`). In the one-pass streaming model
the same move costs memory, and this is now a theorem in the repository:

```lean
theorem equality_forces_memory {σ : Type} [Fintype σ] (A : StreamingAlgo σ) (m : Nat)
    (hSolve : ∀ u v : List Bool, u.length = m → v.length = m →
      (A.decideOn (u ++ v) = true ↔ u = v)) :
    2 ^ m ≤ Fintype.card σ
```

and its packaged form

```lean
theorem fixed_slice_hardwiring_costs_memory (space m : Nat)
    (hAll : ∀ f : List Bool → Bool,
      ∃ A : SpaceBoundedStreaming space, A.SolvesLength (2 * m) f) :
    m ≤ space
```

Reading: *if a memory budget of `space` bits sufficed to decide every Boolean
function on the single input length `N = 2m`, then `space ≥ N / 2`.* Hardwiring
a slice is not free here; it costs essentially the whole input.

The proof is the classical fooling-set argument, and it is short. That it is
short is the point: the model is weak enough that unconditional lower bounds are
elementary, which is exactly the property a magnification target needs and
exactly the property `PpolyDAG` lacks.

### 2.2 The predicate the port consumes is satisfiable, concretely

The repository's standing rule is that a new source predicate must pass a
falsifiability audit before being wired to a final theorem. The audit module
supplies five probes; the decisive one is

```lean
theorem probeD_mcsp_streaming_hard_concrete : MCSPStreamingHard 0 1 1
```

This is the actual predicate consumed by the port, with the repository's own
MCSP semantics (`circuitComplexityLE treeCircuitClass`), proved to hold at
concrete parameters. No previous source predicate in this project ever passed
that test; each one was proved `→ False` instead.

The parameters are of course far below the magnification budget. The claim being
certified is not "MCSP is hard" — it is "this predicate is not refutable in the
way all previous ones were".

### 2.3 Barrier status

* **Natural proofs (B2)** does not apply directly: the obligation is a uniform
  space lower bound, not a constructive-and-large property of Boolean functions
  useful against `P/poly`. CHMY themselves note that magnification-based
  arguments appear to bypass it.
* **Locality barrier (B4)** — the CHOPRS JACM 2022 paper states the barrier for
  `AC⁰-XOR`, `Formula-XOR`, almost-formulas, `GapAND-Formula` and `AC⁰`
  (HM frontiers A–E). One-pass streaming and one-tape machines are not in its
  stated scope. **This must not be read as "the barrier fails here."** CHMY
  Theorem 3 proves precisely the analogous obstruction for their own technique:
  their lower bound relativizes with respect to `N^{o(1)}`-length oracle
  queries, and hence cannot reach the magnification regime. The honest statement
  is: *the published barrier does not as stated cover this port, and the same
  phenomenon reappears in a model-specific form that is now quantified.*
* **Internal NoGo entries** (`NOGO-000004/6/8/9`, Probe 13, iso-strong,
  hardwiring) do not transfer: none of them is about a uniform sequential model,
  and §2.1 rules out the hardwiring family outright.

---

## 3. The frontier, quantified

This is the part that changes what "remaining work" means on this route.

| | size parameter | model | time exponent |
|---|---|---|---|
| MMW magnification **needs** | `2^{μ₁ n}`, `μ₁ = o(1)` | `DTIME₁` | `N^{1.01}` |
| CHMY **prove** | `2^{μ₂ n}`, `μ₂ = 1 - o(1)` | `BPTIME₁` (stronger) | `N^{1.99}` |

**The time side is already won**, with room to spare and with the stronger
randomised model: `1.99 > 1.01`. Recorded as
`time_exponents_are_compatible`.

**The whole remaining distance to `P ≠ NP` on this route is the gap between two
constants in the MCSP size parameter.** CHMY state it themselves:

> *"what is missing for proving P ≠ NP is to decrease the size parameter from
> `2^{(1-o(1))n}` to `2^{o(n)}` in Theorem 2, or to increase the size parameter
> from `2^{o(n)}` to `2^{(1-o(1))n}` in Theorem 1."*

### 3.1 The obvious bridge, and why it fails

Padding. Extend `f` on `n` variables to `g(x, y) := f(x)` on `n' = k·n`
variables. Circuit complexity is unchanged, so the same absolute threshold `T`
corresponds to relative exponent `log T / n` before and `log T / (k n)` after:
padding moves from large `μ₂` towards small `μ₁`, which is the direction needed.

The exactness of that step is now a theorem
(`padding_preserves_circuit_size`, both directions, with exact size
preservation via `liftCircuit` / `restrictCircuit`).

The obstruction is the input length. A truth table of length `N = 2^n` becomes
one of length `N' = N^k`, so a proved `N^α` lower bound survives only as
`N'^{α/k}`. Matching the exponents forces `μ₁ · k = μ₂`, hence `k ≥ 2` whenever
`μ₁ < μ₂`, hence a transferred exponent of at most `1.99 / 2 = 0.995` — already
below the required `1.01`. Kernel-checked as

```lean
theorem padding_cannot_close_size_parameter_gap
    (mu1 mu2 k : Nat) (hmatch : mu1 * k = mu2) (hlt : mu1 < mu2) :
    chmyTimeExponentNum < mmwTimeExponentNum * k
```

Even a single doubling of the variable count destroys the bound, long before one
reaches the true ratio `μ₂ / μ₁ = ω(1)`. The arithmetic model is deliberately
generous to padding — it ignores the cost of physically writing the padded truth
table on a one-tape machine, which only makes the transfer worse.

### 3.2 What is actually left

1. **Lower `μ₂`.** Prove a one-tape / streaming lower bound for `MCSP[2^{μn}]`
   at small `μ`. The published route goes through a *local* hitting-set
   generator; the seed length of the Forbes–Kelley construction is `Õ(√N)`, and
   the outputs of a local HSG with seed length `λ` are MCSP-YES instances only
   at thresholds `s ≳ λ`. That is what pins `μ ≥ 1/2`. Lowering `μ` therefore
   requires a **local HSG with seed length `N^{o(1)}` secure against read-once
   oblivious branching programs**.
2. **Raise `μ₁`.** CHMY Theorem 3 shows this is impossible for `μ > 1/2` by the
   existing technique (near-linear-time oracle algorithms making
   `N^{o(1)}`-length queries), so it needs a genuinely new magnification
   mechanism.
3. **Padding.** Closed, §3.1.

Note where (1) and (2) meet: `μ = 1/2`, which is exactly the seed-length
exponent of the best known PRGs for read-once oblivious branching programs. On
this route, the residual obstruction to `P ≠ NP` is a **pseudorandomness**
question — improve local PRG/HSG seed length against ROBPs from `N^{1/2}` to
`N^{o(1)}` — rather than a circuit-complexity question. That reformulation is,
to this author's knowledge, not written down anywhere in this repository, and it
is a considerably more specific research target than "prove a non-uniform lower
bound against `P/poly`".


---

## 3b. Stage 2 (same session): the obligation reduced to pseudorandomness

The frontier statement in §3.2 — "lower `μ₂` via a local HSG with seed length
`N^{o(1)}`" — is now a formal object rather than a remark.

`LocalHSG.lean` defines a **local generator** at size parameter `s` (every
output is the truth table of a function with circuit complexity `≤ s`) and its
**hitting-set security** against space-bounded one-pass tests, and proves:

```lean
theorem MCSPStreamingHard_of_localHSG
    (G : LocalGenerator n s seedLen)
    (hHit : HitsStreamingTests G space)
    (hSlack : 2 * (easyFunctions n s).card ≤ Fintype.card (TruthTable n)) :
    MCSPStreamingHard space n s
```

The argument is the standard one: a solver for MCSP[`s`] has a complement that
accepts every NO instance, hence at least half of all tables by Shannon
counting, hence is a large test; but the complement rejects every output of a
local generator, since those are all YES instances. So a secure local HSG and an
MCSP solver cannot coexist. The class of one-pass devices is closed under
complement at no memory cost, which is what makes the step legal —
`SpaceBoundedStreaming.complement`.

Composed with the port, `SequentialCapstone.lean` gives

```lean
theorem P_ne_NP_of_localHSG
    (C : MMWStreamingMagnification) (s : Nat → Nat) (n seedLen : Nat)
    (G : LocalGenerator n (s n) seedLen)
    (hHit : HitsStreamingTests G (C.spaceBudget (s n)))
    (hSlack : ...) :
    Pnp3.ComplexityInterfaces.P_ne_NP
```

### Where `μ ≥ 1/2` actually comes from

The second theorem of the module is the one that explains the published
parameters:

```lean
theorem seedLength_bound_of_injective_localGenerator
    (G : LocalGenerator n s seedLen) (hinj : Function.Injective G.gen) :
    2 ^ seedLen ≤ Pnp3.Models.circuitCountBound n s
```

An injective local generator cannot have more seeds than there are functions of
circuit complexity `≤ s`. That single inequality is the price of locality, and
it is what couples the two parameters that the two published theorems disagree
about. Writing `N = 2^n` and `s = N^μ`, the right-hand side is `2^{Õ(N^μ)}`, so

```text
seed length λ ≲ Õ(N^μ).
```

The Forbes–Kelley generator used by CHMY has `λ = Õ(√N)`, forcing `μ ≥ 1/2` —
precisely the constant at which CHMY's own Theorem 3 says the magnification side
stops working. The two sides of the frontier meet at `1/2` because both are
governed by the same quantity.

Sharp form, also proved:

```lean
theorem no_injective_localGenerator_of_seed_too_long
    (hbig : circuitCountBound n s < 2 ^ seedLen) :
    ¬ ∃ G : LocalGenerator n s seedLen, Function.Injective G.gen
```

### Net effect

The open obligation changed shape:

| before | after |
|---|---|
| "prove a weak lower bound for MCSP against one-pass streaming" | "construct a local hitting-set generator against read-once/one-pass devices with seed length `N^{o(1)}`" |

Both are open. The second is a *construction task with named parameters* in a
well-developed area (unconditional PRG/HSG constructions for ROBPs), rather than
an open-ended search for a lower-bound technique — and its difficulty is now
bounded below by a kernel-checked inequality rather than by intuition.

`FoolingSet.lean` additionally records the one-way communication method
(`card_le_card_state_of_foolingFamily`) as a reusable tool, since that is the
technique any direct attack on `MCSPStreamingHard` would use.

## 3c. Governance decision (2026-07-25)

Accepted by the maintainer in this session:

* `AGENTS.md` now recognises **two** mainlines. Mainline A is unchanged
  (`SearchMCSPWeakLowerBound → VerifiedNPDAGLowerBoundSource → PpolyDAG`).
  Mainline B is the sequential route, reducing `MCSPStreamingHard` or the
  stronger `LocalHSGWitness`.
* `spec/target.toml` gained an additive `[secondary_target]` block;
  `[meta].spec_version` 0.1.2 → 0.1.3, with `spec/version_manifest.toml`
  updated in the same change and the cross-check passing.
* The frozen `[target]` block, `[frozen_identifiers]`, `[frozen_files]` and
  `pnp3/Magnification/UnconditionalResearchGap.lean` are **untouched**. The
  target-lock guard passes unchanged.
* Every claim built on Mainline B must state its dependency on the unproved
  `MMWStreamingMagnification` contract; `AGENTS.md` says so explicitly.

---

## 3d. Stage 3 (same session): the local-HSG shortcut is closed, and why

The natural next question after §3b is: *does a generator with those parameters
exist?*  It does not — not in the test class the module used — and the reason is
elementary enough that it should have been checked before §3b was written.

### The window test

A one-pass device can hold the **last `w` bits** of its input in a shift
register: `2 ^ w` states, no counter. Take `w = seedLen + 1`. The set `P` of
last-`w` windows realised by the `2 ^ seedLen` generator outputs has
`|P| ≤ 2 ^ seedLen = 2 ^ w / 2`, so the test

> accept iff the last `w` bits are not a realised window

rejects **every** output of the generator and accepts **at least half** of all
truth tables. Both halves are proved: the shift-register semantics
(`run_windowAlgo`), and largeness by an explicit injection that rewrites the
window of a rejected table through an injection `P ↪ Pᶜ`
(`largeAcceptance_windowSolver`).

Therefore `HitsStreamingTests G space` is false whenever `space ≥ seedLen + 1`
(`not_hitsStreamingTests_of_space_ge_seed`).

### The resulting inequality

Combined with the price of locality from §3b:

```lean
theorem localHSG_budget_bound (G : LocalGenerator n s seedLen)
    (hinj : Function.Injective G.gen) (hfit : seedLen + 1 ≤ tableLen n)
    (hHit : HitsStreamingTests G space) :
    2 ^ space ≤ Pnp3.Models.circuitCountBound n s
```

**The memory budget a local hitting-set generator can defeat is at most the
logarithm of the number of circuits of size `≤ s`, i.e. `Õ(s)`.** The
magnification contract supplies `space = p(s)`. So the local-HSG route is
available only while `p(s)` stays within `Õ(s)` — for any polynomial of degree
above 1 it is closed.

This matches the published convention exactly, which is the reassuring part.
CHMY define a local generator as `G : {0,1}^s → {0,1}^N` whose output bits come
from circuits of size at most `s` — *the seed length and the size parameter are
the same `s`*. A generator cannot fool a class whose resource bound exceeds its
own seed length; that is what the theorem says in the space-bounded setting, and
it is why the published construction lives at `μ ≈ 1`.

### What is retracted and what is not

* **Retracted:** the framing of §3b that the remaining obligation "is" the
  construction of a local HSG. In the *non-uniform space-bounded* test class of
  `MCSPStreamingTarget.lean`, that object does not exist at the port's
  parameters. `LocalHSG.MCSPStreamingHard_of_localHSG` remains a true theorem
  with an unreachable hypothesis.
* **Not retracted:** `MCSPStreamingHard` itself, which is the port's actual
  obligation. The window test rejects one finite set; it does not decide MCSP.
  Nothing here bears on it.
* **Not retracted:** everything in §2 — the anti-hardwiring theorem, the
  falsifiability audit, the port itself.

### The repair, and why it is the right one anyway

The window test hardwires `P`. It is non-uniform. McKay–Murray–Williams produce
a *uniform* streaming algorithm with **bounded update time**, and a
bounded-update-time device cannot hardwire an arbitrary set of `2 ^ seedLen`
windows.

So the fix is to restrict `SpaceBoundedStreaming` to bounded-update-time /
uniform devices — which is exactly the modelling caveat already flagged as
limitation 3 of this report when the port was first written. The caveat was not
cosmetic: it is load-bearing, and the space-only model is not merely *stronger
than needed* but *too strong to be satisfiable* on the HSG side.

This is the concrete next work item, and it is well-defined: add an update-time
budget to the model, re-derive §3b in the restricted class, and re-run the
window test to confirm it is excluded.


---

## 4. What was added to the repository

Six modules, all built, zero `axiom`/`sorry`/`admit`/`native_decide`, axiom
surface limited to `propext`, `Classical.choice`, `Quot.sound`:

* `StreamingModel.lean` — the model.
* `StreamingLowerBounds.lean` — `equality_forces_memory`, `parity_solvable`.
* `MCSPStreamingTarget.lean` — MCSP as a stream; `MCSPStreamingHard`;
  `fixed_slice_hardwiring_costs_memory`.
* `MMWMagnificationPort.lean` — the MMW contract, the machine-checked
  contrapositive, `SequentialResearchGapWitness`, and the widened endpoint
  `PvsNPClosureRoute`.
* `SizeParameterPadding.lean` — the exact padding lemma.
* `MuGapNoGo.lean` — the two published constants and the padding no-go.
* `FoolingSet.lean` — the one-way communication method as a reusable tool.
* `LocalHSG.lean` — local hitting-set generators, the reduction
  `local HSG → MCSPStreamingHard`, and the seed-length counting bound.
* `SequentialCapstone.lean` — `P_ne_NP_of_localHSG`, `LocalHSGWitness`.
* `HSGWindowNoGo.lean` — the window test and the budget inequality that closes
  the local-HSG shortcut in the space-only model.
* `Tests/SequentialMagnificationAudit.lean` — probes A–H (H is negative).

Deliberately **not** changed: `RESEARCH_CONSTITUTION.md`, the frozen `[target]`
block of `spec/target.toml`, and
`pnp3/Magnification/UnconditionalResearchGap.lean`. The frozen target is intact
and the target-lock guard passes unchanged. `spec/target.toml` gained only an
additive `[secondary_target]` block after the maintainer accepted the widening
(§3c).

## 5. Honest limitations

1. **No new lower bound is proved.** The weak sequential lower bound — the whole
   mathematical content of the route — remains open, and nothing here makes it
   easier to prove. What changes is which statement one should be trying to
   prove, and (after §3b) that the statement is a construction task with named
   parameters plus a kernel-checked inequality bounding how good the
   construction must be.
2. **`MMWStreamingMagnification` is an unproved external contract.** It is
   recorded in the same style as the existing `AC0pCoinLowerBoundContract`, and
   formalising MMW19 Theorem 1.3 in Lean would be a large independent project.
3. **The streaming model here bounds space only, not update time.** This makes
   the contract weaker (hence safer to assume) and the required hardness
   stronger (hence sufficient) — conservative on both sides, but it does mean
   the port asks for a *space* lower bound, which is more than MMW strictly
   need.
4. **The `μ`-gap arithmetic uses integer-scaled exponents** (`101`, `199` over a
   denominator of `100`) and an idealised transfer model. It is a faithful
   record of the published constants, not a substitute for the analytic
   argument.
5. **The locality-barrier claim is a scope claim, not an evasion claim.** See
   §2.3.
6. **The Shannon slack is a hypothesis, not yet discharged.**
   `MCSPStreamingHard_of_localHSG` takes `hSlack` as an input. The repository's
   counting layer has the machinery to prove it below the counting threshold;
   wiring that in is listed as TODO Target 4 item 2.
7. **This is one route.** It is not an argument that the non-uniform route is
   wrong, only that it is strictly harder than necessary and that its known
   failure modes are structural.

## References

* D. M. McKay, C. D. Murray, R. R. Williams. *Weak lower bounds on
  resource-bounded compression imply strong separations of complexity classes.*
  STOC 2019.
* M. Cheraghchi, S. Hirahara, D. Myrisiotis, Y. Yoshida. *One-Tape Turing
  Machine and Branching Program Lower Bounds for MCSP.* STACS 2021;
  ECCC TR20-103.
* L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam.
  *Beyond Natural Proofs: Hardness Magnification and Locality.* JACM 69(4):25,
  2022; arXiv:1911.08297.
* M. Forbes, Z. Kelley. *Pseudorandom generators for read-once branching
  programs, in any order.* FOCS 2018.
* I. C. Oliveira, J. Pich, R. Santhanam. *Hardness magnification near
  state-of-the-art lower bounds.* CCC 2019.
* A. A. Razborov, S. Rudich. *Natural proofs.* JCSS 55(1):24–35, 1997.
