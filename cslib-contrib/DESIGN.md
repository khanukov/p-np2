# Complexity classes for CSLib: P, coP, NP — consolidated design

Audience: Dmitry, CSLib maintainers, and a hostile reviewer. Everything stated here is either
(a) verified against the local CSLib/Mathlib sources, (b) present in the drafted Lean code under
`out/write/lean/`, or (c) explicitly marked as *not claimed* in §5.

---

## 1. Goal and scope

Add the first complexity-class layer to CSLib: the classes **P**, **coP**, and **NP** over
CSLib's existing deterministic single-tape Turing machine (`Cslib.Turing.SingleTapeTM`,
Deterministic.lean), with the theorems **coP = P** and **P ⊆ NP**, both proved by genuine
machine constructions. CSLib's `Cslib/Computability/README.md` lists complexity classes as
planned scope; nothing of the kind is on `main` (verified 2026-07-17: no `P`, `NP`, `DTIME`,
deciders, or verifiers anywhere; the closest artifacts are `TimeComputable` /
`PolyTimeComputable` for word functions and the merged NTM file).

Non-goals for this contribution (roadmap only, see §5): DTIME/DSPACE, the verifier↔NTM
equivalence, padding equivalence for certificate length, reductions, Cook–Levin, multi-tape
machines.

Design pillars, in one paragraph. A decider for `L : Language Symbol` (Mathlib's `Language`)
is a `SingleTapeTM` over the extended alphabet `DecSym Symbol` — the input symbols plus two
dedicated verdict symbols `.verdict true / .verdict false`. Input `x` is laid on the tape as
`x.map .input` (injective end to end, by theorem). The machine *decides* `L` within `T` iff on
**every** input it halts within `T x.length` steps — counted by the **existing**
`OutputsWithinTime` — with the tape holding exactly `[.verdict b]` and `b = true ↔ x ∈ L`.
`P` = ∃ machine + `Polynomial ℕ` bound; `coP` = complements; `coP = P` by post-composing (the
existing `compComputer`) with a one-step verdict-flipping machine. `NP` is verifier-based:
a pair language over `Symbol ⊕ Bool` **in P** (hence a total, two-sided, time-bounded
verifier) plus a certificate-length polynomial; certificates are bitstrings (`List Bool`).
`P ⊆ NP` is an honest construction: input-well-formedness scanner + alphabet-relabeling
simulation + verdict extraction, glued by `compComputer`.

Status of the code: PR-1 and PR-2 are fully drafted (no `sorry`) under
`out/write/lean/Cslib/…` — PR-1 as edits to `Foundations/Data/BiTape.lean` and
`Computability/Machines/Turing/SingleTape/Deterministic.lean` (~145 lines added, ~29 changed),
PR-2 as the new file `Computability/Complexity/Defs.lean` (441 lines). No Lean compiler was
available while drafting; §6 makes compilation a hard gate before submission, and
`out/write/lean-core-risks.md` lists every elaboration risk with a concrete fallback.

## 2. The definitions, and why each is THE standard one

All identifiers below exist in the drafted code; the model API they build on is quoted from
CSLib `Deterministic.lean` as it is on `main`:

```lean
structure SingleTapeTM Symbol [Inhabited Symbol] [Fintype Symbol] where
  (State : Type) [stateFintype : Fintype State] (q₀ : State)
  (tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State)

def initCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg := ⟨some tm.q₀, BiTape.mk₁ s⟩
def haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg := ⟨none, BiTape.mk₁ s⟩
def OutputsWithinTime (tm : SingleTapeTM Symbol) (l l' : List Symbol) (m : ℕ) :=
  RelatesWithinSteps tm.TransitionRelation (initCfg tm l) (haltCfg tm l') m
structure PolyTimeComputable (f : List Symbol → List Symbol) extends TimeComputable f where
  poly : Polynomial ℕ
  bounds : ∀ n, timeBound n ≤ poly.eval n
```

### 2.1 `DecSym` — the decider alphabet

```lean
inductive DecSym (Symbol : Type) : Type where
  | input : Symbol → DecSym Symbol
  | verdict : Bool → DecSym Symbol

instance : Inhabited (DecSym Symbol) := ⟨verdict false⟩
def DecSym.equivSum (Symbol : Type) : DecSym Symbol ≃ Symbol ⊕ Bool
instance [Fintype Symbol] : Fintype (DecSym Symbol) := Fintype.ofEquiv _ (equivSum Symbol).symm

def inputWord (x : List Symbol) : List (DecSym Symbol) := x.map .input
theorem inputWord_injective : Function.Injective (inputWord (Symbol := Symbol))
```

**Standard because:** every textbook decider has a tape alphabet Γ strictly containing the
input alphabet Σ (Sipser, *Introduction to the Theory of Computation* 3e, Ch. 3, Def. 3.1:
"Γ is the tape alphabet, where ␣ ∈ Γ and Σ ⊆ Γ"). `DecSym Symbol` is exactly "Σ plus two
fresh work symbols". Verdict symbols are distinct from every input symbol *by constructor* and
from the blank *by type* (blank is `none : Option (DecSym Symbol)` in CSLib's model).
Why an inductive and not `Symbol ⊕ Bool`: `SingleTapeTM` demands `[Inhabited Symbol]`, and
Mathlib has **no** `Inhabited (α ⊕ β)` instance (verified by grep; only `Fintype (α ⊕ β)`,
`Mathlib/Data/Fintype/Sum.lean`); `DecSym` carries canonical instances and needs only
`[Fintype Symbol]`. The `Fintype` instance goes through `Fintype.ofEquiv` deliberately —
no dependence on the `deriving Fintype` handler (compile-time alternative only).

### 2.2 `DecidesWithinTime` — the decider

```lean
def DecidesWithinTime (tm : SingleTapeTM (DecSym Symbol)) (L : Language Symbol)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Symbol, ∃ b : Bool,
    tm.OutputsWithinTime (inputWord x) [.verdict b] (T x.length) ∧ (b = true ↔ x ∈ L)
```

**Standard because:** this is Arora–Barak, *Computational Complexity* (2009), **Def. 1.13**
verbatim, adapted to CSLib's model: "L ∈ DTIME(T(n)) iff there is a TM that runs in time
c·T(n) and **computes the characteristic function of L** (outputs 1 on x ∈ L, 0 otherwise)".
The verdict is the halting tape content `[.verdict b]` — the tape-alphabet analogue of
Sipser's `q_accept/q_reject` (Sipser Def. 3.1 / Def. 7.12), forced by the model itself:
CSLib's `Deterministic.lean` states in its design notes that "we do not make the halting state
a member of the state type" (halting = `tr` returning `none`; the run ends exactly at
`haltCfg`). With no states to designate as accepting, the verdict must live on the tape, and
Arora–Barak's χ_L formulation is precisely the textbook definition that does so. The
accept/reject-*states* alternative (a `Decider` structure with `q_accept/q_reject`, mirroring
the merged NTM's `accept : Set State` and `accept_halting`) was considered and is offered to
maintainers as an explicit option in the Zulip post (§7); we default against it because it
duplicates the NTM's acceptance layer on a model that deliberately lacks halt states, whereas
χ_L reuses the existing function-computation semantics unchanged.

Three deliberate features a reviewer should notice:
- **Totality is inside the definition** — `∀ x, ∃ b, …` with a hard time bound; there is no
  input on which behavior is unconstrained (Sipser Def. 7.12 is stated for deciders, i.e.
  machines that halt on all inputs).
- `∃ b, … ∧ (b = true ↔ x ∈ L)` avoids any `Decidable (x ∈ L)` hypothesis; determinism makes
  `b` unique (`outputs_unique`).
- The raw `T : ℕ → ℕ` is only a device; §2.3's `mem_P_iff_timeBound` certifies it equivalent
  to the `Polynomial ℕ` convention.

Companion lemmas (drafted): `DecidesWithinTime.mono` (weaken the bound) and

```lean
theorem DecidesWithinTime.language_eq (h : tm.DecidesWithinTime L T)
    (h' : tm.DecidesWithinTime L' T') : L = L'
```

— a machine decides at most one language, so "the language decided by `tm`" is well-defined.

### 2.3 `P` and `coP`

```lean
def P (Symbol : Type) [Fintype Symbol] : Set (Language Symbol) :=
  { L | ∃ (tm : SingleTapeTM (DecSym Symbol)) (p : Polynomial ℕ),
      tm.DecidesWithinTime L fun n => p.eval n }

def coP (Symbol : Type) [Fintype Symbol] : Set (Language Symbol) := { L | Lᶜ ∈ P Symbol }

theorem mem_P_iff_timeBound {L : Language Symbol} :
    L ∈ P Symbol ↔ ∃ (tm : SingleTapeTM (DecSym Symbol)) (T : ℕ → ℕ),
      tm.DecidesWithinTime L T ∧ ∃ p : Polynomial ℕ, ∀ n, T n ≤ p.eval n
```

**Standard because:** Arora–Barak Def. 1.13 ("P = ⋃_c DTIME(n^c)") / Sipser **Def. 7.12**
("P is the class of languages that are decidable in polynomial time on a deterministic
single-tape Turing machine") — note Sipser's P is defined on *single-tape* machines, exactly
CSLib's model. Bounds are `Polynomial ℕ` evaluated with `Polynomial.eval`, byte-for-byte the
convention of the existing `PolyTimeComputable` (`poly : Polynomial ℕ`,
`bounds : ∀ n, timeBound n ≤ poly.eval n`); `mem_P_iff_timeBound` mirrors that exact field
layout, so both packagings are interchangeable by theorem. `coP` is defined for uniformity
with the future `coNP` (complement classes, Sipser §7 exercises / Arora–Barak Def. 2.20) and
immediately collapsed:

```lean
theorem coP_eq_P (Symbol : Type) [Fintype Symbol] : coP Symbol = P Symbol
```

proved by a **machine** (`compComputer tm (mapHeadComputer DecSym.flip)`): run the decider,
then a one-step machine rewrites the verdict cell under the head by
`flip : .verdict b ↦ .verdict !b`. This genuinely flips the model's verdict; it is not an
artifact of a symmetric encoding. (Note: rewriting `tm.tr`'s final write would be *unsound*
in this model — the last statement may move the head, and the verdict cell may have been
written earlier — which is why the proof is honest post-composition, time `p.eval n + 1 =
(p+1).eval n`.) Non-vacuity ships in the same PR: `bot_mem_P`, `top_mem_P` via
`constComputer b` (sweep right erasing, write `.verdict b`, halt; time `n + 1 ≤ (X+1).eval n`).

Bridge to the existing bundled machinery (one-directional, see §5):

```lean
theorem mem_P_of_polyTimeComputable {L : Language Symbol}
    {f : List (DecSym Symbol) → List (DecSym Symbol)}
    (hf : SingleTapeTM.PolyTimeComputable f)
    (hL : ∀ x, ∃ b, f (inputWord x) = [.verdict b] ∧ (b = true ↔ x ∈ L)) : L ∈ P Symbol
```

### 2.4 `pairEncode` — the (input, certificate) encoding (PR-4)

```lean
def pairEncode (x : List Symbol) (u : List Bool) : List (Symbol ⊕ Bool) :=
  x.map .inl ++ u.map .inr

theorem pairEncode_injective :
    Function.Injective fun p : List Symbol × List Bool => pairEncode p.1 p.2
theorem pairEncode_takeWhile : (pairEncode x u).takeWhile Sum.isLeft = x.map .inl
theorem pairEncode_dropWhile : (pairEncode x u).dropWhile Sum.isLeft = u.map .inr
theorem pairEncode_eq_iff {w : List (Symbol ⊕ Bool)} :
    w = pairEncode x u ↔
      w.takeWhile Sum.isLeft = x.map .inl ∧ w.dropWhile Sum.isLeft = u.map .inr
@[simp] theorem pairEncode_length : (pairEncode x u).length = x.length + u.length
```

**Standard because:** this is the ⟨x, u⟩ of Sipser Def. 7.19 / Arora–Barak Def. 2.1, realized
without a separator *symbol*: the boundary is a type-level tag (`inl` = input, `inr` =
certificate), so no string over the pair alphabet can spoof it, and it is machine-detectable
by one scan (the boundary is the end of the maximal `isLeft`-prefix —
`pairEncode_takeWhile/_dropWhile`, packaged as the recovery iff `pairEncode_eq_iff`). Time
bounds for verifiers are in `x.length + u.length` (`pairEncode_length`), the literal number of
non-blank cells the machine starts with.

### 2.5 `NP` (PR-4)

```lean
def NP (Symbol : Type) [Fintype Symbol] : Set (Language Symbol) :=
  { L | ∃ V : Language (Symbol ⊕ Bool), V ∈ P (Symbol ⊕ Bool) ∧
      ∃ p : Polynomial ℕ, ∀ x : List Symbol,
        x ∈ L ↔ ∃ u : List Bool, u.length ≤ p.eval x.length ∧ pairEncode x u ∈ V }
```

**Standard because:** Arora–Barak **Def. 2.1** verbatim: "L ∈ NP if there exists a polynomial
p and a polynomial-time TM M (the *verifier*) such that for every x, x ∈ L ⇔ ∃ u ∈ {0,1}^{p(|x|)}
with M(x, u) = 1"; equivalently Sipser **Def. 7.19/7.20** (NP = polynomially-bounded-certificate
verifiers). Two deliberate choices, both to be surfaced on Zulip:

- **Certificates are `List Bool`, never the input alphabet.** Arora–Barak's certificates are
  u ∈ {0,1}\*. This is not cosmetic: over a unary input alphabet, input-alphabet certificates
  carry only their length as information, degenerating NP on tally languages. The NP docstring
  documents this so no reviewer re-proposes Σ\*-certificates.
- **`≤ p.eval |x|` rather than `=`.** Arora–Barak use exact length; `≤` is equivalent via
  padding, and the equivalence is a stated PR-5 roadmap theorem — *never assumed* (§5).

Because `V ∈ P`, the verifier is **total**: some machine satisfies `DecidesWithinTime` for
`V`, i.e. halts with an explicit two-sided verdict within its bound on *every* word over the
pair alphabet — accepted pairs, rejected pairs, and ill-formed words alike. NP non-vacuity
(`bot_mem_NP`, `top_mem_NP`, reusing the PR-2 `constComputer` witnesses over `Symbol ⊕ Bool`)
lands in the same PR that defines NP, together with a monotonicity-in-`p` robustness lemma.

### 2.6 `P_subset_NP` (PR-4, machinery from PR-3)

```lean
theorem P_subset_NP (Symbol : Type) [Fintype Symbol] : P Symbol ⊆ NP Symbol
```

Witnesses: `p := 0`, `V := { w | ∃ x ∈ L, w = x.map .inl }`, so
`x ∈ L ↔ pairEncode x [] ∈ V` — the step that would be a cheat if `pairEncode`/`inputWord`
were not injective (it uses `Function.Injective.list_map Sum.inl_injective`). The honest cost
is `V ∈ P (Symbol ⊕ Bool)`: the given decider for `L` works over `DecSym Symbol`, but `V`'s
decider must work over `DecSym (Symbol ⊕ Bool)` and reject ill-formed words. The construction
(textbook: "V(x,u) := M(x)" hides a simulation) is

```
compComputer (checkComputer Symbol)
  (compComputer (relabelComputer ι ι⁻¹ hι tm) (mapHeadComputer g))
```

- `checkComputer` — a 4-state scanner: if every cell is `.input (.inl _)`, restore the head
  and output the input unchanged (time `2n + 3`); otherwise erase the tape and output a marker
  `[.input (.inr false)]` (reusing the `constComputer` erase gadget for the error path).
- `relabelComputer f g hgf tm` — simulate `tm` over a larger alphabet along an injection with
  retraction; same state space, same step count, via a config-map step-homomorphism
  transported by the existing `RelatesInSteps.map` (this is exactly what that lemma was built
  for). On a head symbol outside the range (the error marker), halt in place in one step.
- `mapHeadComputer g` — extract: fix verdicts, send the marker to `.verdict false`.

Key accounting trick (avoids needing `Polynomial.eval` monotonicity in the assembly): on the
good path the checker's output *is* the input word `x.map .inl`, of the **same length** as the
outer input `w`, so the inner run is bounded by `p.eval w.length` exactly, not by a
monotonicity argument. Total time `(2n+3) + p.eval n + 1 + 1 ≤ (2•X + p + 5).eval n`.
Where PR-4 does need eval-monotonicity (certificate-length arithmetic), the ~5-line helper
`Polynomial.eval_mono` (verified **absent** from Mathlib) is added explicitly with an
upstream-to-Mathlib note — bound arithmetic never silently assumes it.

## 3. Blocker map

Each of the 7 blockers, answered by named artifacts (all in drafted code unless marked PR-3/4).

**B1 — input injectivity.** The model was designed for this; `BiTape.lean`'s docstring:
mapping over `some` "ensures that `List`s of the base alphabet … will not collide", and
`initCfg`'s docstring: "distinct lists map to distinct initial configurations". There is no
quotient anywhere (`BiTape`/`StackTape` are plain structures; `StackTape`'s
no-trailing-`none` invariant makes representatives canonical). PR-1 turns intent into
theorems: `StackTape.toList_injective`, `StackTape.mapSome_injective`, `BiTape.mk₁_injective`,
**`SingleTapeTM.initCfg_injective`**, `haltCfg_injective`; PR-2 composes them:
`DecSym.input_injective`, `inputWord_injective`, **`initCfg_inputWord_injective`**
(`x ↦ tm.initCfg (inputWord x)` injective end to end).

**B2 — honest pair encoding.** **`pairEncode_injective`** (joint injectivity);
**`pairEncode_eq_iff`** + `pairEncode_takeWhile/_dropWhile` (machine-detectable, unspoofable
boundary: `inl`/`inr`/blank are three syntactically disjoint classes, no in-alphabet separator
symbol exists to collide with); **`pairEncode_length`** (bounds stated in the number of
non-blank cells the machine starts with, determinable by one scan). PR-4.

**B3 — total verifier.** NP requires `V ∈ P (Symbol ⊕ Bool)`; `P`-membership unfolds to
**`DecidesWithinTime`**, whose body is `∀ w, ∃ b, OutputsWithinTime … [.verdict b] (T w.length)
∧ (b = true ↔ w ∈ V)` — a halting, time-bounded, two-sided verdict on **every** word over the
pair alphabet, hence on every rejecting pair and even on ill-formed words (strictly stronger
than demanded). No "∃ certificate such that it accepts in time" clause exists anywhere on the
deterministic side.

**B4 — canonical verdict.** No `accept : … → Prop` parameter exists anywhere in the design.
The verdict is the halting tape being exactly `[.verdict b]` for the fixed constructor
`DecSym.verdict` — nothing to vary, so no invariance theorem is owed (stated explicitly in the
docstring). The certificate pair ships across PR-1/PR-2: **`outputs_unique`** (PR-1: a
deterministic machine outputs at most one word — proved via the existing
`Relation.ReflTransGen.total_of_right_unique`, `transitionRelation_deterministic`,
`not_transitionRelation_haltCfg`, `haltCfg_injective`) and **`DecidesWithinTime.language_eq`**
(PR-2: a machine decides at most one language).

**B5 — no parallel infrastructure.** Time is the **existing** `OutputsWithinTime` — the
identical predicate used by `TimeComputable.outputsFunInTime`, itself
`RelatesWithinSteps tm.TransitionRelation`, CSLib's single step-counting semantics. Machine
composition is the **existing** `compComputer`; PR-1's **`compComputer_outputsWithinTime`** is
*extracted from* the file's existing private lemmas (`comp_left_relatesWithinSteps` /
`comp_right_relatesWithinSteps`) and `TimeComputable.comp` is refactored to consume it — one
composition proof in the library, not two, and a net simplification of the incumbent code.
**`mem_P_of_polyTimeComputable`** bridges to the bundled machinery; **`mem_P_iff_timeBound`**
certifies the packaging.

**B6 — polynomial convention.** `P` quantifies `p : Polynomial ℕ` and bounds runtime by
`p.eval n` — byte-for-byte `PolyTimeComputable`'s convention. The raw `T : ℕ → ℕ` inside
`DecidesWithinTime` is an internal device certified equivalent by **`mem_P_iff_timeBound`**
(mirroring the `TimeComputable`/`PolyTimeComputable` field split). No lighter growth predicate
exists anywhere. The one known Mathlib gap — no `Polynomial.eval` monotonicity on ℕ — is
avoided in PR-1/2 (`p.eval n + 1 = (p + 1).eval n` needs only `eval_add`/`eval_one`), dodged
in the P⊆NP assembly by the same-length trick (§2.6), and added as an explicit ~5-line helper
with an upstream note when PR-4 first needs it.

**B7 — process.** PR-1 adds only lemmas to two existing files — no new concepts, no classes,
independently valuable (it strengthens the model author's own file and removes duplication).
Classes appear only in PR-2 together with inhabitation and `coP_eq_P`; NP only after its
toolkit exists, together with `bot/top_mem_NP`; no file states a theorem it defers; every
deferred claim is labeled roadmap (§5). Zulip precedes **PR-1** (not just PR-2 — PR-1 touches
Bolton Bailey's file while his draft #192 is active and #396 edits the same declarations).
Titles follow the CI-enforced `feat(Computability): …` format; AI use is disclosed per the
Mathlib policy CSLib adopts (§6).

Extra rules. *P ⊆ NP is not a one-liner:* the statement forces an alphabet change
(`DecSym Symbol` machine → `DecSym (Symbol ⊕ Bool)` machine) plus input validation — the
honest ~550–700 lines of PR-3/PR-4, with B1/B2 injectivity closing every encoding-degeneracy
escape hatch. *P = coP genuinely flips verdicts:* `DecidesWithinTime.compl` runs a real
one-step machine over the model's verdict cell. *Standard to a cold reader:* every definition
above carries its Sipser/Arora–Barak citation in its docstring.

## 4. PR plan

Pre-PR: **Zulip post** (see §7 for its content) — before any code PR.

| PR | Title | Contents | Size |
|----|-------|----------|------|
| PR-1 | `feat(Computability): injectivity and uniqueness lemmas for single-tape TMs` | `StackTape.toList_injective`, `StackTape.mapSome_injective`, `BiTape.mk₁_injective`; `initCfg_injective`, `haltCfg_injective`, `transitionRelation_deterministic`, `not_transitionRelation_haltCfg`, `OutputsWithinTime.outputs`, `outputs_unique`; public `compComputer_outputsWithinTime` extracted from the existing private comp lemmas + `TimeComputable.comp` proof refactor (no signature changes). Two existing files, no new files/concepts. | ~145 lines added, ~29 refactored (drafted) |
| PR-2 | `feat(Computability): deciders and the complexity classes P and coP` | New `Cslib/Computability/Complexity/Defs.lean`: `DecSym` (+ `equivSum`, instances, injectivity), `inputWord`, `mapHeadComputer`, `DecidesWithinTime` (+ `mono`, `language_eq`, `compl`), `initCfg_inputWord_injective`, `P`, `coP`, `compl_mem_P(_iff)`, `coP_eq_P`, `P_eq_coP`, `constComputer`, `bot/top_mem_P`, `mem_P_of_polyTimeComputable`, `mem_P_iff_timeBound`. | 441 lines (drafted) |
| PR-3 | `feat(Computability): tape relabeling and input well-formedness machines` | Toolkit only, no classes: `StackTape.map`/`BiTape.map` + commutation lemmas (~80 ln); `relabelComputer` + `relabel_outputsWithinTime` via `RelatesInSteps.map` (~100–150 ln); `checkComputer` + `checkComputer_outputs_ok/err`, **including** the StackTape helper lemmas it needs (cons-none normalization, `mapSome` stack facts) — not smuggled into PR-4. Splittable 3a/3b. | ~400–550 lines (honest budget; `checkComputer` alone ~250–350) |
| PR-4 | `feat(Computability): pair encodings, NP, and P ⊆ NP` | `pairEncode` + `pairEncode_injective`/`_eq_iff`/`_takeWhile`/`_dropWhile`/`_length`; `NP` + `bot_mem_NP`, `top_mem_NP` + monotonicity-in-`p` robustness; `Polynomial.eval_mono` helper (with Mathlib-upstream note); assembly of `P_subset_NP` (~120 ln). | ~250–350 lines |
| PR-5+ | roadmap only | `DTIME` (`P = ⋃ p, DTIME (p.eval ·)`), `≤`/`=` certificate-length padding equivalence, closure of P under `⊓/⊔`, verifier-NP ≡ NTM-NP, reductions, Cook–Levin. | — |

Before PR-3 review: the `checkComputer` configuration invariants (the two list/stack
inductions and their exact intermediate configurations) are written out and pinned — it is the
critical path of P ⊆ NP.

## 5. What is NOT claimed

- **Not compiled yet.** No Lean toolchain in the drafting sandbox. Every cited CSLib/Mathlib
  identifier was verified by reading the local sources, and `out/write/lean-core-risks.md`
  lists each elaboration risk with fallbacks — but nothing will be PR'd before `lake build`,
  `lake test`, `lake lint`, `lake exe mk_all`, and `lake shake` pass locally.
- **No converse of `mem_P_of_polyTimeComputable`.** Extracting a *total word function* from a
  decider is deliberately unclaimed: a decider's behavior on words containing verdict symbols
  is unconstrained, exactly as a textbook decider is specified only on Σ\*.
- **`≤` vs `=` certificate length:** the padding equivalence is a stated PR-5 target, assumed
  nowhere (the NP docstring documents the choice).
- **No NTM connection is claimed.** The verifier-NP ≡ NTM-NP bridge (`NP_iff_NTIME`, via
  `SingleTapeNTM.AcceptsInAtMostSteps`) is named as the roadmap theorem that must exist before
  any NTM-based class is introduced — and it is blocked on real gaps stated openly:
  `SingleTapeNTM`'s `State` and `accept : Set State` carry no finiteness constraints, and its
  `TrLabel` one-action-per-step granularity costs a constant factor (~3 per textbook
  transition, absorbable into the polynomial but requiring proof).
- **No `DTIME`/`DSPACE`, no reductions, no Cook–Levin, no multi-tape/RAM robustness** — the
  classes are stated for CSLib's single-tape model only (Sipser Def. 7.12 is single-tape, so
  this is standard, but machine-model invariance of P is future work).
- **Universe 0 only:** `Symbol : Type`, inherited from `SingleTapeTM`; classes are not
  universe-polymorphic (flagged in docstrings).
- **No Acceptor instance yet.** `SingleTapeNTM` has an `Acceptor` typeclass instance;
  the deterministic decider layer instead provides `DecidesWithinTime.language_eq`
  (the-language-decided is unique). Whether to add a `decidedLanguage`/`Acceptor` bridge for
  deciders is asked on Zulip (§7) rather than presumed — the honest obstacle is that a
  decider's language is only defined relative to a *proof* of deciding, since `SingleTapeTM`
  has no acceptance primitive.
- Proof-length figures for PR-3/PR-4 are estimates, not commitments.

## 6. Process checklist (from CONTRIBUTING.md, GOVERNANCE.md)

- [ ] **Zulip first.** CONTRIBUTING: "for any major development, it is strongly recommended to
  discuss first on Zulip (or via a GitHub issue) so that the scope, dependencies, and placement
  in the library are aligned" — a first complexity-class layer is squarely a "major
  development". Post *before PR-1* on the Lean Zulip CSLib channel; content per §7.
- [ ] **Coordination with the incumbents.** Invite **@BoltonBailey** (author of the single-tape
  TM files PR-1 edits, and of draft #192 `BitstringDecisionProblem`/quantifier-NP, updated
  2026-07-15) as reviewer or co-author. Position explicitly against draft **#192**, roadmap
  issue **#611** (crei's DTIME-first ladder, 0 comments), and closed **#400** (Timeroot's
  verifier critique — our B3 totality answer) in the Zulip post and every PR description.
  State a rebase plan against open **#396** (removes `h_mono` from `PolyTimeComputable.comp`,
  updated 2026-07-15, same file as PR-1): PR-1 makes no signature changes and passes explicit
  trivial monotonicity facts where needed so it compiles before and after #396.
- [ ] **AI disclosure in every PR description.** CONTRIBUTING: CSLib "follows the Mathlib
  policy on use of AI … If you use artificial intelligence … please explain this in the PR
  description. Explain which tool(s) you used and how you used it." See PR1_DESCRIPTION.md.
- [ ] **PR titles**: CI-enforced category prefix — `feat(Computability): …`.
- [ ] **One maintainer approval** required (GOVERNANCE.md); relevant code owners for
  Computability: fmontesi, chenson2018 (both were requested on #192).
- [ ] **Style**: Mathlib style guide; docstrings on all public defs/theorems, **with published
  references** (CONTRIBUTING: "When formalising a concept that is explained in a published
  resource, please reference the resource in your documentation") — Sipser/Arora–Barak
  citations are in every class docstring. Domain variable names OK (`tm`, `L`, `T`).
- [ ] **Module system**: files start with `module`, use `public import`,
  `@[expose] public section`; every file imports `Cslib.Init` (CI-checked via
  `lake exe checkInitImports`).
- [ ] **Local CI before pushing**: `lake build` (syntax linters), `lake test`, `lake lint`
  (environment linters), `lake exe lint-style --fix`, `lake exe mk_all`
  (Cslib.lean imports-all check), `lake shake --add-public --keep-implied --keep-prefix --fix`.
- [ ] **Reuse principle** (CONTRIBUTING "Design principles / Reuse"): new definitions
  instantiate existing abstractions — hence `OutputsWithinTime`, `compComputer`,
  `RelatesInSteps.map`, `Relation.ReflTransGen.total_of_right_unique`, Mathlib `Language`,
  `Polynomial ℕ` throughout, and zero new timing semantics.
- [ ] **Claims ≤ proofs** in each PR: no `sorry`, no stated-but-deferred theorems, roadmap
  items live only in PR descriptions/Zulip, never in code.

## 7. Open questions for maintainers (the Zulip post)

1. **Verdict convention**: tape-verdict χ_L (Arora–Barak Def. 1.13; our default, motivated by
   Deterministic.lean's own "we do not make the halting state a member of the state type"
   design note) **vs** an accept/reject-states `Decider` structure mirroring the merged NTM's
   `accept`/`accept_halting`. We implement the former; the latter is a documented,
   considered-and-deferred alternative we are happy to switch to if maintainers prefer —
   before PR-2 lands, not after.
2. **Per-alphabet classes** `P Symbol : Set (Language Symbol)` (consistent with the
   `Language`/`Acceptor` culture — the NTM's `Acceptor` instance already yields
   `Language Symbol` for arbitrary `Symbol`) **vs** bitstring-only classes (#192's
   `List Bool → Bool` style). Related: should deciders get a `decidedLanguage`/`Acceptor`
   bridge, given the language is only defined relative to a deciding proof?
3. **Namespace/placement**: proposed `Cslib/Computability/Complexity/` with
   `namespace Cslib.Computability.Complexity` for classes and machine-attached lemmas in
   `Cslib.Turing.SingleTapeTM` for dot-notation. Note the existing split: Deterministic.lean
   uses `Cslib.Turing`, while Defs.lean/NonDeterministic.lean use
   `Cslib.Computability.Turing.SingleTape` — PR-1's lemmas follow the file they live in
   (`Cslib.Turing.SingleTapeTM`); we need an explicit ruling for the new files. Also: bare
   `P`/`NP` inside the namespace, or `ClassP`-style names?
4. **DTIME-first vs classes-first**: issue #611 proposes a DTIME/DSPACE ladder. We propose
   classes-first with `DTIME` as a 3-line PR-5 refactor (`P = ⋃ p, DTIME (p.eval ·)`), and ask
   whether #611's author (crei) wants DTIME in PR-2 instead.
5. **Certificate-length convention**: `≤ p.eval |x|` (our default) vs Arora–Barak's exact `=`,
   with the padding equivalence as a stated roadmap theorem either way.
6. **Sequencing with #396 and #192**: agree the rebase order for `TimeComputable.comp` (#396)
   and whether @BoltonBailey wants PR-1's private-lemma extraction folded into his plans or
   reviewed by him (preferred).
7. **NTM bridge obligation**: we name `NP_iff_NTIME` (verifier-NP ≡ NTM-NP over
   `SingleTapeNTM`) as the theorem that must exist before any NTM-defined class is added, and
   flag the missing finiteness constraints on `SingleTapeNTM.State`/`accept` — should those
   constraints be added to the NTM structure now?
8. **`Polynomial.eval_mono` on ℕ** is absent from Mathlib — OK to add locally in PR-4 with an
   upstream PR to Mathlib in parallel?
