# Risk register: PR-3/PR-4 draft files (Relabel.lean, WellFormed.lean, NP.lean)

Status: **DRAFT, not compiled** (no Lean toolchain in sandbox). All CSLib/Mathlib
identifiers were verified against the local sources; Lean-core identifiers (no core
sources available) are flagged below. No `sorry` anywhere; the single open obligation is
the named TODO `checkComputer_spec` (WellFormed.lean), consumed only through the
`CheckComputerSpec` hypothesis, so every stated theorem is fully proven.

## Architecture recap (what is proven vs. open)

- **Fully proven (draft-level):** `StackTape.map`/`BiTape.map` + commutation lemmas;
  `relabelComputer` + step-for-step simulation (via existing
  `Relation.RelatesWithinSteps.map`, verified at RelatesInSteps.lean:214) + out-of-range
  one-step halt; `checkComputer` definition + two sanity anchors (explicit 2-step good run
  and 4-step error run); StackTape normal-form helpers (`cons_none_nil`,
  `cons_head?_mapSome_tail`, …); `pairEncode` + `length`/`takeWhile`/`dropWhile`/
  `eq_iff`/`injective`; `NP` + `mem_NP_iff` + `bot_mem_NP`/`top_mem_NP`;
  `verifierComputer_decides`; `P_subset_NP_of_checkComputerSpec`.
- **Open (named TODO, no sorry):** `checkComputer_spec : CheckComputerSpec Symbol`
  (est. 250–350 lines; configuration invariants pinned in the WellFormed.lean comment:
  `tapeAt pre suf` mid-sweep shape, four phase lemmas by list induction, step counts
  2n+2 both paths). `P_subset_NP` unconditional = one line after that.
- **Deliberately absent:** monotonicity-in-`p` for NP (false as naively stated — enlarging
  the certificate bound can admit new accepting certificates; documented in NP.lean);
  padding (`≤` vs `=` certificate length) equivalence — stated TODO, never assumed;
  NP_iff_NTIME — roadmap only, blocked on SingleTapeNTM finiteness (State/accept
  unconstrained) + TrLabel step-granularity accounting.

## Elaboration risks (ranked)

1. **`rfl` transition steps** (`checkComputer_outputsWithinTime_nil`/`_inr`,
   `relabelComputer_outputsWithinTime_of_lower_eq_none`): rely on kernel reduction through
   nested matchers (`SingleTapeTM.step` → `tr` match → `BiTape.moveLeft/Right` →
   `StackTape.cons/head/tail` matches on structure literals) plus definitional proof
   irrelevance for the `StackTape` invariant field. Expected to work (all scrutinees are
   literal constructors); fallback: replace `rfl` with `by simp [step, checkComputer,
   BiTape.moveLeft, StackTape.cons, ...]` or `by decide`-free `show`+`simp` chains.
2. **simp-unfolding of `relabelComputer`'s nested `match` in
   `relabelComputer_transitionRelation`**: the proof mirrors CSLib's own
   `map_toCompCfg_left_step` (generalize `tm.tr q t.head`, destructure, case on head).
   Risk that `simp only [..., relabelComputer, hM, hgf a]` needs an extra `split`/`unfold`
   to reduce the inner match. Medium confidence; the CSLib precedent uses `grind` for the
   analogous step — `grind [relabelComputer, step]` is the fallback.
3. **Lean-core names unverifiable in sandbox** (used, believed current for v4.33):
   `List.takeWhile_cons`, `List.dropWhile_cons`, `List.getLast?_map`, `Option.map_none`,
   `Option.map_some`, `Sum.isLeft_inl`/`isLeft_inr` (in default simp set), `Nat.le_zero`.
   Verified against Mathlib usage (hence existing): `List.takeWhile_append_dropWhile`
   (Mathlib/Data/List/DropRight.lean:196), `List.length_eq_zero_iff`,
   `Option.map_eq_some_iff`/`map_eq_none_iff`, `Sum.inl_injective`/`inr_injective`
   (Mathlib/Data/Sum/Basic.lean:41/43), `Function.Injective.list_map`
   (Mathlib/Data/List/Basic.lean:740), `Bool.false_ne_true`. If `Option.map_none/map_some`
   are still primed (`map_none'`), swap names.
4. **`toRelabelCfg` typechecking** uses defeq `(relabelComputer f g tm).State ≡ tm.State`
   (structure-field unfolding). Under the module system the defs are in the same
   `@[expose] public section`, so exposure is not an issue.
5. **Set-builder at `Language`**: `verifierLanguage` uses `{ w | ... } : Language _` and
   `mem_verifierLanguage_iff := Iff.rfl`; `Language` is a semireducible def of
   `Set (List _)`. Mirrors how Defs.lean's `P` is defined; low risk. Fallback: `setOf`.
6. **`omega` with opaque atoms** (`p.eval x.length`): omega atomizes non-arithmetic
   subterms; the bound goals are linear in the atoms. `simp only [verifierTimePoly_eval,
   List.length_map]` is applied first so both sides share the same atom (used `simp only`,
   not `rw`, to beta-reduce the `fun n => …` time argument first).
7. **`Fintype CheckState`**: explicit `Finset` literal + `cases x <;> decide` — no
   dependence on the `deriving Fintype` handler (per must-fix 15). `decide` on
   `Finset` membership of a 4-element literal is safe.
8. **`pairEncode_takeWhile/dropWhile` induction**: depends on the exact core statement
   shape of `takeWhile_cons` (ite with Bool coercion). If the simp normal form differs,
   use `List.takeWhile_cons_of_pos/neg` instead.

## Same-length trick (no eval-monotonicity anywhere)

The simulated input `x.map Sum.inl` has *exactly* the outer input's length
(`List.length_map`), so `verifierComputer_decides` needs no `Polynomial.eval`
monotonicity lemma (verified absent from Mathlib). The planned `Polynomial.eval_mono`
helper is therefore NOT needed in PR-3/PR-4 as drafted; it remains queued (with an
upstream-to-Mathlib note) for the first PR that genuinely needs it (padding equivalence
or reductions).

## Design/process notes for the PRs

- **Blocker coverage:** B2 = `pairEncode_injective` + `pairEncode_eq_iff` +
  `pairEncode_length` (bounds in machine-determinable lengths); B3 = `NP` demands
  `V ∈ P`, i.e. a total two-sided `DecidesWithinTime` verifier — no one-sided acceptance
  anywhere; B5 = time is `OutputsWithinTime` throughout, composition is the existing
  `compComputer` via `compComputer_outputsWithinTime`, simulation transport is the
  existing `RelatesWithinSteps.map`; B6 = all bounds are `Polynomial ℕ` `.eval`;
  B7 = conditional-assembly structure keeps claims ≤ proofs (the only TODO is named,
  scoped, and consumed hypothetically).
- **Extra rules:** `P ⊆ NP` costs the real 3-machine pipeline; the certificate logic
  visibly uses injectivity (`Sum.inl_injective.list_map`) — no encoding degeneracy.
  Certificates are `List Bool` with the unary-degeneracy rationale in the `NP` docstring.
- **Grafts implemented:** `pairEncode_eq_iff` (textbook), NP non-vacuity in the defining
  PR (textbook), same-length trick (idiomatic), helpers-in-PR-3 (must-fix 21),
  `errSym`-out-of-range error path reusing the relabel stuck lemma.
- **Placement/namespace**: `StackTape.map`/`BiTape.map` and the StackTape helpers are
  written in `Complexity/` files but flagged for upstreaming into `Foundations/Data`;
  final call (and `Cslib.Computability.Complexity` namespace approval) is a pre-PR Zulip
  item. Machine transformer `relabelComputer` sits in `Cslib.Turing.SingleTapeTM`
  (parallel to `compComputer`); `checkComputer`/`verifierComputer` sit in
  `Cslib.Computability.Complexity` (parallel to `constComputer` in Defs.lean).
- **#396 coordination**: nothing here touches `TimeComputable.comp`/`h_mono`; only
  `compComputer_outputsWithinTime` (PR-1 extraction) is consumed, so these files survive
  #396 in either order.
- The `checkComputer` termination design avoids the classic bidirectional-tape trap (a
  machine cannot sense the left end): it turns around exactly once and only ever moves
  left over `some` cells, so the first blank read while moving left *is* the left end;
  the erased suffix disappears from the representation (`StackTape.cons_none_nil`),
  making both halting configurations on-the-nose `haltCfg` equalities. The 4-step
  `checkComputer_outputsWithinTime_inr` anchor exercises exactly this endgame.
