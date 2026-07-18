# Elaboration risk list for the PR-1/PR-2 Lean files

No Lean compiler is available in this sandbox; every proof below is believed complete, but
these are the spots where elaboration could plausibly diverge from the paper reasoning,
with concrete fallbacks. File paths are relative to
`out/write/lean/`.

## Cslib/Foundations/Data/BiTape.lean

1. **Transitive availability of `Option.some_injective` / `Function.Injective.list_map`.**
   Both verified to exist (Mathlib/Data/Option/Basic.lean:70, Mathlib/Data/List/Basic.lean:740)
   but BiTape.lean only imports them *transitively* (via `Mathlib.Computability.TuringMachine.Tape`).
   Fallback: add `public import Mathlib.Data.List.Basic` (and/or `Mathlib.Data.Option.Basic`);
   `lake shake` will confirm or prune.

2. **`StackTape.toList_injective` — `simp_all` after double `cases`.**
   Relies on simp proj-reducing `toList ⟨as, h⟩` and using auto-generated `StackTape.mk.injEq`
   (which drops the `Prop` field). Fallbacks, in order:
   `subst h` variants; `exact congrArg (fun l => (⟨l, ‹_›⟩ : StackTape Symbol)) h` (no);
   cleanest: `rintro ⟨as₁, h₁⟩ ⟨as₂, h₂⟩ h; dsimp at h; subst h; rfl`
   (after `dsimp`, `h : as₁ = as₂` and the goal closes by proof irrelevance);
   ultimate: `grind`.

3. **`StackTape.mapSome_injective` — `congrArg toList h` at type `l₁.map some = l₂.map some`.**
   Needs the unifier to delta-reduce `(mapSome l).toList`. Fallback:
   `have h' : l₁.map some = l₂.map some := by simpa [StackTape.mapSome] using congrArg toList h`.

4. **`mk₁_injective` — `simp [mk₁, nil] at hhead` / `simpa [mk₁] using this`.**
   Needs simp to unfold `mk₁` on constructor lists, rewrite `∅` to `nil` (via the existing
   `@[simp] empty_eq_nil`), unfold `nil` with the provided lemma, proj-reduce the structure
   literal, and close `none = some b` by `reduceCtorEq`. All standard; if the `nil` unfold
   misbehaves, add `empty_eq_nil, BiTape.nil` explicitly or use
   `cases l₁ <;> cases l₂ <;> simp_all [mk₁, nil]` followed by the `mapSome_injective` step.

## Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean

5. **`initCfg_injective`/`haltCfg_injective` — `have h' : BiTape.mk₁ l₁ = BiTape.mk₁ l₂ := congrArg Cfg.BiTape h`.**
   Needs `Cfg.BiTape (tm.initCfg l)` to defeq-reduce to `BiTape.mk₁ l` (delta of `initCfg`
   + proj-of-literal; should be accepted by `have`-ascription unification).
   Fallback: `simp only [initCfg, Cfg.mk.injEq, true_and] at h; exact BiTape.mk₁_injective h`
   — if `simp only` leaves the state conjunct `some tm.q₀ = some tm.q₀`, use full
   `simp [initCfg, Cfg.mk.injEq] at h`. Note `Cfg.BiTape` is the (unusually capitalized)
   field name from the existing structure.

6. **`transitionRelation_deterministic` — `intro` through `Relator.RightUnique` and the
   `have hᵢ' : tm.step c = some cᵢ := hᵢ` casts (delta of `TransitionRelation`).**
   `RightUnique` is a plain def with strict-implicit binders (Mathlib/Logic/Relator.lean:61),
   so `intro` should unfold it. Fallbacks: `unfold Relator.RightUnique` first;
   `simp only [TransitionRelation] at h₁ h₂` for the casts.

7. **`not_transitionRelation_haltCfg` — `simp [haltCfg] at h`.**
   Needs the `@[simp]` equations of `step` to reduce `tm.step ⟨none, _⟩` to `none`.
   Fallback (rfl-level): `have h' : (none : Option tm.Cfg) = some c := hstep;
   exact Option.noConfusion h'` — `tm.step (tm.haltCfg s)` is definitionally `none`.

8. **`outputs_unique` — passing `h₁ : tm.Outputs l l₁` where `ReflTransGen` is expected
   (`have`-ascription), and `tm.transitionRelation_deterministic` where
   `Relator.RightUnique` is expected.** Both are pure delta unfoldings; if the ascription
   is rejected, insert `simp only [Outputs] at h₁ h₂` (equation-lemma unfold).
   `ReflTransGen.total_of_right_unique` and `ReflTransGen.cases_head` verified at
   Mathlib/Logic/Relation.lean:498 and :489.

9. **`compComputer_outputsWithinTime` — final `exact` must identify the private
   `initialCfg tm1 tm2 a` / `finalCfg tm1 tm2 c` with
   `initCfg (compComputer tm1 tm2) a` / `haltCfg (compComputer tm1 tm2) c`.**
   Both are delta + proj reductions (`(compComputer tm1 tm2).q₀ ≡ Sum.inl tm1.q₀` is `rfl`,
   cf. the existing `compComputer_q₀_eq := rfl`). Fallback: mirror the incumbent proof —
   `simp only [OutputsWithinTime, initCfg, haltCfg, compComputer_q₀_eq] at h₁ h₂ ⊢` before
   the `exact`, or `refine RelatesWithinSteps.trans (comp_left_relatesWithinSteps _ _ _ _ _ h₁) ?_`
   stepwise.

10. **Refactored `TimeComputable.comp` — `RelatesWithinSteps.of_le h (...)` against a goal
    stated with `OutputsWithinTime` and `(g ∘ f) a`.** Delta + beta (`Function.comp_apply`
    is rfl). Fallback: prepend `simp only [OutputsWithinTime, Function.comp_apply]`.
    `Nat.add_le_add_left` signature assumed `(h : n ≤ m) (k) : k + n ≤ k + m` (core);
    if the argument order differs on the pinned toolchain, use `Nat.add_le_add le_rfl (h_mono ...)`
    or `by omega`-free `add_le_add_left`. This proof intentionally keeps the exact public
    signature (incl. `h_mono`) so it composes with PR #396's planned removal of `h_mono`.

## Cslib/Computability/Complexity/Defs.lean

11. **`Fintype (DecSym Symbol)` via `Fintype.ofEquiv (Symbol ⊕ Bool) (equivSum Symbol).symm`.**
    `Fintype.ofEquiv` verified (Mathlib/Data/Fintype/OfMap.lean:76), Sum instance verified
    (Mathlib/Data/Fintype/Sum.lean:27); imports added explicitly. `deriving Fintype` is the
    alternative to try at compile time (`Mathlib.Tactic.DeriveFintype`), not relied upon.

12. **`mapHeadComputer_outputsWithinTime` / `constComputer_outputsWithinTime` — the `rfl`s.**
    These check kernel-defeq through: `BiTape.mk₁` match reduction, the `EmptyCollection`
    instance (`∅ ↦ nil`), structure-update `write`, `optionMove`/`moveRight` unfolding,
    `StackTape.cons`'s match on `⟨[], _⟩` (proof fields are definitionally irrelevant), and
    `StackTape.head/tail/mapSome` reductions, plus `List.modifyHead` on `[]`/cons (rfl-level
    in core: `modifyHead_nil`/`modifyHead_cons` are proved by `rfl`). All reductions were
    traced by hand and land exactly on `haltCfg`/`initCfg` forms. If a `rfl` times out or
    fails on an instance projection, fallback:
    `simp [mapHeadComputer, constComputer, initCfg, haltCfg, BiTape.mk₁, BiTape.write,
    BiTape.optionMove, BiTape.moveRight, StackTape.cons, StackTape.head, StackTape.tail,
    StackTape.mapSome, TransitionRelation]` on the shown `step _ = some _` goal
    (possibly with `StackTape.eq_iff` + `Subtype`-style extension via `toList_injective`).

13. **`show (constComputer (Symbol := Symbol) b).step _ = some _` named-argument
    instantiation.** `Symbol` is a section-variable-turned-implicit; `(Symbol := Symbol)`
    should be accepted. Fallback: type-ascribe instead:
    `show ((constComputer b : SingleTapeTM (DecSym Symbol))).step _ = some _`.

14. **`hc : x ∈ Lᶜ ↔ x ∉ L := Iff.rfl` (in `DecidesWithinTime.compl`).**
    Relies on `Language`'s derived `CompleteAtomicBooleanAlgebra` being definitionally the
    `Set` instance. Fallback: `Set.mem_compl_iff L x` (with `L` used at `Set (List Symbol)`),
    or `by simp [Language, Set.mem_compl_iff]`-style, or add a one-line
    `Language.mem_compl_iff` helper (upstream candidate).

15. **`Set.notMem_empty x : x ∉ (⊥ : Language Symbol)` and
    `Set.mem_univ x : x ∈ (⊤ : Language Symbol)` (in `bot_mem_P`/`top_mem_P`).**
    Same derived-instance defeq assumption (`⊥ ≡ ∅`, `⊤ ≡ univ` for `Set`, both `rfl` in
    Mathlib). Fallbacks: `fun h => h` for `⊥` (membership reduces to `False`) and
    `trivial` for `⊤`; or `Set.bot_eq_empty ▸ …` after a `show` to the `Set` type.

16. **Small simp closures.** (a) `simpa using hout` in `language_eq` needs
    `List.cons.injEq` + `DecSym.verdict.injEq` (auto-generated, simp-available);
    fallback `injection hout with h1 _; injection h1 with h2; exact h2`.
    (b) `cases b <;> simp` in `compl` needs `Bool.not_false/not_true` + `reduceCtorEq`;
    fallback `decide`-style `by cases b <;> simp [Bool.not_eq_true]` or explicit `constructor`.
    (c) `simp` for `p.eval n + 1 ≤ (p + 1).eval n` and `x.length + 1 ≤ (X + 1).eval x.length`
    uses `@[simp] eval_add/eval_one/eval_X` (verified) + `le_refl`;
    fallback `simp [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]`.
    (d) `simp [hx]` for the `⊥`/`⊤` verdict iffs needs `reduceCtorEq` on `false = true`;
    fallback explicit `constructor <;> intro h <;> simp_all`.

17. **`rintro`/`refine ⟨…⟩` through `Set`-membership of `P`.** Standard whnf-through-`setOf`
    behavior; if it balks, rewrite with `mem_P_iff` (provided as `Iff.rfl`) first.

18. **`open Computability.Complexity` inside `namespace Cslib.Turing.SingleTapeTM`** resolves
    relative to `Cslib`; if name resolution surprises, use the absolute
    `open Cslib.Computability.Complexity`.

19. **Linters, not proofs:** new file must be added to `Cslib.lean` (`lake exe mk_all`);
    `lake shake` may prune `Mathlib.Data.Fintype.OfMap`/`Sum` if transitively implied;
    docstring linter requires doc comments on the two anonymous instances only if CSLib's
    lint set demands them (existing CSLib files leave instances undocumented, so this
    matches house style); `Polynomial.eval` being noncomputable is harmless (all uses are
    in `Prop`).

20. **Statement-level convention flags for review (not compile risks):**
    `DecidesWithinTime` lives in `Cslib.Turing.SingleTapeTM` (dot-notation) while classes
    live in `Cslib.Computability.Complexity` — the namespace split must be confirmed on
    Zulip before PR; `P`/`coP` bare names inside the `Complexity` namespace likewise.
