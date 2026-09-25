import Complexity.Uniform.V1.SequentialComposition

/-!
Surface pins for the Part A G2x generic half: the sequential composition `M₁.seq M₂` of two fixed
`UniformTM`s into one closed table.  Every public declaration is restated in full; `check_absorption`
bundles the three absorption facts the handoffs rest on, `check_seq_rows` the row equations.

The literal probe.  `writer` writes `some true` on a blank, moves right and accepts, and rejects in
place otherwise; `reader` writes `some false` on a blank and accepts in place, and rejects
otherwise; `term` starts in one of its own verdicts.  `check_seq_literal_probe` reduces the three
compositions by kernel computation: `pair = writer.seq reader` has six states, start `0`, accept
`4`, reject `5`, and on the empty word its control is the reader's start `3` after **one** step —
the writer's accepting step, routed, the zero-cost handoff made visible — and the composed accept
after two, while the one-bit word `true` rejects after one; `handed` and `refused` have *terminal*
left starts, so at step zero they already stand in the reader's start and in the composed reject.

Not here: no concrete Part A machine, clock or budget, no first-arrival theorem for any concrete
machine, and no `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation` or language-membership
statement about a composed machine. -/

namespace Pnp3.Tests.UniformV1SequentialCompositionSurfaceTests
open Complexity.Uniform.V1
def check_seqLeft (M₁ M₂ : UniformTM) :
    Fin M₁.stateCount → Fin (M₁.stateCount + M₂.stateCount) := M₁.seqLeft M₂
def check_seqRight (M₁ M₂ : UniformTM) :
    Fin M₂.stateCount → Fin (M₁.stateCount + M₂.stateCount) := M₁.seqRight M₂
def check_seqRoute (M₁ M₂ : UniformTM) :
    Fin M₁.stateCount → Fin (M₁.stateCount + M₂.stateCount) := M₁.seqRoute M₂
def check_seqRawStep (M₁ M₂ : UniformTM) :
    Fin (M₁.stateCount + M₂.stateCount) → Option Bool →
      Fin (M₁.stateCount + M₂.stateCount) × Option Bool × Move := M₁.seqRawStep M₂
def check_seq (M₁ M₂ : UniformTM) : UniformTM := M₁.seq M₂
def check_seqEmbedRouted (M₁ M₂ : UniformTM) {n B : Nat} :
    Config M₁.stateCount n B → Config (M₁.seq M₂).stateCount n B := M₁.seqEmbedRouted M₂
def check_seqEmbedRight (M₁ M₂ : UniformTM) {n B : Nat} :
    Config M₂.stateCount n B → Config (M₁.seq M₂).stateCount n B := M₁.seqEmbedRight M₂
/-- Configurations are determined by their three projections, restated in full. -/
theorem check_ext_parts {k n B : Nat} {c d : Config k n B} (hstate : c.state = d.state)
    (hhead : c.head = d.head) (htape : c.tape = d.tape) : c = d :=
  Config.ext_parts hstate hhead htape
/-- Absorption across time, restated in full: a verdict at `t` is the configuration at every
`T ≥ t`, and a non-verdict at `T` excludes both verdicts at every `t ≤ T`. -/
theorem check_absorption (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B) {t T : Nat} :
    ((M.run t c).state = M.accept → t ≤ T → M.run T c = M.run t c) ∧
      ((M.run t c).state = M.reject → t ≤ T → M.run T c = M.run t c) ∧
      ((M.run T c).state ≠ M.accept → (M.run T c).state ≠ M.reject → t ≤ T →
        (M.run t c).state ≠ M.accept ∧ (M.run t c).state ≠ M.reject) :=
  ⟨fun h hle => M.run_accept_of_le c h hle, fun h hle => M.run_reject_of_le c h hle,
    fun ha hr hle => M.no_terminal_of_le c ha hr t hle⟩

/-- Off the two terminals the public step is the raw row, restated in full. -/
theorem check_step_of_ne (M : UniformTM) {q : Fin M.stateCount} (ha : q ≠ M.accept)
    (hr : q ≠ M.reject) (s : Option Bool) : M.step q s = M.rawStep q s :=
  M.step_of_ne ha hr s
/-- The composed control, restated in full: state count, distinguished states, block injections,
disjointness and the three routing cases. -/
theorem check_seq_pins (M₁ M₂ : UniformTM) :
    (M₁.seq M₂).stateCount = M₁.stateCount + M₂.stateCount ∧
      (M₁.seq M₂).start = M₁.seqRoute M₂ M₁.start ∧
      (M₁.seq M₂).accept = M₁.seqRight M₂ M₂.accept ∧
      (M₁.seq M₂).reject = M₁.seqRight M₂ M₂.reject ∧
      (∀ q, (M₁.seqLeft M₂ q).val = q.val) ∧
      (∀ q, (M₁.seqRight M₂ q).val = M₁.stateCount + q.val) ∧
      Function.Injective (M₁.seqLeft M₂) ∧ Function.Injective (M₁.seqRight M₂) ∧
      (∀ p q, M₁.seqLeft M₂ p ≠ M₁.seqRight M₂ q) ∧
      M₁.seqRoute M₂ M₁.accept = M₁.seqRight M₂ M₂.start ∧
      M₁.seqRoute M₂ M₁.reject = M₁.seqRight M₂ M₂.reject ∧
      (∀ q, q ≠ M₁.accept → q ≠ M₁.reject → M₁.seqRoute M₂ q = M₁.seqLeft M₂ q) :=
  M₁.seq_pins M₂
/-- The two embeddings replace the control and nothing else: the six projection equations, and the
composed `initialConfig` as `M₁`'s own routed — every budget, every input, no hypothesis on
`M₁.start`. -/
theorem check_seqEmbed_pins (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B)
    (d : Config M₂.stateCount n B) (x : Bitstring n) :
    (M₁.seqEmbedRouted M₂ c).state = M₁.seqRoute M₂ c.state ∧
      (M₁.seqEmbedRouted M₂ c).head = c.head ∧ (M₁.seqEmbedRouted M₂ c).tape = c.tape ∧
      (M₁.seqEmbedRight M₂ d).state = M₁.seqRight M₂ d.state ∧
      (M₁.seqEmbedRight M₂ d).head = d.head ∧ (M₁.seqEmbedRight M₂ d).tape = d.tape ∧
      initialConfig (M₁.seq M₂) B x = M₁.seqEmbedRouted M₂ (initialConfig M₁ B x) :=
  ⟨M₁.seqEmbedRouted_state M₂ c, M₁.seqEmbedRouted_head M₂ c, M₁.seqEmbedRouted_tape M₂ c,
    M₁.seqEmbedRight_state M₂ d, M₁.seqEmbedRight_head M₂ d, M₁.seqEmbedRight_tape M₂ d,
    M₁.seq_initialConfig M₂ B x⟩
/-- Every row of the composed table, restated in full: the raw and the public left rows are the
routed `M₁` rows, the raw and the public right rows are the `M₂` rows re-embedded, and the public
step agrees with the raw table everywhere. -/
theorem check_seq_rows (M₁ M₂ : UniformTM) (p : Fin M₁.stateCount) (q : Fin M₂.stateCount)
    (r : Fin (M₁.seq M₂).stateCount) (s : Option Bool) :
    M₁.seqRawStep M₂ (M₁.seqLeft M₂ p) s =
        (M₁.seqRoute M₂ (M₁.step p s).1, (M₁.step p s).2.1, (M₁.step p s).2.2) ∧
      M₁.seqRawStep M₂ (M₁.seqRight M₂ q) s =
        (M₁.seqRight M₂ (M₂.step q s).1, (M₂.step q s).2.1, (M₂.step q s).2.2) ∧
      (M₁.seq M₂).step (M₁.seqLeft M₂ p) s =
        (M₁.seqRoute M₂ (M₁.step p s).1, (M₁.step p s).2.1, (M₁.step p s).2.2) ∧
      (M₁.seq M₂).step (M₁.seqRight M₂ q) s =
        (M₁.seqRight M₂ (M₂.step q s).1, (M₂.step q s).2.1, (M₂.step q s).2.2) ∧
      (M₁.seq M₂).step r s = (M₁.seq M₂).rawStep r s :=
  ⟨M₁.seqRawStep_left M₂ p s, M₁.seqRawStep_right M₂ q s, M₁.seq_step_left M₂ p s,
    M₁.seq_step_right M₂ q s, M₁.seq_step_eq_rawStep M₂ r s⟩
/-- One composed transition, restated in full: a right-embedded configuration takes an `M₂`
transition, and a routed-embedded configuration not in `M₁.accept` takes an `M₁` transition. -/
theorem check_seq_stepConfig (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B)
    (d : Config M₂.stateCount n B) (hna : c.state ≠ M₁.accept) :
    (M₁.seq M₂).stepConfig (M₁.seqEmbedRight M₂ d) = M₁.seqEmbedRight M₂ (M₂.stepConfig d) ∧
      (M₁.seq M₂).stepConfig (M₁.seqEmbedRouted M₂ c) =
        M₁.seqEmbedRouted M₂ (M₁.stepConfig c) :=
  ⟨M₁.seq_stepConfig_right M₂ d, M₁.seq_stepConfig_routed M₂ c hna⟩
/-- The right block runs `M₂`, restated in full: no hypothesis, every step count. -/
theorem check_seq_run_right (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₂.stateCount n B)
    (t : Nat) :
    (M₁.seq M₂).run t (M₁.seqEmbedRight M₂ c) = M₁.seqEmbedRight M₂ (M₂.run t c) :=
  M₁.seq_run_right M₂ c t

/-- The left block runs `M₁` until `M₁` first accepts, restated in full.  No hypothesis about
`M₁.reject` occurs: a rejection is absorbing on both sides. -/
theorem check_seq_run_left (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B)
    {T : Nat} (hwork : ∀ t, t < T → (M₁.run t c).state ≠ M₁.accept) :
    ∀ t, t ≤ T →
      (M₁.seq M₂).run t (M₁.seqEmbedRouted M₂ c) = M₁.seqEmbedRouted M₂ (M₁.run t c) :=
  M₁.seq_run_left M₂ c hwork

/-- The executed handoff, restated in full.  The first-arrival hypothesis is load-bearing: the
routed edge fires the first time `M₁` would accept, and the handoff costs no step. -/
theorem check_seq_handoff (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B)
    {T : Nat} (hwork : ∀ t, t < T → (M₁.run t c).state ≠ M₁.accept)
    (hacc : (M₁.run T c).state = M₁.accept) (s : Nat) :
    (M₁.seq M₂).run (T + s) (M₁.seqEmbedRouted M₂ c) =
      M₁.seqEmbedRight M₂ (M₂.run s ⟨M₂.start, (M₁.run T c).head, (M₁.run T c).tape⟩) :=
  M₁.seq_handoff M₂ c hwork hacc s

/-- The rejecting handoff, restated in full: no first-arrival hypothesis. -/
theorem check_seq_reject_handoff (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₁.stateCount n B) {T : Nat} (hrej : (M₁.run T c).state = M₁.reject) (s : Nat) :
    (M₁.seq M₂).run (T + s) (M₁.seqEmbedRouted M₂ c) =
      ⟨(M₁.seq M₂).reject, (M₁.run T c).head, (M₁.run T c).tape⟩ :=
  M₁.seq_reject_handoff M₂ c hrej s

/-! ### Independent literal reduction probe -/

/-- On a blank: write `some true`, move right, accept.  On anything else: reject in place. -/
private def writer : UniformTM where
  stateCount := 3
  start := ⟨0, by decide⟩
  accept := ⟨1, by decide⟩
  reject := ⟨2, by decide⟩
  accept_ne_reject := by decide
  rawStep := fun q s =>
    match q.val, s with
    | 0, none => (⟨1, by decide⟩, some true, .right)
    | 0, some b => (⟨2, by decide⟩, some b, .stay)
    | _, s => (q, s, .stay)

/-- On a blank: write `some false`, accept in place.  On anything else: reject in place. -/
private def reader : UniformTM where
  stateCount := 3
  start := ⟨0, by decide⟩
  accept := ⟨1, by decide⟩
  reject := ⟨2, by decide⟩
  accept_ne_reject := by decide
  rawStep := fun q s =>
    match q.val, s with
    | 0, none => (⟨1, by decide⟩, some false, .stay)
    | 0, some b => (⟨2, by decide⟩, some b, .stay)
    | _, s => (q, s, .stay)

/-- A start that is itself a terminal, which `UniformTM` permits: `term ⟨0,_⟩` starts in its own
accept, `term ⟨1,_⟩` in its own reject.  Either way its rows are unobservable. -/
private def term (i : Fin 2) : UniformTM :=
  ⟨2, i, ⟨0, by decide⟩, ⟨1, by decide⟩, by decide, fun q s => (q, s, .stay)⟩
private def pair : UniformTM := writer.seq reader
private def handed : UniformTM := (term ⟨0, by decide⟩).seq reader
private def refused : UniformTM := (term ⟨1, by decide⟩).seq reader
private def emptyWord : Bitstring 0 := fun i => Fin.elim0 i
private def oneWord : Bitstring 1 := fun _ => true

/-- **The composed run, reduced**, at budget `2`.  Empty word: after **one** step the reader's start
`3` — the writer's accepting step, routed — with `some true` at cell `0` and the head on `1`; after
two the composed accept with `some false` at cell `1`; step five shows it absorbing.  Word `true`:
the composed reject after one step, on cell `0`; step four shows it absorbing.  `handed` and
`refused` have the two *terminal* left starts.  `handed`'s composed start is the routed one, the
reader's start `2` and not the dead `seqLeft` copy of the left accept at `0`: it is in the right
block at step zero already, and in the composed accept one step later, no step spent crossing.
`refused`'s is the composed reject `4` at step zero, not the dead `seqLeft` copy of the left reject.
Each conjunct is a claim about its own literal machine and input only. -/
theorem check_seq_literal_probe :
    pair.stateCount = 6 ∧ pair.start.val = 0 ∧ pair.accept.val = 4 ∧ pair.reject.val = 5 ∧
    handed.stateCount = 5 ∧ handed.start.val = 2 ∧ handed.accept.val = 3 ∧
    refused.stateCount = 5 ∧ refused.start.val = 4 ∧ refused.reject.val = 4 ∧
    (handed.run 0 (initialConfig handed 2 emptyWord)).state.val = 2 ∧
    (handed.run 1 (initialConfig handed 2 emptyWord)).state = handed.accept ∧
    (refused.run 0 (initialConfig refused 2 emptyWord)).state = refused.reject ∧
    (pair.run 1 (initialConfig pair 2 emptyWord)).state.val = 3 ∧
    (pair.run 1 (initialConfig pair 2 emptyWord)).head.val = 1 ∧
    (pair.run 1 (initialConfig pair 2 emptyWord)).tape ⟨0, by decide⟩ = some true ∧
    (pair.run 2 (initialConfig pair 2 emptyWord)).state = pair.accept ∧
    (pair.run 2 (initialConfig pair 2 emptyWord)).head.val = 1 ∧
    (pair.run 2 (initialConfig pair 2 emptyWord)).tape ⟨1, by decide⟩ = some false ∧
    (pair.run 5 (initialConfig pair 2 emptyWord)).state = pair.accept ∧
    (pair.run 1 (initialConfig pair 2 oneWord)).state = pair.reject ∧
    (pair.run 1 (initialConfig pair 2 oneWord)).head.val = 0 ∧
    (pair.run 4 (initialConfig pair 2 oneWord)).state = pair.reject := by
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1SequentialCompositionSurfaceTests
