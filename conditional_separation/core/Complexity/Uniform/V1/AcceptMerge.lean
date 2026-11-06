import Complexity.Uniform.V1.SequentialComposition

/-!
# Merging a second successful endpoint into `accept` (Part A G3g, generic half)

A **table transformation**, not a machine.  `M.mergeAccept e` keeps the states and both verdicts of
`M`; its start and each raw row have a target `e` retargeted to `M.accept` (`mergeState`), and
nothing else changes — every written symbol and move is `M`'s, every row not targeting `e` is `M`'s
verbatim.  With `e` neither verdict of `M` it becomes a **dead index**: no row of the merged public
step targets it and no merged run out of a merged configuration is ever in it
(`mergeAccept_step_ne`, `mergeAccept_run_ne`).

`mergeState`, `mergeAccept` and `mergeConfig` retarget **whatever** index they are handed, no case
hidden: at `e = M.reject` they retarget `M`'s *rejecting raw* rows to `M.accept` as well, so no
merged raw row targets the merged `reject` at all.  Every theorem that reads `e` as a **second success**
therefore carries `e ≠ M.reject`.  `mergeAccept_step`, `mergeAccept_step_ne`, `mergeAccept_run_ne`
and `mergeAccept_seq_reject_handoff` consume it in the proof; in `mergeAccept_run_accept` and
`mergeAccept_seq_handoff` it is a **scope guard** the proof does not use — the equations hold for
any `e`, and `mergeAccept_run` with `mergeConfig_pins` still states them unrestrictedly — that
excludes the one instantiation under which they would be *read* wrongly, `e := M.reject`, where
`mergeAccept_seq_handoff` would send a first *rejection* of `M₁` into `M₂.start`.  The purely
simulational `mergeAccept_stepConfig`, `mergeAccept_run`, `mergeAccept_run_ne_accept` and
`mergeAccept_seq_run_left` say nothing about the merged endpoint's meaning and carry no guard.

Purpose.  `UniformTM.seq` routes the left machine's `accept` and `reject` and nothing else, so a
left machine with a *second* absorbing successful endpoint `e` — G2k's payload dispatcher, whose
`qHasOne` is absorbing but neither verdict — would stick in `e` inside the left block.
`(M.mergeAccept e).seq M₂` routes both endpoints into `M₂.start` in the same transition; row for
row it is the table a bespoke two-success-source combinator would produce, and every landed `seq`
lemma is reused unchanged (`mergeAccept_seq_handoff` is `seq_handoff` for the merged left machine,
`mergeAccept_seq_reject_handoff` is `seq_reject_handoff`).  The verdict `e` is **not** preserved —
an `M` run ending in `e` and one ending in `M.accept` are indistinguishable after the merge — while
`mergeAccept_run` preserves head and tape at every time up to `T`.

No concrete machine, input, budget or clock occurs here, no run theorem about any concrete machine
lives here, and no `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation` or
language-membership fact is stated.  Classification (AGENTS.md): **Infrastructure**. -/

namespace Pnp3.Complexity.Uniform.V1

/-- Retarget one state: `e` becomes `M.accept`, every other state is itself. -/
def UniformTM.mergeState (M : UniformTM) (e q : Fin M.stateCount) : Fin M.stateCount :=
  if q = e then M.accept else q

/-- The merged table: `M`'s states and verdicts, `M`'s start and every raw row with a target `e`
retargeted to `M.accept`.  Written symbols and moves are untouched.  `e` is unrestricted here: at
`e = M.reject` the rejecting rows are retargeted too (see the module note). -/
def UniformTM.mergeAccept (M : UniformTM) (e : Fin M.stateCount) : UniformTM where
  stateCount := M.stateCount
  start := M.mergeState e M.start
  accept := M.accept
  reject := M.reject
  accept_ne_reject := M.accept_ne_reject
  rawStep := fun q s =>
    (M.mergeState e (M.rawStep q s).1, (M.rawStep q s).2.1, (M.rawStep q s).2.2)

/-- An `M` configuration in the merged control: the state merged, head and tape kept. -/
def UniformTM.mergeConfig (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) : Config (M.mergeAccept e).stateCount n B :=
  ⟨M.mergeState e c.state, c.head, c.tape⟩

/-! ### The retargeting map -/

theorem UniformTM.mergeState_self (M : UniformTM) (e : Fin M.stateCount) :
    M.mergeState e e = M.accept := by
  simp [UniformTM.mergeState]

theorem UniformTM.mergeState_of_ne (M : UniformTM) {e q : Fin M.stateCount} (h : q ≠ e) :
    M.mergeState e q = q := by
  simp [UniformTM.mergeState, h]

theorem UniformTM.mergeState_accept (M : UniformTM) (e : Fin M.stateCount) :
    M.mergeState e M.accept = M.accept := by
  unfold UniformTM.mergeState
  split <;> rfl

/-- With `e ≠ M.accept`, no state is retargeted onto `e`. -/
theorem UniformTM.mergeState_ne (M : UniformTM) (e : Fin M.stateCount) (ha : e ≠ M.accept)
    (q : Fin M.stateCount) : M.mergeState e q ≠ e := by
  unfold UniformTM.mergeState
  split
  · exact Ne.symm ha
  · assumption

/-! ### Table pins -/

/-- The merged table, pinned: the state count, the start, the two verdicts, and every raw row as
the `M` raw row with its target merged. -/
theorem UniformTM.mergeAccept_pins (M : UniformTM) (e : Fin M.stateCount) :
    (M.mergeAccept e).stateCount = M.stateCount ∧
      (M.mergeAccept e).start = M.mergeState e M.start ∧
      (M.mergeAccept e).accept = M.accept ∧ (M.mergeAccept e).reject = M.reject ∧
      (∀ q s, (M.mergeAccept e).rawStep q s =
        (M.mergeState e (M.rawStep q s).1, (M.rawStep q s).2.1, (M.rawStep q s).2.2)) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The merged embedding replaces the control and nothing else; a configuration in `e` or in
`M.accept` embeds into the merged `accept`, one off `e` keeps its state. -/
theorem UniformTM.mergeConfig_pins (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) :
    (M.mergeConfig e c).state = M.mergeState e c.state ∧
      (M.mergeConfig e c).head = c.head ∧ (M.mergeConfig e c).tape = c.tape ∧
      (c.state = e ∨ c.state = M.accept →
        (M.mergeConfig e c).state = (M.mergeAccept e).accept) ∧
      (c.state ≠ e → (M.mergeConfig e c).state = c.state) := by
  refine ⟨rfl, rfl, rfl, fun h => ?_, fun h => M.mergeState_of_ne h⟩
  show M.mergeState e c.state = M.accept
  rcases h with h | h <;> rw [h]
  · exact M.mergeState_self e
  · exact M.mergeState_accept e

/-! ### Rows of the merged public step -/

/-- Off the two verdicts, the merged public step is the `M` public step with its target merged. -/
theorem UniformTM.mergeAccept_step_of_ne (M : UniformTM) (e : Fin M.stateCount)
    {q : Fin M.stateCount} (ha : q ≠ M.accept) (hr : q ≠ M.reject) (s : Option Bool) :
    (M.mergeAccept e).step q s =
      (M.mergeState e (M.step q s).1, (M.step q s).2.1, (M.step q s).2.2) := by
  rw [UniformTM.step_of_ne M ha hr]
  exact UniformTM.step_of_ne (M.mergeAccept e) ha hr s

/-- **Every row** of the merged public step is the `M` public row with its target merged, once
`e ≠ M.reject`: on the two verdicts both steps absorb, and both verdicts are fixed. -/
theorem UniformTM.mergeAccept_step (M : UniformTM) (e : Fin M.stateCount) (he : e ≠ M.reject)
    (q : Fin M.stateCount) (s : Option Bool) :
    (M.mergeAccept e).step q s =
      (M.mergeState e (M.step q s).1, (M.step q s).2.1, (M.step q s).2.2) := by
  by_cases ha : q = M.accept
  · subst ha
    rw [UniformTM.step_accept, M.mergeState_accept]
    exact UniformTM.step_accept (M.mergeAccept e) s
  · by_cases hr : q = M.reject
    · subst hr
      rw [UniformTM.step_reject, M.mergeState_of_ne (Ne.symm he)]
      exact UniformTM.step_reject (M.mergeAccept e) s
    · exact M.mergeAccept_step_of_ne e ha hr s

/-- **`e` is a dead index**: with `e` neither verdict of `M`, no merged row targets it. -/
theorem UniformTM.mergeAccept_step_ne (M : UniformTM) (e : Fin M.stateCount) (ha : e ≠ M.accept)
    (hr : e ≠ M.reject) (q : Fin M.stateCount) (s : Option Bool) :
    ((M.mergeAccept e).step q s).1 ≠ e := by
  rw [M.mergeAccept_step e hr q s]
  exact M.mergeState_ne e ha _

/-! ### Simulation -/

/-- One merged transition out of a merged configuration not in `e` is one `M` transition,
re-embedded; on `M`'s two verdicts both sides absorb. -/
theorem UniformTM.mergeAccept_stepConfig (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) (hne : c.state ≠ e) :
    (M.mergeAccept e).stepConfig (M.mergeConfig e c) = M.mergeConfig e (M.stepConfig c) := by
  by_cases ha : c.state = M.accept
  · have h1 : (M.mergeConfig e c).state = (M.mergeAccept e).accept := by
      show M.mergeState e c.state = M.accept
      rw [ha]
      exact M.mergeState_accept e
    rw [UniformTM.stepConfig_accept _ _ h1, UniformTM.stepConfig_accept _ _ ha]
  · by_cases hr : c.state = M.reject
    · have h1 : (M.mergeConfig e c).state = (M.mergeAccept e).reject := by
        show M.mergeState e c.state = M.reject
        rw [M.mergeState_of_ne hne]
        exact hr
      rw [UniformTM.stepConfig_reject _ _ h1, UniformTM.stepConfig_reject _ _ hr]
    · cases c with
      | mk q h t =>
          change q ≠ e at hne
          change q ≠ M.accept at ha
          change q ≠ M.reject at hr
          simp only [UniformTM.stepConfig, UniformTM.mergeConfig]
          rw [M.mergeState_of_ne hne, M.mergeAccept_step_of_ne e ha hr]

/-- **The merged run is the `M` run re-embedded** up to and including `T`, provided the `M` run is
not in `e` strictly before `T`. -/
theorem UniformTM.mergeAccept_run (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) {T : Nat} (hwork : ∀ t, t < T → (M.run t c).state ≠ e) :
    ∀ t, t ≤ T → (M.mergeAccept e).run t (M.mergeConfig e c) = M.mergeConfig e (M.run t c) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [UniformTM.run, ih (by omega), M.mergeAccept_stepConfig e _ (hwork t (by omega)),
        UniformTM.run]

/-- **`e` is unreachable**: with `e` neither verdict, no merged run out of a merged configuration
is in `e` at any time. -/
theorem UniformTM.mergeAccept_run_ne (M : UniformTM) (e : Fin M.stateCount) (ha : e ≠ M.accept)
    (hr : e ≠ M.reject) {n B : Nat} (c : Config M.stateCount n B) (t : Nat) :
    ((M.mergeAccept e).run t (M.mergeConfig e c)).state ≠ e := by
  cases t with
  | zero => exact M.mergeState_ne e ha c.state
  | succ t =>
      show ((M.mergeAccept e).stepConfig ((M.mergeAccept e).run t (M.mergeConfig e c))).state ≠ e
      exact M.mergeAccept_step_ne e ha hr _ _

/-- **Both successful endpoints read back as the merged `accept`**, on the head and tape the `M`
run has at `T`; which of the two `M` reached is not recoverable.  `e ≠ M.reject` is the scope guard
that makes `e` a second *success*: unused by the proof, it keeps out `e := M.reject`, which would
read a first rejection back as an accept.  `mergeAccept_run` states the equation for any `e`. -/
theorem UniformTM.mergeAccept_run_accept (M : UniformTM) (e : Fin M.stateCount)
    (_hr : e ≠ M.reject) {n B : Nat}
    (c : Config M.stateCount n B) {T : Nat} (hwork : ∀ t, t < T → (M.run t c).state ≠ e)
    (hT : (M.run T c).state = e ∨ (M.run T c).state = M.accept) :
    (M.mergeAccept e).run T (M.mergeConfig e c) =
      ⟨(M.mergeAccept e).accept, (M.run T c).head, (M.run T c).tape⟩ := by
  rw [M.mergeAccept_run e c hwork T le_rfl]
  exact Config.ext_parts ((M.mergeConfig_pins e _).2.2.2.1 hT) rfl rfl

/-- No merged accept before `T` if `M` is in neither `e` nor `M.accept` before `T`: the
`seq_run_left` premise for the merged machine. -/
theorem UniformTM.mergeAccept_run_ne_accept (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M.run t c).state ≠ e ∧ (M.run t c).state ≠ M.accept) :
    ∀ t, t < T → ((M.mergeAccept e).run t (M.mergeConfig e c)).state ≠ (M.mergeAccept e).accept := by
  intro t ht
  rw [M.mergeAccept_run e c (fun t ht => (hwork t ht).1) t (Nat.le_of_lt ht)]
  show M.mergeState e (M.run t c).state ≠ M.accept
  rw [M.mergeState_of_ne (hwork t ht).1]
  exact (hwork t ht).2

/-! ### Composition with `seq` -/

/-- **The merged left block of a composition runs `M₁`**, routed, up to and including `T`, as long
as `M₁` is in neither `e` nor `M₁.accept` before `T`. -/
theorem UniformTM.mergeAccept_seq_run_left (M₁ M₂ : UniformTM) (e : Fin M₁.stateCount) {n B : Nat}
    (c : Config M₁.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M₁.run t c).state ≠ e ∧ (M₁.run t c).state ≠ M₁.accept) :
    ∀ t, t ≤ T →
      ((M₁.mergeAccept e).seq M₂).run t
          ((M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e c)) =
        (M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e (M₁.run t c)) := by
  intro t ht
  rw [(M₁.mergeAccept e).seq_run_left M₂ _ (M₁.mergeAccept_run_ne_accept e c hwork) t ht,
    M₁.mergeAccept_run e c (fun t ht => (hwork t ht).1) t ht]

/-- **The two-success-source handoff.**  If the `M₁` run is in `e` or in `M₁.accept` at `T` and in
neither before `T`, the composed run is, at `T + s`, the `M₂` run of `s` steps out of `M₂.start` on
the head and tape `M₁` left at `T` — whichever endpoint `M₁` reached.  First arrival is
load-bearing, now against both endpoints at once.  `e ≠ M₁.reject` is the scope guard that makes
`e` a second *success*: handed on to `mergeAccept_run_accept`, which does not consume it either, it
keeps out `e := M₁.reject`, under which this equation would route a first *rejection* of `M₁` into
`M₂.start` instead of the composed reject `mergeAccept_seq_reject_handoff` gives. -/
theorem UniformTM.mergeAccept_seq_handoff (M₁ M₂ : UniformTM) (e : Fin M₁.stateCount) {n B : Nat}
    (c : Config M₁.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M₁.run t c).state ≠ e ∧ (M₁.run t c).state ≠ M₁.accept)
    (hT : (M₁.run T c).state = e ∨ (M₁.run T c).state = M₁.accept) (he : e ≠ M₁.reject) (s : Nat) :
    ((M₁.mergeAccept e).seq M₂).run (T + s)
        ((M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e c)) =
      (M₁.mergeAccept e).seqEmbedRight M₂
        (M₂.run s ⟨M₂.start, (M₁.run T c).head, (M₁.run T c).tape⟩) := by
  have hacc := M₁.mergeAccept_run_accept e he c (fun t ht => (hwork t ht).1) hT
  have hstate : ((M₁.mergeAccept e).run T (M₁.mergeConfig e c)).state =
      (M₁.mergeAccept e).accept := by
    rw [hacc]
  have h := (M₁.mergeAccept e).seq_handoff M₂ _ (M₁.mergeAccept_run_ne_accept e c hwork) hstate s
  rw [hacc] at h
  exact h

/-- **The rejecting handoff through the merge**: `M₁` rejecting at `T`, not in `e` before, gives
the composed reject from `T` on; `e ≠ M₁.reject` keeps `M₁.reject` fixed by the retargeting. -/
theorem UniformTM.mergeAccept_seq_reject_handoff (M₁ M₂ : UniformTM) (e : Fin M₁.stateCount)
    {n B : Nat} (c : Config M₁.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M₁.run t c).state ≠ e) (hrej : (M₁.run T c).state = M₁.reject)
    (he : e ≠ M₁.reject) (s : Nat) :
    ((M₁.mergeAccept e).seq M₂).run (T + s)
        ((M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e c)) =
      ⟨((M₁.mergeAccept e).seq M₂).reject, (M₁.run T c).head, (M₁.run T c).tape⟩ := by
  have hmr := M₁.mergeAccept_run e c hwork T le_rfl
  have hr : ((M₁.mergeAccept e).run T (M₁.mergeConfig e c)).state = (M₁.mergeAccept e).reject := by
    rw [hmr]
    show M₁.mergeState e (M₁.run T c).state = M₁.reject
    rw [hrej]
    exact M₁.mergeState_of_ne (Ne.symm he)
  have h := (M₁.mergeAccept e).seq_reject_handoff M₂ _ hr s
  rw [hmr] at h
  exact h

end Pnp3.Complexity.Uniform.V1
