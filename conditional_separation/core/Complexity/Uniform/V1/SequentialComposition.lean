import Complexity.Uniform.V1.Machine

/-!
# Sequential composition of two fixed `UniformTM`s (Part A G2x, generic half)

One closed finite table out of two.  `M₁.seq M₂` has `M₁.stateCount + M₂.stateCount` states — those
of `M₁` at their own indices (`seqLeft`), those of `M₂` shifted past them (`seqRight`) — and its raw
table is the disjoint union of the two public step functions with every `M₁` row **routed** through
`seqRoute`: a target `M₁.accept` becomes `M₂.start` *in that same transition*, a target `M₁.reject`
becomes the composed reject, every other target stays left.  This is the routed-edge handoff of the
P2-3cB2 parser/verifier constructor (`CombinedMachine.lean`, `routeParserState`) with the left
component made generic; as there, the handoff costs **zero** steps, and routing inspects the target
state of a row and nothing else.  The **start** is routed too, so `seq_initialConfig` reads
`initialConfig (M₁.seq M₂)` as `initialConfig M₁` routed with no hypothesis on `M₁.start`: a
*terminal* start, which `UniformTM` permits, hands over at time zero, not one step late.  The two
`seqLeft` terminal copies stay dead: no routed row or start targets them.

`seq_run_right`: out of a right-embedded configuration the composed run is the `M₂` run, with no
hypothesis.  `seq_run_left`: out of a routed embedding it is the `M₁` run up to `T`, provided `M₁`
does not accept strictly before `T`; an `M₁` rejection needs no hypothesis, since both machines
absorb it.  `seq_handoff`: if `M₁` accepts **for the first time** at `T`, the composed run at `T + s`
is the `M₂` run of `s` steps out of `M₂.start` on the head and tape `M₁` left.  First arrival is
load-bearing, not a persistence fact.  `seq_reject_handoff` needs no first-arrival hypothesis.

No concrete machine, input, parser, budget or clock occurs here, and no `AcceptsAt`,
`DecidesWithin`, `UniformP`, `VerifiesRelation` or language-membership fact about a composed machine
is proved: reaching `(M₁.seq M₂).accept` is reaching `M₂.accept` inside the composed control.
Classification (AGENTS.md): **Infrastructure**. -/

namespace Pnp3.Complexity.Uniform.V1

/-- Two configurations with the same three projections are equal (`Machine.lean` keeps its copy
private). -/
theorem Config.ext_parts {k n B : Nat} {c d : Config k n B} (hstate : c.state = d.state)
    (hhead : c.head = d.head) (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
      cases d with
      | mk ds dh dt =>
          change cs = ds at hstate; change ch = dh at hhead; change ct = dt at htape
          subst ds; subst dh; subst dt; rfl

/-! ### Absorption across time, for one machine -/

/-- A configuration in `M.accept` at time `t` is the configuration at every later time. -/
theorem UniformTM.run_accept_of_le (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B)
    {t T : Nat} (h : (M.run t c).state = M.accept) (hle : t ≤ T) : M.run T c = M.run t c := by
  rw [show T = t + (T - t) by omega, UniformTM.run_add]
  exact M.run_accept _ h _

/-- A configuration in `M.reject` at time `t` is the configuration at every later time. -/
theorem UniformTM.run_reject_of_le (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B)
    {t T : Nat} (h : (M.run t c).state = M.reject) (hle : t ≤ T) : M.run T c = M.run t c := by
  rw [show T = t + (T - t) by omega, UniformTM.run_add]
  exact M.run_reject _ h _

/-- **No verdict before a non-verdict.**  A configuration in neither terminal state at `T` was in
neither at any earlier time: a verdict entered earlier would have absorbed. -/
theorem UniformTM.no_terminal_of_le (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B)
    {T : Nat} (ha : (M.run T c).state ≠ M.accept) (hr : (M.run T c).state ≠ M.reject) :
    ∀ t, t ≤ T → (M.run t c).state ≠ M.accept ∧ (M.run t c).state ≠ M.reject :=
  fun t ht => ⟨fun h => ha (by rw [M.run_accept_of_le c h ht]; exact h),
    fun h => hr (by rw [M.run_reject_of_le c h ht]; exact h)⟩

/-- Off the two terminal states the public step is the raw row. -/
theorem UniformTM.step_of_ne (M : UniformTM) {q : Fin M.stateCount} (ha : q ≠ M.accept)
    (hr : q ≠ M.reject) (s : Option Bool) : M.step q s = M.rawStep q s := by
  simp [UniformTM.step, ha, hr]

/-! ### The composed control -/

/-- Left block: the states of `M₁`, at their own indices. -/
def UniformTM.seqLeft (M₁ M₂ : UniformTM) (q : Fin M₁.stateCount) :
    Fin (M₁.stateCount + M₂.stateCount) :=
  ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ _)⟩

/-- Right block: the states of `M₂`, shifted past the whole of `M₁`. -/
def UniformTM.seqRight (M₁ M₂ : UniformTM) (q : Fin M₂.stateCount) :
    Fin (M₁.stateCount + M₂.stateCount) :=
  ⟨M₁.stateCount + q.val, Nat.add_lt_add_left q.isLt _⟩

/-- Route the target of an `M₁` row: `M₁.accept` becomes `M₂.start`, `M₁.reject` becomes
`M₂.reject`, every other target stays left.  This inspects a state and nothing else. -/
def UniformTM.seqRoute (M₁ M₂ : UniformTM) (q : Fin M₁.stateCount) :
    Fin (M₁.stateCount + M₂.stateCount) :=
  if q = M₁.accept then M₁.seqRight M₂ M₂.start
  else if q = M₁.reject then M₁.seqRight M₂ M₂.reject
  else M₁.seqLeft M₂ q

/-- The composed raw table: the routed `M₁` rows on the left block, the `M₂` rows on the right.
Calling `M₁.step` or `M₂.step` here constructs one row of a finite table; it is not a run. -/
def UniformTM.seqRawStep (M₁ M₂ : UniformTM) (q : Fin (M₁.stateCount + M₂.stateCount))
    (s : Option Bool) : Fin (M₁.stateCount + M₂.stateCount) × Option Bool × Move :=
  if h : q.val < M₁.stateCount then
    let a := M₁.step ⟨q.val, h⟩ s
    (M₁.seqRoute M₂ a.1, a.2.1, a.2.2)
  else
    let a := M₂.step ⟨q.val - M₁.stateCount, by have := q.isLt; omega⟩ s
    (M₁.seqRight M₂ a.1, a.2.1, a.2.2)

theorem UniformTM.seqLeft_injective (M₁ M₂ : UniformTM) : Function.Injective (M₁.seqLeft M₂) := by
  intro p q h
  have hv : (M₁.seqLeft M₂ p).val = (M₁.seqLeft M₂ q).val := congrArg Fin.val h
  exact Fin.ext hv

theorem UniformTM.seqRight_injective (M₁ M₂ : UniformTM) : Function.Injective (M₁.seqRight M₂) := by
  intro p q h
  have hv : M₁.stateCount + p.val = M₁.stateCount + q.val := congrArg Fin.val h
  exact Fin.ext (by omega)
theorem UniformTM.seqLeft_ne_seqRight (M₁ M₂ : UniformTM) (p : Fin M₁.stateCount)
    (q : Fin M₂.stateCount) : M₁.seqLeft M₂ p ≠ M₁.seqRight M₂ q := fun h => by
  have hv : p.val = M₁.stateCount + q.val := congrArg Fin.val h
  have := p.isLt
  omega

/-- The sequential composition: `M₁`'s start **routed**, `M₂`'s verdicts, the routed union table. -/
def UniformTM.seq (M₁ M₂ : UniformTM) : UniformTM where
  stateCount := M₁.stateCount + M₂.stateCount
  start := M₁.seqRoute M₂ M₁.start
  accept := M₁.seqRight M₂ M₂.accept
  reject := M₁.seqRight M₂ M₂.reject
  accept_ne_reject := fun h => M₂.accept_ne_reject (M₁.seqRight_injective M₂ h)
  rawStep := M₁.seqRawStep M₂

/-- An `M₁` configuration in the composed control, with its state routed: how a composed run
*starts* on an `M₁` configuration, and what keeps the two dead states unoccupied. -/
def UniformTM.seqEmbedRouted (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B) :
    Config (M₁.seq M₂).stateCount n B :=
  ⟨M₁.seqRoute M₂ c.state, c.head, c.tape⟩

/-- An `M₂` configuration in the composed control. -/
def UniformTM.seqEmbedRight (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₂.stateCount n B) :
    Config (M₁.seq M₂).stateCount n B :=
  ⟨M₁.seqRight M₂ c.state, c.head, c.tape⟩

/-! ### Table pins -/

/-- The composed control, pinned: the state count, the three distinguished states, the two
block injections with their disjointness, and the three routing cases. -/
theorem UniformTM.seq_pins (M₁ M₂ : UniformTM) :
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
      (∀ q, q ≠ M₁.accept → q ≠ M₁.reject → M₁.seqRoute M₂ q = M₁.seqLeft M₂ q) := by
  refine ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, M₁.seqLeft_injective M₂,
    M₁.seqRight_injective M₂, M₁.seqLeft_ne_seqRight M₂, ?_, ?_, fun q ha hr => ?_⟩
  · simp [UniformTM.seqRoute]
  · simp [UniformTM.seqRoute, M₁.accept_ne_reject.symm]
  · simp [UniformTM.seqRoute, ha, hr]

theorem UniformTM.seqEmbedRouted_state (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₁.stateCount n B) :
    (M₁.seqEmbedRouted M₂ c).state = M₁.seqRoute M₂ c.state := rfl
theorem UniformTM.seqEmbedRouted_head (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₁.stateCount n B) : (M₁.seqEmbedRouted M₂ c).head = c.head := rfl
theorem UniformTM.seqEmbedRouted_tape (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₁.stateCount n B) : (M₁.seqEmbedRouted M₂ c).tape = c.tape := rfl
theorem UniformTM.seqEmbedRight_state (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₂.stateCount n B) :
    (M₁.seqEmbedRight M₂ c).state = M₁.seqRight M₂ c.state := rfl
theorem UniformTM.seqEmbedRight_head (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₂.stateCount n B) : (M₁.seqEmbedRight M₂ c).head = c.head := rfl
theorem UniformTM.seqEmbedRight_tape (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₂.stateCount n B) : (M₁.seqEmbedRight M₂ c).tape = c.tape := rfl

/-- **A composed `initialConfig` is `M₁`'s, routed.**  For every budget and input, and with no
hypothesis on `M₁.start`: a working `M₁.start` begins on the left block, and a *terminal* one —
legal for a `UniformTM` — begins already handed over, at time zero rather than one step later. -/
theorem UniformTM.seq_initialConfig (M₁ M₂ : UniformTM) {n : Nat} (B : Nat) (x : Bitstring n) :
    initialConfig (M₁.seq M₂) B x = M₁.seqEmbedRouted M₂ (initialConfig M₁ B x) := rfl

/-- Every left-block row of the composed *raw* table is the routed `M₁` row. -/
theorem UniformTM.seqRawStep_left (M₁ M₂ : UniformTM) (q : Fin M₁.stateCount) (s : Option Bool) :
    M₁.seqRawStep M₂ (M₁.seqLeft M₂ q) s =
      (M₁.seqRoute M₂ (M₁.step q s).1, (M₁.step q s).2.1, (M₁.step q s).2.2) := by
  have hlt : (M₁.seqLeft M₂ q).val < M₁.stateCount := q.isLt
  simp only [UniformTM.seqRawStep, dif_pos hlt]
  rfl

/-- Every right-block row of the composed *raw* table is the `M₂` row, re-embedded. -/
theorem UniformTM.seqRawStep_right (M₁ M₂ : UniformTM) (q : Fin M₂.stateCount)
    (s : Option Bool) :
    M₁.seqRawStep M₂ (M₁.seqRight M₂ q) s =
      (M₁.seqRight M₂ (M₂.step q s).1, (M₂.step q s).2.1, (M₂.step q s).2.2) := by
  have hnot : ¬ (M₁.seqRight M₂ q).val < M₁.stateCount := by
    simp only [UniformTM.seqRight]
    omega
  have hq : (⟨(M₁.seqRight M₂ q).val - M₁.stateCount,
      by have := (M₁.seqRight M₂ q).isLt; omega⟩ : Fin M₂.stateCount) = q := by
    apply Fin.ext
    simp only [UniformTM.seqRight]
    omega
  simp only [UniformTM.seqRawStep, dif_neg hnot]
  rw [hq]

/-- Every left-block row of the composed *public* step is the routed `M₁` row: the left block
contains no composed terminal, so the public wrapper is transparent there. -/
theorem UniformTM.seq_step_left (M₁ M₂ : UniformTM) (q : Fin M₁.stateCount) (s : Option Bool) :
    (M₁.seq M₂).step (M₁.seqLeft M₂ q) s =
      (M₁.seqRoute M₂ (M₁.step q s).1, (M₁.step q s).2.1, (M₁.step q s).2.2) := by
  rw [UniformTM.step_of_ne _ (M₁.seqLeft_ne_seqRight M₂ q M₂.accept)
    (M₁.seqLeft_ne_seqRight M₂ q M₂.reject)]
  exact M₁.seqRawStep_left M₂ q s

/-- Every right-block row of the composed *public* step is the `M₂` public row, re-embedded. -/
theorem UniformTM.seq_step_right (M₁ M₂ : UniformTM) (q : Fin M₂.stateCount) (s : Option Bool) :
    (M₁.seq M₂).step (M₁.seqRight M₂ q) s =
      (M₁.seqRight M₂ (M₂.step q s).1, (M₂.step q s).2.1, (M₂.step q s).2.2) := by
  by_cases ha : q = M₂.accept
  · subst ha; rw [UniformTM.step_accept]; exact UniformTM.step_accept (M₁.seq M₂) s
  · by_cases hr : q = M₂.reject
    · subst hr; rw [UniformTM.step_reject]; exact UniformTM.step_reject (M₁.seq M₂) s
    · rw [UniformTM.step_of_ne (M₁.seq M₂) (fun h => ha (M₁.seqRight_injective M₂ h))
        (fun h => hr (M₁.seqRight_injective M₂ h))]
      exact M₁.seqRawStep_right M₂ q s

/-- The composed public step agrees with the composed raw table on every row. -/
theorem UniformTM.seq_step_eq_rawStep (M₁ M₂ : UniformTM) (q : Fin (M₁.seq M₂).stateCount)
    (s : Option Bool) : (M₁.seq M₂).step q s = (M₁.seq M₂).rawStep q s := by
  by_cases ha : q = (M₁.seq M₂).accept
  · subst ha; rw [UniformTM.step_accept]
    show _ = M₁.seqRawStep M₂ (M₁.seqRight M₂ M₂.accept) s
    rw [UniformTM.seqRawStep_right, UniformTM.step_accept]; rfl
  · by_cases hr : q = (M₁.seq M₂).reject
    · subst hr; rw [UniformTM.step_reject]
      show _ = M₁.seqRawStep M₂ (M₁.seqRight M₂ M₂.reject) s
      rw [UniformTM.seqRawStep_right, UniformTM.step_reject]; rfl
    · exact UniformTM.step_of_ne _ ha hr s

/-! ### Simulation -/

/-- One composed transition out of a right-embedded configuration is one `M₂` transition. -/
theorem UniformTM.seq_stepConfig_right (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₂.stateCount n B) :
    (M₁.seq M₂).stepConfig (M₁.seqEmbedRight M₂ c) = M₁.seqEmbedRight M₂ (M₂.stepConfig c) := by
  cases c with
  | mk q h t =>
      simp only [UniformTM.stepConfig, UniformTM.seqEmbedRight]
      rw [UniformTM.seq_step_right]

/-- One composed transition out of a routed-embedded configuration not in `M₁.accept` is one `M₁`
transition: a rejecting one absorbs on both sides, a working one takes its routed row. -/
theorem UniformTM.seq_stepConfig_routed (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₁.stateCount n B) (hna : c.state ≠ M₁.accept) :
    (M₁.seq M₂).stepConfig (M₁.seqEmbedRouted M₂ c) =
      M₁.seqEmbedRouted M₂ (M₁.stepConfig c) := by
  by_cases hr : c.state = M₁.reject
  · have h1 : (M₁.seqEmbedRouted M₂ c).state = (M₁.seq M₂).reject := by
      show M₁.seqRoute M₂ c.state = M₁.seqRight M₂ M₂.reject
      rw [hr]
      simp [UniformTM.seqRoute, M₁.accept_ne_reject.symm]
    rw [UniformTM.stepConfig_reject _ _ h1, UniformTM.stepConfig_reject _ _ hr]
  · cases c with
    | mk q h t =>
        change q ≠ M₁.accept at hna
        change q ≠ M₁.reject at hr
        have hroute : M₁.seqRoute M₂ q = M₁.seqLeft M₂ q := by
          simp [UniformTM.seqRoute, hna, hr]
        simp only [UniformTM.stepConfig, UniformTM.seqEmbedRouted]
        rw [hroute, UniformTM.seq_step_left]

/-- **The right block runs `M₂`**, for every step count and with no hypothesis. -/
theorem UniformTM.seq_run_right (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₂.stateCount n B)
    (t : Nat) : (M₁.seq M₂).run t (M₁.seqEmbedRight M₂ c) = M₁.seqEmbedRight M₂ (M₂.run t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [UniformTM.run, ih, UniformTM.seq_stepConfig_right, UniformTM.run]

/-- **The left block runs `M₁` until `M₁` first accepts.**  No hypothesis about `M₁.reject` is
needed: a rejection absorbs on both sides. -/
theorem UniformTM.seq_run_left (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B)
    {T : Nat} (hwork : ∀ t, t < T → (M₁.run t c).state ≠ M₁.accept) :
    ∀ t, t ≤ T →
      (M₁.seq M₂).run t (M₁.seqEmbedRouted M₂ c) = M₁.seqEmbedRouted M₂ (M₁.run t c) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [UniformTM.run, ih (by omega), UniformTM.seq_stepConfig_routed _ _ _ (hwork t (by omega)),
        UniformTM.run]

/-- **The executed handoff.**  If `M₁` accepts at `T` and not before, the composed run at `T + s`
is the `M₂` run of `s` steps out of `M₂.start` on the head and tape `M₁` left at `T`.  First
arrival is load-bearing — an earlier acceptance would have started `M₂` earlier — and the handoff
costs no step. -/
theorem UniformTM.seq_handoff (M₁ M₂ : UniformTM) {n B : Nat} (c : Config M₁.stateCount n B)
    {T : Nat} (hwork : ∀ t, t < T → (M₁.run t c).state ≠ M₁.accept)
    (hacc : (M₁.run T c).state = M₁.accept) (s : Nat) :
    (M₁.seq M₂).run (T + s) (M₁.seqEmbedRouted M₂ c) =
      M₁.seqEmbedRight M₂ (M₂.run s ⟨M₂.start, (M₁.run T c).head, (M₁.run T c).tape⟩) := by
  rw [UniformTM.run_add, UniformTM.seq_run_left M₁ M₂ c hwork T le_rfl]
  have hswitch : M₁.seqEmbedRouted M₂ (M₁.run T c) =
      M₁.seqEmbedRight M₂ ⟨M₂.start, (M₁.run T c).head, (M₁.run T c).tape⟩ := by
    refine Config.ext_parts ?_ rfl rfl
    show M₁.seqRoute M₂ (M₁.run T c).state = M₁.seqRight M₂ M₂.start
    rw [hacc]
    simp [UniformTM.seqRoute]
  rw [hswitch, UniformTM.seq_run_right]

/-- **The rejecting handoff.**  If `M₁` rejects at `T`, the composed run at `T + s` is the composed
reject on the head and tape `M₁` left at `T`.  No first-arrival hypothesis: an earlier `M₁`
acceptance would contradict the rejection by absorption. -/
theorem UniformTM.seq_reject_handoff (M₁ M₂ : UniformTM) {n B : Nat}
    (c : Config M₁.stateCount n B) {T : Nat} (hrej : (M₁.run T c).state = M₁.reject) (s : Nat) :
    (M₁.seq M₂).run (T + s) (M₁.seqEmbedRouted M₂ c) =
      ⟨(M₁.seq M₂).reject, (M₁.run T c).head, (M₁.run T c).tape⟩ := by
  have hwork : ∀ t, t < T → (M₁.run t c).state ≠ M₁.accept := by
    intro t ht hacc
    have hrun := M₁.run_accept_of_le c hacc (Nat.le_of_lt ht)
    rw [hrun, hacc] at hrej
    exact M₁.accept_ne_reject hrej
  rw [UniformTM.run_add, UniformTM.seq_run_left M₁ M₂ c hwork T le_rfl]
  have hswitch : M₁.seqEmbedRouted M₂ (M₁.run T c) =
      ⟨(M₁.seq M₂).reject, (M₁.run T c).head, (M₁.run T c).tape⟩ := by
    refine Config.ext_parts ?_ rfl rfl
    show M₁.seqRoute M₂ (M₁.run T c).state = M₁.seqRight M₂ M₂.reject
    rw [hrej]
    simp [UniformTM.seqRoute, M₁.accept_ne_reject.symm]
  rw [hswitch]
  exact (M₁.seq M₂).run_reject _ rfl s

end Pnp3.Complexity.Uniform.V1
