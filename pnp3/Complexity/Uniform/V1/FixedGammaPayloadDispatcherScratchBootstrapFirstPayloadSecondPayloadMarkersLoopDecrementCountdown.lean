import Complexity.Uniform.V1.AcceptMerge
import Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
import
  Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The gamma-payload dispatcher, the scratch bootstrap, the first payload digit, the second payload
digit, the loop markers, the payload loop, the decrement and the countdown as one machine
(Part A G3g)

**No new table row.**  `machine` is `mergedDispatcher.seq
FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
where `mergedDispatcher` is G2k's fixed 28-state, 84-row payload dispatcher with its second
successful absorbing endpoint `qHasOne` merged into its `accept` `qAllZero` by the generic
`UniformTM.mergeAccept`: the same 28 states and 84 rows, exactly the two working-state rows that
targeted `qHasOne` — `qCursorFillOne` on the blank, `qPendingFillOne` on `true` — now targeting
`qAllZero`, and `qHasOne` a dead index.  That merged table is the left block `[0, 28)`; the whole
landed G3e 95-state composite is the right block `[28, 123)`, G2p-a's bootstrap at `[28, 37)` and
G2p-b, G2p-c, G2p-d's preamble, G2p-d's round, G2q, G2s-a at `37`, `55`, `69`, `83`, `105`, `112`:
one closed 123-state, 369-row table whose every row is a row of one of those eight tables with its
target routed.  Write `N = a + m` and `d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries
the long-form notes.  Classification (AGENTS.md): **Infrastructure**.

**Seven executed handoffs.**  H11 is the newly executed one, with **six** live routed rows into
G3e's start `tailStart` at index `28`: the four rows that targeted `qAllZero` (`qCursorBackFirst`,
`qCursorFillVirtual` on the blank; `qZeroFillCounter`, `qPendingFillVirtual` on `true`) and the two
that targeted `qHasOne`, which the merge retargets so that `seq` routes them too, in that same
transition, at no cost — this is why H11 could not be composed before, since `seq` routes a left
`accept` and `reject` only.  The left copies of the three endpoints stay dead.  H12 (`34 → 37`)
to H17 (`109 → 112`) are inherited from G3e, its indices shifted by twenty-eight, located by
`(inTail q).val = 28 + q.val` composed with G3e's own pins and carried by the universal right-block
row equation.

**The switch time is input-dependent.**  H11 fires at the dispatcher's strict first terminal time
`C` of G3f's `StrictFirstTerminalAt B x w C q`, one of seven closed forms selected by the payload;
no length-only formula exists.  `handoff_of_first_terminal` takes that first arrival, `q ≠ qReject`
and `C ≤ deadline N` as hypotheses; `side_premises_of_strictFirstTerminalAt` derives the latter two
from a matching tag and a decoded width, `strictFirstTerminalAt_unique` pins the arrival unique and
`tagged_handoff` packages the switch existentially.  The deadline premise identifies the
dispatcher's configuration at `C` with the G2m deadline configuration G2p-a's `startConfig`, and
through it G3e's, retags; it is used in that direction only.

**Both outcomes route, the reject stays rejecting, the verdict is merged.**  With `q = qAllZero`
or `q = qHasOne` the merged control at `C` is `qAllZero`, and the same row the standalone dispatcher
takes is routed on the same head and tape; before `C` no terminal of any kind occurs, so no merged
accept does.  On a malformed
gamma the composed control is the composed reject `122` from step `1` on.  Head and tape are
preserved at every time up to `C`, and the switch hands G2p-a exactly its own `startConfig`
projections (`handoff_endpoint_pins`).  The composed control after the switch does not record
which of `qAllZero` and `qHasOne` the dispatcher reached — exactly what G2p-a's landed
`retagDispatcher` already discards, keeping only head and tape; the distinction survives in the
theorems through `q`, and G2m's `qHasOne_iff` family remains about the standalone dispatcher.  The
drained theorem lands the composed accept `121` at exactly `dispatcherChainClock C N zeros d v =
C + bootChainClock N zeros d v` under G3e's seven hypotheses plus the first arrival.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
ten handoffs before H11 remain proof-level identifications (G2k's `startConfig` retags the actual
G2a anchor deadline endpoint), no raw-input `initialConfig` is executed, and no clock here counts
a step of any earlier phase.  No **first arrival** of the composed accept (the one proved is the
dispatcher's, inside the left block); the **fence** (all eight tables are uncapped); every
**converse**; a **footprint** theorem; and the pnp4 bridge, not built here, the standalone
dispatcher's pnp4 semantics being unchanged.  The composed `accept` is the countdown's phase-local
`qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw input nor
language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or
`ContentVerifierBridge` is stated.  The table is fixed and complete but not claimed state-minimal. -/
namespace
  Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedGammaPayloadDispatcher (qCursorStart qCursorBackFirst qCursorFillOne qCursorFillVirtual
  qZeroFillCounter qPendingFillOne qPendingFillVirtual qAllZero qHasOne qReject)
open FixedGammaPayloadDispatcherFirstArrival
open FixedGammaPayloadDispatcherDeadline (deadline qReject_iff tagged_endpoint_classification)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown (firstChainClock)
open FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)

/-- G2k's dispatcher with `qHasOne` merged into `qAllZero`: the same 28 states and 84 rows, two
working-state rows retargeted, `qHasOne` dead. -/
def mergedDispatcher : UniformTM := FixedGammaPayloadDispatcher.machine.mergeAccept qHasOne

/-- The composed machine: the merged dispatcher, then G3e's whole composite, as one closed table.
No row is new; the left rows are routed. -/
def machine : UniformTM :=
  mergedDispatcher.seq
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- A dispatcher state in the composed control, at its own index. -/
def inDispatcher (q : Fin FixedGammaPayloadDispatcher.stateCount) : Fin machine.stateCount :=
  mergedDispatcher.seqLeft
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- A G3e state in the composed control, shifted past the twenty-eight dispatcher states. -/
def inTail
    (q : Fin
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  mergedDispatcher.seqRight
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- The routed target of a merged dispatcher row: `qAllZero` becomes G3e's start, `qReject` the
composed reject, every working state itself.  `qHasOne` is no row's target after the merge. -/
def route (q : Fin FixedGammaPayloadDispatcher.stateCount) : Fin machine.stateCount :=
  mergedDispatcher.seqRoute
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- G3e's start in the composed control, index `28`: the target of every live routed row. -/
def tailStart : Fin machine.stateCount :=
  inTail
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start

/-- G2k's own `startConfig` — the retagged *actual* G2a anchor deadline endpoint — merged and
routed into the composed control.  Still a phase-local retag, not `initialConfig` on a raw pair
input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  mergedDispatcher.seqEmbedRouted
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    (FixedGammaPayloadDispatcher.machine.mergeConfig qHasOne
      (FixedGammaPayloadDispatcher.startConfig B x w))

/-- Exact cost of the dispatcher phase followed by the whole of G3e: the dispatcher's first
arrival `C`, an input-dependent quantity G3f pins path by path, plus G3e's `bootChainClock`.  The
handoff between them costs nothing. -/
def dispatcherChainClock (C N zeros d v : Nat) : Nat := C + bootChainClock N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the state and row counts, the merged dispatcher's start and
verdicts, the distinguished states with their indices, the block injections with their offsets and
disjointness, `tailStart` at `28`, the routing cases, **every** merged row as G2k's row with its
target merged, `qHasOne` as no merged row's target, the two retargeted rows, every left row as the
routed merged row, every right row as the G3e row, the public step against the composed raw table,
the **six** live routed rows into `tailStart`, and the routed reject row out of the start.  The
inherited rows are not restated: the right-block row equation transports every G3e row verbatim,
and the offset equation, composed with G3e's own pins, locates them. -/
theorem table_and_resource_pins :
    machine.stateCount = 123 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 369 ∧
      mergedDispatcher.start = qCursorStart ∧ mergedDispatcher.accept = qAllZero ∧
      mergedDispatcher.reject = qReject ∧
      machine.start = route qCursorStart ∧ machine.start = inDispatcher qCursorStart ∧
      machine.accept =
        inTail
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inTail
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 121 ∧ machine.reject.val = 122 ∧
      (∀ q, (inDispatcher q).val = q.val) ∧ (∀ q, (inDispatcher q).val < 28) ∧
      (∀ q, (inTail q).val = 28 + q.val) ∧ (∀ q, 28 ≤ (inTail q).val) ∧
      Function.Injective inDispatcher ∧ Function.Injective inTail ∧
      (∀ p q, inDispatcher p ≠ inTail q) ∧
      tailStart =
        inTail
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      tailStart.val = 28 ∧ route qAllZero = tailStart ∧ route qReject = machine.reject ∧
      (∀ q, q ≠ qAllZero → q ≠ qReject → route q = inDispatcher q) ∧
      (∀ q s, mergedDispatcher.step q s =
        (FixedGammaPayloadDispatcher.machine.mergeState qHasOne
            (FixedGammaPayloadDispatcher.machine.step q s).1,
          (FixedGammaPayloadDispatcher.machine.step q s).2.1,
          (FixedGammaPayloadDispatcher.machine.step q s).2.2)) ∧
      (∀ q s, (mergedDispatcher.step q s).1 ≠ qHasOne) ∧
      mergedDispatcher.step qCursorFillOne none = (qAllZero, some false, .left) ∧
      mergedDispatcher.step qPendingFillOne (some true) = (qAllZero, some true, .stay) ∧
      (∀ q s, machine.step (inDispatcher q) s =
        (route (mergedDispatcher.step q s).1, (mergedDispatcher.step q s).2.1,
          (mergedDispatcher.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail
            (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inDispatcher qCursorBackFirst) none = (tailStart, some false, .stay) ∧
      machine.step (inDispatcher qCursorFillOne) none = (tailStart, some false, .left) ∧
      machine.step (inDispatcher qCursorFillVirtual) none = (tailStart, some false, .left) ∧
      machine.step (inDispatcher qZeroFillCounter) (some true) = (tailStart, some true, .stay) ∧
      machine.step (inDispatcher qPendingFillOne) (some true) = (tailStart, some true, .stay) ∧
      machine.step (inDispatcher qPendingFillVirtual) (some true) =
        (tailStart, some true, .stay) ∧
      machine.step (inDispatcher qCursorStart) none = (machine.reject, none, .stay) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    mergedDispatcher.seq_pins
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, fun q => q.isLt, fun _ => rfl, fun _ => Nat.le_add_right _ _,
    hli, hri, hne, rfl, rfl, hra, hrr, hrw,
    fun q s => FixedGammaPayloadDispatcher.machine.mergeAccept_step qHasOne (by decide) q s,
    fun q s =>
      FixedGammaPayloadDispatcher.machine.mergeAccept_step_ne qHasOne (by decide) (by decide) q s,
    by decide, by decide,
    fun q s => mergedDispatcher.seq_step_left
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => mergedDispatcher.seq_step_right
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => mergedDispatcher.seq_step_eq_rawStep
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The start, pinned: G2k's `startConfig` merged and routed into the composed control — the same
head and tape, the composed start as control.  Neither the merge nor the routing consults decoded
data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    let c := startConfig B x w
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl⟩

/-- The chained clock, pinned: G3e's sum prefixed by the dispatcher's first arrival `C`, and on
`2 ≤ zeros` its full expansion.  `C` has no closed form in `N`. -/
theorem clock_pins (C N zeros d v : Nat) :
    dispatcherChainClock C N zeros d v = C + bootChainClock N zeros d v ∧
      (2 ≤ zeros → dispatcherChainClock C N zeros d v =
        C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v)))))) := by
  refine ⟨rfl, fun hz => ?_⟩
  show C + bootChainClock N zeros d v = _
  rw [(FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    N zeros d v).2.2 hz]

/-! ### The dispatcher's first arrival, as the composition consumes it -/

/-- The strict first terminal arrival is unique: two of them on the same start agree in time and
in endpoint. -/
theorem strictFirstTerminalAt_unique {a m B C C' : Nat}
    {q q' : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (h : StrictFirstTerminalAt B x w C q) (h' : StrictFirstTerminalAt B x w C' q') :
    C = C' ∧ q = q' := by
  obtain ⟨hq, ht, hno⟩ := h
  obtain ⟨hq', ht', hno'⟩ := h'
  have hC : C = C' := by
    rcases Nat.lt_trichotomy C C' with hlt | heq | hgt
    · exact (hno' C hlt (by rw [hq]; exact ht)).elim
    · exact heq
    · exact (hno C' hgt (by rw [hq']; exact ht')).elim
  subst hC
  exact ⟨rfl, hq.symm.trans hq'⟩

/-- On a matching tag with a decoded width, the strict first arrival is at or below G2m's
length-only deadline `2 * N * N` (G3f's existential produces one, and it is the only one) and its
endpoint is not `qReject`, which G2m's `qReject_iff` reserves for a malformed gamma. -/
theorem side_premises_of_strictFirstTerminalAt {a m B C zeros : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q) : C ≤ deadline (a + m) ∧ q ≠ qReject := by
  obtain ⟨C', q', hle, h', -⟩ := tagged_strict_first_terminal (B := B) x w htag
  obtain ⟨rfl, rfl⟩ := strictFirstTerminalAt_unique x w h h'
  refine ⟨hle, fun hqr => ?_⟩
  subst hqr
  have hr : (FixedGammaPayloadDispatcher.machine.run (deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)).state = qReject := by
    rw [run_deadline_eq_of_strictFirstTerminalAt x w h hle]
    exact h.1
  have hnone := (qReject_iff (B := B) x w htag).1 hr
  rw [hg] at hnone
  cases hnone

/-! ### The executed handoff -/

/-- **H11 fires at whatever time the dispatcher first stops in a success endpoint, whichever of
the two, and it costs nothing.**  The composed run out of `startConfig` is in neither composed
verdict before `C`, is G2k's own run merged and routed up to and including `C` — the same head and
whole tape at every such time — at exactly `C` **is** G3e's landed `startConfig B x w`
re-embedded, and takes G3e steps afterwards. -/
theorem handoff_of_first_terminal {a m B C : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (h : StrictFirstTerminalAt B x w C q) (hq : q ≠ qReject) (hle : C ≤ deadline (a + m)) :
    let c := startConfig B x w
    (∀ t, t < C →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ C → machine.run t c =
        mergedDispatcher.seqEmbedRouted
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaPayloadDispatcher.machine.mergeConfig qHasOne
            (FixedGammaPayloadDispatcher.machine.run t
              (FixedGammaPayloadDispatcher.startConfig B x w)))) ∧
      machine.run C c =
        mergedDispatcher.seqEmbedRight
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (C + s) c =
        mergedDispatcher.seqEmbedRight
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
            s
            (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) := by
  intro c
  obtain ⟨hD, hterm, hno⟩ := h
  have hwork : ∀ t, t < C →
      (FixedGammaPayloadDispatcher.machine.run t
        (FixedGammaPayloadDispatcher.startConfig B x w)).state ≠ qHasOne ∧
      (FixedGammaPayloadDispatcher.machine.run t
        (FixedGammaPayloadDispatcher.startConfig B x w)).state ≠
        FixedGammaPayloadDispatcher.machine.accept :=
    fun t ht => ⟨fun hh => hno t ht (Or.inr (Or.inl hh)), fun hh => hno t ht (Or.inl hh)⟩
  have hT : (FixedGammaPayloadDispatcher.machine.run C
      (FixedGammaPayloadDispatcher.startConfig B x w)).state = qHasOne ∨
      (FixedGammaPayloadDispatcher.machine.run C
        (FixedGammaPayloadDispatcher.startConfig B x w)).state =
        FixedGammaPayloadDispatcher.machine.accept := by
    rw [hD]
    rcases hterm with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact absurd rfl hq
  have hdead := run_deadline_eq_of_strictFirstTerminalAt x w ⟨hD, hterm, hno⟩ hle
  have hcfg :
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
        B x w =
      ⟨FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
        (FixedGammaPayloadDispatcher.machine.run C
          (FixedGammaPayloadDispatcher.startConfig B x w)).head,
        (FixedGammaPayloadDispatcher.machine.run C
          (FixedGammaPayloadDispatcher.startConfig B x w)).tape⟩ := by
    unfold
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
      FixedGammaTerminatorScratchBootstrap.startConfig
      FixedGammaTerminatorScratchBootstrap.retagDispatcher
    rw [hdead]
    rfl
  have hleft : ∀ t, t ≤ C → machine.run t c =
      mergedDispatcher.seqEmbedRouted
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcher.machine.mergeConfig qHasOne
          (FixedGammaPayloadDispatcher.machine.run t
            (FixedGammaPayloadDispatcher.startConfig B x w))) :=
    FixedGammaPayloadDispatcher.machine.mergeAccept_seq_run_left
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      qHasOne _ hwork
  have hsuffix : ∀ s, machine.run (C + s) c =
      mergedDispatcher.seqEmbedRight
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          s
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) := by
    intro s
    rw [hcfg]
    exact FixedGammaPayloadDispatcher.machine.mergeAccept_seq_handoff
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      qHasOne _ hwork hT s
  have hC : machine.run C c =
      mergedDispatcher.seqEmbedRight
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          B x w) :=
    hsuffix 0
  have hCs : (machine.run C c).state = tailStart := by
    rw [hC]; rfl
  have hCa : (machine.run C c).state ≠ machine.accept := by
    rw [hCs]; decide
  have hCr : (machine.run C c).state ≠ machine.reject := by
    rw [hCs]; decide
  exact ⟨fun t ht => UniformTM.no_terminal_of_le machine c hCa hCr t (Nat.le_of_lt ht), hleft, hC,
    hsuffix⟩

/-- **What the switch hands over is exactly what G2p-a reads.**  At the strict first arrival `C`
in `q`: `q` is one of the two success endpoints, the composed configuration's head and whole tape
are *the same two projections* that G2p-a's own `startConfig` carries, that tape is the unchanged
`contentTape B x w`, and the head is the dispatcher's cleaned head — `7` at width zero, `6` at a
positive width — read off G2m's landed endpoint classification. -/
theorem handoff_endpoint_pins {a m B C zeros : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q) :
    let e := machine.run C (startConfig B x w)
    let p := FixedGammaTerminatorScratchBootstrap.startConfig B x w
    (q = qAllZero ∨ q = qHasOne) ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (zeros = 0 → e.head.val = 7) ∧ (0 < zeros → e.head.val = 6) := by
  obtain ⟨hle, hq⟩ := side_premises_of_strictFirstTerminalAt x w htag hg h
  obtain ⟨-, -, hC, -⟩ := handoff_of_first_terminal x w h hq hle
  have hhead : (machine.run C (startConfig B x w)).head =
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head := by
    rw [hC]; rfl
  have htape : (machine.run C (startConfig B x w)).tape =
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape := by
    rw [hC]; rfl
  obtain ⟨hct, hcases⟩ := tagged_endpoint_classification (B := B) x w htag
  rw [hg] at hcases
  refine ⟨?_, hhead, htape, ?_, fun hz => ?_, fun hz => ?_⟩
  · rcases h.2.1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hq
  · rw [htape]; exact hct
  · rw [hhead]
    subst hz
    rcases hcases with ⟨-, -, h1⟩ | ⟨-, hh, -⟩ | ⟨z, hz', hpos, -, -⟩
    · cases h1
    · exact hh
    · exact absurd (Option.some.inj hz').symm (by omega)
  · rw [hhead]
    rcases hcases with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨z, -, -, hh, -⟩
    · cases h1
    · exact absurd (Option.some.inj h1) (by omega)
    · exact hh

/-- **The concrete exact run: the payload dispatcher, H11, the scratch bootstrap, H12, the first
payload digit, H13, the second payload digit, H14, the markers, H15, the loop, H16, the decrement,
H17, the countdown, one machine.**  Under G3e's **seven** hypotheses plus the dispatcher's strict
first arrival at `C` in `q`, after exactly `dispatcherChainClock C (a+m) zeros d v` steps the
composed machine is in its accept (the countdown's `qDone`) on the separator blank `a+m+2+zeros`
with tape `loopTape B x w zeros 0 v`, persisting; `q ≠ qReject` and `C ≤ deadline (a+m)` are
derived.  `v` is universally quantified and nothing in pnp3 supplies it; persistence is not first
arrival of the composed accept. -/
theorem dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let K := dispatcherChainClock C (a + m) zeros d v
    let e := machine.run K (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨hle, hq⟩ := side_premises_of_strictFirstTerminalAt x w htag hg h
  obtain ⟨-, -, -, hsuffix⟩ := handoff_of_first_terminal x w h hq hle
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg hzeros hfence hroom hv hhigh
  have hE : machine.run (dispatcherChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      mergedDispatcher.seqEmbedRight
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (bootChainClock (a + m) zeros (borrow x w zeros) v)
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) :=
    hsuffix (bootChainClock (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (dispatcherChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = dispatcherChainClock C (a + m) zeros (borrow x w zeros) v +
      (t - dispatcherChainClock C (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **Every tagged input with a decoded width hands over**: there is a strict first arrival `C` at
or below G2m's deadline, in one of the two success endpoints, at which the composed configuration
**is** G3e's landed `startConfig B x w` re-embedded.  `C` is produced, not chosen. -/
theorem tagged_handoff {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ deadline (a + m) ∧ StrictFirstTerminalAt B x w C q ∧
      (q = qAllZero ∨ q = qHasOne) ∧
      machine.run C (startConfig B x w) =
        mergedDispatcher.seqEmbedRight
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) := by
  obtain ⟨C, q, hle, h, -⟩ := tagged_strict_first_terminal (B := B) x w htag
  have hq := (side_premises_of_strictFirstTerminalAt x w htag hg h).2
  refine ⟨C, q, hle, h, ?_, (handoff_of_first_terminal x w h hq hle).2.2.1⟩
  rcases h.2.1 with h3 | h3 | h3
  · exact Or.inl h3
  · exact Or.inr h3
  · exact absurd h3 hq

/-- **The routed reject, executed one block further left.**  A matching tag with no decoded width:
G2k rejects in one step at the blank boundary cell `a + m` (its landed `malformed_exact`), the
merge keeps `qReject` fixed, and the generic rejecting handoff lands the composed reject — index
`122`, not G2k's `qReject` at `27` — from step one on, on the unchanged content tape.  Forward
direction only: **not** a converse, and it characterises no parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have he := FixedGammaPayloadDispatcher.malformed_exact (B := B) x w htag hg
  dsimp only at he
  have hwork : ∀ t, t < 1 →
      (FixedGammaPayloadDispatcher.machine.run t
        (FixedGammaPayloadDispatcher.startConfig B x w)).state ≠ qHasOne := by
    intro t ht
    rw [show t = 0 by omega]
    exact fun hh => start_not_terminal x w (Or.inr (Or.inl hh))
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedGammaPayloadDispatcher.machine.run 1
          (FixedGammaPayloadDispatcher.startConfig B x w)).head,
        (FixedGammaPayloadDispatcher.machine.run 1
          (FixedGammaPayloadDispatcher.startConfig B x w)).tape⟩ := by
    have h := FixedGammaPayloadDispatcher.machine.mergeAccept_seq_reject_handoff
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      qHasOne (FixedGammaPayloadDispatcher.startConfig B x w) (T := 1) hwork he.1 (by decide) (s - 1)
    rw [show 1 + (s - 1) = s by omega] at h
    exact h
  exact ⟨by rw [hrun], by rw [hrun]; exact he.2.1, by rw [hrun]; exact he.2.2⟩

end
  Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
