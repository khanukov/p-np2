import Complexity.Uniform.V1.SequentialComposition
import
  Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The structural one-cell origin shift, the pair origin alignment, the trailing content-marker
erasure, the content tag gate, the gamma terminator, the gamma anchor, the payload dispatcher, the
scratch bootstrap, the first payload digit, the second payload digit, the loop markers, the payload
loop, the decrement and the countdown as one machine (Part A G3m)

**No new table row.**  `machine` is `FixedPairOriginShiftBootstrap.machine.seq` the whole landed G3l
composite: the bootstrap phase's fixed 7-state, 21-row structural left shift on `[0, 7)` and G3l's
177 states on `[7, 184)`, one closed 184-state, 552-row table whose every row is a row of one of those
fourteen tables with its target routed.  Write `N = a + m` and `d = borrow x w zeros`.
`pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Thirteen executed handoffs.**  H5 — the origin-shift bootstrap into the origin-alignment phase — is
the newly executed one, and its live accept list is as narrow as a live handoff's can be: **one** row,
the bootstrap state `4` on `none`, which `accept_rows_unique` proves is the only row targeting the
phase's accept once the accept's own absorbing three are excluded (nine of the twelve landed handoffs
route one row too; only H6, with three, H15, with four, and H11, with six, are plural).  `seq`
retargets it to the right block's start `tailStart` at index `7`, keeping its written `none` and its
`.stay`, in that same transition and at no cost.  The endpoint head is `pairLength a m + min B 1`,
which is what `seq_handoff` transports: it uses the post-move head, and the row itself does not move.
The **boundary distinction** matters here: the bootstrap's own last right move, at source time
`switchTime a m - 2`, clamps exactly when `B = 0` — the landed `clamps` proves that equivalence —
whereas H5 itself is a `.stay` and so clamps on neither budget.  On the reject side, once **both**
verdicts' own absorbing rows are excluded, every row of the bootstrap table targeting its reject is
one of **six** — the two Boolean rows of each of the states `1`, `2`, `3`, the carry and hole probes
that find a cell occupied where the shift invariant requires it blank — `reject_rows_unique` proves
that list exhaustive **in both directions**, over all `7` states and all three symbols, and
`reject_rows_routed` sends each to the composed reject `183` with the symbol written and the move
unchanged.  None is *taken* out of this `startConfig`:
`bootstrap_first_arrival` proves the left block never enters its reject there at any time, so the
composed reject is reachable only through the right block.  The left copies of the two bootstrap
verdicts are dead: no composed row targets either, and the start is neither
(`table_and_resource_pins`).  H6 (three rows, `17`, `18` and `19`, all into `33`), H7 (`34 → 37`),
H8 (`49 → 52`), H9 (`52 → 55`), H10 (`58 → 61`), H11 (six rows inside `[61, 89)`, all into `89`) to
H17 (`170 → 173`) are inherited from G3l, its indices shifted by seven and located by
`(inTail q).val = 7 + q.val` with the universal right-block row equation.

**The feasibility of this one step, as measured before it was built.**  The bootstrap phase has
exactly two absorbing states, `qAccept` and `qReject` — its raw states `5` and `6`, three rows each —
so the landed `seq` routes both and no `mergeAccept` is needed, as for H6 to H10 and unlike H11.  Its
strict first arrival was already exported in the shape `UniformTM.seq_handoff` consumes: the landed
`noEarlyTerminal` excludes **both** verdicts strictly before the clock and takes **no hypothesis at
all** — no tag, no width, no room, no positive budget — and `run_exact` gives the exact endpoint there,
so `bootstrap_first_arrival` only repackages the two at `switchTime a m = clock a m` and adds the
never-rejects consequence, from the landed `run_after`.  `run_exact` alone would **not** suffice: it is
one endpoint identity, and an absorbing phase satisfies it at every later time too, while `seq_handoff`
starts the right machine inside the accepting transition and so needs the absence of any earlier
acceptance.  The endpoint is compatible with the right block's start by construction: the
origin-alignment `startConfig` is built field-for-field out of the bootstrap `finalConfig`, which
`run_exact` shows *is* the bootstrap run at `switchTime a m` for every input, and
`alignment_start_at_first_arrival` records that hypothesis-free as whole-`Config` equality.  So the
switch hands over exactly the head and tape the right block's own `startConfig` carries — the
`shiftedTape`, whose content-plus-marker block starts at cell `a` and which is therefore **not yet
origin-aligned**; G3l's own first `(10 * a + 7) * (N + 1) + 3 * a` steps are what move that block down
to the origin.

**The switch time is linear, and far below G3l's quadratic one.**  `switchTime a m = 4 * a + 3 * m + 5`:
one `a + 1`-cell scan to the top of the blank prefix, then three steps for each of the `N + 1` block
cells, then one closing step — `12` against G3l's `54` at `a = m = 1`, both in `clock_pins`, and `64`
against `1590` at the surface test's `a = 8`, `m = 9`.  It is *not* the smallest switch time in the
chain: the length-only `N + 3` and `3 * N + 7` are `20` and `58` at that fixture, both below `64`.  It
reads the two split lengths apart, as G3l's `(10 * a + 7) * (N + 1) + 3 * a` does — `clock_pins`
exhibits three different values at one `N` — so the composed clock stays quadratic in `a`, and whether
the cubic budget dominates it is *not* proved.

**The composed run.**  `handoff_exact` takes **no hypothesis** — no tag, no width, no room, no positive
budget, no budget-dominates-clock premise: the run out of `startConfig` stays strictly inside the left
block `[0, 7)` at every time strictly before `switchTime a m`, is in neither composed verdict at any
time up to and including it (at the switch time itself the control is `tailStart`, so that bound is
`≤`), is the bootstrap phase's own run routed at every such time as whole-`Config` equality, at exactly
`switchTime a m` **is** G3l's landed `startConfig B x w` re-embedded, and every later step is a G3l
step.  `handoff_endpoint_pins` reads that switch configuration back as G3l's own and as the
origin-alignment phase's own `startConfig` projections, and records the source head
`pairLength a m + min B 1`, the `shiftedTape`, the content block on cells `a … a + N - 1` read as
`Fin.append x w`, the marker `some true` on cell `a + N = 2 * a + m`, the blank prefix below `a`, the
blanks from `pairLength a m` on, and — for a nonempty query block — that this tape is **not** the
`alignedTape` G3l's own phase produces.  `inherited_alignment_switch` locates the inherited H6 at
`switchTime a m + tailSwitchTime a m`, at index `33`, on exactly the head and tape G3k's own
`startConfig` carries, and the inherited H7 three-plus-`N` steps after that, at index `37`.  The deeper
inherited locators are **not** re-wrapped here: `handoff_exact`'s last conjunct is a universal suffix
equality, so G3l's own `handoff_endpoint_pins` and `inherited_marker_erase_switch`, and through them
G3k's four deeper ones, transport into this machine by composing that one equation with
`UniformTM.seqEmbedRight_state/_head/_tape` and `(inTail q).val = 7 + q.val`, exactly as
`inherited_alignment_switch` does; no fact is lost and none is claimed that is not proved.  The drained
theorem lands the composed accept `182` at exactly
`shiftChainClock C a m zeros d v = switchTime a m + alignmentChainClock C a m zeros d v` under G3l's
eight hypotheses unchanged.  Two rejecting branches are inherited, both forward direction only.  On a
matching tag whose physical suffix holds **no** gamma terminator the whole prefix hands over and
`malformed_reject_handoff` lands the composed reject `183` from
`switchTime a m + (tailSwitchTime a m + (N + 3 + (3 * N + 7 + (N - 7))))` on.  On a **mismatched** tag
`mismatched_tag_reject_handoff` lands it from
`switchTime a m + (tailSwitchTime a m + (N + 3 + (3 * N + 7)))` on, the gamma blocks never running;
that branch is deliberately **not** timed exactly, for the reason G3j to G3l record — on a nonempty
content the gate's own first rejection is at `3 * N + j` for its mismatch cell `j`, which this chain
does not derive from `tagMatches (Fin.append x w) = false`, the value of
`FixedContentTagGate.finalConfig`'s head being the only public trace of the `badIndex` that defines it
— and the composed run may already be in the composed reject before the time stated.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** the four handoffs before H5:
the bootstrap `startConfig` retags the actual tag-removal `finalConfig`, which `handoff_pins` records
hypothesis-free, no raw-input `initialConfig` is executed, and no clock here counts a step of any phase
*before* the origin shift — this clock does count the bootstrap phase's own `4 * a + 3 * m + 5` steps,
which no landed clock in this chain did.  No **first arrival** of the composed accept: the arrivals
proved are the bootstrap phase's and, as a hypothesis, the dispatcher's, each inside its own block.
The **fence** (all fourteen tables are uncapped, and `hfence` is a proof premise the tables do not
enforce, so an oversized register still times out); every **converse**, so neither composed reject
implies anything about the input; a **footprint** theorem, the bootstrap phase's own bounding its head
only through its own clock and saying nothing about the right block; and the pnp4 bridge, not built
here, the standalone phases' pnp4 semantics being unchanged.  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or
`ContentVerifierBridge` is stated.  `run` permits more steps than `B`, which fixes the tape extent and
is not a timeout guard.  The table is fixed and complete but not claimed state-minimal. -/
namespace Pnp3.Complexity.Uniform.V1.FixedPairOriginShiftAlignmentCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (eraseChainClock)
open FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (alignmentChainClock)

/-- The right block: the machine of the landed G3l composite, named once so that the statements below
stay readable.  An `abbrev`, hence reducible, so every pin below is a pin on that machine itself;
`table_and_resource_pins` spells the identification out. -/
abbrev tailMachine : UniformTM :=
  FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- The right block's own start configuration: G3l's landed `startConfig`, named once.  Also an
`abbrev`; `alignment_start_at_first_arrival` identifies it with what this switch hands over. -/
abbrev tailStartConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config tailMachine.stateCount (pairLength a m) B :=
  FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
    B x w

/-- G3l's own switch time — the origin-alignment phase's first arrival — named once.  Also an
`abbrev`; `clock_pins` records the identification and both closed forms. -/
abbrev tailSwitchTime (a m : Nat) : Nat :=
  FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
    a m

/-- The composed machine: the origin-shift bootstrap, then G3l's whole composite, as one closed table.
No row is new; the left rows are routed. -/
def machine : UniformTM := FixedPairOriginShiftBootstrap.machine.seq tailMachine

/-- A bootstrap state in the composed control, at its own index. -/
def inShift (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount) : Fin machine.stateCount :=
  FixedPairOriginShiftBootstrap.machine.seqLeft tailMachine q

/-- A G3l state in the composed control, shifted past the seven bootstrap states. -/
def inTail (q : Fin tailMachine.stateCount) : Fin machine.stateCount :=
  FixedPairOriginShiftBootstrap.machine.seqRight tailMachine q

/-- The routed target of a bootstrap row: `qAccept` becomes G3l's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount) : Fin machine.stateCount :=
  FixedPairOriginShiftBootstrap.machine.seqRoute tailMachine q

/-- G3l's start in the composed control, index `7`: the target of the single live routed row. -/
def tailStart : Fin machine.stateCount := inTail tailMachine.start

/-- The bootstrap phase's own `startConfig` — the retagged *actual* tag-removal endpoint — routed into
the composed control.  Still a phase-local retag, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedPairOriginShiftBootstrap.machine.seqEmbedRouted tailMachine
    (FixedPairOriginShiftBootstrap.startConfig B x w)

/-- The bootstrap phase's strict first arrival, for every input: its own landed `clock a m`.  One
`a + 1`-cell scan to the top of the blank prefix, then three steps — fetch, carry, hole — for each of
the `a + m + 1` cells of the block, then the closing accepting step. -/
def switchTime (a m : Nat) : Nat := 4 * a + 3 * m + 5

/-- Exact cost of the origin shift followed by the whole of G3l: the bootstrap phase's linear first
arrival, plus the origin-alignment phase's quadratic `(10 * a + 7) * (a + m + 1) + 3 * a`, plus the
marker-erase scan's length-only `N + 3`, plus the tag gate's length-only `3 * N + 7`, plus the
terminator's width-only `zeros + 1`, plus the anchor's width-only `2 * zeros + 5`, plus the
dispatcher's input-dependent `C`, plus G3e's `bootChainClock`.  All seven handoffs cost nothing. -/
def shiftChainClock (C a m zeros d v : Nat) : Nat :=
  switchTime a m + alignmentChainClock C a m zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the composition itself spelled out, both blocks' state counts, the
composed state and row counts, the bootstrap start and verdicts with their indices, G3l's three
distinguished states with theirs, the composed distinguished states with theirs, the block injections
with their offsets, disjointness and exhaustive coverage, `tailStart` at `7`, the three routing cases,
every left row as the routed bootstrap row, every right row as the G3l row, the public step against the
composed raw table, the **one** live routed accept row — the bootstrap state `4` on `none`, writing
`none` and staying — the **six** live routed reject rows — each of the states `1`, `2`, `3` on either
Boolean, writing that Boolean and staying — the two dead verdict copies' three rows each, and that no
**left-block** row targets either dead copy.  The two injective, disjoint block maps have domain sizes
`7` and `177`, summing to the composed state count `184`, and the coverage conjunct exhibits the
splitting map explicitly.  Thus the two block equations account for every composed row, and block
disjointness excludes right-block targets from the dead left copies as well.  The right-block equation
transports every G3l row.  Deciding rows of a table this deep unfolds the whole fourteen-block
composition, so the kernel needs a raised recursion budget here. -/
theorem table_and_resource_pins :
    machine = FixedPairOriginShiftBootstrap.machine.seq
        FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      tailMachine =
        FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      machine.stateCount = 184 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 552 ∧
      FixedPairOriginShiftBootstrap.machine.stateCount = 7 ∧ tailMachine.stateCount = 177 ∧
      FixedPairOriginShiftBootstrap.machine.start.val = 0 ∧
      FixedPairOriginShiftBootstrap.machine.accept.val = 5 ∧
      FixedPairOriginShiftBootstrap.machine.reject.val = 6 ∧
      tailMachine.start.val = 0 ∧ tailMachine.accept.val = 175 ∧ tailMachine.reject.val = 176 ∧
      machine.start = route FixedPairOriginShiftBootstrap.machine.start ∧
      machine.start = inShift FixedPairOriginShiftBootstrap.machine.start ∧
      machine.accept = inTail tailMachine.accept ∧ machine.reject = inTail tailMachine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 182 ∧ machine.reject.val = 183 ∧
      (∀ q, (inShift q).val = q.val) ∧ (∀ q, (inShift q).val < 7) ∧
      (∀ q, (inTail q).val = 7 + q.val) ∧ (∀ q, 7 ≤ (inTail q).val) ∧
      Function.Injective inShift ∧ Function.Injective inTail ∧
      (∀ p q, inShift p ≠ inTail q) ∧
      (∀ q : Fin machine.stateCount, (∃ p, q = inShift p) ∨ (∃ p, q = inTail p)) ∧
      tailStart = inTail tailMachine.start ∧ tailStart.val = 7 ∧
      route FixedPairOriginShiftBootstrap.machine.accept = tailStart ∧
      route FixedPairOriginShiftBootstrap.machine.reject = machine.reject ∧
      (∀ q, q ≠ FixedPairOriginShiftBootstrap.machine.accept →
        q ≠ FixedPairOriginShiftBootstrap.machine.reject → route q = inShift q) ∧
      (∀ q s, machine.step (inShift q) s =
        (route (FixedPairOriginShiftBootstrap.machine.step q s).1,
          (FixedPairOriginShiftBootstrap.machine.step q s).2.1,
          (FixedPairOriginShiftBootstrap.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1, (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inShift ⟨4, by decide⟩) none = (tailStart, none, .stay) ∧
      (∀ b : Bool, machine.step (inShift ⟨1, by decide⟩) (some b) =
        (machine.reject, some b, .stay)) ∧
      (∀ b : Bool, machine.step (inShift ⟨2, by decide⟩) (some b) =
        (machine.reject, some b, .stay)) ∧
      (∀ b : Bool, machine.step (inShift ⟨3, by decide⟩) (some b) =
        (machine.reject, some b, .stay)) ∧
      (∀ s, machine.step (inShift FixedPairOriginShiftBootstrap.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inShift FixedPairOriginShiftBootstrap.machine.reject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inShift q) s).1 ≠
          inShift FixedPairOriginShiftBootstrap.machine.accept ∧
        (machine.step (inShift q) s).1 ≠
          inShift FixedPairOriginShiftBootstrap.machine.reject) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedPairOriginShiftBootstrap.machine.seq_pins tailMachine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, rfl, ?_,
    rfl, rfl, by decide, by decide, by decide, fun _ => rfl, fun q => q.isLt, fun _ => rfl,
    fun _ => Nat.le_add_right _ _, hli, hri, hne, ?_, rfl, by decide, hra, hrr, hrw,
    fun q s => FixedPairOriginShiftBootstrap.machine.seq_step_left tailMachine q s,
    fun q s => FixedPairOriginShiftBootstrap.machine.seq_step_right tailMachine q s,
    fun q s => FixedPairOriginShiftBootstrap.machine.seq_step_eq_rawStep tailMachine q s,
    by decide, fun b => by cases b <;> decide, fun b => by cases b <;> decide,
    fun b => by cases b <;> decide, ?_, ?_, by decide⟩
  · exact hrw FixedPairOriginShiftBootstrap.machine.start (by decide) (by decide)
  · intro q
    have hcount : machine.stateCount = 7 + tailMachine.stateCount := rfl
    have hlt := q.isLt
    by_cases h : q.val < 7
    · exact Or.inl ⟨⟨q.val, h⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨q.val - 7, by omega⟩, Fin.ext (by show q.val = 7 + (q.val - 7); omega)⟩
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide

/-- **The bootstrap table has exactly one row targeting its accept.**  Over all seven states and all
three symbols, with the accept's own absorbing three excluded, a target of
`FixedPairOriginShiftBootstrap.machine.accept` forces the fetch state `4` on `none` — the probe that
finds the block exhausted.  So H5 has exactly **one** live routed row, the fewest a live handoff can
have (nine of the twelve landed handoffs route one row too; only H6, with three, H15, with four, and
H11, with six, are plural), and `table_and_resource_pins` exhibits it with its written `none` and its
`.stay`.  This quantifies over the bootstrap rows alone and says nothing about the composed table as
a whole: the inherited right block keeps its own rows, and the only rows this excludes are the dead
left accept copy's own three — the reject copy's are *not* excluded here — which `seq` routes to
`tailStart` and no composed row ever enters. -/
theorem accept_rows_unique (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount)
    (s : Option Bool) (hq : q ≠ FixedPairOriginShiftBootstrap.machine.accept)
    (h : (FixedPairOriginShiftBootstrap.machine.rawStep q s).1 =
      FixedPairOriginShiftBootstrap.machine.accept) :
    q.val = 4 ∧ s = none := by
  revert h
  revert hq
  revert s
  revert q
  decide

/-- **Exactly six live rows of the bootstrap table target its reject, and this classification is an
equivalence.**  Over all seven states and all three symbols, with both verdicts' own absorbing rows
excluded, a target of `FixedPairOriginShiftBootstrap.machine.reject` holds **iff** the symbol is a
Boolean and the state is one of `1`, `2`, `3` — the two carry states and the hole state, whose probes
find a cell occupied where the shift invariant requires it blank.  Both directions are stated: the list
is exhaustive *and* every one of the six really does target the reject.  It is a statement about the
fixed table, not about reachability: `bootstrap_first_arrival` proves no row of it is ever taken out of
this slice's `startConfig`, and it characterises no malformed configuration in general. -/
theorem reject_rows_unique (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairOriginShiftBootstrap.machine.accept)
    (hq : q ≠ FixedPairOriginShiftBootstrap.machine.reject) :
    (FixedPairOriginShiftBootstrap.machine.rawStep q s).1 =
        FixedPairOriginShiftBootstrap.machine.reject ↔
      (s ≠ none ∧ (q.val = 1 ∨ q.val = 2 ∨ q.val = 3)) := by
  revert hq
  revert ha
  revert s
  revert q
  decide

/-- **Every live row targeting the bootstrap reject is routed to the composed reject `183`.**  `seq`
sends each of the six to the composed reject, with the symbol written and the move unchanged.  The two
verdicts' own rows are excluded: both of their left copies are dead. -/
theorem reject_rows_routed (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairOriginShiftBootstrap.machine.accept)
    (hq : q ≠ FixedPairOriginShiftBootstrap.machine.reject)
    (h : (FixedPairOriginShiftBootstrap.machine.rawStep q s).1 =
      FixedPairOriginShiftBootstrap.machine.reject) :
    machine.step (inShift q) s =
      (machine.reject, (FixedPairOriginShiftBootstrap.machine.rawStep q s).2.1,
        (FixedPairOriginShiftBootstrap.machine.rawStep q s).2.2) := by
  have hstep : FixedPairOriginShiftBootstrap.machine.step q s =
      FixedPairOriginShiftBootstrap.machine.rawStep q s :=
    FixedPairOriginShiftBootstrap.machine.step_of_ne ha hq s
  have hleft : machine.step (inShift q) s =
      (route (FixedPairOriginShiftBootstrap.machine.step q s).1,
        (FixedPairOriginShiftBootstrap.machine.step q s).2.1,
        (FixedPairOriginShiftBootstrap.machine.step q s).2.2) :=
    FixedPairOriginShiftBootstrap.machine.seq_step_left tailMachine q s
  rw [hleft, hstep, h]
  rfl

-- The composed index of G3l's start, and of G3l's own tail start, reduced once here so that the
-- theorems below can shift G3l's indices by seven without each paying for the reduction.
private theorem tail_start_val : tailStart.val = 7 := by decide

private theorem alignment_tail_start_val :
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailStart.val
      = 26 := by decide

/-- **The start is the retagged actual tag-removal endpoint, not a raw input and not G3l's start
relabelled, and this needs no hypothesis.**  The tag-removal phase's run at its own clock is its
`finalConfig`, on the origin cell `0` over the `compactTape`; the bootstrap `startConfig` is that
configuration retagged; and this slice's `startConfig` is *that* one routed into the composed control —
the same head `0` and tape, the composed start `0` as control.  The last conjunct separates this from a
retag-only wrapper: the composed start is **not** G3l's own start re-embedded, whose control is the
right-block index `7`.  This is handoff **H4**, recorded as an identification and not executed by this
table.  No `initialConfig` and no raw pair input appears, neither retag costs a step, and no table row
of any phase before the origin shift is pinned. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let r := FixedPairTagRemoval.machine.run (FixedPairTagRemoval.clock a)
      (FixedPairTagRemoval.startConfig B x w)
    let p := FixedPairOriginShiftBootstrap.startConfig B x w
    let c := startConfig B x w
    r = FixedPairTagRemoval.finalConfig B x w ∧
      r.state = FixedPairTagRemoval.qAccept ∧
      p = FixedPairOriginShiftBootstrap.retag r ∧
      p.state = FixedPairOriginShiftBootstrap.machine.start ∧ p.head = r.head ∧ p.tape = r.tape ∧
      c = FixedPairOriginShiftBootstrap.machine.seqEmbedRouted tailMachine p ∧
      c.state = machine.start ∧ c.state = inShift FixedPairOriginShiftBootstrap.machine.start ∧
      c.head = r.head ∧ c.tape = r.tape ∧ c.head.val = 0 ∧
      c.tape = FixedPairTagRemoval.compactTape B x w ∧
      c ≠ FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
        (tailStartConfig B x w) := by
  obtain ⟨hfin, hst, -, hhead, htape⟩ := FixedPairOriginShiftBootstrap.handoff_exact (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ :=
    FixedPairOriginShiftBootstrap.machine.seq_pins tailMachine
  refine ⟨hfin, hst, ?_, rfl, hhead, htape, rfl, rfl,
    hrw FixedPairOriginShiftBootstrap.machine.start (by decide) (by decide), hhead, htape, rfl, rfl,
    fun hcon => ?_⟩
  · rw [hfin]; rfl
  · have hv : machine.start.val = 7 :=
      (congrArg Fin.val (congrArg Config.state hcon)).trans tail_start_val
    exact absurd hv (by decide)

/-- The chained clock, pinned: G3l's sum prefixed by the bootstrap phase's first arrival, that arrival
identified with the phase's own landed `clock` and given in both landed closed forms, the alignment
phase's quadratic arrival, and the full expansion the contract fixes — no extra `+ 1`, and no
replacement by a deadline or by a function of `a + m` alone.  **Neither switch time is a function of
`a + m`**: the three pairs with `a + m = 2` give `11`, `12` and `13` here and `21`, `54` and `87` in
G3l, so no reformulation of this chain's clock on `N` alone is possible, and the composed clock stays
quadratic in `a`.  The switch time is positive on every input, so the left block really does run. -/
theorem clock_pins (C a m zeros d v : Nat) :
    shiftChainClock C a m zeros d v = switchTime a m + alignmentChainClock C a m zeros d v ∧
      switchTime a m = 4 * a + 3 * m + 5 ∧
      switchTime a m = FixedPairOriginShiftBootstrap.clock a m ∧
      switchTime a m = (a + 1) + 3 * (a + m + 1) + 1 ∧
      5 ≤ switchTime a m ∧
      switchTime 0 0 = 5 ∧ switchTime 0 2 = 11 ∧ switchTime 1 1 = 12 ∧ switchTime 2 0 = 13 ∧
      tailSwitchTime a m =
        FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          a m ∧
      tailSwitchTime a m = (10 * a + 7) * (a + m + 1) + 3 * a ∧
      tailSwitchTime a m = FixedPairOriginAlignment.clock a m ∧
      tailSwitchTime 0 2 = 21 ∧ tailSwitchTime 1 1 = 54 ∧ tailSwitchTime 2 0 = 87 ∧
      alignmentChainClock C a m zeros d v =
        tailSwitchTime a m + eraseChainClock C (a + m) zeros d v ∧
      shiftChainClock C a m zeros d v =
        4 * a + 3 * m + 5 +
          ((10 * a + 7) * (a + m + 1) + 3 * a + eraseChainClock C (a + m) zeros d v) := by
  refine ⟨rfl, rfl, rfl, (FixedPairOriginShiftBootstrap.clock_exact a m).1, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  show 5 ≤ 4 * a + 3 * m + 5
  omega

/-! ### The bootstrap phase's arrival, in the shape the composition consumes -/

/-- **The bootstrap phase's strict first arrival, for every input and with no hypothesis.**  It is in
neither verdict at every time before `switchTime a m`, at that time its run **is** its `finalConfig`
and its control its accept, that time **equals** its own landed `clock a m`, and it is never in its
reject at any time at all.  The first three conjuncts repackage the landed `noEarlyTerminal` and
`run_exact`, which state the two verdicts as the phase's own `qAccept` and `qReject` — its landed
`resource_pins` identifies those with `machine.accept` and `machine.reject`; the last adds the landed
`run_after`, which keeps the accepting endpoint unchanged from the clock on.  Empty inputs and a zero
budget are included: `clock 0 0 = 5`, so the strictness range is never empty. -/
theorem bootstrap_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime a m →
        (FixedPairOriginShiftBootstrap.machine.run t
            (FixedPairOriginShiftBootstrap.startConfig B x w)).state ≠
          FixedPairOriginShiftBootstrap.machine.accept ∧
        (FixedPairOriginShiftBootstrap.machine.run t
            (FixedPairOriginShiftBootstrap.startConfig B x w)).state ≠
          FixedPairOriginShiftBootstrap.machine.reject) ∧
      FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
          (FixedPairOriginShiftBootstrap.startConfig B x w) =
        FixedPairOriginShiftBootstrap.finalConfig B x w ∧
      (FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
          (FixedPairOriginShiftBootstrap.startConfig B x w)).state =
        FixedPairOriginShiftBootstrap.machine.accept ∧
      switchTime a m = FixedPairOriginShiftBootstrap.clock a m ∧
      (∀ t, (FixedPairOriginShiftBootstrap.machine.run t
          (FixedPairOriginShiftBootstrap.startConfig B x w)).state ≠
        FixedPairOriginShiftBootstrap.machine.reject) := by
  refine ⟨fun t ht => FixedPairOriginShiftBootstrap.noEarlyTerminal x w t ht,
    FixedPairOriginShiftBootstrap.run_exact B x w,
    (FixedPairOriginShiftBootstrap.final_fields x w).2.1, rfl, fun t => ?_⟩
  by_cases ht : t < switchTime a m
  · exact (FixedPairOriginShiftBootstrap.noEarlyTerminal x w t ht).2
  · have hle : FixedPairOriginShiftBootstrap.clock a m ≤ t := by
      have : ¬ t < FixedPairOriginShiftBootstrap.clock a m := ht
      omega
    rw [show t = FixedPairOriginShiftBootstrap.clock a m +
        (t - FixedPairOriginShiftBootstrap.clock a m) by omega,
      FixedPairOriginShiftBootstrap.run_after x w (t - FixedPairOriginShiftBootstrap.clock a m)]
    exact FixedPairOriginShiftBootstrap.machine.accept_ne_reject

/-- G3l's `startConfig` is the bootstrap run at `switchTime a m`, field for field — and this holds for
**every** input, because the phase's `run_exact` is unconditional.  This is the semantic dependency H5
has to respect; it executes nothing.  The last conjunct is the whole-`Config` equality
`UniformTM.seq_handoff` consumes: the right block's start configuration *is* G3l's start on the head
and tape the bootstrap phase leaves, not merely a tape agreement or an equal numeric head. -/
theorem alignment_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    g = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
      (FixedPairOriginAlignment.startConfig B x w).state =
        FixedPairOriginAlignment.machine.start ∧
      (FixedPairOriginAlignment.startConfig B x w).head = g.head ∧
      (FixedPairOriginAlignment.startConfig B x w).tape = g.tape ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp
  rw [show FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
      (FixedPairOriginShiftBootstrap.startConfig B x w) =
      FixedPairOriginShiftBootstrap.finalConfig B x w from
    FixedPairOriginShiftBootstrap.run_exact B x w]
  exact ⟨rfl, rfl, rfl, rfl, Config.ext_parts rfl rfl rfl⟩

/-! ### The executed handoff -/

/-- **H5 fires when the bootstrap phase probes past the last block cell, finds it blank, and stays,
and it costs nothing.**  The probe cell is the endpoint head `pairLength a m + min B 1`: one past the
last block cell `2 * a + m` at `B = 0`, two at every positive `B`.  With **no hypothesis** — no tag,
no width, no room, no positive budget — the run out of `startConfig` stays strictly inside the left
block `[0, 7)` at every time strictly before `switchTime a m`, is in neither composed verdict at any
time up to and including it (at the switch time itself the control is `tailStart`, so that bound is
`≤`), is the bootstrap phase's own run routed at every such time — same head and whole tape — at
exactly `switchTime a m` **is** G3l's landed `startConfig B x w` re-embedded, and runs G3l on from
there. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let cS := FixedPairOriginShiftBootstrap.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime a m → (machine.run t c).state.val < 7) ∧
      (∀ t, t ≤ switchTime a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime a m → machine.run t c =
        FixedPairOriginShiftBootstrap.machine.seqEmbedRouted tailMachine
          (FixedPairOriginShiftBootstrap.machine.run t cS)) ∧
      machine.run (switchTime a m) c =
        FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
      (∀ s, machine.run (switchTime a m + s) c =
        FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
          (tailMachine.run s (tailStartConfig B x w))) := by
  intro cS c
  obtain ⟨hno, -, hacc, -, -⟩ := bootstrap_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, hcfg⟩ := alignment_start_at_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ :=
    FixedPairOriginShiftBootstrap.machine.seq_pins tailMachine
  have hwork : ∀ t, t < switchTime a m →
      (FixedPairOriginShiftBootstrap.machine.run t cS).state ≠
        FixedPairOriginShiftBootstrap.machine.accept := fun t ht => (hno t ht).1
  have hleft := FixedPairOriginShiftBootstrap.machine.seq_run_left tailMachine cS hwork
  have hsuffix : ∀ s, machine.run (switchTime a m + s) c =
      FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w)) := by
    intro s
    rw [hcfg]
    exact FixedPairOriginShiftBootstrap.machine.seq_handoff tailMachine cS hwork hacc s
  have hC : machine.run (switchTime a m) c =
      FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine (tailStartConfig B x w) :=
    hsuffix 0
  have hCs : (machine.run (switchTime a m) c).state = tailStart := by rw [hC]; rfl
  have hCa : (machine.run (switchTime a m) c).state ≠ machine.accept := by rw [hCs]; decide
  have hCr : (machine.run (switchTime a m) c).state ≠ machine.reject := by rw [hCs]; decide
  refine ⟨fun t ht => ?_, UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC, hsuffix⟩
  have hrt : machine.run t c = FixedPairOriginShiftBootstrap.machine.seqEmbedRouted tailMachine
    (FixedPairOriginShiftBootstrap.machine.run t cS) := hleft t (Nat.le_of_lt ht)
  rw [hrt]
  show (FixedPairOriginShiftBootstrap.machine.seqRoute tailMachine
    (FixedPairOriginShiftBootstrap.machine.run t cS).state).val < 7
  rw [hrw _ (hno t ht).1 (hno t ht).2]
  exact (FixedPairOriginShiftBootstrap.machine.run t cS).state.isLt

/-- Every configuration from the switch on is the right block's own, transported by the one embedding
that shifts the control by seven and preserves the head and the **whole** allocated tape.  The four
projections, stated once, so that the inherited locators below do not each repeat them. -/
private theorem shift_fields {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    let e := machine.run (switchTime a m + s) (startConfig B x w)
    let p := tailMachine.run s (tailStartConfig B x w)
    e.state = inTail p.state ∧ e.state.val = 7 + p.state.val ∧ e.head = p.head ∧
      e.tape = p.tape := by
  have hrun := (handoff_exact (B := B) x w).2.2.2.2 s
  exact ⟨by rw [hrun]; rfl, by rw [hrun]; rfl, by rw [hrun]; rfl, by rw [hrun]; rfl⟩

/-- **What the switch hands over is exactly what the origin-alignment phase reads.**  At the bootstrap
phase's first arrival `switchTime a m`: the composed control is G3l's start `7`, the composed head and
whole tape are *the same* projections G3l's own `startConfig` carries and, field for field, the ones the
origin-alignment phase's own `startConfig` carries; the head is the source cell
`pairLength a m + min B 1`; the tape is the `shiftedTape`, so the blank prefix occupies `[0, a)`, the
content-plus-marker block sits on `[a, pairLength a m)` and reads as `Fin.append x w` at `a + j`, the
trailing content marker is `some true` on cell `a + N = 2 * a + m`, and every allocated cell from
`pairLength a m` on is blank.  The last conjunct is the point of the phase that follows: on a nonempty
query block this tape is **not** the `alignedTape`, whose cell `0` already carries `x 0` — the origin
alignment still has to run. -/
theorem handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m) (startConfig B x w)
    let p := tailStartConfig B x w
    e.state = tailStart ∧ e.state.val = 7 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head = (FixedPairOriginAlignment.startConfig B x w).head ∧
      e.tape = (FixedPairOriginAlignment.startConfig B x w).tape ∧
      e.head.val = pairLength a m + Nat.min B 1 ∧
      e.tape = FixedPairOriginShiftBootstrap.shiftedTape B x w ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val < a → e.tape i = none) ∧
      (∀ j : Fin (a + m), e.tape ⟨a + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
      e.tape ⟨2 * a + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), pairLength a m ≤ i.val → e.tape i = none) ∧
      (0 < a → e.tape ≠ FixedPairOriginAlignment.alignedTape B x w) := by
  obtain ⟨-, -, -, hC, -⟩ := handoff_exact (B := B) x w
  obtain ⟨-, -, hhv, htv⟩ := FixedPairOriginShiftBootstrap.final_fields (B := B) x w
  obtain ⟨hlow, -, -, -, hhigh⟩ := FixedPairOriginShiftBootstrap.final_layout (B := B) x w
  obtain ⟨-, -, -, -, -, -, happ, hmark, -⟩ :=
    FixedPairOriginShiftBootstrap.phase_contract (B := B) x w
  obtain ⟨-, -, -, -, -, hal, halx, -, -, -⟩ :=
    FixedPairOriginAlignment.final_fields_and_layout (B := B) x w
  rw [FixedPairOriginShiftBootstrap.run_exact] at hhv htv hlow hhigh happ hmark
  rw [hal] at halx
  have hstate : (machine.run (switchTime a m) (startConfig B x w)).state = tailStart :=
    congrArg Config.state hC
  have hhead : (machine.run (switchTime a m) (startConfig B x w)).head =
      (tailStartConfig B x w).head := congrArg Config.head hC
  have htape : (machine.run (switchTime a m) (startConfig B x w)).tape =
      (tailStartConfig B x w).tape := congrArg Config.tape hC
  refine ⟨hstate, by rw [hstate]; exact tail_start_val, hhead, htape, hhead, htape,
    by rw [hhead]; exact hhv, by rw [htape]; exact htv,
    fun i hi => by rw [htape]; exact hlow i hi,
    fun j => by rw [htape]; exact happ j, by rw [htape]; exact hmark,
    fun i hi => by rw [htape]; exact hhigh i hi, fun hpos hcon => ?_⟩
  have hzero : FixedPairOriginAlignment.alignedTape B x w
      (⟨0, by unfold tapeLength; omega⟩ : Fin (tapeLength (pairLength a m) B)) =
      some (x ⟨0, hpos⟩) := halx ⟨0, hpos⟩
  have hblank : FixedPairOriginAlignment.alignedTape B x w
      (⟨0, by unfold tapeLength; omega⟩ : Fin (tapeLength (pairLength a m) B)) = none := by
    rw [← hcon, htape]; exact hlow _ hpos
  exact Option.noConfusion (hzero.symm.trans hblank)

/-! ### The inherited switches and the composed run -/

/-- **The inherited H6 and H7 fire inside this machine at `switchTime a m + tailSwitchTime a m` and
`N + 3` after that.**  The bootstrap phase's own steps counted first, the composed control at the
former is G3k's start at index `33` — G3l's `26` shifted by the seven bootstrap states — on exactly the
head and tape G3k's landed `startConfig` carries: the origin cell `0` over the `alignedTape`, with the
trailing content marker **still** `some true` on cell `N` and every allocated cell above `N` blank.  At
the latter the control is G1's content-tag-gate start at index `37` — G3l's `30` shifted by seven — the
marker now erased by the inherited routed row itself.  The deeper inherited locators are not re-wrapped
here; `handoff_exact`'s universal suffix equality transports G3l's own verbatim. -/
theorem inherited_alignment_switch {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m + tailSwitchTime a m) (startConfig B x w)
    let p :=
      FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailStartConfig
        B x w
    e.state.val = 33 ∧ e.head = p.head ∧ e.tape = p.tape ∧ e.head.val = 0 ∧
      e.tape = FixedPairOriginAlignment.alignedTape B x w ∧
      e.tape ⟨a + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 ≤ i.val → e.tape i = none) ∧
      (machine.run (switchTime a m + (tailSwitchTime a m + (a + m + 3)))
        (startConfig B x w)).state.val = 37 := by
  obtain ⟨-, hsv, hhd, htp⟩ := shift_fields x w (tailSwitchTime a m)
  obtain ⟨hs, -, hhead, htape, -, -, hhv, htv, hmark, hblank⟩ :=
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins
      (B := B) x w
  obtain ⟨-, hsv7, -, -⟩ := shift_fields x w (tailSwitchTime a m + (a + m + 3))
  obtain ⟨h7, -, -, -, -, -⟩ :=
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inherited_marker_erase_switch
      (B := B) x w
  have hs26 : (tailMachine.run (tailSwitchTime a m) (tailStartConfig B x w)).state.val = 26 :=
    (congrArg Fin.val hs).trans alignment_tail_start_val
  have hs30 : (tailMachine.run (tailSwitchTime a m + (a + m + 3))
    (tailStartConfig B x w)).state.val = 30 := h7
  refine ⟨?_, hhd.trans hhead, htp.trans htape, by rw [hhd]; exact hhv, htp.trans htv,
    by rw [htp]; exact hmark, fun i hi => by rw [htp]; exact hblank i hi, ?_⟩
  · rw [hsv, hs26]
  · rw [hsv7, hs30]

/-- **The concrete exact run: the origin shift, H5, the origin alignment, H6, the marker erasure, H7,
the content tag gate, H8, the gamma terminator, H9, the gamma anchor, H10, the payload dispatcher, H11,
the scratch bootstrap, H12, the first and second payload digits, H13 and H14, the markers, H15, the
loop, H16, the decrement, H17 and the countdown, one machine.**  Under G3l's **eight** hypotheses
unchanged, after exactly `shiftChainClock C a m zeros d v` steps the composed machine is in its accept,
the countdown's `qDone`, on the separator blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 v`,
persisting.  The new prefix is executed before G3l's result is consumed: the left block runs its own
`switchTime a m` steps first, and `handoff_exact`'s suffix equality is what carries G3l's endpoint
across.  `v` is universally quantified and unsupplied — nothing here decodes it — and persistence is
exact execution at that time plus absorption, not first arrival of the composed accept.  Neither
`C ≤ deadline N` nor a successful-`q` premise is added: `StrictFirstTerminalAt` is the whole dispatcher
hypothesis, and no positive budget, budget-dominates-clock premise or accepted-content membership is
assumed either. -/
theorem shift_alignment_countdown_drained {a m B C zeros v F : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let D := shiftChainClock C a m zeros d v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.origin_alignment_marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (shiftChainClock C a m zeros (borrow x w zeros) v) (startConfig B x w) =
      FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
        (tailMachine.run (alignmentChainClock C a m zeros (borrow x w zeros) v)
          (tailStartConfig B x w)) :=
    hsuffix (alignmentChainClock C a m zeros (borrow x w zeros) v)
  have hstate : (machine.run (shiftChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head, he2]
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = shiftChainClock C a m zeros (borrow x w zeros) v +
      (t - shiftChainClock C a m zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject on a matching tag with no gamma terminator.**  The bootstrap phase hands over
at `switchTime a m`, the origin alignment `tailSwitchTime a m` after that, the marker erasure `N + 3`
after that and the gate `3 * N + 7` after that, the composed run is in neither verdict before
`switchTime a m + (tailSwitchTime a m + (N + 3 + (3 * N + 7 + (N - 7))))`, and from that time on it is
in the composed reject — index `183`, not the bootstrap `qReject` at `6`, nor the alignment one at `32`,
nor the marker-erase one at `36`, nor G1's at `51`, nor G2's at `54` — on the blank boundary cell `N`,
over the `contentTape`: the anchor never runs.  **Not** a converse; it characterises no parsed
target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime a m + (tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime a m + (tailSwitchTime a m +
            (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) := by
  intro c
  obtain ⟨-, hnoPre, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨hno, hpost⟩ :=
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.malformed_reject_handoff
      (B := B) x w htag hg
  have hts : tailSwitchTime a m =
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
      a m := rfl
  have hshift : ∀ s, (machine.run (switchTime a m + s) c).state =
      inTail (tailMachine.run s (tailStartConfig B x w)).state := by
    intro s; rw [hsuffix s]; rfl
  refine ⟨fun t ht => ?_, fun s hs => ?_⟩
  · by_cases hle : t ≤ switchTime a m
    · exact hnoPre t hle
    · have hgt : switchTime a m ≤ t := Nat.le_of_lt (Nat.lt_of_not_le hle)
      obtain ⟨ha, hr⟩ := hno (t - switchTime a m) (by omega)
      have hst := hshift (t - switchTime a m)
      rw [show switchTime a m + (t - switchTime a m) = t by omega] at hst
      refine ⟨fun hcon => ha ?_, fun hcon => hr ?_⟩
      · exact (Function.Injective.eq_iff
          ((FixedPairOriginShiftBootstrap.machine.seq_pins
            tailMachine).2.2.2.2.2.2.2.1)).mp (hst.symm.trans hcon)
      · exact (Function.Injective.eq_iff
          ((FixedPairOriginShiftBootstrap.machine.seq_pins
            tailMachine).2.2.2.2.2.2.2.1)).mp (hst.symm.trans hcon)
  · obtain ⟨hrj, hhd, htp⟩ := hpost (s - switchTime a m) (by omega)
    have hrun := hsuffix (s - switchTime a m)
    rw [show switchTime a m + (s - switchTime a m) = s by omega] at hrun
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
    · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
    · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

/-- **The routed reject on a mismatched tag.**  From
`switchTime a m + (tailSwitchTime a m + (N + 3 + (3 * N + 7)))` on — the bootstrap phase's arrival, the
alignment phase's, the marker-erase scan's and the gate's length-only deadline — the composed run is in
the composed reject `183`, on the gate's own `finalConfig` head, its mismatch cell clamped to `N`, over
the `contentTape`; the gamma blocks never run.  Forward direction only, and **not** timed exactly: this
time is the gate's deadline, not its first rejection, so the composed run may already be in the
composed reject strictly earlier, and nothing here says when.  On a nonempty content the gate first
rejects at `3 * N + j` for its mismatch cell `j`, which this slice does not derive from
`tagMatches (Fin.append x w) = false`; `FixedContentTagGate.finalConfig`'s head is the only public
trace of the `badIndex` that defines it.  **Not** a converse either. -/
theorem mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime a m + (tailSwitchTime a m + (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w := by
  intro s hs
  obtain ⟨-, -, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  have hts : tailSwitchTime a m =
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
      a m := rfl
  obtain ⟨hrj, hhd, htp⟩ :=
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.mismatched_tag_reject_handoff
      (B := B) x w htag (s - switchTime a m) (by omega)
  have hrun := hsuffix (s - switchTime a m)
  rw [show switchTime a m + (s - switchTime a m) = s by omega] at hrun
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

end Pnp3.Complexity.Uniform.V1.FixedPairOriginShiftAlignmentCountdown
