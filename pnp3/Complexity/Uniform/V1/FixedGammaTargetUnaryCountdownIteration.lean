import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown

/-!
# Iterating the gamma target countdown round (Part A G2u)

**No new machine and no new table row.**  Every step below is G2s-a's fixed 11-state, 33-row
`FixedGammaTargetUnaryCountdown.machine`, run for longer.  Write `N = a + m` and
`S = N + 2 + zeros` for the separator blank.  `pnp3/Docs/UniformP_V1.md` carries the long-form
design notes.  Classification: **Infrastructure**.  Nothing here is P-vs-NP mainline progress.

G2s-a proves one round out of an arbitrary `qLoop` configuration on `S`, one exhaustion out of an
all-`false` register, and the entry plus one round out of the phase-local `startConfig`.  This
module composes those, and nothing else.  `iterate_generic` chains `round_generic` with itself `k`
times; `drain_generic` takes `k := v`, so the register reaches zero and G2s-a's `exhaust_generic`
fires; `register_drained` does both out of the landed `startConfig`, reusing the entry
identification `first_round` already performs -- the portion of it that does not use positivity.

The clocks are closed forms of sums of G2s-a's clocks.  `roundsClock zeros r k` is
`∑_{i < k} roundClock zeros (r + i)`, written `k*k + k*(2*zeros + 2*r + 6)` so that no `Nat`
subtraction occurs anywhere; `drainClock` adds the exhaustion, `fullClock` the entry.  Each is an
**exact** time out of its own configuration, and each counts the steps of this phase alone -- not
one of the steps `startConfig` embeds, and no clock of any earlier phase.

**The fence policy, reconciled.**  The G2s-a entry in `pnp3/Docs/UniformP_V1.md` states two
requirements.  The first is that this slice's loop theorem take `F` as a parameter with room
premise `zeros + 2 + F <= a + B`; every execution theorem below carries it.  The second is that
the justification for `F = N` be derived or replaced first -- and that requirement is about a
different object.  The theorems here are **canonical bounded execution lemmas**: `F` is an explicit
parameter of the *statement*, the tape is the unchanged canonical `loopTape`, and no cell of it is a
cutoff.  They are **not** execution with an installed cutoff, and they are not claimed to survive
one: an installed `some false` at `N + 3 + zeros + F` is not a `loopTape` -- `loopTape` is blank
there -- so the execution theorems would have to be re-proved against that tape, and nothing here is
evidence that it can be.  The executed-fence requirement therefore stands, unchanged and
undischarged, for the fenced machine that a later phase must build; it is not a precondition of
lemmas that install nothing.  The production statements leave `F` abstract; the surface tests use
literal budgets.  No general `F = N` bound is claimed.

`lane_room` is **sufficient and used, never necessary**, and it is not even the tightest sufficient
condition: it reserves the cell at `N + 3 + zeros + F` that an installed cutoff would occupy, so it
can fail on a budget where the canonical unfenced drain still completes -- at `a = m = zeros = 0`,
`v = F = 1`, `B = 2` it fails while the drain finishes on the tape, which the surface test's
`check_below_room_drain_probe` reduces.  No footprint or budget theorem exists here, so no room
premise is shown necessary and none is claimed.

Deferred, and deliberately not claimed.  The **fence phase** itself: the lane is still uncapped in
the machine, a register too large for the budget still runs `qRunEnd` off the end of the tape and
sticks there, which is a timeout and therefore neither verdict, and the `qRunEnd`-on-`some false`
row stays pinned and unexercised.  Any **pnp4 bridge**, and with it every connection to
`contentHeader?`, to `contentInput?` or to a parsed target: `v` is universally quantified here and
no theorem of this module supplies one.  Every **converse**: nothing says that `qLoop` at
`roundsClock`, that `qDone`, or that any endpoint cell implies anything about `zeros`, about `v`,
about `k` or about the incoming digits.  **First arrival**: `qDone` absorbs, so the persistence
conjuncts are persistence and nothing more -- no theorem here says `qDone` is entered for the
*first* time at `drainClock` or at `fullClock`, and none is proved.  A **malformed-gamma branch**,
since G2q characterises no non-`qDone` endpoint to route.  And any restoration of the gamma
leading-digit convention, which G2q already destroyed.

The lane holds `v` marks, where `v` is the **parameter** whose register digits are *hypothesised*:
calling them the target in unary would be a claim about a decoded value, and no theorem here
decodes a register, executes a parser or produces a `v` from a parse.  `qDone` is `machine.accept`
of a machine started from a phase-local retag of an *actual* prior run rather than from
`initialConfig` on a raw pair input, so reaching it is phase-local acceptance -- neither halting of
a composed machine nor raw-input language acceptance.  This module states no `accepts`, no
`AcceptsAt` and no language membership.  `v = 0` is a legitimate case of `drain_generic`, where no
round runs and the exhaustion fires at once; it cannot inhabit `register_drained`'s digit
hypotheses under `2 <= zeros`, so no concrete zero-target coverage is advertised.  Clock
composition with earlier phases, the fixed parser, advice freedom, `NP` membership and
`ContentVerifierBridge` are out of scope. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration

open PairEncoding
open FixedGammaTargetRegisterDecrement (decBit borrow deadline)
open FixedGammaTargetUnaryCountdown

/-! ### The register width, as arithmetic

Pure `Nat` facts about `testBit`: no machine, no tape, no parser and no codec occurs in this
section.  `v` is an arbitrary natural throughout. -/

/-- The register-width hypothesis in its two interchangeable forms.  "`v` has no digit above
`zeros`" and "`v < 2 ^ (zeros + 1)`" are one condition, which is what lets the decrement be taken
`k` times without re-deriving the bound at each round.  Nothing here decodes `v`. -/
theorem high_iff_lt (v zeros : Nat) :
    (∀ b, zeros < b → v.testBit b = false) ↔ v < 2 ^ (zeros + 1) :=
  ⟨fun h => Nat.lt_pow_two_of_testBit v fun i hi => h i (by omega),
    fun h b hb =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))⟩

/-- Subtraction cannot create a high digit: the register stays `zeros + 1` digits wide however many
rounds have run.  This is the conjunct the induction below threads, and it is load-bearing -- a `v`
with a digit above `zeros` is not the value the `zeros + 1` register cells physically hold. -/
private theorem high_sub {v zeros : Nat} (hhigh : ∀ b, zeros < b → v.testBit b = false) (k : Nat) :
    ∀ b, zeros < b → (v - k).testBit b = false := by
  intro b hb
  refine Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Nat.sub_le v k) ?_)
  exact Nat.lt_of_lt_of_le ((high_iff_lt v zeros).1 hhigh)
    (Nat.pow_le_pow_right (by omega) (by omega))

/-! ### The clocks -/

/-- Exact cost of `k` consecutive rounds out of `qLoop` at `r` marks already laid: the closed form
of `∑_{i < k} roundClock zeros (r + i)`, written without any `Nat` subtraction.  `qPadL` and `qPadR`
make each round independent of the stored digits, so the only dependence is on how many marks the
lane already holds. -/
def roundsClock (zeros r k : Nat) : Nat := k * k + k * (2 * zeros + 2 * r + 6)

/-- Exact cost of `v` rounds followed by the exhaustion, out of a register holding `v`. -/
def drainClock (zeros r v : Nat) : Nat := roundsClock zeros r v + zeroClock zeros

/-- Exact cost of the entry at offset `d` followed by the whole drain. -/
def fullClock (zeros d v : Nat) : Nat := (d + 2) + drainClock zeros 0 v

/-- The recurrence the induction consumes: one more round costs `roundClock zeros r`, and the rest
run against a lane that already holds one more mark. -/
private theorem rounds_succ (zeros r k : Nat) :
    roundsClock zeros r (k + 1) = roundClock zeros r + roundsClock zeros (r + 1) k := by
  unfold roundsClock roundClock
  ring

/-- Closed forms of the three clocks, the recurrence that drives the induction, and the two
compositions.  Each is an exact time out of its own configuration; only the drain's endpoint
absorbs, so only its time carries a persistence conjunct below. -/
theorem rounds_clock_pins (zeros r k v d : Nat) :
    roundsClock zeros r k = k * k + k * (2 * zeros + 2 * r + 6) ∧
      roundsClock zeros r 0 = 0 ∧
      roundsClock zeros r 1 = roundClock zeros r ∧
      roundsClock zeros r (k + 1) = roundClock zeros r + roundsClock zeros (r + 1) k ∧
      drainClock zeros r v = roundsClock zeros r v + zeroClock zeros ∧
      fullClock zeros d v = (d + 2) + drainClock zeros 0 v ∧
      fullClock zeros d 1 = firstClock zeros d + zeroClock zeros := by
  refine ⟨rfl, ?_, ?_, rounds_succ zeros r k, rfl, rfl, ?_⟩ <;>
    simp only [roundsClock, roundClock, drainClock, fullClock, firstClock, zeroClock] <;> omega

/-- **The lane budget.**  `F` is an explicit parameter: a bound on how many marks the lane is
allowed to hold.  Under `r + k ≤ F` and `zeros + 2 + F ≤ a + B`, every round of the iteration and
the exhaustion have their own room, and one cell past the last mark is reserved besides.  Nothing
here instantiates `F`, nothing lays a cutoff at `N + 3 + zeros + F`, and this condition is
sufficient and used, never shown necessary -- the reserved cell is why it can fail on a budget where
the canonical unfenced drain still completes, as the surface test's `check_below_room_drain_probe`
exhibits. -/
theorem lane_room {a m B zeros r k F : Nat} (hfence : r + k ≤ F) (hroom : zeros + 2 + F ≤ a + B) :
    (∀ i, i ≤ k → a + m + 3 + zeros + (r + i) < tapeLength (pairLength a m) B) ∧
      a + m + 2 + zeros < tapeLength (pairLength a m) B := by
  unfold tapeLength pairLength
  exact ⟨fun i hi => by omega, by omega⟩

/-! ### The iteration -/

private theorem iterate_at {a m B zeros F : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : zeros + 2 + F ≤ a + B) :
    ∀ k v r : Nat, r + k ≤ F → k ≤ v → (∀ b, zeros < b → v.testBit b = false) →
      ∀ c : Config stateCount (pairLength a m) B, c.state = qLoop →
        c.head.val = a + m + 2 + zeros → c.tape = loopTape B x w zeros v r →
        (machine.run (roundsClock zeros r k) c).state = qLoop ∧
          (machine.run (roundsClock zeros r k) c).head.val = a + m + 2 + zeros ∧
          (machine.run (roundsClock zeros r k) c).tape =
            loopTape B x w zeros (v - k) (r + k) := by
  intro k
  induction k with
  | zero =>
      intro v r _ _ _ c hq hh ht
      have h0 : roundsClock zeros r 0 = 0 := by unfold roundsClock; omega
      rw [h0]
      exact ⟨hq, hh, ht⟩
  | succ k ih =>
      intro v r hf hkv hhigh c hq hh ht
      have hr0 : a + m + 3 + zeros + r < tapeLength (pairLength a m) B :=
        (lane_room hf hroom).1 0 (Nat.zero_le _)
      obtain ⟨h1, h2, h3⟩ := round_generic x w hr0 (by omega) hhigh c hq hh ht
      obtain ⟨g1, g2, g3⟩ := ih (v - 1) (r + 1) (by omega) (by omega) (high_sub hhigh 1)
        (machine.run (roundClock zeros r) c) h1 h2 h3
      rw [rounds_succ zeros r k, machine.run_add]
      refine ⟨g1, g2, ?_⟩
      rw [g3, show v - 1 - k = v - (k + 1) by omega, show r + 1 + k = r + (k + 1) by omega]

/-- **Arbitrary iteration.**  Out of an arbitrary `qLoop` configuration on the separator blank whose
register holds `v` and whose lane holds `r` marks, `k` rounds cost exactly `roundsClock zeros r k`
and leave the register holding `v - k` with `r + k` marks -- the same canonical `loopTape`, so the
endpoint is again an entry point of this theorem.  `k ≤ v` is what keeps every one of those rounds a
subtraction rather than an exhaustion, and `hhigh` is what ties the abstract `v` to the `zeros + 1`
digits the register physically holds; both are load-bearing, and dropping either breaks the
conclusion at `0 < k`.  `qLoop` does not absorb, so this is an exact time and not a deadline, no
conjunct claims first arrival, and no cell of the tape is a cutoff. -/
theorem iterate_generic {a m B zeros F : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : zeros + 2 + F ≤ a + B) :
    ∀ k v r : Nat, r + k ≤ F → k ≤ v → (∀ b, zeros < b → v.testBit b = false) →
      ∀ c : Config stateCount (pairLength a m) B, c.state = qLoop →
        c.head.val = a + m + 2 + zeros → c.tape = loopTape B x w zeros v r →
        let e := machine.run (roundsClock zeros r k) c
        e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧
          e.tape = loopTape B x w zeros (v - k) (r + k) :=
  fun k v r hf hkv hhigh c hq hh ht => iterate_at x w hroom k v r hf hkv hhigh c hq hh ht

/-- **The drain.**  Taking `k := v` runs the register to zero, and G2s-a's exhaustion then fires, so
after exactly `drainClock zeros r v` steps the machine is in `qDone` on the separator blank with an
all-`false` register and `r + v` marks in the lane.  `qDone` absorbs, so the last conjunct is
persistence and not first arrival: no theorem says `qDone` is entered for the first time at this
time.  There is no `1 ≤ v` hypothesis -- at `v = 0` no round runs and the exhaustion fires at once.
Here the incoming configuration is arbitrary subject to the canonical-tape hypotheses; reaching
`qDone` proves no raw-input language acceptance.  `drainClock` counts steps from that configuration. -/
theorem drain_generic {a m B zeros v r F : Nat} (x : Bitstring a) (w : Bitstring m)
    (hfence : r + v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hhigh : ∀ b, zeros < b → v.testBit b = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros v r) :
    let e := machine.run (drainClock zeros r v) c
    e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 (r + v) ∧
      (∀ t, drainClock zeros r v ≤ t → machine.run t c = e) := by
  obtain ⟨h1, h2, h3⟩ := iterate_at x w hroom v v r hfence le_rfl hhigh c hq hh ht
  rw [Nat.sub_self] at h3
  obtain ⟨g1, g2, g3, -⟩ := exhaust_generic x w (lane_room hfence hroom).2 _ h1 h2 h3
  have hE : machine.run (drainClock zeros r v) c
      = machine.run (zeroClock zeros) (machine.run (roundsClock zeros r v) c) := by
    rw [show drainClock zeros r v = roundsClock zeros r v + zeroClock zeros from rfl,
      machine.run_add]
  have hstate : (machine.run (drainClock zeros r v) c).state = qDone := by rw [hE]; exact g1
  refine ⟨hstate, by rw [hE]; exact g2, by rw [hE]; exact g3, fun t hts => ?_⟩
  rw [show t = drainClock zeros r v + (t - drainClock zeros r v) by omega, machine.run_add]
  exact machine.run_accept _ hstate _

/-! ### The concrete exact run out of the landed start configuration -/

private theorem width_le {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    9 + zeros ≤ a + m := by
  have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
  omega

/-- **The concrete exact run: `startConfig` to `qDone`, register empty, `v` marks laid.**  Out of
the landed phase-local `startConfig B x w` -- the *actual* G2q machine retagged at G2q's own
length-only `deadline (a + m)`, not an arbitrary configuration -- the machine *enters* `qLoop` on
the separator blank after exactly `d + 2` steps with the register holding `v`, and after exactly
`fullClock zeros d v` steps is in the absorbing `qDone` on that same cell with every register cell
`some false`, exactly `v` marks in the lane `[N+3+zeros, N+3+zeros+v)` and blanks beyond.  That
endpoint persists, which is all the persistence conjunct claims: nothing says `qDone` is entered
there for the first time.

`v` is universally quantified and nothing here supplies one: the marks are `v` marks, where `v` is
the parameter whose digits the entry register is *hypothesised* to hold, and no theorem of this
module decodes a register, executes a parser or produces a `v` from a parse.  `F` is a parameter and
nothing instantiates it.  `fullClock` counts the steps of this phase alone -- not one of the steps
`startConfig` embeds.  Under `2 ≤ zeros` the digit hypothesis cannot be inhabited at `v = 0`, so
this theorem covers no concrete zero target. -/
theorem register_drained {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let c0 := machine.run (d + 2) (startConfig B x w)
    let e := machine.run (fullClock zeros d v) (startConfig B x w)
    c0.state = qLoop ∧ c0.head.val = a + m + 2 + zeros ∧ c0.tape = loopTape B x w zeros v 0 ∧
      e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧
        e.tape = loopTape B x w zeros 0 v ∧
        (∀ t, fullClock zeros d v ≤ t → machine.run t (startConfig B x w) = e) ∧
        (∀ j, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + j →
          e.tape i = some false) ∧
        (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros ≤ i.val →
          i.val < a + m + 3 + zeros + v → e.tape i = some true) ∧
        (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros + v ≤ i.val →
          e.tape i = none) := by
  have hN := width_le x w hg
  have hroom2 : a + m + 2 + zeros < tapeLength (pairLength a m) B :=
    (lane_room (r := 0) (k := 0) (Nat.zero_le F) hroom).2
  have hd := (FixedGammaTargetRegisterDecrement.borrow_pins x w zeros).1
  obtain ⟨-, hh0, ht0, -, -, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented x w htag hg hzeros hroom2
  have hcover : FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w) =
      FixedGammaTargetRegisterDecrement.machine.run
        (FixedGammaTargetRegisterDecrement.decClock (a + m) zeros (borrow x w zeros))
        (FixedGammaTargetRegisterDecrement.startConfig B x w) :=
    hclamp _ ((FixedGammaTargetRegisterDecrement.clock_pins (a + m) zeros
      (borrow x w zeros)).2.2.2.2 hN hd)
  have hcq : (startConfig B x w).state = qStart := rfl
  have hch : (startConfig B x w).head.val = a + m + 1 + zeros - borrow x w zeros := by
    change (FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w)).head.val = _
    rw [hcover]
    exact hh0
  have hct : (startConfig B x w).tape = loopTape B x w zeros v 0 := by
    change (FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w)).tape = _
    rw [hcover, ht0]
    exact (loopTape_zero_eq_decTape x w htag hg hv).symm
  have hlowb : ∀ b, b < borrow x w zeros → v.testBit b = true := by
    intro b hb
    have h := hv (zeros - b) (by omega)
    rw [show zeros - (zeros - b) = b by omega] at h
    rw [h]
    unfold decBit
    rw [if_neg (by omega), if_neg (by omega)]
  have hstopb : v.testBit (borrow x w zeros) = false := by
    have h := hv (zeros - borrow x w zeros) (by omega)
    rw [show zeros - (zeros - borrow x w zeros) = borrow x w zeros by omega] at h
    rw [h]
    unfold decBit
    rw [if_neg (by omega), if_pos rfl]
  obtain ⟨he1, he2, he3⟩ :=
    entry_generic (v := v) x w hroom2 hd hlowb hstopb (startConfig B x w) hcq hch hct
  obtain ⟨hf1, hf2, hf3, hf4⟩ :=
    drain_generic (r := 0) (F := F) x w (by omega) hroom hhigh
      (machine.run (borrow x w zeros + 2) (startConfig B x w)) he1 he2 he3
  rw [Nat.zero_add] at hf3
  have hE : machine.run (fullClock zeros (borrow x w zeros) v) (startConfig B x w)
      = machine.run (drainClock zeros 0 v)
        (machine.run (borrow x w zeros + 2) (startConfig B x w)) := by
    rw [show fullClock zeros (borrow x w zeros) v
      = (borrow x w zeros + 2) + drainClock zeros 0 v from rfl, machine.run_add]
  have htape : (machine.run (fullClock zeros (borrow x w zeros) v) (startConfig B x w)).tape
      = loopTape B x w zeros 0 v := by rw [hE]; exact hf3
  refine ⟨he1, he2, he3, by rw [hE]; exact hf1, by rw [hE]; exact hf2, htape, fun t hts => ?_,
    fun j hj i hi => ?_, fun i h1 h2 => ?_, fun i h => ?_⟩
  · have hts' : (borrow x w zeros + 2) + drainClock zeros 0 v ≤ t := hts
    rw [show t = (borrow x w zeros + 2) + (t - (borrow x w zeros + 2)) by omega,
      machine.run_add, hE]
    exact hf4 _ (by omega)
  · rw [htape, (loopTape_pins x w).1 j hj i hi, Nat.zero_testBit]
  · rw [htape]
    exact (loopTape_pins x w).2.2.2.1 i h1 h2
  · rw [htape]
    exact (loopTape_pins x w).2.2.2.2.1 i h

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration
