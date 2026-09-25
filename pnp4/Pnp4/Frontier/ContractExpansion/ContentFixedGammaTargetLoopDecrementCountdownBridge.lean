import Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetDecrementCountdownBridge

/-!
# The executed payload-loop-to-G2x handoff on the parsed target (Part A G2y)

G2x ran G2q's decrement and G2s-a's countdown as one machine, out of G2q's own `startConfig` — a
proof-level retag of the payload loop's run at G2q's length-only deadline — for exactly
`B := polyClock 3 (pairLength a m)` steps, under three hypotheses.  This module runs **one machine**
for the payload loop, the decrement *and* the countdown under the **same three hypotheses** at the
**same budget**: the pnp3 G2y composed `FixedGammaTargetLoopDecrementCountdown.machine`, G2p-d's
22-state round table followed by G2x's 18-state composite as one closed 40-state table.  The routed
row `qFin`-on-`some false` → G2x's `qStart` (index `19` → `22`) is the newly executed cross-block
edge H16; G2x's own `qBorrow`-on-`some true` row (index `26` → `29`) is H17, inherited.  Neither is
the table's only cross-block edge: `seq` also routes every round row targeting `qReject` into the
composed reject, and the dead left `qDone` rows into G2x's start.  Write `N = a + m`,
`zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`.

`loop_decrement_countdown_drained_accepted_content_at_polyClock` has exactly G2x's hypotheses — the
parse, the acceptance, `3 ≤ pr.2.n`, at the concrete `treeCircuitWitnessCodec (thresholdPoly k)` —
and no tag, cap, room, budget, clock, width, digit, initial-state, correctness or runtime premise.
Out of the composed `startConfig` — the payload round's own, the retagged *actual* G2p-d foundation
endpoint, routed — it concludes the cap `pr.2.n ≤ N`, the length bound `11 ≤ N`, the tag,
`pr.2.n = pr.1`, the header and the width; the chained clock
`C = totalClock N zeros + composedClock N zeros d pr.2.n ≤ B`; **the executed handoff H16** — before
`T = totalClock N zeros` the composed control is in neither verdict, and at exactly `T` the composed
configuration *is* G2x's landed `startConfig B x w` re-embedded, the switch happening at the payload
loop's first arrival (`loop_strict`), not at G2q's deadline; and at exactly `C`, at exactly `B` and
at every later time, the composed accept on the separator blank `N + 2 + zeros` with tape
`loopTape B x w zeros 0 pr.2.n`, one equality from which the cleared register, exactly `pr.2.n`
marks and the blanks beyond follow (G2x's cell-by-cell conjuncts are not restated).  The
target is tracked as `pr.2.n`, the field `ContentAccepts` reads; the register value is the G2r digit
fact on the decoded header, as in G2v and G2x; nothing here executes a parser.

The arithmetic.  G2x's domination lemma is private and bounds `composedClock` alone, so
`chainClock_le_polyClock` expands the public clock formulas instead.  Its inputs are exactly
`pr.2.n ≤ N`, `d ≤ zeros`, `2 ≤ zeros` and `9 + zeros ≤ N`, the last two giving `11 ≤ N`; neither
`3 ≤ pr.2.n` nor a decoded bound `zeros ≤ pr.2.n` is consumed, since `9 + zeros ≤ N` already caps
`zeros` by the length.  `totalClock N zeros ≤ 3N²` is G2q's `prior_covers` at `9 + zeros ≤ N`;
`composedClock N zeros d pr.2.n ≤ 3N² + 12N + 7` follows from `clock_pins` under `pr.2.n ≤ N`,
`d ≤ zeros` and `zeros ≤ N`; and their sum is at most `(N+1)³ + 3 ≤ B` once `11 ≤ N`.  The gamma
contract supplies `9 + zeros ≤ N` from the decoded width.  The exponent `3` is sufficient and not
shown least; `B` is both tape budget and step count, an instantiation choice.

Not claimed.  **Two handoffs of seventeen**: `startConfig` still embeds every earlier phase, the
fifteen handoffs before H16 stay proof-level, no `initialConfig` on a raw pair input is executed,
and no clock here counts a step of any earlier phase.  **Composed first arrival**: nothing says `C`
is the first time the composed accept is entered; the first arrival used here is the payload loop's,
inside the left block.  **The fence**: all three tables are unfenced; accepted words never overflow
the lane, since `pr.2.n ≤ N` is derived, but an overshooting word still runs off the tape and
sticks, a timeout and neither verdict, and no rejected or malformed input is characterised here.
**Small targets** `0`, `1`, `2` are excluded by `3 ≤ pr.2.n`, as in G2w-b and G2x.  **Every
converse**, every witness-check phase, and the **model connection**: this is a V1 `UniformTM` on
`Option Bool` cells laid out against `pairLength a m`, while `ContentVerifierBridge` asks for the
legacy `TM` with a `runTime` field on `concatBitstring x w`; the legacy `runTime` advice channel of
`VERIFIER_RETARGET_PLAN.md` caveat 6 is untouched.  Reaching the composed accept out of a retagged
actual prior endpoint is neither halting on a raw input nor language acceptance.  No `accepts`,
`AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation`, `NP` membership, advice-freedom claim
or `ContentVerifierBridge` is stated, and neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced.

**Progress classification (AGENTS.md): Infrastructure.**  It makes no `P ≠ NP` claim.
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-- **The cubic budget dominates the chained clock.**  Pure arithmetic: under `n ≤ a + m`,
`d ≤ zeros`, `2 ≤ zeros` and `9 + zeros ≤ a + m`, the loop's `totalClock (a+m) zeros` is at most
G2q's `priorDeadline (a+m) = 3 (a+m)²`, G2x's `composedClock (a+m) zeros d n` is at most
`3 (a+m)² + 12 (a+m) + 7`, and `(a + m + 1) ^ 3 + 3 ≤ polyClock 3 (pairLength a m)` exceeds their
sum once `11 ≤ a + m`, which the last two premises give.  The decoded width bound `zeros ≤ n` G2x
needs is not needed here, because `9 + zeros ≤ a + m` already caps `zeros` by the length.  G2x's own
domination lemma is private, so the public clock formulas are expanded here rather than reused.
Sufficient; the exponent `3` is not shown least. -/
private theorem chainClock_le_polyClock {a m zeros d n : Nat}
    (hcap : n ≤ a + m) (hd : d ≤ zeros) (hzeros : 2 ≤ zeros)
    (hzN : 9 + zeros ≤ a + m) :
    FixedGammaTargetLoopDecrementCountdown.chainClock (a + m) zeros d n
      ≤ polyClock 3 (PairEncoding.pairLength a m) := by
  have hN : 11 ≤ a + m := by omega
  have hchain : FixedGammaTargetLoopDecrementCountdown.chainClock (a + m) zeros d n =
      FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros +
        FixedGammaTargetDecrementCountdown.composedClock (a + m) zeros d n :=
    rfl
  have hloop : FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros
      ≤ 3 * ((a + m) * (a + m)) := FixedGammaTargetRegisterDecrement.prior_covers hzN
  rw [hchain, (FixedGammaTargetDecrementCountdown.clock_pins (a + m) zeros d n).2.1]
  have hP : a + m + 1 ≤ PairEncoding.pairLength a m := by
    unfold PairEncoding.pairLength
    omega
  have hcube : (a + m + 1) ^ 3 ≤ PairEncoding.pairLength a m ^ 3 := Nat.pow_le_pow_left hP 3
  have hexp : (a + m + 1) ^ 3
      = (a + m) * (a + m) * (a + m) + 3 * ((a + m) * (a + m)) + 3 * (a + m) + 1 := by ring
  have hsq : 11 * (a + m) ≤ (a + m) * (a + m) := Nat.mul_le_mul (by omega) (Nat.le_refl (a + m))
  have hcb : (a + m) * (a + m) * 11 ≤ (a + m) * (a + m) * (a + m) :=
    Nat.mul_le_mul (Nat.le_refl ((a + m) * (a + m))) (by omega)
  have h1 : n * n ≤ (a + m) * (a + m) := Nat.mul_le_mul hcap hcap
  have h2 : n * (2 * zeros + 6) ≤ (a + m) * (2 * (a + m) + 6) := Nat.mul_le_mul hcap (by omega)
  have h3 : (a + m) * (2 * (a + m) + 6) = 2 * ((a + m) * (a + m)) + 6 * (a + m) := by ring
  unfold polyClock
  omega

/-- **The payload loop, both handoffs, the decrement and the countdown as one run on the parsed
target, at the cubic budget (Part A G2y).**  Exactly G2x's **three** proposition hypotheses — the
parse, the acceptance, `3 ≤ pr.2.n` — and no others.  With `T = totalClock N zeros`,
`C = chainClock N zeros d pr.2.n` and `B = polyClock 3 (pairLength a m)`, out of the composed
`startConfig B x w`: before `T` the composed control is in neither verdict and at exactly `T` it is
G2x's landed `startConfig B x w` re-embedded (H16, at the payload loop's first arrival, at no cost);
`C = T + composedClock N zeros d pr.2.n ≤ B`, both conclusions; and at exactly `C` — and at exactly
`B`, and at every time from `C` on — the composed machine is in its accept on the separator blank
`N + 2 + zeros` with tape `loopTape B x w zeros 0 pr.2.n`, which already fixes the cleared register,
the `pr.2.n` marks and the blanks beyond.  Tag, cap, width, header and clock bound are derived and
exported as in G2x, and the exported length bound is `11 ≤ N` where G2x exported `3 ≤ N`; the room
is derived and used, not exported; persistence is not first
arrival of the composed accept; `startConfig` still embeds every earlier phase as a retag; the lane
is unfenced; reaching the composed accept is neither halting on a raw input nor language
acceptance. -/
theorem loop_decrement_countdown_drained_accepted_content_at_polyClock (k : Nat) {a m : Nat}
    (x : Bitstring a) (w : Bitstring m)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr)
    (haccept : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w) = true)
    (hn : 3 ≤ pr.2.n) :
    let B := polyClock 3 (PairEncoding.pairLength a m)
    let M := FixedGammaTargetLoopDecrementCountdown.machine
    let c := FixedGammaTargetLoopDecrementCountdown.startConfig B x w
    pr.2.n ≤ a + m ∧ 11 ≤ a + m ∧
      FixedContentTagGate.tagMatches (Fin.append x w) = true ∧
      ∃ zeros, zeros = gammaZeros pr.2.n ∧ 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
        contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
        let T := FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros
        let C := FixedGammaTargetLoopDecrementCountdown.chainClock (a + m) zeros d pr.2.n
        C = T + FixedGammaTargetDecrementCountdown.composedClock (a + m) zeros d pr.2.n ∧ C ≤ B ∧
        (∀ t, t < T → (M.run t c).state ≠ M.accept ∧ (M.run t c).state ≠ M.reject) ∧
        M.run T c =
          FixedGammaTargetPayloadRound.machine.seqEmbedRight
            FixedGammaTargetDecrementCountdown.machine
            (FixedGammaTargetDecrementCountdown.startConfig B x w) ∧
        let e := M.run C c
        e.state = M.accept ∧ e.head.val = a + m + 2 + zeros ∧
          e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros 0 pr.2.n ∧
          M.run B c = e ∧ (∀ t, C ≤ t → M.run t c = e) := by
  obtain ⟨hcap, -, htag, zeros, hzg, hz, hidx, hheader, hg, hroom, -, -, -, -, -, -, -, -⟩ :=
    countdown_drained_accepted_content_at_polyClock k x w hpr haccept hn
  obtain ⟨zeros', hg', -, -, -, -, hdec, hdechigh⟩ := decremented_register_digits x w hheader
  have hzz : zeros' = zeros := Option.some.inj (hg'.symm.trans hg)
  rw [hzz] at hdec hdechigh
  have hzN : 9 + zeros ≤ a + m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  have hroom' : zeros + 2 + (a + m) ≤ a + polyClock 3 (PairEncoding.pairLength a m) := by
    rw [hzg]
    exact hroom
  have hd := (FixedGammaTargetRegisterDecrement.borrow_pins x w zeros).1
  have hCB : FixedGammaTargetLoopDecrementCountdown.chainClock (a + m) zeros
      (FixedGammaTargetRegisterDecrement.borrow x w zeros) pr.2.n
      ≤ polyClock 3 (PairEncoding.pairLength a m) :=
    chainClock_le_polyClock hcap hd hz hzN
  obtain ⟨hfirst, -, hT, -⟩ :=
    FixedGammaTargetLoopDecrementCountdown.handoff_exact
      (B := polyClock 3 (PairEncoding.pairLength a m)) x w htag hg hz
      ((FixedGammaTargetRegisterDecrement.room_iff a m
        (polyClock 3 (PairEncoding.pairLength a m)) zeros).2
        ((FixedGammaTargetUnaryCountdownIteration.lane_room (r := 0) (k := 0) (Nat.zero_le _)
          hroom').2))
  obtain ⟨he1, he2, he3, hpers⟩ :=
    FixedGammaTargetLoopDecrementCountdown.loop_decrement_countdown_drained (F := a + m) x w htag hg
      hz hcap hroom' (fun j hj => (hdec j hj).symm) hdechigh
  exact ⟨hcap, by omega, htag, zeros, hzg, hz, hidx, hheader, hg, rfl, hCB, hfirst, hT, he1, he2,
    he3, hpers _ hCB, hpers⟩

end Pnp4.Frontier.ContractExpansion
