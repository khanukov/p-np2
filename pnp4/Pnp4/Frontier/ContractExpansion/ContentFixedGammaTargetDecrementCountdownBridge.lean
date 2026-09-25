import Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown
import Pnp4.Frontier.ContractExpansion.ContentCountdownLinearCap

/-!
# The executed decrement-to-countdown handoff on the parsed target (Part A G2x)

G2w-b ran G2s-a's countdown alone, out of the countdown's own `startConfig` — a proof-level retag of
G2q's run at G2q's length-only deadline — for exactly `B := polyClock 3 (pairLength a m)` steps,
under three hypotheses.  This module runs **one machine** for the decrement *and* the countdown
under the **same three hypotheses** at the **same budget**: the pnp3 G2x composed
`FixedGammaTargetDecrementCountdown.machine`, G2q's table followed by G2s-a's as one closed 18-state
table.  The routed row `qBorrow`-on-`some true` → countdown `qStart` is the *successful* cross-block
edge, the one the runs characterised here take, and not the table's only one: `seq` also routes every
G2q row targeting `qReject` into the composed reject, and the dead left `qDone` rows into `qStart`.
Write `N = a + m`, `zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`.

`decrement_countdown_drained_accepted_content_at_polyClock` has exactly G2w-b's hypotheses — the
parse, the acceptance, `3 ≤ pr.2.n`, at the concrete `treeCircuitWitnessCodec (thresholdPoly k)` —
and no tag, cap, room, budget, clock, width, digit, initial-state, correctness or runtime premise.
Out of the composed `startConfig` — G2q's own, the retagged *actual* G2p-f endpoint, routed — it
concludes the cap `pr.2.n ≤ N`, the tag, `pr.2.n = pr.1`, the header and the width; the composed
clock `C = decClock N zeros d + fullClock zeros d pr.2.n ≤ B`; **the executed handoff** — before
`T = decClock N zeros d` the composed control is in neither verdict, and at exactly `T` the composed
configuration *is* the countdown's landed `startConfig B x w` re-embedded, the switch happening at
G2q's first arrival (`decrement_strict`), not at G2q's deadline; and at exactly `C`, at exactly `B`
and at every later time, the composed accept on the separator blank `N + 2 + zeros` with tape
`loopTape B x w zeros 0 pr.2.n` — the register cleared, exactly `pr.2.n` marks, blanks beyond.  The
target is tracked as `pr.2.n`, the field `ContentAccepts` reads; the register value is the G2r digit
fact on the decoded header, as in G2v; nothing here executes a parser.

The arithmetic.  G2w-b's private domination lemma bounds `fullClock` alone; with
`decClock N zeros d = N + zeros + d - 3` added, `C ≤ 3N² + 12N + 4 ≤ (N+1)³ + 3 ≤ B` from
`3 ≤ pr.2.n ≤ N`, `d ≤ zeros` and `zeros ≤ pr.2.n`, the last read off the decoded header's
`2 ^ zeros ≤ pr.2.n + 1`.  The exponent `3` is sufficient and not shown least; `B` is both tape
budget and step count, an instantiation choice.

Not claimed.  **One handoff of seventeen**: `startConfig` still embeds every earlier phase, the
sixteen earlier handoffs stay proof-level, no `initialConfig` on a raw pair input is executed, and
no clock here counts a step of any earlier phase.  **Composed first arrival**: nothing says `C` is
the first time the composed accept is entered.  **The fence**: both tables are unfenced; accepted
words never overflow the lane, since `pr.2.n ≤ N` is derived, but an overshooting word still runs
off the tape and sticks, a timeout and neither verdict, and no rejected or malformed input is
characterised.  **Small targets** `0`, `1`, `2` are excluded by `3 ≤ pr.2.n`, as in G2w-b.  **Every
converse**, every witness-check phase, and the **model connection**: this is a V1 `UniformTM` on
`Option Bool` cells laid out against `pairLength a m`, while `ContentVerifierBridge` asks for the
legacy `TM` with a `runTime` field on `concatBitstring x w`; the legacy `runTime` advice channel of
`VERIFIER_RETARGET_PLAN.md` caveat 6 is untouched.  Reaching the composed accept out of a retagged
actual prior endpoint is neither halting on a raw input nor language acceptance.  No `accepts`,
`AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation`, `NP` membership, advice-freedom claim
or `ContentVerifierBridge` is stated, and neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced.

**Progress classification (AGENTS.md): Infrastructure.**
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-- **The cubic budget dominates the composed clock.**  Pure arithmetic: under `3 ≤ n ≤ a + m`,
`zeros ≤ n` and `d ≤ zeros`, `composedClock (a + m) zeros d n ≤ 3 (a+m)² + 12 (a+m) + 4`, and
`(a + m + 1) ^ 3 + 3 ≤ polyClock 3 (pairLength a m)` exceeds that once `3 ≤ a + m`.  Sufficient;
the exponent `3` is not shown least. -/
private theorem composedClock_le_polyClock {a m zeros d n : Nat}
    (hn : 3 ≤ n) (hcap : n ≤ a + m) (hzn : zeros ≤ n) (hd : d ≤ zeros) :
    FixedGammaTargetDecrementCountdown.composedClock (a + m) zeros d n
      ≤ polyClock 3 (PairEncoding.pairLength a m) := by
  rw [(FixedGammaTargetDecrementCountdown.clock_pins (a + m) zeros d n).2.1]
  have hP : a + m + 1 ≤ PairEncoding.pairLength a m := by
    unfold PairEncoding.pairLength
    omega
  have hcube : (a + m + 1) ^ 3 ≤ PairEncoding.pairLength a m ^ 3 := Nat.pow_le_pow_left hP 3
  have hexp : (a + m + 1) ^ 3
      = (a + m) * (a + m) * (a + m) + 3 * ((a + m) * (a + m)) + 3 * (a + m) + 1 := by ring
  have hsq : 3 * 3 ≤ (a + m) * (a + m) := Nat.mul_le_mul (by omega) (by omega)
  have hcb : 3 * 3 * (a + m) ≤ (a + m) * (a + m) * (a + m) :=
    Nat.mul_le_mul hsq (Nat.le_refl (a + m))
  have h1 : n * n ≤ (a + m) * (a + m) := Nat.mul_le_mul hcap hcap
  have h2 : n * (2 * zeros + 6) ≤ (a + m) * (2 * (a + m) + 6) := Nat.mul_le_mul hcap (by omega)
  have h3 : (a + m) * (2 * (a + m) + 6) = 2 * ((a + m) * (a + m)) + 6 * (a + m) := by ring
  unfold polyClock
  omega

/-- **The decrement, the handoff and the countdown as one run on the parsed target, at the cubic
budget (Part A G2x).**  Exactly G2w-b's **three** proposition hypotheses — the parse, the
acceptance, `3 ≤ pr.2.n` — and no others.  With `T = decClock N zeros d`,
`C = composedClock N zeros d pr.2.n` and `B = polyClock 3 (pairLength a m)`, out of the composed
`startConfig B x w`: before `T` the composed control is in neither verdict and at exactly `T` it is
the countdown's landed `startConfig B x w` re-embedded (the handoff, at G2q's first arrival, at no
cost); `C = T + fullClock zeros d pr.2.n ≤ B`, both conclusions; and at exactly `C` — and at
exactly `B`, and at every time from `C` on — the composed machine is in its accept on the separator
blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 pr.2.n`, the register cleared and exactly
`pr.2.n` marks laid.  Tag, cap, width, header and clock bound are derived and exported as in G2w-b;
G2w-b's room is derived and used, not exported; persistence is not first arrival of the composed
accept; `startConfig` still embeds every earlier phase as a retag; the lane is unfenced; reaching
the composed accept is neither halting on a raw input nor language acceptance. -/
theorem decrement_countdown_drained_accepted_content_at_polyClock (k : Nat) {a m : Nat}
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
    let M := FixedGammaTargetDecrementCountdown.machine
    let c := FixedGammaTargetDecrementCountdown.startConfig B x w
    pr.2.n ≤ a + m ∧ 3 ≤ a + m ∧
      FixedContentTagGate.tagMatches (Fin.append x w) = true ∧
      ∃ zeros, zeros = gammaZeros pr.2.n ∧ 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
        contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
        let T := FixedGammaTargetRegisterDecrement.decClock (a + m) zeros d
        let C := FixedGammaTargetDecrementCountdown.composedClock (a + m) zeros d pr.2.n
        C = T + FixedGammaTargetUnaryCountdownIteration.fullClock zeros d pr.2.n ∧ C ≤ B ∧
        (∀ t, t < T → (M.run t c).state ≠ M.accept ∧ (M.run t c).state ≠ M.reject) ∧
        M.run T c =
          FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
            FixedGammaTargetUnaryCountdown.machine
            (FixedGammaTargetUnaryCountdown.startConfig B x w) ∧
        let e := M.run C c
        e.state = M.accept ∧ e.head.val = a + m + 2 + zeros ∧
          e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros 0 pr.2.n ∧
          M.run B c = e ∧ (∀ t, C ≤ t → M.run t c = e) ∧
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some false) ∧
          (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 3 + zeros ≤ i.val →
            i.val < a + m + 3 + zeros + pr.2.n → e.tape i = some true) ∧
          (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            a + m + 3 + zeros + pr.2.n ≤ i.val → e.tape i = none) := by
  obtain ⟨hcap, h3N, htag, zeros, hzg, hz, hidx, hheader, hg, hroom, -, -, -, -, -, -, -, -⟩ :=
    countdown_drained_accepted_content_at_polyClock k x w hpr haccept hn
  obtain ⟨zeros', hg', -, hlo, -, -, hdec, hdechigh⟩ := decremented_register_digits x w hheader
  have hzz : zeros' = zeros := Option.some.inj (hg'.symm.trans hg)
  rw [hzz] at hlo hdec hdechigh
  have hroom' : zeros + 2 + (a + m) ≤ a + polyClock 3 (PairEncoding.pairLength a m) := by
    rw [hzg]
    exact hroom
  -- The load-bearing hypothesis is `hlo : 2 ^ zeros ≤ pr.2.n + 1`, the decoded-header width bound
  -- from `decremented_register_digits`; `Nat.lt_two_pow_self` alone gives only `zeros < 2 ^ zeros`.
  have hzn : zeros ≤ pr.2.n := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le Nat.lt_two_pow_self hlo)
  have hd := (FixedGammaTargetRegisterDecrement.borrow_pins x w zeros).1
  have hCB : FixedGammaTargetDecrementCountdown.composedClock (a + m) zeros
      (FixedGammaTargetRegisterDecrement.borrow x w zeros) pr.2.n
      ≤ polyClock 3 (PairEncoding.pairLength a m) :=
    composedClock_le_polyClock hn hcap hzn hd
  obtain ⟨hfirst, -, hT, -⟩ :=
    FixedGammaTargetDecrementCountdown.handoff_exact
      (B := polyClock 3 (PairEncoding.pairLength a m)) x w htag hg hz
      ((FixedGammaTargetUnaryCountdownIteration.lane_room (r := 0) (k := 0) (Nat.zero_le _)
        hroom').2)
  obtain ⟨he1, he2, he3, hpers, hreg, hmark, hlane⟩ :=
    FixedGammaTargetDecrementCountdown.decrement_countdown_drained (F := a + m) x w htag hg hz
      hcap hroom' (fun j hj => (hdec j hj).symm) hdechigh
  exact ⟨hcap, h3N, htag, zeros, hzg, hz, hidx, hheader, hg, rfl, hCB, hfirst, hT, he1, he2, he3,
    hpers _ hCB, hpers, hreg, hmark, hlane⟩

end Pnp4.Frontier.ContractExpansion
