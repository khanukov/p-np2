import Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier
import Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownIterationBridge

/-!
# The linear lane cap, as semantics (Part A G2w-a)

G2u leaves the countdown's lane budget `F` a parameter, and G2v carries it as a hypothesis together
with the room it needs.  Neither supplies a value, and the obvious candidate — the compacted
content length `N = a + m`, the length the fixed phases lay their tape out against — is **not**
available from parser success.  A successful `contentInput?` decodes a header and runs the strict
parser on a *virtually zero-padded* word: no theorem of that chain bounds the target it returns by
the physical length of the word, and this module proves none.

Content **acceptance** does bound it, and that is the whole content of this module.  At the concrete
`treeCircuitWitnessCodec (thresholdPoly k)`:

```text
contentInput? codec z = some pr  ∧  contentSemanticAccepts codec z = true  →  pr.2.n ≤ N
```

for `z : PrefixBitVec N`.  The two cases are already available.  When the target's convention length
fits, `treeMCSPPrefixM codec pr.2.n ≤ N`, the layout fact `instanceSize_lt_treeMCSPPrefixM` gives
`pr.2.n < treeMCSPPrefixM codec pr.2.n` and the bound is immediate.  When it does not, FEAS-0's
`contentAccepts_parsed_tableLen_le_of_header_target_wide` applies: on that codec the witness window
is blank in the wide case, the decoder reads it as the input-zero projection, and acceptance forces
the last truth-table cell into the physical support, so `2 ^ pr.2.n = tableLen pr.2.n ≤ N` and
`pr.2.n < 2 ^ pr.2.n ≤ N`.  `contentInput?_target_eq_contentHeader` is what lets the wide case be
stated at the parsed target rather than at the header's, since the two are equal.  Both branches
cover `N = 0` and `N = 1` without a side condition.

Four public theorems.

* `contentSemanticAccepts_parsed_target_le_length` is the bound above.
* `contentSemanticAccepts_eq_false_of_length_lt_parsed_target` is its contrapositive in the form a
  routing phase would consume: a successful parse whose target exceeds the word's length makes the
  Boolean verifier **reject**.  It is a statement about `contentSemanticAccepts`, the frozen
  specification-side checker, and not about any machine: no `qOverflow` state, no fence cell and no
  execution is built or claimed here.
* `contentSemanticAccepts_parsed_target_le_pair_length` is the same bound at the split
  `z := Fin.append x w`, where `N` is the compacted content length `a + m` the G2v tape is laid out
  against.  This is the form that makes `F := a + m` a legitimate instantiation.
* `countdown_drained_accepted_content` takes it: on an accepted word whose parse succeeds, G2v's
  drain runs at the concrete cap `F := a + m`, so the cap is *derived* from acceptance rather than
  assumed.  The room stays a hypothesis.

## The alternative that is not implemented

If the desired contract is that **every bounded-parser success** complete the countdown rather than
every accepted word, the cap has to come from the bounded parser instead, as
`boundedContentCap k N = N ^ contentCapExponent k + contentCapExponent k`: `boundedContentInput?`
success bounds `treeMCSPPrefixM codec pr.1` by that polynomial, and `pr.2.n = pr.1 ≤
treeMCSPPrefixM codec pr.1`.  That route is sound and strictly more expensive — a polynomial lane
rather than a linear one — and **nothing here implements it**: this module defines no such cap, and
`BoundedContentSemanticVerifier` is not imported.

## What is not claimed

**No theorem here bounds the target from parser success alone**, and none is claimed: every
statement below either carries acceptance as a hypothesis or concludes a rejection.  Nothing here is a claim about
`ContentAccepts` non-vacuity — GATE-0's `contentAccepts_nonvacuous_treePoly` supplies that
separately, and the surface probe `probe_linear_cap_accepted_nonvacuous` only reads it back.

**No fence exists.**  This module builds no machine, no state, no table row and no cutoff cell; it
adds no `qOverflow` endpoint, and it does not show that any execution theorem of G2s-a, G2u or G2v
survives an installed `some false` in the lane.  The lane is still uncapped *in the machine*: a
target too large for the budget runs `qRunEnd` off the end of the tape and sticks there, which is a
timeout and therefore neither verdict, and the bound proved here does not change that — it only
identifies a cap value that is legitimate for accepted words.

The bound is one-way in the target and **not** a converse of anything: nothing here derives
acceptance, a parse, a header or a width from `pr.2.n ≤ N`, and nothing derives a parse from an
endpoint.  The capstone carries G2v's room hypothesis unchanged; it is sufficient and used, never
shown necessary.  `qDone` there remains phase-local acceptance of a machine handed a retagged actual
prior endpoint, `fullClock` counts that phase's steps alone, and the persistence conjunct is
persistence rather than first arrival.  The codec is the concrete `treeCircuitWitnessCodec
(thresholdPoly k)` throughout, because the wide case is a codec-specific fact; no codec-generic
analogue is asserted.  This module states no `accepts`, no `AcceptsAt`, no language membership, no
runtime bound, no advice-freedom claim, no `NP` membership and no `ContentVerifierBridge`.

**Progress classification (AGENTS.md): Infrastructure.**
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-- Every target is smaller than its own truth-table length, `tableLen n = 2 ^ n`.  The arithmetic
step both branches of the cap share. -/
private theorem target_lt_tableLen (n : Nat) : n < Pnp3.Models.Partial.tableLen n := by
  unfold Pnp3.Models.Partial.tableLen
  exact Nat.lt_two_pow_self

/-- **The linear cap.**  At the concrete polynomial-threshold codec, a complete word that both
parses and is *accepted* has a parsed target no larger than its own length.

Acceptance is load-bearing and is not decoration: the source is virtually zero-padded, so parser
success gives a header and a target but no support bound, and nothing here proves this conclusion
from the first hypothesis alone.  The proof splits on the parsed target's convention length.  If
`treeMCSPPrefixM codec pr.2.n ≤ N`, the layout bound `instanceSize_lt_treeMCSPPrefixM` already puts
`pr.2.n` below it.  If not, FEAS-0's wide-case theorem turns acceptance into
`tableLen pr.2.n ≤ N`, and `pr.2.n < tableLen pr.2.n` finishes; the header and the parsed target
agree there by `contentInput?_target_eq_contentHeader`.  Neither branch needs `0 < N`.

This is a bound on a *number*, not the installation of a fence: no machine, state, row or cutoff
cell occurs here, and nothing claims that an execution theorem survives one. -/
theorem contentSemanticAccepts_parsed_target_le_length (k : Nat) {N : Nat}
    (z : PrefixBitVec N)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (haccept : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    pr.2.n ≤ N := by
  have haccepts : ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z :=
    (contentSemanticAccepts_eq_true_iff _ z).1 haccept
  obtain ⟨consumed, hheader, hidx⟩ :=
    contentInput?_target_eq_contentHeader (treeCircuitWitnessCodec (thresholdPoly k)) z hpr
  rw [← hidx] at hheader
  by_cases hwide :
      N < treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n
  · obtain ⟨pr', hpr', htable⟩ :=
      contentAccepts_parsed_tableLen_le_of_header_target_wide k z pr.2.n consumed hheader
        haccepts hwide
    rw [show pr' = pr from Option.some.inj (hpr'.symm.trans hpr)] at htable
    have := target_lt_tableLen pr.2.n
    omega
  · have hnarrow := instanceSize_lt_treeMCSPPrefixM
      (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n
    omega

/-- **Overflow is a semantic rejection.**  The contrapositive, in the form a routing phase would
consume: a complete word whose parse succeeds with a target exceeding the word's own length is
rejected by the frozen Boolean content verifier.

This is a statement about `contentSemanticAccepts`, and about nothing else.  It builds no
`qOverflow` state, no fence cell and no execution, and it does not say that any machine detects the
overflow — only that, if one ever does, rejecting is the correct verdict.  The implication runs one
way: nothing here derives a target bound, a header or a parse from a `false` verdict, which can also
come from a failed parse or from a failed witness check. -/
theorem contentSemanticAccepts_eq_false_of_length_lt_parsed_target (k : Nat) {N : Nat}
    (z : PrefixBitVec N)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (hlt : N < pr.2.n) :
    contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = false := by
  by_contra hcon
  have haccept : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true := by
    simpa using hcon
  have := contentSemanticAccepts_parsed_target_le_length k z hpr haccept
  omega

/-- **The linear cap at the compacted content length.**  The same bound on the split
`z := Fin.append x w` that every fixed phase of this pipeline is laid out against: on an accepted
word, the parsed target is at most `a + m`, which is the `N` of the G2q/G2s-a/G2u tape ABI.  This is
the form that makes `F := a + m` a legitimate lane cap for accepted words; it instantiates no `F`
by itself. -/
theorem contentSemanticAccepts_parsed_target_le_pair_length (k : Nat) {a m : Nat}
    (x : Bitstring a) (w : Bitstring m)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr)
    (haccept : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w) = true) :
    pr.2.n ≤ a + m :=
  contentSemanticAccepts_parsed_target_le_length k (Fin.append x w) hpr haccept

/-- **The G2v drain at the derived cap.**  On a matching tag, a successful parse, content
acceptance, `3 ≤ pr.2.n` and the room `gammaZeros pr.2.n + 2 + (a + m) ≤ a + B`, the lane cap is no
longer a hypothesis: acceptance supplies `pr.2.n ≤ a + m`, and G2v's drain runs at `F := a + m`.
After exactly `fullClock zeros d pr.2.n` steps out of the landed `startConfig` the register is all
`some false`, the lane holds exactly `pr.2.n` marks and is blank beyond them, and that endpoint
persists.

The **room is still carried**: `B` is a free budget and no hypothesis of this theorem implies it.
The cap is derived, the room is not, and neither is shown necessary.  Nothing is fenced: `a + m`
occurs as a *number* in the room premise and in G2v's statement, not as a `some false` cell laid on
the tape, and no `qOverflow` route exists to take when the bound fails — a word whose parse succeeds
and whose target exceeds `a + m` is semantically rejected by
`contentSemanticAccepts_eq_false_of_length_lt_parsed_target`, but no machine here detects that.  The
persistence conjunct is persistence, not first arrival; `qDone` is phase-local, not halting or
language acceptance; and `fullClock` counts this phase's steps alone. -/
theorem countdown_drained_accepted_content (k : Nat) {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr)
    (haccept : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w) = true)
    (hn : 3 ≤ pr.2.n) (hroom : gammaZeros pr.2.n + 2 + (a + m) ≤ a + B) :
    pr.2.n ≤ a + m ∧
      ∃ zeros, zeros = gammaZeros pr.2.n ∧ 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
        contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
        let e := FixedGammaTargetUnaryCountdown.machine.run
          (FixedGammaTargetUnaryCountdownIteration.fullClock zeros d pr.2.n)
          (FixedGammaTargetUnaryCountdown.startConfig B x w)
        e.state = FixedGammaTargetUnaryCountdown.qDone ∧
          e.head.val = a + m + 2 + zeros ∧
          e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros 0 pr.2.n ∧
          (∀ t, FixedGammaTargetUnaryCountdownIteration.fullClock zeros d pr.2.n ≤ t →
            FixedGammaTargetUnaryCountdown.machine.run t
              (FixedGammaTargetUnaryCountdown.startConfig B x w) = e) ∧
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some false) ∧
          (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 3 + zeros ≤ i.val →
            i.val < a + m + 3 + zeros + pr.2.n → e.tape i = some true) ∧
          (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            a + m + 3 + zeros + pr.2.n ≤ i.val → e.tape i = none) := by
  have hcap : pr.2.n ≤ a + m :=
    contentSemanticAccepts_parsed_target_le_pair_length k x w hpr haccept
  obtain ⟨zeros, hzg, hz, hidx, hheader, hg, -, -, -, -, -, -, -, -, -, he1, he2, he3, hpers,
    hreg, hmark, hlane⟩ :=
    countdown_drained_parsed_target (B := B) (F := a + m) (treeCircuitWitnessCodec
      (thresholdPoly k)) x w htag hpr hn hcap hroom
  exact ⟨hcap, zeros, hzg, hz, hidx, hheader, hg, he1, he2, he3, hpers, hreg, hmark, hlane⟩

end Pnp4.Frontier.ContractExpansion
