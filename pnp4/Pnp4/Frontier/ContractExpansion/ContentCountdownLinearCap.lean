import Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier
import Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownIterationBridge

/-!
# The linear lane cap, as semantics (Part A G2w-a), closed at a fixed cubic budget (Part A G2w-b)

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

Six public theorems.

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
* `concatBitstring_eq_append` is a word-shape bridge and nothing else: the verifier interface's
  `concatBitstring x w` and the fixed-phase split `Fin.append x w` are the same function of the two
  blocks.  No parse, no acceptance, no header and no machine occurs in it.  It exists because
  GATE-0's accepted words are built with `concatBitstring` while every fixed-phase statement of this
  pipeline is laid out against `Fin.append`, and something has to say they agree.
* `countdown_drained_accepted_content_at_polyClock` is G2w-b, described next.

## Closing the budget (Part A G2w-b)

`countdown_drained_accepted_content` still carries a free budget `B` and the room premise that `B`
has to satisfy.  G2w-b removes both by *choosing* `B`:

```text
B := polyClock 3 (PairEncoding.pairLength a m) = (2 * a + 1 + m) ^ 3 + 3
```

a fixed cubic function of the split's own two lengths.  With `N = a + m` and
`d = FixedGammaTargetRegisterDecrement.borrow x w zeros`, acceptance caps the target at `N`,
`gammaZeros n ≤ n` caps the width at `N`, `borrow_pins` caps `d` by the width, and G2u's clock
expands to `fullClock zeros d n = d + n * n + n * (2 * zeros + 6) + 2 * zeros + 7`, every summand of
which is then below a fixed quadratic in `N`.  The cube dominates it because `3 ≤ pr.2.n ≤ N` is in
force, so both the room `gammaZeros pr.2.n + 2 + N ≤ a + B` and the clock bound
`fullClock zeros d pr.2.n ≤ B` are *derived*, not assumed; each is exported as a conjunct of the
conclusion, alongside `3 ≤ N` and the derived tag, so the reader can see they are results rather
than premises.  G2v's endpoint is then transported from `fullClock` to exactly `B` steps by the
persistence conjunct G2v already proves, and persistence at `B` is re-exported the same way.

So `countdown_drained_accepted_content_at_polyClock` has exactly **three** proposition hypotheses —
the successful parse, the Boolean acceptance, and `3 ≤ pr.2.n` — and no others: no tag premise (the
factorization `fixedTag_semantic_factorization` derives it from acceptance), no cap, no room, no
free `B`, no free `F`, no runtime premise and no correctness premise.  The exponent `3` is chosen to
dominate the quadratic clock; nothing here shows it is least, and no smaller exponent is ruled out.
The derived room is still **sufficient only**: instantiating `B` is not a proof that this budget is
necessary, and no footprint or budget theorem exists on the pnp3 side to make one.

The same number `B` plays two roles in that statement — the tape budget `startConfig` and
`tapeLength` are laid out against, and the number of steps the machine is run for.  That is an
instantiation choice, not a theorem: nothing below says the two must agree, only that this one value
is large enough for both.

## The alternative that is not implemented

If the desired contract is that **every bounded-parser success** complete the countdown rather than
every accepted word, the cap has to come from the bounded parser instead, as
`boundedContentCap k N = N ^ contentCapExponent k + contentCapExponent k`: `boundedContentInput?`
success bounds `treeMCSPPrefixM codec pr.1` by that polynomial, and `pr.2.n = pr.1 ≤
treeMCSPPrefixM codec pr.1`.  That route is sound and strictly more expensive — a polynomial lane
rather than a linear one — and **nothing here implements it**: this module defines no such cap and
adds **no new direct import** for one.  `BoundedContentSemanticVerifier` is nonetheless already in
this module's transitive import closure — `FixedContentTagGateCorrect` imports it, and the G2v
bridge reaches that module through the G2o header-value bridge — so the accurate statement is that
no declaration of it is *used* here, not that it is absent.

## What is not claimed

**No theorem here bounds the target from parser success alone**, and none is claimed: every
statement below that mentions a target either carries acceptance as a hypothesis or concludes a
rejection, and the one statement that mentions no target, `concatBitstring_eq_append`, mentions no
parser either.  Nothing here is a claim about `ContentAccepts` non-vacuity — GATE-0's
`contentAccepts_nonvacuous_treePoly` and `contentAccepts_zeroPrefixQuery_of_predicate` supply that
separately, and the surface probes only read it back.  `probe_linear_cap_accepted_nonvacuous`
inhabits the parse-and-acceptance premise pair of
`contentSemanticAccepts_parsed_target_le_length`, on one word, and nothing more: it pins no target
value, and it inhabits neither the overflow theorem's premises nor the free-budget capstone's five
jointly.  `probe_countdown_polyClock_accepted_target_three` does inhabit the three premises of the
G2w-b endpoint jointly — one accepted word per exponent, GATE-0's zero-prefix query for the
all-false table on three variables followed by its certificate — at the pinned target `pr.2.n = 3`
and hence the pinned width `gammaZeros 3 = 2`, and reads the `qDone` endpoint state back after
exactly `B` steps.  So G2w-b is not a statement about an empty premise set.  That probe exhibits one
word per exponent and claims nothing about any other: it pins no tape cell, and in particular
exhibits no *rejected* and no *overshooting* word.

**No fence exists.**  This module builds no machine, no state, no table row and no cutoff cell; it
adds no `qOverflow` endpoint, and it does not show that any execution theorem of G2s-a, G2u or G2v
survives an installed `some false` in the lane.  The lane is still uncapped *in the machine*: a
target too large for the budget runs `qRunEnd` off the end of the tape and sticks there, which is a
timeout and therefore neither verdict, and nothing proved here changes that — G2w-a identifies a cap
value that is legitimate for accepted words, G2w-b identifies a budget value that is large enough
for them, and neither installs a mechanism that enforces either.

The bound is one-way in the target and **not** a converse of anything: nothing here derives
acceptance, a parse, a header or a width from `pr.2.n ≤ N`, and nothing derives a parse from an
endpoint.  `countdown_drained_accepted_content` carries G2v's room hypothesis unchanged and
`countdown_drained_accepted_content_at_polyClock` derives it from a chosen `B`; in both cases the
room is sufficient and used, never shown necessary.  `qDone` in both remains phase-local acceptance
of a machine handed a retagged actual prior endpoint, `fullClock` counts that phase's steps alone —
no pipeline clock is composed and no raw-input deadline is stated — and the persistence conjunct is
persistence rather than first arrival.  Every statement that mentions a codec mentions the concrete
`treeCircuitWitnessCodec (thresholdPoly k)`, because the wide case is a codec-specific fact and no
codec-generic analogue is asserted; `concatBitstring_eq_append` mentions none.  `polyClock` occurs
here as an ordinary arithmetic function of two lengths: this module states no `accepts`, no
`AcceptsAt`, no `DecidesWithin`, no `UniformP`, no language membership, no runtime bound, no
advice-freedom claim, no `NP` membership and no `ContentVerifierBridge`.

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

Acceptance is **used** by the proof below, and no theorem here proves this conclusion from the first
hypothesis alone: the source is virtually zero-padded, so parser success gives a header and a target
but no support bound.  That acceptance is *necessary* — that some parse-successful word really does
overshoot its own length — is **not claimed and not exhibited here**; no probe inhabits that
situation.  The proof splits on the parsed target's convention length.  If
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
come from a failed parse or from a failed witness check.  No word is exhibited that satisfies both
hypotheses, so this statement is not shown to be non-vacuous. -/
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
The cap is derived, the room is not, and neither is shown necessary.  The five hypotheses are not
independent — acceptance already implies the tag premise, by
`fixedTag_semantic_factorization`, which is carried here only to match G2v's shape — and **no probe
inhabits them jointly**, so the capstone is not shown to be non-vacuous.  Nothing is fenced: `a + m`
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

/-! ### The two spellings of a split word -/

/-- **`concatBitstring` and `Fin.append` are the same function.**  The verifier interface builds its
words with the `Classical.choose`-based `Pnp3.ComplexityInterfaces.concatBitstring`; every fixed
phase of this pipeline lays its tape out against `Fin.append`.  On the same two blocks they agree.

This is a statement about two functions on `Fin (n + m)` and nothing else: no parse, no header, no
acceptance, no codec, no machine and no constraint on either block occurs in it.  It is one way only
in a trivial sense — it is an equation — and it says nothing about *which* splits of a given word
exist.  The proof is the existing bit-level projections `concatBitstring_left` /
`concatBitstring_right` read against `Fin.append_left` / `Fin.append_right`. -/
theorem concatBitstring_eq_append {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    Pnp3.ComplexityInterfaces.concatBitstring x w = Fin.append x w := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · rw [Fin.append_left, concatBitstring_left x w _ (by simp)]
    exact congrArg x (Fin.ext (by simp))
  · rw [Fin.append_right, concatBitstring_right x w _ (by simp)]
    exact congrArg w (Fin.ext (by simp))

/-! ### Closing the budget at a fixed cubic clock -/

/-- The canonical gamma width never exceeds its own target:
`gammaZeros n < 2 ^ gammaZeros n ≤ n + 1` by the defining `bitLength` bound.  This is all the budget
derivation below needs to know about `gammaZeros`. -/
private theorem gammaZeros_le (n : Nat) : gammaZeros n ≤ n := by
  have hlo : 2 ^ gammaZeros n ≤ n + 1 := by
    unfold gammaZeros
    exact two_pow_bitLength_pred_le (a := n + 1) (Nat.succ_pos n)
  have hlt : gammaZeros n < 2 ^ gammaZeros n := Nat.lt_two_pow_self
  omega

/-- **The cubic budget dominates.**  Pure arithmetic, with `zeros` and `d` abstract: under
`3 ≤ n ≤ a + m`, `zeros ≤ n` and `d ≤ zeros`, the fixed value
`polyClock 3 (pairLength a m) = (2 * a + 1 + m) ^ 3 + 3` satisfies both of G2v's numeric premises —
the room, and the expanded exact clock `fullClock zeros d n`.  Only `(a + m + 1) ^ 3 ≤
pairLength a m ^ 3` and `3 ≤ a + m` are used.  The exponent `3` is sufficient here; nothing shows it
is least, and no smaller exponent is ruled out. -/
private theorem polyClock_room_and_clock {a m zeros d n : Nat}
    (hn : 3 ≤ n) (hcap : n ≤ a + m) (hzn : zeros ≤ n) (hd : d ≤ zeros) :
    zeros + 2 + (a + m) ≤ a + polyClock 3 (PairEncoding.pairLength a m) ∧
      d + n * n + n * (2 * zeros + 6) + 2 * zeros + 7
        ≤ polyClock 3 (PairEncoding.pairLength a m) := by
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

/-- **The G2v drain at a closed budget (Part A G2w-b).**  Instantiating
`countdown_drained_accepted_content` at the fixed cubic budget
`B := polyClock 3 (pairLength a m) = (2 * a + 1 + m) ^ 3 + 3`
and running to exactly `B` steps.  Exactly **three** proposition hypotheses — the successful parse,
the Boolean acceptance, `3 ≤ pr.2.n` — and no others: no tag premise, no cap, no room, no free `B`,
no free `F`, no runtime premise and no correctness premise.

Everything else is *derived*.  Acceptance caps the target at `a + m` and, through
`fixedTag_semantic_factorization`, supplies the tag; `gammaZeros pr.2.n ≤ pr.2.n` caps the width;
`borrow_pins` caps the borrow by the width; and `polyClock_room_and_clock` then puts both the room
`gammaZeros pr.2.n + 2 + (a + m) ≤ a + B` and the exact clock
`fullClock zeros (borrow x w zeros) pr.2.n ≤ B` below the cube.  Both are exported as conjuncts, so
the reader can see they are conclusions rather than premises.  The endpoint is transported from
`fullClock` to exactly `B` steps by the persistence conjunct G2v already proves, and persistence at
`B` is re-exported in the same way.

The same number `B` is used twice — as the tape budget `startConfig`/`tapeLength` are laid out
against, and as the number of steps run.  That is an instantiation choice, not a theorem: nothing
here says the two must agree, only that this one value is large enough for both.  The exponent `3`
is sufficient and is not shown least.  Everything `countdown_drained_accepted_content` disclaims
still holds: the persistence conjunct is persistence and **not** first arrival, `qDone` is
phase-local acceptance of a machine handed a retagged actual prior endpoint rather than halting or
language acceptance, `fullClock` counts this phase's steps alone, the lane is still unfenced in the
machine, and no converse — no parse, header, width or acceptance from an endpoint — is stated. -/
theorem countdown_drained_accepted_content_at_polyClock (k : Nat) {a m : Nat}
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
    pr.2.n ≤ a + m ∧ 3 ≤ a + m ∧
      FixedContentTagGate.tagMatches (Fin.append x w) = true ∧
      ∃ zeros, zeros = gammaZeros pr.2.n ∧ 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
        contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        gammaZeros pr.2.n + 2 + (a + m) ≤ a + B ∧
        FixedGammaTargetUnaryCountdownIteration.fullClock zeros
            (FixedGammaTargetRegisterDecrement.borrow x w zeros) pr.2.n ≤ B ∧
        let e := FixedGammaTargetUnaryCountdown.machine.run B
          (FixedGammaTargetUnaryCountdown.startConfig B x w)
        e.state = FixedGammaTargetUnaryCountdown.qDone ∧
          e.head.val = a + m + 2 + zeros ∧
          e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros 0 pr.2.n ∧
          (∀ t, B ≤ t → FixedGammaTargetUnaryCountdown.machine.run t
            (FixedGammaTargetUnaryCountdown.startConfig B x w) = e) ∧
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some false) ∧
          (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 3 + zeros ≤ i.val →
            i.val < a + m + 3 + zeros + pr.2.n → e.tape i = some true) ∧
          (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            a + m + 3 + zeros + pr.2.n ≤ i.val → e.tape i = none) := by
  intro B
  have hcap : pr.2.n ≤ a + m :=
    contentSemanticAccepts_parsed_target_le_pair_length k x w hpr haccept
  have htag : FixedContentTagGate.tagMatches (Fin.append x w) = true := by
    have h := fixedTag_semantic_factorization.1 (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w)
    rw [haccept] at h
    simpa using h.symm
  have hroom : gammaZeros pr.2.n + 2 + (a + m) ≤ a + B :=
    (polyClock_room_and_clock (d := 0) hn hcap (gammaZeros_le pr.2.n) (Nat.zero_le _)).1
  obtain ⟨-, zeros, hzg, hz, hidx, hheader, hg, he1, he2, he3, hpers, hreg, hmark, hlane⟩ :=
    countdown_drained_accepted_content (B := B) k x w htag hpr haccept hn hroom
  subst hzg
  have hclock : FixedGammaTargetUnaryCountdownIteration.fullClock (gammaZeros pr.2.n)
      (FixedGammaTargetRegisterDecrement.borrow x w (gammaZeros pr.2.n)) pr.2.n ≤ B := by
    have hfull : FixedGammaTargetUnaryCountdownIteration.fullClock (gammaZeros pr.2.n)
        (FixedGammaTargetRegisterDecrement.borrow x w (gammaZeros pr.2.n)) pr.2.n
        = FixedGammaTargetRegisterDecrement.borrow x w (gammaZeros pr.2.n)
          + pr.2.n * pr.2.n + pr.2.n * (2 * gammaZeros pr.2.n + 6)
          + 2 * gammaZeros pr.2.n + 7 := by
      unfold FixedGammaTargetUnaryCountdownIteration.fullClock
        FixedGammaTargetUnaryCountdownIteration.drainClock
        FixedGammaTargetUnaryCountdownIteration.roundsClock
        FixedGammaTargetUnaryCountdown.zeroClock
      ring
    rw [hfull]
    exact (polyClock_room_and_clock hn hcap (gammaZeros_le pr.2.n)
      (FixedGammaTargetRegisterDecrement.borrow_pins x w (gammaZeros pr.2.n)).1).2
  have hBe := hpers B hclock
  refine ⟨hcap, le_trans hn hcap, htag, gammaZeros pr.2.n, rfl, hz, hidx, hheader, hg, hroom,
    hclock, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBe]; exact he1
  · rw [hBe]; exact he2
  · rw [hBe]; exact he3
  · intro t ht
    rw [hBe]
    exact hpers t (le_trans hclock ht)
  · rw [hBe]; exact hreg
  · rw [hBe]; exact hmark
  · rw [hBe]; exact hlane

end Pnp4.Frontier.ContractExpansion
