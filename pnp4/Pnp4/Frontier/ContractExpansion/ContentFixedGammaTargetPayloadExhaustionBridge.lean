import Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetSecondPayloadBridge

/-!
# The complete target register is the parsed target's digits (Part A G2p-g)

The landed pnp3 slice `FixedGammaTargetPayloadExhaustion.payload_exhausted` runs the fixed
22-state G2p-d table out of its `startConfig` for exactly
`totalClock (a + m) zeros = loopClock (a + m) zeros + exhaustClock (a + m) zeros` steps and
leaves the target register `[a+m+1, a+m+1+zeros]` holding the `zeros + 1` *tape symbols*
`registerBit x w zeros j`.  It deliberately stops there: `registerBit` is content, and on a
truncated payload its digits past the physical word are a virtual `false` that no theorem
there ties to any parsed value.  This bridge supplies exactly that tie, and nothing else.

Write `N = a + m`.  On a decoded content header `contentHeader? (Fin.append x w) =
some (n, consumed)` the whole register is the binary expansion of `n + 1`, most significant
digit first:

```text
register cell  a+m+1+j   holds   (n + 1).testBit (zeros - j)      for every  j ≤ zeros
```

* `exhaustion_register_digits` is the parser-side half, with **no machine run in its
  statement** — `registerBit` is the loop foundation's register-*content* function, a pure
  function of the input word and the width, and no `Config`, clock, tag or budget occurs:
  a decoded header fixes the physical gamma width `zeros`, `consumed = 2 * zeros + 1`, the bit
  length `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the register equation above at every
  `j ≤ zeros`, the completeness fact that `n + 1` has *no* bit above `zeros`, and the
  **virtual-tail** conjunct: for `1 ≤ j ≤ zeros`, wherever the payload cell `8 + zeros + j`
  has left the physical word (`a + m ≤ 8 + zeros + j`), the register digit is `false` *and*
  so is the parsed `(n + 1).testBit (zeros - j)`.  That last conjunct is the whole point of
  the slice.  `registerBit` pads with `false` there because the payload cell is not in the
  word — on `contentTape` that cell is blank — while the decoder pads with a virtual zero
  because `contentHeader?` reads through `VirtualZeroTailReader`.  Those are two different
  paddings, and this theorem is where they are proved to agree — so a virtual `false` in the
  register is *the parsed target's digit*, not a fiction that happens to sit in a cell.
* `register_determines_target`: the register does not merely contain digits of `n + 1`, it
  pins `n + 1` uniquely.  Any `v` whose bits match the register cells and which has no bit
  above `zeros` *is* `n + 1`.  Together with the previous theorem this is the precise sense
  in which the completed register "encodes the parsed target".
* `room_iff_target_bound` makes the room premise of the two machine theorems legible: on a
  decoded header, `n + 1 < 2 ^ (a + B + 1)`, `zeros ≤ a + B`, and the room premise the pnp3
  iteration hands to `payload_exhausted`,
  `a + m + 1 + zeros < tapeLength (pairLength a m) B`, are the same condition.  It is a joint
  condition on the parsed target and the budget, and a header alone does **not** imply it:
  `B` is free, and at `a = B = 0` only the degenerate width `zeros = 0` is affordable.  The
  surface test's `probe_exhausted_room_not_implied` makes that sharper.  One twelve-cell word
  with a matching tag and the decoded header `(5, 5)`, hence `3 ≤ n`, is split once as
  `a = 8`, `m = 4` and once as `a = 1`, `m = 11`, and the probe pins that the two splits are
  literally the same word.  Every reader here sees `Fin.append x w`, so both splits decode to
  the same header; but room depends on `a` and `B`, not on `a + m`, and at `B = 0` it holds on
  the first split and fails on the second.  Room is therefore not a function of the decoded
  header at all.
* `exhausted_register_header_value` carries the header through to the actual G2p-f endpoint:
  matching tag, decoded header, `3 ≤ n`, and that room.  The exhausted machine is in `qDone`
  on the tag cell `7` with tape `finishTape B x w zeros`, every register cell holds the
  matching digit of `n + 1`, every virtual-tail cell holds `some false` together with the
  matching parsed `false`, those endpoint cells *pin* `n + 1` among all values with no bit
  above `zeros`, the tag cell `7` together with the gamma zero field `[8, 7 + zeros]` is back
  to the incoming content tape, and the endpoint persists at every later time.
* `exhausted_register_parsed_target` replaces the header by a successful **dependent parse**
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec.  It exports
  `pr.2.n = pr.1` — the target the parsed `PrefixInput` carries, which is what
  `ContentAccepts` reads, is the outer Sigma index and the header's first component — and
  then states the register, pinning conjunct included, in terms of `pr.2.n`.  This is the
  "actual parsed target".  It re-exports every conjunct of the header form except the gamma
  zero field restoration, which is about the tape and not about the target.

## The parsed target versus the header's conventions

Three different numbers are in play and this module keeps them apart.

* `pr.2.n`, the **actual parsed target**: the field of the parsed `PrefixInput` that
  `ContentAccepts` feeds to the search relation.  `contentInput?_target_eq_contentHeader`
  makes it the header's `n`, for every codec and with no monotonicity premise.
* `n + 1`, the gamma **convention value**: what an Elias-gamma header physically stores, so
  that the leading digit is a `true` the decoder can find.  The register holds the digits of
  `n + 1`, **not** of `n`.  The decrement is not performed by any machine here and is not
  claimed; `payload_exhausted` records it as deferred and this bridge does not close it.
* `consumed = 2 * zeros + 1`, the header's **cell count**: a length convention describing how
  much of the tape the header occupies.  It is not the target, and the register never holds
  it.  The parser's other length convention, `treeMCSPPrefixM codec pr.1`, is the width of
  the window the strict parser re-reads; it appears in the type of `pr` and in no conclusion
  about a register cell.

## What is not claimed

No machine here executes `contentHeader?`, `contentInput?`, or any parser: `n` occurs only in
the *statements*, and the control of the fixed table reads a tape symbol and nothing else —
no width, digit index, address, advice, producer mark, or proof term.  Nothing is computed
from a proof; no `Nat.find`, choice, or decidability instance supplies a runtime value.  In
particular the machine is never shown to *recover* `n`: the register is a tape object whose
cells this bridge identifies with digits, and `register_determines_target` is an arithmetic
uniqueness statement about those digits, not a decoding step the machine performs.

There is deliberately no converse: nothing derives a valid header, a width, `2 ≤ zeros`, or
room from `qDone`, from the endpoint tape, or from a digit found at a register cell.  Nothing
here decrements `n + 1` to `n`, reads the register as a number *on the tape* — the uniqueness
conjunct is arithmetic about the digits found there, not a decoding step the control
performs — states a footprint or budget theorem (so no room premise is shown necessary),
covers a malformed gamma, or measures first arrival from `startConfig`.  The two machine
theorems do not cover the degenerate widths `zeros ≤ 1`, which `payload_exhausted` excludes;
the three parser-side theorems carry no width premise and do cover them.  Given a decoded
header `3 ≤ n` is exactly `2 ≤ zeros`, in the same sense as in the G2p-c bridge: the exported
bounds `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)` make `zeros` the index of the leading digit of
`n + 1`, so both directions are derivable from the exported conjuncts, and neither is stated
as an equivalence theorem — only the direction used here, `3 ≤ n → 2 ≤ zeros`, is proved.
The premise admits `zeros = 2`, where the G2p-e round count `zeros - 2` is zero and the
endpoint is the finish alone; by the same arithmetic `7 ≤ n` is what forces at least one
round.  `qDone` is an internal control tag of a phase whose `startConfig` retags an
*actual* prior run: reaching it is neither halting of a composed machine nor language
acceptance, and `totalClock` counts no step that `startConfig` embeds, so it clocks no
composed pipeline.  Clock composition, advice freedom, `NP` membership,
`ContentVerifierBridge`, and P-vs-NP mainline progress are out of scope.

**Progress classification (AGENTS.md): Infrastructure.**
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-! ### The parser side: the register equation, completeness, and the virtual tail -/

/-- **The register equation.**  On a decoded content header the target register digit `j` is
the binary digit `zeros - j` of `n + 1`, for *every* `j ≤ zeros`: the bootstrap's leading
`true` at `j = 0` is the header's own leading digit `(n + 1).testBit zeros`, and each later
digit is the payload cell `8 + zeros + j`.  Two further conjuncts make "complete" precise.
`n + 1` has no bit above `zeros`, so the `zeros + 1` register cells carry *all* of its digits
and none is stored elsewhere.  And for `1 ≤ j ≤ zeros`, where the payload cell has left the
physical word — the **virtual tail** — the register digit is `false` and the parsed digit is
`false` too: `registerBit`'s own padding and the decoder's virtual zero tail agree there,
which is what makes a `false` in a truncated register the parsed target's digit rather than a
default.  The statement mentions no machine, no tag, and no budget. -/
theorem exhaustion_register_digits {a m n consumed : Nat} (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) :
    ∃ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      consumed = 2 * zeros + 1 ∧ 2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      (∀ j, j ≤ zeros →
        FixedGammaTargetPayloadLoopFoundation.registerBit x w zeros j =
          (n + 1).testBit (zeros - j)) ∧
      (∀ b, zeros < b → (n + 1).testBit b = false) ∧
      (∀ j, 1 ≤ j → j ≤ zeros → a + m ≤ 8 + zeros + j →
        FixedGammaTargetPayloadLoopFoundation.registerBit x w zeros j = false ∧
          (n + 1).testBit (zeros - j) = false) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, htop, hdigit⟩ :=
    header_digits (Fin.append x w) hheader
  have hbits : ∀ j, j ≤ zeros →
      FixedGammaTargetPayloadLoopFoundation.registerBit x w zeros j =
        (n + 1).testBit (zeros - j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [(FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).1,
        Nat.sub_zero, htop]
    · obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      rw [(FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).2.2.2 t,
        hdigit t (by omega), show zeros - 1 - t = zeros - (t + 1) by omega]
  refine ⟨zeros, hg, hconsumed, hlo, hhi, hbits, fun b hb => ?_, fun j h1 h2 h3 => ?_⟩
  · have hpow : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.testBit_lt_two_pow (by omega)
  · have hcell : FixedGammaTargetPayloadLoopFoundation.registerBit x w zeros j = false := by
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      rw [(FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).2.2.2 t]
      unfold FixedContentTagGate.physicalSymbol
      rw [dif_neg (by omega)]
      rfl
    exact ⟨hcell, (hbits j h2).symm.trans hcell⟩

/-- **The register pins the target.**  Not only does every register cell hold a digit of
`n + 1`; the cells jointly determine it.  Any `v` whose bit `zeros - j` is the register digit
`j` for every `j ≤ zeros`, and which has no bit above `zeros`, equals `n + 1`.  Both premises
are needed: the register carries only the `zeros + 1` digits at indices `0 … zeros`, so
without the second premise `v` could differ from `n + 1` above the header's leading digit.
This is arithmetic about the digits, not a decoding step performed by any machine. -/
theorem register_determines_target {a m n consumed zeros v : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hbits : ∀ j, j ≤ zeros →
      v.testBit (zeros - j) = FixedGammaTargetPayloadLoopFoundation.registerBit x w zeros j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    v = n + 1 := by
  obtain ⟨zeros', hg', -, -, -, hdig, hzero, -⟩ := exhaustion_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hdig hzero
  refine Nat.eq_of_testBit_eq fun b => ?_
  rcases Nat.lt_or_ge zeros b with hb | hb
  · rw [hhigh b hb, hzero b hb]
  · have h1 := hbits (zeros - b) (by omega)
    have h2 := hdig (zeros - b) (by omega)
    rw [show zeros - (zeros - b) = b by omega] at h1 h2
    rw [h1, h2]

/-- **The room premise, in header terms.**  On a decoded header the bound
`n + 1 < 2 ^ (a + B + 1)` on the parsed target, the width bound `zeros ≤ a + B`, and the room
premise `payload_exhausted` inherits from the pnp3 iteration,
`a + m + 1 + zeros < tapeLength (pairLength a m) B` — the premise that allocates the top
register cell — are one and the same condition.  A decoded header does not imply it: `B` is a
free budget, and at `a = B = 0` the condition fails for every `1 ≤ zeros`.  So the machine
theorems below carry it explicitly, and it is sufficient, not shown necessary: no footprint
theorem exists on the pnp3 side. -/
theorem room_iff_target_bound {a m B n consumed zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (n + 1 < 2 ^ (a + B + 1) ↔ zeros ≤ a + B) ∧
      (zeros ≤ a + B ↔
        a + m + 1 + zeros < tapeLength (PairEncoding.pairLength a m) B) := by
  obtain ⟨zeros', hg', -, hlo, hhi, -, -, -⟩ := exhaustion_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hlo hhi
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · by_contra hc
    have hpow : (2 : Nat) ^ (a + B + 1) ≤ 2 ^ zeros :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hpow : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ (a + B + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · unfold tapeLength PairEncoding.pairLength
    omega

/-! ### The machine side: the exhausted endpoint reads the parsed target -/

/-- **The exhausted register holds the digits of the decoded header's target.**  On a matching
tag, a decoded header with `3 ≤ n`, and the room `n + 1 < 2 ^ (a + B + 1)`, the landed G2p-d
round machine run out of the landed `startConfig` for exactly
`totalClock (a + m) zeros` steps is in `qDone` on the tag cell `7` with tape
`finishTape B x w zeros`, and *every* register cell `a + m + 1 + j`, `j ≤ zeros`, holds the
digit `(n + 1).testBit (zeros - j)`.  Where the payload has been truncated the cell holds
`some false` and the parsed digit is `false` as well, so the virtual tail is the target's own
low digits.  Those endpoint cells moreover *pin* the target: any `v` read off them that has
no bit above `zeros` is `n + 1`.  The tag cell `7` together with the gamma zero field
`[8, 7 + zeros]` is back to the incoming content tape, and because `qDone` absorbs the
endpoint persists at every later time.

Given a decoded header `3 ≤ n` is exactly `2 ≤ zeros`, the premise of the pnp3 endpoint —
both directions follow from the exported bounds, only the direction used here is proved — and
it admits `zeros = 2`, where the round count `zeros - 2` is zero and `totalClock` is the
finish alone.  The room premise is carried, not derived, and is sufficient only
(`room_iff_target_bound`).  The digits of `n + 1` are the header's convention value; nothing
here decrements it to `n`, decodes the register on the tape — the pinning conjunct is
arithmetic about the digits, not a decoding step the control performs — or claims that any
machine executes `contentHeader?`.  `qDone` is an internal control tag: this is neither
halting of a composed machine nor language acceptance, and no converse is claimed. -/
theorem exhausted_register_header_value {a m B n consumed : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) (hn : 3 ≤ n)
    (hroom : n + 1 < 2 ^ (a + B + 1)) :
    ∃ zeros, 2 ≤ zeros ∧ consumed = 2 * zeros + 1 ∧
      2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      a + m + 1 + zeros < tapeLength (PairEncoding.pairLength a m) B ∧
      let d := FixedGammaTargetPayloadRound.machine.run
        (FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros)
        (FixedGammaTargetPayloadRound.startConfig B x w)
      d.state = FixedGammaTargetPayloadRound.qDone ∧ d.head.val = 7 ∧
        d.tape = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → d.tape i = some ((n + 1).testBit (zeros - j))) ∧
        (∀ j : Nat, 1 ≤ j → j ≤ zeros → a + m ≤ 8 + zeros + j →
          (n + 1).testBit (zeros - j) = false ∧
            ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
              i.val = a + m + 1 + j → d.tape i = some false) ∧
        (∀ b : Nat, zeros < b → (n + 1).testBit b = false) ∧
        (∀ v : Nat,
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → d.tape i = some (v.testBit (zeros - j))) →
          (∀ b : Nat, zeros < b → v.testBit b = false) → v = n + 1) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), 7 ≤ i.val →
          i.val < 8 + zeros →
          d.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
        (∀ t, FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros ≤ t →
          FixedGammaTargetPayloadRound.machine.run t
            (FixedGammaTargetPayloadRound.startConfig B x w) = d) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, hbits, hhigh, hvirt⟩ :=
    exhaustion_register_digits x w hheader
  have hz : 2 ≤ zeros := by
    rcases (show zeros = 0 ∨ zeros = 1 ∨ 2 ≤ zeros by omega) with rfl | rfl | h
    · rw [show (2 : Nat) ^ (0 + 1) = 2 from rfl] at hhi
      omega
    · rw [show (2 : Nat) ^ (1 + 1) = 4 from rfl] at hhi
      omega
    · exact h
  have hbound := room_iff_target_bound (B := B) x w hheader hg
  have hroom' : a + m + 1 + zeros < tapeLength (PairEncoding.pairLength a m) B :=
    hbound.2.1 (hbound.1.1 hroom)
  obtain ⟨hq, hh, ht, -, hreg, hgam, hclamp⟩ :=
    FixedGammaTargetPayloadExhaustion.payload_exhausted x w htag hg hz hroom'
  refine ⟨zeros, hz, hconsumed, hlo, hhi, hroom', hq, hh, ht, fun j hj i hi => ?_,
    fun j h1 h2 h3 => ⟨(hvirt j h1 h2 h3).2, fun i hi => ?_⟩, hhigh,
    fun v hv hvhigh => register_determines_target x w hheader hg (fun j hj => ?_) hvhigh,
    fun i h1 h2 => ?_, hclamp⟩
  · rw [hreg j hj i hi, hbits j hj]
  · rw [hreg j h2 i hi, (hvirt j h1 h2 h3).1]
  · have hlt : a + m + 1 + j < tapeLength (PairEncoding.pairLength a m) B := by omega
    exact Option.some.inj
      ((hv j hj ⟨a + m + 1 + j, hlt⟩ rfl).symm.trans (hreg j hj ⟨a + m + 1 + j, hlt⟩ rfl))
  · exact (hgam i h1 h2).1

/-- **The exhausted register holds the digits of the *actual parsed target*.**  Replacing the
header by a successful dependent parse `contentInput? codec (Fin.append x w) = some pr`, for
an arbitrary codec: the target carried by the parsed `PrefixInput` — the `pr.2.n` that
`ContentAccepts` feeds to the search relation — is the outer Sigma index `pr.1` and the
decoded header's first component, and every register cell of the exhausted endpoint holds the
matching digit of `pr.2.n + 1`, virtual tail included.  Those cells pin `pr.2.n + 1` as well:
any `v` whose digits they are and which has no bit above `zeros` is `pr.2.n + 1`.

The parse is the hypothesis, not a claim about execution: no machine here runs
`contentInput?`, the strict parser, or the decoder, and the window length convention
`treeMCSPPrefixM codec pr.1` occurs only in the type of `pr`.  As above the register holds the
digits of `pr.2.n + 1`, the gamma convention value, and the decrement to `pr.2.n` is not
performed.  Nothing here is a `ContentAccepts` statement, a language membership, or
P-vs-NP mainline progress. -/
theorem exhausted_register_parsed_target {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec (Fin.append x w) = some pr) (hn : 3 ≤ pr.2.n)
    (hroom : pr.2.n + 1 < 2 ^ (a + B + 1)) :
    ∃ zeros, 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
      contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
      2 ^ zeros ≤ pr.2.n + 1 ∧ pr.2.n + 1 < 2 ^ (zeros + 1) ∧
      a + m + 1 + zeros < tapeLength (PairEncoding.pairLength a m) B ∧
      let d := FixedGammaTargetPayloadRound.machine.run
        (FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros)
        (FixedGammaTargetPayloadRound.startConfig B x w)
      d.state = FixedGammaTargetPayloadRound.qDone ∧ d.head.val = 7 ∧
        d.tape = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → d.tape i = some ((pr.2.n + 1).testBit (zeros - j))) ∧
        (∀ j : Nat, 1 ≤ j → j ≤ zeros → a + m ≤ 8 + zeros + j →
          (pr.2.n + 1).testBit (zeros - j) = false ∧
            ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
              i.val = a + m + 1 + j → d.tape i = some false) ∧
        (∀ b : Nat, zeros < b → (pr.2.n + 1).testBit b = false) ∧
        (∀ v : Nat,
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → d.tape i = some (v.testBit (zeros - j))) →
          (∀ b : Nat, zeros < b → v.testBit b = false) → v = pr.2.n + 1) ∧
        (∀ t, FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros ≤ t →
          FixedGammaTargetPayloadRound.machine.run t
            (FixedGammaTargetPayloadRound.startConfig B x w) = d) := by
  obtain ⟨consumed, hheader, hidx⟩ :=
    contentInput?_target_eq_contentHeader codec (Fin.append x w) hpr
  rw [← hidx] at hheader
  obtain ⟨zeros, hz, hconsumed, hlo, hhi, hroom', hq, hh, ht, hreg, hvirt, hhigh, hpin, -,
    hclamp⟩ := exhausted_register_header_value (B := B) x w htag hheader hn hroom
  exact ⟨zeros, hz, hidx, by rw [hheader, hconsumed], hlo, hhi, hroom', hq, hh, ht, hreg,
    hvirt, hhigh, hpin, hclamp⟩

end Pnp4.Frontier.ContractExpansion
