import Pnp4.Frontier.StreamingMagnification.StreamMergePrenexWire
import Mathlib.Tactic

/-!
# Arithmetic bounds for the fixed Stream-Merge prenex wires

The three prenex carriers have exact lengths

* `1 + codeLength n s`,
* `1 + (n + codeLength n s)`, and
* `n + (s + s)`.

This module proves a coarse explicit polynomial upper bound on those lengths.
It does not bound the running time of `OutputBitMatrix`, relate `n,s` to the
length of one globally encoded request, or provide an operational machine.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergePrenexBounds

open StreamMergePrenexWire

/-- Exact number of outer-choice bits. -/
def choiceLength (n s : Nat) : Nat :=
  1 + DAGCodec.codeLength n s

/-- Exact number of universal-query bits. -/
def queryLength (n s : Nat) : Nat :=
  1 + (n + DAGCodec.codeLength n s)

/-- Exact number of innermost trace/failure bits. -/
def innerLength (n s : Nat) : Nat :=
  n + (s + s)

/-- Coarse polynomial bound obtained by replacing `ceil(log_2 x)` by `x`. -/
def coarseCodeBound (n s : Nat) : Nat :=
  5 * (s + 1) * (n + s + 2)

/-- One common polynomial bound for every prenex wire. -/
def commonWireBound (n s : Nat) : Nat :=
  1 + n + 2 * s + coarseCodeBound n s

/-- Elementary arithmetic used to remove the logarithm from the code bound. -/
theorem self_le_two_pow (value : Nat) : value ≤ 2 ^ value := by
  induction value with
  | zero => simp
  | succ value ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ value := Nat.one_le_two_pow
      omega

/-- The binary ceiling logarithm is at most its argument. -/
theorem clog_two_le_self (value : Nat) : Nat.clog 2 value ≤ value := by
  exact (Nat.le_pow_iff_clog_le (by decide : 1 < (2 : Nat))).1
    (self_le_two_pow value)

/-- The canonical circuit body has a uniform coarse polynomial length. -/
theorem codeLength_le_coarseCodeBound (n s : Nat) :
    DAGCodec.codeLength n s ≤ coarseCodeBound n s := by
  apply (DAGCodec.codeLength_le n s).trans
  have hlog : Nat.clog 2 (n + s + 2) ≤ n + s + 2 :=
    clog_two_le_self (n + s + 2)
  simpa [coarseCodeBound] using
    Nat.mul_le_mul_left (5 * (s + 1)) hlog

/-- Every gate slot contributes at least its three tag bits.  This lower
bound is useful when a future request format contains a complete prior code:
the request length then controls the threshold parameter `s`. -/
theorem three_mul_le_codeLength (n s : Nat) :
    3 * s ≤ DAGCodec.codeLength n s := by
  have hslot : 3 ≤ DAGCodec.slotWidth n s := by
    simp [DAGCodec.slotWidth]
  have hmul : s * 3 ≤ s * DAGCodec.slotWidth n s :=
    Nat.mul_le_mul_left s hslot
  unfold DAGCodec.codeLength
  omega

theorem choiceLength_le_commonWireBound (n s : Nat) :
    choiceLength n s ≤ commonWireBound n s := by
  have hcode := codeLength_le_coarseCodeBound n s
  unfold choiceLength commonWireBound
  omega

theorem queryLength_le_commonWireBound (n s : Nat) :
    queryLength n s ≤ commonWireBound n s := by
  have hcode := codeLength_le_coarseCodeBound n s
  unfold queryLength commonWireBound
  omega

theorem innerLength_le_commonWireBound (n s : Nat) :
    innerLength n s ≤ commonWireBound n s := by
  unfold innerLength commonWireBound
  omega

/-- Once both Stream-Merge parameters are bounded by an ambient input length,
all three fixed wires have one explicit quadratic ambient bound.  Establishing
those two parameter inequalities is deliberately left to the future global
request parser. -/
theorem commonWireBound_le_of_parameters_le
    (m n s : Nat) (hn : n ≤ m) (hs : s ≤ m) :
    commonWireBound n s ≤ 14 * (m + 1) ^ 2 := by
  have hs1 : s + 1 ≤ m + 1 := by omega
  have hsum : n + s + 2 ≤ 2 * (m + 1) := by omega
  have hcoarse : coarseCodeBound n s ≤ 10 * (m + 1) ^ 2 := by
    unfold coarseCodeBound
    calc
      5 * (s + 1) * (n + s + 2) ≤
          5 * (m + 1) * (2 * (m + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 5 hs1) hsum
      _ = 10 * (m + 1) ^ 2 := by ring
  have hprefix : 1 + n + 2 * s ≤ 4 * (m + 1) ^ 2 := by
    nlinarith
  unfold commonWireBound
  omega

/-- A concrete certificate exponent large enough to absorb the common
quadratic wire bound even at the exceptional ambient lengths `0` and `1`.
This is a length statement only; it supplies no parser or verifier machine. -/
theorem commonWireBound_le_certificateLength
    (m n s : Nat) (hn : n ≤ m) (hs : s ≤ m) :
    commonWireBound n s ≤
      Pnp3.ComplexityInterfaces.certificateLength m 64 := by
  apply (commonWireBound_le_of_parameters_le m n s hn hs).trans
  unfold Pnp3.ComplexityInterfaces.certificateLength
  by_cases hm : m < 2
  · interval_cases m <;> norm_num
  · have hm2 : 2 ≤ m := by omega
    have hplus : m + 1 ≤ 2 * m := by omega
    have hpow : 56 ≤ m ^ 62 := by
      calc
        56 ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by norm_num)
        _ ≤ m ^ 62 := Nat.pow_le_pow_left hm2 62
    calc
      14 * (m + 1) ^ 2 ≤ 14 * (2 * m) ^ 2 :=
        Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left hplus 2)
      _ = 56 * m ^ 2 := by ring
      _ ≤ m ^ 62 * m ^ 2 := Nat.mul_le_mul_right (m ^ 2) hpow
      _ = m ^ 64 := by ring
      _ ≤ m ^ 64 + 64 := Nat.le_add_right _ _

/-- The carrier aliases expose exactly the declared lengths. -/
theorem choiceWire_card (n s : Nat) :
    Fintype.card (ChoiceWire n s) = 2 ^ choiceLength n s := by
  simp [ChoiceWire, EncodedTotalSearch.ResultWire, choiceLength,
    DAGCodec.BitString]

theorem queryWire_card (n s : Nat) :
    Fintype.card (QueryWire n s) = 2 ^ queryLength n s := by
  simp [QueryWire, queryLength, DAGCodec.BitString]

theorem innerWire_card (n s : Nat) :
    Fintype.card (InnerWire n s) = 2 ^ innerLength n s := by
  simp [InnerWire, StreamMergeFailureMatrix.FailureWitness,
    innerLength, DAGCodec.BitString]

end StreamMergePrenexBounds
end StreamingMagnification
end Frontier
end Pnp4
