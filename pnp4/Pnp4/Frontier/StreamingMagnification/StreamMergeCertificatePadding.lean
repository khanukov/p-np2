import Pnp4.Frontier.StreamingMagnification.StreamMergeEncodedPrenex
import Pnp4.Frontier.StreamingMagnification.StreamMergePrenexBounds
import Mathlib.Tactic

/-!
# Certificate-length padding for the fixed Stream-Merge E-A-E shell

The fixed Stream-Merge shell uses three different wire lengths.  This module
embeds those wires, by explicit zero extension, into the three successive
certificate lengths used by a nested `exists-forall-exists` projection with
exponent `64`:

* `certificateLength m 64`,
* `certificateLength (m + certificateLength m 64) 64`, and
* `certificateLength
    (m + certificateLength m 64 +
      certificateLength (m + certificateLength m 64) 64) 64`.

Here `m` is only an ambient bound with `n <= m` and `s <= m`.  Canonical
outer and inner witnesses have an all-zero unused suffix.  A noncanonical
universal query is deliberately accepted vacuously; this is what makes
universal quantification over the larger carrier exactly equivalent to
universal quantification over the original query wire.

Everything below is a fixed-slice semantic equivalence.  It constructs no
global request encoding, no `OperationalTM`, and no running-time bound for the
matrix predicate.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeCertificatePadding

open Pnp3.ComplexityInterfaces
open StreamMergePrenexWire
open StreamMergePrenexBounds
open StreamMergeEncodedPrenex

/-! ## Successive certificate carriers -/

/-- Certificate length of the outer existential witness. -/
def outerCertificateLength (m : Nat) : Nat :=
  certificateLength m 64

/-- Input length visible to the universal projection after the outer suffix. -/
def middleInputLength (m : Nat) : Nat :=
  m + outerCertificateLength m

/-- Certificate length of the universal witness. -/
def middleCertificateLength (m : Nat) : Nat :=
  certificateLength (middleInputLength m) 64

/-- Input length visible to the inner existential projection. -/
def innerInputLength (m : Nat) : Nat :=
  middleInputLength m + middleCertificateLength m

/-- Certificate length of the inner existential witness. -/
def innerCertificateLength (m : Nat) : Nat :=
  certificateLength (innerInputLength m) 64

/-- Outer witness carrier at the first successive certificate length. -/
abbrev PaddedChoiceWire (m : Nat) :=
  DAGCodec.BitString (outerCertificateLength m)

/-- Universal carrier at the second successive certificate length. -/
abbrev PaddedQueryWire (m : Nat) :=
  DAGCodec.BitString (middleCertificateLength m)

/-- Inner witness carrier at the third successive certificate length. -/
abbrev PaddedInnerWire (m : Nat) :=
  DAGCodec.BitString (innerCertificateLength m)

/-! ## Monotonicity and wire-length bounds -/

/-- `certificateLength` is monotone in its input-length argument. -/
theorem certificateLength_mono_input {left right exponent : Nat}
    (h : left <= right) :
    certificateLength left exponent <= certificateLength right exponent := by
  unfold certificateLength
  exact Nat.add_le_add_right (Nat.pow_le_pow_left h exponent) exponent

theorem choiceLength_le_outerCertificateLength
    (m n s : Nat) (hn : n <= m) (hs : s <= m) :
    choiceLength n s <= outerCertificateLength m := by
  exact (choiceLength_le_commonWireBound n s).trans
    (commonWireBound_le_certificateLength m n s hn hs)

theorem commonWireBound_le_middleCertificateLength
    (m n s : Nat) (hn : n <= m) (hs : s <= m) :
    commonWireBound n s <= middleCertificateLength m := by
  apply (commonWireBound_le_certificateLength m n s hn hs).trans
  apply certificateLength_mono_input
  simp [middleInputLength]

theorem queryLength_le_middleCertificateLength
    (m n s : Nat) (hn : n <= m) (hs : s <= m) :
    queryLength n s <= middleCertificateLength m := by
  exact (queryLength_le_commonWireBound n s).trans
    (commonWireBound_le_middleCertificateLength m n s hn hs)

theorem commonWireBound_le_innerCertificateLength
    (m n s : Nat) (hn : n <= m) (hs : s <= m) :
    commonWireBound n s <= innerCertificateLength m := by
  apply (commonWireBound_le_middleCertificateLength m n s hn hs).trans
  apply certificateLength_mono_input
  simp [innerInputLength]

theorem innerLength_le_innerCertificateLength
    (m n s : Nat) (hn : n <= m) (hs : s <= m) :
    innerLength n s <= innerCertificateLength m := by
  exact (innerLength_le_commonWireBound n s).trans
    (commonWireBound_le_innerCertificateLength m n s hn hs)

/-! ## Executable zero extension and slicing -/

/-- Extend a bitstring to a known larger carrier, filling the suffix by zero. -/
def zeroExtend {short long : Nat} (_h : short <= long)
    (bits : DAGCodec.BitString short) : DAGCodec.BitString long :=
  fun index =>
    if hi : index.val < short then bits <| Fin.mk index.val hi else false

/-- Read the active prefix of a known larger bitstring. -/
def slice {short long : Nat} (h : short <= long)
    (bits : DAGCodec.BitString long) : DAGCodec.BitString short :=
  fun index => bits <| Fin.mk index.val (lt_of_lt_of_le index.isLt h)

/-- The unused suffix of a larger carrier is the canonical all-zero string. -/
def HasZeroPadding {short long : Nat} (_h : short <= long)
    (bits : DAGCodec.BitString long) : Prop :=
  forall index : Fin long, short <= index.val -> bits index = false

instance instDecidableHasZeroPadding {short long : Nat}
    (h : short <= long) (bits : DAGCodec.BitString long) :
    Decidable (HasZeroPadding h bits) := by
  unfold HasZeroPadding
  exact Fintype.decidableForallFintype

@[simp] theorem slice_zeroExtend {short long : Nat} (h : short <= long)
    (bits : DAGCodec.BitString short) :
    slice h (zeroExtend h bits) = bits := by
  funext index
  simp [slice, zeroExtend]

theorem hasZeroPadding_zeroExtend {short long : Nat} (h : short <= long)
    (bits : DAGCodec.BitString short) :
    HasZeroPadding h (zeroExtend h bits) := by
  intro index hindex
  simp [zeroExtend, Nat.not_lt.mpr hindex]

theorem zeroExtend_slice_of_hasZeroPadding {short long : Nat}
    (h : short <= long) (bits : DAGCodec.BitString long)
    (hpadding : HasZeroPadding h bits) :
    zeroExtend h (slice h bits) = bits := by
  funext index
  by_cases hi : index.val < short
  · simp [zeroExtend, slice, hi]
  · rw [zeroExtend, dif_neg hi]
    exact (hpadding index (Nat.le_of_not_gt hi)).symm

/-! ## Typed padding maps for the three Stream-Merge wires -/

def padChoice {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (choice : ChoiceWire n s) : PaddedChoiceWire m :=
  zeroExtend (choiceLength_le_outerCertificateLength m n s hn hs) choice

def unpadChoice {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (choice : PaddedChoiceWire m) : ChoiceWire n s :=
  slice (choiceLength_le_outerCertificateLength m n s hn hs) choice

def ChoicePadding {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (choice : PaddedChoiceWire m) : Prop :=
  HasZeroPadding (choiceLength_le_outerCertificateLength m n s hn hs) choice

instance instDecidableChoicePadding {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (choice : PaddedChoiceWire m) :
    Decidable (ChoicePadding hn hs choice) := by
  unfold ChoicePadding
  infer_instance

def padQuery {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (query : QueryWire n s) : PaddedQueryWire m :=
  zeroExtend (queryLength_le_middleCertificateLength m n s hn hs) query

def unpadQuery {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (query : PaddedQueryWire m) : QueryWire n s :=
  slice (queryLength_le_middleCertificateLength m n s hn hs) query

def QueryPadding {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (query : PaddedQueryWire m) : Prop :=
  HasZeroPadding (queryLength_le_middleCertificateLength m n s hn hs) query

instance instDecidableQueryPadding {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (query : PaddedQueryWire m) :
    Decidable (QueryPadding hn hs query) := by
  unfold QueryPadding
  infer_instance

def padInner {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (inner : InnerWire n s) : PaddedInnerWire m :=
  zeroExtend (innerLength_le_innerCertificateLength m n s hn hs) inner

def unpadInner {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (inner : PaddedInnerWire m) : InnerWire n s :=
  slice (innerLength_le_innerCertificateLength m n s hn hs) inner

def InnerPadding {m n s : Nat} (hn : n <= m) (hs : s <= m)
    (inner : PaddedInnerWire m) : Prop :=
  HasZeroPadding (innerLength_le_innerCertificateLength m n s hn hs) inner

instance instDecidableInnerPadding {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (inner : PaddedInnerWire m) :
    Decidable (InnerPadding hn hs inner) := by
  unfold InnerPadding
  infer_instance

@[simp] theorem unpadChoice_padChoice {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (choice : ChoiceWire n s) :
    unpadChoice hn hs (padChoice hn hs choice) = choice := by
  exact slice_zeroExtend _ choice

theorem choicePadding_padChoice {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (choice : ChoiceWire n s) :
    ChoicePadding hn hs (padChoice hn hs choice) := by
  exact hasZeroPadding_zeroExtend _ choice

theorem padChoice_unpadChoice_of_padding {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (choice : PaddedChoiceWire m)
    (hpadding : ChoicePadding hn hs choice) :
    padChoice hn hs (unpadChoice hn hs choice) = choice := by
  exact zeroExtend_slice_of_hasZeroPadding _ choice hpadding

@[simp] theorem unpadQuery_padQuery {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (query : QueryWire n s) :
    unpadQuery hn hs (padQuery hn hs query) = query := by
  exact slice_zeroExtend _ query

theorem queryPadding_padQuery {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (query : QueryWire n s) :
    QueryPadding hn hs (padQuery hn hs query) := by
  exact hasZeroPadding_zeroExtend _ query

theorem padQuery_unpadQuery_of_padding {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (query : PaddedQueryWire m)
    (hpadding : QueryPadding hn hs query) :
    padQuery hn hs (unpadQuery hn hs query) = query := by
  exact zeroExtend_slice_of_hasZeroPadding _ query hpadding

@[simp] theorem unpadInner_padInner {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (inner : InnerWire n s) :
    unpadInner hn hs (padInner hn hs inner) = inner := by
  exact slice_zeroExtend _ inner

theorem innerPadding_padInner {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (inner : InnerWire n s) :
    InnerPadding hn hs (padInner hn hs inner) := by
  exact hasZeroPadding_zeroExtend _ inner

theorem padInner_unpadInner_of_padding {m n s : Nat}
    (hn : n <= m) (hs : s <= m) (inner : PaddedInnerWire m)
    (hpadding : InnerPadding hn hs inner) :
    padInner hn hs (unpadInner hn hs inner) = inner := by
  exact zeroExtend_slice_of_hasZeroPadding _ inner hpadding

/-! ## Padded matrix and exact E-A-E equivalence -/

/--
The fixed row lifted to successive certificate-length carriers.

The outer suffix must be canonical.  For a canonical universal query, the
inner suffix must also be canonical and the original row is checked on the
three active prefixes.  A noncanonical universal query is accepted
vacuously, so enlarging the universally quantified carrier adds no new
obligation.
-/
def PaddedOutputBitMatrix {m n s blockLength start : Nat}
    (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : PaddedChoiceWire m) (query : PaddedQueryWire m)
    (inner : PaddedInnerWire m) : Prop :=
  And (ChoicePadding hn hs choice)
    (And (InnerPadding hn hs inner)
      (if QueryPadding hn hs query then
        OutputBitMatrix prior block hwindow position
          (unpadChoice hn hs choice) (unpadQuery hn hs query)
          (unpadInner hn hs inner)
      else True))

instance instDecidablePaddedOutputBitMatrix
    {m n s blockLength start : Nat} (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : PaddedChoiceWire m) (query : PaddedQueryWire m)
    (inner : PaddedInnerWire m) :
    Decidable (PaddedOutputBitMatrix hn hs prior block hwindow position
      choice query inner) := by
  unfold PaddedOutputBitMatrix
  infer_instance

/-- A noncanonical universal string imposes no original-matrix obligation;
only the independently required canonical outer and inner padding remains. -/
theorem paddedOutputBitMatrix_noncanonicalQuery_iff
    {m n s blockLength start : Nat} (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : PaddedChoiceWire m) (query : PaddedQueryWire m)
    (inner : PaddedInnerWire m)
    (hquery : QueryPadding hn hs query -> False) :
    PaddedOutputBitMatrix hn hs prior block hwindow position
        choice query inner <->
      ChoicePadding hn hs choice ∧ InnerPadding hn hs inner := by
  unfold PaddedOutputBitMatrix
  rw [if_neg hquery]
  simp

/-- On three canonical extensions, the padded row is exactly the original
fixed-wire row. -/
@[simp] theorem paddedOutputBitMatrix_pad_iff
    {m n s blockLength start : Nat} (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : ChoiceWire n s) (query : QueryWire n s)
    (inner : InnerWire n s) :
    PaddedOutputBitMatrix hn hs prior block hwindow position
        (padChoice hn hs choice) (padQuery hn hs query)
        (padInner hn hs inner) <->
      OutputBitMatrix prior block hwindow position choice query inner := by
  simp [PaddedOutputBitMatrix, choicePadding_padChoice,
    queryPadding_padQuery, innerPadding_padInner]

/-- The certificate-length E-A-E shell for one fixed Stream-Merge slice. -/
def PaddedCertificateEAEShell {m n s blockLength start : Nat}
    (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) : Prop :=
  Exists fun choice : PaddedChoiceWire m =>
    forall query : PaddedQueryWire m,
      Exists fun inner : PaddedInnerWire m =>
        PaddedOutputBitMatrix hn hs prior block hwindow position
          choice query inner

/--
Exact semantic preservation of the fixed E-A-E prefix under the three
successive certificate-length zero extensions.
-/
theorem exists_forall_exists_outputBitMatrix_iff_padded
    {m n s blockLength start : Nat} (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) :
    (Exists fun choice : ChoiceWire n s =>
      forall query : QueryWire n s,
        Exists fun inner : InnerWire n s =>
          OutputBitMatrix prior block hwindow position choice query inner) <->
      PaddedCertificateEAEShell hn hs prior block hwindow position := by
  constructor
  · rintro ⟨choice, hchoice⟩
    refine ⟨padChoice hn hs choice, ?_⟩
    intro query
    by_cases hquery : QueryPadding hn hs query
    · rcases hchoice (unpadQuery hn hs query) with ⟨inner, hinner⟩
      refine ⟨padInner hn hs inner, ?_⟩
      simp only [PaddedOutputBitMatrix, choicePadding_padChoice,
        innerPadding_padInner, true_and, hquery, if_pos,
        unpadChoice_padChoice, unpadInner_padInner]
      exact hinner
    · refine ⟨padInner hn hs (fun _ => false), ?_⟩
      simp [PaddedOutputBitMatrix, choicePadding_padChoice,
        innerPadding_padInner, hquery]
  · rintro ⟨choice, hchoice⟩
    refine ⟨unpadChoice hn hs choice, ?_⟩
    intro query
    rcases hchoice (padQuery hn hs query) with ⟨inner, hinner⟩
    have hquery : QueryPadding hn hs (padQuery hn hs query) :=
      queryPadding_padQuery hn hs query
    have hrow :
        OutputBitMatrix prior block hwindow position
          (unpadChoice hn hs choice) query (unpadInner hn hs inner) := by
      unfold PaddedOutputBitMatrix at hinner
      rw [if_pos hquery] at hinner
      simpa using hinner.2.2
    exact ⟨unpadInner hn hs inner, hrow⟩

/-- Alias-level statement: `EncodedEAEShell` is exactly the padded
certificate-length shell. -/
theorem encodedEAEShell_iff_paddedCertificateEAEShell
    {m n s blockLength start : Nat} (hn : n <= m) (hs : s <= m)
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) :
    EncodedEAEShell prior block hwindow position <->
      PaddedCertificateEAEShell hn hs prior block hwindow position := by
  exact exists_forall_exists_outputBitMatrix_iff_padded
    hn hs prior block hwindow position

/-- Direct capstone for one reference output bit: the executable reference
semantics is equivalent to the E-A-E shell over the three successive
certificate-length carriers. -/
theorem referenceOutputBit_eq_true_iff_paddedCertificateEAEShell
    {m n s blockLength start : Nat} (hn : n <= m) (hs : s <= m)
    (block : List Bool) (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : StreamMerge.WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) :
    StreamMergeWire.referenceOutputBit
        priorCode blockLength start block position = true <->
      PaddedCertificateEAEShell hn hs prior block hwindow position := by
  calc
    StreamMergeWire.referenceOutputBit
          priorCode blockLength start block position = true <->
        EncodedEAEShell prior block hwindow position :=
      referenceOutputBit_eq_true_iff_encodedEAEShell
        block priorCode prior hprior hwindow position
    _ <-> PaddedCertificateEAEShell hn hs prior block hwindow position :=
      encodedEAEShell_iff_paddedCertificateEAEShell
        hn hs prior block hwindow position

end StreamMergeCertificatePadding
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeCertificatePadding.exists_forall_exists_outputBitMatrix_iff_padded
#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeCertificatePadding.encodedEAEShell_iff_paddedCertificateEAEShell
#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeCertificatePadding.referenceOutputBit_eq_true_iff_paddedCertificateEAEShell
