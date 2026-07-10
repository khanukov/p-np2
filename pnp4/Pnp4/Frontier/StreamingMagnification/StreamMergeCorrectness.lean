import Pnp4.Frontier.StreamingMagnification.StreamMerge
import Mathlib.Tactic

/-!
# Correctness of the executable Stream-Merge reference function

The theorems here establish exhaustive size-then-serialized-lex selection,
the exact prefix-extension invariant, and the two final total-search
directions.  They concern `referenceStreamMerge`, not an operational
`StreamingRAM.Program` and not a resource bound.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMerge

open StandardDAG
open TotalSearch

/-! ## The serialized enumeration is exact -/

@[simp] theorem serializedIndex_codeAtSerializedIndex
    {n s : Nat} (index : Fin (2 ^ DAGCodec.codeLength n s)) :
    serializedIndex (codeAtSerializedIndex index) = index := by
  apply Fin.ext
  change
    (BitVec.ofFnBE
      (fun position =>
        (BitVec.ofNatLT index.val index.isLt).getMsb position)).toNat =
      index.val
  have hvector :
      BitVec.ofFnBE
        (fun position =>
          (BitVec.ofNatLT index.val index.isLt).getMsb position) =
        BitVec.ofNatLT index.val index.isLt := by
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    rw [BitVec.getMsbD_ofFnBE]
    simp [hi, BitVec.getMsb, BitVec.getMsbD,
      BitVec.getLsb, BitVec.getLsbD]
  rw [hvector]
  exact BitVec.toNat_ofNatLT index.val index.isLt

@[simp] theorem codeAtSerializedIndex_serializedIndex
    {n s : Nat} (code : DAGCodec.Code n s) :
    codeAtSerializedIndex (serializedIndex code) = code := by
  funext position
  change
    (BitVec.ofNatLT (BitVec.ofFnBE code).toNat _).getMsb position =
      code position
  rw [BitVec.ofNatLT_toNat]
  exact BitVec.getMsb_ofFnBE code position

theorem serializedIndex_injective {n s : Nat} :
    Function.Injective (@serializedIndex n s) := by
  intro left right heq
  simpa only [codeAtSerializedIndex_serializedIndex] using
    congrArg (@codeAtSerializedIndex n s) heq

/-! ## Facts about the nested exhaustive search -/

/-- `Fin.find?` really returns the least successful natural index.  Batteries
currently exposes soundness and the `none` characterization but not this
minimality direction. -/
theorem finFind_minimal
    {m : Nat} {predicate : Fin m -> Bool} {index : Fin m}
    (hfind : Fin.find? predicate = some index) :
    forall earlier : Fin m, earlier < index -> predicate earlier = false := by
  induction m with
  | zero => exact Fin.elim0 index
  | succ m ih =>
      rw [Fin.find?_succ] at hfind
      split at hfind
      next hzero =>
        have hindex : (0 : Fin (m + 1)) = index :=
          Option.some.inj hfind
        subst index
        intro earlier hearlier
        exact (Fin.not_lt_zero earlier hearlier).elim
      next hzero =>
        rcases Option.map_eq_some_iff.mp hfind with
          ⟨previous, hprevious, hindex⟩
        subst index
        intro earlier hearlier
        cases earlier using Fin.cases with
        | zero => exact Bool.eq_false_of_not_eq_true hzero
        | succ earlier' =>
          apply ih hprevious earlier'
          change earlier'.val < previous.val
          change earlier'.val + 1 < previous.val + 1 at hearlier
          omega

theorem eligibleAtGateCount_eq_true_iff
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) (gateCount : Fin (s + 1))
    (index : Fin (2 ^ DAGCodec.codeLength n s)) :
    eligibleAtGateCount prior start block gateCount index = true <->
      Exists fun candidate : DAGCodec.BoundedCircuit n s =>
        DAGCodec.decode (codeAtSerializedIndex index) = some candidate /\
          candidate.val.gateCount = gateCount.val /\
          Fits prior candidate start block := by
  unfold eligibleAtGateCount
  split <;> simp_all

theorem firstCodeAtGateCount_some_sound
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool} {gateCount : Fin (s + 1)}
    {index : Fin (2 ^ DAGCodec.codeLength n s)}
    (hfind : firstCodeAtGateCount prior start block gateCount = some index) :
    Exists fun candidate : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode (codeAtSerializedIndex index) = some candidate /\
        candidate.val.gateCount = gateCount.val /\
        Fits prior candidate start block := by
  apply (eligibleAtGateCount_eq_true_iff
    prior start block gateCount index).mp
  exact Fin.eq_true_of_find?_eq_some hfind

theorem firstCodeAtGateCount_isSome_of_candidate
    {n s : Nat} (prior candidate : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool)
    (gateCount : Fin (s + 1))
    (hgate : candidate.val.gateCount = gateCount.val)
    (hfits : Fits prior candidate start block) :
    (firstCodeAtGateCount prior start block gateCount).isSome = true := by
  rw [firstCodeAtGateCount, Fin.find?_isSome_iff]
  refine Exists.intro (serializedIndex (DAGCodec.encode candidate)) ?_
  apply (eligibleAtGateCount_eq_true_iff prior start block gateCount _).mpr
  refine Exists.intro candidate ?_
  simp only [codeAtSerializedIndex_serializedIndex, DAGCodec.decode_encode,
    true_and]
  exact And.intro hgate hfits

theorem firstGateCount_some_sound
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool} {gateCount : Fin (s + 1)}
    (hfind : firstGateCount prior start block = some gateCount) :
    Exists fun index : Fin (2 ^ DAGCodec.codeLength n s) =>
      firstCodeAtGateCount prior start block gateCount = some index := by
  have hsome :
      (firstCodeAtGateCount prior start block gateCount).isSome = true :=
    Fin.eq_true_of_find?_eq_some hfind
  exact Option.isSome_iff_exists.mp hsome

theorem firstGateCount_isSome_of_candidate
    {n s : Nat} (prior candidate : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool)
    (hfits : Fits prior candidate start block) :
    (firstGateCount prior start block).isSome = true := by
  rw [firstGateCount, Fin.find?_isSome_iff]
  let gateCount : Fin (s + 1) :=
    { val := candidate.val.gateCount
      isLt := Nat.lt_succ_of_le candidate.property }
  refine Exists.intro gateCount ?_
  exact firstCodeAtGateCount_isSome_of_candidate
    prior candidate start block gateCount rfl hfits

theorem firstGateCount_le_of_some
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool}
    {selected other : Fin (s + 1)}
    (hselected : firstGateCount prior start block = some selected)
    (hother :
      (firstCodeAtGateCount prior start block other).isSome = true) :
    selected <= other := by
  by_contra hnot
  have hlt : other < selected := by omega
  have hfalse := finFind_minimal hselected other hlt
  rw [hother] at hfalse
  contradiction

theorem firstCodeAtGateCount_le_serializedIndex
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool} {gateCount : Fin (s + 1)}
    {selectedIndex : Fin (2 ^ DAGCodec.codeLength n s)}
    (hselected :
      firstCodeAtGateCount prior start block gateCount = some selectedIndex)
    (otherCode : DAGCodec.Code n s)
    (other : DAGCodec.BoundedCircuit n s)
    (hdecode : DAGCodec.decode otherCode = some other)
    (hgate : other.val.gateCount = gateCount.val)
    (hfits : Fits prior other start block) :
    selectedIndex <= serializedIndex otherCode := by
  by_contra hnot
  have hlt : serializedIndex otherCode < selectedIndex := by omega
  have hfalse := finFind_minimal hselected (serializedIndex otherCode) hlt
  have htrue : eligibleAtGateCount prior start block gateCount
      (serializedIndex otherCode) = true := by
    apply (eligibleAtGateCount_eq_true_iff prior start block gateCount _).mpr
    exact ⟨other, by simpa using hdecode, hgate, hfits⟩
  rw [htrue] at hfalse
  contradiction

theorem selectCode_some_indices
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool} {code : DAGCodec.Code n s}
    (hselect : selectCode prior start block = some code) :
    Exists fun gateCount : Fin (s + 1) =>
      Exists fun index : Fin (2 ^ DAGCodec.codeLength n s) =>
        firstGateCount prior start block = some gateCount /\
          firstCodeAtGateCount prior start block gateCount = some index /\
          code = codeAtSerializedIndex index := by
  cases hgate : firstGateCount prior start block with
  | none =>
      simp [selectCode, hgate] at hselect
  | some gateCount =>
      cases hindex : firstCodeAtGateCount prior start block gateCount with
      | none =>
          simp [selectCode, hgate, hindex] at hselect
      | some index =>
          refine ⟨gateCount, index, rfl, hindex, ?_⟩
          simpa [selectCode, hgate, hindex] using hselect.symm

/-- The selected body has minimum internal-gate count and, among bodies at
that count, is first in physical serialized-bit order. -/
theorem selectCode_some_optimal
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool} {code : DAGCodec.Code n s}
    (hselect : selectCode prior start block = some code) :
    Exists fun selected : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some selected /\
        Fits prior selected start block /\
        forall (otherCode : DAGCodec.Code n s)
          (other : DAGCodec.BoundedCircuit n s),
          DAGCodec.decode otherCode = some other ->
          Fits prior other start block ->
          selected.val.gateCount <= other.val.gateCount /\
            (selected.val.gateCount = other.val.gateCount ->
              SerializedLexLE code otherCode) := by
  rcases selectCode_some_indices hselect with
    ⟨gateCount, index, hgateFind, hindexFind, hcode⟩
  rcases firstCodeAtGateCount_some_sound hindexFind with
    ⟨selected, hselectedDecode, hselectedGate, hselectedFits⟩
  refine ⟨selected, ?_, hselectedFits, ?_⟩
  · simpa [hcode] using hselectedDecode
  · intro otherCode other hotherDecode hotherFits
    let otherGateCount : Fin (s + 1) :=
      { val := other.val.gateCount
        isLt := Nat.lt_succ_of_le other.property }
    have hotherSome :
        (firstCodeAtGateCount prior start block otherGateCount).isSome = true :=
      firstCodeAtGateCount_isSome_of_candidate prior other start block
        otherGateCount rfl hotherFits
    have hgateLE : gateCount <= otherGateCount :=
      firstGateCount_le_of_some hgateFind hotherSome
    constructor
    · rw [hselectedGate]
      exact hgateLE
    · intro hequal
      have hotherGate : other.val.gateCount = gateCount.val := by
        calc
          other.val.gateCount = selected.val.gateCount := hequal.symm
          _ = gateCount.val := hselectedGate
      have hindexLE := firstCodeAtGateCount_le_serializedIndex
        hindexFind otherCode other hotherDecode hotherGate hotherFits
      unfold SerializedLexLE
      simpa [hcode] using hindexLE

theorem selectCode_some_sound
    {n s : Nat} {prior : DAGCodec.BoundedCircuit n s}
    {start : Nat} {block : List Bool} {code : DAGCodec.Code n s}
    (hselect : selectCode prior start block = some code) :
    Exists fun candidate : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some candidate /\
        Fits prior candidate start block := by
  cases hgate : firstGateCount prior start block with
  | none =>
      simp [selectCode, hgate] at hselect
  | some gateCount =>
      cases hindex : firstCodeAtGateCount prior start block gateCount with
      | none =>
          simp [selectCode, hgate, hindex] at hselect
      | some index =>
          have hcode : codeAtSerializedIndex index = code := by
            simpa [selectCode, hgate, hindex] using hselect
          rcases firstCodeAtGateCount_some_sound hindex with
            ⟨candidate, hdecode, _hgate, hfits⟩
          subst code
          exact ⟨candidate, hdecode, hfits⟩

theorem selectCode_isSome_of_candidate
    {n s : Nat} (prior candidate : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool)
    (hfits : Fits prior candidate start block) :
    (selectCode prior start block).isSome = true := by
  have hgateSome := firstGateCount_isSome_of_candidate
    prior candidate start block hfits
  rcases Option.isSome_iff_exists.mp hgateSome with ⟨gateCount, hgate⟩
  rcases firstGateCount_some_sound hgate with ⟨index, hindex⟩
  simp [selectCode, hgate, hindex]

theorem selectCode_eq_none_iff
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) :
    selectCode prior start block = none <->
      Not (HasCandidate prior start block) := by
  constructor
  · intro hnone hcandidate
    rcases hcandidate with ⟨candidate, hfits⟩
    have hsome := selectCode_isSome_of_candidate
      prior candidate start block hfits
    rw [hnone] at hsome
    contradiction
  · intro hnone
    cases hselect : selectCode prior start block with
    | none => rfl
    | some code =>
        rcases selectCode_some_sound hselect with
          ⟨candidate, _hdecode, hfits⟩
        exact (hnone ⟨candidate, hfits⟩).elim

theorem selectCode_some_exists_iff
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) :
    (Exists fun code : DAGCodec.Code n s =>
      selectCode prior start block = some code) <->
      HasCandidate prior start block := by
  constructor
  · rintro ⟨code, hselect⟩
    rcases selectCode_some_sound hselect with
      ⟨candidate, _hdecode, hfits⟩
    exact ⟨candidate, hfits⟩
  · intro hcandidate
    cases hselect : selectCode prior start block with
    | none =>
        exact ((selectCode_eq_none_iff prior start block).mp
          hselect hcandidate).elim
    | some code =>
        exact ⟨code, rfl⟩

/-! ## Public tagged-result correctness -/

theorem referenceStreamMerge_valid_eq
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block) :
    referenceStreamMerge priorCode blockLength start block =
      match selectCode prior start block with
      | some code => Result.found code
      | none => Result.noCircuit := by
  simp [referenceStreamMerge, hprior, hwindow.1, hwindow.2]
  rfl

theorem referenceStreamMerge_found_iff_selectCode
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode code : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block) :
    referenceStreamMerge priorCode blockLength start block = Result.found code <->
      selectCode prior start block = some code := by
  rw [referenceStreamMerge_valid_eq block priorCode prior hprior hwindow]
  cases selectCode prior start block <;> simp

theorem referenceStreamMerge_found_sound
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode code : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hmerge : referenceStreamMerge priorCode blockLength start block =
      Result.found code) :
    Exists fun candidate : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some candidate /\
        Fits prior candidate start block := by
  apply selectCode_some_sound
  exact (referenceStreamMerge_found_iff_selectCode
    block priorCode code prior hprior hwindow).mp hmerge

/-- Public optimality statement for a concrete `found` result: the returned
body is canonical, fitting, minimum-size, and serialized-bit-lex-first among
all fitting bodies of the same size. -/
theorem referenceStreamMerge_found_optimal
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode code : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hmerge : referenceStreamMerge priorCode blockLength start block =
      Result.found code) :
    Exists fun selected : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some selected /\
        Fits prior selected start block /\
        forall (otherCode : DAGCodec.Code n s)
          (other : DAGCodec.BoundedCircuit n s),
          DAGCodec.decode otherCode = some other ->
          Fits prior other start block ->
          selected.val.gateCount <= other.val.gateCount /\
            (selected.val.gateCount = other.val.gateCount ->
              SerializedLexLE code otherCode) := by
  apply selectCode_some_optimal
  exact (referenceStreamMerge_found_iff_selectCode
    block priorCode code prior hprior hwindow).mp hmerge

theorem referenceStreamMerge_found_exists_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block) :
    (Exists fun code : DAGCodec.Code n s =>
      referenceStreamMerge priorCode blockLength start block =
        Result.found code) <->
      HasCandidate prior start block := by
  constructor
  · rintro ⟨code, hmerge⟩
    rcases referenceStreamMerge_found_sound hprior hwindow hmerge with
      ⟨candidate, _hdecode, hfits⟩
    exact ⟨candidate, hfits⟩
  · intro hcandidate
    rcases (selectCode_some_exists_iff prior start block).mpr hcandidate with
      ⟨code, hselect⟩
    refine ⟨code, ?_⟩
    rw [referenceStreamMerge_valid_eq block priorCode prior hprior hwindow,
      hselect]

theorem referenceStreamMerge_noCircuit_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block) :
    referenceStreamMerge priorCode blockLength start block = Result.noCircuit <->
      Not (HasCandidate prior start block) := by
  rw [← selectCode_eq_none_iff prior start block]
  cases hselect : selectCode prior start block <;>
    simp [referenceStreamMerge, hprior, hwindow.1, hwindow.2, hselect]

theorem referenceStreamMerge_invalidPrior_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s) :
    referenceStreamMerge priorCode blockLength start block =
        Result.malformed MalformedReason.invalidPrior <->
      DAGCodec.decode priorCode = none := by
  unfold referenceStreamMerge
  cases hdecode : DAGCodec.decode priorCode with
  | none => simp
  | some prior =>
      simp only
      by_cases hstart : start <= 2 ^ n
      · rw [if_pos hstart]
        by_cases hlength : block.length = expectedLength n blockLength start
        · rw [if_pos hlength]
          cases selectCode prior start block <;> simp
        · rw [if_neg hlength]
          simp
      · rw [if_neg hstart]
        simp

theorem referenceStreamMerge_startPastEnd_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior) :
    referenceStreamMerge priorCode blockLength start block =
        Result.malformed MalformedReason.startPastEnd <->
      2 ^ n < start := by
  unfold referenceStreamMerge
  rw [hprior]
  simp only
  by_cases hstart : start <= 2 ^ n
  · rw [if_pos hstart]
    have hnot : Not (2 ^ n < start) := by omega
    rw [iff_false_intro hnot]
    by_cases hlength : block.length = expectedLength n blockLength start
    · rw [if_pos hlength]
      cases selectCode prior start block <;> simp
    · rw [if_neg hlength]
      simp
  · rw [if_neg hstart]
    simp
    omega

theorem referenceStreamMerge_wrongBlockLength_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hstart : start <= 2 ^ n) :
    referenceStreamMerge priorCode blockLength start block =
        Result.malformed MalformedReason.wrongBlockLength <->
      block.length ≠ expectedLength n blockLength start := by
  unfold referenceStreamMerge
  rw [hprior]
  simp only
  rw [if_pos hstart]
  by_cases hlength : block.length = expectedLength n blockLength start
  · rw [if_pos hlength]
    cases selectCode prior start block <;> simp [hlength]
  · rw [if_neg hlength]
    simp [hlength]

/-! ## Exact prefix-extension invariant -/

@[simp] theorem expectedLength_at_completed
    (n blockLength : Nat) :
    expectedLength n blockLength (2 ^ n) = 0 := by
  simp [expectedLength]

/-- A nominal block larger than the whole table becomes one exact initial
partial block rather than overrunning or skipping the table. -/
theorem expectedLength_at_zero_of_table_le
    {n blockLength : Nat} (hlarge : 2 ^ n <= blockLength) :
    expectedLength n blockLength 0 = 2 ^ n := by
  simp [expectedLength, min_eq_right hlarge]

/-- At any final partial window, the actual length is exactly the remaining
number of table bits. -/
theorem expectedLength_eq_remaining
    {n blockLength start : Nat}
    (hremaining : 2 ^ n - start <= blockLength) :
    expectedLength n blockLength start = 2 ^ n - start := by
  exact min_eq_right hremaining

/-- Away from the final partial window, a full nominal block is used. -/
theorem expectedLength_eq_nominal
    {n blockLength start : Nat}
    (hfull : blockLength <= 2 ^ n - start) :
    expectedLength n blockLength start = blockLength := by
  exact min_eq_left hfull

/-- Agreement with the first `used` bits of a supplied truth table. -/
def PrefixAgreement {n : Nat} (circuit : FlatCircuit n)
    (table : TruthTable n) (used : Nat) : Prop :=
  (circuitBits circuit).take used = (tableBits table).take used

/-- The literal table block beginning at `start`. -/
def tableBlock {n : Nat} (table : TruthTable n)
    (start length : Nat) : List Bool :=
  ((tableBits table).drop start).take length

theorem nextConsumed_le
    {n blockLength start : Nat} {block : List Bool}
    (hwindow : WindowWellFormed n blockLength start block) :
    start + block.length <= 2 ^ n := by
  have hstart := hwindow.1
  have hlength : block.length <= 2 ^ n - start := by
    rw [hwindow.2]
    exact min_le_right _ _
  omega

/-- Under the exact window bounds, the combined-prefix definition of `Fits`
is equivalent to the two literal MMW constraints. -/
theorem fits_iff_priorPrefix_and_block
    {n s blockLength start : Nat} {block : List Bool}
    (prior candidate : DAGCodec.BoundedCircuit n s)
    (hwindow : WindowWellFormed n blockLength start block) :
    Fits prior candidate start block <->
      (circuitBits candidate.val).take start =
          (circuitBits prior.val).take start /\
        ((circuitBits candidate.val).drop start).take block.length = block := by
  have hstart : start <= 2 ^ n := hwindow.1
  have hpriorLength :
      ((circuitBits prior.val).take start).length = start := by
    simp [List.length_take, circuitBits_length, hstart]
  constructor
  · intro hfits
    unfold Fits targetPrefix at hfits
    have hprefix := congrArg (List.take start) hfits
    have hblock := congrArg (List.drop start) hfits
    constructor
    · simpa [List.take_take, hpriorLength] using hprefix
    · simpa [List.drop_take, hpriorLength] using hblock
  · rintro ⟨hprefix, hblock⟩
    unfold Fits targetPrefix
    rw [List.take_add, hprefix, hblock]

/-- A correct prior prefix and literal next block identify the combined
target with the corresponding longer table prefix. -/
theorem targetPrefix_eq_tablePrefix
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (table : TruthTable n) (start : Nat) (block : List Bool)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length) :
    targetPrefix prior start block =
      (tableBits table).take (start + block.length) := by
  unfold PrefixAgreement at hprior
  unfold targetPrefix
  rw [hprior]
  calc
    (tableBits table).take start ++ block =
        (tableBits table).take start ++
          ((tableBits table).drop start).take block.length := by
      exact congrArg ((tableBits table).take start ++ ·) hblock
    _ = (tableBits table).take (start + block.length) :=
      List.take_add.symm

/-- The semantic merge candidate exists exactly when a bounded circuit for
the enlarged literal prefix exists.  This is the one-step inductive
invariant used by the block driver. -/
theorem hasCandidate_iff_prefixExtension
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (table : TruthTable n) (start : Nat) (block : List Bool)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length) :
    HasCandidate prior start block <->
      Exists fun candidate : DAGCodec.BoundedCircuit n s =>
        PrefixAgreement candidate.val table (start + block.length) := by
  have htarget := targetPrefix_eq_tablePrefix
    prior table start block hprior hblock
  constructor
  · rintro ⟨candidate, hfits⟩
    refine ⟨candidate, ?_⟩
    unfold Fits PrefixAgreement at *
    simpa only [htarget] using hfits
  · rintro ⟨candidate, hagree⟩
    refine ⟨candidate, ?_⟩
    unfold Fits PrefixAgreement at *
    simpa only [htarget] using hagree

/-- On a well-formed request, a found tag exists exactly when the longer
prefix has a bounded circuit. -/
theorem referenceStreamMerge_found_iff_prefixExtension
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (table : TruthTable n)
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length) :
    (Exists fun code : DAGCodec.Code n s =>
      referenceStreamMerge priorCode blockLength start block =
        Result.found code) <->
      Exists fun candidate : DAGCodec.BoundedCircuit n s =>
        PrefixAgreement candidate.val table (start + block.length) := by
  exact (referenceStreamMerge_found_exists_iff
    block priorCode prior hdecode hwindow).trans
      (hasCandidate_iff_prefixExtension prior table start block hprior hblock)

/-- The genuine `noCircuit` tag is equivalent to non-existence for the
enlarged prefix. -/
theorem referenceStreamMerge_noCircuit_iff_noPrefixExtension
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (table : TruthTable n)
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length) :
    referenceStreamMerge priorCode blockLength start block = Result.noCircuit <->
      Not (Exists fun candidate : DAGCodec.BoundedCircuit n s =>
        PrefixAgreement candidate.val table (start + block.length)) := by
  rw [referenceStreamMerge_noCircuit_iff
    block priorCode prior hdecode hwindow]
  exact not_congr
    (hasCandidate_iff_prefixExtension prior table start block hprior hblock)

/-- A concrete found body decodes to a circuit satisfying the enlarged
prefix invariant. -/
theorem referenceStreamMerge_found_prefixAgreement
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode code : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    {table : TruthTable n}
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hmerge : referenceStreamMerge priorCode blockLength start block =
      Result.found code) :
    Exists fun candidate : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some candidate /\
        PrefixAgreement candidate.val table (start + block.length) := by
  rcases referenceStreamMerge_found_sound hdecode hwindow hmerge with
    ⟨candidate, hcandidateDecode, hfits⟩
  refine ⟨candidate, hcandidateDecode, ?_⟩
  have htarget := targetPrefix_eq_tablePrefix
    prior table start block hprior hblock
  unfold Fits PrefixAgreement at *
  simpa only [htarget] using hfits

/-! ## Full-table endpoints -/

theorem prefixAgreement_full_iff_computes
    {n : Nat} (circuit : FlatCircuit n) (table : TruthTable n) :
    PrefixAgreement circuit table (2 ^ n) <-> Computes circuit table := by
  unfold PrefixAgreement circuitBits tableBits Computes
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  exact List.ofFn_inj

theorem boundedComputes_iff_hasCircuit
    {n s : Nat} (table : TruthTable n) :
    (Exists fun circuit : DAGCodec.BoundedCircuit n s =>
      Computes circuit.val table) <-> HasCircuit n s table := by
  constructor
  · rintro ⟨circuit, hcomputes⟩
    exact ⟨circuit.val, circuit.property, hcomputes⟩
  · rintro ⟨circuit, hsize, hcomputes⟩
    exact ⟨⟨circuit, hsize⟩, hcomputes⟩

theorem referenceStreamMerge_final_found_iff_hasCircuit
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (table : TruthTable n)
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hfinal : start + block.length = 2 ^ n) :
    (Exists fun code : DAGCodec.Code n s =>
      referenceStreamMerge priorCode blockLength start block =
        Result.found code) <-> HasCircuit n s table := by
  rw [referenceStreamMerge_found_iff_prefixExtension
    block priorCode prior table hdecode hwindow hprior hblock]
  simp only [hfinal, prefixAgreement_full_iff_computes]
  exact boundedComputes_iff_hasCircuit table

theorem referenceStreamMerge_final_noCircuit_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (table : TruthTable n)
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hfinal : start + block.length = 2 ^ n) :
    referenceStreamMerge priorCode blockLength start block = Result.noCircuit <->
      Not (HasCircuit n s table) := by
  rw [referenceStreamMerge_noCircuit_iff_noPrefixExtension
    block priorCode prior table hdecode hwindow hprior hblock]
  simp only [hfinal, prefixAgreement_full_iff_computes]
  exact not_congr (boundedComputes_iff_hasCircuit table)

theorem referenceStreamMerge_final_noCircuit_sound
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    {table : TruthTable n}
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hfinal : start + block.length = 2 ^ n)
    (hmerge : referenceStreamMerge priorCode blockLength start block =
      Result.noCircuit) :
    Not (HasCircuit n s table) :=
  (referenceStreamMerge_final_noCircuit_iff
    block priorCode prior table hdecode hwindow hprior hblock hfinal).mp hmerge

theorem referenceStreamMerge_final_noCircuit_complete
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    {table : TruthTable n}
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hfinal : start + block.length = 2 ^ n)
    (hnone : Not (HasCircuit n s table)) :
    referenceStreamMerge priorCode blockLength start block = Result.noCircuit :=
  (referenceStreamMerge_final_noCircuit_iff
    block priorCode prior table hdecode hwindow hprior hblock hfinal).mpr hnone

theorem referenceStreamMerge_final_found_sound
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode code : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    {table : TruthTable n}
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hfinal : start + block.length = 2 ^ n)
    (hmerge : referenceStreamMerge priorCode blockLength start block =
      Result.found code) :
    Exists fun candidate : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some candidate /\ Computes candidate.val table := by
  rcases referenceStreamMerge_found_prefixAgreement
    hdecode hwindow hprior hblock hmerge with
    ⟨candidate, hcandidateDecode, hagree⟩
  refine ⟨candidate, hcandidateDecode, ?_⟩
  apply (prefixAgreement_full_iff_computes candidate.val table).mp
  simpa only [hfinal] using hagree

theorem referenceStreamMerge_final_found_complete
    {n s blockLength start : Nat} {block : List Bool}
    {priorCode : DAGCodec.Code n s}
    {prior : DAGCodec.BoundedCircuit n s}
    {table : TruthTable n}
    (hdecode : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (hprior : PrefixAgreement prior.val table start)
    (hblock : block = tableBlock table start block.length)
    (hfinal : start + block.length = 2 ^ n)
    (hhas : HasCircuit n s table) :
    Exists fun code : DAGCodec.Code n s =>
      referenceStreamMerge priorCode blockLength start block =
        Result.found code :=
  (referenceStreamMerge_final_found_iff_hasCircuit
    block priorCode prior table hdecode hwindow hprior hblock hfinal).mpr hhas

end StreamMerge
end StreamingMagnification
end Frontier
end Pnp4
