import VirtualFinalClosure.Source
namespace VirtualFinalClosure.GuardMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds
set_option autoImplicit false
/-- Source-side reader facts consumed by the physical BE guard. These definitions
are not transition-table operands and do not supply a parser oracle. -/
private theorem allZero_iff {N : Nat} (y : PrefixBitVec N) (offset width : Nat)
    (range : offset+width ≤ N) :
    allZeroSlice? y offset width=some true ↔
      ∀ j : Fin width,y ⟨offset+j.val,by omega⟩=false := by
  induction width generalizing offset with
  | zero => simp [allZeroSlice?]
  | succ w ih =>
    have first : offset < N := by omega
    have rest : offset+1+w ≤ N := by omega
    rw [allZeroSlice?]
    dsimp only [readBit?]
    rw [dif_pos first]
    dsimp only [Bind.bind,Option.bind]
    cases bit : y ⟨offset,first⟩
    · change (Option.bind (allZeroSlice? y (offset+1) w) (fun v=>some v)=some true) ↔ _
      have identity (o : Option Bool) : Option.bind o (fun v=>some v)=o := by cases o <;> rfl
      rw [identity,ih (offset+1) rest]
      constructor
      · intro tail j
        by_cases zero : j.val=0
        · have eq : (⟨offset+j.val,by omega⟩ : Fin N)=⟨offset,first⟩ := Fin.ext (by change offset+j.val=offset;omega)
          rw [eq,bit]
        · simpa only [show offset+1+(j.val-1)=offset+j.val by omega] using
            tail ⟨j.val-1,by omega⟩
      · intro bits j
        simpa only [show offset+(j.val+1)=offset+1+j.val by omega] using
          bits ⟨j.val+1,by omega⟩
    · change (Option.bind (allZeroSlice? y (offset+1) w) (fun _=>some false)=some true) ↔ _
      constructor
      · intro impossible
        cases h : allZeroSlice? y (offset+1) w <;> simp [h] at impossible
      · intro bits
        have contradiction:=bits ⟨0,by omega⟩
        simp only [Nat.add_zero,bit,Bool.true_eq_false] at contradiction
private theorem readNatBE_zero {N : Nat} (y : PrefixBitVec N) (offset width : Nat)
    (range : offset+width ≤ N)
    (zero : ∀ j : Fin width,y ⟨offset+j.val,by omega⟩=false) :
    readNatBE y offset width=some 0 := by
  induction width generalizing offset with
  | zero => rfl
  | succ w ih =>
    have first : offset < N := by omega
    have bit : y ⟨offset,first⟩=false := by simpa using zero ⟨0,by omega⟩
    have tail : ∀ j : Fin w,y ⟨offset+1+j.val,by omega⟩=false := by
      intro j
      simpa only [show offset+(j.val+1)=offset+1+j.val by omega] using zero ⟨j.val+1,by omega⟩
    rw [readNatBE]
    dsimp only [readBit?]
    rw [dif_pos first,bit]
    dsimp only [Bind.bind,Option.bind]
    rw [ih (offset+1) (by omega) tail]
    rfl
private def parsedFrame (k N n consumed index : Nat) (y : PrefixBitVec N)
    (fits : index ≤ (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n) :
    PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
      (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n) where
  tag:=treePrefixTag
  n:=n
  x:=fun j=>padRead y (tagLen+consumed+j.val)
  i:=index
  prefixLength_le:=fits
  p:=fun j=>padRead y (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
    idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+j.val)
  padBits:=(treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n-index
  pad:=fun j=>padRead y (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
    idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+index+j.val)
private theorem parser_of_guard {N n consumed index : Nat} (k : Nat) (y : PrefixBitVec N)
    (header : contentHeader? y=some (n,consumed))
    (tag : readNatBE (padWord y (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      0 tagLen=some treePrefixTag)
    (indexRead : readNatBE (padWord y (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      (tagLen+consumed+Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)=some index)
    (fits : index ≤ (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)
    (zero : ∀ j : Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n),
      padRead y (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
        idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+j.val)=false) :
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) y=
      some ⟨n,parsedFrame k N n consumed index y fits⟩ ∧
    (parsedFrame k N n consumed index y fits).prefixAgrees (fun _=>false) := by
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  let m:=treeMCSPPrefixM codec n
  let yy:=padWord y m
  change index ≤ codec.witnessBits n at fits
  change ∀ j : Fin (codec.witnessBits n),padRead y
    (tagLen+consumed+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+j.val)=false at zero
  let start:=tagLen+consumed
  let atIndex:=start+Pnp3.Models.Partial.tableLen n
  let atPrefix:=atIndex+idxWidth codec.witnessBits n
  have fits' : index ≤ codec.witnessBits n := fits
  have canonical : consumed=gammaLen n := contentHeader?_consumed_eq_gammaLen y header
  have layout : atPrefix+codec.witnessBits n=m := by
    dsimp only [atPrefix,atIndex,start,m,treeMCSPPrefixM]
    rw [canonical]
  have gamma : decodeGamma? yy tagLen=some (n,consumed) :=
    decodeGamma?_padWord_narrow y codec header
  have sx : sliceBits? yy start (Pnp3.Models.Partial.tableLen n)=
      some (fun j=>padRead y (start+j.val)) := by
    dsimp only [sliceBits?]
    rw [dif_pos (by omega)]
    rfl
  have sp : sliceBits? yy atPrefix index=some (fun j=>padRead y (atPrefix+j.val)) := by
    dsimp only [sliceBits?]
    rw [dif_pos (by omega)]
    rfl
  have sd : sliceBits? yy (atPrefix+index) (codec.witnessBits n-index)=
      some (fun j=>padRead y (atPrefix+index+j.val)) := by
    dsimp only [sliceBits?]
    rw [dif_pos (by omega)]
    rfl
  have zeros : allZeroSlice? yy (atPrefix+index) (codec.witnessBits n-index)=some true := by
    apply (allZero_iff yy _ _ (by omega)).2
    intro j
    change padRead y (atPrefix+index+j.val)=false
    simpa only [atPrefix,atIndex,start,Nat.add_assoc] using zero ⟨index+j.val,by omega⟩
  constructor
  · dsimp only [contentInput?]
    rw [header]
    dsimp only
    change (parseTreeMCSPPrefixInput (thresholdPoly k) codec yy).map _=_
    unfold parseTreeMCSPPrefixInput
    rw [tag]
    dsimp only [Bind.bind,Option.bind]
    rw [dif_pos rfl,gamma]
    dsimp only [Bind.bind,Option.bind]
    rw [dif_pos rfl,sx,indexRead]
    dsimp only [Bind.bind,Option.bind]
    rw [dif_pos fits,sp,sd,zeros]
    rfl
  · change ∀ j : Fin index,false=padRead y (tagLen+consumed+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+j.val)
    intro j
    exact (zero ⟨j.val,by omega⟩).symm
/-- The actual authoritative parser success is DERIVED from the native guard's
value tests. This is source semantics, not a runtime execution theorem. -/
theorem checked_guard_acceptance {a m n consumed index : Nat} (k : Nat)
    (x : Bitstring a) (w : Bitstring m) (canonical : m=a+1) (positive : 0<n)
    (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n)) 0 tagLen=some treePrefixTag)
    (indexRead : readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      (tagLen+consumed+Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)=some index)
    (fits : index ≤ (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)
    (zero : ∀ j : Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n),
      padRead (Fin.append x w) (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
        idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+j.val)=false)
    (virtual : a+m ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      ∀ j : Fin (2^n),padRead (Fin.append x w) (tagLen+consumed+j.val)=Nat.testBit j.val 0 := by
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  have virtual' : a+m ≤ treeMCSPPrefixM codec n := virtual
  let input:=parsedFrame k (a+m) n consumed index (Fin.append x w) fits
  obtain ⟨parsed,agree⟩:=parser_of_guard k (Fin.append x w) header tag indexRead fits zero
  have blank : contentWitness codec (Fin.append x w) n=(fun _=>false) := by
    funext j
    exact padRead_ge (Fin.append x w) (by omega)
  have iff:=VirtualFinalClosure.virtual_relation k x w (pr:=⟨n,input⟩)
    canonical positive parsed blank
  change (_ ↔ input.prefixAgrees (fun _=>false) ∧ _) at iff
  rw [iff]
  change (input.prefixAgrees (fun _=>false) ∧ _) ↔ _
  have a0 : input.prefixAgrees (fun _=>false) := agree
  simp only [a0,true_and]
  rfl
set_option autoImplicit false in
theorem check_checked_guard_acceptance :
    ∀ {a m n consumed index : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m),
    m=a+1 → 0<n → contentHeader? (Fin.append x w)=some (n,consumed) →
    readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n)) 0 tagLen=some treePrefixTag →
    readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      (tagLen+consumed+Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)=some index →
    index ≤ (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n →
    (∀ j : Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n),
      padRead (Fin.append x w) (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
        idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+j.val)=false) →
    a+m ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n →
    (PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      ∀ j : Fin (2^n),padRead (Fin.append x w) (tagLen+consumed+j.val)=Nat.testBit j.val 0) := by
  intro a m n consumed index k x w canonical positive header tag indexRead fits zero virtual
  exact checked_guard_acceptance k x w canonical positive header tag indexRead fits zero virtual
#print axioms checked_guard_acceptance
#print axioms check_checked_guard_acceptance
end VirtualFinalClosure.GuardMeaning
