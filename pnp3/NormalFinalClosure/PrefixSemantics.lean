import NormalFinalClosure.Semantics
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds Lean
private theorem zero_iff {m : Nat} (y : Fin m → Bool) (o w : Nat) (fit:o+w ≤ m) :
    allZeroSlice? y o w=some true ↔ ∀ j,∀ hj:j < w,y ⟨o+j,by omega⟩=false := by
  induction w generalizing o with
  | zero=>simp [allZeroSlice?]
  | succ w ih=>
    rw [allZeroSlice?,show readBit? y o=some (y ⟨o,by omega⟩) by rw [readBit?,dif_pos (by omega)]]
    cases hz:allZeroSlice? y (o+1) w with
    | none=>
      simp only [Option.bind_eq_bind,Option.bind_some,Option.bind_none,reduceCtorEq,false_iff]
      intro zeros
      have tail:= (ih (o+1) (by omega)).mpr (fun j hj=>by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using zeros (j+1) (by omega))
      rw [hz] at tail
      cases tail
    | some b=>
      simp only [Option.bind_eq_bind,Option.bind_some,Option.some.injEq,Bool.and_eq_true]
      constructor
      · rintro ⟨head,hb⟩
        subst b
        have tail:=(ih (o+1) (by omega)).mp hz
        intro j hj
        cases j with
        | zero=>simpa using head
        | succ j=>simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail j (by omega)
      · intro zeros
        have tail:=(ih (o+1) (by omega)).mpr (fun j hj=>by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using zeros (j+1) (by omega))
        exact ⟨by simpa using zeros 0 (by omega),Option.some.inj (hz.symm.trans tail)⟩
private theorem canonical_parse {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {S : Nat} (source : Fin S → Bool)
    (n cg i : Nat) (canon:gammaLen n=cg)
    (tag:readNatBE (padWord source (treeMCSPPrefixM codec n)) 0 tagLen=some treePrefixTag)
    (gamma:decodeGamma? (padWord source (treeMCSPPrefixM codec n)) tagLen=some (n,cg))
    (index:readNatBE (padWord source (treeMCSPPrefixM codec n))
      (tagLen+cg+Pnp3.Models.Partial.tableLen n) (idxWidth codec.witnessBits n)=some i)
    (hi:i ≤ codec.witnessBits n)
    (zero:allZeroSlice? (padWord source (treeMCSPPrefixM codec n))
      (tagLen+cg+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+i)
      (codec.witnessBits n-i)=some true) :
    ∃ input : PrefixInput (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n),
    parseTreeMCSPPrefixInput threshold codec (padWord source (treeMCSPPrefixM codec n))=some input ∧
    input.n=n ∧ input.i=i ∧
    (∀ j:Fin (Pnp3.Models.Partial.tableLen input.n),input.x j=padRead source (tagLen+cg+j.val)) ∧
    (∀ j:Fin input.i,input.p j=padRead source (tagLen+cg+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+j.val)) := by
  let y:=padWord source (treeMCSPPrefixM codec n)
  have layout:tagLen+cg+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+codec.witnessBits n=treeMCSPPrefixM codec n := by
    unfold treeMCSPPrefixM
    rw [canon]
  let a:=tagLen+cg
  let b:=a+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n
  let xx:Fin (Pnp3.Models.Partial.tableLen n) → Bool:=fun j=>y ⟨a+j.val,by dsimp only [a];omega⟩
  let pp:Fin i → Bool:=fun j=>y ⟨b+j.val,by dsimp only [b,a];omega⟩
  let zz:Fin (codec.witnessBits n-i) → Bool:=fun j=>y ⟨b+i+j.val,by dsimp only [b,a];omega⟩
  have hx:sliceBits? y a (Pnp3.Models.Partial.tableLen n)=some xx := by
    rw [sliceBits?,dif_pos (by dsimp only [a];omega)]
  have hp:sliceBits? y b i=some pp := by rw [sliceBits?,dif_pos (by dsimp only [b,a];omega)]
  have hz:sliceBits? y (b+i) (codec.witnessBits n-i)=some zz := by
    rw [sliceBits?,dif_pos (by dsimp only [b,a];omega)]
  let input:PrefixInput (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) (treeMCSPPrefixM codec n):=
    ⟨treePrefixTag,n,xx,i,hi,pp,codec.witnessBits n-i,zz⟩
  refine ⟨input,?_,rfl,rfl,?_,?_⟩
  · simp only [parseTreeMCSPPrefixInput,tag,Option.bind_eq_bind,Option.bind_some,gamma,↓reduceDIte]
    change (do
      let x←sliceBits? y a (Pnp3.Models.Partial.tableLen n)
      let v←readNatBE y (a+Pnp3.Models.Partial.tableLen n) (idxWidth codec.witnessBits n)
      if hv:v ≤ codec.witnessBits n then do
        let p←sliceBits? y b v
        let pad←sliceBits? y (b+v) (codec.witnessBits n-v)
        let padZero←allZeroSlice? y (b+v) (codec.witnessBits n-v)
        if padZero=true then some ⟨treePrefixTag,n,x,v,hv,p,codec.witnessBits n-v,pad⟩ else none
      else none)=some input
    have ir:readNatBE y (a+Pnp3.Models.Partial.tableLen n) (idxWidth codec.witnessBits n)=some i:=index
    have zr:allZeroSlice? y (b+i) (codec.witnessBits n-i)=some true:=zero
    simp only [hx,Option.bind_eq_bind,Option.bind_some,ir,dif_pos hi,hp,hz,zr,ite_true]
    rfl
  · intro j;rfl
  · intro j;rfl
private theorem parse_tests : ∀ {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {m : Nat} (y : Fin m → Bool)
    (input : PrefixInput (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m),
    parseTreeMCSPPrefixInput threshold codec y=some input →
    readNatBE y 0 tagLen=some treePrefixTag ∧ ∃ cg,
      decodeGamma? y tagLen=some (input.n,cg) ∧
      readNatBE y (tagLen+cg+Pnp3.Models.Partial.tableLen input.n) (idxWidth codec.witnessBits input.n)=some input.i ∧
      input.i ≤ codec.witnessBits input.n ∧
      allZeroSlice? y (tagLen+cg+Pnp3.Models.Partial.tableLen input.n+idxWidth codec.witnessBits input.n+input.i)
        (codec.witnessBits input.n-input.i)=some true := by
  run_tac do
    let owner:=`Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure
    let n:=Name.str (Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "Pnp4") "Frontier") "ContractExpansion") "parseTreeMCSPPrefixInput_value_tests"
    let e←Lean.getEnv
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact parser tests theorem"
    let some i:=e.getModuleIdxFor? n | throwError "Missing parser-test owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong parser-test owner"
    Lean.logInfo m!"normal-prefix-parser-test|{n}|{ci.type}"
    Lean.Elab.Tactic.closeMainGoal `parse_tests (Lean.mkConst n (ci.levelParams.map Lean.Level.param))
private theorem address {S : Nat} (k n z : Nat) (source : Fin S → Bool)
    (header:contentHeader? source=some (n,2*z+1)) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n=Cursor.Target.M k n z := by
  have canon:=contentHeader?_consumed_eq_gammaLen source header
  dsimp only [treeMCSPPrefixM,idxWidth]
  rw [←canon]
  change tagLen+(2*z+1)+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n=Cursor.Target.M k n z
  unfold tagLen Cursor.Target.M
  omega
private theorem accepted_prefix {S : Nat} (k n z : Nat) (source : Fin S → Bool)
    (header:contentHeader? source=some (n,2*z+1))
    (accepted:contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) source=true) :
    Target.PrefixOK source n z (Cursor.Target.W k n) := by
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  have indexWidth:idxWidth codec.witnessBits n=bitLength (Cursor.Target.W k n):=rfl
  obtain ⟨pr,hpr,agrees,_verify⟩:=(contentSemanticAccepts_eq_true_iff codec source).mp accepted
  unfold contentInput? at hpr
  rw [header] at hpr
  cases hp:parseTreeMCSPPrefixInput (thresholdPoly k) codec (padWord source (treeMCSPPrefixM codec n)) with
  | none=>simp only [hp,Option.map_none] at hpr;cases hpr
  | some input=>
    simp only [hp,Option.map_some] at hpr
    have same:=Option.some.inj hpr
    subst pr
    obtain ⟨tag,cg,gamma,index,hi,zero⟩:=parse_tests codec _ input hp
    have gn:=decodeGamma?_padWord_narrow source codec header
    have pairs:(input.n,cg)=(n,2*z+1):=Option.some.inj (gamma.symm.trans gn)
    rcases input with ⟨tag',q,x,i,bound,p,padBits,pad⟩
    dsimp only at pairs index hi zero agrees
    have qn:q=n:=congrArg Prod.fst pairs
    subst q
    have gz:cg=2*z+1:=congrArg Prod.snd pairs
    subst cg
    obtain ⟨canonInput,hcanon,hn,hi',_table,pref⟩:=canonical_parse codec source n (2*z+1) i
      (contentHeader?_consumed_eq_gammaLen source header).symm tag gn index hi zero
    have eqInput:canonInput=⟨tag',n,x,i,bound,p,padBits,pad⟩:=Option.some.inj (hcanon.symm.trans hp)
    subst canonInput
    dsimp only at pref
    have ambient:treeMCSPPrefixM codec n=Cursor.Target.M k n z:=address k n z source header
    have shift:tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n=9+2*z+2^n := by
      change 8+(2*z+1)+2^n=9+2*z+2^n
      omega
    refine ⟨i,?_,hi,?_,?_⟩
    · change readNatBE (padWord source (Cursor.Target.M k n z)) (9+2*z+2^n) (bitLength (Cursor.Target.W k n))=some i
      have ir:=index
      change readNatBE (padWord source (treeMCSPPrefixM codec n))
        (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n) (idxWidth codec.witnessBits n)=some i at ir
      rw [ambient,shift,indexWidth] at ir
      exact ir
    · intro j hj
      have value:=agrees ⟨j,hj⟩
      have cell:=pref ⟨j,hj⟩
      change padRead source (treeMCSPPrefixM codec n+j)=p ⟨j,hj⟩ at value
      rw [ambient] at value
      change p ⟨j,hj⟩=padRead source (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+bitLength (Cursor.Target.W k n)+j) at cell
      rw [shift] at cell
      exact cell.symm.trans value.symm
    · intro j lo hj
      have fit:tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+i+(codec.witnessBits n-i) ≤ treeMCSPPrefixM codec n := by
        have can:=contentHeader?_consumed_eq_gammaLen source header
        change tagLen+(2*z+1)+2^n+bitLength (Cursor.Target.W k n)+i+(Cursor.Target.W k n-i) ≤
          tagLen+gammaLen n+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
        rw [←can]
        change i ≤ Cursor.Target.W k n at hi
        omega
      have zeros:=(zero_iff _ _ _ fit).mp zero
      have atJ:=zeros (j-i) (by change j-i < Cursor.Target.W k n-i;omega)
      change padRead source (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+bitLength (Cursor.Target.W k n)+i+(j-i))=false at atJ
      rw [shift] at atJ
      simpa only [show 9+2*z+2^n+bitLength (Cursor.Target.W k n)+i+(j-i)=9+2*z+2^n+bitLength (Cursor.Target.W k n)+j by omega] using atJ
private theorem logical_tag_read {S : Nat} (source : Fin S → Bool) (T : Nat) (fit:8 ≤ T)
    (tag:FixedContentTagGate.tagMatches source=true) :
    readNatBE (padWord source T) 0 tagLen=some treePrefixTag := by
  obtain ⟨_e0,_e1,_e2,_e3,_e4,_e5,_e6,_e7,contract,length⟩:=FixedContentTagGate.tag_contract source
  have bits:=contract.mp tag
  have room:=length tag
  have equal:=readNatBE_eq_of_readBit_eq (padWord source T) FixedContentTagGate.expectedTagBit 0 0 8 (by
    intro j hj
    have physical:=bits ⟨j,hj⟩
    have js:j < S:=by omega
    have jt:j < T:=by omega
    simpa only [Nat.zero_add,FixedContentTagGate.physicalSymbol,dif_pos js,readBit?,dif_pos jt,dif_pos hj,padWord,padRead] using physical)
  change readNatBE (padWord source T) 0 8=some 178
  rw [equal]
  decide
/-- Exact ORIGINAL-rho logical specification for a normal all-row success.
It retains every byte of the internal witness, including ignored decoder tail.
This proposition does not assert physical execution of the new guard. -/
theorem rows_prefix_rho (k a m n z : Nat) (x : Bitstring a) (w : Bitstring m)
    (length:m=a+1) (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (circuit:Pnp3.Models.Circuit n) (tail:List Bool)
    (decoded:decodeCircuitFull n (bitLength n) (SerializedBody.window (Fin.append x w) (Cursor.Target.M k n z) (Cursor.Target.W k n))=some (circuit,tail))
    (cap:circuit.size ≤ n^k+k)
    (table:∀ j,j < 2^n → padRead (Fin.append x w) (9+2*z+j)=circuit.eval (Pnp3.Core.vecOfNat n j)) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      Target.PrefixOK (Fin.append x w) n z (Cursor.Target.W k n) := by
  have fitM:8 ≤ Cursor.Target.M k n z := by
    change 8 ≤ 9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
    exact (show 8 ≤ 9 by decide).trans ((Nat.le_add_right 9 (2*z)).trans
      ((Nat.le_add_right (9+2*z) (2^n)).trans ((Nat.le_add_right (9+2*z+2^n) (bitLength (Cursor.Target.W k n))).trans
        (Nat.le_add_right _ (Cursor.Target.W k n)))))
  have tagRead:=logical_tag_read (Fin.append x w) (Cursor.Target.M k n z) fitM tag
  rw [rho_append k a m x w length]
  constructor
  · exact accepted_prefix k n z (Fin.append x w) header
  · rintro ⟨i,index,hi,active,inactive⟩
    let source:=Fin.append x w
    let codec:=treeCircuitWitnessCodec (thresholdPoly k)
    have indexWidth:idxWidth codec.witnessBits n=bitLength (Cursor.Target.W k n):=rfl
    have ambient:treeMCSPPrefixM codec n=Cursor.Target.M k n z:=address k n z source header
    have can:=contentHeader?_consumed_eq_gammaLen source header
    have narrow:=decodeGamma?_padWord_narrow source codec header
    have shift:tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n=9+2*z+2^n := by
      change 8+(2*z+1)+2^n=9+2*z+2^n
      omega
    have tag':readNatBE (padWord source (treeMCSPPrefixM codec n)) 0 tagLen=some treePrefixTag := by
      rw [ambient];exact tagRead
    have index':readNatBE (padWord source (treeMCSPPrefixM codec n))
      (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n) (idxWidth codec.witnessBits n)=some i := by
      rw [ambient,shift,indexWidth]
      change readNatBE (padWord (Fin.append x w) (9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n))
        (9+2*z+2^n) (bitLength (Cursor.Target.W k n))=some i
      exact index
    have fit:tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+i+(codec.witnessBits n-i) ≤ treeMCSPPrefixM codec n := by
      change tagLen+(2*z+1)+2^n+bitLength (Cursor.Target.W k n)+i+(Cursor.Target.W k n-i) ≤
        tagLen+gammaLen n+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
      rw [←can]
      omega
    have zero:allZeroSlice? (padWord source (treeMCSPPrefixM codec n))
        (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n+i)
        (codec.witnessBits n-i)=some true := by
      apply (zero_iff _ _ _ fit).mpr
      intro j hj
      change padRead source (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+bitLength (Cursor.Target.W k n)+i+j)=false
      rw [shift]
      have eq:9+2*z+2^n+bitLength (Cursor.Target.W k n)+i+j=9+2*z+2^n+bitLength (Cursor.Target.W k n)+(i+j):=by omega
      rw [eq]
      exact inactive (i+j) (by omega) (by change j < Cursor.Target.W k n-i at hj;omega)
    obtain ⟨input,parsed,hn,hi',fieldTable,fieldPrefix⟩:=canonical_parse codec source n (2*z+1) i can.symm tag' narrow index' hi zero
    cases input with
    | mk tag' q xx v bound pp padBits pad=>
      dsimp only at hn hi' fieldTable fieldPrefix parsed
      subst q
      subst v
      have tableEq:xx=(fun j=>padRead source (9+2*z+j.val)) := by
        funext j
        have eq:=fieldTable j
        change xx j=padRead source (tagLen+(2*z+1)+j.val) at eq
        rw [show tagLen+(2*z+1)=9+2*z by unfold tagLen;omega] at eq
        exact eq
      apply (contentSemanticAccepts_eq_true_iff codec source).mpr
      refine ⟨⟨n,⟨tag',n,xx,i,bound,pp,padBits,pad⟩⟩,?_,?_,?_⟩
      · unfold contentInput?
        rw [header]
        dsimp only
        rw [parsed]
        rfl
      · change ∀ j:Fin i,padRead source (treeMCSPPrefixM codec n+j.val)=pp j
        intro j
        simp only [ambient]
        have fp:=fieldPrefix j
        change pp j=padRead source (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n+bitLength (Cursor.Target.W k n)+j.val) at fp
        rw [shift] at fp
        exact (active j.val j.isLt).symm.trans fp.symm
      · change codec.verifies n xx (contentWitness codec source n)
        rw [tableEq]
        apply (codec_rows (thresholdPoly k) source (9+2*z) n (contentWitness codec source n)).mpr
        refine ⟨circuit,tail,?_,cap,table⟩
        have bits:List.ofFn (contentWitness codec source n)=SerializedBody.window source (Cursor.Target.M k n z) (Cursor.Target.W k n) := by
          change List.ofFn (fun j:Fin (Cursor.Target.W k n)=>padRead source (treeMCSPPrefixM codec n+j.val))=List.ofFn (fun j:Fin (Cursor.Target.W k n)=>padRead source (Cursor.Target.M k n z+j.val))
          rw [ambient]
        rw [bits]
        exact decoded
/-- Independently complete logical proposition mirror, not an execution claim. -/
theorem rows_prefix_rho_mirror (k a m n z : Nat) (x : Bitstring a) (w : Bitstring m)
    (length:m=a+1) (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (circuit:Pnp3.Models.Circuit n) (tail:List Bool)
    (decoded:decodeCircuitFull n (bitLength n) (SerializedBody.window (Fin.append x w) (Cursor.Target.M k n z) (Cursor.Target.W k n))=some (circuit,tail))
    (cap:circuit.size ≤ n^k+k)
    (table:∀ j,j < 2^n → padRead (Fin.append x w) (9+2*z+j)=circuit.eval (Pnp3.Core.vecOfNat n j)) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      ∃ i,readNatBE (padWord (Fin.append x w) (9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n))
        (9+2*z+2^n) (bitLength (Cursor.Target.W k n))=some i ∧ i ≤ Cursor.Target.W k n ∧
        (∀ j,j < i → padRead (Fin.append x w) (9+2*z+2^n+bitLength (Cursor.Target.W k n)+j)=padRead (Fin.append x w) (9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n+j)) ∧
        (∀ j,i ≤ j → j < Cursor.Target.W k n → padRead (Fin.append x w) (9+2*z+2^n+bitLength (Cursor.Target.W k n)+j)=false) :=
  rows_prefix_rho k a m n z x w length header tag circuit tail decoded cap table
#print axioms rows_prefix_rho
#print axioms rows_prefix_rho_mirror
end NormalFinalClosure
