import VirtualFinalClosure.ParsedPrefixFields
namespace VirtualFinalClosure.GuardNecessity
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ParsedPrefixFields","VirtualFinalClosure.ParsedPrefixFields","parsed_prefix_fields","prefixFields",1),
      ("VirtualFinalClosure.GuardMeaning","VirtualFinalClosure.GuardMeaning","allZero_iff","allZero",1) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
private theorem semantic {a m : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
  have h:=accepted
  unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
  split at h
  · rename_i shape
    cases shape
    simpa only [AcceptedBody.concat_eq_append] using h
  · contradiction
/-- Necessity is proved from the ORIGINAL relation and authoritative parser,
not assumed by the raw machine. Hence neither a nonzero legal BE index nor
W>r permits a reject. Prefix/padding failure or index>W contradicts acceptance. -/
private theorem necessary {a m n consumed index : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (indexRead : readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      (tagLen+consumed+Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)=some index)
    (virtual : a+m ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    0<n ∧ index ≤ (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n ∧
      ∀ j : Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n),
        padRead (Fin.append x w) (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
          idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+j.val)=false := by
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  let word:=Fin.append x w
  let M:=treeMCSPPrefixM codec n
  let yy:=padWord word M
  have sem:=semantic k x w accepted
  change contentSemanticAccepts codec word=true at sem
  cases parsed : parseTreeMCSPPrefixInput (thresholdPoly k) codec yy with
  | none=>
    have no : contentInput? codec word=none:=by
      dsimp only [contentInput?];rw [header];dsimp only;rw [parsed];rfl
    dsimp only [contentSemanticAccepts] at sem
    rw [no] at sem
    cases sem
  | some input=>
    have yes : contentInput? codec word=some ⟨n,input⟩:=by
      dsimp only [contentInput?];rw [header];dsimp only;rw [parsed];rfl
    dsimp only [contentSemanticAccepts] at sem
    rw [yes] at sem
    dsimp only at sem
    rw [Bool.and_eq_true] at sem
    obtain ⟨agreeBool,verifyBool⟩:=sem
    have agree:= (prefixAgreesBool_eq_true_iff input (contentWitness codec word input.n)).mp agreeBool
    have verifies:= (verifiesBool_eq_true_iff codec input.n input.x (contentWitness codec word input.n)).mp verifyBool
    obtain ⟨cg,gamma,readI,sliceP,padZero⟩:=prefixFields codec yy input parsed
    have narrow:=decodeGamma?_padWord_narrow word codec header
    have pair : (input.n,cg)=(n,consumed):=Option.some.inj (gamma.symm.trans narrow)
    have hn : input.n=n:=congrArg Prod.fst pair
    have hc : cg=consumed:=congrArg Prod.snd pair
    have readI' : readNatBE yy (tagLen+consumed+Pnp3.Models.Partial.tableLen n)
        (idxWidth codec.witnessBits n)=some input.i:=by simpa only [hn,hc] using readI
    have indexEq : input.i=index:=Option.some.inj (readI'.symm.trans indexRead)
    have fits : input.i ≤ codec.witnessBits n:=by simpa only [hn] using input.prefixLength_le
    let start:=tagLen+consumed+Pnp3.Models.Partial.tableLen n+idxWidth codec.witnessBits n
    have layout : start+codec.witnessBits n=M:=by
      dsimp only [start,M,treeMCSPPrefixM]
      rw [contentHeader?_consumed_eq_gammaLen word header]
    have blank : contentWitness codec word input.n=(fun _=>false):=by
      funext j
      dsimp only [contentWitness]
      have virtualN : a+m ≤ treeMCSPPrefixM codec input.n:=by simpa only [hn] using virtual
      exact padRead_ge word (virtualN.trans (Nat.le_add_right _ j.val))
    have positive : 0<n:=by
      by_contra no
      have zero : n=0:=by omega
      obtain ⟨c,decoded,_size,_computes⟩:=verifies
      have empty : codec.decode input.n (fun _=>false)=none:=by
        rw [hn,zero]
        exact treeCircuitWitnessCodec_decode_blank_zero k
      rw [blank,empty] at decoded
      cases decoded
    rw [blank] at agree
    have preZero : ∀ j : Fin input.i,input.p j=false:=by
      intro j
      exact (agree j).symm
    have sp : sliceBits? yy start input.i=some input.p:=by simpa only [hn,hc,start] using sliceP
    have zp : allZeroSlice? yy (start+input.i) (codec.witnessBits n-input.i)=some true:=by
      simpa only [hn,hc,start] using padZero
    have zeros:= (allZero yy (start+input.i) (codec.witnessBits n-input.i) (by omega)).mp zp
    have active : ∀ j : Fin input.i,padRead word (start+j.val)=false:=by
      dsimp only [sliceBits?] at sp
      split at sp
      · have equal:=Option.some.inj sp
        intro j
        exact (congrFun equal j).trans (preZero j)
      · cases sp
    refine ⟨positive,by simpa only [indexEq] using fits,?_⟩
    intro j
    have jfit : j.val < codec.witnessBits n:=j.isLt
    by_cases before : j.val < input.i
    · exact active ⟨j.val,before⟩
    · have pad:=zeros ⟨j.val-input.i,by omega⟩
      change padRead word (start+input.i+(j.val-input.i))=false at pad
      simpa only [show start+input.i+(j.val-input.i)=start+j.val by omega] using pad
#print axioms semantic
#print axioms necessary
end VirtualFinalClosure.GuardNecessity
