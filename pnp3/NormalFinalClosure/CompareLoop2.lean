import NormalFinalClosure.CompareNative2
import NormalFinalClosure.PrefixSemantics2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["compareState"]),
    (`NormalFinalClosure.PrefixDigit2,`NormalFinalClosure,["cleanup_at"]),
    (`NormalFinalClosure.PrefixSemantics2,`NormalFinalClosure,["mode_one_iff","encodeBits","windowBits"]),
    (`NormalFinalClosure.CompareNative2,`NormalFinalClosure,["modeValue","compare_consume","compare_record","compare_end"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing complete actual comparison recurrence API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing actual comparison recurrence owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong actual comparison recurrence owner"
      logInfo m!"complete-actual-comparison-recurrence-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing comparison recurrence Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing comparison recurrence Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong comparison recurrence Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private structure CompareRep (records : List Nat) (seen : Nat) (bits : List Bool) (inactive : Nat) : Prop where
  length : records.length=seen+bits.length+inactive
  processed : ∀ j,j < seen → records[j]! = 3
  active : ∀ j,j < bits.length → records[seen+j]! = if bits[j]! then 2 else 1
  padding : ∀ j,j < inactive → records[seen+bits.length+j]! = 0
private theorem CompareRep.past {records seen bits inactive} (rep:CompareRep records seen bits inactive) :
    ∀ j,j < seen → j < records.length ∧ records[j]! = 3 := by
  intro j hj
  exact ⟨by have h:=rep.length;omega,rep.processed j hj⟩
private theorem CompareRep.advance {records seen bit bits inactive}
    (rep:CompareRep records seen (bit::bits) inactive) :
    CompareRep (records.set seen 3) (seen+1) bits inactive := by
  have len:=rep.length
  simp only [List.length_cons] at len
  constructor
  · simp only [List.length_set];omega
  · intro j hj
    by_cases eq:j=seen
    · subst j
      simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_self (by omega : seen < records.length),Option.getD_some]
    · simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (by omega : seen≠j)]
      simpa only [List.getElem!_eq_getElem?_getD] using rep.processed j (by omega)
  · intro j hj
    simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (by omega : seen≠seen+1+j)]
    have h:=rep.active (j+1) (by simp only [List.length_cons];omega)
    simpa only [show seen+(j+1)=seen+1+j by omega,List.getElem!_eq_getElem?_getD,List.getElem?_cons_succ] using h
  · intro j hj
    simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (by omega : seen≠seen+1+bits.length+j)]
    have h:=rep.padding j hj
    simpa only [List.length_cons,show seen+(bits.length+1)+j=seen+1+bits.length+j by omega,List.getElem!_eq_getElem?_getD] using h
private theorem initial_records (bits : List Bool) (inactive : Nat) :
    CompareRep (encodeBits bits++List.replicate inactive 0) 0 bits inactive := by
  constructor
  · simp only [encodeBits,List.length_append,List.length_map,List.length_replicate,Nat.zero_add]
  · intro j hj;omega
  · intro j hj
    simp only [Nat.zero_add]
    have hjm:j < (encodeBits bits).length:=by simpa only [encodeBits,List.length_map] using hj
    rw [List.getElem!_eq_getElem?_getD,List.getElem?_append_left hjm]
    dsimp only [encodeBits]
    rw [List.getElem?_map,List.getElem?_eq_getElem hj]
    simp only [Option.map_some,Option.getD_some]
    rw [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
  · intro j hj
    simp only [Nat.zero_add]
    have right:(encodeBits bits).length ≤ bits.length+j:=by simp only [encodeBits,List.length_map];omega
    rw [List.getElem!_eq_getElem?_getD,List.getElem?_append_right right]
    rw [show (encodeBits bits).length=bits.length by simp only [encodeBits,List.length_map]]
    simp only [Nat.add_sub_cancel_left,List.getElem?_replicate,if_pos hj,Option.getD_some]
private def bitsAgree {S : Nat} (source : Fin S → Bool) (offset : Nat) : List Bool → Prop
  | []=>True
  | bit::bits=>bit=padRead source offset ∧ bitsAgree source (offset+1) bits
private theorem modeValue_original {S : Nat} (source : Fin S → Bool) (offset : Nat) :
    modeValue (sourceMode source (min offset S))=padRead source offset := by
  by_cases one:(sourceMode source (min offset S)).val=1
  · rw [modeValue,decide_eq_true one,(mode_one_iff source offset).mp one]
  · have bit:padRead source offset=false:=by
      cases b:padRead source offset
      · rfl
      · exact False.elim (one ((mode_one_iff source offset).mpr b))
    rw [modeValue,decide_eq_false one,bit]
/-- The ENTIRE actual original-window comparison, every record and virtual
source suffix, including all processed scans, source shuttles and final cleanup
ONCE. A nonmatching byte reaches literal reject; all matching bytes reach
literal accept/H with the SAME complete original cleared image. -/
private theorem compare_loop (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (bits : List Bool) (offset a seen inactive : Nat)
    (records : List Nat) (rep:CompareRep records seen bits inactive)
    (capacity:records.length ≤ r) (lo:S-r ≤ offset) :
    ∃ (t : Nat) (answer : Bool),t ≤ 2048*(bits.length+1)*(D F r n 13+1) ∧
      (answer=true ↔ bitsAgree source offset bits) ∧
      Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (compareState k (sourceMode source (min offset S))) (D F r n 0)
          (repImage T F r n S (min offset S) a 0 0 0 records))
        (node (if answer then (machine2 k).accept else (machine2 k).reject) (S+z+2+n+1)
          (repImage T F r n S S 0 0 0 0 [])) := by
  induction bits generalizing offset seen records with
  | nil=>
    have len:=rep.length
    simp only [List.length_nil,Nat.add_zero] at len
    have finished:seen=records.length ∨ seen < records.length ∧ records[seen]! = 0:=by
      by_cases zero:inactive=0
      · left;omega
      · right
        refine ⟨by omega,?_⟩
        simpa only [List.length_nil,Nat.add_zero] using rep.padding 0 (by omega)
    obtain ⟨aTime,aPrice,stop⟩:=compare_end k fr (min offset S) a records seen capacity rep.past finished
    obtain ⟨bTime,bPrice,cleanup⟩:=cleanup_at k true fr (min offset S) a 0 0 0 records (by omega)
    refine ⟨aTime+bTime,true,?_,by simp only [bitsAgree],stop.append cleanup⟩
    simp only [List.length_nil]
    omega
  | cons bit bits ih=>
    have len:=rep.length
    simp only [List.length_cons] at len
    have code:records[seen]! = if bit then 2 else 1:=by simpa only [Nat.add_zero,List.getElem!_cons_zero] using rep.active 0 (by simp)
    obtain ⟨aTime,aPrice,headPath⟩:=compare_record k fr (min offset S) a records seen capacity rep.past (by omega) bit code
    rw [modeValue_original] at headPath
    by_cases equal:bit=padRead source offset
    · rw [if_pos equal] at headPath
      obtain ⟨sTime,sPrice,consume⟩:=compare_consume k fr (min offset S) a (records.set seen 3) (by omega) (by omega)
      rw [show min (min offset S+1) S=min (offset+1) S by omega] at consume
      obtain ⟨bTime,answer,bPrice,correct,tail⟩:=ih (offset+1) (seen+1) (records.set seen 3) rep.advance
        (by simpa only [List.length_set] using capacity) (by omega)
      refine ⟨aTime+(sTime+bTime),answer,?_,?_,headPath.append (consume.append tail)⟩
      · simp only [List.length_cons]
        nlinarith only [aPrice,sPrice,bPrice]
      · simpa only [bitsAgree,equal,true_and] using correct
    · rw [if_neg equal] at headPath
      obtain ⟨bTime,bPrice,cleanup⟩:=cleanup_at k false fr (min offset S) a 0 0 0 records (by omega)
      refine ⟨aTime+bTime,false,?_,?_,headPath.append cleanup⟩
      · simp only [List.length_cons]
        nlinarith only [aPrice,bPrice]
      · constructor
        · intro h;cases h
        · intro h
          exact False.elim (equal h.1)
end NormalFinalClosure
