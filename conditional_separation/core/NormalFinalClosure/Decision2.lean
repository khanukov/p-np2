import NormalFinalClosure.NativeContract2
import NormalFinalClosure.IndexRun2
import NormalFinalClosure.PrefixRun2
import NormalFinalClosure.CompareSemantics2
import NormalFinalClosure.NativeCleanup2
import NormalFinalClosure.Horner2
import NormalFinalClosure.AdvanceCertificates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.NativeContract2,`NormalFinalClosure,["NativeGuard","node"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","repImage","PrefixAt","GuardFrame.windowRoom"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Path"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2","ns2"]),
    (`NormalFinalClosure.IndexRun2,`NormalFinalClosure,["index_run"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["beDone"]),
    (`NormalFinalClosure.PrefixRun2,`NormalFinalClosure,["prefix_run"]),
    (`NormalFinalClosure.PrefixLoop2,`NormalFinalClosure,["prefixGood","prefixGood_decidable"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["compareState"]),
    (`NormalFinalClosure.PrefixSemantics2,`NormalFinalClosure,["prefixGood_original","windowBits","windowBits_length","encodeBits"]),
    (`NormalFinalClosure.CompareLoop2,`NormalFinalClosure,["compare_loop","initial_records"]),
    (`NormalFinalClosure.CompareSemantics2,`NormalFinalClosure,["matches_window_original"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact connected decision API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing connected decision owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong connected decision owner"
      logInfo m!"full-native-decision-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private theorem phase_price (r P t u : Nat)
    (preBound:t ≤ 32768*(r+1)^2*(P+1))
    (tail:u ≤ 524288*(r+1)^4*(P+1)^2) :
    t+u+1 ≤ 1048576*(r+1)^4*(P+1)^2 := by
  have rp:(r+1)^2 ≤ (r+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have pp:P+1 ≤ (P+1)^2:=by nlinarith
  have mono:=Nat.mul_le_mul rp pp
  have before:t ≤ 32768*((r+1)^4*(P+1)^2):=by
    have p:=Nat.mul_le_mul_left 32768 mono
    nlinarith only [preBound,p]
  have unit:1 ≤ (r+1)^4*(P+1)^2:=Nat.succ_le_of_lt (by positivity)
  nlinarith only [before,tail,unit]
private theorem second_price (r P a b : Nat)
    (ap:a ≤ 8192*(r+1)*(P+1)) (bp:b ≤ 262144*(r+1)^4*(P+1)^2) :
    a+b ≤ 524288*(r+1)^4*(P+1)^2 := by
  have rp:r+1 ≤ (r+1)^4:=by
    have square:r+1 ≤ (r+1)^2:=by nlinarith
    have fourth:(r+1)^2 ≤ (r+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
    exact square.trans fourth
  have pp:P+1 ≤ (P+1)^2:=by nlinarith
  have mono:=Nat.mul_le_mul rp pp
  have abs:a ≤ 8192*((r+1)^4*(P+1)^2):=by
    have p:=Nat.mul_le_mul_left 8192 mono
    nlinarith only [ap,p]
  nlinarith only [abs,bp]
/-- SAME full frozen NativeGuard. The actual prefixPath is composed here, so the
remaining ordinary RED is exactly the native BE/prefixPath/compare recurrence and
its existing cleanup, not another assumed initializer/row observer. -/
private theorem native_guard (k : Nat) : NativeGuard k := by
  intro S z n F r W source T frame
  obtain ⟨t,i,price,read,prefixPath⟩:=index_run k frame
  by_cases indexOK:i ≤ W
  · rw [if_pos indexOK] at prefixPath
    obtain ⟨q,qp,prePath⟩:=prefix_run k frame i indexOK
    let offset:=S-r+Pnp4.Frontier.ContractExpansion.bitLength W
    by_cases padOK:prefixGood source (min offset S) W i
    · rw [if_pos padOK] at prePath
      suffices remaining : ∃ (u : Nat) (answer : Bool),
          u ≤ 262144*(r+1)^4*(D F r n 13+1)^2 ∧
          (answer=true ↔ PrefixAt source (S-r) W) ∧
          Path (machine2 k) (Safe2 k) (D F r n 13) u
            (node (compareState k (sourceMode source (min (offset+W) S))) (D F r n 0)
              (repImage T F r n S (min (offset+W) S) (W-i) 0 0 0
                (encodeBits (windowBits source offset i)++List.replicate (W-i) 0)))
            (node (if answer then (machine2 k).accept else (machine2 k).reject)
              (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) by
        obtain ⟨u,answer,bound,correct,run⟩:=remaining
        exact ⟨t+(q+u),answer,phase_price r (D F r n 13) t (q+u) price
          (second_price r (D F r n 13) q u qp bound),correct,prefixPath.append (prePath.append run)⟩
      let bits:=windowBits source offset i
      let records:=encodeBits bits++List.replicate (W-i) 0
      have wr:=windowRoom frame
      obtain ⟨u,answer,up,correct,path⟩:=compare_loop k frame bits (offset+W) (W-i) 0 (W-i) records
        (initial_records bits (W-i)) (by
          dsimp only [records,bits]
          simp only [List.length_append,encodeBits,List.length_map,List.length_replicate,windowBits_length]
          omega) (by omega)
      refine ⟨u,answer,?_,?_,path⟩
      · rw [show bits.length=i by exact windowBits_length source i offset] at up
        have direct:u ≤ 2048*(r+1)*(D F r n 13+1):=up.trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2048 (by omega)))
        have rp:r+1 ≤ (r+1)^4:=by
          have square:r+1 ≤ (r+1)^2:=by nlinarith
          exact square.trans (Nat.pow_le_pow_right (by omega) (by decide))
        have pp:D F r n 13+1 ≤ (D F r n 13+1)^2:=by nlinarith
        have bound:=Nat.mul_le_mul_left 2048 (Nat.mul_le_mul rp pp)
        nlinarith only [direct,bound]
      · change (answer=true ↔ _) at correct
        rw [matches_window_original] at correct
        constructor
        · intro yes
          exact ⟨i,read,indexOK,correct.mp yes,(prefixGood_original source W offset i indexOK).mp padOK⟩
        · intro good
          obtain ⟨j,rj,_jW,active,_inactive⟩:=good
          have same:i=j:=Option.some.inj (read.symm.trans rj)
          subst j
          exact correct.mpr active
    · rw [if_neg padOK] at prePath
      refine ⟨t+q,false,?_,?_,prefixPath.append prePath⟩
      · exact phase_price r (D F r n 13) t q price (by
          simpa only [Nat.add_zero] using second_price r (D F r n 13) q 0 qp (by omega))
      · constructor
        · intro impossible;cases impossible
        · intro good
          obtain ⟨j,rj,jW,_active,inactive⟩:=good
          have same:i=j:=Option.some.inj (read.symm.trans rj)
          subst j
          exact False.elim (padOK ((prefixGood_original source W offset i indexOK).mpr inactive))
  · rw [if_neg indexOK] at prefixPath
    refine ⟨t,false,?_,?_,prefixPath⟩
    · have bound:=phase_price r (D F r n 13) t 0 price (by omega)
      omega
    · constructor
      · intro impossible
        cases impossible
      · intro good
        obtain ⟨j,rj,jW,_active,_inactive⟩:=good
        have same:i=j:=Option.some.inj (read.symm.trans rj)
        omega
end NormalFinalClosure
