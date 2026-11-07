import NormalFinalClosure.BufferImage2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["put"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.BufferImage2,`NormalFinalClosure,["buffer_width","rep_stack","rep_record","first_false"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing comparison record image API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing comparison record image owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong comparison record image owner"
      logInfo m!"comparison-record-image-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private theorem set_self (records : List Nat) (j : Nat) (h:j < records.length) :
    (records.set j 3)[j]! = 3 := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_self h,Option.getD_some]
private theorem set_other (records : List Nat) (j i : Nat) (ne:j≠i) :
    (records.set j 3)[i]! = records[i]! := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne ne]
/-- Both physical comparison writes turn001/010 into011 and leave every other
cell (including original source hole/assignment/exterior) exactly unchanged. -/
private theorem rep_process {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (seen : Nat)
    (capacity:records.length ≤ r+1) (stored:seen < records.length) (bound:records[seen]! < 4) :
    let h:=D F r n 10+1+3*seen
    put (put (repImage T F r n S cursor a b c index records) (h+2) (some true))
      (h+1) (some true)=repImage T F r n S cursor a b c index (records.set seen 3) := by
  intro h
  funext i
  by_cases inside:D F r n 10 < i ∧ i < D F r n 11
  · rw [rep_stack fr cursor a b c index (records.set seen 3) i inside,List.length_set]
    let j:=(i-D F r n 10-1)/3
    let bit:=(i-D F r n 10-1)%3
    have bitRoom:bit < 3:=Nat.mod_lt _ (by decide)
    have form:i=D F r n 10+1+3*j+bit:=by dsimp only [j,bit];omega
    by_cases eq:j=seen
    · have occurs:(i-D F r n 10-1)/3 < records.length:=by change j < _;omega
      rw [if_pos occurs,show (i-D F r n 10-1)/3=seen from eq,set_self records seen stored]
      change _=some (Nat.testBit 3 (2-bit))
      have cell:i=h+bit:=by dsimp only [h];omega
      rw [cell]
      interval_cases bit
      · simp only [Nat.add_zero,put,show h≠h+1 by omega,show h≠h+2 by omega,if_false]
        have old:=rep_record fr cursor a b c index records seen 0 capacity stored (by decide)
        simpa only [Nat.add_zero,Nat.sub_zero,first_false _ bound] using old
      · simp only [put,if_true]
        rfl
      · simp only [put,show h+2≠h+1 by omega,if_false,if_true]
        rfl
    · have ne1:i≠h+1:=by dsimp only [h];omega
      have ne2:i≠h+2:=by dsimp only [h];omega
      simp only [put,if_neg ne1,if_neg ne2]
      rw [rep_stack fr cursor a b c index records i inside]
      by_cases occurs:j < records.length
      · rw [if_pos occurs,if_pos occurs,set_other records seen j (by omega)]
      · rw [if_neg occurs,if_neg occurs]
  · have notHere (bit : Nat) (hbit:bit < 3):i≠h+bit:=by
      intro eq
      subst i
      apply inside
      have width:=buffer_width F r n
      constructor <;> dsimp only [h] at * <;> omega
    simp only [put,if_neg (notHere 1 (by decide)),if_neg (notHere 2 (by decide)),repImage,if_neg inside]
end NormalFinalClosure
