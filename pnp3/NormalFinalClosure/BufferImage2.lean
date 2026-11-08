import NormalFinalClosure.IndexImage2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["put"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_nohole","rep_disjoint"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing physical record image API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing physical record image owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong physical record image owner"
      logInfo m!"physical-prefix-record-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private theorem buffer_width (F r n : Nat) : D F r n 11=D F r n 10+3*r+4 := by
  norm_num only [D,SerializedBody.delimiter,ite_true,ite_false]
  omega
private theorem rep_stack {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (i : Nat)
    (inside:D F r n 10 < i ∧ i < D F r n 11) :
    repImage T F r n S cursor a b c index records i=
      if (i-D F r n 10-1)/3 < records.length then
        some (Nat.testBit (records[(i-D F r n 10-1)/3]!) (2-(i-D F r n 10-1)%3)) else some true := by
  simp only [repImage,if_neg (rep_nohole fr cursor i 10 (by decide) inside),
    if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 4 ≤ 12) (by decide) inside),
    if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 5 ≤ 12) (by decide) inside),
    if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 6 ≤ 12) (by decide) inside),
    if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 11 ≤ 12) (by decide) inside),if_pos inside]
private theorem rep_record {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (j bit : Nat)
    (capacity:records.length ≤ r+1) (stored:j < records.length) (bitRoom:bit < 3) :
    repImage T F r n S cursor a b c index records (D F r n 10+1+3*j+bit)=
      some (Nat.testBit (records[j]!) (2-bit)) := by
  have width:=buffer_width F r n
  rw [rep_stack fr cursor a b c index records _ (by omega),
    show (D F r n 10+1+3*j+bit-D F r n 10-1)=3*j+bit by omega,
    show (3*j+bit)/3=j by omega,show (3*j+bit)%3=bit by omega,if_pos stored]
private theorem rep_free {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (j bit : Nat)
    (unstored:records.length ≤ j) (room:j ≤ r) (bitRoom:bit < 3) :
    repImage T F r n S cursor a b c index records (D F r n 10+1+3*j+bit)=some true := by
  have width:=buffer_width F r n
  rw [rep_stack fr cursor a b c index records _ (by omega),
    show (D F r n 10+1+3*j+bit-D F r n 10-1)=3*j+bit by omega,
    show (3*j+bit)/3=j by omega,if_neg (by omega)]
private theorem first_false (code : Nat) (bound:code < 4) : Nat.testBit code 2=false := by
  interval_cases code <;> decide
private theorem appended_left (records : List Nat) (code j : Nat) (h:j < records.length) :
    (records++[code])[j]! = records[j]! := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_append_left h]
private theorem appended_last (records : List Nat) (code : Nat) :
    (records++[code])[records.length]! = code := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_append_right le_rfl,Nat.sub_self,
    List.getElem?_cons_zero,Option.getD_some]
/-- Exact full-image effect of the three literal writes into the real111 free
sentinel. Source hole, all counters, beta and every exterior cell are preserved. -/
private theorem rep_append {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (code : Nat) (bound:code < 4) (capacity:records.length ≤ r) :
    let h:=D F r n 10+1+3*records.length
    put (put (put (repImage T F r n S cursor a b c index records) h (some false))
      (h+1) (some (Nat.testBit code 1))) (h+2) (some (Nat.testBit code 0))=
      repImage T F r n S cursor a b c index (records++[code]) := by
  intro h
  funext i
  by_cases inside:D F r n 10 < i ∧ i < D F r n 11
  · rw [rep_stack fr cursor a b c index (records++[code]) i inside]
    let j:=(i-D F r n 10-1)/3
    let bit:=(i-D F r n 10-1)%3
    have bitRoom:bit < 3:=Nat.mod_lt _ (by decide)
    have form:i=D F r n 10+1+3*j+bit:=by dsimp only [j,bit];omega
    by_cases old:j < records.length
    · have ne0:i≠h:=by dsimp only [h];omega
      have ne1:i≠h+1:=by dsimp only [h];omega
      have ne2:i≠h+2:=by dsimp only [h];omega
      simp only [put,if_neg ne0,if_neg ne1,if_neg ne2]
      rw [rep_stack fr cursor a b c index records i inside,if_pos old,
        if_pos (show (i-D F r n 10-1)/3 < (records++[code]).length by simp only [List.length_append,List.length_cons,List.length_nil];change j < _;omega),
        appended_left records code j old]
    · by_cases eq:j=records.length
      · have occurs:(i-D F r n 10-1)/3 < (records++[code]).length:=by
          simp only [List.length_append,List.length_cons,List.length_nil]
          change j < _
          omega
        rw [if_pos occurs,show (i-D F r n 10-1)/3=records.length from eq,appended_last]
        change _=some (Nat.testBit code (2-bit))
        have cell:i=h+bit:=by dsimp only [h];omega
        rw [cell]
        interval_cases bit
        · simp only [Nat.add_zero,put,show h≠h+2 by omega,show h≠h+1 by omega,
            if_false,if_true,Nat.sub_zero,first_false code bound]
        · simp only [put,show h+1≠h+2 by omega,if_false,if_true]
        · simp only [put,if_true]
      · have ne0:i≠h:=by dsimp only [h];omega
        have ne1:i≠h+1:=by dsimp only [h];omega
        have ne2:i≠h+2:=by dsimp only [h];omega
        have later:¬(i-D F r n 10-1)/3 < (records++[code]).length:=by
          simp only [List.length_append,List.length_cons,List.length_nil]
          change ¬j < _
          omega
        simp only [put,if_neg ne0,if_neg ne1,if_neg ne2]
        rw [rep_stack fr cursor a b c index records i inside,if_neg old,if_neg later]
  · have notHere (j : Nat) (hj:j < 3):i≠h+j:=by
      intro eq
      subst i
      have width:=buffer_width F r n
      apply inside
      constructor <;> dsimp only [h] at * <;> omega
    simp only [put,if_neg (notHere 2 (by decide)),if_neg (notHere 1 (by decide)),
      show i≠h by simpa only [Nat.add_zero] using notHere 0 (by decide),if_false,repImage,if_neg inside]
end NormalFinalClosure
