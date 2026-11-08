import NormalFinalClosure.SourceImage2
import NormalFinalClosure.Copy2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Unary"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["GuardFrame","D","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["d_mono","frame_before"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact shared counter image API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing shared counter image owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong shared counter image owner"
      logInfo m!"shared-counter-image-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem rep_width (F r n j : Nat) (hj:j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=11) :
    D F r n (j+1)=D F r n j+r+1 := by
  rcases hj with eq|eq|eq|eq|eq <;> subst j <;> norm_num only [D,SerializedBody.delimiter,ite_true,ite_false] <;> omega
private theorem rep_disjoint {F r n i j k} (hj:j ≤ 12) (hk:k ≤ 12) (ne:j≠k)
    (inside:D F r n j < i ∧ i < D F r n (j+1)) :
    ¬(D F r n k < i ∧ i < D F r n (k+1)) := by
  by_cases lt:j < k
  · have order:=d_mono F r n (j+1) k (by omega) (by omega)
    omega
  · have order:=d_mono F r n (k+1) j (by omega) (by omega)
    omega
private theorem rep_nohole {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor i j : Nat) (hj:j ≤ 12) (inside:D F r n j < i ∧ i < D F r n (j+1)) :
    ¬(i=cursor ∧ cursor < S) := by
  have low:=frame_before fr
  have order:=d_mono F r n 0 j (by omega) (by omega)
  omega
private theorem rep_unary4 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    Unary (D F r n) (repImage T F r n S cursor a b c index records) 4 a := by
  intro i lo hi
  simp only [repImage,if_neg (rep_nohole fr cursor i 4 (by decide) ⟨lo,hi⟩),if_pos (show D F r n 4 < i ∧ i < D F r n 5 from ⟨lo,hi⟩)]
private theorem rep_unary5 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    Unary (D F r n) (repImage T F r n S cursor a b c index records) 5 b := by
  intro i lo hi
  simp only [repImage,if_neg (rep_nohole fr cursor i 5 (by decide) ⟨lo,hi⟩),
    if_neg (rep_disjoint (by decide : 5 ≤ 12) (by decide : 4 ≤ 12) (by decide) ⟨lo,hi⟩),if_pos (show D F r n 5 < i ∧ i < D F r n 6 from ⟨lo,hi⟩)]
private theorem rep_unary6 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    Unary (D F r n) (repImage T F r n S cursor a b c index records) 6 c := by
  intro i lo hi
  simp only [repImage,if_neg (rep_nohole fr cursor i 6 (by decide) ⟨lo,hi⟩),
    if_neg (rep_disjoint (by decide : 6 ≤ 12) (by decide : 4 ≤ 12) (by decide) ⟨lo,hi⟩),
    if_neg (rep_disjoint (by decide : 6 ≤ 12) (by decide : 5 ≤ 12) (by decide) ⟨lo,hi⟩),if_pos (show D F r n 6 < i ∧ i < D F r n 7 from ⟨lo,hi⟩)]
private theorem rep_unary11 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    Unary (D F r n) (repImage T F r n S cursor a b c index records) 11 index := by
  intro i lo hi
  simp only [repImage,if_neg (rep_nohole fr cursor i 11 (by decide) ⟨lo,hi⟩),
    if_neg (rep_disjoint (by decide : 11 ≤ 12) (by decide : 4 ≤ 12) (by decide) ⟨lo,hi⟩),
    if_neg (rep_disjoint (by decide : 11 ≤ 12) (by decide : 5 ≤ 12) (by decide) ⟨lo,hi⟩),
    if_neg (rep_disjoint (by decide : 11 ≤ 12) (by decide : 6 ≤ 12) (by decide) ⟨lo,hi⟩),if_pos (show D F r n 11 < i ∧ i < D F r n 12 from ⟨lo,hi⟩)]
private theorem rep_field4 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index v : Nat) (records : List Nat) :
    field (repImage T F r n S cursor a b c index records) (D F r n) 4 v=
      repImage T F r n S cursor v b c index records := by
  funext i
  by_cases inside:D F r n 4 < i ∧ i < D F r n (4+1)
  · simp only [field,repImage,if_neg (rep_nohole fr cursor i 4 (by decide) inside),
      if_pos inside]
  · simp only [field,repImage,inside,if_false]
private theorem rep_field5 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index v : Nat) (records : List Nat) :
    field (repImage T F r n S cursor a b c index records) (D F r n) 5 v=
      repImage T F r n S cursor a v c index records := by
  funext i
  by_cases inside:D F r n 5 < i ∧ i < D F r n (5+1)
  · simp only [field,repImage,if_neg (rep_nohole fr cursor i 5 (by decide) inside),
      if_neg (rep_disjoint (by decide : 5 ≤ 12) (by decide : 4 ≤ 12) (by decide) inside),
      if_pos inside]
  · simp only [field,repImage,inside,if_false]
private theorem rep_field6 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index v : Nat) (records : List Nat) :
    field (repImage T F r n S cursor a b c index records) (D F r n) 6 v=
      repImage T F r n S cursor a b v index records := by
  funext i
  by_cases inside:D F r n 6 < i ∧ i < D F r n (6+1)
  · simp only [field,repImage,if_neg (rep_nohole fr cursor i 6 (by decide) inside),
      if_neg (rep_disjoint (by decide : 6 ≤ 12) (by decide : 4 ≤ 12) (by decide) inside),
      if_neg (rep_disjoint (by decide : 6 ≤ 12) (by decide : 5 ≤ 12) (by decide) inside),
      if_pos inside]
  · simp only [field,repImage,inside,if_false]
private theorem rep_field11 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index v : Nat) (records : List Nat) :
    field (repImage T F r n S cursor a b c index records) (D F r n) 11 v=
      repImage T F r n S cursor a b c v records := by
  funext i
  by_cases inside:D F r n 11 < i ∧ i < D F r n (11+1)
  · simp only [field,repImage,if_neg (rep_nohole fr cursor i 11 (by decide) inside),
      if_neg (rep_disjoint (by decide : 11 ≤ 12) (by decide : 4 ≤ 12) (by decide) inside),
      if_neg (rep_disjoint (by decide : 11 ≤ 12) (by decide : 5 ≤ 12) (by decide) inside),
      if_neg (rep_disjoint (by decide : 11 ≤ 12) (by decide : 6 ≤ 12) (by decide) inside),
      if_pos inside]
  · simp only [field,repImage,inside,if_false]
end NormalFinalClosure
