import VirtualFinalClosure.WeightCodeFloor
namespace VirtualFinalClosure.WeightRowFloor
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.PowerCodeFloor","VirtualFinalClosure.PowerCodeFloor","row_floor","powerFloor",(1:Nat)),
      ("VirtualFinalClosure.WeightCodeFloor","VirtualFinalClosure.WeightCodeFloor","middle","middleCert",1),
      ("VirtualFinalClosure.WeightCodeFloor","VirtualFinalClosure.WeightCodeFloor","add","addCert",1),
      ("VirtualFinalClosure.WeightCodeFloor","VirtualFinalClosure.WeightCodeFloor","after","afterCert",1),
      ("PowerDriver.Rows","PowerDriver","decode_row","decodeRow",1),
      ("FullWeight.Rows","FullWeight","codes","codes",0),
      ("FullWeight.Rows","FullWeight","middle","middle",0),
      ("FullWeight.Rows","FullWeight","afterCodes","afterCodes",0),
      ("FullWeight.Rows","FullWeight","addCodes","addCodes",0),
      ("FullWeight.Rows","FullWeight","lookup_add","lookupAdd",1),
      ("FullWeight.Rows","FullWeight","lookup_after","lookupAfter",1),
      ("FullWeight.Rows","FullWeight","program","program",1),
      ("FullWeight.Rows","FullWeight","blen","blen",1),
      ("FullWeight.Rows","FullWeight","powers","powers",1),
      ("FullWeight.Rows","FullWeight","mlen","mlen",1),
      ("FullWeight.Rows","FullWeight","head_length","headLength",1),
      ("FullWeight.Rows","FullWeight","before","before",0),
      ("FullWeight.Rows","FullWeight","power","power",0),
      ("FullWeight.Rows","FullWeight","add","add",0),
      ("FullWeight.Rows","FullWeight","after","after",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual whole-weight ROM interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual whole-weight ROM interface {mod}/{key}"
private theorem selected (k ix : Nat) (xs : List Nat) (fits : ix < xs.length)
    (certificate : xs.all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true) :
    let code:=xs[ix]!
    xs[ix]?=some code ∧ (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k) := by
  intro code
  have member : code ∈ xs:=by
    dsimp only [code]
    rw [getElem!_pos xs ix fits]
    exact List.getElem_mem fits
  refine ⟨?_,of_decide_eq_true ((List.all_eq_true.mp certificate) code member)⟩
  dsimp only [code]
  rw [List.getElem?_eq_getElem fits,getElem!_pos xs ix fits]
private theorem middle_lookup (k ix : Nat) (fits : ix < 3) :
    (codes k)[795+246*k+ix]?=(middle k)[ix]? := by
  rw [program,List.append_assoc,List.append_assoc,List.append_assoc,List.getElem?_toArray,
    List.getElem?_append_right (by rw [blen];omega),blen,
    List.getElem?_append_right (by rw [powers];omega),powers]
  rw [show 795+246*k+ix-795-246*k=ix by omega,
    List.getElem?_append_left (by rw [mlen];exact fits)]
private theorem decoded (k i code : Nat) (b : Option Bool) (lo : 329 ≤ i) (hi : i < 430+93*k)
    (got : (codes k)[3*(i-64)+(match b with | none=>0 | some false=>1 | some true=>2)]?=some code)
    (range : code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k) :
    ((Cursor.machine k).step (Cursor.q k i) b).1.val=40 ∨
      329 ≤ ((Cursor.machine k).step (Cursor.q k i) b).1.val ∧ ((Cursor.machine k).step (Cursor.q k i) b).1.val ≤ 798+93*k := by
  have row:=decodeRow k i code b (by omega) (by omega) (by omega) (by omega) (by omega) got
  have bound : code/9 < Cursor.stateCount k:=by unfold Cursor.stateCount;rcases range with h|h <;> omega
  rw [row]
  change (code/9)%Cursor.stateCount k=40 ∨ 329 ≤ (code/9)%Cursor.stateCount k ∧ (code/9)%Cursor.stateCount k ≤ 798+93*k
  rw [Nat.mod_eq_of_lt bound]
  exact range
/-- Exhaustive actual indexed rows: all k-power blocks, middle, ALL +k blocks,
+4 and final multiplication. The returned cap798 is retained, not discarded.
This is the missing literal lower-control fact for full W-path projection. -/
private theorem row_floor (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (lo : 329 ≤ q.val) (hi : q.val < 430+93*k) :
    ((Cursor.machine k).step q b).1.val=40 ∨
      329 ≤ ((Cursor.machine k).step q b).1.val ∧ ((Cursor.machine k).step q b).1.val ≤ 798+93*k := by
  have state : Cursor.q k q.val=q:=Fin.ext (Nat.mod_eq_of_lt q.isLt)
  suffices ((Cursor.machine k).step (Cursor.q k q.val) b).1.val=40 ∨
      329 ≤ ((Cursor.machine k).step (Cursor.q k q.val) b).1.val ∧ ((Cursor.machine k).step (Cursor.q k q.val) b).1.val ≤ 798+93*k by
    simpa only [state] using this
  let sym:=match b with | none=>0 | some false=>1 | some true=>2
  have hs : sym < 3:=by cases b with | none=>decide | some v=>cases v <;> decide
  by_cases power : q.val < 329+82*k
  · let j:=(q.val-329)/82
    exact powerFloor k j q.val b (by dsimp only [j];omega) (by dsimp only [j];omega) (by dsimp only [j];omega)
  · by_cases single : q.val=329+82*k
    · have middleLen : (middle k).length=3:=mlen k
      have fits : sym < (middle k).length:=by rw [middleLen];exact hs
      obtain ⟨lookup,range⟩:=selected k sym (middle k) fits (middleCert k)
      apply decoded k q.val (middle k)[sym]! b lo hi
      · change (codes k)[3*(q.val-64)+sym]?=some (middle k)[sym]!
        rw [show 3*(q.val-64)+sym=795+246*k+sym by omega,middle_lookup k sym hs]
        exact lookup
      · exact range
    · by_cases adding : q.val < 330+93*k
      · let j:=(q.val-(330+82*k))/11
        let ix:=3*(q.val-(330+82*k+11*j))+sym
        have hj : j < k:=by dsimp only [j];omega
        have bound : ix < 33:=by dsimp only [ix,j];omega
        have len : (addCodes k j).length=33:=by rfl
        obtain ⟨lookup,range⟩:=selected k ix (addCodes k j) (by rw [len];exact bound) (addCert k j hj)
        apply decoded k q.val (addCodes k j)[ix]! b lo hi
        · change (codes k)[3*(q.val-64)+sym]?=some (addCodes k j)[ix]!
          rw [show 3*(q.val-64)+sym=798+246*k+33*j+ix by dsimp only [ix,j];omega,lookupAdd k j ix hj bound]
          exact lookup
        · exact range
      · let ix:=3*(q.val-(330+93*k))+sym
        have bound : ix < 360:=by dsimp only [ix];omega
        have len : (afterCodes k).length=360:=headLength k
        obtain ⟨lookup,range⟩:=selected k ix (afterCodes k) (by rw [len];exact bound) (afterCert k)
        apply decoded k q.val (afterCodes k)[ix]! b lo hi
        · change (codes k)[3*(q.val-64)+sym]?=some (afterCodes k)[ix]!
          rw [show 3*(q.val-64)+sym=798+279*k+ix by dsimp only [ix];omega,lookupAfter k ix bound]
          exact lookup
        · exact range
#print axioms selected
#print axioms middle_lookup
#print axioms decoded
#print axioms row_floor
end VirtualFinalClosure.WeightRowFloor
