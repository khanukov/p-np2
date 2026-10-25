import NormalFinalClosure.RepCounters2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["put"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["GuardFrame","repImage"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["rep_source"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact restored source image API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing restored source owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong restored source owner"
      logInfo m!"restored-source-image-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem rep_restore {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (lo:S-r ≤ cursor) (hi:cursor < S) :
    put (repImage T F r n S cursor a b c index records) cursor (some (source ⟨cursor,hi⟩))=
      repImage T F r n S S a b c index records := by
  funext i
  by_cases eq:i=cursor
  · subst i
    simp only [put,if_true]
    rw [rep_source fr S a b c index records cursor lo hi,if_neg (by omega)]
  · simp only [put,if_neg eq,repImage,show ¬(i=cursor ∧ cursor < S) by omega,
      show ¬(i=S ∧ S < S) by omega,if_false]
private theorem rep_lift {S z n F r W source T} (_fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (hi:cursor < S) :
    put (repImage T F r n S S a b c index records) cursor none=
      repImage T F r n S cursor a b c index records := by
  funext i
  by_cases eq:i=cursor
  · subst i
    rw [show put (repImage T F r n S S a b c index records) cursor none cursor=none by simp only [put,if_true]]
    dsimp only [repImage]
    rw [if_pos ⟨rfl,hi⟩]
  · simp only [put,if_neg eq,repImage,show ¬(i=cursor ∧ cursor < S) by omega,
      show ¬(i=S ∧ S < S) by omega,if_false]
end NormalFinalClosure
