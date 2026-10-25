import NormalFinalClosure.PrefixEntry2
import NormalFinalClosure.NativeCleanup2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep","dec_zero","dec_positive"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks","field_dec"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary5","rep_unary11","rep_field5","rep_field11"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","sourceMode_physical","sourceMode_virtual"]),
    (`NormalFinalClosure.NativeCleanup2,`NormalFinalClosure,["start","cleanup_physical","cleanup_virtual"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price"]),
    (`NormalFinalClosure.BufferNative2,`NormalFinalClosure,["append_record"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["prefixState","prefixTaken","prefixActive","prefixInactive","prefixAdvance","activeCode","prefix_dec","active_dec","append_active","append_inactive","inactive_one"]),
    (`NormalFinalClosure.PrefixEntry2,`NormalFinalClosure,["prefix_consume"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["select_safe"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing connected physical prefix digit API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing physical prefix digit owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong physical prefix digit owner"
      logInfo m!"connected-native-prefix-digit-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing prefix digit Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing prefix digit Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix digit Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private theorem cleanup_at (k : Nat) (answer : Bool) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) :
    ∃ t,t ≤ 1024*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (start k answer (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a b c index records))
      (node (if answer then (machine2 k).accept else (machine2 k).reject) (S+z+2+n+1)
        (repImage T F r n S S 0 0 0 0 [])) := by
  by_cases physical:cursor < S
  · rw [sourceMode_physical physical]
    exact cleanup_physical k answer fr cursor a b c index records lo physical
  · rw [sourceMode_virtual (by omega : S ≤ cursor)]
    exact cleanup_virtual k answer fr cursor a b c index records (by omega)
private def nextRecord (m : Fin 3) (index : Nat) : Nat := if index=0 then 0 else activeCode m
/-- One entire prefix iteration: real remaining and active-index payment,
3bit physical append, original-source read, or literal inactive-one rejection
including full cleanup. No source bit is supplied by a proof-side initializer. -/
private theorem prefix_digit (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a remaining index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) (vr:remaining+1 ≤ r) (ir:index ≤ r)
    (capacity:records.length ≤ r) (codes:∀ j,j < records.length → records[j]! < 4) :
    ∃ t,t ≤ 2048*(D F r n 13+1) ∧
      if index=0 ∧ (sourceMode source cursor).val=1 then
        Path (machine2 k) (Safe2 k) (D F r n 13) t
          (node (prefixState k (sourceMode source cursor)) (D F r n 0)
            (repImage T F r n S cursor a (remaining+1) 0 index records))
          (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 []))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (prefixState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a (remaining+1) 0 index records))
        (node (prefixState k (sourceMode source (min (cursor+1) S))) (D F r n 0)
          (repImage T F r n S (min (cursor+1) S) a remaining 0 (index-1)
            (records++[nextRecord (sourceMode source cursor) index]))) := by
  let m:=sourceMode source cursor
  have g:=rep_grid fr cursor a (remaining+1) 0 index records
  have take:=dec_positive g (by decide) le_rfl (rep_width F r n 5 (by simp))
    (rep_unary5 fr cursor a (remaining+1) 0 index records) (by omega) vr (prefix_dec k m)
  rw [field_dec g (by decide) (rep_width F r n 5 (by simp))
    (rep_unary5 fr cursor a (remaining+1) 0 index records) (by omega) vr,
    rep_field5 fr,show remaining+1-1=remaining by omega] at take
  have g1:=rep_grid fr cursor a remaining 0 index records
  have rP:r ≤ D F r n 13:=by
    have w:=rep_width F r n 5 (by simp)
    have d:=d_mono F r n 6 13 (by decide) (by decide)
    change D F r n 6=D F r n 5+r+1 at w
    omega
  have p1:=op_price (D F r n) 5 (remaining+1) (D F r n 13)
    (d_mono F r n 5 13 (by decide) (by decide)) (by decide) (by omega)
  cases index with
  | succ index=>
    have active:=dec_positive g1 (by decide) le_rfl (rep_width F r n 11 (by simp))
      (rep_unary11 fr cursor a remaining 0 (index+1) records) (by omega) ir (active_dec k m)
    rw [field_dec g1 (by decide) (rep_width F r n 11 (by simp))
      (rep_unary11 fr cursor a remaining 0 (index+1) records) (by omega) ir,
      rep_field11 fr,show index+1-1=index by omega] at active
    obtain ⟨aTime,aPrice,append⟩:=append_record k fr cursor a remaining 0 index records capacity codes
      (activeCode m) (by dsimp only [activeCode];split <;> omega) _ _ (append_active k m)
    obtain ⟨sTime,sPrice,consume⟩:=prefix_consume k fr cursor a remaining 0 index (records++[activeCode m]) lo hi
    have path:=take.append (active.append (append.append consume))
    refine ⟨(2*(D F r n 5-D F r n 0+5)+2*(remaining+1)+3)+((2*(D F r n 11-D F r n 0+11)+2*(index+1)+3)+(aTime+sTime)),?_,?_⟩
    · have p2:=op_price (D F r n) 11 (index+1) (D F r n 13)
        (d_mono F r n 11 13 (by decide) (by decide)) (by decide) (by omega)
      omega
    · rw [if_neg (by omega : ¬(index+1=0 ∧ (sourceMode source cursor).val=1))]
      simpa only [nextRecord,show index+1≠0 by omega,if_false,Nat.add_sub_cancel] using path
  | zero=>
    have inactive:=dec_zero g1 (by decide) le_rfl (rep_width F r n 11 (by simp))
      (rep_unary11 fr cursor a remaining 0 0 records) (active_dec k m)
    have p2:=op_price (D F r n) 11 0 (D F r n 13)
      (d_mono F r n 11 13 (by decide) (by decide)) (by decide) (by omega)
    by_cases one:m.val=1
    · have eq:m=1:=Fin.ext one
      have fit:=d_mono F r n 0 13 (by decide) (by decide)
      have entry:=keep (prefixInactive k m) (start k false m) (D F r n 0) (D F r n 0)
        (repImage T F r n S cursor a remaining 0 0 records) .stay (P:=D F r n 13) fit fit
        (select_safe k m 1428 2280 2982) (by rw [blanks g1 0 (by decide),eq];exact inactive_one k) rfl
      obtain ⟨t,tp,cleanup⟩:=cleanup_at k false fr cursor a remaining 0 0 records lo
      have path:=take.append (inactive.append (entry.append cleanup))
      refine ⟨(2*(D F r n 5-D F r n 0+5)+2*(remaining+1)+3)+((2*(D F r n 11-D F r n 0+11)+3)+(1+t)),?_,?_⟩
      · omega
      · rw [if_pos ⟨rfl,one⟩]
        exact path
    · obtain ⟨t,tp,append⟩:=append_record k fr cursor a remaining 0 0 records capacity codes 0 (by decide)
        _ _ (append_inactive k m one)
      obtain ⟨u,up,consume⟩:=prefix_consume k fr cursor a remaining 0 0 (records++[0]) lo hi
      have path:=take.append (inactive.append (append.append consume))
      refine ⟨(2*(D F r n 5-D F r n 0+5)+2*(remaining+1)+3)+((2*(D F r n 11-D F r n 0+11)+3)+(t+u)),?_,?_⟩
      · omega
      · rw [if_neg (by omega : ¬(0=0 ∧ (sourceMode source cursor).val=1))]
        simpa only [nextRecord,if_pos rfl,Nat.zero_sub] using path
end NormalFinalClosure
