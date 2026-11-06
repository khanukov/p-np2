import PhysicalCallerClosure.MetadataRows0
import PhysicalCallerClosure.MetadataRows1
import PhysicalCallerClosure.MetadataRows2
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact comparison interface {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong comparison term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong comparison owner"
  logInfo m!"comparison-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","ns","NativeSafe"]),
      (`PhysicalCallerClosure.Metadata,["MetaRows","metadata_path"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing comparison support {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong comparison support owner"
      logInfo m!"comparison-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private abbrev m_0_0_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 2714) (ns k 1435) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_0_0_0" "definition"
private abbrev m_0_0_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 2714) (ns k 1514) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_0_0_1" "definition"
private abbrev m_0_0_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 2714) (ns k 2085) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_0_1_0" "definition"
private abbrev m_0_0_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 2714) (ns k 2085) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_0_1_1" "definition"
private abbrev m_0_0_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 2714) (ns k 2210) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_0_2_0" "definition"
private abbrev m_0_0_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 2714) (ns k 2219) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_0_2_1" "definition"
private abbrev m_0_1_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 2714) (ns k 1740) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_1_0_0" "definition"
private abbrev m_0_1_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 2714) (ns k 1751) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_1_0_1" "definition"
private abbrev m_0_1_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 2714) (ns k 2128) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_1_1_0" "definition"
private abbrev m_0_1_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 2714) (ns k 2128) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_1_1_1" "definition"
private abbrev m_0_1_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 2714) (ns k 2365) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_1_2_0" "definition"
private abbrev m_0_1_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 2714) (ns k 2374) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_1_2_1" "definition"
private abbrev m_0_2_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 2714) (ns k 1909) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_2_0_0" "definition"
private abbrev m_0_2_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 2714) (ns k 1918) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_2_0_1" "definition"
private abbrev m_0_2_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 2714) (ns k 2169) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_2_1_0" "definition"
private abbrev m_0_2_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 2714) (ns k 2169) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_2_1_1" "definition"
private abbrev m_0_2_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 2714) (ns k 2520) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_2_2_0" "definition"
private abbrev m_0_2_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 2714) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.MetadataRows0 "code_0_2_2_1" "definition"
private abbrev m_1_0_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 3211) (ns k 1514) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_0_0_0" "definition"
private abbrev m_1_0_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 3211) (ns k 1514) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_0_0_1" "definition"
private abbrev m_1_0_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 3211) (ns k 2743) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_0_1_0" "definition"
private abbrev m_1_0_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 3211) (ns k 2085) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_0_1_1" "definition"
private abbrev m_1_0_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 3211) (ns k 2219) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_0_2_0" "definition"
private abbrev m_1_0_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 3211) (ns k 2219) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_0_2_1" "definition"
private abbrev m_1_1_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 3211) (ns k 1751) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_1_0_0" "definition"
private abbrev m_1_1_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 3211) (ns k 1751) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_1_0_1" "definition"
private abbrev m_1_1_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 3211) (ns k 2875) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_1_1_0" "definition"
private abbrev m_1_1_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 3211) (ns k 2128) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_1_1_1" "definition"
private abbrev m_1_1_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 3211) (ns k 2374) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_1_2_0" "definition"
private abbrev m_1_1_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 3211) (ns k 2374) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_1_2_1" "definition"
private abbrev m_1_2_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 3211) (ns k 1918) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_2_0_0" "definition"
private abbrev m_1_2_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 3211) (ns k 1918) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_2_0_1" "definition"
private abbrev m_1_2_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 3211) (ns k 3007) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_2_1_0" "definition"
private abbrev m_1_2_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 3211) (ns k 2169) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_2_1_1" "definition"
private abbrev m_1_2_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 3211) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_2_2_0" "definition"
private abbrev m_1_2_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 3211) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.MetadataRows1 "code_1_2_2_1" "definition"
private abbrev m_2_0_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 3334) (ns k 1514) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_0_0_0" "definition"
private abbrev m_2_0_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 3334) (ns k 1514) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_0_0_1" "definition"
private abbrev m_2_0_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 3334) (ns k 2085) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_0_1_0" "definition"
private abbrev m_2_0_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 3334) (ns k 2085) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_0_1_1" "definition"
private abbrev m_2_0_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 3334) (ns k 2219) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_0_2_0" "definition"
private abbrev m_2_0_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 3334) (ns k 2219) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_0_2_1" "definition"
private abbrev m_2_1_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 3334) (ns k 1751) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_1_0_0" "definition"
private abbrev m_2_1_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 3334) (ns k 1751) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_1_0_1" "definition"
private abbrev m_2_1_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 3334) (ns k 2128) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_1_1_0" "definition"
private abbrev m_2_1_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 3334) (ns k 2128) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_1_1_1" "definition"
private abbrev m_2_1_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 3334) (ns k 2374) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_1_2_0" "definition"
private abbrev m_2_1_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 3334) (ns k 2374) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_1_2_1" "definition"
private abbrev m_2_2_0_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 3334) (ns k 1918) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_2_0_0" "definition"
private abbrev m_2_2_0_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 3334) (ns k 1918) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_2_0_1" "definition"
private abbrev m_2_2_1_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 3334) (ns k 2169) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_2_1_0" "definition"
private abbrev m_2_2_1_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 3334) (ns k 2169) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_2_1_1" "definition"
private abbrev m_2_2_2_0 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 3334) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_2_2_0" "definition"
private abbrev m_2_2_2_1 : ∀ k : Nat,
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 3334) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.MetadataRows2 "code_2_2_2_1" "definition"
private def flags (a t : Fin 3) (last : Bool) : Fin 5 → Bool := fun j=>
  #[decide (t.val=2),decide (t.val=1),decide (a.val=2),decide (a.val=1),last][j.val]!
private def callbackEntry (k : Nat) (result : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[2714,3211,3334][result.val]!)
private def rejectEntry (k : Nat) (a t : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[1514,2085,2219,1751,2128,2374,1918,2169,1499][3*a.val+t.val]!)
private def payEntry (k : Nat) (a t : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[1435,2743,2210,1740,2875,2365,1909,3007,2520][3*a.val+t.val]!)
private def command (k : Nat) (result a t : Fin 3) (last : Bool) : Fin (callerMachine k).stateCount :=
  if result.val=2 ∨ decide (result.val=1)≠decide (t.val=1) then rejectEntry k a t
  else if last then rejectEntry k a t else payEntry k a t
private theorem compare_code (k : Nat) (result a t : Fin 3) (last : Bool) :
    Nonempty (MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (flags a t last)
      (callbackEntry k result) (command k result a t last)) := by
  fin_cases result
  · fin_cases a
    · fin_cases t
      · cases last
        · exact ⟨m_0_0_0_0 k⟩
        · exact ⟨m_0_0_0_1 k⟩
      · cases last
        · exact ⟨m_0_0_1_0 k⟩
        · exact ⟨m_0_0_1_1 k⟩
      · cases last
        · exact ⟨m_0_0_2_0 k⟩
        · exact ⟨m_0_0_2_1 k⟩
    · fin_cases t
      · cases last
        · exact ⟨m_0_1_0_0 k⟩
        · exact ⟨m_0_1_0_1 k⟩
      · cases last
        · exact ⟨m_0_1_1_0 k⟩
        · exact ⟨m_0_1_1_1 k⟩
      · cases last
        · exact ⟨m_0_1_2_0 k⟩
        · exact ⟨m_0_1_2_1 k⟩
    · fin_cases t
      · cases last
        · exact ⟨m_0_2_0_0 k⟩
        · exact ⟨m_0_2_0_1 k⟩
      · cases last
        · exact ⟨m_0_2_1_0 k⟩
        · exact ⟨m_0_2_1_1 k⟩
      · cases last
        · exact ⟨m_0_2_2_0 k⟩
        · exact ⟨m_0_2_2_1 k⟩
  · fin_cases a
    · fin_cases t
      · cases last
        · exact ⟨m_1_0_0_0 k⟩
        · exact ⟨m_1_0_0_1 k⟩
      · cases last
        · exact ⟨m_1_0_1_0 k⟩
        · exact ⟨m_1_0_1_1 k⟩
      · cases last
        · exact ⟨m_1_0_2_0 k⟩
        · exact ⟨m_1_0_2_1 k⟩
    · fin_cases t
      · cases last
        · exact ⟨m_1_1_0_0 k⟩
        · exact ⟨m_1_1_0_1 k⟩
      · cases last
        · exact ⟨m_1_1_1_0 k⟩
        · exact ⟨m_1_1_1_1 k⟩
      · cases last
        · exact ⟨m_1_1_2_0 k⟩
        · exact ⟨m_1_1_2_1 k⟩
    · fin_cases t
      · cases last
        · exact ⟨m_1_2_0_0 k⟩
        · exact ⟨m_1_2_0_1 k⟩
      · cases last
        · exact ⟨m_1_2_1_0 k⟩
        · exact ⟨m_1_2_1_1 k⟩
      · cases last
        · exact ⟨m_1_2_2_0 k⟩
        · exact ⟨m_1_2_2_1 k⟩
  · fin_cases a
    · fin_cases t
      · cases last
        · exact ⟨m_2_0_0_0 k⟩
        · exact ⟨m_2_0_0_1 k⟩
      · cases last
        · exact ⟨m_2_0_1_0 k⟩
        · exact ⟨m_2_0_1_1 k⟩
      · cases last
        · exact ⟨m_2_0_2_0 k⟩
        · exact ⟨m_2_0_2_1 k⟩
    · fin_cases t
      · cases last
        · exact ⟨m_2_1_0_0 k⟩
        · exact ⟨m_2_1_0_1 k⟩
      · cases last
        · exact ⟨m_2_1_1_0 k⟩
        · exact ⟨m_2_1_1_1 k⟩
      · cases last
        · exact ⟨m_2_1_2_0 k⟩
        · exact ⟨m_2_1_2_1 k⟩
    · fin_cases t
      · cases last
        · exact ⟨m_2_2_0_0 k⟩
        · exact ⟨m_2_2_0_1 k⟩
      · cases last
        · exact ⟨m_2_2_1_0 k⟩
        · exact ⟨m_2_2_1_1 k⟩
      · cases last
        · exact ⟨m_2_2_2_0 k⟩
        · exact ⟨m_2_2_2_1 k⟩
private theorem comparison_path (k : Nat) (result a t : Fin 3) (last : Bool)
    (D : Nat → Nat) (T : Nat → Option Bool) (H Q F P : Nat) (grid:Grid D T)
    (anchor:D 0=F+1) (metaWidth:D 13=D 12+6) (room:D 13 ≤ P)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (metadata:∀ j:Fin 5,T (D 12+1+j.val)=some (flags a t last j)) :
    Path (callerMachine k) (NativeSafe k) P (2*(D 12-H)+38)
      (node (callbackEntry k result) H T) (node (command k result a t last) H T) := by
  obtain ⟨code⟩:=compare_code k result a t last
  exact metadata_path grid anchor metaWidth room positive arena th tf marks gap metadata code
end PhysicalCallerClosure
