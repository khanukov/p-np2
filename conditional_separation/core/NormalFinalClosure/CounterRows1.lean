import NormalFinalClosure.CounterSupport2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def selectCounter (owner : Name) (leaf kind : String) : TacticM Unit := do
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure")
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact split counter API"
  let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
  unless actual==kind do throwError "Wrong split counter kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing split counter owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong split counter owner"
  logInfo m!"split-native-certificate|{n}|{kind}|{ci.type}"
  closeMainGoal `selectCounter (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["ClearRows","DecRows","IncRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing actual counter type"
      let some i:=e.getModuleIdxFor? n | throwError "Missing actual counter type owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong actual counter type owner"
      logInfo m!"split-native-type|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev nativeRow : TacticM Unit := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nativeRow" "definition"
private abbrev nativeRoute : Nat → TacticM Unit := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nativeRoute" "definition"
private theorem nsSafe : ∀ k i,Safe2 k (ns2 k i) := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nsSafe" "theorem"

private theorem clearCode_0 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 4) (ns2 k 24) := by
  refine ⟨ns2 k 12,ns2 k 13,ns2 k 14,nsSafe k 12,nsSafe k 13,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_1 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 24) (ns2 k 48) := by
  refine ⟨ns2 k 34,ns2 k 35,ns2 k 36,nsSafe k 34,nsSafe k 35,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_2 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 48) (ns2 k 76) := by
  refine ⟨ns2 k 60,ns2 k 61,ns2 k 62,nsSafe k 60,nsSafe k 61,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_3 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 76) (ns2 k 124) := by
  refine ⟨ns2 k 98,ns2 k 99,ns2 k 100,nsSafe k 98,nsSafe k 99,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_4 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 125) (ns2 k 189) (ns2 k 147) := by
  refine ⟨ns2 k 131,ns2 k 132,ns2 k 133,ns2 k 134,ns2 k 135,ns2 k 141,nsSafe k 131,nsSafe k 132,nsSafe k 133,nsSafe k 134,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_5 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 147) (ns2 k 166) := by
  refine ⟨ns2 k 155,ns2 k 156,ns2 k 157,ns2 k 158,nsSafe k 155,nsSafe k 156,nsSafe k 157,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_6 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 166) (ns2 k 125) := by
  refine ⟨ns2 k 176,ns2 k 177,ns2 k 178,ns2 k 179,nsSafe k 176,nsSafe k 177,nsSafe k 178,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_7 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 189) (ns2 k 238) (ns2 k 223) := by
  refine ⟨ns2 k 199,ns2 k 200,ns2 k 201,ns2 k 202,ns2 k 203,ns2 k 213,nsSafe k 199,nsSafe k 200,nsSafe k 201,nsSafe k 202,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_8 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 223) (ns2 k 189) := by
  refine ⟨ns2 k 229,ns2 k 230,ns2 k 231,ns2 k 232,nsSafe k 229,nsSafe k 230,nsSafe k 231,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_9 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 238) (ns2 k 445) (ns2 k 266) := by
  refine ⟨ns2 k 246,ns2 k 247,ns2 k 248,ns2 k 249,ns2 k 250,ns2 k 258,nsSafe k 246,nsSafe k 247,nsSafe k 248,nsSafe k 249,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_10 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 266) (ns2 k 285) := by
  refine ⟨ns2 k 274,ns2 k 275,ns2 k 276,ns2 k 277,nsSafe k 274,nsSafe k 275,nsSafe k 276,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_11 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 285) (ns2 k 312) := by
  refine ⟨ns2 k 297,ns2 k 298,ns2 k 299,ns2 k 300,nsSafe k 297,nsSafe k 298,nsSafe k 299,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_12 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 312) (ns2 k 391) (ns2 k 340) := by
  refine ⟨ns2 k 320,ns2 k 321,ns2 k 322,ns2 k 323,ns2 k 324,ns2 k 332,nsSafe k 320,nsSafe k 321,nsSafe k 322,nsSafe k 323,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_13 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 340) (ns2 k 391) (ns2 k 368) := by
  refine ⟨ns2 k 348,ns2 k 349,ns2 k 350,ns2 k 351,ns2 k 352,ns2 k 360,nsSafe k 348,nsSafe k 349,nsSafe k 350,nsSafe k 351,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_14 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 368) (ns2 k 312) := by
  refine ⟨ns2 k 378,ns2 k 379,ns2 k 380,ns2 k 381,nsSafe k 378,nsSafe k 379,nsSafe k 380,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_15 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 392) (ns2 k 238) (ns2 k 426) := by
  refine ⟨ns2 k 402,ns2 k 403,ns2 k 404,ns2 k 405,ns2 k 406,ns2 k 416,nsSafe k 402,nsSafe k 403,nsSafe k 404,nsSafe k 405,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_16 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 426) (ns2 k 392) := by
  refine ⟨ns2 k 434,ns2 k 435,ns2 k 436,ns2 k 437,nsSafe k 434,nsSafe k 435,nsSafe k 436,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_17 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 true (ns2 k 445) (ns2 k 571) := by
  refine ⟨ns2 k 453,ns2 k 454,ns2 k 455,nsSafe k 453,nsSafe k 454,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_18 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 465) (ns2 k 622) (ns2 k 493) := by
  refine ⟨ns2 k 473,ns2 k 474,ns2 k 475,ns2 k 476,ns2 k 477,ns2 k 485,nsSafe k 473,nsSafe k 474,nsSafe k 475,nsSafe k 476,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_19 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 518) (ns2 k 736) (ns2 k 546) := by
  refine ⟨ns2 k 526,ns2 k 527,ns2 k 528,ns2 k 529,ns2 k 530,ns2 k 538,nsSafe k 526,nsSafe k 527,nsSafe k 528,nsSafe k 529,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_20 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 571) (ns2 k 0) (ns2 k 599) := by
  refine ⟨ns2 k 579,ns2 k 580,ns2 k 581,ns2 k 582,ns2 k 583,ns2 k 591,nsSafe k 579,nsSafe k 580,nsSafe k 581,nsSafe k 582,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_21 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 623) (ns2 k 687) (ns2 k 645) := by
  refine ⟨ns2 k 629,ns2 k 630,ns2 k 631,ns2 k 632,ns2 k 633,ns2 k 639,nsSafe k 629,nsSafe k 630,nsSafe k 631,nsSafe k 632,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_22 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 645) (ns2 k 664) := by
  refine ⟨ns2 k 653,ns2 k 654,ns2 k 655,ns2 k 656,nsSafe k 653,nsSafe k 654,nsSafe k 655,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_23 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 664) (ns2 k 623) := by
  refine ⟨ns2 k 674,ns2 k 675,ns2 k 676,ns2 k 677,nsSafe k 674,nsSafe k 675,nsSafe k 676,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_24 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 687) (ns2 k 850) (ns2 k 721) := by
  refine ⟨ns2 k 697,ns2 k 698,ns2 k 699,ns2 k 700,ns2 k 701,ns2 k 711,nsSafe k 697,nsSafe k 698,nsSafe k 699,nsSafe k 700,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_25 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 721) (ns2 k 687) := by
  refine ⟨ns2 k 727,ns2 k 728,ns2 k 729,ns2 k 730,nsSafe k 727,nsSafe k 728,nsSafe k 729,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_26 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 737) (ns2 k 801) (ns2 k 759) := by
  refine ⟨ns2 k 743,ns2 k 744,ns2 k 745,ns2 k 746,ns2 k 747,ns2 k 753,nsSafe k 743,nsSafe k 744,nsSafe k 745,nsSafe k 746,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
