import NormalFinalClosure.BESemantics2
import NormalFinalClosure.Ready2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary4","rep_unary5","rep_field4"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","sourceMode_physical","beState","rep_unary3"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["beDone"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["CopyRows","copy_run"]),
    (`NormalFinalClosure.MacroCertificates2,`NormalFinalClosure,["copyCore_2","copyCore_3","macroEntry_2","macroEntry_3"]),
    (`NormalFinalClosure.BELoop2,`NormalFinalClosure,["indexValue","be_loop"]),
    (`NormalFinalClosure.BESemantics2,`NormalFinalClosure,["read_indexValue"]),
    (`NormalFinalClosure.Ready2,`NormalFinalClosure,["index_ready"]),
    (`NormalFinalClosure.LeftLoop2,`NormalFinalClosure,["readyState"]),
    (`BitLengthDriver.Kernel,`BitLengthDriver,["length_step"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing H-to-original-index API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing H-to-index owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong H-to-index owner"
      logInfo m!"connected-H-original-index-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing index run Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing index run Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong index run Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private def copyEntry (k : Nat) (b : Bool) := if b then ns2 k 737 else ns2 k 623
private def copyCode (k : Nat) (b : Bool) :
    CopyRows (Safe:=Safe2 k) 3 4 5 (copyEntry k b) (beState k (if b then 1 else 0)) := by
  cases b
  · exact copyCore_2 k
  · exact copyCore_3 k
private theorem copy_entry (k : Nat) (b : Bool) :
    (machine2 k).step (readyState k b) none=(copyEntry k b,none,.stay) := by
  cases b
  · exact macroEntry_2 k
  · exact macroEntry_3 k
private theorem readySafe (k : Nat) (b : Bool) : Safe2 k (readyState k b) := by
  cases b <;> exact ns2_safe k _
private theorem length_le (v : Nat) : bitLength v ≤ v := by
  induction v using Nat.strong_induction_on with
  | h v ih=>
    by_cases zero:v=0
    · subst v;exact le_rfl
    · have eq:=length_step v (by omega)
      have bound:=ih (v/2) (Nat.div_lt_self (by omega) (by decide))
      omega
/-- Connected original H-entry through the entire source positioning and BE
parser. The returned i is the ORIGINAL readNatBE value, including virtual low
zeros; i>W executes literal reject/H/full cleared tape on this same table. -/
private theorem index_run (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) :
    ∃ t i,t ≤ 32768*(r+1)^2*(D F r n 13+1) ∧
      readNatBE (padWord source (S-r+bitLength W+W)) (S-r) (bitLength W)=some i ∧
      if i ≤ W then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (ns2 k 1) (S+z+2+n+1) T)
        (node (beDone k (sourceMode source (min (S-r+bitLength W) S))) (D F r n 0)
          (repImage T F r n S (min (S-r+bitLength W) S) (W-i) 0 0 i []))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (ns2 k 1) (S+z+2+n+1) T)
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  obtain ⟨hp,a,ap,initialPath⟩:=index_ready k fr
  have g:=rep_grid fr (S-r) 0 0 (bitLength W) 0 []
  have fit:=d_mono F r n 0 13 (by decide) (by decide)
  let bit:=source ⟨S-r,hp⟩
  have entry:=keep (readyState k bit) (copyEntry k bit) (D F r n 0) (D F r n 0)
    (repImage T F r n S (S-r) 0 0 (bitLength W) 0 []) .stay (P:=D F r n 13) fit fit
    (readySafe k bit) (by rw [blanks g 0 (by decide)];exact copy_entry k bit) rfl
  have wr:=windowRoom fr
  obtain ⟨b,bp,copy⟩:=copy_run g (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl (fun j hj=>rep_width F r n j (by rcases hj with h|h|h;exact Or.inl h;exact Or.inr (Or.inl h);exact Or.inr (Or.inr (Or.inl h))))
    (rep_unary3 fr (S-r) 0 0 (bitLength W) 0 [])
    (rep_unary4 fr (S-r) 0 0 (bitLength W) 0 [])
    (rep_unary5 fr (S-r) 0 0 (bitLength W) 0 []) wr (copyCode k bit)
  rw [rep_field4 fr] at copy
  have bitMode:sourceMode source (S-r)=(if bit then 1 else 0):=sourceMode_physical hp
  rw [←bitMode] at copy
  obtain ⟨c,cp,loop⟩:=be_loop k fr (bitLength W) (S-r) 0 (by omega) (by omega) (by omega) ((length_le W).trans wr)
  simp only [Nat.sub_zero] at loop
  let i:=indexValue source (S-r) (bitLength W) 0
  have read:=read_indexValue source (bitLength W) (S-r) (S-r+bitLength W+W) (by omega)
  rw [show min (S-r) S=S-r by omega] at read
  refine ⟨a+(1+(b+c)),i,?_,read,?_⟩
  · have mono:(W+1) ≤ r+1:=by omega
    have ell:bitLength W+1 ≤ r+1:=by have b:=length_le W;omega
    have product:8192*(bitLength W+1)*(W+1)*(D F r n 13+1) ≤ 8192*(r+1)^2*(D F r n 13+1):=by
      have p:=Nat.mul_le_mul ell mono
      nlinarith only [p]
    have copyPrice:256*(W+1)*(D F r n 13+1) ≤ 256*(r+1)^2*(D F r n 13+1):=by nlinarith
    have pos:0 < (r+1)^2*(D F r n 13+1):=by positivity
    nlinarith only [ap,bp,cp,product,copyPrice,pos]
  · by_cases ok:i ≤ W
    · rw [if_pos ok] at loop ⊢
      exact initialPath.append (entry.append (copy.append loop))
    · rw [if_neg ok] at loop ⊢
      exact initialPath.append (entry.append (copy.append loop))
end NormalFinalClosure
