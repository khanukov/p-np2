import NormalFinalClosure.ReadyImage2
import NormalFinalClosure.LeftLoop2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","clear_run","dec_positive"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field_dec"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["paint_field","op_price"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["clearCode_17","decCode_20"]),
    (`NormalFinalClosure.SourceCertificates2,`NormalFinalClosure,["left_599"]),
    (`NormalFinalClosure.SourceLeft2,`NormalFinalClosure,["left_eof"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.rSource","GuardFrame.positive","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_unary4","rep_field4","rep_width"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["rep_frame_low","rep_source","physical_room"]),
    (`NormalFinalClosure.SourceUpdates2,`NormalFinalClosure,["rep_lift"]),
    (`NormalFinalClosure.ReadyImage2,`NormalFinalClosure,["initialized_image"]),
    (`NormalFinalClosure.Initialization2,`NormalFinalClosure,["initialization"]),
    (`NormalFinalClosure.LeftLoop2,`NormalFinalClosure,["left_loop","payState","readyState"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing connected H-to-index ABI {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing connected H-to-index owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong connected H-to-index owner"
      logInfo m!"connected-H-to-index-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing connected Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing connected Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong connected Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
/-- Executes the complete INITIAL portion of the frozen final guard from its
actual H-entry: reset, W-copy, full bitLengthW and paid source-left positioning.
This is one same-table Path, not a proof-side source cursor initializer. -/
private theorem index_ready (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) :
    ∃ (hp:S-r < S) (t : Nat),t ≤ 8192*(r+1)^2*(D F r n 13+1) ∧
      Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (ns2 k 1) (S+z+2+n+1) T)
        (node (readyState k (source ⟨S-r,hp⟩)) (D F r n 0)
          (repImage T F r n S (S-r) 0 0 (bitLength W) 0 [])) := by
  have wp:=positive fr
  have wr:=windowRoom fr
  have rs:=rSource fr
  have rp:0 < r:=by omega
  have bound:=physical_room fr
  have fit:F+1 ≤ D F r n 13:=by change F+1 ≤ F+13*r+2*n+22;omega
  obtain ⟨a,ap,begin⟩:=initialization k fr
  rw [initialized_image fr] at begin
  have g:=rep_grid fr S 0 0 (bitLength W) 0 []
  have fill:=clear_run g (by decide) le_rfl (clearCode_17 k)
  rw [paint_field g 4 (by decide) true,show D F r n 5-D F r n 4-1=r by
    have eq:=rep_width F r n 4 (by simp);change D F r n 5=D F r n 4+r+1 at eq;omega,
    rep_field4 fr] at fill
  have gr:=rep_grid fr S r 0 (bitLength W) 0 []
  have dec:=dec_positive gr (by decide) le_rfl (rep_width F r n 4 (by simp))
    (rep_unary4 fr S r 0 (bitLength W) 0 []) rp le_rfl (decCode_20 k)
  rw [field_dec gr (by decide) (rep_width F r n 4 (by simp)) (rep_unary4 fr S r 0 (bitLength W) 0 []) rp le_rfl,
    rep_field4 fr] at dec
  have low:=rep_frame_low fr S (r-1) 0 (bitLength W) 0 []
  obtain ⟨bit,hbit,one⟩:=left_eof low fit (by omega) (by
    rw [rep_source fr S (r-1) 0 (bitLength W) 0 [] (S-1) (by omega) (by omega),if_neg (by omega)]
    exact ⟨_,rfl⟩) (left_599 k)
  rw [rep_lift fr (S-1) (r-1) 0 (bitLength W) 0 [] (by omega)] at one
  have bitEq:bit=source ⟨S-1,by omega⟩:=by
    rw [rep_source fr S (r-1) 0 (bitLength W) 0 [] (S-1) (by omega) (by omega),if_neg (by omega)] at hbit
    exact (Option.some.inj hbit).symm
  have previous:S-1=S-r+(r-1):=by omega
  simp only [bitEq,previous] at one
  obtain ⟨b,bp,rest⟩:=left_loop k fr (bitLength W) (r-1) (by omega) (by omega)
  have path:=begin.append (fill.append (dec.append (one.append rest)))
  refine ⟨by omega,a+((2*(D F r n 5-D F r n 0+4)+2)+((2*(D F r n 4-D F r n 0+4)+2*r+3)+(2*(F+1-S)+6+b))),?_,?_⟩
  · have d5:=d_mono F r n 5 13 (by decide) (by decide)
    have d4:=d_mono F r n 4 13 (by decide) (by decide)
    have rP:r ≤ D F r n 13:=by
      have eq:=rep_width F r n 4 (by simp)
      change D F r n 5=D F r n 4+r+1 at eq
      omega
    have p1:2*(D F r n 5-D F r n 0+4)+2 ≤ 64*(D F r n 13+1):=by omega
    have p2:=op_price (D F r n) 4 r (D F r n 13) d4 (by decide) rP
    have p3:2*(F+1-S)+6 ≤ 16*(D F r n 13+1):=by omega
    have square:r ≤ (r+1)^2:=by nlinarith
    rw [show r-1+1=r by omega] at bp
    have squareP:=Nat.mul_le_mul_right (D F r n 13+1) square
    have unitP:=Nat.mul_le_mul_right (D F r n 13+1) (show 1 ≤ (r+1)^2 by nlinarith)
    simp only [one_mul] at unitP
    nlinarith only [ap,bp,p1,p2,p3,squareP,unitP]
  · simpa only [previous] using path
end NormalFinalClosure
