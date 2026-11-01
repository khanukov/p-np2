import NormalFinalClosure.SourceCertificates2
import NormalFinalClosure.CodeCertificates2
import NormalFinalClosure.RepCounters2
import NormalFinalClosure.SourceUpdates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","dec_zero","dec_positive","DecRows"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field_dec"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["decCode_18","decCode_19"]),
    (`NormalFinalClosure.SourceCertificates2,`NormalFinalClosure,["left_493","left_546"]),
    (`NormalFinalClosure.SourceLeft2,`NormalFinalClosure,["PhysicalLeftRows","left_physical"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.rSource","GuardFrame.positive","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_unary4","rep_field4","rep_width"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["rep_frame_low","rep_source","physical_room"]),
    (`NormalFinalClosure.SourceUpdates2,`NormalFinalClosure,["rep_restore","rep_lift"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing shared real source-left loop API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing real source-left loop owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong real source-left loop owner"
      logInfo m!"paid-source-left-loop-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing source-left loop Node"
    let some i:=e.getModuleIdxFor? name | throwError "Missing source-left loop Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source-left loop Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private abbrev payState (k : Nat) (b : Bool) := if b then ns2 k 518 else ns2 k 465
private abbrev goState (k : Nat) (b : Bool) := ns2 k (if b then 546 else 493)
private abbrev readyState (k : Nat) (b : Bool) := ns2 k (if b then 736 else 622)
private theorem payCode (k : Nat) (b : Bool) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (payState k b) (readyState k b) (goState k b) := by
  cases b
  · exact decCode_18 k
  · exact decCode_19 k
private theorem leftCode (k : Nat) (b : Bool) : PhysicalLeftRows (M:=machine2 k) (Safe:=Safe2 k) (goState k b) (payState k) b := by
  cases b
  · exact left_493 k
  · exact left_546 k
/-- The complete physically paid source-left recurrence. It consumes the REAL
remaining-r field and moves the REAL carried hole, preserving the original
source, arbitrary assignment, length count and exterior at every boundary. -/
private theorem left_loop (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (ell v : Nat) (vr:v < r) :
    let cursor:=S-r+v
    ∀ hc:cursor < S,
    let b:=source ⟨cursor,hc⟩
    ∃ t,t ≤ 256*(v+1)*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (payState k b) (D F r n 0) (repImage T F r n S cursor v 0 ell 0 []))
      (node (readyState k (source ⟨S-r,by omega⟩)) (D F r n 0)
        (repImage T F r n S (S-r) 0 0 ell 0 [])) := by
  intro cursor hc b
  have room:=physical_room fr
  have rs:=rSource fr
  have fit:F+1 ≤ D F r n 13:=by change F+1 ≤ F+13*r+2*n+22;omega
  have width:=rep_width F r n 4 (by simp)
  have d4:D F r n 4 ≤ D F r n 13:=d_mono F r n 4 13 (by decide) (by decide)
  have rP:r ≤ D F r n 13:=by
    have h:=d_mono F r n 5 13 (by decide) (by decide)
    change D F r n 5=D F r n 4+r+1 at width
    omega
  induction v with
  | zero=>
    have g:=rep_grid fr cursor 0 0 ell 0 []
    have step:=dec_zero g (by decide) le_rfl width (rep_unary4 fr cursor 0 0 ell 0 []) (payCode k b)
    refine ⟨2*(D F r n 4-D F r n 0+4)+3,?_,?_⟩
    · have p:=op_price (D F r n) 4 0 (D F r n 13) d4 (by decide) (by omega)
      omega
    · simpa only [cursor,b,Nat.add_zero] using step
  | succ v ih=>
    have cursorEq:cursor=S-r+(v+1):=rfl
    have cp:0 < cursor:=by omega
    have g:=rep_grid fr cursor (v+1) 0 ell 0 []
    have step:=dec_positive g (by decide) le_rfl width (rep_unary4 fr cursor (v+1) 0 ell 0 []) (by omega) (by omega) (payCode k b)
    rw [field_dec g (by decide) width (rep_unary4 fr cursor (v+1) 0 ell 0 []) (by omega) (by omega),rep_field4 fr,
      show v+1-1=v by omega] at step
    have low:=rep_frame_low fr cursor v 0 ell 0 []
    have hole:repImage T F r n S cursor v 0 ell 0 [] cursor=none:=by
      rw [rep_source fr cursor v 0 ell 0 [] cursor (by omega) hc,if_pos rfl]
    obtain ⟨bit,hbit,path⟩:=left_physical low fit cp hc hole (by
      intro i lo hi ne
      rw [rep_source fr cursor v 0 ell 0 [] i (by omega) hi,if_neg ne]
      exact ⟨_,rfl⟩) (leftCode k b)
    have restored:=rep_restore fr cursor v 0 ell 0 [] (by omega) hc
    have lifted:=rep_lift fr (cursor-1) v 0 ell 0 [] (by omega)
    rw [show b=source ⟨cursor,hc⟩ from rfl,restored,lifted] at path
    have previous:cursor-1=S-r+v:=by omega
    have bitEq:bit=source ⟨cursor-1,by omega⟩:=by
      rw [rep_source fr cursor v 0 ell 0 [] (cursor-1) (by omega) (by omega),if_neg (by omega)] at hbit
      exact (Option.some.inj hbit).symm
    simp only [bitEq,previous] at path
    obtain ⟨t,price,tail⟩:=ih (by omega) (by omega)
    have whole:=step.append (path.append tail)
    refine ⟨(2*(D F r n 4-D F r n 0+4)+2*(v+1)+3)+(2*(F+1-cursor)+7+t),?_,?_⟩
    · have p1:=op_price (D F r n) 4 (v+1) (D F r n 13) d4 (by decide) (by omega)
      have p2:2*(F+1-cursor)+7 ≤ 16*(D F r n 13+1):=by omega
      simp only [Nat.add_mul,Nat.mul_add] at price ⊢
      omega
    · simpa only [cursor,b] using whole
end NormalFinalClosure
